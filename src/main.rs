use std::{fs::File, path::{Path, PathBuf}, ffi::OsString, collections::HashSet};
use clap::{Parser, ArgGroup};
use byteorder::{ReadBytesExt, LittleEndian};
use log::{error, debug, info, warn};
use quick_error::quick_error;

mod peparser;

quick_error! {
    #[derive(Debug)]
    pub enum Error {
        Io(err: std::io::Error, file: PathBuf) {
            source(err)
            display("I/O error while accessing {}: {}", file.display(), err)
        }
        Utf16(err: std::string::FromUtf16Error) {
            from()
            display("Error reading EFI variable: {}", err)
        }
        UkiParseError(err: peparser::Error) {
            from()
            display("Parsing image failed: {}", err)
        }
        EspNotFound(paths: String) {
            display("ESP not found. Tried {}.", paths)
        }
        SourceNotFound(path: PathBuf) {
            display("Source image '{}' not found.", path.display())
        }
        InvalidSourcePath(path: PathBuf) {
            display("Source image '{}' path invalid.", path.display())
        }
        DestinationPathInvalid(path: PathBuf) {
            display("'{}' is not a valid destination path. It may not exist or may name a file insted of a directory.", path.display())
        }
        FileNameRequired(name: OsString) {
            display("The file name '{}' contains a path seperator. This is not allowed.", name.to_string_lossy())
        }
        AbsPathRequired {
            display("Absolute path required. Use -f to force usage of a relative path.")
        }
        MissingSection(images: Vec<&'static str>) {
            display("Some sections ({}) that should be inside a unified kernel image missing. Making a backup copy of this image will not capture all necessary information to boot the system.", images.join(", "))
        }
    }
}

/// Simple program to greet a person
#[derive(Parser, Debug)]
#[command(version, about, long_about = None)]
#[command(group(ArgGroup::new("dest")))]
struct Args {
    /// Absolute path to the esp.
    #[arg(short, long, value_name="ESP", env="UKIBAK_ESP")]
    esp: Option<OsString>,

    /// Name of the backup copy.
    ///
    /// The copy is created within the same directory as the source UKI.
    #[arg(short, long, value_name="NAME", env="UKIBAK_NAME", group="dest", default_value="linux-last.efi")]
    name: Option<OsString>,

    /// Path and file name of the backup copy. Allows placing the backup copy in a separate directory. Use only if neccessary.
    #[arg(short = 'A', long, value_name="PATH", group="dest")]
    absname: Option<OsString>,

    /// Set the mount point of the efivarfs filesystem.
    #[arg(short = 'E', long, value_name="PATH", env="UKIBAK_EFIVARFS", default_value="/sys/firmware/efi/efivars")]
    efivarfs: OsString,

    /// Suppresses any output
    #[arg(short, long, group="verbosity")]
    quiet: bool,

    /// Enable debug output
    #[arg(short, long, group="verbosity")]
    debug: bool,

    /// Force usage of relative paths.
    #[arg(short, long)]
    force: bool,

    /// Always make a copy of the source EFI file, even if the checksums of both files match.
    ///
    /// Beware that this will also copy the backup copy over itself if it is the currently booted UKI! Use with care.
    #[arg(short = 'F', long)]
    forcecopy: bool,
}

/// Extracts the load_image_name of a UKI image from an evivarfs filesyystem.
fn get_loader_image_name(efivarfs: &Path) -> Result<String, Error>{
    let lii_filename = efivarfs.join("LoaderImageIdentifier-4a67b082-0a4c-41cf-b6c7-440b29bb8c4f");
    let mut efi_var = File::options()
        .read(true)
        .open(&lii_filename)
        .map_err(|e| { Error::Io(e, lii_filename.clone()) })?;

    let mut buffer = Vec::new();

    // Skipt the 4 attribute bytes
    efi_var.read_u32::<LittleEndian>().map_err(|e| { Error::Io(e, lii_filename.clone()) })?;

    // Read the UTF-16 chars
    loop {
        let mut char = efi_var.read_u16::<LittleEndian>().map_err(|e| { Error::Io(e, lii_filename.clone()) })?;
        if char == 0 { break };

        // Replace backslash by slash
        if char == 92 { char = 47 }

        buffer.push(char);
    }

    Ok(String::from_utf16(&buffer[..])?)
}

/// Setup simple_logger based on the value of the quiet and debug flags.
/// If quiet and debug are set (which clap should prevent) the debug flag wins.
fn setup_logging(quiet: bool, debug: bool) {
    let log_level = match (quiet, debug) {
        (false, false) => log::Level::Info,
        (true, false) => log::Level::Warn,
        (_, true) => log::Level::Debug
    };

    simple_logger::init_with_level(log_level).unwrap();
}

/// Check that the given file is a unified kernel image and that it contains
/// the relevant sections for a backup to be usefull.
fn check_uki(source: &Path) -> Result<u64, Error> {
    debug!("Parsing image {}...", source.display());

    let mut image_file = File::options().read(true).open(source).map_err(|e| { Error::Io(e, source.into()) })?;
    let mut missing_sections = HashSet::from([".linux", ".initrd", ".cmdline"]);

    let pe_info = peparser::parse(&mut image_file)?;

    for section_name in pe_info.1.into_iter() {
        missing_sections.remove(section_name.as_str());
    }

    if missing_sections.is_empty() {
        debug!("Image is self contained.");
        Ok(pe_info.0)
    } else {
        debug!("Image is not self contained.");
        Err(Error::MissingSection(missing_sections.into_iter().collect()))
    }
}

// Checks a list of paths and returns the first existing path that is a directory.
fn get_esp_path_from_list<'p>(paths: &[&'p Path], allow_relative: bool) -> Result<&'p Path, Error> {
    for &path in paths {
        if path.is_relative() {
            warn!("The path to the ESP should be absolute. '{}' is relative.", path.display());
            if !allow_relative { Err(Error::AbsPathRequired)?; }
        }

        if path.exists() && path.is_dir() {
            return Ok(path);
        }
    }

    Err(Error::EspNotFound(paths.iter().map(|&p| p.display().to_string()).collect::<Vec<String>>().join(", ")))?
}

/// Determins the destination path for the copy operation from the source UKI file,
/// the configured absname/relname and the force flag.
fn get_dest_path(source_path: &Path, name: &Option<OsString>, absname: &Option<OsString>, force: bool) -> Result<PathBuf, Error> {
    // Determin the destination path:
    // If the "relname" ist set, check that it is indeed relative and combine it with the
    // basepath of the source EFI file to get the destination path.
    // If "relname" is not set, use "absname" as is.
    let dest_path = if let Some(ref name) = name {
        let path = Path::new(name);

        if path.file_name().map(|n| n.len()).unwrap_or_default() != name.len() {
            Err(Error::FileNameRequired(name.clone()))
        }
        else if let Some(parent) = source_path.parent() {
            Ok(parent.join(name))
        } else {
            Err(Error::InvalidSourcePath(source_path.to_owned()))
        }
    } else {
        Ok(PathBuf::from(absname.as_ref().unwrap()))    // We can safely unwrap here because clap has ensured that either name or absname are set.
    }?;

    // Now the destination path should be absolute. If it is relative some of the input paths
    // (the ESP path or the path passed via absname) must have been relative. Do not allow this
    // without the force flag. This tool will mostly run within automated scripts and systemd
    // units and relative paths are easy to get wrong. We don't want to scatter .efi-files
    // around the users machine.
    if dest_path.is_relative() {
        warn!("The destination path should be absolute. Not using a relative path can lead to backup files being created in strange places.");
        if !force { Err(Error::AbsPathRequired)?; }
    }

    // Check that the parent directory of the destination path exists.
    if dest_path.parent().map(|p| p.exists() && p.is_dir()).unwrap_or(false) {

        // Verify that the destination is a path
        if dest_path.file_name().is_some() && !dest_path.is_dir() {
            Ok(dest_path)
        } else {
            Err(Error::DestinationPathInvalid(dest_path))
        }
    } else {
        Err(Error::DestinationPathInvalid(dest_path))
    }
}

fn backup_uki(args: &Args) -> Result<(), Error> {
    // Create a list of ESP paths.
    // If a path is given on the command line, use only this path.
    // If no path is given, use `/efi` and `/boot`.
    let esp_paths = if let Some(ref esp) = args.esp {
        vec![Path::new(esp)]
    } else {
        vec![Path::new("/efi"), Path::new("/boot")]
    };

    // Select a path from the list.
    let esp_path = get_esp_path_from_list(&esp_paths, args.force)?;

    let active_esp: PathBuf = get_loader_image_name(&PathBuf::from(&args.efivarfs))?.into();
    debug!("Active loader image name is '{}'.", active_esp.display());

    // Combine the relative path of the active ESP with the mountpoint of the ESP
    // specified on the command line (or the default).
    let source_path = esp_path.join(active_esp);
    if !source_path.exists() {
        Err(Error::SourceNotFound(source_path.clone()))?;
    }

    let dest_path = get_dest_path(&source_path, &args.name, &args.absname, args.force)?;

    // Check that the source is a unified kernel image and output a warning,
    // if sections are missing or if the file is something else.
    match check_uki(&source_path) {
        Ok(source_hash) => {
            if args.forcecopy || source_hash != check_uki(&dest_path).unwrap_or(0) {
                info!("Copying '{}' to '{}'...", source_path.display(), dest_path.display());
                std::fs::copy(&source_path, dest_path).map_err(|e| { Error::Io(e, source_path) })?;
                debug!("Copy succeeded.");
            } else {
                info!("Checksums of '{}' and '{}' match. Skipping copy.", source_path.display(), dest_path.display());
            }
        },
        Err(err) => {
            warn!("{}", err);
            if !args.force { Err(err)?; }
        }
    }

    Ok(())
}

fn main() {
    let args = Args::parse();

    setup_logging(args.quiet, args.debug);

    if let Err(err) = backup_uki(&args) {
        error!("{}", err);

        let exit_code = match err {
            Error::FileNameRequired(_) => 1,
            Error::AbsPathRequired => 1,
            Error::Io(_, _) => 2,
            Error::Utf16(_) => 3,
            Error::EspNotFound(_) => 3,
            Error::UkiParseError(_) => 4,
            Error::MissingSection(_) => 4,
            Error::SourceNotFound(_) => 4,
            Error::InvalidSourcePath(_) => 4,
            Error::DestinationPathInvalid(_) => 5
        };

        std::process::exit(exit_code);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Check that get_loader_image_name returns the correct image name.
    /// This test uses a snapshot of the neccessary efivarfs content in `testdata/efivarfs`.
    #[test]
    fn load_image_name() {
        let dummy_efivarfs = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("testdata/efivarfs");

        assert_eq!(get_loader_image_name(&dummy_efivarfs).unwrap(), "EFI/Linux/test_usable_uki.efi");
    }

    /// Verify that the checksum of an existing UKI file is
    /// correctly calculated.
    #[test]
    fn check_uki_success() {
        let test_image_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("testdata/efi/EFI/Linux/test_usable_uki.efi");

        assert_eq!(check_uki(&test_image_path).unwrap(), 0xb56744082a8ac104);
    }

    /// Verify that a non existing UK iis correctly detected and that the
    /// error message contains the correct path.
    #[test]
    fn check_uki_notfound() {
        let test_image_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("testdata/efi/EFI/Linux/missing.efi");

        if let Err(Error::Io(err, file)) = check_uki(&test_image_path) {
            assert_eq!(err.kind(), std::io::ErrorKind::NotFound);
            assert_eq!(file, test_image_path);
        } else {
            panic!("No error returned on missing input file.")
        }
    }

    /// Check with an image that is missing the `.initrd` section that this is
    /// correctly detected.
    #[test]
    fn check_uki_noinitrdsection() {
        let test_image_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("testdata/efi/EFI/Linux/test_noinitrd.efi");

        if let Err(Error::MissingSection(mut sections)) = check_uki(&test_image_path) {
            sections.sort();
            assert_eq!(sections.join(","), ".initrd");
        } else {
            panic!("No error returned on missing .initrd section.")
        }
    }

    /// Check that the get_esp_path_from_list correctly returns the first existing
    /// path.
    #[test]
    fn check_get_existing_path_from_list() {
        // Generate some test paths
        let base_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("testdata");
        let exists1 = base_path.join("efi");
        let exists2 = exists1.join("efivarfs");
        let not_exists1 = exists1.join("xxx");
        let not_exists2 = exists1.join("yyy");

        // Check that the first existing path is returned
        assert_eq!(get_esp_path_from_list(&[&not_exists1, &exists1], false).unwrap(), exists1);
        assert_eq!(get_esp_path_from_list(&[&not_exists1, &exists1, &not_exists2], false).unwrap(), exists1);
        assert_eq!(get_esp_path_from_list(&[&not_exists1, &not_exists2, &exists1], false).unwrap(), exists1);
        assert_eq!(get_esp_path_from_list(&[&exists1, &exists2], false).unwrap(), exists1);

        // Check that the correct list of paths is returned if all paths do not exist
        if let Err(Error::EspNotFound(path_list)) = get_esp_path_from_list(&[&not_exists1, &not_exists2], false) {
            assert_eq!(path_list, format!("{}, {}", not_exists1.display(), not_exists2.display()));
        } else {
            panic!("Non existing path list did not fail.");
        }
    }

    #[test]
    fn check_get_dest_path() {
        let base_path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("testdata");
        let existing_efi = base_path.join("efi/EFI/Linux/test_usable_uki.efi");
        let abs_target_efi = base_path.join("last.efi");
        let rel_target_efi = base_path.join("efi/EFI/Linux/last.efi");

        assert_eq!(get_dest_path(&existing_efi, &Some(OsString::from("last.efi")), &None, false).unwrap(), rel_target_efi);
        assert_eq!(get_dest_path(&base_path, &None, &Some(abs_target_efi.as_os_str().to_owned()), false).unwrap(), abs_target_efi);

        // Check that a non existing destination path is correctly reported.
        let non_exsiting_path = base_path.join("xxx/xxx.efi");
        let non_exsiting_path_dst = base_path.join("xxx/last.efi");
        if let Err(Error::DestinationPathInvalid(dst_path)) = get_dest_path(&non_exsiting_path, &Some(OsString::from("last.efi")), &None, false) {
            assert_eq!(dst_path, non_exsiting_path_dst);
        } else {
            panic!("Non existing source path does not yield error.");
        }

        // Check that a source path with no parent (for eg. the root path) yields an error.
        if let Err(Error::InvalidSourcePath(src_path)) = get_dest_path(&PathBuf::from("/"), &Some(OsString::from("last.efi")), &None, false) {
            assert_eq!(src_path.to_string_lossy(), "/");
        } else {
            panic!("Invalid source path does not yield error.");
        }

        // Check that a absolute path can not be used as a name
        if let Err(Error::FileNameRequired(dst_path)) = get_dest_path(&base_path, &Some(abs_target_efi.as_os_str().to_owned()), &None, false) {
            assert_eq!(dst_path, abs_target_efi);
        } else {
            panic!("Relative path is not detected.");
        }

        // Check that a path delimiter is detected within the file name.
        let delimiter_in_name = OsString::from("../reltest.efi");
        if let Err(Error::FileNameRequired(name)) = get_dest_path(&base_path, &Some(delimiter_in_name.clone()), &None, false) {
            assert_eq!(name, delimiter_in_name);
        } else {
            panic!("Invalid file name not detected.");
        }

        // Check that an absolute path that treats a file as a directory can not be used.
        let abs_target_invalid = base_path.join("efi/EFI/Linux/test_usable_uki.efi/mytest");
        if let Err(Error::DestinationPathInvalid(dst_path)) = get_dest_path(&base_path, &None, &Some(abs_target_invalid.as_os_str().to_owned()), false) {
            assert_eq!(dst_path, abs_target_invalid);
        } else {
            panic!("Invalid destination path not detected.");
        }

        // Check that a relative path can not be used as an absname using the force flag
        if let Err(Error::AbsPathRequired) = get_dest_path(&base_path, &None, &Some(OsString::from("test/last.efi")), false) {
            //OK
        } else {
            panic!("Using a relative path as an absname without force did not panic.");
        }
        if let Err(Error::DestinationPathInvalid(_)) = get_dest_path(&base_path, &None, &Some(OsString::from("test/last.efi")), true) {
            //OK: We test for PathNotFound here because this signals that the path was accepted.
        } else {
            panic!("Using a relative path as an absname without force did not panic.");
        }
    }
}
