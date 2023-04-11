use std::io::{Read, Seek, SeekFrom};
use byteorder::{ReadBytesExt, BigEndian, LittleEndian};

const MZ_SIGNATURE: u16 = 0x4d5a;
const PE_START_OFFSET: u64 = 0x3c;
const PE_SIGNATURE: u32 = 0x50450000;

#[derive(Debug, thiserror::Error)]
pub enum Error {
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
    
    #[error("Invalid image format. Not a PE file.")]
    InvalidImageFormat
}

/// Converts a zero terminated byte array into a string that contains
/// the first run of bytes until the first NULL character.
fn nullstr_to_str(nstr: &[u8]) -> Option<&str>{
    let end = nstr.iter().position(|&c| c == 0).unwrap_or(nstr.len());
    std::str::from_utf8(&nstr[0..end]).ok()
}

/// Reads the section table from the reader.
/// Before calling this function the reader must be positioned at the start of
/// the section table. It returns a vector of strings containing the section names.
fn read_section_table<T: Read + Seek> (reader: &mut T, sec_count: u16)  -> Result<Vec<String>, Error> {
    let mut sections = Vec::with_capacity(sec_count as usize);

    for _i in 0..sec_count {
        let mut section_name = [0u8; 8];
        reader.read_exact(&mut section_name)?;
        if let Some(section_name_str) = nullstr_to_str(&section_name) {
            sections.push(section_name_str.to_owned());
        }
        reader.seek(SeekFrom::Current(32))?;
    }

    Ok(sections)
}

/// Parse and check a PE file. Only the minimum is done to verify that this
/// is an EFI-PE file. The hash of the optional header (that also contains a
/// hash of the rest of the executable) and a vector of section names is returned.
pub fn parse<T: Read + Seek> (reader: &mut T) -> Result<(u64, Vec<String>), Error> {
    // Check the Header of the DOS-Stub to be "MZ"
    if reader.read_u16::<BigEndian>()? != MZ_SIGNATURE {
        return Err(Error::InvalidImageFormat);
    }

    // Check the PE header
    reader.seek(SeekFrom::Start(PE_START_OFFSET))?;
    let pe_start_offset = reader.read_u32::<LittleEndian>()?;
    reader.seek(SeekFrom::Start(pe_start_offset as u64))?;
    if reader.read_u32::<BigEndian>()? != PE_SIGNATURE {
        return Err(Error::InvalidImageFormat);
    }

    // Read the number of sections
    reader.seek(SeekFrom::Current(2))?;
    let sections = reader.read_u16::<LittleEndian>()?;

    // Get the size of the optional header and calculate the start of
    // the section header
    reader.seek(SeekFrom::Current(12))?;
    let optional_header_size = reader.read_u16::<LittleEndian>()?;
    if optional_header_size == 0 || optional_header_size > 1024 {
        return Err(Error::InvalidImageFormat);
    }

    // Seek to the start of the optional header and read the complete
    // optional header into a buffer
    reader.seek(SeekFrom::Current(2))?;
    let mut buffer = vec![0u8; optional_header_size as usize];
    reader.read_exact(&mut buffer)?;
    let hash = const_fnv1a_hash::fnv1a_hash_64(&buffer, None);

    // Skip the characteristiks field. Now we're past the header at the
    // start of the section table.
    Ok((hash, read_section_table(reader, sections)?))
}

#[cfg(test)]
mod tests {
    use super::parse;
    use std::{path::PathBuf, collections::HashSet};

    #[test]
    fn corkami_testset_positive() {
        let mut test_pes = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        test_pes.push("testdata/pe");

        for file in std::fs::read_dir(test_pes).unwrap() {
            let file = file.unwrap();
            let mut image_file = std::fs::File::options().read(true).open(file.path()).unwrap();
            assert!(parse(&mut image_file).is_ok(), "File {} should not have failed.", file.file_name().to_string_lossy());
        }
    }

    #[test]
    fn corkami_testset_negative() {
        let mut test_pes = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        test_pes.push("testdata/nope");

        for file in std::fs::read_dir(test_pes).unwrap() {
            let file = file.unwrap();
            let mut image_file = std::fs::File::options().read(true).open(file.path()).unwrap();
            assert!(parse(&mut image_file).is_err(), "File {} should have failed.", file.file_name().to_string_lossy());
        }
    }

    #[test]
    fn verify_image() {
        let mut test_image_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        test_image_path.push("testdata/pe/linux.efi");

        let mut image_file = std::fs::File::options().read(true).open(test_image_path).unwrap();
        let (checksum, sections) = parse(&mut image_file).expect("Parsing UKI failed.");
        assert_eq!(checksum, 0xb56744082a8ac104);

        let mut expected_sections = HashSet::from([".text", ".reloc", ".data", ".dynamic", ".rela", ".dynsym", ".sbat", ".sdmagic", ".osrel", ".cmdline", ".linux", ".initrd"]);
        for section in sections {
            assert!(expected_sections.remove(section.as_str()), "Unexpected section {} in section list.", section);
        }
        assert!(expected_sections.is_empty(), "Section(s) {} missing from section list.", expected_sections.into_iter().collect::<Vec<&str>>().join(", "))
    }
}