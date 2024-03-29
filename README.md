# Unified Kernel Image backup utility

To facilitate secure boot the Linux kernel can be combined with an initrd and its command line into a Unified Kernel Image. This combined image contains all information and binaries needed to boot the system. It is meant to be signed as a whole to allow measuring the boot process of the kernel and securing the system against an [evil maid attack](https://en.wikipedia.org/wiki/Evil_maid_attack).

To learn more about creating and using a unified kernel image take a look at the excellent article on the [Arch Linux Wiki](https://wiki.archlinux.org/title/Unified_kernel_image).

You may say: "But I don't want to use secure boot. It's evil and only allows big tech to restrict my control over my own hardware."
Maybe, but even if you do not want to use secure boot a UKI can have a nice advantage for you:

## Having a bootable backup

The UKI contains all parts necessary to boot your system. The kernel, the initrd and the kernel command line are no longer separate parts. They are combined into one file. If we backup this file, we've got a complete backup of this system configuration. If we keep this backup within the ESP[^esp], this backup can simply be added to the boot menu and can be used if something goes wrong with the current kernel image or configuration.

Let's say we've got a tool that creates a backup copy of the UKI some time after the system was booted. Maybe 5 minutes after the boot, we conclude that the system is stable enough to make a snapshot of the current kernel, initrd and command line.

If we now modify the kernel command line or the initrd and create an unbootable system, we just select the backup copy from the boot menu and are back to a working configuration. This is the same if a kernel update bricks our system. Just select the backup copy of the UKI and your system is bootable again.

`ukibak` is this tool.

## What ukibak does

`ukibak` will do the following things:

1. Check that the currently booted kernel isn't already the backup copy.
1. Check that the currently booted kernel image is in deed a UKI and that it contains at least the kernel, an initrd and the kernel command line. This makes sure that we do not create an unusable backup copy.
1. Check that the currently booted kernel image was not modified since the last reboot. This is done to make sure that image has at least booted once successfully before we copy it.
1. Check that the currently booted kernel is different from the backup copy. This makes sure that we do not make unnecessary copy operations that may be slow and can wear out your eMMC or SDCard. This check is fast because only the header of the UKI is checked. It contains enough information do decide if the UKI was updated. [^include1]

[^esp]: EFI system partition
[^include1]: This step makes step one kind of obsolete. If the backup copy was booted it is by definition identical with the backup copy.

## How to use ukibak

### Creating backups

`ukibak` is started by a systemd timer 5 minutes after the last boot. This ensures that the kernel is only copied if the system was up and stable for at least 5 minutes. You can increase this timeout if you want to wait longer before creating the backup copy.

In the simplest configuration you just run `ukibak`. It will automatically determine the name of the booted kernel image and create a backup copy named `linux-last.efi` within the same directory. The name of the backup file can be changed via the `-n` option.

If you do not want to put the backup copy within the ESP, you can supply an absolute path for the backup copy via the `-A` parameter.

`ukibak` assumes that your ESP is mounted as `/efi` or `/boot`. It checks if `/efi` exists. If it does not, `/boot` is used. If you mounted you ESP somewhere else, you can use the `-e` switch, to specify this directory.

A complete list of command line arguments can be generated by using the `--help` command line switch.

### Automating backups

`ukibak` comes with two systemd-units that automate the backup process: `ukibak.service` and `ukibak.timer`. The timer-unit needs to be enabled. It automatically starts the service unit 5 minutes after the system was booted. The service-unit will then use `ukibak` to create a backup.

The service-unit sources `/etc/ukibak.conf` as an environment file. The following environment-variables are respected by `ukibak` and allow it to be configured without modifying the service-unit:

| Environment variable | Description                                                        | Default value               |
| -------------------- | ------------------------------------------------------------------ | --------------------------- |
| `UKIBAK_ESP`         | Path to the EFI service partition. Command line option '-e'.       | `/efi`                      |
| `UKIBAK_NAME`        | Name of the backup file. Command line option '-n'.                 | `linux-last.efi`            |
| `UKIBAK_EFIVARFS`    | Path to the mount point of the evivarfs. Command line option '-E'. | `/sys/firmware/efi/efivars` |

To enable the timer use: `systemctl enable --now ukibak.timer`. This will also start the timer immediately and create the first backup copy.

### Using backups

To make the created backup usable, a boot menu option must be created. If you use the default configuration of `ukibak`, the parameters must be the same as for the default linux boot entry. Only the name of the loader must be changed:

```bash
efibootmgr --create --disk /dev/sdX --part partition_number --label "Linux (last good configuration)" --loader 'EFI\Linux\linux-last.efi' --unicode
```

# How to build and install ukibak

## From source

To use `ukibak` on one of your systems just clone this repository and execute the following commands:

```bash
cargo build --release
install -Dm0750 -t "/usr/sbin/" "target/release/ukibak"
install -Dm0755 -t "/etc/systemd/system" "systemd/ukibak.service"
install -Dm0755 -t "/etc/systemd/system" "systemd/ukibak.timer"
```

## Via the arch linux AUR

There is an [AUR package](https://aur.archlinux.org/packages/ukibak) for arch linux that can be [installed manually](https://wiki.archlinux.org/title/Arch_User_Repository) or via your favourite AUR helper.

# Credits

The test files for the PE parser are taken from [corkami](https://github.com/corkami) to have a wide variate of different (and strange) cases for testing.
