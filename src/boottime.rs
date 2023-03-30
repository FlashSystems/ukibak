use core::time::Duration;

/// Determin the time since the last reboot of the operating system.
pub fn time_since_boot() -> Option<Duration> {
    let mut t = libc::timespec { tv_sec: 0, tv_nsec: 0 };
    if unsafe { libc::clock_gettime(libc::CLOCK_BOOTTIME, &mut t) } == 0 {
        if let Ok(sec_since_boot) = t.tv_sec.try_into() {
            Some(Duration::from_secs(sec_since_boot))
        } else {
            None
        }
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Check that the returned timestamp advances by 2s if we sleep the
    // thread for 2s. This a very basic test.
    #[test]
    fn ticking() {
        let a = time_since_boot().unwrap();
        std::thread::sleep(Duration::from_secs(2));
        let b = time_since_boot().unwrap();

        assert_eq!(b.checked_sub(a).unwrap(), Duration::from_secs(2));
    }
}