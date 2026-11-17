//! Linux process accounting. RSS is a whole-process measurement, not an
//! allocation attribution. VmHWM is read after exec to avoid inherited peaks.
use serde::Serialize;
#[derive(Clone, Copy, Debug, Serialize)]
pub struct Resources {
    pub user_seconds: f64,
    pub system_seconds: f64,
    pub rss_kib: u64,
    pub hwm_kib: u64,
}
pub fn snapshot() -> crate::Result<Resources> {
    #[cfg(target_os = "linux")]
    {
        let mut usage = std::mem::MaybeUninit::<libc::rusage>::uninit();
        // The OS initializes the complete rusage struct on successful return.
        let code = unsafe { libc::getrusage(libc::RUSAGE_SELF, usage.as_mut_ptr()) };
        if code != 0 {
            return Err(std::io::Error::last_os_error().to_string());
        }
        let usage = unsafe { usage.assume_init() };
        let status = std::fs::read_to_string("/proc/self/status").map_err(|e| e.to_string())?;
        let field = |key: &str| -> crate::Result<u64> {
            status
                .lines()
                .find(|l| l.starts_with(key))
                .and_then(|l| l.split_whitespace().nth(1))
                .ok_or("missing RSS field")?
                .parse()
                .map_err(|_| "invalid RSS field".into())
        };
        Ok(Resources {
            user_seconds: usage.ru_utime.tv_sec as f64 + usage.ru_utime.tv_usec as f64 / 1e6,
            system_seconds: usage.ru_stime.tv_sec as f64 + usage.ru_stime.tv_usec as f64 / 1e6,
            rss_kib: field("VmRSS:")?,
            hwm_kib: field("VmHWM:")?,
        })
    }
    #[cfg(not(target_os = "linux"))]
    {
        Err("experiment resource accounting requires Linux".into())
    }
}
