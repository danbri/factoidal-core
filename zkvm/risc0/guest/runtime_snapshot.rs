//! Link only the bytes already read, hashed and approved by build.rs.
//! The digest is the caller's SHA-256 of those exact bytes, never a path supplied
//! by the runtime manifest. Existing snapshots are compared and never replaced.
use std::{fs, io::{self, Write}, path::{Path, PathBuf}};

fn invalid(message: &str) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message)
}

pub fn snapshot_verified_archive(out: &Path, digest: &str, bytes: &[u8]) -> io::Result<PathBuf> {
    if digest.len() != 64 || !digest.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)) {
        return Err(invalid("snapshot name requires the computed lowercase SHA-256"));
    }
    let directory = out.join(format!("factoidal-runtime-{digest}"));
    let mut builder = fs::DirBuilder::new();
    #[cfg(unix)] {
        use std::os::unix::fs::DirBuilderExt;
        builder.mode(0o700);
    }
    match builder.create(&directory) {
        Ok(()) => {},
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            if !fs::symlink_metadata(&directory)?.file_type().is_dir() {
                return Err(invalid("snapshot directory was replaced"));
            }
        }
        Err(error) => return Err(error),
    }
    #[cfg(unix)] {
        use std::os::unix::fs::PermissionsExt;
        if fs::symlink_metadata(&directory)?.permissions().mode() & 0o077 != 0 {
            return Err(invalid("snapshot directory must remain private"));
        }
    }
    let archive = directory.join("libfactoidal_ask.a");
    let mut options = fs::OpenOptions::new();
    options.write(true).create_new(true);
    #[cfg(unix)] {
        use std::os::unix::fs::OpenOptionsExt;
        options.mode(0o600);
    }
    match options.open(&archive) {
        Ok(mut file) => {
            file.write_all(bytes)?;
            file.sync_all()?;
            let mut permissions = file.metadata()?.permissions();
            permissions.set_readonly(true);
            file.set_permissions(permissions)?;
        }
        Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {
            let metadata = fs::symlink_metadata(&archive)?;
            if !metadata.file_type().is_file() || !metadata.permissions().readonly() || fs::read(&archive)? != bytes {
                return Err(invalid("existing snapshot differs; refusing to replace it"));
            }
        }
        Err(error) => return Err(error),
    }
    Ok(directory)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicUsize, Ordering};
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    struct Temporary(PathBuf);
    impl Temporary {
        fn new() -> Self {
            let path = std::env::temp_dir().join(format!("factoidal-runtime-snapshot-{}-{}",
                std::process::id(), NEXT.fetch_add(1, Ordering::Relaxed)));
            fs::create_dir(&path).unwrap();
            Self(path)
        }
    }
    impl Drop for Temporary {
        fn drop(&mut self) { fs::remove_dir_all(&self.0).unwrap(); }
    }
    fn digest() -> String { "a".repeat(64) }

    #[test]
    fn source_changes_cannot_change_the_link_snapshot() {
        let temp = Temporary::new();
        let source = temp.0.join("mutable.a");
        fs::write(&source, b"the verified archive").unwrap();
        let verified = fs::read(&source).unwrap();
        fs::write(&source, b"replacement before snapshot").unwrap();
        let dir = snapshot_verified_archive(&temp.0, &digest(), &verified).unwrap();
        fs::write(&source, b"replacement after snapshot").unwrap();
        let archive = dir.join("libfactoidal_ask.a");
        assert_eq!(fs::read(&archive).unwrap(), verified);
        assert!(archive.metadata().unwrap().permissions().readonly());
        assert!(dir.ends_with(format!("factoidal-runtime-{}", digest())));
    }

    #[test]
    fn identical_snapshot_can_be_reused_but_never_replaced() {
        let temp = Temporary::new();
        let dir = snapshot_verified_archive(&temp.0, &digest(), b"original").unwrap();
        assert_eq!(snapshot_verified_archive(&temp.0, &digest(), b"original").unwrap(), dir);
        assert!(snapshot_verified_archive(&temp.0, &digest(), b"replacement").is_err());
        assert_eq!(fs::read(dir.join("libfactoidal_ask.a")).unwrap(), b"original");
    }

    #[test]
    fn path_like_or_noncanonical_digest_is_refused() {
        let temp = Temporary::new();
        for value in ["../outside".to_string(), "a".repeat(63), "a".repeat(65), "A".repeat(64), "g".repeat(64)] {
            assert!(snapshot_verified_archive(&temp.0, &value, b"archive").is_err());
        }
        assert_eq!(fs::read_dir(&temp.0).unwrap().count(), 0);
    }

    #[cfg(unix)]
    #[test]
    fn symlink_snapshot_cannot_alias_a_mutable_archive() {
        use std::os::unix::fs::{symlink, PermissionsExt};
        let temp = Temporary::new();
        let dir = temp.0.join(format!("factoidal-runtime-{}", digest()));
        fs::create_dir(&dir).unwrap();
        fs::set_permissions(&dir, fs::Permissions::from_mode(0o700)).unwrap();
        let source = temp.0.join("mutable.a");
        fs::write(&source, b"same bytes").unwrap();
        symlink(&source, dir.join("libfactoidal_ask.a")).unwrap();
        assert!(snapshot_verified_archive(&temp.0, &digest(), b"same bytes").is_err());
        assert_eq!(fs::read(source).unwrap(), b"same bytes");
    }

    #[cfg(unix)]
    #[test]
    fn symlink_snapshot_directory_is_refused() {
        use std::os::unix::fs::symlink;
        let temp = Temporary::new();
        let elsewhere = temp.0.join("elsewhere");
        fs::create_dir(&elsewhere).unwrap();
        symlink(&elsewhere, temp.0.join(format!("factoidal-runtime-{}", digest()))).unwrap();
        assert!(snapshot_verified_archive(&temp.0, &digest(), b"archive").is_err());
        assert_eq!(fs::read_dir(elsewhere).unwrap().count(), 0);
    }
}
