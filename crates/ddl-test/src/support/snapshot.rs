use difference::{Changeset, Difference as Diff};
use std::path::{Path, PathBuf};
use std::{fmt, fs, io, str};

pub fn compare(out_path: &Path, found_bytes: &[u8]) -> Result<(), SnapshotError> {
    use std::env;

    let found_str = std::str::from_utf8(found_bytes).map_err(SnapshotError::OutputUtf8)?;
    let is_bless = env::var("DDL_BLESS").is_ok();

    if out_path.exists() {
        let expected_string = read_snapshot(&out_path)?;
        let changeset = Changeset::new(&expected_string, found_str, "\n");

        if !changeset.diffs.iter().all(is_same_diff) {
            if is_bless {
                bless_snapshot(out_path, found_str)?;
            } else {
                return Err(SnapshotError::UnexpectedChangesFound(
                    out_path.to_owned(),
                    changeset,
                ));
            }
        }
    } else {
        if is_bless {
            bless_snapshot(out_path, found_str)?;
        } else {
            return Err(SnapshotError::ExistingSnapshotNotFound(out_path.to_owned()));
        }
    }

    Ok(())
}

fn is_same_diff(diff: &Diff) -> bool {
    match diff {
        Diff::Same(_) => true,
        _ => false,
    }
}

fn read_snapshot(out_path: &Path) -> Result<String, SnapshotError> {
    fs::read_to_string(&out_path)
        .map_err(|error| SnapshotError::ReadSnapshot(out_path.to_owned(), error))
}

fn bless_snapshot(out_path: &Path, found_str: &str) -> Result<(), SnapshotError> {
    fs::create_dir_all(out_path.parent().unwrap())
        .and_then(|()| fs::write(&out_path, found_str))
        .map_err(|error| SnapshotError::WriteSnapshot(out_path.to_owned(), error))
}

pub enum SnapshotError {
    OutputUtf8(str::Utf8Error),
    ReadSnapshot(PathBuf, io::Error),
    WriteSnapshot(PathBuf, io::Error),
    ExistingSnapshotNotFound(PathBuf),
    UnexpectedChangesFound(PathBuf, Changeset),
}

impl fmt::Display for SnapshotError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SnapshotError::OutputUtf8(error) => writeln!(f, "actual output not utf8: {}", error)?,
            SnapshotError::ReadSnapshot(path, error) => {
                writeln!(f, "error reading snapshot `{}`: {}", path.display(), error)?;
            }
            SnapshotError::WriteSnapshot(path, error) => {
                writeln!(f, "error writing snapshot `{}`: {}", path.display(), error)?;
            }
            SnapshotError::ExistingSnapshotNotFound(path) => {
                writeln!(f, "existing snapshot `{}` not found", path.display())?;
                writeln!(f)?;
                writeln!(
                    f,
                    "note: Run with `DDL_BLESS=1` environment variable to regenerate."
                )?;
                writeln!(f)?;
            }
            SnapshotError::UnexpectedChangesFound(path, changeset) => {
                writeln!(f, "changes found in snapshot `{}`: ", path.display())?;
                writeln!(f)?;
                for diff in &changeset.diffs {
                    match diff {
                        // TODO: Colored diffs
                        Diff::Same(data) => write_lines(f, "      ", data)?,
                        Diff::Add(data) => write_lines(f, "    + ", data)?,
                        Diff::Rem(data) => write_lines(f, "    - ", data)?,
                    }
                }
                writeln!(f)?;
                writeln!(
                    f,
                    "note: Run with `DDL_BLESS=1` environment variable to regenerate."
                )?;
                writeln!(f)?;
            }
        }
        Ok(())
    }
}

fn write_lines(writer: &mut impl fmt::Write, prefix: &str, data: &str) -> fmt::Result {
    let mut last = 0;
    for (index, space) in data.match_indices('\n') {
        write!(writer, "{}{}{}", prefix, &data[last..index], space)?;
        last = index + space.len();
    }
    writeln!(writer, "{}{}", prefix, &data[last..])?;
    Ok(())
}
