
mod reader;

#[cfg(test)]
macro_rules! TEST_DATA_PATH {
    () => {
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/test-data/{}",
        )
    };
}

#[cfg(test)]
pub(crate) use TEST_DATA_PATH;
 