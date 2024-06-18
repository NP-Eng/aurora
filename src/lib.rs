
mod reader;

macro_rules! TEST_DATA_PATH {
    () => {
        concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/test_data/{}",
        )
    };
}

pub(crate) use TEST_DATA_PATH;
 