#[macro_export]
macro_rules! boxed {
    ($val:expr) => {
        Box::new($val)
    };
}
