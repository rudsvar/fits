#[test]
fn test_fibonacci() {
    let content = std::fs::read_to_string("examples/fibonacci.fs").unwrap();
    fits::run(&content).unwrap();
}
