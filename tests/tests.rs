#[test]
fn examples_run() {
    for f in std::fs::read_dir("examples").unwrap() {
        let f = f.unwrap();
        let path = f.path();
        println!("Running {:?}", path);
        if path.extension().unwrap() == "fs" {
            let content = std::fs::read_to_string(&path).unwrap();
            fits::run(&content).unwrap();
        }
    }
}
