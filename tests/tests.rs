use fits::{expr::RuntimeError, typecheck::TypeError};

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

#[test]
fn variables_in_block_leave_scope() {
    let input = r#"
        {
            let inBlock = 0;
        }
        println(inBlock);
    "#;
    let program = fits::parse(input).unwrap();
    assert_eq!(
        Err(TypeError::NotDefined("inBlock".to_string())),
        fits::typecheck(&program)
    );
}

#[test]
fn invalid_assert_fails() {
    let input = r#"
        assert(false);
    "#;
    assert_eq!(
        Err(RuntimeError::AssertionError("false".to_string()).into()),
        fits::run(input)
    );
}

#[test]
fn values_can_change_in_scope() {
    let input = r#"
        let a = 0;
        {
            a = 10;
        }
        assert(a == 10);
    "#;
    fits::run(input).unwrap();
}
