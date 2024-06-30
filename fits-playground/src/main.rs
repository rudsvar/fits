use std::error::Error;

use leptos::*;

fn main() {
    console_error_panic_hook::set_once();
    leptos::mount_to_body(|| view! { <App/> })
}

struct FakeStdout {
    output: String,
}

impl std::io::Write for FakeStdout {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.output.push_str(&String::from_utf8_lossy(buf));
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fn run_to_string(input: &str) -> Result<String, Box<dyn Error>> {
    let mut env = fits::env::Env::default();
    let program = fits::parse(input)?;
    fits::typecheck(&program)?;
    let mut output = FakeStdout {
        output: String::new(),
    };
    fits::statement::exec(program.stmts, &mut env, &mut output)?;
    Ok(output.output)
}

#[component]
fn App() -> impl IntoView {
    let init = "let person = { name: \"Hello\", age: 3 };\nprintln(person);";
    let (input, set_input) = create_signal(init.to_string());
    let (ast, set_ast) = create_signal(fits::parse(init).unwrap());
    let (output, set_output) = create_signal(String::new());
    let (error, set_error) = create_signal(String::new());

    view! {
        <h1>Programming Languages Playground</h1>
        <div class="main">
            <div class="input_and_ast">
                <div class="input">
                    <h3>Input</h3>
                    <textarea
                        on:input=move |ev| {
                            let text = event_target_value(&ev);
                            set_input(text.clone());
                            match fits::parse(&text) {
                                Ok(ast) => {
                                    set_ast(ast);
                                    set_error("".to_string());
                                }
                                Err(e) => {
                                    set_error(e.to_string());
                                }
                            }
                        }
                    >
                    {input}
                    </textarea>
                </div>
                <div class="ast">
                    <h3>AST</h3>
                    <textarea
                        on:input=move |ev| {
                            let text = event_target_value(&ev).clone();
                            match serde_json::from_str::<fits::Program>(&text) {
                                Ok(ast) => {
                                    set_input(ast.to_string());
                                    set_ast(ast);
                                    set_error("".to_string());
                                }
                                Err(e) => {
                                    set_error(e.to_string());
                                }
                            }
                        }
                    >
                    {move || serde_json::to_string_pretty(&ast).unwrap()}
                    </textarea>
                </div>
            </div>
            <div class="error">
                {error}
            </div>
            <div class="run">
                <button type="button" name="mode" value="Run"
                    on:click=move |_|
                    match run_to_string(&input.get()) {
                        Ok(result) => {
                            set_error("".to_string());
                            set_output(result);
                        }
                        Err(e) => {
                            set_error(e.to_string());
                        }
                    }
                >
                Run
                </button>
            </div>
            <h2>Output</h2>
            <div class="output">
                {output}
            </div>
        </div>
    }
}
