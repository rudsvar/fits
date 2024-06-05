use std::error::Error;

use leptos::*;

fn main() {
    console_error_panic_hook::set_once();
    leptos::mount_to_body(|| view! { <App/> })
}

#[derive(Clone, Copy, Debug)]
enum Mode {
    Parse,
    Type,
    Run,
}

fn parse_to_string(input: &str) -> Result<String, Box<dyn Error>> {
    let result = fits::parse(input)
        .map(|ast| format!("{:#?}", ast))
        .map_err(|e| e.to_string())?;
    Ok(result)
}

fn typecheck_to_string(input: &str) -> Result<String, Box<dyn Error>> {
    let program = fits::parse(input)?;
    fits::typecheck(&program)?;
    Ok("Typecheck successful".to_string())
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
    let (mode, set_mode) = create_signal(Mode::Parse);
    let (input, set_input) = create_signal(String::new());
    let (output, set_output) = create_signal(String::new());

    let init = "let person = { name: String, age: Int };";
    set_input(init.to_string());
    set_output(parse_to_string(init).expect("Invalid init"));

    view! {
        <h1>Fits Playground</h1>
        <div style="display: flex; gap: 40px;">
            <textarea
                on:input=move |ev| {
                    let text = event_target_value(&ev);
                    let result = match mode.get() {
                        Mode::Parse => parse_to_string(&text),
                        Mode::Type => typecheck_to_string(&text),
                        Mode::Run => run_to_string(&text),
                    };
                    match result {
                        Ok(result) => {
                            set_input(text);
                            set_output(result);
                        }
                        Err(e) => {
                            set_input(text);
                            set_output(e.to_string());
                        }
                    }
                }
            >
            {input}
            </textarea>
            <form style="display: flex; flex-direction: column">
                <div>
                    <input type="radio" name="mode" value="parse" checked=true
                        on:input=move |_| {
                            set_mode(Mode::Parse);
                            match parse_to_string(&input.get()) {
                                Ok(result) => set_output(result),
                                Err(e) => set_output(e.to_string()),
                            }
                        }
                    />
                    <label>"Parse"</label>
                </div>
                <div>
                    <input type="radio" name="mode" value="type"
                        on:input=move |_| {
                            set_mode(Mode::Type);
                            match typecheck_to_string(&input.get()) {
                                Ok(result) => set_output(result),
                                Err(e) => set_output(e.to_string()),
                            }
                        }
                    />
                    <label>"Type"</label>
                </div>
                <div>
                    <input type="radio" name="mode" value="run"
                        on:input=move |_| {
                            set_mode(Mode::Run);
                            match run_to_string(&input.get()) {
                                Ok(result) => set_output(result),
                                Err(e) => set_output(e.to_string()),
                            }
                        }
                    />
                    <label>"Run"</label>
                </div>
            </form>
            <textarea>{output}</textarea>
        </div>
    }
}
