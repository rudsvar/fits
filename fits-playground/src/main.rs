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

#[component]
fn App() -> impl IntoView {
    let (mode, set_mode) = create_signal(Mode::Parse);
    let (error, set_error) = create_signal(String::new());
    let (input, set_input) = create_signal(String::new());
    let (output, set_output) = create_signal(String::new());

    let init = "let person = { name: String, age: Int };";
    set_input(init.to_string());
    set_output(
        fits::parse(init)
            .map(|ast| format!("{:#?}", ast))
            .unwrap_or_default(),
    );

    view! {
        <h1>Fits Playground</h1>
        <div style="display: flex; gap: 40px;">
            <textarea
                on:input=move |ev| {
                    let text = event_target_value(&ev);
                    match mode.get() {
                        Mode::Parse => {
                            match fits::parse(&text) {
                                Ok(ast) => {
                                    set_output(format!("{:#?}", ast));
                                    set_error(String::new());
                                },
                                Err(err) => {
                                    set_error(err.to_string());
                                    set_output(String::new());
                                }
                            }
                        },
                        Mode::Type => {
                            match fits::parse(&text) {
                                Ok(program) => {
                                    match fits::typecheck(&program) {
                                        Ok(()) => {
                                            set_output("Typecheck successful".to_string());
                                            set_error(String::new());
                                        },
                                        Err(err) => {
                                            set_error(err.to_string());
                                            set_output(String::new());
                                        }
                                    }
                                },
                                Err(err) => {
                                    set_error(err.to_string());
                                    set_output(String::new());
                                }
                            }

                        },
                        Mode::Run => {
                            // Parse, typecheck, execute, and print env
                            match fits::parse(&text) {
                                Ok(program) => {
                                    match fits::typecheck(&program) {
                                        Ok(()) => {
                                            let mut env = fits::env::Env::default();
                                            match fits::statement::exec(program.stmts, &mut env) {
                                                Ok(()) => {
                                                    // Pretty-print the environment
                                                    let env_pretty = env
                                                        .iter()
                                                        .map(|(k, v)| format!("{}: {}", k, v))
                                                        .collect::<Vec<_>>()
                                                        .join("\n");
                                                    set_output(env_pretty);
                                                    set_error(String::new());
                                                },
                                                Err(err) => {
                                                    set_error(err.to_string());
                                                    set_output(String::new());
                                                }
                                            }
                                        },
                                        Err(err) => {
                                            set_error(err.to_string());
                                            set_output(String::new());
                                        }
                                    }
                                },
                                Err(err) => {
                                    set_error(err.to_string());
                                    set_output(String::new());
                                }
                            }
                        },
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
                        }
                    />
                    <label>"Parse"</label>
                </div>
                <div>
                    <input type="radio" name="mode" value="type"
                        on:input=move |_| {
                            set_mode(Mode::Type);
                        }
                    />
                    <label>"Type"</label>
                </div>
                <div>
                    <input type="radio" name="mode" value="run"
                        on:input=move |_| {
                            set_mode(Mode::Run);
                        }
                    />
                    <label>"Run"</label>
                </div>
            </form>
            <textarea>{output}</textarea>
        </div>
        <p style="color: red">{error}</p>
    }
}
