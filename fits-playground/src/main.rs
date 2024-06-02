use leptos::*;

fn main() {
    console_error_panic_hook::set_once();
    leptos::mount_to_body(|| view! { <App/> })
}

enum Mode {
    Parse,
    Type,
    Run,
}

#[component]
fn App() -> impl IntoView {
    let (mode, set_mode) = create_signal(Mode::Parse);
    let (error, set_error) = create_signal(String::new());
    let (output, set_output) = create_signal(String::new());

    view! {
        <h1>Fits Playground</h1>
        <textarea
            on:input=move |ev| {
                let text = event_target_value(&ev);
                match fits::parse(&text) {
                    Ok(ast) => set_output(format!("{:#?}", ast)),
                    Err(err) => {
                        set_error(err.to_string());
                        set_output(String::new());
                    }
                }
            }
        />
        {error}
        <div>
            <input type="radio" name="mode" value="parse" checked=true
                on:input=move |_| {
                    set_mode(Mode::Parse);
                }
            />
            <label>"Parse"</label>
            <input type="radio" name="mode" value="type"
                on:input=move |_| {
                    set_mode(Mode::Type);
                }
            />
            <label>"Type"</label>
            <input type="radio" name="mode" value="run"
                on:input=move |_| {
                    set_mode(Mode::Run);
                }
            />
            <label>"Run"</label>
        </div>
        <textarea>{output}</textarea>
    }
}
