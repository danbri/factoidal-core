mod engine;
mod gpu;
mod window;

use std::error::Error;
use std::path::Path;
use std::time::{Duration, Instant};

use engine::{DeviceLimits, Engine, Session};
use gpu::{Gpu, Scene};
use serde_json::{Value, json};
use window::Window;

const FIXTURE: &str = include_str!("../click.html");
const URL: &str = "file:///click.html";
const SIZE: [u32; 2] = [480, 240];

fn start(page: &mut Session<'_>, size: [u32; 2]) -> Result<Value, Box<dyn Error>> {
    start_document(page, FIXTURE, size)
}

fn start_document(
    page: &mut Session<'_>,
    html: &str,
    size: [u32; 2],
) -> Result<Value, Box<dyn Error>> {
    let plan = page.call(
        "",
        &json!({"op":"scriptPlan","setting":"","scripts":1,"host":"native"}),
        size,
    )?;
    if plan["engine"] != "bubblepop" || plan["run"] != true {
        return Err(format!("unexpected fresh page-script setting: {plan}").into());
    }
    let turn = page.call(
        html,
        &json!({
            "op":"scriptSession","action":"start","url":URL,"resources":[],
            "engine":plan["engine"],"width":size[0],"height":size[1]
        }),
        size,
    )?;
    check_turn(&turn)?;
    Ok(turn)
}

fn check_turn(turn: &Value) -> Result<(), Box<dyn Error>> {
    if turn["session"].as_u64().is_none() || turn["errors"] != json!([]) {
        return Err(format!("script turn failed: {turn}").into());
    }
    Ok(())
}

// The engine gives both numbers in its own clock. The host only maps elapsed
// monotonic time to that clock and reports it back when Lean asks for a turn.
struct Wake {
    origin: Instant,
    initial_clock: u64,
    clock: u64,
    due: Option<u64>,
}

impl Wake {
    fn new(turn: &Value) -> Result<Self, Box<dyn Error>> {
        let mut wake = Self {
            origin: Instant::now(),
            initial_clock: 0,
            clock: 0,
            due: None,
        };
        wake.observe(turn)?;
        wake.initial_clock = wake.clock;
        Ok(wake)
    }

    fn observe(&mut self, turn: &Value) -> Result<(), Box<dyn Error>> {
        self.clock = turn["clock"].as_u64().ok_or("script answer has no clock")?;
        self.due = match turn.get("nextWake") {
            Some(Value::Null) => None,
            Some(value) => Some(value.as_u64().ok_or("invalid script wake time")?),
            None => return Err("script answer has no wake time".into()),
        };
        Ok(())
    }

    fn elapsed(&self) -> u64 {
        self.initial_clock
            .saturating_add(u64::try_from(self.origin.elapsed().as_millis()).unwrap_or(u64::MAX))
    }

    fn wait(&self) -> Duration {
        let wait = self
            .due
            .map_or(250, |due| due.saturating_sub(self.elapsed()).min(250));
        Duration::from_millis(wait)
    }

    fn advance(
        &mut self,
        page: &mut Session<'_>,
        session: &Value,
        size: [u32; 2],
    ) -> Result<Option<Value>, Box<dyn Error>> {
        let elapsed = self.elapsed();
        if !self.due.is_some_and(|due| elapsed >= due) {
            return Ok(None);
        }
        let turn = page.call(
            "",
            &json!({
                "op":"scriptSession","action":"advance","session":session,
                "ms":elapsed.saturating_sub(self.clock)
            }),
            size,
        )?;
        check_turn(&turn)?;
        self.observe(&turn)?;
        Ok(Some(turn))
    }
}

fn check_timer(engine: &Engine) -> Result<(), Box<dyn Error>> {
    let mut page = engine.session()?;
    let start = start_document(
        &mut page,
        "<!doctype html><script>setTimeout(() => console.log('timer fired'), 20);</script>",
        SIZE,
    )?;
    let mut wake = Wake::new(&start)?;
    if wake.due.is_none() || start["logs"] != json!([]) {
        return Err("engine did not schedule the fixture timer".into());
    }
    let deadline = Instant::now() + Duration::from_secs(2);
    loop {
        std::thread::sleep(wake.wait());
        if let Some(turn) = wake.advance(&mut page, &start["session"], SIZE)? {
            if turn["logs"] == json!(["timer fired"]) && wake.due.is_none() {
                return Ok(());
            }
            return Err(format!("unexpected timer turn: {turn}").into());
        }
        if Instant::now() >= deadline {
            return Err("engine timer did not become due".into());
        }
    }
}

fn check_audio(library: &Path) -> Result<(), Box<dyn Error>> {
    if std::env::var("FOAFNAUT_AUDIO_SINK").as_deref() != Ok("null") {
        return Err("run the audio smoke with FOAFNAUT_AUDIO_SINK=null".into());
    }
    const AUDIO_PAGE: &str = r#"<!doctype html>
<style>body{margin:0} button{width:200px;height:80px}</style>
<button id="go">Play</button>
<script>
const ctx = new AudioContext();
document.getElementById('go').addEventListener('click', () => {
  const tone = new OscillatorNode(ctx, {frequency: 440});
  tone.connect(ctx.destination);
  tone.onended = () => ctx.close().then(() => console.log('audio closed'));
  tone.start();
  tone.stop(ctx.currentTime + 0.10);
  ctx.resume().then(() => console.log('audio running'));
});
</script>"#;
    let engine = Engine::open(library)?;
    let mut page = engine.session()?;
    let start = start_document(&mut page, AUDIO_PAGE, SIZE)?;
    let mut wake = Wake::new(&start)?;
    if wake.due.is_some() {
        return Err("audio scheduled a wake before activation".into());
    }
    let target = page.call(
        AUDIO_PAGE,
        &json!({
            "op":"nodeAt","url":URL,"commands":start["commands"],"x":30,"y":30
        }),
        SIZE,
    )?;
    let node = target["node"]
        .as_u64()
        .ok_or("engine found no audio button")?;
    let click = page.call(
        "",
        &json!({
            "op":"scriptSession","action":"click","session":start["session"],"node":node
        }),
        SIZE,
    )?;
    check_turn(&click)?;
    wake.observe(&click)?;

    let mut samples_taken = false;
    let mut running = false;
    let mut turn = click;
    let deadline = Instant::now() + Duration::from_secs(5);
    while Instant::now() < deadline {
        let audio = page.call("", &json!({"op":"audioRuns"}), SIZE)?;
        let items = audio["items"]
            .as_array()
            .ok_or("engine returned no audio runs")?;
        samples_taken |= items
            .iter()
            .any(|item| item["read"].as_u64().unwrap_or(0) > 0);
        let logs = turn["logs"].as_array().ok_or("script answer has no logs")?;
        running |= logs.iter().any(|line| line == "audio running");
        if logs.iter().any(|line| line == "audio closed") {
            if running && samples_taken {
                println!(
                    "{}",
                    json!({"audioSink":"null","activated":true,"consumedFrames":true,"closed":true})
                );
                return Ok(());
            }
            return Err("the audio closed without reporting running and delivering frames".into());
        }
        std::thread::sleep(wake.wait());
        if let Some(next) = wake.advance(&mut page, &start["session"], SIZE)? {
            turn = next;
        }
    }
    Err(format!("audio smoke timed out after turn {turn}").into())
}

fn frame_at(
    page: &mut Session<'_>,
    commands: &Value,
    size: [u32; 2],
) -> Result<Value, Box<dyn Error>> {
    let request = json!({"url":URL,"commands":commands,"checks":false});
    let answer = page.call(FIXTURE, &request, size)?;
    if answer["data"].as_array().is_none_or(Vec::is_empty) {
        return Err("native engine returned no scene data".into());
    }
    Ok(answer)
}

fn frame(page: &mut Session<'_>, commands: &Value) -> Result<Value, Box<dyn Error>> {
    frame_at(page, commands, SIZE)
}

fn click_once(page: &mut Session<'_>, turn: &Value) -> Result<Value, Box<dyn Error>> {
    let hit = page.call(
        FIXTURE,
        &json!({
            "op":"nodeAt","url":URL,"commands":turn["commands"],"x":30,"y":30
        }),
        SIZE,
    )?;
    let node = hit["node"].as_u64().ok_or("engine found no click target")?;
    let click = page.call(
        "",
        &json!({
            "op":"scriptSession","action":"click","session":turn["session"],"node":node
        }),
        SIZE,
    )?;
    check_turn(&click)?;
    if click["logs"] != json!(["click 1"]) {
        return Err(format!("unexpected script state before its first click: {click}").into());
    }
    Ok(click)
}

fn smoke(library: &Path) -> Result<(), Box<dyn Error>> {
    let started = Instant::now();
    let engine = Engine::open(library)?;
    let mut first = engine.session()?;
    let mut second = engine.session()?;
    let first_start = start(&mut first, SIZE)?;
    let second_start = start(&mut second, SIZE)?;
    let before = frame(&mut first, &first_start["commands"])?;
    let first_frame_ms = started.elapsed().as_secs_f64() * 1000.0;
    let other_before = frame(&mut second, &second_start["commands"])?;
    if before["data"] != other_before["data"] {
        return Err("identical pages in separate sessions produced different scenes".into());
    }

    let click = click_once(&mut first, &first_start)?;
    let after = frame(&mut first, &click["commands"])?;
    if click["changed"] != true || before["data"] == after["data"] {
        return Err("the scripted click did not change the scene".into());
    }

    let other = second.call(
        "",
        &json!({
            "op":"scriptSession","action":"advance","session":second_start["session"],"ms":0
        }),
        SIZE,
    )?;
    check_turn(&other)?;
    if other["changed"] != false {
        return Err("the script in the second session changed without a click".into());
    }
    drop(first);
    let other_after = frame(&mut second, &second_start["commands"])?;
    if other_before["data"] != other_after["data"] {
        return Err("the second session's scene changed after closing the first".into());
    }

    let second_click = click_once(&mut second, &second_start)?;
    let second_clicked = frame(&mut second, &second_click["commands"])?;
    if after["data"] != second_clicked["data"] {
        return Err("the second session produced a different first click".into());
    }

    check_timer(&engine)?;
    println!(
        "{}",
        json!({
            "engine":"bubblepop","sessions":2,"clickChangedScene":true,"timerFired":true,
            "secondSessionUnchanged":true,"firstSceneMs":first_frame_ms
        })
    );
    Ok(())
}

fn check_render_plan(library: &Path) -> Result<(), Box<dyn Error>> {
    let engine = Engine::open(library)?;
    let mut session = engine.session()?;
    let start = start(&mut session, SIZE)?;
    let scene = frame(&mut session, &start["commands"])?;
    let floats = u32::try_from(scene["data"].as_array().ok_or("missing scene data")?.len())?;
    let limits = DeviceLimits {
        uniform_bytes: 16,
        texture_dimension: 4096,
        storage_bytes: 16 * 1024 * 1024,
        buffer_bytes: 16 * 1024 * 1024,
    };
    let plan = engine.render_plan(c"svg-window", c"bgra8unorm", SIZE, floats, &limits)?;
    // This is a smoke-test assertion for fixed inputs. The renderer will execute
    // the engine's returned descriptors and commands.
    if plan["abi"] != "lean-render-plan-v1"
        || plan["mode"] != "svg-window"
        || plan["format"] != "bgra8unorm"
        || plan["width"] != SIZE[0]
        || plan["height"] != SIZE[1]
        || plan["uniform"]["bindingType"] != "read-only-storage"
        || plan["uniform"]["floatCount"] != floats
        || plan["surface"]["usage"] != json!(["render-attachment"])
        || plan.get("readback").is_some()
        || plan["commands"]
            != json!([
                "beginPass",
                "setPipeline",
                "setBindGroup",
                "draw",
                "endPass",
                "submit",
                "present"
            ])
    {
        return Err(format!("unexpected window plan: {plan}").into());
    }
    let limited = DeviceLimits {
        storage_bytes: 0,
        ..limits
    };
    match engine.render_plan(c"svg-window", c"bgra8unorm", SIZE, floats, &limited) {
        Err(error) if error.to_string() == "storage bytes exceed device limit" => {}
        result => return Err(format!("expected a storage limit refusal, got {result:?}").into()),
    }
    println!(
        "{}",
        json!({"nativeRenderPlan": "svg-window", "storageLimitRefused": true})
    );
    Ok(())
}

fn show_fixture(library: &Path, window_library: &Path) -> Result<(), Box<dyn Error>> {
    let engine = Engine::open(library)?;
    let mut page = engine.session()?;
    let window = Window::open(window_library, SIZE)?;
    let mut gpu = Gpu::open(&window)?;
    let mut size = SIZE;
    // Both bridges queue the initial physical backing size on window creation.
    while let Some(event) = window.next() {
        if event.kind == 1 && event.a > 0 && event.b > 0 {
            size = [u32::try_from(event.a)?, u32::try_from(event.b)?];
        }
    }
    let start = start(&mut page, size)?;
    let session = &start["session"];
    let mut wake = Wake::new(&start)?;
    let mut commands = start["commands"].clone();
    let mut dirty = true;
    let mut down = false;
    let mut last_pointer = None;

    loop {
        if dirty {
            let scene: Scene = serde_json::from_value(frame_at(&mut page, &commands, size)?)?;
            gpu.present(&engine, scene)?;
            dirty = false;
        }
        window.wait_and_pump(wake.wait());
        while let Some(event) = window.next() {
            if event.kind == 6 {
                return Ok(());
            }
            if event.kind == 1 && event.a > 0 && event.b > 0 {
                let next = [u32::try_from(event.a)?, u32::try_from(event.b)?];
                if next != size {
                    size = next;
                    let resize = page.call(
                        "",
                        &json!({
                            "op":"scriptSession","action":"resize","session":session,
                            "width":size[0],"height":size[1]
                        }),
                        size,
                    )?;
                    check_turn(&resize)?;
                    wake.observe(&resize)?;
                    if let Some(updated) = resize.get("commands") {
                        commands = updated.clone();
                    }
                    dirty = true;
                }
                continue;
            }
            let kind = match event.kind {
                2 if (event.flags >> 16) & 3 == 0 => {
                    down = true;
                    "down"
                }
                3 => "move",
                4 if (event.flags >> 16) & 3 == 0 => {
                    down = false;
                    "up"
                }
                14 => {
                    down = false;
                    "cancel"
                }
                _ => continue,
            };
            let hit = if kind == "cancel" {
                last_pointer.take().unwrap_or(Value::Null)
            } else {
                page.call(
                    FIXTURE,
                    &json!({
                        "op":"nodeAt","url":URL,"commands":commands,
                        "x":event.a.max(0),"y":event.b.max(0)
                    }),
                    size,
                )?
            };
            let Some(node) = hit["node"].as_u64() else {
                continue;
            };
            let mut request = hit.clone();
            request["op"] = json!("scriptSession");
            request["action"] = json!("pointer");
            request["session"] = session.clone();
            request["kind"] = json!(kind);
            request["node"] = json!(node);
            request["button"] = json!(0);
            request["buttons"] = json!(u32::from(down));
            request["pressure"] = json!(if down { 0.5 } else { 0.0 });
            request["pointerType"] = json!("mouse");
            if down {
                last_pointer = Some(hit);
            }
            let turn = page.call("", &request, size)?;
            check_turn(&turn)?;
            wake.observe(&turn)?;
            if let Some(updated) = turn.get("commands") {
                commands = updated.clone();
                dirty = true;
            }
        }
        if let Some(turn) = wake.advance(&mut page, session, size)?
            && let Some(updated) = turn.get("commands")
        {
            commands = updated.clone();
            dirty = true;
        }
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    const USAGE: &str = "Usage: foafnaut-native-desktop LIBWEB_RENDER [--check-render-plan | --check-audio | --window LIBNATIVE_WINDOW]";
    let mut args = std::env::args_os().skip(1);
    let library = args.next().ok_or(USAGE)?;
    match (args.next().as_deref(), args.next(), args.next()) {
        (None, None, None) => smoke(Path::new(&library)),
        (Some(flag), None, None) if flag == "--check-render-plan" => {
            check_render_plan(Path::new(&library))
        }
        (Some(flag), None, None) if flag == "--check-audio" => check_audio(Path::new(&library)),
        (Some(flag), Some(window), None) if flag == "--window" => {
            show_fixture(Path::new(&library), Path::new(&window))
        }
        _ => Err(USAGE.into()),
    }
}
