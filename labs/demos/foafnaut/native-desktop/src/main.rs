mod engine;

use std::error::Error;
use std::path::Path;
use std::time::Instant;

use engine::{DeviceLimits, Engine, Session};
use serde_json::{Value, json};

const FIXTURE: &str = include_str!("../click.html");
const URL: &str = "file:///click.html";
const SIZE: [u32; 2] = [480, 240];

fn start(page: &mut Session<'_>) -> Result<Value, Box<dyn Error>> {
    let plan = page.call(
        "",
        &json!({"op":"scriptPlan","setting":"","scripts":1,"host":"native"}),
        SIZE,
    )?;
    if plan["engine"] != "bubblepop" || plan["run"] != true {
        return Err(format!("unexpected fresh page-script setting: {plan}").into());
    }
    let turn = page.call(
        FIXTURE,
        &json!({
            "op":"scriptSession","action":"start","url":URL,"resources":[],
            "engine":plan["engine"],"width":SIZE[0],"height":SIZE[1]
        }),
        SIZE,
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

fn frame(page: &mut Session<'_>, commands: &Value) -> Result<Value, Box<dyn Error>> {
    let request = json!({"url":URL,"commands":commands,"checks":false});
    let answer = page.call(FIXTURE, &request, SIZE)?;
    if answer["data"].as_array().is_none_or(Vec::is_empty) {
        return Err("native engine returned no scene data".into());
    }
    Ok(answer)
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
    let first_start = start(&mut first)?;
    let second_start = start(&mut second)?;
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

    println!(
        "{}",
        json!({
            "engine":"bubblepop","sessions":2,"clickChangedScene":true,
            "secondSessionUnchanged":true,"firstSceneMs":first_frame_ms
        })
    );
    Ok(())
}

fn check_render_plan(library: &Path) -> Result<(), Box<dyn Error>> {
    let engine = Engine::open(library)?;
    let mut session = engine.session()?;
    let start = start(&mut session)?;
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

fn main() -> Result<(), Box<dyn Error>> {
    const USAGE: &str = "Usage: foafnaut-native-desktop LIBWEB_RENDER [--check-render-plan]";
    let mut args = std::env::args_os().skip(1);
    let library = args.next().ok_or(USAGE)?;
    match (args.next().as_deref(), args.next()) {
        (None, None) => smoke(Path::new(&library)),
        (Some(flag), None) if flag == "--check-render-plan" => {
            check_render_plan(Path::new(&library))
        }
        _ => Err(USAGE.into()),
    }
}
