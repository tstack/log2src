use insta_cmd::assert_cmd_snapshot;
use std::path::Path;

mod common_settings;

#[test]
fn statements_in_file() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = common_settings::CommandGuard::new("statements")?;
    cmd.arg("-d").arg("examples").arg("--file").arg("basic.rs");

    assert_cmd_snapshot!(cmd.cmd);
    Ok(())
}

#[test]
fn statements_summary() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = common_settings::CommandGuard::new("statements")?;
    let source = Path::new("tests").join("java");
    cmd.arg("-d")
        .arg(source.to_str().expect("test case path is valid"))
        .arg("--summary");

    assert_cmd_snapshot!(cmd.cmd);
    Ok(())
}

#[test]
fn statements_by_level() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = common_settings::CommandGuard::new("statements")?;
    let source = Path::new("tests").join("java");
    cmd.arg("-d")
        .arg(source.to_str().expect("test case path is valid"))
        .arg("--level")
        .arg("info");

    assert_cmd_snapshot!(cmd.cmd);
    Ok(())
}

#[test]
fn calls() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = common_settings::CommandGuard::new("calls")?;
    cmd.arg("-d").arg("examples");

    assert_cmd_snapshot!(cmd.cmd);
    Ok(())
}

#[test]
fn statements_missing_file() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = common_settings::CommandGuard::new("statements")?;
    cmd.arg("-d").arg("examples").arg("--file").arg("nope.rs");

    assert_cmd_snapshot!(cmd.cmd);
    Ok(())
}

#[test]
fn locate() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = common_settings::CommandGuard::new("locate")?;
    let source = Path::new("tests").join("java");
    cmd.arg("-d")
        .arg(source.to_str().expect("test case path is valid"))
        .arg(r"C:\build\src\BasicWithLog.java")
        .arg("other/BasicWithLog.java");

    assert_cmd_snapshot!(cmd.cmd);
    Ok(())
}

#[test]
fn match_message() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = common_settings::CommandGuard::new("match")?;
    let source = Path::new("examples").join("basic.rs");
    cmd.arg("-d")
        .arg(source.to_str().expect("test case path is valid"))
        .arg("--message")
        .arg("Hello from foo i=42");

    assert_cmd_snapshot!(cmd.cmd);
    Ok(())
}

#[test]
fn missing_source() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = common_settings::CommandGuard::new("statements")?;

    assert_cmd_snapshot!(cmd.cmd);
    Ok(())
}

#[test]
fn missing_source_dir() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = common_settings::CommandGuard::new("cache")?;
    cmd.arg("update").arg("-d").arg("does-not-exist");

    assert_cmd_snapshot!(cmd.cmd);
    Ok(())
}

#[test]
fn statements_by_lang() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = common_settings::CommandGuard::new("statements")?;
    cmd.arg("-d")
        .arg("tests")
        .arg("--lang")
        .arg("KOTLIN,cpp")
        .arg("--summary");

    assert_cmd_snapshot!(cmd.cmd);
    Ok(())
}

#[test]
fn match_message_with_start() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = common_settings::CommandGuard::new("match")?;
    cmd.arg("-d")
        .arg("examples")
        .arg("--message")
        .arg("hello")
        .arg("--start")
        .arg("1");

    assert_cmd_snapshot!(cmd.cmd);
    Ok(())
}

#[test]
fn cache_clear_nested_source() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = common_settings::CommandGuard::new("cache")?;
    let source = Path::new("tests").join("java");
    cmd.arg("update")
        .arg("-d")
        .arg("tests")
        .arg("-d")
        .arg(&source);
    assert!(cmd.cmd.output()?.status.success());

    // The entry is for `tests`, which contains `tests/java`.
    let mut clear = cmd.sibling("cache")?;
    clear.arg("clear").arg("-v").arg("-d").arg(&source);
    let output = clear.output()?;
    assert!(output.status.success());
    assert!(String::from_utf8(output.stderr)?.contains("Removed "));

    let mut list = cmd.sibling("cache")?;
    list.arg("list");
    assert!(list.output()?.stdout.is_empty());
    Ok(())
}
