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
