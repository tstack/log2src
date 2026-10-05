use insta_cmd::assert_cmd_snapshot;
use std::path::Path;

mod common_settings;

#[test]
fn basic() -> Result<(), Box<dyn std::error::Error>> {
    let mut cmd = common_settings::CommandGuard::new()?;
    let source = Path::new("tests").join("kotlin");
    let log = Path::new("tests")
        .join("resources")
        .join("kotlin")
        .join("basic.log");
    cmd.arg("-d")
        .arg(source.to_str().expect("test case source code exists"))
        .arg("-l")
        .arg(log.to_str().expect("test case log exists"))
        .arg("-f")
        .arg(
            "^(?<timestamp>\\d{4}-\\d{2}-\\d{2} \\d{2}:\\d{2}:\\d{2}) (?<thread>\\d+) (?<body>.*)$",
        );

    assert_cmd_snapshot!(cmd.cmd);
    Ok(())
}
