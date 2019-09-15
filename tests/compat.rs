use std::io;
use std::process::Command;

#[test]
fn test_noflags() -> io::Result<()> {
    let commands = compile_commands("noflags")?;
    for command in &commands {
        let output = Command::new(command).output()?;
        assert!(output.status.success());
        assert_eq!(output.stdout, b"");

        let output = Command::new(command).args(&["foo", "bar", "-f"]).output()?;
        assert!(output.status.success());
        assert_eq!(output.stdout, b"foo\nbar\n-f\n");

        let output = Command::new(command).args(&["--", "-f", "foo"]).output()?;
        assert!(output.status.success());
        assert_eq!(output.stdout, b"-f\nfoo\n");

        let output = Command::new(command).args(&["-", "foo"]).output()?;
        assert!(output.status.success());
        assert_eq!(output.stdout, b"-\nfoo\n");

        let output = Command::new(command).args(&["-f", "foo"]).output()?;
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("flag provided but not defined"));

        let output = Command::new(command).args(&["--f", "foo"]).output()?;
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("flag provided but not defined"));

        let output = Command::new(command).args(&["---f", "foo"]).output()?;
        assert!(!output.status.success());
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(stderr.contains("bad flag syntax"));
    }

    Ok(())
}

fn compile_commands(name: &str) -> io::Result<[String; 2]> {
    let go_cmdname = format!("examples/{}-go", name);
    let output = Command::new("go")
        .args(&["build", "-o"])
        .arg(&go_cmdname)
        .arg(&format!("examples/{}.go", name))
        .output()?;
    assert!(output.status.success());

    let rust_cmdname = format!("target/debug/examples/{}", name);
    let output = Command::new("cargo")
        .args(&["build", "--example", name])
        .output()?;
    assert!(output.status.success());

    Ok([rust_cmdname, go_cmdname])
}
