use std::process::Command;

pub fn light_up_screen() {
    // Define the script path and arguments.
    let script_path = "scripts/adjust_screen_brightness.sh";
    let args = ["1.0", "HDMI-0", "0.5"];

    // Use Command to execute the script with arguments.
    let output = Command::new(script_path).args(&args).output();

    match output {
        Ok(output) => {
            if !output.status.success() {
                // Print stderr if the command failed.
                panic!(
                    "Script execution failed: {}",
                    String::from_utf8_lossy(&output.stderr)
                );
            }
        }
        Err(e) => {
            panic!("Failed to execute script: {}", e)
        }
    }
}
