//! usage:
//!
//! husky-developer --session <session-yaml-path>
use clap::Parser;
use husky_session::Session;
use std::path::PathBuf;

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    /// Path to the session YAML file
    #[arg(long)]
    session: Option<PathBuf>,
}

fn main() {
    let cli = Cli::parse();

    if let Some(session_path) = cli.session {
        // Add session loading logic here
        let session = Session::load_from_yaml_file_path(&session_path);
        println!("session = {session:?}");
        run(session);
    }
}

fn run(session: Session) {
    use husky_devtime::Devtime;
    use husky_devtime::IsTracetime;
    use husky_standard_devsoul::StandardDevsoul;

    let devtime: Devtime<StandardDevsoul> = Devtime::new(&session.dir, None).expect("valid");
    devtime.serve_traces(format!("localhost:{}", session.port))
}
