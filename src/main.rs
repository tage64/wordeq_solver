use std::fs;
use std::io::{self, Read};
use std::path::PathBuf;
use std::time::Duration;

use anyhow::{Result, anyhow};
use clap::Parser as _;
use flexi_logger::Logger;
use smt_str_solver::*;

#[derive(clap::Parser)]
#[command(version, about, author)]
struct Cli {
  /// Read a .eq file, otherwise read equations line by line from STDIN where uppercase letters are
  /// variables.
  eq_file: Option<PathBuf>,
  /// Try for at most this number of seconds.
  #[arg(short, long)]
  timeout: Option<f64>,
  /// Be super verbose and print lots of trace debug info.
  #[arg(short, long)]
  debug: bool,
}

fn main() -> Result<()> {
  let cli = Cli::parse();
  let log_level = if cli.debug { "trace" } else { "info" };
  Logger::try_with_env_or_str(log_level)
    .unwrap()
    .format(|f, _, r| write!(f, "{}", r.args()))
    .log_to_stdout()
    .start()
    .unwrap();
  let formula = if let Some(eq_file) = cli.eq_file {
    Formula::from_eq_file(&fs::read_to_string(eq_file)?)?
  } else {
    let mut stdin = String::new();
    io::stdin().lock().read_to_string(&mut stdin)?;
    Formula::from_strs(
      &stdin
        .lines()
        .map(|line| {
          line
            .split_once(" = ")
            .ok_or_else(|| anyhow!("The LHS and RHS should be separated by \" = \""))
        })
        .collect::<Result<Vec<_>>>()?,
      char::is_uppercase,
    )
  };
  let (mut solution, stats) = solve(
    formula.clone(),
    CollectNodeStats::from_now(cli.timeout.map(Duration::from_secs_f64)),
  );
  let stats = stats.finished();
  println!("{solution}; {stats}");
  if let Sat(x) = &mut solution {
    x.assert_correct();
    println!("{}", x.display());
  }
  Ok(())
}
