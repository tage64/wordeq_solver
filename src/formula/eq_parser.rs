use pest::Parser;
use pest_derive::Parser;

use super::*;

#[derive(Parser)]
#[grammar = "eq.pest"]
pub struct EqParser;

impl EqParser {
  pub fn parse_to_formula(text: &str) -> anyhow::Result<Formula> {
    let mut lines = EqParser::parse(Rule::file, text)?
      .next()
      .unwrap()
      .into_inner();
    let _vars = lines.next().unwrap().into_inner().next().unwrap();
    let _terminals = lines.next().unwrap().into_inner().next().unwrap();
    let mut parsed_equation = lines.next().unwrap().into_inner();
    let lhs = parsed_equation.next().unwrap().as_str();
    let rhs = parsed_equation.next().unwrap().as_str();
    Ok(Formula::from_strs(&[(lhs, rhs)], char::is_uppercase))
  }
}
