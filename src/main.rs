mod algebra;
use algebra::Clause;
use std::collections::HashMap;

fn main() {
    println!("{}", algebra::negate_type(&"mixed".to_string()));

    let mut formula = vec![];

    let mut possibilities = HashMap::new();

    possibilities.insert("$a".to_string(), vec!["Foo".to_string()]);
    possibilities.insert("$b".to_string(), vec!["Bar".to_string()]);

    formula.push(Clause::new(&possibilities, 1, 1, None, None, None, None));

    let mut possibilities = HashMap::new();

    possibilities.insert("$c".to_string(), vec!["Baz".to_string()]);
    possibilities.insert("$d".to_string(), vec!["Bat".to_string()]);

    formula.push(Clause::new(&possibilities, 1, 1, None, None, None, None));

    let negated = algebra::negate_formula(&formula);

    for clause in negated.unwrap() {
        println!("{}", clause.to_string());
    }

    println!("Hello, world!");
}
