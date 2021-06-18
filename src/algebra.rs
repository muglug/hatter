mod clause;

use clause::Clause;
use std::collections::HashMap;
use std::collections::HashSet;
use std::hash::Hash;

pub fn negate_type(type_text: &String) -> String {
    if type_text == "mixed" {
        return type_text.clone();
    }

    if &type_text[0..1] == "!" {
        return String::from(&type_text[1..]);
    }

    return "!".to_string() + &type_text;
}

pub fn negate_types(
    all_types: HashMap<String, Vec<Vec<String>>>,
) -> HashMap<String, Vec<Vec<String>>> {
    let mut new_all_types: HashMap<String, Vec<Vec<String>>> = HashMap::new();

    'outer: for (var, anded_types) in all_types.iter() {
        if anded_types.len() > 1 {
            let mut new_anded_types: Vec<String> = Vec::new();

            for orred_types in anded_types.iter() {
                if orred_types.len() > 1 {
                    break 'outer;
                }

                new_anded_types.push(negate_type(&orred_types[0]));
            }

            new_all_types.insert(var.to_string(), vec![new_anded_types]);
            break;
        }

        let mut new_orred_types: Vec<Vec<String>> = Vec::new();

        for orred_type in anded_types[0].iter() {
            new_orred_types.push(vec![negate_type(orred_type)]);
        }

        new_all_types.insert(var.to_string(), new_orred_types);
    }

    return new_all_types;
}

fn keys_match<T: Eq + Hash, U, V>(map1: &HashMap<T, U>, map2: &HashMap<T, V>) -> bool {
    map1.len() == map2.len() && map1.keys().all(|k| map2.contains_key(k))
}

// This is a very simple simplification heuristic
// for CNF formulae.
//
// It simplifies formulae:
//     ($a) && ($a || $b) => $a
//     (!$a) && (!$b) && ($a || $b || $c) => $c
//
// @param list<Clause>  $clauses
//
// @return list<Clause>
//
// @psalm-pure
//
pub fn simplify_cnf(clauses: &Vec<Clause>) -> Vec<Clause> {
    let clause_count = clauses.len();

    if clause_count > 50 {
        let mut all_has_unknown = true;

        for clause in clauses.iter() {
            let mut clause_has_unknown = false;

            for (key, _) in clause.possibilities.iter() {
                if &key[0..1] == "*" {
                    clause_has_unknown = true;
                    break;
                }
            }

            if !clause_has_unknown {
                all_has_unknown = false;
                break;
            }
        }

        if all_has_unknown {
            return clauses.clone();
        }
    }

    let mut unique_clauses: HashSet<Clause> = HashSet::new();

    for clause in clauses.iter() {
        unique_clauses.insert(clause.clone());
    }

    // remove impossible types
    'outer: for clause_a in unique_clauses.clone().iter() {
        if !clause_a.reconcilable || clause_a.wedge {
            continue;
        }

        let mut is_clause_a_simple: bool = true;

        if clause_a.possibilities.len() != 1 {
            is_clause_a_simple = false;
        } else {
            for (_, var_possibilities) in clause_a.possibilities.clone() {
                if var_possibilities.len() != 1 {
                    is_clause_a_simple = false;
                }
            }
        }

        if !is_clause_a_simple {
            'inner: for clause_b in unique_clauses.clone().iter() {
                if clause_a == clause_b || !clause_b.reconcilable || clause_b.wedge {
                    continue;
                }

                if keys_match(&clause_a.possibilities, &clause_b.possibilities) {
                    let mut opposing_keys = vec![];

                    for (key, a_possibilities) in clause_a.possibilities.iter() {
                        let b_possibilities = &clause_b.possibilities[key];

                        if &a_possibilities == &b_possibilities {
                            continue;
                        }

                        if a_possibilities.len() == 1
                            && b_possibilities.len() == 1
                            && (a_possibilities[0] == "!".to_string() + &b_possibilities[0]
                                || b_possibilities[0] == "!".to_string() + &a_possibilities[0])
                        {
                            opposing_keys.push(key.clone());
                            continue;
                        }

                        continue 'inner;
                    }

                    if opposing_keys.len() == 1 {
                        unique_clauses.remove(clause_a);

                        let maybe_new_clause = clause_a.remove_possibilities(&opposing_keys[0]);

                        if maybe_new_clause == None {
                            continue 'outer;
                        }

                        unique_clauses.insert(maybe_new_clause.unwrap());
                    }
                }
            }

            continue;
        }

        // only iterates over one single possibility
        for (clause_var, var_possibilities) in clause_a.possibilities.iter() {
            let only_type = &var_possibilities[0];
            let negated_clause_type = negate_type(only_type);

            for clause_b in unique_clauses.clone().iter() {
                if clause_a == clause_b || !clause_b.reconcilable || clause_b.wedge {
                    continue 'outer;
                }

                let maybe_matching_clause_possibilities = clause_b.possibilities.get(clause_var);

                if let Some(matching_clause_possibilities) = maybe_matching_clause_possibilities {
                    if matching_clause_possibilities.contains(&negated_clause_type) {
                        let mut clause_var_possibilities = vec![];

                        for x in matching_clause_possibilities.iter() {
                            if x != &negated_clause_type {
                                clause_var_possibilities.push(x.clone());
                            }
                        }

                        unique_clauses.remove(clause_b);

                        if clause_var_possibilities.len() == 0 {
                            let maybe_updated_clause = clause_b.remove_possibilities(&clause_var);

                            if let Some(x) = maybe_updated_clause {
                                unique_clauses.insert(x);
                            }
                        } else {
                            let mut updated_clause = clause_b.clone();

                            updated_clause
                                .possibilities
                                .insert(clause_var.clone(), clause_var_possibilities);

                            unique_clauses.insert(updated_clause);
                        }
                    }
                }
            }
        }
    }

    let mut simplified_clauses = vec![];

    for clause_a in unique_clauses.clone().iter() {
        let mut is_redundant = false;

        for clause_b in unique_clauses.iter() {
            if clause_a == clause_b || !clause_b.reconcilable || clause_b.wedge || clause_a.wedge {
                continue;
            }

            if clause_a.contains(clause_b) {
                is_redundant = true;
                break;
            }
        }

        if !is_redundant {
            simplified_clauses.push(clause_a.clone());
        }
    }

    return simplified_clauses;
}
