mod clause;

pub use clause::Clause;
use rand::Rng;
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

pub fn group_impossibilities(clauses: &Vec<Clause>) -> Result<Vec<Clause>, String> {
    let mut complexity = 1;

    let mut clauses = clauses.clone();

    let mut seed_clauses = vec![];

    let clause = clauses.pop();

    if clause == None {
        panic!("there should be clauses")
    }

    let clause = clause.unwrap();

    if !clause.wedge {
        if clause.impossibilities == None {
            panic!("Clause should have impossibilities");
        }

        let impossibilities = clause.impossibilities.unwrap();

        for (var, impossible_types) in impossibilities.iter() {
            for impossible_type in impossible_types.iter() {
                let mut seed_clause_possibilities = HashMap::new();
                seed_clause_possibilities.insert(var.clone(), vec![impossible_type.clone()]);

                let seed_clause = Clause::new(
                    &seed_clause_possibilities,
                    clause.creating_conditional_id,
                    clause.creating_object_id,
                    None,
                    None,
                    None,
                    None,
                );

                seed_clauses.push(seed_clause);

                complexity += 1;
            }
        }

        if clauses.len() == 0 || seed_clauses.len() == 0 {
            return Ok(seed_clauses);
        }
    }

    while clauses.len() > 0 {
        let clause = clauses.pop();

        if clause == None {
            panic!("impossible");
        }

        let clause = clause.unwrap();

        let mut new_clauses = vec![];

        for grouped_clause in seed_clauses.clone().iter() {
            let clause_impossibilities = clause.impossibilities.clone();

            if clause_impossibilities == None {
                panic!("Should not be possible");
            }

            for (var, impossible_types) in clause_impossibilities.unwrap() {
                for impossible_type in impossible_types.iter() {
                    let mut new_clause_possibilities = grouped_clause.possibilities.clone();

                    let grouped_clause_possibilities = grouped_clause.possibilities.get(&var);

                    if let Some(x) = grouped_clause_possibilities {
                        let mut new_insert_value = x.clone();
                        if !new_insert_value.contains(impossible_type) {
                            new_insert_value.push(impossible_type.clone());
                        }
                        new_clause_possibilities.insert(var.clone(), new_insert_value.clone());

                        let mut removed_indexes = HashSet::new();

                        let new_len = new_insert_value.len();

                        for i in 0..new_len {
                            for j in i + 1..new_len {
                                let ith = new_insert_value[i].clone();
                                let jth = new_insert_value[j].clone();

                                if ith == "!".to_string() + &jth || jth == "!".to_string() + &ith {
                                    removed_indexes.insert(i);
                                    removed_indexes.insert(j);
                                }
                            }
                        }

                        if removed_indexes.len() > 0 {
                            let mut new_possibilities = vec![];
                            let mut i = 0;

                            for val in new_insert_value {
                                if !removed_indexes.contains(&i) {
                                    new_possibilities.push(val);
                                }
                                i += 1;
                            }

                            if new_possibilities.len() == 0 {
                                new_clause_possibilities.remove(&var);
                            } else {
                                new_clause_possibilities.insert(var.clone(), new_possibilities);
                            }
                        }
                    } else {
                        new_clause_possibilities.insert(var.clone(), vec![impossible_type.clone()]);
                    }

                    if new_clause_possibilities.len() == 0 {
                        continue;
                    }

                    new_clauses.push(Clause::new(
                        &new_clause_possibilities,
                        grouped_clause.creating_conditional_id,
                        clause.creating_object_id,
                        Some(false),
                        Some(true),
                        Some(true),
                        None,
                    ));

                    complexity += 1;

                    if complexity > 20000 {
                        return Err("Complicated".to_string());
                    }
                }
            }
        }

        seed_clauses = new_clauses.clone();
    }

    return Ok(seed_clauses);
}

pub fn combine_ored_clauses(
    left_clauses: &Vec<Clause>,
    right_clauses: &Vec<Clause>,
    conditional_object_id: u32,
) -> Vec<Clause> {
    let mut clauses = vec![];

    let mut all_wedges = true;
    let mut has_wedge = false;

    for left_clause in left_clauses {
        for right_clause in right_clauses {
            all_wedges = all_wedges && (left_clause.wedge && right_clause.wedge);
            has_wedge = has_wedge || (left_clause.wedge && right_clause.wedge);
        }
    }

    if all_wedges {
        return vec![Clause::new(
            &HashMap::new(),
            conditional_object_id,
            conditional_object_id,
            Some(true),
            None,
            None,
            None,
        )];
    }

    for left_clause in left_clauses {
        'right: for right_clause in right_clauses {
            if left_clause.wedge && right_clause.wedge {
                // handled below
                continue;
            }

            let mut possibilities: HashMap<String, Vec<String>> = HashMap::new();

            let can_reconcile = !left_clause.wedge
                && !right_clause.wedge
                && left_clause.reconcilable
                && right_clause.reconcilable;

            for (var, possible_types) in left_clause.possibilities.iter() {
                if right_clause.possibilities.contains_key(var) {
                    continue;
                }

                if let Some(var_possibilities) = possibilities.get(var) {
                    let mut var_possibilities = var_possibilities.clone();
                    let mut possible_types = possible_types.clone();
                    var_possibilities.append(&mut possible_types);
                    possibilities.insert(var.clone(), var_possibilities);
                } else {
                    possibilities.insert(var.clone(), possible_types.clone());
                }
            }

            for (var, possible_types) in right_clause.possibilities.iter() {
                if let Some(var_possibilities) = possibilities.get(var) {
                    let mut var_possibilities = var_possibilities.clone();
                    let mut possible_types = possible_types.clone();
                    var_possibilities.append(&mut possible_types);
                    possibilities.insert(var.clone(), var_possibilities);
                } else {
                    possibilities.insert(var.clone(), possible_types.clone());
                }
            }

            if left_clauses.len() > 1 || right_clauses.len() > 1 {
                for (var, p) in possibilities.clone().iter() {
                    let mut p = p.clone();
                    p.dedup();
                    possibilities.insert(var.clone(), p);
                }
            }

            for (_, var_possibilities) in possibilities.iter() {
                if var_possibilities.len() == 2 {
                    if var_possibilities[0] == "!".to_string() + &var_possibilities[1]
                        || var_possibilities[1] == "!".to_string() + &var_possibilities[0]
                    {
                        continue 'right;
                    }
                }
            }

            let creating_conditional_id;

            if right_clause.creating_conditional_id == left_clause.creating_conditional_id {
                creating_conditional_id = right_clause.creating_conditional_id;
            } else {
                creating_conditional_id = conditional_object_id;
            }

            let is_generated = right_clause.generated
                || left_clause.generated
                || left_clauses.len() > 1
                || right_clauses.len() > 1;

            clauses.push(Clause::new(
                &possibilities,
                creating_conditional_id,
                creating_conditional_id,
                Some(false),
                Some(can_reconcile),
                Some(is_generated),
                None,
            ))
        }
    }

    if has_wedge {
        clauses.push(Clause::new(
            &HashMap::new(),
            conditional_object_id,
            conditional_object_id,
            Some(true),
            None,
            None,
            None,
        ));
    }

    return clauses;
}

// Negates a set of clauses
// negateClauses([$a || $b]) => !$a && !$b
// negateClauses([$a, $b]) => !$a || !$b
// negateClauses([$a, $b || $c]) =>
//   (!$a || !$b) &&
//   (!$a || !$c)
// negateClauses([$a, $b || $c, $d || $e || $f]) =>
//   (!$a || !$b || !$d) &&
//   (!$a || !$b || !$e) &&
//   (!$a || !$b || !$f) &&
//   (!$a || !$c || !$d) &&
//   (!$a || !$c || !$e) &&
//   (!$a || !$c || !$f)
pub fn negate_formula(clauses: &Vec<Clause>) -> Result<Vec<Clause>, String> {
    let clauses: Vec<Clause> = clauses
        .iter()
        .filter(|clause| clause.reconcilable)
        .cloned()
        .collect();

    if clauses.len() == 0 {
        let mut rng = rand::thread_rng();

        let n2: u32 = rng.gen();
        return Ok(vec![Clause::new(
            &HashMap::new(),
            n2,
            n2,
            Some(true),
            None,
            None,
            None,
        )]);
    }

    let mut better_clauses = vec![];

    for clause in clauses {
        better_clauses.push(clause.calculate_negation());
    }

    let impossible_clauses = group_impossibilities(&better_clauses);

    if let Err(x) = impossible_clauses {
        return Err(x);
    }

    let impossible_clauses = impossible_clauses.unwrap();

    if impossible_clauses.len() == 0 {
        let mut rng = rand::thread_rng();

        let n2: u32 = rng.gen();
        return Ok(vec![Clause::new(
            &HashMap::new(),
            n2,
            n2,
            Some(true),
            None,
            None,
            None,
        )]);
    }

    let negated = simplify_cnf(&impossible_clauses);

    if negated.len() == 0 {
        let mut rng = rand::thread_rng();

        let n2: u32 = rng.gen();
        return Ok(vec![Clause::new(
            &HashMap::new(),
            n2,
            n2,
            Some(true),
            None,
            None,
            None,
        )]);
    }

    return Ok(negated);
}
