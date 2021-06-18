use std::collections::HashMap;
extern crate rustc_serialize;
use std::hash::{Hash, Hasher};

#[derive(Clone)]
pub struct Clause {
    pub creating_conditional_id: i32,
    pub creating_object_id: i32,

    // An array of strings of the form
    // [
    //     '$a' => ['falsy'],
    //     '$b' => ['!falsy'],
    //     '$c' => ['!null'],
    //     '$d' => ['string', 'int']
    // ]
    //
    // represents the formula
    // !$a || $b || $c !== null || is_string($d) || is_int($d)
    pub possibilities: HashMap<String, Vec<String>>,

    // An array of things that are not true
    // [
    //     '$a' => ['!falsy'],
    //     '$b' => ['falsy'],
    //     '$c' => ['null'],
    //     '$d' => ['!string', '!int']
    // ]
    //
    // represents the formula
    // $a && !$b && $c === null && !is_string($d) && !is_int($d)
    pub impossibilities: Option<HashMap<String, Vec<String>>>,
    pub wedge: bool,
    pub reconcilable: bool,
    pub generated: bool,
    pub redefined_vars: HashMap<String, bool>,
}

impl PartialEq for Clause {
    fn eq(&self, other: &Self) -> bool {
        if self.wedge || other.wedge || !self.reconcilable || !other.reconcilable {
            return self.wedge == other.wedge
                && self.creating_object_id == other.creating_object_id;
        }

        return self.possibilities == other.possibilities;
    }
}
impl Eq for Clause {}

impl Hash for Clause {
    fn hash<H: Hasher>(&self, state: &mut H) {
        if self.wedge || !self.reconcilable {
            self.wedge.hash(state);
            self.creating_object_id.hash(state);
        } else {
            let mut sorted_possibilities: Vec<(String, Vec<String>)> = vec![];

            for (var_id, var_possibilities) in self.possibilities.iter() {
                sorted_possibilities.push((var_id.to_string(), var_possibilities.clone()));
            }

            sorted_possibilities.sort_by(|a, b| b.0.cmp(&a.0));

            sorted_possibilities.hash(state);
        }
    }
}

impl Clause {
    fn new(
        possibilities: HashMap<String, Vec<String>>,
        creating_conditional_id: i32,
        creating_object_id: i32,
        wedge: Option<bool>,
        reconcilable: Option<bool>,
        generated: Option<bool>,
        redefined_vars: Option<HashMap<String, bool>>,
    ) -> Clause {
        let mut sorted_possibilities = HashMap::new();

        for (var_id, var_possibilities) in possibilities.iter() {
            let mut var_possibilities = var_possibilities.clone();
            var_possibilities.dedup();
            var_possibilities.sort();

            sorted_possibilities.insert(var_id.clone(), var_possibilities);
        }

        return Clause {
            possibilities: sorted_possibilities,
            impossibilities: None,
            creating_conditional_id,
            creating_object_id,
            wedge: match wedge {
                None => false,
                Some(x) => x,
            },
            reconcilable: match reconcilable {
                None => true,
                Some(x) => x,
            },
            generated: match generated {
                None => false,
                Some(x) => x,
            },
            redefined_vars: match redefined_vars {
                None => HashMap::new(),
                Some(x) => x,
            },
        };
    }

    pub fn remove_possibilities(&self, var_id: &String) -> Option<Clause> {
        let mut possibilities = self.possibilities.clone();

        possibilities.remove(var_id);

        if possibilities.len() == 0 {
            return None;
        }

        return Some(Clause {
            possibilities,
            impossibilities: None,
            creating_conditional_id: self.creating_conditional_id,
            creating_object_id: self.creating_object_id,
            wedge: self.wedge,
            reconcilable: self.reconcilable,
            generated: self.generated,
            redefined_vars: self.redefined_vars.clone(),
        });
    }

    pub fn contains(&self, other_clause: &Self) -> bool {
        if other_clause.possibilities.len() > self.possibilities.len() {
            return false;
        }

        for (var, possible_types) in other_clause.possibilities.iter() {
            let local_possibilities = self.possibilities.get(var);

            if local_possibilities == None {
                return false;
            }

            for i in possible_types {
                if !local_possibilities.unwrap().contains(&i) {
                    return false;
                }
            }
        }

        return true;
    }
}