use std::collections::{HashMap, VecDeque};

use rustc_hash::FxBuildHasher;

use crate::*;

type Unifier = HashMap<Slot, AppliedId>;

fn compute_mgus<L: Language, N: Analysis<L>>
    (eg: &EGraph<L,N>, a: &AppliedId, b: &AppliedId, mu: &Unifier, visited: &HashSet<(AppliedId, AppliedId)>)
     -> (Vec<HashMap<Slot, AppliedId>>, HashSet<(AppliedId, AppliedId)>) {

    let mut l : Vec<HashMap<Slot, AppliedId>> = Vec::new();
    if visited.contains(&(a.clone(),b.clone())) || visited.contains(&(b.clone(),a.clone())) {
        return (l, visited.clone());
    }
    let mut visited_bis = visited.clone();
    visited_bis.insert((a.clone(),b.clone()));

    for na in eg.enodes_applied(&a) {
        for nb in eg.enodes_applied(&b) {
            match &na.to_syntax()[0] { // the binder case is not handled at the moment
                SyntaxElem::String(f) => {
                    match &nb.to_syntax()[0] {
                        SyntaxElem::String(g) => {
                            if f==g {
                                // Dec
                                let mut eqs : Vec<(&AppliedId, &AppliedId)> = Vec::new();
                                let mut i = 0;
                                // i am quite unsure on which variables they are defined here... I must check that!
                                for c in (&na).applied_id_occurrences() {
                                    let mut j = 0;
                                    for c_bis in (&nb).applied_id_occurrences() {
                                        if i==j {
                                            eqs.push((c,c_bis));
                                            break;
                                        } else { // j < i
                                            j += 1;
                                        }
                                    }
                                    i += 1;
                                }
                                let l_bis = dec_case(&eg, &mut eqs, vec![(mu.clone(), visited_bis.clone())]);
                                for (sigma,_) in l_bis {
                                    if !l.contains(&sigma){
                                        l.push(sigma.clone());
                                    }
                                }
                            } else {
                                // DecFail
                                continue;  
                            };
                        },
                        SyntaxElem::Slot(x) => {
                            match mu.get(x) {
                                Some(c) => {
                                    // LazyRep'
                                    let (l_bis, _) = &compute_mgus(eg, a, c, mu, &visited_bis);
                                    for el in l_bis {
                                        if !l.contains(el) {
                                            l.push(el.clone());
                                        }
                                    }
                                },
                                None => {
                                    if !occ(eg, mu, a, x) {
                                        // Bind'
                                        let mut sigma = mu.clone();
                                        sigma.insert(*x, a.clone());
                                        if !l.contains(&sigma) {
                                            l.push(sigma);
                                        }
                                    } else {
                                        // Check'
                                        continue;
                                    }
                                }
                            }
                        },
                        SyntaxElem::AppliedId(_) => {
                            // "is there really something to do?"
                            continue;
                        }
                    }
                },
                SyntaxElem::Slot(y) => {
                    match &nb.to_syntax()[0] {
                        SyntaxElem::String(_) => {
                            match mu.get(y) {
                                Some(c) => {
                                    // LazyRep
                                    let (l_bis, _) = &compute_mgus(eg, c, b, mu, &visited_bis);
                                    //l.extend_from_slice(l_bis);
                                    for el in l_bis {
                                        if !l.contains(&el) {
                                            l.push(el.clone());
                                        }
                                    }
                                },
                                None => {
                                    if !occ(eg, mu, b, y) {
                                        // Bind
                                        let mut sigma = mu.clone();
                                        sigma.insert(*y, b.clone());
                                        if !l.contains(&sigma){
                                            l.push(sigma);
                                        }
                                    } else {
                                        // Check
                                        continue;
                                    }
                                }
                            }
                        },
                        SyntaxElem::Slot(x) => {
                            if x == y {
                                // Triv
                                if !l.contains(mu) {
                                    l.push(mu.clone());
                                }
                            } else {
                                match mu.get(y) {
                                    Some(c) => {
                                        // LazyRep
                                        let (l_bis, _) = &compute_mgus(eg, c, b, mu, &visited_bis);
                                        //l.extend_from_slice(l_bis);
                                        for el in l_bis {
                                            if !l.contains(&el) {
                                                l.push(el.clone());
                                            }
                                        }
                                    },
                                    None => {
                                        if !occ(eg, mu, b, y) {
                                            // Bind
                                            let mut sigma = mu.clone();
                                            sigma.insert(*y, b.clone());
                                            if !l.contains(&sigma) {
                                                l.push(sigma);
                                            }
                                        } else {
                                            // Check
                                            continue;
                                        }
                                    }
                                }
                            }
                        },
                        SyntaxElem::AppliedId(_) => {
                            // "is there really something to do?"
                            continue;
                        }
                    }
                },
                SyntaxElem::AppliedId(_) => {
                    // "is there really something to do?"
                    continue;
                }
            }
        }
    }
    return (l, visited_bis);
}

fn dec_case<L: Language, N: Analysis<L>>
    (eg: &EGraph<L,N>, equalities: &mut Vec<(&AppliedId, &AppliedId)>, pairs: Vec<(Unifier, HashSet<(AppliedId, AppliedId)>)>)
    -> Vec<(Unifier, HashSet<(AppliedId, AppliedId)>)> {
    if equalities.len() == 0 {
        let mut pairs_cp = Vec::new();
        for (mu, v) in pairs {
            pairs_cp.push((mu.clone(), v.clone()));
        }
        return pairs_cp;
    }
    let (c,c_bis) = equalities.pop().unwrap();
    let mut l = Vec::new();
    for (mu, visited) in pairs {
        let (res, v_bis) = compute_mgus(eg, c, c_bis, &mu, &visited);
        for el in res {
            l.push((el, v_bis.clone()));
        }
    }
    return dec_case(eg, equalities, l);
}

fn occ<L: Language, N: Analysis<L>>
    (_eg: &EGraph<L,N>, mu: &Unifier, c: &AppliedId, v: &Slot) -> bool {
    for x in c.slots() {
        match mu.get(&x) {
            Some(c_bis) => {
                if c_bis.slots().contains(v) {
                    return true;
                }
            },
            None => {
                continue;
            }
        }
    }
    return false;
}

fn apply_unifier_class<L: Language>
    (eg: &EGraph<L,AstSizeAnalysis>, mu: &Unifier, c0: &AppliedId) -> (AppliedId, bool) 
{
    todo!()
}

fn rec_parents<L: Language, N: Analysis<L>>
    (eg: &mut EGraph<L,N>, c0: &AppliedId) -> Vec<AppliedId>
{
    todo!()
}

pub(crate) fn merge<L: Language>
    (eg: &mut EGraph<L,AstSizeAnalysis>, max: u64, wo: &mut VecDeque<AppliedId>, us: &mut VecDeque<AppliedId>, c0: &AppliedId) -> bool 
{
    for c1 in wo.clone() {
        // quite unsure about this beginning
        let hash_builder = rustc_hash::FxBuildHasher::from(FxBuildHasher {});
        let empty = HashMap::new();
        let visited = HashSet::with_hasher(hash_builder);
        let (mgus,_) = compute_mgus(eg, c0, &c1, &empty, &visited);
        for mu in mgus {
            let (c_new, added_new_node) = apply_unifier_class(eg, &mu, c0);
            eg.rebuild();
            // satisfiability of the class tested by the analyses
            let analysis = *eg.analysis_data(c_new.id);
            let mut sat = true;
            if analysis > max {
                sat = false;
            }

            if sat {
                let mut subsumed = !added_new_node; // all nodes that were added were already in the e-graph and no new equality between classes has been learned

                if !subsumed {
                    for c in wo.clone() {
                        if eg.find_id(c_new.id) == eg.find_id(c.id) {
                            let reachable_parents = rec_parents(eg, &c);
                            // wo - reachable parents
                            // us + reachable parents
                            todo!()
                        }
                        // us = us - c
                        if eg.find_id(c.id) == eg.find_id(c0.id) {
                            subsumed = true;
                        }
                    }
                    if !subsumed {
                        //let mut new_subsumed = false;
                        for c in us.clone() {
                            if eg.find_id(c_new.id) == eg.find_id(c.id) {
                                todo!()
                            } 
                        }
                        if !subsumed {
                            if eg.find_id(c_new.id) == eg.find_id(c0.id) {
                                todo!()
                            }
                        }
                    }
                    // us = us + cnew.applied_id
                    if subsumed {
                        return false;
                    }
                }
            }
        }
    }
    return true;
}