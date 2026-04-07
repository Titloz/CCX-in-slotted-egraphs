use crate::*;

type Unifier = HashMap<Slot, AppliedId>;

pub(crate) fn compute_mgus<L: Language, N: Analysis<L>>
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
                                todo!();
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
                                    l.extend_from_slice(l_bis);
                                },
                                None => {
                                    todo!();
                                }
                            }
                        },
                        SyntaxElem::AppliedId(j) => {
                            todo!("is there really something to do?");
                        }
                    }
                },
                SyntaxElem::Slot(y) => {
                    match &nb.to_syntax()[0] {
                        SyntaxElem::String(g) => {
                            match mu.get(y) {
                                Some(c) => {
                                    // LazyRep
                                    let (l_bis, _) = &compute_mgus(eg, c, b, mu, &visited_bis);
                                    l.extend_from_slice(l_bis);
                                },
                                None => {
                                    todo!();
                                }
                            }
                        },
                        SyntaxElem::Slot(x) => {
                            if x == y {
                                // Triv
                                l.push(mu.clone());
                            } else {
                                match mu.get(y) {
                                    Some(c) => {
                                        // LazyRep
                                        let (l_bis, _) = &compute_mgus(eg, c, b, mu, &visited_bis);
                                        l.extend_from_slice(l_bis);
                                    },
                                    None => {
                                        todo!()
                                    }
                                }
                            }
                        },
                        SyntaxElem::AppliedId(j) => {
                            todo!("is there really something to do?");
                        }
                    }
                },
                SyntaxElem::AppliedId(i) => {
                    todo!("is there really something to do?");
                }
            }
        }
    }
    return (l, visited_bis);
}