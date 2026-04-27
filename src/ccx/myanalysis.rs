use std::cmp::min;

use crate::*;


pub struct AstSizeAnalysis;

impl<L:Language> Analysis<L> for AstSizeAnalysis {
    type Data = u64;
    fn make(eg: &EGraph<L, Self>, enode: &L) -> Self::Data {
        let mut s: u64 = 1;
        for x in enode.applied_id_occurrences(){
            s = s.saturating_add(*eg.analysis_data(x.id));
        }
        s
    }
    fn merge(l: Self::Data, r: Self::Data) -> Self::Data {
        min(l, r)
    }
}