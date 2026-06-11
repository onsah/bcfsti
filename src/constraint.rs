use std::collections::HashSet;

use crate::syntax::Type;

pub struct Constraints(HashSet<(Type, Type)>);

impl Constraints {
    pub fn empty() -> Constraints {
        Constraints(HashSet::new())
    }

    pub fn join(self, other: Constraints) -> Constraints {
        let mut constraints = self.0;
        for constraint in other.0 {
            constraints.insert(constraint);
        }
        Constraints(constraints)
    }

    pub fn add(&mut self, ty1: Type, ty2: Type) {
        self.0.insert((ty1, ty2));
    }

    pub fn iter(&self) -> impl Iterator<Item = &(Type, Type)> {
        self.0.iter()
    }
}
