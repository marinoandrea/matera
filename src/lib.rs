use std::{
    collections::{HashMap, HashSet},
    fmt,
    hash::Hash,
};

use num_traits::{PrimInt, Signed};

pub struct PetriNet<
    TPlaceId: Hash + Eq + Clone + fmt::Debug,
    TTransitionId: Hash + Eq + Clone + fmt::Debug,
    TRange: PrimInt + Signed + fmt::Debug = i8,
> {
    /// 1D array storing initial marking for each place
    marking: Vec<TRange>,
    /// 2D matrix storing weights between transitions (x) and places (y)
    incidence_matrix: Vec<TRange>,

    place_indices: HashMap<TPlaceId, usize>,
    place_ids: HashMap<usize, TPlaceId>,

    transition_indices: HashMap<TTransitionId, usize>,
    transition_external: HashSet<TTransitionId>,
    transition_ids: HashMap<usize, TTransitionId>,

    place_index_head: usize,
    transition_index_head: usize,
}

impl<
        TPlaceId: Hash + Eq + Clone + fmt::Debug,
        TTransitionId: Hash + Eq + Clone + fmt::Debug,
        TRange: PrimInt + Signed + fmt::Debug,
    > PetriNet<TPlaceId, TTransitionId, TRange>
{
    pub fn new() -> Self {
        PetriNet {
            marking: Vec::new(),
            incidence_matrix: Vec::new(),
            place_indices: HashMap::new(),
            place_ids: HashMap::new(),
            transition_indices: HashMap::new(),
            transition_external: HashSet::new(),
            transition_ids: HashMap::new(),
            place_index_head: 0,
            transition_index_head: 0,
        }
    }

    /// Add place to the Petri net.
    ///
    /// # Arguments
    /// * `p_id` - new place identifier
    /// * `marking` - initial marking for the place. must be positive.
    ///
    /// # Errors
    ///
    /// * `PetriNetError::InvalidInitialMarking` - if the marking is negative
    /// * `PetriNetError::DuplicatePlace` - if the place id already exists
    ///
    pub fn add_place(
        &mut self,
        p_id: TPlaceId,
        marking: TRange,
    ) -> Result<(), PetriNetError<TPlaceId, TTransitionId, TRange>> {
        if marking < TRange::zero() {
            return Err(PetriNetError::InvalidInitialMarking(marking));
        }

        if self.place_indices.contains_key(&p_id) {
            return Err(PetriNetError::DuplicatePlace(p_id));
        }

        let p_index = self.place_index_head;
        self.place_index_head += 1;

        self.place_indices.insert(p_id.clone(), p_index);
        self.place_ids.insert(p_index, p_id);

        // ensure marking size
        if self.marking.len() > p_index {
            self.marking[p_index] = marking;
        } else {
            self.marking.push(marking);
        }

        // ensure incidence matrix size
        if self.place_index_head * self.transition_index_head > self.incidence_matrix.len() {
            // move rows by 1 in bulk starting at the end of the matrix
            for t_index in (0..self.transition_index_head).rev() {
                let row_index = t_index * self.place_index_head;
                let row_range = row_index..row_index + self.place_index_head;
                self.incidence_matrix.copy_within(row_range, row_index + 1);
                self.incidence_matrix[row_index] = TRange::zero();
            }
        }

        Ok(())
    }

    /// Remove place from the Petri net.
    ///
    /// # Arguments
    /// * `p_id` - place identifier to remove
    ///
    /// # Errors
    ///
    /// * `PetriNetError::UnkownPlace` - if the place id does not exists
    ///
    pub fn remove_place(
        &mut self,
        p_id: TPlaceId,
    ) -> Result<(), PetriNetError<TPlaceId, TTransitionId, TRange>> {
        if !self.place_indices.contains_key(&p_id) {
            return Err(PetriNetError::UnknownPlace(p_id));
        }

        let plast_index = self.place_index_head - 1;
        let premoved_index = *self
            .place_indices
            .get(&p_id)
            .expect("corrupted place indices store");

        if premoved_index != plast_index {
            // swap index
            let plast_id = self
                .place_ids
                .get(&plast_index)
                .expect("corrupted place ids store");
            self.place_indices.insert(plast_id.clone(), premoved_index);

            // swap id
            self.place_ids.insert(premoved_index, plast_id.clone());

            // copy over incidence column
            for t_index in 0..self.transition_index_head {
                let row_index = t_index * self.place_index_head;
                let cell_old = row_index + plast_index;
                let cell_new = row_index + premoved_index;
                self.incidence_matrix[cell_new] = self.incidence_matrix[cell_old];
            }

            // copy over marking
            self.marking[premoved_index] = self.marking[plast_index];
        } else {
            self.place_ids.remove(&premoved_index);
        }

        self.place_indices.remove(&p_id);
        self.place_index_head -= 1;

        Ok(())
    }

    /// Get current marking for a place.
    ///
    /// # Arguments
    /// * `p_id` - place identifier
    ///
    /// # Returns
    ///
    /// The current amount of tokens for the given place.
    ///
    /// # Errors
    ///
    /// * `PetriNetError::UnknownPlace` - if the place id does not exist
    ///
    pub fn get_tokens(
        &self,
        p_id: TPlaceId,
    ) -> Result<TRange, PetriNetError<TPlaceId, TTransitionId, TRange>> {
        match self.place_indices.get(&p_id) {
            Some(p_index) => Ok(self
                .marking
                .get(*p_index)
                .expect("corrupted place indices store")
                .clone()),
            None => Err(PetriNetError::UnknownPlace(p_id)),
        }
    }

    /// Add transition to the Petri net.
    ///
    /// # Arguments
    /// * `t_id` - new transition identifier
    /// * `external` - whether the transition is external
    ///
    /// # Errors
    ///
    /// * `PetriNetError::DuplicateTransition` - if the transition id already exists
    ///
    pub fn add_transition(
        &mut self,
        t_id: TTransitionId,
        external: bool,
    ) -> Result<(), PetriNetError<TPlaceId, TTransitionId, TRange>> {
        if self.transition_indices.contains_key(&t_id) {
            return Err(PetriNetError::DuplicateTransition(t_id));
        }

        let t_index = self.transition_index_head;
        self.transition_index_head += 1;

        self.transition_indices.insert(t_id.clone(), t_index);
        self.transition_ids.insert(t_index, t_id.clone());
        if external {
            self.transition_external.insert(t_id);
        }

        // ensure incidence matrix size
        if self.place_index_head * self.transition_index_head > self.incidence_matrix.len() {
            self.incidence_matrix
                .extend(std::iter::repeat(TRange::zero()).take(self.place_index_head));
        }

        Ok(())
    }

    /// Remove transition from the Petri net.
    ///
    /// # Arguments
    /// * `t_id` - transition identifier to remove
    ///
    /// # Errors
    ///
    /// * `PetriNetError::UnkownTransition` - if the transition id does not exists
    ///
    pub fn remove_transition(
        &mut self,
        t_id: TTransitionId,
    ) -> Result<(), PetriNetError<TPlaceId, TTransitionId, TRange>> {
        if !self.transition_indices.contains_key(&t_id) {
            return Err(PetriNetError::UnknownTransition(t_id));
        }

        let tlast_index = self.transition_index_head - 1;
        let tremoved_index = *self
            .transition_indices
            .get(&t_id)
            .expect("corrupted transition indices store");

        if tremoved_index != tlast_index {
            // swap index
            let tlast_id = self
                .transition_ids
                .get(&tlast_index)
                .expect("corrupted transition indices store");
            self.transition_indices
                .insert(tlast_id.clone(), tremoved_index);

            // swap id
            self.transition_ids.insert(tremoved_index, tlast_id.clone());

            // copy over incidence row
            let row_old = tlast_index * self.place_index_head;
            let row_new = tremoved_index * self.place_index_head;
            for p_index in 0..self.place_index_head {
                let cell_old = row_old + p_index;
                let cell_new = row_new + p_index;
                self.incidence_matrix[cell_new] = self.incidence_matrix[cell_old];
            }
        } else {
            self.transition_ids.remove(&tremoved_index);
        }

        self.transition_indices.remove(&t_id);
        self.transition_external.remove(&t_id);
        self.transition_index_head -= 1;

        Ok(())
    }
}

#[derive(Debug)]
pub enum PetriNetError<
    TPlaceId: Hash + Eq + Clone + fmt::Debug,
    TTransitionId: Hash + Eq + Clone + fmt::Debug,
    TRange: PrimInt + Signed + fmt::Debug,
> {
    InvalidInitialMarking(TRange),
    DuplicatePlace(TPlaceId),
    DuplicateTransition(TTransitionId),
    UnknownPlace(TPlaceId),
    UnknownTransition(TTransitionId),
}

impl<
        TPlaceId: Hash + Eq + Clone + fmt::Debug,
        TTransitionId: Hash + Eq + Clone + fmt::Debug,
        TRange: PrimInt + Signed + fmt::Debug,
    > fmt::Display for PetriNetError<TPlaceId, TTransitionId, TRange>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PetriNetError::InvalidInitialMarking(marking) => {
                write!(f, "InvalidInitialMarking {:?}", marking)
            }
            PetriNetError::DuplicatePlace(p_id) => write!(f, "DuplicatePlace {:?}", p_id),
            PetriNetError::DuplicateTransition(t_id) => write!(f, "DuplicateTransition {:?}", t_id),
            PetriNetError::UnknownPlace(p_id) => write!(f, "UnknownPlace {:?}", p_id),
            PetriNetError::UnknownTransition(t_id) => write!(f, "UnknownTransition {:?}", t_id),
        }
    }
}

impl<
        TPlaceId: Hash + Eq + Clone + fmt::Debug,
        TTransitionId: Hash + Eq + Clone + fmt::Debug,
        TRange: PrimInt + Signed + fmt::Debug,
    > std::error::Error for PetriNetError<TPlaceId, TTransitionId, TRange>
{
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            _ => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::error::Error;

    type TestPetriNet = PetriNet<&'static str, &'static str, i8>;

    #[test]
    fn add_and_remove_place() -> Result<(), Box<dyn Error>> {
        let mut net = TestPetriNet::new();
        net.add_place("p1", 2)?;
        assert_eq!(net.get_tokens("p1")?, 2);
        net.remove_place("p1")?;
        assert!(matches!(net.get_tokens("p1"), Err(_)));
        Ok(())
    }

    #[test]
    fn add_same_place_fails() -> Result<(), Box<dyn Error>> {
        let mut net = TestPetriNet::new();
        net.add_place("p1", 0)?;
        assert!(matches!(net.add_place("p1", 1), Err(_)));
        Ok(())
    }

    #[test]
    fn add_and_remove_transition() -> Result<(), Box<dyn Error>> {
        let mut net = TestPetriNet::new();
        net.add_transition("t1", false)?;
        net.remove_transition("t1")?;
        Ok(())
    }

    #[test]
    fn add_same_transition_fails() -> Result<(), Box<dyn Error>> {
        let mut net = TestPetriNet::new();
        net.add_transition("t1", false)?;
        assert!(matches!(net.add_transition("t1", true), Err(_)));
        Ok(())
    }
}
