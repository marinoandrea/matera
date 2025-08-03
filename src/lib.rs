//! Reactive Petri nets implementation.
//!
//! Reactive Petri nets differ from normal ones because they can interact with an
//! external system. Therefore, the token-game semantics are modified to account
//! for asynchronous interactions with an environment that the net is monitoring.
//!
//! To achieve this, the net distinguishes between _internal_ and _external_ transitions.
//! We call a net _stable_ if all its internal transitions are disabled, _unstable_
//! otherwise. Moreover, we assume the _Perfect Synchrony Hypothesis_, which states that
//! internal transitions are always faster that external ones. Based on these definitions,
//! the net operates in two different modes: it either executes internal transitions until
//! it reaches stability, or it executes external ones one at a time.
//!
//! The net is implemented using an incidence matrix and marking array approach.
//! While each node (place or transition) is labeled with a string name, they
//! are internally mapped to integer indices. In the marking array T, for each
//! place i we have:
//!
//! T[i] = tokens_i
//!
//! This also allows us to build an incidence matrix W with size NxM (where N = # of transitions
//! and M = # of places). Therefore, given a transition x and place y:
//!
//! W[x][y] = weight_arc_xy
//!
//! We represent input arcs with negative weights so they consume tokens, and
//! output arcs with positive weights so they produce tokens. With this premise,
//! firing a complete transition x is equivalent to the following operation:
//!
//! T = T + W[x]
//!
//! External transitions are fired in two steps, first tokens are consumed and events are
//! pushed to the environment. Then, once the completion event is received, tokens are
//! produced in the ouput arcs.
use std::{
    collections::{HashMap, HashSet},
    fmt,
    hash::Hash,
};

use num_traits::{PrimInt, Signed};

/// A reactive Petri net implementation based on [Eshuis et al. from 2003](https://doi.org/10.1007/3-540-44919-1_20).
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
            // add column-sized chunk
            self.incidence_matrix
                .extend(std::iter::repeat(TRange::zero()).take(self.transition_index_head));

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
        let premoved_index;
        if let Some(index) = self.place_indices.get(&p_id) {
            premoved_index = *index;
        } else {
            return Err(PetriNetError::UnknownPlace(p_id));
        }

        let plast_index = self.place_index_head - 1;

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
            Some(p_index) => Ok(self.marking[*p_index]),
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
        let tremoved_index;
        if let Some(index) = self.transition_indices.get(&t_id) {
            tremoved_index = *index;
        } else {
            return Err(PetriNetError::UnknownTransition(t_id));
        }

        let tlast_index = self.transition_index_head - 1;

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

    pub fn add_input_arc(
        &mut self,
        source: TPlaceId,
        target: TTransitionId,
        weight: TRange,
    ) -> Result<(), PetriNetError<TPlaceId, TTransitionId, TRange>> {
        match self.place_indices.get(&source) {
            Some(p_index) => match self.transition_indices.get(&target) {
                Some(t_index) => {
                    let cell = t_index * self.place_index_head + p_index;
                    self.incidence_matrix[cell] = -weight.abs();
                    Ok(())
                }
                None => Err(PetriNetError::UnknownTransition(target)),
            },
            None => Err(PetriNetError::UnknownPlace(source)),
        }
    }

    pub fn remove_input_arc(
        &mut self,
        source: TPlaceId,
        target: TTransitionId,
    ) -> Result<(), PetriNetError<TPlaceId, TTransitionId, TRange>> {
        match self.place_indices.get(&source) {
            Some(p_index) => match self.transition_indices.get(&target) {
                Some(t_index) => {
                    let cell = t_index * self.place_index_head + p_index;
                    self.incidence_matrix[cell] = TRange::zero();
                    Ok(())
                }
                None => Err(PetriNetError::UnknownTransition(target)),
            },
            None => Err(PetriNetError::UnknownPlace(source)),
        }
    }

    pub fn add_output_arc(
        &mut self,
        source: TTransitionId,
        target: TPlaceId,
        weight: TRange,
    ) -> Result<(), PetriNetError<TPlaceId, TTransitionId, TRange>> {
        match self.place_indices.get(&target) {
            Some(p_index) => match self.transition_indices.get(&source) {
                Some(t_index) => {
                    let cell = t_index * self.place_index_head + p_index;
                    self.incidence_matrix[cell] = weight.abs();
                    Ok(())
                }
                None => Err(PetriNetError::UnknownTransition(source)),
            },
            None => Err(PetriNetError::UnknownPlace(target)),
        }
    }

    pub fn remove_output_arc(
        &mut self,
        source: TTransitionId,
        target: TPlaceId,
    ) -> Result<(), PetriNetError<TPlaceId, TTransitionId, TRange>> {
        match self.place_indices.get(&target) {
            Some(p_index) => match self.transition_indices.get(&source) {
                Some(t_index) => {
                    let cell = t_index * self.place_index_head + p_index;
                    self.incidence_matrix[cell] = TRange::zero();
                    Ok(())
                }
                None => Err(PetriNetError::UnknownTransition(source)),
            },
            None => Err(PetriNetError::UnknownPlace(target)),
        }
    }

    pub fn is_transition_enabled(
        &self,
        t_id: TTransitionId,
    ) -> Result<bool, PetriNetError<TPlaceId, TTransitionId, TRange>> {
        match self.transition_indices.get(&t_id) {
            Some(t_index) => Ok(self.is_transition_enabled_internal(*t_index)),
            None => Err(PetriNetError::UnknownTransition(t_id)),
        }
    }

    #[inline]
    fn is_transition_enabled_internal(&self, t_index: usize) -> bool {
        self.marking
            .iter()
            .enumerate()
            .all(|(p_index, &p_marking)| {
                p_marking + self.incidence_matrix[t_index * self.place_index_head + p_index]
                    >= TRange::zero()
            })
    }

    #[inline]
    pub fn is_unstable(&self) -> bool {
        self.transition_indices
            .values()
            .into_iter()
            .any(|t_index| self.is_transition_enabled_internal(*t_index))
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

    type TestPetriNet<'i> = PetriNet<&'i str, &'i str, i8>;

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
    fn add_and_remove_many_places() -> Result<(), Box<dyn Error>> {
        let mut net = TestPetriNet::new();
        let mut ids: Vec<String> = Vec::new();
        for i in 0..100 {
            ids.push(format!("p{}", i));
        }
        for i in 0..100 {
            net.add_place(ids[i].as_str(), 0).unwrap();
        }
        for i in 0..100 {
            net.remove_place(ids[i].as_str()).unwrap();
        }
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

    #[test]
    fn add_and_remove_many_transitions() -> Result<(), Box<dyn Error>> {
        let mut net = TestPetriNet::new();
        let mut ids: Vec<String> = Vec::new();
        for i in 0..100 {
            ids.push(format!("p{}", i));
        }
        for i in 0..100 {
            net.add_transition(ids[i].as_str(), false).unwrap();
        }
        for i in 0..100 {
            net.remove_transition(ids[i].as_str()).unwrap();
        }
        Ok(())
    }

    #[test]
    fn add_and_remove_arc() -> Result<(), Box<dyn Error>> {
        let mut net = TestPetriNet::new();
        net.add_place("p1", 1)?;
        net.add_transition("t1", false)?;
        net.add_input_arc("p1", "t1", 1)?;
        net.remove_input_arc("p1", "t1")?;
        Ok(())
    }

    #[test]
    fn is_internal_transition_enabled() -> Result<(), Box<dyn Error>> {
        let mut net = TestPetriNet::new();
        net.add_place("p1", 1)?;
        net.add_transition("t1", false)?;
        net.add_input_arc("p1", "t1", 1)?;
        assert!(net.is_transition_enabled("t1")?);
        Ok(())
    }

    #[test]
    fn is_external_transition_enabled() -> Result<(), Box<dyn Error>> {
        let mut net = TestPetriNet::new();
        net.add_place("p1", 1)?;
        net.add_transition("t1", true)?;
        net.add_input_arc("p1", "t1", 1)?;
        assert!(net.is_transition_enabled("t1")?);
        Ok(())
    }
}
