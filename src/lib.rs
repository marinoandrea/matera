//! A Petri net library for reactive workflow modelling in Rust, optimised for step-wise simulation speed.
//!
//! Reactive Petri nets, as defined by [Eshuis et al. in 2003](https://doi.org/10.1007/3-540-44919-1_20),
//! differ from normal ones because they can interact with an external system.
//! Therefore, the token-game semantics are modified to account for asynchronous
//! interactions with an environment that the net is monitoring.
//!
//! To achieve this, the net distinguishes between _internal_ and _external_ transitions.
//! We call a net _stable_ if all its internal transitions are disabled, _unstable_
//! otherwise. Moreover, we assume the _Perfect Synchrony Hypothesis_, which states that
//! internal transitions are always faster that external ones. Based on these definitions,
//! the net operates in two different modes: it either executes internal transitions until
//! it reaches stability, or it executes external ones one at a time.
//!
//! # Basic Usage
//!
//! [`PetriNet`] is a graph-like data-structure which is fully resizable and can
//! be initialized using [`PetriNet::new`] to start with an empty graph. It exposes
//! functions to modify place nodes, transition nodes, and arc weights.
//!
//! The struct is meant to be used in step-wise simulation mode by calling the [`PetriNet::step`]
//! function which performs a transition at every step (either internal or external).
//! Internal transitions are always prioritized.
//!
//! ## Example
//!
//!     use matera::PetriNet;
//!     use std::sync::mpsc;
//!
//!     let (_, input_rx) = mpsc::channel();
//!     let (output_tx, _) = mpsc::channel();
//!     let mut net = PetriNet::new(input_rx, output_tx);
//!
//!     net.add_place("Start", 1);
//!     net.add_place("Middle", 0);
//!     net.add_place("End", 0);
//!
//!     net.add_transition("StepA", false);
//!     net.add_transition("StepB", false);
//!
//!     net.add_input_arc("Start", "StepA", 1);
//!     net.add_output_arc("StepA", "Middle", 1);
//!     net.add_input_arc("Middle", "StepB", 1);
//!     net.add_output_arc("StepB", "End", 1);
//!
//!     net.step();
//!
use std::{
    collections::{HashMap, HashSet},
    fmt,
    hash::Hash,
    ops::AddAssign,
    sync::mpsc::{Receiver, RecvError, SendError, Sender},
};

use num_traits::{PrimInt, Signed};

/// A stateful reactive Petri net.
///
/// The net is implemented using an incidence matrix and marking array approach.
///
/// While each node (place or transition) is labeled with a string name, they
/// are internally mapped to integer indices. In the marking array T, for each
/// place i we have:
///
/// `T[i] = tokens_i`
///
/// This also allows us to build an incidence matrix W with size NxM (where N = # of transitions
/// and M = # of places). Therefore, given a transition x and place y:
///
/// `W[x][y] = weight_arc_xy`
///
/// We represent input arcs with negative weights so they consume tokens, and
/// output arcs with positive weights so they produce tokens. With this premise,
/// firing a complete transition x is equivalent to the following operation:
///
/// `T = T + W[x]`
///
#[derive(Debug)]
pub struct PetriNet<
    TPlaceId: Hash + Eq + Clone + fmt::Debug,
    TTransitionId: Hash + Eq + Clone + fmt::Debug,
    TRange: PrimInt + Signed + AddAssign + fmt::Debug = i8,
> {
    /// 1D array storing current marking for each place
    marking: Vec<TRange>,
    /// 1D array storing initial marking for each place
    initial_marking: Vec<TRange>,
    /// 2D matrix storing weights between transitions (x) and places (y)
    incidence_matrix: Vec<TRange>,

    place_indices: HashMap<TPlaceId, usize>,
    place_ids: HashMap<usize, TPlaceId>,

    transition_indices: HashMap<TTransitionId, usize>,
    transition_external: HashSet<TTransitionId>,
    transition_ids: HashMap<usize, TTransitionId>,

    place_index_head: usize,
    transition_index_head: usize,

    input_queue: Receiver<TTransitionId>,
    output_queue: Sender<TTransitionId>,
}

impl<
        TPlaceId: Hash + Eq + Clone + fmt::Debug,
        TTransitionId: Hash + Eq + Clone + fmt::Debug,
        TRange: PrimInt + Signed + AddAssign + fmt::Debug,
    > PetriNet<TPlaceId, TTransitionId, TRange>
{
    /// Create a new empty Petri net.
    ///
    /// # Arguments
    /// * `input_queue` - external transition completion inbound channel
    /// * `output_queue` - external transition announcement outbound channel
    ///
    pub fn new(input_queue: Receiver<TTransitionId>, output_queue: Sender<TTransitionId>) -> Self {
        PetriNet {
            marking: Vec::new(),
            initial_marking: Vec::new(),
            incidence_matrix: Vec::new(),
            place_indices: HashMap::new(),
            place_ids: HashMap::new(),
            transition_indices: HashMap::new(),
            transition_external: HashSet::new(),
            transition_ids: HashMap::new(),
            place_index_head: 0,
            transition_index_head: 0,
            input_queue,
            output_queue,
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
    /// # Time Complexity
    ///
    /// Given:
    /// - N = # number of transitions
    /// - M = # number of places
    ///
    /// Resizing the matrix requires N `memcopy` operations to expand each row
    /// which individually are O(M). Therefore, the final complexity is O(N*M).
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
            self.initial_marking[p_index] = marking;
        } else {
            self.marking.push(marking);
            self.initial_marking.push(marking);
        }

        // ensure incidence matrix size
        if self.place_index_head * self.transition_index_head > self.incidence_matrix.len() {
            // add column-sized chunk
            self.incidence_matrix
                .extend(std::iter::repeat(TRange::zero()).take(self.transition_index_head));
        }

        // move rows by 1 in bulk starting at the end of the matrix
        for t_index in (0..self.transition_index_head).rev() {
            let row_index = t_index * self.place_index_head;
            let row_range = row_index..row_index + self.place_index_head;
            self.incidence_matrix.copy_within(row_range, row_index + 1);
            self.incidence_matrix[row_index] = TRange::zero();
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
    /// * `PetriNetError::UnknownPlace` - if the place id does not exists
    ///
    /// # Time Complexity
    ///
    /// Given:
    /// - N = # number of transitions
    /// - M = # number of places
    ///
    /// In the best case scenario, when the removed transition is at the last row
    /// index in the matrix it is O(1). However, in the worst case, copying over
    /// the matrix row is O(M).
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
            self.initial_marking[premoved_index] = self.initial_marking[plast_index];
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
    /// # Time Complexity
    ///
    /// Given:
    /// - N = # number of transitions
    /// - M = # number of places
    ///
    /// In the best case scenario, when the matrix is large enough to accomodate
    /// a new transition, it is O(1). However, in the worst case, resizing the
    /// matrix requires a full vector copy which is O(N*M).
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
    /// * `PetriNetError::UnknownTransition` - if the transition id does not exists
    ///
    /// # Time Complexity
    ///
    /// Given:
    /// - N = # number of transitions
    /// - M = # number of places
    ///
    /// In the best case scenario, when the removed transition is at the last row
    /// index in the matrix it is O(1). However, in the worst case, copying over
    /// the matrix row is O(M).
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

    /// Add input arc with weight from the Petri net.
    ///
    /// The weight is taken in absolute value and will be stored as `-weight.abs()`.
    /// Direct loops, as in the same place as input and output, will error.
    ///
    /// # Arguments
    /// * `source` - source node identifier (place)
    /// * `target` - source node identifier (transition)
    /// * `weight` - weight of the arc
    ///
    /// # Errors
    ///
    /// * `PetriNetError::UnknownPlace` - if the place id does not exists
    /// * `PetriNetError::UnknownTransition` - if the transition id does not exists
    /// * `PetriNetError::DuplicateArc` - if source and target are already connected
    ///
    /// # Time Complexity
    ///
    /// This operation is always O(1).
    ///
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
                    if self.incidence_matrix[cell] != TRange::zero() {
                        Err(PetriNetError::DuplicateArc(source, target))
                    } else {
                        self.incidence_matrix[cell] = -weight.abs();
                        Ok(())
                    }
                }
                None => Err(PetriNetError::UnknownTransition(target)),
            },
            None => Err(PetriNetError::UnknownPlace(source)),
        }
    }

    /// Remove input arc with weight from the Petri net.
    ///
    /// # Arguments
    /// * `source` - source node identifier (transition)
    /// * `target` - source node identifier (place)
    ///
    /// # Errors
    ///
    /// * `PetriNetError::UnknownPlace` - if the place id does not exists
    /// * `PetriNetError::UnknownTransition` - if the transition id does not exists
    ///
    /// # Time Complexity
    ///
    /// This operation is always O(1).
    ///
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

    /// Add output arc with weight from the Petri net.
    ///
    /// The weight is taken in absolute value and will be stored as `+weight.abs()`.
    /// Direct loops, as in the same place as input and output, will error.
    ///
    /// # Arguments
    /// * `source` - source node identifier (place)
    /// * `target` - source node identifier (transition)
    /// * `weight` - weight of the arc
    ///
    /// # Errors
    ///
    /// * `PetriNetError::UnknownPlace` - if the place id does not exists
    /// * `PetriNetError::UnknownTransition` - if the transition id does not exists
    /// * `PetriNetError::DuplicateArc` - if source and target are already connected
    ///
    /// # Time Complexity
    ///
    /// This operation is always O(1).
    ///
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
                    if self.incidence_matrix[cell] != TRange::zero() {
                        Err(PetriNetError::DuplicateArc(target, source))
                    } else {
                        self.incidence_matrix[cell] = weight.abs();
                        Ok(())
                    }
                }
                None => Err(PetriNetError::UnknownTransition(source)),
            },
            None => Err(PetriNetError::UnknownPlace(target)),
        }
    }

    /// Remove output arc with weight from the Petri net.
    ///
    /// # Arguments
    /// * `source` - source node identifier (transition)
    /// * `target` - source node identifier (place)
    ///
    /// # Errors
    ///
    /// * `PetriNetError::UnknownPlace` - if the place id does not exists
    /// * `PetriNetError::UnknownTransition` - if the transition id does not exists
    ///
    /// # Time Complexity
    ///
    /// This operation is always O(1).
    ///
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

    /// Check whether the transition is enabled.
    ///
    /// A transition is enabled if, for each input arc, the amount of tokens
    /// in the source place are greater or equal than the arc's weight.
    ///
    /// # Arguments
    /// * `t_id` - transition identifier
    ///
    /// # Errors
    ///
    /// * `PetriNetError::UnknownTransition` - if the transition id does not exists
    ///
    pub fn is_transition_enabled(
        &self,
        t_id: TTransitionId,
    ) -> Result<bool, PetriNetError<TPlaceId, TTransitionId, TRange>> {
        match self.transition_indices.get(&t_id) {
            Some(t_index) => Ok(self._is_transition_enabled(*t_index)),
            None => Err(PetriNetError::UnknownTransition(t_id)),
        }
    }

    #[inline]
    fn _is_transition_enabled(&self, t_index: usize) -> bool {
        self.marking
            .iter()
            .enumerate()
            .all(|(p_index, &p_marking)| {
                p_marking + self.incidence_matrix[t_index * self.place_index_head + p_index]
                    >= TRange::zero()
            })
    }

    /// Check whether the net is unstable.
    /// That is, there is at least one enabled internal transition.
    #[inline]
    pub fn is_unstable(&self) -> bool {
        self.transition_indices
            .values()
            .into_iter()
            .any(|t_index| self._is_transition_enabled(*t_index))
    }

    /// Reset the net to the original marking values.
    #[inline]
    pub fn reset(&mut self) {
        self.marking.copy_from_slice(&self.initial_marking);
    }

    /// Fire the given transition.
    fn fire(&mut self, t_index: usize) {
        let row_index = t_index * self.place_index_head;
        for p_index in 0..self.place_index_head {
            self.marking[p_index] += self.incidence_matrix[row_index + p_index];
        }
    }

    /// Perform one step of the simulation.
    ///
    /// # Arguments
    /// * `source` - source node identifier (transition)
    /// * `target` - source node identifier (place)
    ///
    /// # Errors
    ///
    /// * `PetriNetError::UnknownTransition` - if the received completion event is for a transition that does not exists
    /// * `PetriNetError::InvalidCompletionEvent` - if the received completion event is for a transition that is not enabled
    /// * `PetriNetError::SendError` - if announcing the transitions errors out
    /// * `PetriNetError::RecvError` - if receiving the completion events errors out
    ///
    /// # Time Complexity
    ///
    /// Given:
    /// - N = # number of transitions
    /// - M = # number of places
    ///
    /// This operation is always O(N+M).
    ///
    pub fn step(&mut self) -> Result<(), PetriNetError<TPlaceId, TTransitionId, TRange>> {
        // due to the perfect synchrony hypothesis, we assume that internal reactions
        // are always faster than the external system. Therefore, we fire internal
        // transitions first until we reach stability.
        for (t_id, t_index) in self.transition_indices.iter() {
            if !self.transition_external.contains(t_id) && self._is_transition_enabled(*t_index) {
                // the net is unstable
                self.fire(*t_index);
                return Ok(());
            }
        }

        // the net is stable, we publish all enabled external transitions
        for (t_id, t_index) in self.transition_indices.iter() {
            if self.transition_external.contains(t_id) && self._is_transition_enabled(*t_index) {
                self.output_queue.send(t_id.clone())?;
            }
        }

        // then we wait for an external transition to complete
        let t_id = self.input_queue.recv()?;

        // we double check it is enabled and then fire it
        match self.transition_indices.get(&t_id) {
            Some(t_index) => {
                if self._is_transition_enabled(*t_index) {
                    self.fire(*t_index);
                    Ok(())
                } else {
                    Err(PetriNetError::InvalidCompletionEvent(t_id))
                }
            }
            None => Err(PetriNetError::UnknownTransition(t_id)),
        }
    }
}

#[derive(Debug)]
pub enum PetriNetError<
    TPlaceId: Hash + Eq + Clone + fmt::Debug,
    TTransitionId: Hash + Eq + Clone + fmt::Debug,
    TRange: PrimInt + Signed + fmt::Debug,
> {
    DuplicatePlace(TPlaceId),
    DuplicateTransition(TTransitionId),
    DuplicateArc(TPlaceId, TTransitionId),
    UnknownPlace(TPlaceId),
    UnknownTransition(TTransitionId),
    SendError(SendError<TTransitionId>),
    RecvError(RecvError),
    InvalidInitialMarking(TRange),
    InvalidCompletionEvent(TTransitionId),
}

impl<
        TPlaceId: Hash + Eq + Clone + fmt::Debug,
        TTransitionId: Hash + Eq + Clone + fmt::Debug,
        TRange: PrimInt + Signed + fmt::Debug,
    > fmt::Display for PetriNetError<TPlaceId, TTransitionId, TRange>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PetriNetError::DuplicatePlace(p_id) => write!(f, "DuplicatePlace {:?}", p_id),
            PetriNetError::DuplicateTransition(t_id) => write!(f, "DuplicateTransition {:?}", t_id),
            PetriNetError::DuplicateArc(p_id, t_id) => {
                write!(f, "DuplicateArc {:?}-{:?}", p_id, t_id)
            }
            PetriNetError::UnknownPlace(p_id) => write!(f, "UnknownPlace {:?}", p_id),
            PetriNetError::UnknownTransition(t_id) => write!(f, "UnknownTransition {:?}", t_id),
            PetriNetError::SendError(err) => write!(f, "SendError {:?}", err),
            PetriNetError::RecvError(err) => write!(f, "RecvError {:?}", err),
            PetriNetError::InvalidInitialMarking(marking) => {
                write!(f, "InvalidInitialMarking {:?}", marking)
            }
            PetriNetError::InvalidCompletionEvent(t_id) => {
                write!(f, "InvalidCompletionEvent {:?}", t_id)
            }
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

impl<
        TPlaceId: Hash + Eq + Clone + fmt::Debug,
        TTransitionId: Hash + Eq + Clone + fmt::Debug,
        TRange: PrimInt + Signed + fmt::Debug,
    > From<SendError<TTransitionId>> for PetriNetError<TPlaceId, TTransitionId, TRange>
{
    fn from(value: SendError<TTransitionId>) -> Self {
        PetriNetError::SendError(value)
    }
}

impl<
        TPlaceId: Hash + Eq + Clone + fmt::Debug,
        TTransitionId: Hash + Eq + Clone + fmt::Debug,
        TRange: PrimInt + Signed + fmt::Debug,
    > From<RecvError> for PetriNetError<TPlaceId, TTransitionId, TRange>
{
    fn from(value: RecvError) -> Self {
        PetriNetError::RecvError(value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{error::Error, sync::mpsc, time::Duration};

    type TestPetriNet<'i> = PetriNet<&'i str, &'i str, i8>;

    #[test]
    fn add_and_remove_place() -> Result<(), Box<dyn Error>> {
        let (_, input_rx) = mpsc::channel();
        let (output_tx, _) = mpsc::channel();
        let mut net = TestPetriNet::new(input_rx, output_tx);
        net.add_place("p1", 2)?;
        assert_eq!(net.get_tokens("p1")?, 2);
        net.remove_place("p1")?;
        assert!(matches!(net.get_tokens("p1"), Err(_)));
        Ok(())
    }

    #[test]
    fn add_same_place_fails() -> Result<(), Box<dyn Error>> {
        let (_, input_rx) = mpsc::channel();
        let (output_tx, _) = mpsc::channel();
        let mut net = TestPetriNet::new(input_rx, output_tx);
        net.add_place("p1", 0)?;
        assert!(matches!(net.add_place("p1", 1), Err(_)));
        Ok(())
    }

    #[test]
    fn add_and_remove_many_places() -> Result<(), Box<dyn Error>> {
        let mut ids: Vec<String> = Vec::new();

        let (_, input_rx) = mpsc::channel();
        let (output_tx, _) = mpsc::channel();
        let mut net = TestPetriNet::new(input_rx, output_tx);

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
        let (_, input_rx) = mpsc::channel();
        let (output_tx, _) = mpsc::channel();
        let mut net = TestPetriNet::new(input_rx, output_tx);
        net.add_transition("t1", false)?;
        net.remove_transition("t1")?;
        Ok(())
    }

    #[test]
    fn add_same_transition_fails() -> Result<(), Box<dyn Error>> {
        let (_, input_rx) = mpsc::channel();
        let (output_tx, _) = mpsc::channel();
        let mut net = TestPetriNet::new(input_rx, output_tx);
        net.add_transition("t1", false)?;
        assert!(matches!(net.add_transition("t1", true), Err(_)));
        Ok(())
    }

    #[test]
    fn add_and_remove_many_transitions() -> Result<(), Box<dyn Error>> {
        let mut ids: Vec<String> = Vec::new();

        let (_, input_rx) = mpsc::channel();
        let (output_tx, _) = mpsc::channel();
        let mut net = TestPetriNet::new(input_rx, output_tx);

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
        let (_, input_rx) = mpsc::channel();
        let (output_tx, _) = mpsc::channel();
        let mut net = TestPetriNet::new(input_rx, output_tx);
        net.add_place("p1", 1)?;
        net.add_transition("t1", false)?;
        net.add_input_arc("p1", "t1", 1)?;
        net.remove_input_arc("p1", "t1")?;
        Ok(())
    }

    #[test]
    fn is_internal_transition_enabled() -> Result<(), Box<dyn Error>> {
        let (_, input_rx) = mpsc::channel();
        let (output_tx, _) = mpsc::channel();
        let mut net = TestPetriNet::new(input_rx, output_tx);
        net.add_place("p1", 1)?;
        net.add_transition("t1", false)?;
        net.add_input_arc("p1", "t1", 1)?;
        assert!(net.is_transition_enabled("t1")?);
        Ok(())
    }

    #[test]
    fn is_external_transition_enabled() -> Result<(), Box<dyn Error>> {
        let (_, input_rx) = mpsc::channel();
        let (output_tx, _) = mpsc::channel();
        let mut net = TestPetriNet::new(input_rx, output_tx);
        net.add_place("p1", 1)?;
        net.add_transition("t1", true)?;
        net.add_input_arc("p1", "t1", 1)?;
        assert!(net.is_transition_enabled("t1")?);
        Ok(())
    }

    #[test]
    fn sequential_workflow() -> Result<(), Box<dyn Error>> {
        let (_, input_rx) = mpsc::channel();
        let (output_tx, _) = mpsc::channel();
        let mut net = TestPetriNet::new(input_rx, output_tx);

        net.add_place("Start", 1)?;
        net.add_place("Middle", 0)?;
        net.add_place("End", 0)?;

        net.add_transition("StepA", false)?;
        net.add_transition("StepB", false)?;

        net.add_input_arc("Start", "StepA", 1)?;
        net.add_output_arc("StepA", "Middle", 1)?;
        net.add_input_arc("Middle", "StepB", 1)?;
        net.add_output_arc("StepB", "End", 1)?;

        assert!(net.is_transition_enabled("StepA")?);

        net.step()?;

        assert!(!net.is_transition_enabled("StepA")?);
        assert!(net.is_transition_enabled("StepB")?);

        net.step()?;

        assert!(!net.is_transition_enabled("StepB")?);
        assert!(!net.is_unstable());

        Ok(())
    }

    #[test]
    fn forkjoin() -> Result<(), Box<dyn Error>> {
        let (_, input_rx) = mpsc::channel();
        let (output_tx, _) = mpsc::channel();
        let mut net = TestPetriNet::new(input_rx, output_tx);

        net.add_place("Start", 1)?;
        net.add_place("P1", 0)?;
        net.add_place("P2", 0)?;
        net.add_place("End", 0)?;

        net.add_transition("Fork", false)?;
        net.add_transition("Join", false)?;

        net.add_input_arc("Start", "Fork", 1)?;
        net.add_output_arc("Fork", "P1", 1)?;
        net.add_output_arc("Fork", "P2", 1)?;

        net.add_input_arc("P1", "Join", 1)?;
        net.add_input_arc("P2", "Join", 1)?;
        net.add_output_arc("Join", "End", 1)?;

        assert!(net.is_transition_enabled("Fork")?);

        net.step()?;

        assert!(!net.is_transition_enabled("Fork")?);
        assert!(net.is_transition_enabled("Join")?);

        net.step()?;

        assert!(!net.is_transition_enabled("Join")?);
        assert!(!net.is_unstable());

        Ok(())
    }

    #[test]
    fn hungry_philosophers() -> Result<(), Box<dyn Error>> {
        let (_, input_rx) = mpsc::channel();
        let (output_tx, _) = mpsc::channel();
        let mut net = TestPetriNet::new(input_rx, output_tx);

        net.add_place("Fork1", 1)?;
        net.add_place("Fork2", 1)?;
        net.add_place("Hungry1", 1)?;
        net.add_place("Hungry2", 1)?;
        net.add_place("Eating1", 0)?;
        net.add_place("Eating2", 0)?;

        net.add_transition("StartEating1", false)?;
        net.add_transition("FinishEating1", false)?;
        net.add_transition("StartEating2", false)?;
        net.add_transition("FinishEating2", false)?;

        net.add_input_arc("Hungry1", "StartEating1", 1)?;
        net.add_input_arc("Fork1", "StartEating1", 1)?;
        net.add_input_arc("Fork2", "StartEating1", 1)?;
        net.add_output_arc("StartEating1", "Eating1", 1)?;
        net.add_input_arc("Eating1", "FinishEating1", 1)?;
        net.add_output_arc("FinishEating1", "Fork1", 1)?;
        net.add_output_arc("FinishEating1", "Fork2", 1)?;
        net.add_input_arc("Hungry2", "StartEating2", 1)?;
        net.add_input_arc("Fork1", "StartEating2", 1)?;
        net.add_input_arc("Fork2", "StartEating2", 1)?;
        net.add_output_arc("StartEating2", "Eating2", 1)?;
        net.add_input_arc("Eating2", "FinishEating2", 1)?;
        net.add_output_arc("FinishEating2", "Fork1", 1)?;
        net.add_output_arc("FinishEating2", "Fork2", 1)?;

        //both philosophers can start eating
        assert!(net.is_transition_enabled("StartEating1")?);
        assert!(net.is_transition_enabled("StartEating2")?);

        // firing order should be left to the implementation and not be assumed
        for i in 0..2 {
            net.step()?;

            // stepping means one philosopher prevails depending on the internal order
            assert!(!net.is_transition_enabled("StartEating1")?);
            assert!(!net.is_transition_enabled("StartEating2")?);

            if net.is_transition_enabled("FinishEating1")? {
                net.step()?;
                assert!(net.is_transition_enabled("StartEating2")? || i == 1)
            } else if net.is_transition_enabled("FinishEating2")? {
                net.step()?;
                assert!(net.is_transition_enabled("StartEating1")? || i == 1)
            } else {
                panic!("no philosopher is eating")
            }
        }

        assert!(!net.is_unstable());

        Ok(())
    }

    #[test]
    fn forkjoin_external() -> Result<(), Box<dyn Error>> {
        let (input_tx, input_rx) = mpsc::channel();
        let (output_tx, output_rx) = mpsc::channel();
        let mut net = TestPetriNet::new(input_rx, output_tx);

        net.add_place("Start", 1)?;
        net.add_place("P1", 0)?;
        net.add_place("P2", 0)?;
        net.add_place("P3", 0)?;
        net.add_place("P4", 0)?;
        net.add_place("End", 0)?;

        net.add_transition("Fork", false)?;
        net.add_transition("External", true)?;
        net.add_transition("Internal", false)?;
        net.add_transition("Join", false)?;

        net.add_input_arc("Start", "Fork", 1)?;
        net.add_output_arc("Fork", "P1", 1)?;
        net.add_output_arc("Fork", "P2", 1)?;
        net.add_input_arc("P1", "External", 1)?;
        net.add_input_arc("P2", "Internal", 1)?;
        net.add_output_arc("External", "P3", 1)?;
        net.add_output_arc("Internal", "P4", 1)?;
        net.add_input_arc("P3", "Join", 1)?;
        net.add_input_arc("P4", "Join", 1)?;
        net.add_output_arc("Join", "End", 1)?;

        assert!(net.is_transition_enabled("Fork")?);

        net.step()?;

        // the initial fork should produce tokens
        assert!(net.get_tokens("P1")? == 1);
        assert!(net.get_tokens("P2")? == 1);
        assert!(net.get_tokens("P3")? == 0);
        assert!(net.get_tokens("P4")? == 0);
        assert!(net.is_transition_enabled("External")?);
        assert!(net.is_transition_enabled("Internal")?);

        net.step()?;

        // we check that the internal transition has been performed first
        assert!(net.get_tokens("P1")? == 1);
        assert!(net.get_tokens("P2")? == 0);
        assert!(net.get_tokens("P3")? == 0);
        assert!(net.get_tokens("P4")? == 1);

        // then we step in a separate thread to avoid hanging
        let handle = std::thread::spawn(move || {
            let mut net = net;
            net.step().unwrap(); // external transition
            net
        });

        // and have announced the transition
        assert_eq!(output_rx.recv()?, "External");

        // we manually push the completion event
        input_tx.send("External")?;

        // and wait for the step to take place
        let mut net = handle.join().unwrap();

        // we should now be ready to join
        assert!(net.get_tokens("P1")? == 0);
        assert!(net.get_tokens("P2")? == 0);
        assert!(net.get_tokens("P3")? == 1);
        assert!(net.get_tokens("P4")? == 1);
        assert!(net.is_transition_enabled("Join")?);

        net.step()?;

        assert!(!net.is_unstable());

        Ok(())
    }

    #[test]
    fn decision_loop() -> Result<(), Box<dyn Error>> {
        let (input_tx, input_rx) = mpsc::channel();
        let (output_tx, output_rx) = mpsc::channel();
        let mut net = TestPetriNet::new(input_rx, output_tx);

        net.add_place("P1", 1)?;
        net.add_place("P2", 0)?;

        net.add_transition("T1", true)?;
        net.add_transition("T2", true)?;
        net.add_transition("T3", true)?;
        net.add_transition("Back", false)?;

        net.add_input_arc("P1", "T1", 1)?;
        net.add_input_arc("P1", "T2", 1)?;
        net.add_input_arc("P1", "T3", 1)?;

        net.add_output_arc("T1", "P2", 1)?;
        net.add_output_arc("T2", "P2", 1)?;
        net.add_output_arc("T3", "P2", 1)?;

        net.add_input_arc("P2", "Back", 1)?;
        net.add_output_arc("Back", "P1", 1)?;

        assert!(net.is_transition_enabled("T1")?);
        assert!(net.is_transition_enabled("T2")?);
        assert!(net.is_transition_enabled("T3")?);

        fn check_for_events(queue: &Receiver<&'static str>) -> Result<(), Box<dyn Error>> {
            let mut missing_events = HashSet::from(["T1", "T2", "T3"]);

            let e1 = queue.recv_timeout(Duration::from_millis(100))?;
            let e2 = queue.recv_timeout(Duration::from_millis(100))?;
            let e3 = queue.recv_timeout(Duration::from_millis(100))?;

            missing_events.remove(e1);
            missing_events.remove(e2);
            missing_events.remove(e3);

            assert!(missing_events.is_empty());

            Ok(())
        }

        for t_id in ["T1", "T2", "T3"] {
            // we step in a separate thread to avoid hanging
            let handle = std::thread::spawn(move || {
                let mut net = net;
                net.step().unwrap();
                net
            });

            check_for_events(&output_rx)?;

            // we manually push the completion event
            input_tx.send(t_id)?;

            // and wait for the step to take place
            net = handle.join().unwrap();

            assert!(net.get_tokens("P2")? == 1);
            assert!(net.is_transition_enabled("Back")?);

            net.step()?;

            // all transitions should be enabled again as the net is a loop
            assert!(net.get_tokens("P1")? == 1);
            assert!(net.is_transition_enabled("T1")?);
            assert!(net.is_transition_enabled("T2")?);
            assert!(net.is_transition_enabled("T3")?);
        }

        Ok(())
    }
}
