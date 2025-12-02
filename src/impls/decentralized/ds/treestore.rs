use crate::{
    crypto::hash::HasherZK,
    generic::{
        bulletin::{CallbackBul, JoinableBulletin, PublicCallbackBul, PublicUserBul, UserBul},
        callbacks::CallbackCom,
        object::{Com, Nul, Time, TimeVar},
        service::ServiceProvider,
        user::{ExecutedMethod, UserData},
    },
    impls,
    impls::{
        centralized::{
            crypto::{FakeSigPubkey, FakeSigPubkeyVar, NoEnc, NoSigOTP},
            ds::{
                sig::Signature,
                sigstore::{CallbackStore, CentralStore, NonmembStore, SigObjStore},
            },
        },
        hash::Poseidon,
    },
};
use ark_bls12_377::Fr as Bls377Fr;
use ark_bls12_381::Fr as BlsFr;
use ark_crypto_primitives::sponge::Absorb;
use ark_ff::{PrimeField, ToConstraintField};
use ark_grumpkin::Fq as BnFr;
use ark_r1cs_std::{
    alloc::AllocVar, convert::ToConstraintFieldGadget, fields::fp::FpVar, prelude::Boolean,
};
use ark_relations::r1cs::SynthesisError;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use incrementalmerkletree_testing::{
    complement_tree::{
        RangeTree, RangeTreePath, RangeTreePathVar, RangeTreeRoot, RangeTreeRootVar,
    },
    incremental_int_tree::{IncIntTree, IntTreePath, IntTreePathVar, IntTreeRoot, IntTreeRootVar},
    tree_util::{TreeParams, TreeParamsVar},
};
use rand::{
    CryptoRng, Rng, RngCore,
    distributions::{Distribution, Standard},
    thread_rng,
};
use std::fmt;

/// This is a de-centralized object storage system, with proofs of membership.
///
/// To add an object, object commitments are added into the Merkle tree.
///
/// To prove membership, users will then prove knowledge of a public root of
/// a Merkle tree that their user object commitment is in.
///
/// Note that this implements [`PublicUserBul`] and [`UserBul`].
#[derive(Clone)]
pub struct IMTObjStore<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8> {
    /// The Merkle Tree struct.
    pub tree: IncIntTree<F, INT_TREE_DEPTH>,

    /// The old nullifiers for each object.
    pub old_nuls: Vec<Nul<F>>,

    /// The callback commitments given by the users.
    pub cb_com_lists: Vec<Vec<Com<F>>>,
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8> Default for IMTObjStore<F, INT_TREE_DEPTH> {
    fn default() -> Self {
        Self {
            tree: IncIntTree::<F, INT_TREE_DEPTH>::new(&[]),
            old_nuls: vec![],
            cb_com_lists: vec![],
        }
    }
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8> fmt::Debug
    for IMTObjStore<F, INT_TREE_DEPTH>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Point")
            .field("root", &self.tree.get_root())
            .field("leaves", &self.tree.leaves)
            .field("old_nuls", &self.old_nuls)
            .field("cb_com_lists", &self.cb_com_lists)
            .finish()
    }
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8> IMTObjStore<F, INT_TREE_DEPTH> {
    /// Construct a new IMTObjStore.
    ///
    /// Sets root as zero.
    pub fn new(rng: &mut (impl CryptoRng + RngCore)) -> Self {
        Self::default()
    }

    /// Given an already existing database, initialize the store from this database.
    pub fn from(tree: IncIntTree<F, INT_TREE_DEPTH>, db: Vec<(Nul<F>, Vec<Com<F>>)>) -> Self {
        let old_nuls = db.iter().map(|(n, _)| n.clone()).collect();
        let cb_com_lists = db.iter().map(|(_, l)| l.clone()).collect();
        Self {
            tree,
            old_nuls,
            cb_com_lists,
        }
    }

    /// Get the root.
    pub fn get_root(&self) -> F {
        self.tree.get_root()
    }

    /// Get the path of a specific object. Returns None if the object is not contained in the
    /// bulletin.
    pub fn get_path_of(&self, obj: &Com<F>) -> Option<IntTreePath<F>> {
        for (i, c) in self.tree.leaves.iter().enumerate() {
            if c == obj {
                return Some(self.tree.auth_path(i));
            }
        }
        None
    }
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8, U: UserData<F>> PublicUserBul<F, U>
    for IMTObjStore<F, INT_TREE_DEPTH>
{
    type MembershipWitness = IntTreePath<F>;

    type MembershipWitnessVar = IntTreePathVar<F>;

    type MembershipPub = IntTreeRoot<F>;

    type MembershipPubVar = IntTreeRootVar<F>;

    fn verify_in<PubArgs, Snark: ark_snark::SNARK<F>, const NUMCBS: usize>(
        &self,
        object: Com<F>,
        old_nul: Nul<F>,
        cb_com_list: [Com<F>; NUMCBS],
        _args: PubArgs,
        _proof: Snark::Proof,
        _memb_data: Self::MembershipPub,
        _verif_key: &Snark::VerifyingKey,
    ) -> bool {
        for (i, c) in self.tree.leaves.iter().enumerate() {
            if c == &object
                && self.old_nuls[i] == old_nul
                && self.cb_com_lists[i] == cb_com_list.to_vec()
            {
                return true;
            }
        }
        false
    }

    fn get_membership_data(&self, object: Com<F>) -> Option<(IntTreeRoot<F>, IntTreePath<F>)> {
        let path = self.get_path_of(&object);
        if path.is_none() {
            return None;
        }
        Some((self.get_root(), path.unwrap()))
    }

    fn enforce_membership_of(
        data_var: crate::generic::object::ComVar<F>,
        extra_witness: Self::MembershipWitnessVar,
        extra_pub: Self::MembershipPubVar,
    ) -> Result<Boolean<F>, SynthesisError> {
        let tree_params_var: TreeParamsVar<F> = TreeParams::new().to_var();
        extra_witness.verify_membership(
            &tree_params_var.leaf_params,
            &tree_params_var.two_to_one_params,
            &extra_pub,
            &[data_var],
        )
    }
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8, U: UserData<F>> UserBul<F, U>
    for IMTObjStore<F, INT_TREE_DEPTH>
{
    type Error = ();

    fn has_never_received_nul(&self, nul: &Nul<F>) -> bool {
        for i in &self.old_nuls {
            if i == nul {
                return false;
            }
        }
        true
    }

    fn append_value<PubArgs, Snark: ark_snark::SNARK<F>, const NUMCBS: usize>(
        &mut self,
        object: Com<F>,
        old_nul: Nul<F>,
        cb_com_list: [Com<F>; NUMCBS],
        _args: PubArgs,
        _proof: Snark::Proof,
        _memb_data: Option<Self::MembershipPub>,
        _verif_key: &Snark::VerifyingKey,
    ) -> Result<(), Self::Error> {
        //let mut rng = thread_rng();
        self.tree.append(object);
        //let new_root = self.get_root();
        self.old_nuls.push(old_nul);
        self.cb_com_lists.push(cb_com_list.into());
        Ok(())
    }
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8, U: UserData<F>> JoinableBulletin<F, U>
    for IMTObjStore<F, INT_TREE_DEPTH>
where
    Standard: Distribution<F>,
{
    type PubData = ();

    fn join_bul(
        &mut self,
        object: crate::generic::object::Com<F>,
        _pub_data: (),
    ) -> Result<(), Self::Error> {
        let mut rng = thread_rng();
        self.tree.append(object);
        self.old_nuls.push(rng.r#gen());
        self.cb_com_lists.push(vec![]);
        Ok(())
    }
}

/// This is a de-centralized nonmembership storage system for tickets.
///
/// Specifically, this trait encompasses nonmembership for plain tickets.
///
///
/// While proofs of membership remain static (a ticket which was once a member will always be a
/// member), this is not true for nonmembership.
///
/// For example, one may have a proof of nonmembership for a ticket at some point in the past, but
/// it could change when the ticket is appended to the bulletin.
///
/// Verifying nonmembership should also account for the epoch. Any nonmembership proof should be
/// unique with respect to the epoch, so any nonmembership witness must encode the information of
/// the epoch.
pub trait NonmembMTStore<F: PrimeField + Absorb>
where
    Standard: Distribution<F>,
{
    /// A nonmembership witness.
    type NonMembershipWitness: Clone + Default;
    /// A nonmembership witness in-circuit.
    type NonMembershipWitnessVar: Clone + AllocVar<Self::NonMembershipWitness, F>;

    /// Nonmembership public data.
    type NonMembershipPub: Clone + Default;
    /// Nonmembership public data in-circuit.
    type NonMembershipPubVar: Clone + AllocVar<Self::NonMembershipPub, F>;

    /// Construct a new nonmembership store.
    fn new(rng: &mut (impl CryptoRng + RngCore)) -> Self;

    /// Get nonmembership data for a specific ticket. If the ticket is a member, this should return
    /// None.
    fn get_nmemb(
        &self,
        tik: &FakeSigPubkey<F>,
    ) -> Option<(Self::NonMembershipPub, Self::NonMembershipWitness)>;

    /// Get the nonmembership public data.
    fn get_nmemb_pub(&self) -> Self::NonMembershipPub;

    /// Return true if the ticket is a non-member, and false if the ticket is a member.
    fn verify_not_in(&self, tik: FakeSigPubkey<F>) -> bool;

    /// Prove nonmembership in-circuit for a ticket. Returns `true` if not a member, and `false` if
    /// a member.
    fn enforce_nonmembership_of(
        tikvar: FakeSigPubkeyVar<F>,
        extra_witness: Self::NonMembershipWitnessVar,
        extra_pub: Self::NonMembershipPubVar,
    ) -> Result<Boolean<F>, SynthesisError>;
}

/// A centralized callback storage system with proofs of membership and nonmembership.
///
/// To add a ticket, the ticket is signed by the private key associated to the callback bulletin.
/// Along with this **the ticket is also inserted into a nonmembership store**, which implements
/// [`NonmembStore`].
///
/// To prove membership, users may then prove knowledge of a signature on the callback ticket which verifies under the
/// public key.
///
/// To prove nonmembership, one uses the [`NonmembStore`] circuit.
#[derive(Clone, Default, Debug)]
pub struct MTCallbackStore<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8, Args>
where
    Standard: Distribution<F>,
    Args: Clone + ToConstraintField<F>,
{
    /// The called tickets.
    pub memb_called_cbs: Vec<(FakeSigPubkey<F>, Args, Time<F>)>,
    /// The Merkle Tree for called tickets.
    pub memb_tree: IncIntTree<F, INT_TREE_DEPTH>,
    /// A nonmembership bulletin for proofs of nonmembership on called tickets.
    pub nmemb_tree: RangeTree<F, INT_TREE_DEPTH>,
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8, Args>
    MTCallbackStore<F, INT_TREE_DEPTH, Args>
where
    Standard: Distribution<F>,
    Args: Clone + ToConstraintField<F>,
{
    /// Construct a new Merkle tree callback store.
    ///
    pub fn new(rng: &mut (impl CryptoRng + RngCore)) -> Self {
        let memb_tree = IncIntTree::default();
        let nmemb_tree = RangeTree::default();

        Self {
            memb_called_cbs: vec![],
            memb_tree,
            nmemb_tree,
        }
    }

    /// Get the Merkle tree root for membership.
    pub fn get_memb_root(&self) -> F {
        self.memb_tree.get_root()
    }

    /// Get the Merkle tree root for non-membership.
    pub fn get_nmemb_root(&self) -> F {
        self.nmemb_tree.get_root()
    }

    /// Get a membership witness (a signature) for a specific ticket. If the ticket is not in the
    /// bulletin, this should return None.
    pub fn get_memb_witness(&self, tik: &FakeSigPubkey<F>) -> Option<IntTreePath<F>> {
        let index = self.memb_tree.get_leaf_index(tik.0);
        if index != usize::MAX {
            Some(self.memb_tree.auth_path(index))
        } else {
            None
        }
    }

    /// Get a nonmembership witness for a ticket. If the ticket is in the bulletin, then this
    /// should return None.
    pub fn get_nmemb_witness(&self, tik: &FakeSigPubkey<F>) -> Option<RangeTreePath<F>> {
        let index = self.nmemb_tree.get_leaf_idx(tik.0);
        if index != usize::MAX {
            Some(self.nmemb_tree.auth_path(index))
        } else {
            None
        }
    }
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8> PublicCallbackBul<F, F, NoSigOTP<F>>
    for MTCallbackStore<F, INT_TREE_DEPTH, F>
where
    Standard: Distribution<F>,
{
    type MembershipWitness = IntTreePath<F>;

    type MembershipWitnessVar = IntTreePathVar<F>;

    type NonMembershipWitness = RangeTreePath<F>;

    type NonMembershipWitnessVar = RangeTreePathVar<F>;

    type MembershipPub = IntTreeRoot<F>;

    type MembershipPubVar = IntTreeRootVar<F>;

    type NonMembershipPub = RangeTreeRoot<F>;

    type NonMembershipPubVar = RangeTreeRootVar<F>;

    fn verify_in(&self, tik: FakeSigPubkey<F>) -> Option<(F, (), Time<F>)> {
        for (t, arg, time) in &self.memb_called_cbs {
            if t == &tik {
                return Some((*arg, (), *time));
            }
        }
        None
    }

    fn verify_not_in(&self, tik: FakeSigPubkey<F>) -> bool {
        let index = self.nmemb_tree.get_leaf_idx(tik.0);
        if index != usize::MAX { true } else { false }
    }

    fn get_membership_data(
        &self,
        tik: FakeSigPubkey<F>,
    ) -> (
        IntTreeRoot<F>,
        IntTreePath<F>,
        RangeTreeRoot<F>,
        RangeTreePath<F>,
    ) {
        let memb_path_idx = self.memb_tree.get_leaf_index(tik.0);
        if memb_path_idx != usize::MAX {
            (
                self.memb_tree.get_root(),
                self.get_memb_witness(&tik).unwrap(),
                self.nmemb_tree.get_root(),
                self.nmemb_tree.auth_path(0),
            )
        } else {
            let nmemb_path_idx = self.nmemb_tree.get_leaf_idx(tik.0);
            (
                self.memb_tree.get_root(),
                self.memb_tree.auth_path(0),
                self.nmemb_tree.get_root(),
                self.nmemb_tree.auth_path(nmemb_path_idx),
            )
        }
    }

    fn enforce_membership_of(
        tikvar: (FakeSigPubkeyVar<F>, FpVar<F>, TimeVar<F>),
        extra_witness: Self::MembershipWitnessVar,
        extra_pub: Self::MembershipPubVar,
    ) -> Result<Boolean<F>, SynthesisError> {
        let tree_params_var: TreeParamsVar<F> = TreeParams::new().to_var();
        let tik_hash = <Poseidon<2>>::hash_in_zk(&[tikvar.0.0, tikvar.1, tikvar.2])?;
        extra_witness.verify_membership(
            &tree_params_var.leaf_params,
            &tree_params_var.two_to_one_params,
            &extra_pub,
            &[tik_hash],
        )
    }

    fn enforce_nonmembership_of(
        tikvar: FakeSigPubkeyVar<F>,
        extra_witness: Self::NonMembershipWitnessVar,
        extra_pub: Self::NonMembershipPubVar,
    ) -> Result<Boolean<F>, SynthesisError> {
        let tree_params_var: TreeParamsVar<F> = TreeParams::new().to_var();
        extra_witness.verify(&tikvar.0, &extra_pub)
    }
}

impl<
    F: PrimeField + Absorb,
    const INT_TREE_DEPTH: u8,
    A: Clone + Default + ToConstraintField<F>,
    AVar: Clone + AllocVar<A, F> + ToConstraintFieldGadget<F>,
> PublicCallbackBul<F, A, NoEnc<F, A, AVar>> for MTCallbackStore<F, INT_TREE_DEPTH, A>
where
    Standard: Distribution<F>,
{
    type MembershipWitness = IntTreePath<F>;

    type MembershipWitnessVar = IntTreePathVar<F>;

    type NonMembershipWitness = RangeTreePath<F>;

    type NonMembershipWitnessVar = RangeTreePathVar<F>;

    type MembershipPub = IntTreeRoot<F>;

    type MembershipPubVar = IntTreeRootVar<F>;

    type NonMembershipPub = RangeTreeRoot<F>;

    type NonMembershipPubVar = RangeTreeRootVar<F>;

    fn verify_in(&self, tik: FakeSigPubkey<F>) -> Option<(A, (), Time<F>)> {
        for (t, arg, time) in &self.memb_called_cbs {
            if t == &tik {
                return Some((arg.clone(), (), *time));
            }
        }
        None
    }

    fn verify_not_in(&self, tik: FakeSigPubkey<F>) -> bool {
        let index = self.nmemb_tree.get_leaf_idx(tik.0);
        if index != usize::MAX { true } else { false }
    }

    fn get_membership_data(
        &self,
        tik: FakeSigPubkey<F>,
    ) -> (
        IntTreeRoot<F>,
        IntTreePath<F>,
        RangeTreeRoot<F>,
        RangeTreePath<F>,
    ) {
        let memb_path_idx = self.memb_tree.get_leaf_index(tik.0);
        if memb_path_idx != usize::MAX {
            (
                self.memb_tree.get_root(),
                self.memb_tree.auth_path(memb_path_idx),
                self.nmemb_tree.get_root(),
                self.nmemb_tree.auth_path(0),
            )
        } else {
            let nmemb_path_idx = self.nmemb_tree.get_leaf_idx(tik.0);
            (
                self.memb_tree.get_root(),
                self.memb_tree.auth_path(0),
                self.nmemb_tree.get_root(),
                self.nmemb_tree.auth_path(nmemb_path_idx),
            )
        }
    }

    fn enforce_membership_of(
        tikvar: (FakeSigPubkeyVar<F>, AVar, TimeVar<F>),
        extra_witness: Self::MembershipWitnessVar,
        extra_pub: Self::MembershipPubVar,
    ) -> Result<Boolean<F>, SynthesisError> {
        let mut v = vec![tikvar.0.0];

        v.extend_from_slice(&tikvar.1.to_constraint_field()?);

        v.push(tikvar.2);

        let tree_params_var: TreeParamsVar<F> = TreeParams::new().to_var();
        let tik_hash = <Poseidon<2>>::hash_in_zk(&v)?;
        extra_witness.verify_membership(
            &tree_params_var.leaf_params,
            &tree_params_var.two_to_one_params,
            &extra_pub,
            &[tik_hash],
        )
    }

    fn enforce_nonmembership_of(
        tikvar: FakeSigPubkeyVar<F>,
        extra_witness: Self::NonMembershipWitnessVar,
        extra_pub: Self::NonMembershipPubVar,
    ) -> Result<Boolean<F>, SynthesisError> {
        let tree_params_var: TreeParamsVar<F> = TreeParams::new().to_var();
        extra_witness.verify(&tikvar.0, &extra_pub)
    }
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8> CallbackBul<F, F, NoSigOTP<F>>
    for MTCallbackStore<F, INT_TREE_DEPTH, F>
where
    Standard: Distribution<F>,
{
    type Error = ();

    fn has_never_received_tik(&self, tik: &FakeSigPubkey<F>) -> bool {
        for (x, _, _) in &self.memb_called_cbs {
            if x == tik {
                return false;
            }
        }
        true
    }

    fn append_value(
        &mut self,
        tik: FakeSigPubkey<F>,
        enc_args: F,
        _signature: (),
        time: Time<F>,
    ) -> Result<(), Self::Error> {
        let tree_params_var: TreeParamsVar<F> = TreeParams::new().to_var();
        let tik_hash = <Poseidon<2>>::hash(&[tik.0, enc_args, time]);
        self.memb_tree.append(tik_hash);
        self.memb_called_cbs.push((tik, enc_args, time));
        Ok(())
    }
}

impl<
    F: PrimeField + Absorb,
    const INT_TREE_DEPTH: u8,
    A: Clone + Default + ToConstraintField<F>,
    AVar: Clone + AllocVar<A, F> + ToConstraintFieldGadget<F>,
> CallbackBul<F, A, NoEnc<F, A, AVar>> for MTCallbackStore<F, INT_TREE_DEPTH, A>
where
    Standard: Distribution<F>,
{
    type Error = ();

    fn has_never_received_tik(&self, tik: &FakeSigPubkey<F>) -> bool {
        for (x, _, _) in &self.memb_called_cbs {
            if x == tik {
                return false;
            }
        }
        true
    }

    fn append_value(
        &mut self,
        tik: FakeSigPubkey<F>,
        enc_args: A,
        _signature: (),
        time: Time<F>,
    ) -> Result<(), Self::Error> {
        let mut rng = thread_rng();
        let mut v2 = vec![];
        v2.push(tik.to());
        v2.extend_from_slice(&enc_args.to_field_elements().unwrap());
        v2.push(time);

        let tree_params_var: TreeParamsVar<F> = TreeParams::new().to_var();
        let tik_hash = <Poseidon<2>>::hash(&v2.as_slice());
        self.memb_tree.append(tik_hash);
        self.memb_called_cbs.push((tik, enc_args, time));
        Ok(())
    }
}

/// A de-centralized storage system for both objects and tickets.
///
/// This consists of object commitment storage, and callback ticket storage.
///
/// Along with that, the central store stores interactions, and so acts as a centralized service
/// provider *and* both bulletins.
#[derive(Clone)]
pub struct DeCentralStore<
    F: PrimeField + Absorb,
    const INT_TREE_DEPTH: u8,
    A: Clone + ToConstraintField<F>,
> where
    Standard: Distribution<F>,
{
    /// The object bulletin storing commitments.
    pub obj_bul: IMTObjStore<F, INT_TREE_DEPTH>,

    /// The callback bulletin storing tickets.
    pub callback_bul: MTCallbackStore<F, INT_TREE_DEPTH, A>,

    /// A list of interactions which have occurred by their interaction id.
    pub interaction_ids: Vec<u64>,
    /// A list of tickets which have not yet been called but handed to the service, each associated
    /// to the interaction id at the same index.
    // pub cb_tickets: Vec<Vec<(CallbackCom<F, F, NoSigOTP<F>>, F)>>,
    pub cb_tickets: Vec<Vec<Vec<u8>>>,
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8> ServiceProvider<F, F, FpVar<F>, NoSigOTP<F>>
    for DeCentralStore<F, INT_TREE_DEPTH, F>
where
    Standard: Distribution<F>,
{
    type Error = ();
    type InteractionData = u64;

    fn has_never_received_tik(&self, tik: FakeSigPubkey<F>) -> bool {
        for j in &self.cb_tickets {
            for k in j {
                let (a, _) =
                    <(CallbackCom<F, F, NoSigOTP<F>>, F)>::deserialize_compressed(&**k).unwrap();
                if a.cb_entry.tik == tik {
                    return false;
                }
            }
        }
        true
    }

    fn store_interaction<U: UserData<F>, Snark: ark_snark::SNARK<F>, const NUMCBS: usize>(
        &mut self,
        interaction: crate::generic::user::ExecutedMethod<F, Snark, F, NoSigOTP<F>, NUMCBS>,
        data: u64,
    ) -> Result<(), Self::Error> {
        self.interaction_ids.push(data);
        let tiks = interaction.cb_tik_list.to_vec();
        let mut v = vec![];
        for tik in tiks {
            let mut ser = vec![];
            tik.serialize_compressed(&mut ser).map_err(|_| ())?;
            v.push(ser);
        }

        self.cb_tickets.push(v);

        Ok(())
    }
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8> DeCentralStore<F, INT_TREE_DEPTH, F>
where
    Standard: Distribution<F>,
{
    /// Get a callback ticket (and signature randomness) so the service provider may call the
    /// callback. This gets the ticket from the index in the list. For each interaction, the set of
    /// callbacks is appended to the list.
    ///
    ///- `index` dictates which interaction.
    ///- `which` dictates which callback for that interaction.
    pub fn get_ticket_ind(
        &self,
        index: usize,
        which: usize,
    ) -> (CallbackCom<F, F, NoSigOTP<F>>, F) {
        <(CallbackCom<F, F, NoSigOTP<F>>, F)>::deserialize_compressed(
            &*self.cb_tickets[index][which],
        )
        .unwrap()
    }

    /// Get a callback ticket (and signature randomness) so the service provider may call the
    /// callback. This gets the ticket by the interaction id. Each interaction is associated with
    /// an interaction id, which should be unique. This function is guaranteed to return a proper
    /// and correct ticket if all ids are unique and the id is within this list. If the id
    /// is not in the list, this function panics.
    pub fn get_ticket_id(&self, id: u64, which: usize) -> (CallbackCom<F, F, NoSigOTP<F>>, F) {
        for i in 0..self.interaction_ids.len() {
            if self.interaction_ids[i] == id {
                return self.get_ticket_ind(i, which);
            }
        }
        panic!("No interaction found.");
    }
}

impl<
    F: PrimeField + Absorb,
    const INT_TREE_DEPTH: u8,
    A: Clone + ToConstraintField<F> + Default,
    AVar: AllocVar<A, F> + Clone,
> ServiceProvider<F, A, AVar, NoEnc<F, A, AVar>> for DeCentralStore<F, INT_TREE_DEPTH, A>
where
    Standard: Distribution<F>,
{
    type Error = ();
    type InteractionData = u64;

    fn has_never_received_tik(&self, tik: FakeSigPubkey<F>) -> bool {
        for j in &self.cb_tickets {
            for k in j {
                let (a, _) =
                    <(CallbackCom<F, A, NoEnc<F, A, AVar>>, F)>::deserialize_compressed(&**k)
                        .unwrap();
                if a.cb_entry.tik == tik {
                    return false;
                }
            }
        }
        true
    }

    fn store_interaction<U: UserData<F>, Snark: ark_snark::SNARK<F>, const NUMCBS: usize>(
        &mut self,
        interaction: ExecutedMethod<F, Snark, A, NoEnc<F, A, AVar>, NUMCBS>,
        data: u64,
    ) -> Result<(), Self::Error> {
        self.interaction_ids.push(data);
        let tiks = interaction.cb_tik_list.to_vec();
        let mut v = vec![];
        for tik in tiks {
            let mut ser = vec![];
            tik.serialize_compressed(&mut ser).map_err(|_| ())?;
            v.push(ser);
        }

        self.cb_tickets.push(v);

        Ok(())
    }
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8, A: Clone + ToConstraintField<F> + Default>
    DeCentralStore<F, INT_TREE_DEPTH, A>
where
    Standard: Distribution<F>,
{
    /// Get a callback ticket (and signature randomness) so the service provider may call the
    /// callback. This gets the ticket from the index in the list. For each interaction, the set of
    /// callbacks is appended to the list.
    ///
    ///- `index` dictates which interaction.
    ///- `which` dictates which callback for that interaction.
    pub fn get_ticket_ind_noenc<AVar: AllocVar<A, F> + Clone>(
        &self,
        index: usize,
        which: usize,
    ) -> (CallbackCom<F, A, NoEnc<F, A, AVar>>, F) {
        <(CallbackCom<F, A, NoEnc<F, A, AVar>>, F)>::deserialize_compressed(
            &*self.cb_tickets[index][which],
        )
        .unwrap()
    }

    /// Get a callback ticket (and signature randomness) so the service provider may call the
    /// callback. This gets the ticket by the interaction id. Each interaction is associated with
    /// an interaction id, which should be unique. This function is guaranteed to return a proper
    /// and correct ticket if all ids are unique and the id is within this list. If the id
    /// is not in the list, this function panics.
    pub fn get_ticket_id_noenc<AVar: AllocVar<A, F> + Clone>(
        &self,
        id: u64,
        which: usize,
    ) -> (CallbackCom<F, A, NoEnc<F, A, AVar>>, F) {
        for i in 0..self.interaction_ids.len() {
            if self.interaction_ids[i] == id {
                return self.get_ticket_ind_noenc(i, which);
            }
        }
        panic!("No interaction found.");
    }
}

impl<F: PrimeField + Absorb, const INT_TREE_DEPTH: u8, A: Clone + ToConstraintField<F>>
    DeCentralStore<F, INT_TREE_DEPTH, A>
where
    Standard: Distribution<F>,
{
    /// Construct a new central store.
    pub fn new(rng: &mut (impl CryptoRng + RngCore)) -> Self {
        let MKCbStore = MTCallbackStore {
            memb_called_cbs: vec![],
            memb_tree: IncIntTree::blank(),
            nmemb_tree: RangeTree::blank(),
        };
        Self {
            obj_bul: IMTObjStore::default(),
            callback_bul: MKCbStore,
            interaction_ids: vec![],
            cb_tickets: vec![],
        }
    }
}
