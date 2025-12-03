use crate::{
    crypto::{enc::AECipherSigZK, hash::FieldHash},
    generic::{
        bulletin::{PublicCallbackBul, PublicUserBul},
        callbacks::{CallbackCom, CallbackComVar, add_ticket_to_hc_zk, create_defaults},
        object::{Com, ComVar, Id, Nul, NulVar, Time},
        scan::{PubScanArgs, get_scan_interaction},
        user::{User, UserData, UserVar},
    },
    util::ArrayVar,
};
use ark_crypto_primitives::sponge::Absorb;
use ark_ff::PrimeField;
use ark_r1cs_std::{alloc::AllocVar, boolean::Boolean, eq::EqGadget, select::CondSelectGadget};
use ark_relations::{
    ns,
    r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Result as ArkResult},
};
use ark_snark::SNARK;
use core::marker::PhantomData;
use incrementalmerkletree_testing::incremental_int_tree::IntTreePath;
use rand::{
    CryptoRng, RngCore,
    distributions::{Distribution, Standard},
};

/// A predicate.
///
/// This is a function `f(U, U', A, B) -> bool`, which outputs true if the old user
/// and new user satisfy some predicate.
///
/// An example predicate could be
/// ```rust
///# use ark_bls12_381::Fr;
///# use zk_callbacks::generic::user::UserVar;
///# use zk_callbacks::zk_object;
///# use ark_r1cs_std::prelude::Boolean;
///# use ark_r1cs_std::eq::EqGadget;
///# use ark_relations::r1cs::{Result as ArkResult};
///#  #[zk_object(Fr)]
///#  #[derive(Default)]
///#  struct Data {
///#      pub rep: Fr,
///#  }
///#
/// fn pred<'a>(old: &'a UserVar<Fr, Data>, new: &'a UserVar<Fr, Data>, _pub: (), _priv: ()) -> ArkResult<Boolean<Fr>> {
///     old.data.rep.is_eq(&new.data.rep)
/// }
/// ```
pub type Predicate<F, UserVar, PubArgsVar, PrivArgsVar> =
    fn(&UserVar, &UserVar, PubArgsVar, PrivArgsVar) -> ArkResult<Boolean<F>>;

/// A predicate on a single user.
///
/// This is a function `f(U, Com(U), A, B) -> bool`, which outputs
/// true if the user satisfies some predicate.
///
/// An example singular predicate could be
/// ```rust
///# use ark_bls12_381::Fr;
///# use zk_callbacks::generic::user::UserVar;
///# use zk_callbacks::zk_object;
///# use ark_r1cs_std::prelude::Boolean;
///# use ark_r1cs_std::eq::EqGadget;
///# use ark_relations::r1cs::{Result as ArkResult};
///# use ark_r1cs_std::fields::fp::FpVar;
///#  #[zk_object(Fr)]
///#  #[derive(Default)]
///#  struct Data {
///#      pub rep: Fr,
///#  }
///#
/// fn pred<'a, 'b>(old: &'a UserVar<Fr, Data>, _com: &'b FpVar<Fr>, _pub: (), _priv: ()) -> ArkResult<Boolean<Fr>> {
///     old.data.rep.is_eq(&FpVar::Constant(Fr::from(3)))
/// }
/// ```
pub type SingularPredicate<F, UserVar, PubUserCom, PubArgsVar, PrivArgsVar> =
    fn(&UserVar, &PubUserCom, PubArgsVar, PrivArgsVar) -> ArkResult<Boolean<F>>;
/// A method.
///
/// This is a function `f(U, A, B) -> U'` which modifies a user based on some private and public
/// arguments.
///
/// An example method could be
/// ```rust
///# use ark_bls12_381::Fr;
///# use zk_callbacks::generic::user::UserVar;
///# use zk_callbacks::zk_object;
///# use zk_callbacks::generic::user::User;
///# use ark_r1cs_std::prelude::Boolean;
///# use ark_r1cs_std::eq::EqGadget;
///# use ark_relations::r1cs::{Result as ArkResult};
///#  #[zk_object(Fr)]
///#  #[derive(Default)]
///#  struct Data {
///#      pub rep: Fr,
///#  }
///#
/// fn method<'a>(old: &'a User<Fr, Data>, _pub: (), _priv: ()) -> User<Fr, Data> {
///     let mut a = old.clone();
///     a.data.rep += Fr::from(1);
///     a
/// }
///```
pub type Method<User, PubArgs, PrivArgs> = fn(&User, PubArgs, PrivArgs) -> User;
/// A method without private arguments.
///
/// This is a function `f(U, A) -> U'` which does not have any private arguments. For example, a
/// method in a callback takes in public arguments provided by the server.
///
/// An example method could be
/// ```rust
///# use ark_bls12_381::Fr;
///# use zk_callbacks::generic::user::UserVar;
///# use zk_callbacks::zk_object;
///# use zk_callbacks::generic::user::User;
///# use ark_r1cs_std::prelude::Boolean;
///# use ark_r1cs_std::eq::EqGadget;
///# use ark_relations::r1cs::{Result as ArkResult};
///#  #[zk_object(Fr)]
///#  #[derive(Default)]
///#  struct Data {
///#      pub rep: Fr,
///#  }
///#
/// fn nopriv_method<'a>(old: &'a User<Fr, Data>, pub_dat: Fr) -> User<Fr, Data> {
///     let mut a = old.clone();
///     a.data.rep = pub_dat;
///     a
/// }
///```
pub type NoPrivMethod<User, Args> = fn(&User, Args) -> User;
/// An in-circuit method update.
///
/// This is meant for interatively scanning callback methods to update the user variable. Note that
/// this is **not a predicate**, this should just perform an update in-circuit.
///
/// An example method may be the following:
/// ```rust
///# use ark_bls12_381::Fr;
///# use zk_callbacks::generic::user::UserVar;
///# use zk_callbacks::zk_object;
///# use zk_callbacks::generic::user::User;
///# use ark_r1cs_std::prelude::Boolean;
///# use ark_r1cs_std::eq::EqGadget;
///# use ark_r1cs_std::fields::fp::FpVar;
///# use ark_relations::r1cs::{Result as ArkResult};
///#  #[zk_object(Fr)]
///#  #[derive(Default)]
///#  struct Data {
///#      pub rep: Fr,
///#  }
///#
/// fn nopriv_cbmethod_var<'a>(old: &'a UserVar<Fr, Data>, pub_dat: FpVar<Fr>) -> ArkResult<UserVar<Fr, Data>> {
///     let mut a = old.clone();
///     a.data.rep = pub_dat;
///     Ok(a)
/// }
///```
pub type NoPrivMethodVar<UserVar, ArgsVar> = fn(&UserVar, ArgsVar) -> ArkResult<UserVar>;

/// A callback. This consists of the data of the function along with expiry information.
///
/// This is not a callback *ticket*. This is a representation of a callback, which is the method
/// called by the service on the user.
///
/// While many callback tickets may be allocated during a session, callbacks should be static
/// throughout the program, and are initialized on startup. The callbacks determine the scan
/// circuit being performed.
///
/// # Example
/// ```rust
/// # use zk_callbacks::zk_object;
/// # use zk_callbacks::generic::user::User;
/// # use rand::thread_rng;
/// # use ark_bn254::{Bn254 as E, Fr};
/// # use ark_r1cs_std::eq::EqGadget;
/// # use ark_r1cs_std::cmp::CmpGadget;
/// # use zk_callbacks::generic::interaction::Interaction;
/// # use zk_callbacks::generic::interaction::Callback;
/// # use zk_callbacks::generic::object::Id;
/// # use zk_callbacks::generic::object::Time;
/// # use zk_callbacks::generic::object::TimeVar;
/// # use ark_relations::r1cs::SynthesisError;
/// # use zk_callbacks::generic::user::UserVar;
/// # use ark_r1cs_std::fields::fp::FpVar;
/// # use ark_groth16::Groth16;
/// # use ark_r1cs_std::prelude::Boolean;
/// # use zk_callbacks::generic::bulletin::UserBul;
/// # use zk_callbacks::impls::hash::Poseidon;
/// # use ark_r1cs_std::prelude::UInt8;
/// # use zk_callbacks::impls::dummy::DummyStore;
/// # use zk_callbacks::generic::scan::get_scan_interaction;
/// # use zk_callbacks::generic::scan::PubScanArgs;
/// # use ark_r1cs_std::select::CondSelectGadget;
/// # use zk_callbacks::impls::centralized::crypto::{FakeSigPrivkey, FakeSigPubkey, NoSigOTP};
/// # use zk_callbacks::scannable_zk_object;
/// # type Groth = Groth16<E>;
/// # type PubScan = PubScanArgs<Fr, Data, Fr, FpVar<Fr>, NoSigOTP<Fr>, DummyStore, 1>;
/// #[scannable_zk_object(Fr)]
/// #[derive(Default)]
/// struct Data {
///     pub num_visits: Fr,
///     pub bad_rep: u8,
///     pub last_interacted_time: Time<Fr>,
/// }
///
/// fn callback<'a>(old_user: &'a User<Fr, Data>, args: Fr) -> User<Fr, Data> {
///     let mut u2 = old_user.clone();
///     if args == Fr::from(0) {
///         u2.data.bad_rep;
///     } else {
///         u2.data.bad_rep += 10;
///     }
///     u2.clone()
/// }
///
/// fn enforce_callback<'a>(old_user: &'a UserVar<Fr, Data>, args: FpVar<Fr>) -> Result<UserVar<Fr, Data>, SynthesisError> {
///     let mut u = old_user.clone();
///     u.data.bad_rep =
///     UInt8::conditionally_select(
///         &args.is_eq(&FpVar::Constant(Fr::from(0)))?,
///         &u.data.bad_rep,
///         &u.data.bad_rep.wrapping_add(&UInt8::constant(10))
///     )?;
///     Ok(u)
/// }
///
/// fn main () {
///     let cb = Callback {
///         method_id: Id::from(0),
///         expirable: true,
///         expiration: Time::from(25),
///         method: callback,
///         predicate: enforce_callback
///     };
/// }
#[derive(Clone)]
pub struct Callback<F: PrimeField + Absorb, U: UserData<F>, Args, ArgsVar: AllocVar<Args, F>> {
    /// Identifies the method. This should be unique per callback.
    pub method_id: Id<F>,
    /// Whether this callback can expire.
    pub expirable: bool,
    /// If the callback can expire, this is the time the callback should expire by.
    pub expiration: Time<F>,
    /// The update method which changes the user.
    pub method: NoPrivMethod<User<F, U>, Args>,
    /// The update method in-circuit, which changes the in-circuit representation of the user.
    pub predicate: NoPrivMethodVar<UserVar<F, U>, ArgsVar>,
}

impl<F: PrimeField + Absorb, U: UserData<F>, Args, ArgsVar: AllocVar<Args, F>> std::fmt::Debug
    for Callback<F, U, Args, ArgsVar>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Callback: {}", self.method_id)
    }
}

/// A constant size array of `N` callbacks, of type [`Callback`].
pub type CallbackList<F, U, A, X, const N: usize> = [Callback<F, U, A, X>; N];

/// A pair of a method and a predicate.
///
/// This consists of a pair of functions (`f(U, args) -> U'`, `p(U, U', args) -> bool`). The first
/// function updates the user object, while the second enforces some statement on the update.
pub type MethProof<F, U, PubArgs, PubArgsVar, PrivArgs, PrivArgsVar> = (
    Method<User<F, U>, PubArgs, PrivArgs>,
    Predicate<F, UserVar<F, U>, PubArgsVar, PrivArgsVar>,
);

/// An interaction.
///
/// An interaction consists of a method, predicate, and a list of callbacks. When a user interacts
/// via a specific interaction, the method is executed on the user, the predicate is enforced via a
/// proof, and callback tickets are appended (for each callback in the list respectively).
///
/// # Example
/// ```rust
/// # use zk_callbacks::zk_object;
/// # use zk_callbacks::generic::user::User;
/// # use rand::thread_rng;
/// # use ark_bn254::{Bn254 as E, Fr};
/// # use ark_r1cs_std::eq::EqGadget;
/// # use ark_r1cs_std::cmp::CmpGadget;
/// # use zk_callbacks::generic::interaction::Interaction;
/// # use zk_callbacks::generic::interaction::Callback;
/// # use zk_callbacks::generic::object::Id;
/// # use zk_callbacks::generic::object::Time;
/// # use zk_callbacks::generic::object::TimeVar;
/// # use ark_relations::r1cs::SynthesisError;
/// # use zk_callbacks::generic::user::UserVar;
/// # use ark_r1cs_std::fields::fp::FpVar;
/// # use ark_groth16::Groth16;
/// # use ark_r1cs_std::prelude::Boolean;
/// # use zk_callbacks::generic::bulletin::UserBul;
/// # use zk_callbacks::impls::hash::Poseidon;
/// # use ark_r1cs_std::prelude::UInt8;
/// # use zk_callbacks::impls::dummy::DummyStore;
/// # use zk_callbacks::generic::scan::get_scan_interaction;
/// # use zk_callbacks::generic::scan::PubScanArgs;
/// # use ark_r1cs_std::select::CondSelectGadget;
/// # use zk_callbacks::impls::centralized::crypto::{FakeSigPrivkey, FakeSigPubkey, NoSigOTP};
/// # use zk_callbacks::scannable_zk_object;
/// # type Groth = Groth16<E>;
///
/// type PubScan = PubScanArgs<Fr, Data, Fr, FpVar<Fr>, NoSigOTP<Fr>, DummyStore, 1>;
/// #[scannable_zk_object(Fr)]
/// #[derive(Default)]
/// struct Data {
///     pub num_visits: Fr,
///     pub bad_rep: u8,
///     pub last_interacted_time: Time<Fr>,
/// }
///
/// fn method<'a>(old_user: &'a User<Fr, Data>, pub_time: Time<Fr>, _priv: ()) -> User<Fr, Data> {
///     let mut new = old_user.clone();
///     new.data.num_visits += Fr::from(1);
///     new.data.last_interacted_time = pub_time;
///     new
/// }
///
/// fn predicate<'a>(old_user: &'a UserVar<Fr, Data>, new_user: &'a UserVar<Fr, Data>, pub_time: TimeVar<Fr>, _priv: ()) -> Result<Boolean<Fr>, SynthesisError> {
///     let o1 = old_user.data.bad_rep.is_eq(&new_user.data.bad_rep)?;
///     let o2 = old_user.data.bad_rep.is_le(&UInt8::constant(40))?;
///     let o3 = new_user.data.num_visits.is_eq(&(old_user.data.num_visits.clone() + FpVar::Constant(Fr::from(1))))?;
///     let o4 = new_user.data.last_interacted_time.is_eq(&pub_time)?;
///     Ok(o1 & o2 & o3 & o4)
/// }
///
/// fn callback<'a>(old_user: &'a User<Fr, Data>, args: Fr) -> User<Fr, Data> {
///     let mut u2 = old_user.clone();
///     if args == Fr::from(0) {
///         u2.data.bad_rep;
///     } else {
///         u2.data.bad_rep += 10;
///     }
///     u2.clone()
/// }
///
/// fn enforce_callback<'a>(old_user: &'a UserVar<Fr, Data>, args: FpVar<Fr>) -> Result<UserVar<Fr, Data>, SynthesisError> {
///     let mut u = old_user.clone();
///     u.data.bad_rep =
///     UInt8::conditionally_select(
///         &args.is_eq(&FpVar::Constant(Fr::from(0)))?,
///         &u.data.bad_rep,
///         &u.data.bad_rep.wrapping_add(&UInt8::constant(10))
///     )?;
///     Ok(u)
/// }
///
///
/// fn main () {
///     let cb = Callback {
///         method_id: Id::from(0),
///         expirable: false,
///         expiration: Time::from(10),
///         method: callback,
///         predicate: enforce_callback
///     };
///
///     let cb_methods = vec![cb.clone()];
///
///     let int = Interaction {
///         meth: (method, predicate),
///         callbacks: [cb.clone()],
///     };
/// }
#[derive(Clone)]
pub struct Interaction<
    F: PrimeField + Absorb,
    U: UserData<F>,
    PubArgs: Clone,
    PubArgsVar: AllocVar<PubArgs, F>,
    PrivArgs: Clone,
    PrivArgsVar: AllocVar<PrivArgs, F>,
    CBArgs: Clone,
    CBArgsVar: AllocVar<CBArgs, F>,
    const NUMCBS: usize,
> {
    /// A method and a predicate. For example, one may have an update method, with a predicate
    /// enforcing some reputation status.
    pub meth: MethProof<F, U, PubArgs, PubArgsVar, PrivArgs, PrivArgsVar>,
    /// A list of callbacks.
    pub callbacks: CallbackList<F, U, CBArgs, CBArgsVar, NUMCBS>,
}

impl<
    F: PrimeField + Absorb,
    U: UserData<F> + Default,
    PubArgs: Clone + Default + std::fmt::Debug,
    PubArgsVar: AllocVar<PubArgs, F> + Clone,
    PrivArgs: Clone + Default + std::fmt::Debug,
    PrivArgsVar: AllocVar<PrivArgs, F> + Clone,
    CBArgs: Clone + Default + std::fmt::Debug,
    CBArgsVar: AllocVar<CBArgs, F> + Clone,
    const NUMCBS: usize,
> Interaction<F, U, PubArgs, PubArgsVar, PrivArgs, PrivArgsVar, CBArgs, CBArgsVar, NUMCBS>
where
    Standard: Distribution<F>,
{
    /// Generate proving and verification keys for an interaction.
    ///
    /// If the public membership data is a constant, it must be encoded into the key, and so it
    /// must be set in `memb_data`. Otherwise, the `memb_data` should be set to `None`.
    ///
    /// For `aux_data`, if the auxiliary public arguments to the interaction method is a constant,
    /// this should be done in the `AllocVar` implementation of the auxiliary data type.
    ///
    /// # Example
    /// ```rust
    /// # use zk_callbacks::zk_object;
    /// # use zk_callbacks::generic::user::User;
    /// # use rand::thread_rng;
    /// # use ark_bn254::{Bn254 as E, Fr};
    /// # use ark_r1cs_std::eq::EqGadget;
    /// # use zk_callbacks::generic::interaction::Interaction;
    /// # use zk_callbacks::generic::interaction::Callback;
    /// # use zk_callbacks::generic::object::Id;
    /// # use zk_callbacks::generic::object::Time;
    /// # use ark_relations::r1cs::SynthesisError;
    /// # use zk_callbacks::generic::user::UserVar;
    /// # use ark_r1cs_std::fields::fp::FpVar;
    /// # use ark_groth16::Groth16;
    /// # use ark_r1cs_std::prelude::Boolean;
    /// # use zk_callbacks::impls::hash::Poseidon;
    /// # use zk_callbacks::impls::dummy::DummyStore;
    /// # use zk_callbacks::impls::centralized::crypto::{FakeSigPubkey, NoSigOTP};
    /// # type Groth = Groth16<E>;
    ///#  #[zk_object(Fr)]
    ///#  #[derive(Default)]
    ///#  struct Data {
    ///#      karma: Fr,
    ///#      is_banned: bool,
    ///#  }
    ///#
    ///#  fn method<'a>(old_user: &'a User<Fr, Data>, _pub: (), _priv: ()) -> User<Fr, Data> {
    ///#      old_user.clone()
    ///#  }
    ///#
    ///#  fn predicate<'a>(old_user: &'a UserVar<Fr, Data>, new_user: &'a UserVar<Fr, Data>, _pub: (), _priv: ()) -> Result<Boolean<Fr>, SynthesisError> {
    ///#      let o1 = old_user.data.karma.is_eq(&new_user.data.karma)?;
    ///#      let o2 = old_user.data.is_banned.is_eq(&new_user.data.is_banned)?;
    ///#      Ok(o1 & o2)
    ///#  }
    ///#
    ///#  fn callback<'a>(old_user: &'a User<Fr, Data>, args: Fr) -> User<Fr, Data> {
    ///#      let mut u = old_user.clone();
    ///#      u.data.karma = args;
    ///#      u
    ///#  }
    ///#
    ///#  fn enforce_callback<'a>(old_user: &'a UserVar<Fr, Data>, args: FpVar<Fr>) -> Result<UserVar<Fr, Data>, SynthesisError> {
    ///#      let mut u = old_user.clone();
    ///#      u.data.karma = args;
    ///#      Ok(u)
    ///#  }
    ///#
    ///#
    /// fn main () {
    ///     let cb = Callback {
    ///         method_id: Id::from(0),
    ///         expirable: false,
    ///         expiration: Time::from(10),
    ///         method: callback,
    ///         predicate: enforce_callback
    ///     };
    ///
    ///     let int = Interaction {
    ///         meth: (method, predicate),
    ///         callbacks: [cb.clone()],
    ///     };
    ///
    ///     let mut rng = thread_rng();
    ///
    ///     let (pk, vk) = int.generate_keys::<Poseidon<2>, Groth, NoSigOTP<Fr>, DummyStore>(&mut rng, Some(()), None, false);
    /// }
    /// ```
    pub fn generate_keys<
        H: FieldHash<F>,
        Snark: SNARK<F>,
        Crypto: AECipherSigZK<F, CBArgs>,
        Bul: PublicUserBul<F, U>,
    >(
        &self,
        rng: &mut (impl CryptoRng + RngCore),
        memb_data: Option<Bul::MembershipPub>,
        aux_data: PubArgs,
        is_scan: bool,
    ) -> (Snark::ProvingKey, Snark::VerifyingKey) {
        let u = User::create(U::default(), rng);

        let cbs: [CallbackCom<F, CBArgs, Crypto>; NUMCBS] =
            create_defaults((*self).clone(), <Time<F>>::default());

        let x = (*self).clone();

        let out: ExecMethodCircuit<
            F,
            H,
            U,
            PubArgs,
            PubArgsVar,
            PrivArgs,
            PrivArgsVar,
            CBArgs,
            CBArgsVar,
            Crypto,
            Bul,
            NUMCBS,
        > = ExecMethodCircuit {
            priv_old_user: u.clone(),
            priv_new_user: u.clone(),
            priv_issued_callbacks: cbs.clone(),
            priv_bul_membership_witness: Bul::MembershipWitness::default(),
            priv_args: PrivArgs::default(),

            pub_new_com: u.commit::<H>(),
            pub_old_nul: u.zk_fields.nul,
            pub_issued_callback_coms: cbs.map(|x| x.commit::<H>()),
            pub_args: aux_data,
            associated_method: x,
            is_scan,
            bul_memb_is_const: memb_data.is_some(),
            pub_bul_membership_data: memb_data.unwrap_or_default(),
            _phantom_hash: PhantomData,
        };

        Snark::circuit_specific_setup(out, rng).unwrap()
    }

    /// generate_keys for mt
    pub fn generate_keys_mt<
        H: FieldHash<F>,
        Snark: SNARK<F>,
        Crypto: AECipherSigZK<F, CBArgs>,
        Bul: PublicUserBul<F, U>,
    >(
        &self,
        rng: &mut (impl CryptoRng + RngCore),
        memb_data: Option<Bul::MembershipPub>,
        aux_data: PubArgs,
        is_scan: bool,
        wit_default: Bul::MembershipWitness,
    ) -> (Snark::ProvingKey, Snark::VerifyingKey) {
        let u = User::create(U::default(), rng);

        let cbs: [CallbackCom<F, CBArgs, Crypto>; NUMCBS] =
            create_defaults((*self).clone(), <Time<F>>::default());

        let x = (*self).clone();

        let out: ExecMethodCircuit<
            F,
            H,
            U,
            PubArgs,
            PubArgsVar,
            PrivArgs,
            PrivArgsVar,
            CBArgs,
            CBArgsVar,
            Crypto,
            Bul,
            NUMCBS,
        > = ExecMethodCircuit {
            priv_old_user: u.clone(),
            priv_new_user: u.clone(),
            priv_issued_callbacks: cbs.clone(),
            priv_bul_membership_witness: wit_default,
            priv_args: PrivArgs::default(),

            pub_new_com: u.commit::<H>(),
            pub_old_nul: u.zk_fields.nul,
            pub_issued_callback_coms: cbs.map(|x| x.commit::<H>()),
            pub_args: aux_data,
            associated_method: x,
            is_scan,
            bul_memb_is_const: memb_data.is_some(),
            pub_bul_membership_data: memb_data.unwrap_or_default(),
            _phantom_hash: PhantomData,
        };

        Snark::circuit_specific_setup(out, rng).unwrap()
    }
}

/// The circuit used to generating proofs of an executed method. This is not necessary for use with the base system.
pub struct ExecMethodCircuit<
    F: PrimeField + Absorb,
    H: FieldHash<F>,
    U: UserData<F>,
    PubArgs: Clone,
    PubArgsVar: AllocVar<PubArgs, F>,
    PrivArgs: Clone,
    PrivArgsVar: AllocVar<PrivArgs, F>,
    CBArgs: Clone,
    CBArgsVar: AllocVar<CBArgs, F>,
    Crypto: AECipherSigZK<F, CBArgs>,
    Bul: PublicUserBul<F, U>,
    const NUMCBS: usize,
> {
    // Private Inputs
    /// The old user object.
    pub priv_old_user: User<F, U>,
    /// The new user object.
    pub priv_new_user: User<F, U>,
    /// The issued callback tickets.
    pub priv_issued_callbacks: [CallbackCom<F, CBArgs, Crypto>; NUMCBS],
    /// The membership witness for the old object.
    pub priv_bul_membership_witness: Bul::MembershipWitness,
    /// Private arguments to the associated method.
    pub priv_args: PrivArgs,

    // Public Inputs
    /// The commitment to the new object.
    pub pub_new_com: Com<F>,
    /// The nullifier of the old object.
    pub pub_old_nul: Nul<F>,
    /// Commitments to the callback tickets.
    pub pub_issued_callback_coms: [Com<F>; NUMCBS],
    /// Public arguments to the associated method.
    pub pub_args: PubArgs,
    /// Public membership data for the old object.
    pub pub_bul_membership_data: Bul::MembershipPub,
    /// If the public membership data is constant.
    pub bul_memb_is_const: bool,

    /// The method.
    pub associated_method:
        Interaction<F, U, PubArgs, PubArgsVar, PrivArgs, PrivArgsVar, CBArgs, CBArgsVar, NUMCBS>,
    /// If this circuit should remove checks for not scanning.
    pub is_scan: bool,
    /// The hash used for commitments.
    pub _phantom_hash: PhantomData<H>,
}

impl<
    F: PrimeField + Absorb,
    H: FieldHash<F>,
    U: UserData<F>,
    PubArgs: Clone + std::fmt::Debug,
    PubArgsVar: AllocVar<PubArgs, F>,
    PrivArgs: Clone + std::fmt::Debug,
    PrivArgsVar: AllocVar<PrivArgs, F>,
    CBArgs: Clone + std::fmt::Debug,
    CBArgsVar: AllocVar<CBArgs, F>,
    Crypto: AECipherSigZK<F, CBArgs>,
    Bul: PublicUserBul<F, U>,
    const NUMCBS: usize,
> ConstraintSynthesizer<F>
    for ExecMethodCircuit<
        F,
        H,
        U,
        PubArgs,
        PubArgsVar,
        PrivArgs,
        PrivArgsVar,
        CBArgs,
        CBArgsVar,
        Crypto,
        Bul,
        NUMCBS,
    >
{
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ArkResult<()> {
        // Create private variables
        let old_user_var = UserVar::new_witness(ns!(cs, "old_user"), || Ok(self.priv_old_user))?;
        let new_user_var = UserVar::new_witness(ns!(cs, "new_user"), || Ok(self.priv_new_user))?;
        let issued_cbs: ArrayVar<CallbackComVar<F, CBArgs, Crypto>, NUMCBS> =
            ArrayVar::new_witness(ns!(cs, "issued_cbs"), || Ok(&self.priv_issued_callbacks))?;
        let priv_bul_witness =
            Bul::MembershipWitnessVar::new_witness(ns!(cs, "priv_bul_witness"), || {
                Ok(&self.priv_bul_membership_witness)
            })?;
        let priv_args_var = PrivArgsVar::new_witness(ns!(cs, "priv_args"), || Ok(&self.priv_args))?;

        // Create public variables
        let new_com_var = ComVar::new_input(ns!(cs, "new_com"), || Ok(&self.pub_new_com))?;
        let old_nul_var = NulVar::new_input(ns!(cs, "old_nul"), || Ok(&self.pub_old_nul))?;
        let pub_args_var = PubArgsVar::new_input(ns!(cs, "pub_args"), || Ok(&self.pub_args))?;

        let issued_cb_coms: ArrayVar<ComVar<F>, NUMCBS> =
            ArrayVar::new_input(ns!(cs, "issued_cb_coms"), || {
                Ok(&self.pub_issued_callback_coms)
            })?;

        let pub_bul_data = match self.bul_memb_is_const {
            true => Bul::MembershipPubVar::new_constant(cs.clone(), &self.pub_bul_membership_data)?,
            false => Bul::MembershipPubVar::new_input(ns!(cs, "pub_bul_data"), || {
                Ok(&self.pub_bul_membership_data)
            })?,
        };

        // Enforce old_user in bulletin
        Bul::enforce_membership_of(
            User::commit_in_zk::<H>(old_user_var.clone())?,
            priv_bul_witness,
            pub_bul_data,
        )?
        .enforce_equal(&Boolean::TRUE)?;

        // Enforce any method-specific predicates
        let b = (self.associated_method.meth.1)(
            &old_user_var,
            &new_user_var,
            pub_args_var,
            priv_args_var,
        )?;

        b.enforce_equal(&Boolean::TRUE)?;

        let mut old_zk_fields = old_user_var.clone().zk_fields;
        let new_zk_fields = new_user_var.clone().zk_fields;

        // Enforce revealed nullifier (previous state) == the old nullifier
        old_nul_var.enforce_equal(&old_zk_fields.nul)?;

        // Enforce we are currently not sweeping.
        if !self.is_scan {
            old_zk_fields.is_ingest_over.enforce_equal(&Boolean::TRUE)?;
        }

        if !self.is_scan {
            for i in 0..NUMCBS {
                // Enforce that the callback commitments are well-formed
                issued_cb_coms.0[i]
                    .enforce_equal(&CallbackCom::commit_in_zk::<H>(issued_cbs.0[i].clone())?)?;

                // Append callbacks to the callback list
                add_ticket_to_hc_zk::<F, H, CBArgs, Crypto>(
                    &mut old_zk_fields.callback_hash,
                    issued_cbs.0[i].clone().cb_entry,
                )?;
            }

            old_zk_fields.old_in_progress_callback_hash = old_zk_fields.callback_hash.clone();

            // Enforce new == the updated states
            new_zk_fields
                .callback_hash
                .enforce_equal(&old_zk_fields.callback_hash)?;

            new_zk_fields
                .old_in_progress_callback_hash
                .enforce_equal(&old_zk_fields.old_in_progress_callback_hash)?;

            new_zk_fields
                .new_in_progress_callback_hash
                .enforce_equal(&old_zk_fields.new_in_progress_callback_hash)?;

            new_zk_fields
                .is_ingest_over
                .enforce_equal(&old_zk_fields.is_ingest_over)?;
        }

        // Enforce that Com(new_user) == new_com
        let com = User::commit_in_zk::<H>(new_user_var)?;

        new_com_var.enforce_equal(&com)?;

        Ok(())
    }
}

impl<
    F: PrimeField + Absorb,
    H: FieldHash<F>,
    U: UserData<F>,
    PubArgs: Clone,
    PubArgsVar: AllocVar<PubArgs, F> + Clone,
    PrivArgs: Clone,
    PrivArgsVar: AllocVar<PrivArgs, F> + Clone,
    CBArgs: Clone,
    CBArgsVar: AllocVar<CBArgs, F> + Clone,
    Crypto: AECipherSigZK<F, CBArgs>,
    Bul: PublicUserBul<F, U>,
    const NUMCBS: usize,
> Clone
    for ExecMethodCircuit<
        F,
        H,
        U,
        PubArgs,
        PubArgsVar,
        PrivArgs,
        PrivArgsVar,
        CBArgs,
        CBArgsVar,
        Crypto,
        Bul,
        NUMCBS,
    >
{
    fn clone(&self) -> Self {
        Self {
            priv_old_user: self.priv_old_user.clone(),
            priv_new_user: self.priv_new_user.clone(),
            priv_issued_callbacks: self.priv_issued_callbacks.clone(),
            priv_bul_membership_witness: self.priv_bul_membership_witness.clone(),
            priv_args: self.priv_args.clone(),

            pub_new_com: self.pub_new_com,
            pub_old_nul: self.pub_old_nul,
            pub_issued_callback_coms: self.pub_issued_callback_coms,
            pub_args: self.pub_args.clone(),
            pub_bul_membership_data: self.pub_bul_membership_data.clone(),
            bul_memb_is_const: self.bul_memb_is_const,

            is_scan: self.is_scan,
            associated_method: self.associated_method.clone(),
            _phantom_hash: self._phantom_hash,
        }
    }
}

/// Generate keys for proving a statement about a user object.
///
/// This is associated to the [`User::prove_statement`] function. For a predicate being shown for
/// the user, this generates the keys for the proof.
///
/// Note that the commitment to the user for these statements is public.
///
/// For `aux_data`, if the auxiliary public arguments to the predicate are constant,
/// this should be done in the `AllocVar` implementation of the auxiliary data type.
///
///# Example
/// ```rust
/// # use zk_callbacks::zk_object;
/// # use zk_callbacks::generic::user::User;
/// # use rand::thread_rng;
/// # use ark_bn254::{Bn254 as E, Fr};
/// # use ark_r1cs_std::eq::EqGadget;
/// # use ark_r1cs_std::cmp::CmpGadget;
/// # use zk_callbacks::generic::interaction::Interaction;
/// # use zk_callbacks::generic::interaction::Callback;
/// # use zk_callbacks::generic::object::Id;
/// # use zk_callbacks::generic::object::Time;
/// # use zk_callbacks::generic::object::TimeVar;
/// # use ark_relations::r1cs::SynthesisError;
/// # use zk_callbacks::generic::user::UserVar;
/// # use ark_r1cs_std::fields::fp::FpVar;
/// # use ark_groth16::Groth16;
/// # use ark_r1cs_std::prelude::Boolean;
/// # use zk_callbacks::impls::hash::Poseidon;
/// # use ark_r1cs_std::prelude::UInt8;
/// # use zk_callbacks::impls::dummy::DummyStore;
/// # use ark_r1cs_std::select::CondSelectGadget;
/// # use zk_callbacks::generic::interaction::generate_keys_for_statement;
/// # use zk_callbacks::impls::centralized::crypto::{NoSigOTP};
/// # type Groth = Groth16<E>;
/// #[zk_object(Fr)]
/// #[derive(Default)]
/// struct Data {
///     pub num_visits: Fr,
///     pub bad_rep: u8,
///     pub last_interacted_time: Time<Fr>,
/// }
///
/// fn predicate<'a, 'b>(user: &'a UserVar<Fr, Data>, _com: &'b FpVar<Fr>, _pub_args: (), _priv_args: ()) -> Result<Boolean<Fr>, SynthesisError> {
///     user.data.num_visits.is_eq(&FpVar::Constant(Fr::from(1)))
/// }
///
/// fn main () {
///
///     let mut rng = thread_rng();
///
///     let (pk, vk) = generate_keys_for_statement::<Fr, Poseidon<2>, Data, _, _, _, _, Groth>(&mut rng, predicate, None);
/// }
/// ```
pub fn generate_keys_for_statement<
    F: PrimeField + Absorb,
    H: FieldHash<F>,
    U: UserData<F> + Default,
    PubArgs: Clone + Default,
    PubArgsVar: AllocVar<PubArgs, F>,
    PrivArgs: Clone + Default,
    PrivArgsVar: AllocVar<PrivArgs, F>,
    Snark: SNARK<F>,
>(
    rng: &mut (impl CryptoRng + RngCore),
    pred: SingularPredicate<F, UserVar<F, U>, ComVar<F>, PubArgsVar, PrivArgsVar>,
    aux_data: PubArgs,
) -> (Snark::ProvingKey, Snark::VerifyingKey)
where
    Standard: Distribution<F>,
{
    let u = User::create(U::default(), rng);
    let out = ProvePredicateCircuit {
        priv_user: u.clone(),
        pub_com: u.commit::<H>(),
        pub_args: aux_data,
        priv_args: PrivArgs::default(),
        associated_method: pred,
    };
    Snark::circuit_specific_setup(out, rng).unwrap()
}

#[derive(Clone)]
/// The circuit used to generating proofs of some predicate. This is not necessary for use with the base system.
pub struct ProvePredicateCircuit<
    F: PrimeField + Absorb,
    U: UserData<F>,
    PubArgs: Clone,
    PubArgsVar: AllocVar<PubArgs, F>,
    PrivArgs: Clone,
    PrivArgsVar: AllocVar<PrivArgs, F>,
> {
    // Private
    /// The private user object.
    pub priv_user: User<F, U>,
    /// Private predicate arguments.
    pub priv_args: PrivArgs,

    // Public
    /// The commitment to the user object. Note that this is public.
    pub pub_com: Com<F>,
    /// The public arguments to the predicate.
    pub pub_args: PubArgs,

    /// The predicate.
    pub associated_method: SingularPredicate<F, UserVar<F, U>, ComVar<F>, PubArgsVar, PrivArgsVar>,
}

impl<
    F: PrimeField + Absorb,
    U: UserData<F>,
    PubArgs: Clone,
    PubArgsVar: AllocVar<PubArgs, F>,
    PrivArgs: Clone,
    PrivArgsVar: AllocVar<PrivArgs, F>,
> ConstraintSynthesizer<F>
    for ProvePredicateCircuit<F, U, PubArgs, PubArgsVar, PrivArgs, PrivArgsVar>
{
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ArkResult<()> {
        let user_var = UserVar::new_witness(ns!(cs, "user"), || Ok(self.priv_user))?;
        let priv_args_var = PrivArgsVar::new_witness(ns!(cs, "priv_args"), || Ok(&self.priv_args))?;

        let com_var = ComVar::new_input(ns!(cs, "com"), || Ok(&self.pub_com))?;
        let pub_args_var = PubArgsVar::new_input(ns!(cs, "pub_args"), || Ok(&self.pub_args))?;

        let b = (self.associated_method)(&user_var, &com_var, pub_args_var, priv_args_var)?;

        b.enforce_equal(&Boolean::TRUE)?;

        Ok(())
    }
}

/// Generate keys for proving a statement about a user object and membership of user.
///
/// This is associated to the [`User::prove_statement_and_in`] function.
///
/// If the public membership data is a constant, it must be encoded into the key, and so it
/// must be set in `memb_data`. Otherwise, the `memb_data` should be set to `None`.
///
/// For `aux_data`, if the auxiliary public arguments to the predicate are constant,
/// this should be done in the `AllocVar` implementation of the auxiliary data type.
///
///# Example
/// ```rust
/// # use zk_callbacks::zk_object;
/// # use zk_callbacks::generic::user::User;
/// # use rand::thread_rng;
/// # use ark_bn254::{Bn254 as E, Fr};
/// # use ark_r1cs_std::eq::EqGadget;
/// # use ark_r1cs_std::cmp::CmpGadget;
/// # use zk_callbacks::generic::interaction::Interaction;
/// # use zk_callbacks::generic::interaction::Callback;
/// # use zk_callbacks::generic::object::Id;
/// # use zk_callbacks::generic::object::Time;
/// # use zk_callbacks::generic::object::TimeVar;
/// # use ark_relations::r1cs::SynthesisError;
/// # use zk_callbacks::generic::user::UserVar;
/// # use ark_r1cs_std::fields::fp::FpVar;
/// # use ark_groth16::Groth16;
/// # use ark_r1cs_std::prelude::Boolean;
/// # use zk_callbacks::impls::hash::Poseidon;
/// # use ark_r1cs_std::prelude::UInt8;
/// # use zk_callbacks::impls::dummy::DummyStore;
/// # use ark_r1cs_std::select::CondSelectGadget;
/// # use zk_callbacks::generic::interaction::generate_keys_for_statement;
/// # use zk_callbacks::impls::centralized::crypto::{NoSigOTP};
/// # use zk_callbacks::impls::centralized::ds::sigstore::UOVObjStore;
/// # use crate::zk_callbacks::generic::bulletin::JoinableBulletin;
/// # use zk_callbacks::generic::interaction::generate_keys_for_statement_in;
/// # type Groth = Groth16<E>;
/// #[zk_object(Fr)]
/// #[derive(Default)]
/// struct Data {
///     pub num_visits: Fr,
///     pub bad_rep: u8,
///     pub last_interacted_time: Time<Fr>,
/// }
///
/// fn predicate<'a, 'b>(user: &'a UserVar<Fr, Data>, _com: &'b FpVar<Fr>, _pub_args: (), _priv_args: ()) -> Result<Boolean<Fr>, SynthesisError> {
///     user.data.num_visits.is_eq(&FpVar::Constant(Fr::from(1)))
/// }
///
/// fn main () {
///
///     let mut rng = thread_rng();
///
///     let mut obj_store = UOVObjStore::new(&mut rng);
///
///     let (pk, vk) = generate_keys_for_statement_in::<Fr, Poseidon<2>, Data, _, _, _, _, Groth, UOVObjStore<Fr>>(&mut rng, predicate, Some(obj_store.get_pubkey()), None);
/// }
/// ```
pub fn generate_keys_for_statement_in<
    F: PrimeField + Absorb,
    H: FieldHash<F>,
    U: UserData<F> + Default,
    PubArgs: Clone + Default,
    PubArgsVar: AllocVar<PubArgs, F>,
    PrivArgs: Clone + Default,
    PrivArgsVar: AllocVar<PrivArgs, F>,
    Snark: SNARK<F>,
    Bul: PublicUserBul<F, U>,
>(
    rng: &mut (impl CryptoRng + RngCore),
    pred: SingularPredicate<F, UserVar<F, U>, ComVar<F>, PubArgsVar, PrivArgsVar>,
    memb_data: Option<Bul::MembershipPub>,

    aux_data: PubArgs,
) -> (Snark::ProvingKey, Snark::VerifyingKey)
where
    Standard: Distribution<F>,
{
    let u = User::create(U::default(), rng);
    let out: ProvePredInCircuit<F, H, U, PubArgs, PubArgsVar, PrivArgs, PrivArgsVar, Bul> =
        ProvePredInCircuit {
            priv_user: u.clone(),
            priv_extra_membership_data: Bul::MembershipWitness::default(),
            pub_args: aux_data,
            priv_args: PrivArgs::default(),
            bul_memb_is_const: memb_data.is_some(),
            pub_extra_membership_data: memb_data.unwrap_or_default(),
            associated_method: pred,

            _phantom_hash: PhantomData,
        };
    Snark::circuit_specific_setup(out, rng).unwrap()
}

/// generate_keys_for_statement_in for merkle tree
pub fn generate_keys_for_statement_in_mt<
    F: PrimeField + Absorb,
    H: FieldHash<F>,
    U: UserData<F> + Default,
    PubArgs: Clone + Default,
    PubArgsVar: AllocVar<PubArgs, F>,
    PrivArgs: Clone + Default,
    PrivArgsVar: AllocVar<PrivArgs, F>,
    Snark: SNARK<F>,
    Bul: PublicUserBul<F, U>,
>(
    rng: &mut (impl CryptoRng + RngCore),
    pred: SingularPredicate<F, UserVar<F, U>, ComVar<F>, PubArgsVar, PrivArgsVar>,
    memb_data: Option<Bul::MembershipPub>,

    aux_data: PubArgs,
    wit_default: Bul::MembershipWitness,
) -> (Snark::ProvingKey, Snark::VerifyingKey)
where
    Standard: Distribution<F>,
{
    let u = User::create(U::default(), rng);
    let out: ProvePredInCircuit<F, H, U, PubArgs, PubArgsVar, PrivArgs, PrivArgsVar, Bul> =
        ProvePredInCircuit {
            priv_user: u.clone(),
            priv_extra_membership_data: wit_default,
            pub_args: aux_data,
            priv_args: PrivArgs::default(),
            bul_memb_is_const: memb_data.is_some(),
            pub_extra_membership_data: memb_data.unwrap_or_default(),
            associated_method: pred,

            _phantom_hash: PhantomData,
        };
    Snark::circuit_specific_setup(out, rng).unwrap()
}

/// The circuit used to generating proofs of some predicate and membership. This is not necessary for use with the base system.
pub struct ProvePredInCircuit<
    F: PrimeField + Absorb,
    H: FieldHash<F>,
    U: UserData<F>,
    PubArgs: Clone,
    PubArgsVar: AllocVar<PubArgs, F>,
    PrivArgs: Clone,
    PrivArgsVar: AllocVar<PrivArgs, F>,
    Bul: PublicUserBul<F, U>,
> {
    // Private
    /// The private user object.
    pub priv_user: User<F, U>,
    /// Membership witness for the user commitment.
    pub priv_extra_membership_data: Bul::MembershipWitness,
    /// Private arguments to the predicate.
    pub priv_args: PrivArgs,

    // Public
    /// Public arguments to the predicate.
    pub pub_args: PubArgs,
    /// Public membership data for the user commitment.
    pub pub_extra_membership_data: Bul::MembershipPub,
    /// If the public membership data constant.
    pub bul_memb_is_const: bool,
    /// The predicate.
    pub associated_method: SingularPredicate<F, UserVar<F, U>, ComVar<F>, PubArgsVar, PrivArgsVar>,

    /// The hash used for the commitment.
    pub _phantom_hash: PhantomData<H>,
}

impl<
    F: PrimeField + Absorb,
    H: FieldHash<F>,
    U: UserData<F>,
    PubArgs: Clone,
    PubArgsVar: AllocVar<PubArgs, F>,
    PrivArgs: Clone,
    PrivArgsVar: AllocVar<PrivArgs, F>,
    Bul: PublicUserBul<F, U>,
> Clone for ProvePredInCircuit<F, H, U, PubArgs, PubArgsVar, PrivArgs, PrivArgsVar, Bul>
{
    fn clone(&self) -> Self {
        Self {
            priv_user: self.priv_user.clone(),
            priv_extra_membership_data: self.priv_extra_membership_data.clone(),
            priv_args: self.priv_args.clone(),
            pub_args: self.pub_args.clone(),
            pub_extra_membership_data: self.pub_extra_membership_data.clone(),
            bul_memb_is_const: self.bul_memb_is_const,
            associated_method: self.associated_method,
            _phantom_hash: self._phantom_hash,
        }
    }
}

impl<
    F: PrimeField + Absorb,
    H: FieldHash<F>,
    U: UserData<F>,
    PubArgs: Clone,
    PubArgsVar: AllocVar<PubArgs, F>,
    PrivArgs: Clone,
    PrivArgsVar: AllocVar<PrivArgs, F>,
    Bul: PublicUserBul<F, U>,
> ConstraintSynthesizer<F>
    for ProvePredInCircuit<F, H, U, PubArgs, PubArgsVar, PrivArgs, PrivArgsVar, Bul>
{
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> ArkResult<()> {
        let user_var = UserVar::new_witness(ns!(cs, "user"), || Ok(self.priv_user))?;
        let extra_data_for_membership =
            Bul::MembershipWitnessVar::new_witness(ns!(cs, "extra_data"), || {
                Ok(self.priv_extra_membership_data)
            })?;

        let priv_args_var = PrivArgsVar::new_witness(ns!(cs, "priv_args"), || Ok(&self.priv_args))?;

        let pub_args_var = PubArgsVar::new_input(ns!(cs, "pub_args"), || Ok(&self.pub_args))?;

        let pub_data_for_membership = match self.bul_memb_is_const {
            true => {
                Bul::MembershipPubVar::new_constant(cs.clone(), &self.pub_extra_membership_data)?
            }
            false => Bul::MembershipPubVar::new_input(ns!(cs, "pub_bul_data"), || {
                Ok(&self.pub_extra_membership_data)
            })?,
        };

        let com = User::commit_in_zk::<H>(user_var.clone())?;

        let b = (self.associated_method)(&user_var, &com, pub_args_var, priv_args_var)?;

        b.enforce_equal(&Boolean::TRUE)?;

        Bul::enforce_membership_of(
            User::commit_in_zk::<H>(user_var)?,
            extra_data_for_membership,
            pub_data_for_membership,
        )?
        .enforce_equal(&Boolean::TRUE)?;

        Ok(())
    }
}

/// Generate proving and verification keys for a scan interaction.
///
/// If the public membership data for a user is constant, then it must be encoded into the key.
/// Therefore, one must set `memb_data` if the public data is constant.
///
/// Similarly, if the auxiliary public arguments for the scan are constant, then they must be
/// encoded, and so it is set in `aux_data`. Otherwise, it should be set to `None`.
///
/// # Example
/// ```rust
/// # use zk_callbacks::generic::interaction::generate_keys_for_scan;
/// # use zk_callbacks::zk_object;
/// # use zk_callbacks::generic::user::User;
/// # use rand::thread_rng;
/// # use ark_bn254::{Bn254 as E, Fr};
/// # use ark_r1cs_std::eq::EqGadget;
/// # use ark_r1cs_std::cmp::CmpGadget;
/// # use zk_callbacks::generic::interaction::Interaction;
/// # use zk_callbacks::generic::interaction::Callback;
/// # use zk_callbacks::generic::object::Id;
/// # use zk_callbacks::generic::object::Time;
/// # use zk_callbacks::generic::object::TimeVar;
/// # use ark_relations::r1cs::SynthesisError;
/// # use zk_callbacks::generic::user::UserVar;
/// # use ark_r1cs_std::fields::fp::FpVar;
/// # use ark_groth16::Groth16;
/// # use ark_r1cs_std::prelude::Boolean;
/// # use zk_callbacks::generic::bulletin::UserBul;
/// # use zk_callbacks::impls::hash::Poseidon;
/// # use ark_r1cs_std::prelude::UInt8;
/// # use zk_callbacks::impls::dummy::DummyStore;
/// # use zk_callbacks::generic::scan::get_scan_interaction;
/// # use zk_callbacks::generic::scan::PubScanArgs;
/// # use ark_r1cs_std::select::CondSelectGadget;
/// # use zk_callbacks::impls::centralized::crypto::{FakeSigPrivkey, FakeSigPubkey, NoSigOTP};
/// # use zk_callbacks::scannable_zk_object;
/// # type Groth = Groth16<E>;
/// # type PubScan = PubScanArgs<Fr, Data, Fr, FpVar<Fr>, NoSigOTP<Fr>, DummyStore, 1>;
/// #[scannable_zk_object(Fr)]
/// #[derive(Default)]
/// struct Data {
///     pub num_visits: Fr,
///     pub bad_rep: u8,
///     pub last_interacted_time: Time<Fr>,
/// }
///
/// fn method<'a>(old_user: &'a User<Fr, Data>, pub_time: Time<Fr>, _priv: ()) -> User<Fr, Data> {
///     let mut new = old_user.clone();
///     new.data.num_visits += Fr::from(1);
///     new.data.last_interacted_time = pub_time;
///     new
/// }
///
/// fn predicate<'a>(old_user: &'a UserVar<Fr, Data>, new_user: &'a UserVar<Fr, Data>, pub_time: TimeVar<Fr>, _priv: ()) -> Result<Boolean<Fr>, SynthesisError> {
///     let o1 = old_user.data.bad_rep.is_eq(&new_user.data.bad_rep)?;
///     let o2 = old_user.data.bad_rep.is_le(&UInt8::constant(40))?;
///     let o3 = new_user.data.num_visits.is_eq(&(old_user.data.num_visits.clone() + FpVar::Constant(Fr::from(1))))?;
///     let o4 = new_user.data.last_interacted_time.is_eq(&pub_time)?;
///     Ok(o1 & o2 & o3 & o4)
/// }
///
/// fn callback<'a>(old_user: &'a User<Fr, Data>, args: Fr) -> User<Fr, Data> {
///     let mut u2 = old_user.clone();
///     if args == Fr::from(0) {
///         u2.data.bad_rep;
///     } else {
///         u2.data.bad_rep += 10;
///     }
///     u2.clone()
/// }
///
/// fn enforce_callback<'a>(old_user: &'a UserVar<Fr, Data>, args: FpVar<Fr>) -> Result<UserVar<Fr, Data>, SynthesisError> {
///     let mut u = old_user.clone();
///     u.data.bad_rep =
///     UInt8::conditionally_select(
///         &args.is_eq(&FpVar::Constant(Fr::from(0)))?,
///         &u.data.bad_rep,
///         &u.data.bad_rep.wrapping_add(&UInt8::constant(10))
///     )?;
///     Ok(u)
/// }
///
///
/// fn main () {
///     let cb = Callback {
///         method_id: Id::from(0),
///         expirable: false,
///         expiration: Time::from(10),
///         method: callback,
///         predicate: enforce_callback
///     };
///
///     let cb_methods = vec![cb.clone()];
///
///     let int = Interaction {
///         meth: (method, predicate),
///         callbacks: [cb.clone()],
///     };
///
///     let ex: PubScan = PubScanArgs {
///         memb_pub: [(); 1],
///         is_memb_data_const: true,
///         nmemb_pub: [(); 1],
///         is_nmemb_data_const: true,
///         cur_time: Fr::from(0),
///         bulletin: DummyStore,
///         cb_methods: cb_methods.clone(),
///     };
///
///     let mut rng = thread_rng();
///
///     let (pk, vk) = int.generate_keys::<Poseidon<2>, Groth, NoSigOTP<Fr>, DummyStore>(&mut rng, Some(()), None, false);
///
///     let (pks, vks) = generate_keys_for_scan::<_, _, _, _, NoSigOTP<Fr>, DummyStore, DummyStore, Poseidon<2>, Groth, 1>(&mut rng, Some(()), Some(ex));
/// }
/// ```
pub fn generate_keys_for_scan<
    F: PrimeField + Absorb,
    U: UserData<F> + Default,
    CBArgs: Clone + Default + std::fmt::Debug,
    CBArgsVar: AllocVar<CBArgs, F> + Clone,
    Crypto: AECipherSigZK<F, CBArgs, AV = CBArgsVar> + Default,
    Bul: PublicUserBul<F, U>,
    CBul: PublicCallbackBul<F, CBArgs, Crypto> + Clone + Default,
    H: FieldHash<F>,
    Snark: SNARK<F>,
    const NUMSCANS: usize,
>(
    rng: &mut (impl CryptoRng + RngCore),
    memb_data: Option<Bul::MembershipPub>,
    aux_data: PubScanArgs<F, U, CBArgs, CBArgsVar, Crypto, CBul, NUMSCANS>,
) -> (Snark::ProvingKey, Snark::VerifyingKey)
where
    U::UserDataVar: CondSelectGadget<F> + EqGadget<F>,
    CBul::MembershipPub: Default,
    CBul::NonMembershipPub: Default,
    CBul::MembershipWitness: Default,
    CBul::NonMembershipWitness: Default,
    Standard: Distribution<F>,
{
    get_scan_interaction::<_, _, _, _, _, _, H, NUMSCANS>()
        .generate_keys::<H, Snark, Crypto, Bul>(rng, memb_data, aux_data, true)
}
