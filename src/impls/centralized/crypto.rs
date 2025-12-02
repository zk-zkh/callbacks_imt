use crate::crypto::{
    enc::{AECipherSigZK, CPACipher},
    rr::{RRSigner, RRVerifier},
};
use ark_ff::PrimeField;
use ark_r1cs_std::{
    fields::fp::FpVar,
    prelude::{AllocVar, AllocationMode},
};
use ark_relations::{
    ns,
    r1cs::{Namespace, SynthesisError},
};
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Valid};
use core::borrow::Borrow;
use rand::{
    CryptoRng, Rng, RngCore,
    distributions::{Distribution, Standard},
};
use std::marker::PhantomData;

use ark_r1cs_std::convert::ToConstraintFieldGadget;
use ark_relations::r1cs::ToConstraintField;

#[derive(
    Clone, Debug, PartialEq, Eq, Default, CanonicalSerialize, CanonicalDeserialize, PartialOrd, Ord,
)]
/// The object associated to a single plain ticket.
///
/// When in the centralized setting (a single service controls the bulletins), tickets don't need
/// to be signature public keys. In this setting, signatures are not necessary (as the bulletin is
/// owned by the service anyways!)
///
/// Therefore, this constitutes a **plain random ticket** which isn't treated as a signature public
/// key.
///
/// **Take a look at the documentation on the type aliases**, as those are more useful.
pub struct PlainTikCrypto<F: CanonicalSerialize + CanonicalDeserialize>(pub(crate) F);

impl<F: CanonicalSerialize + CanonicalDeserialize + Clone> PlainTikCrypto<F> {
    /// Construct a new plain ticket from a field element.
    pub fn new(f: F) -> Self {
        Self(f)
    }

    /// Convert a plain ticket into a field element.
    pub fn to(&self) -> F {
        self.0.clone()
    }
}

impl<F: PrimeField> ToConstraintField<F> for PlainTikCrypto<F> {
    fn to_field_elements(&self) -> Option<Vec<F>> {
        self.0.to_field_elements()
    }
}

/// A plain ticket in-circuit.
#[derive(Clone)]
pub struct PlainTikCryptoVar<F: PrimeField>(pub FpVar<F>);

impl<F: PrimeField> ToConstraintFieldGadget<F> for PlainTikCryptoVar<F> {
    fn to_constraint_field(&self) -> Result<Vec<FpVar<F>>, SynthesisError> {
        self.0.to_constraint_field()
    }
}

impl<F: PrimeField> AllocVar<PlainTikCrypto<F>, F> for PlainTikCryptoVar<F> {
    fn new_variable<T: Borrow<PlainTikCrypto<F>>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let ns = cs.into();
        let cs = ns.cs();
        let res = f();
        res.and_then(|rec| {
            let rec = rec.borrow();
            let tik = FpVar::new_variable(ns!(cs, "tik"), || Ok(rec.0), mode)?;
            Ok(PlainTikCryptoVar(tik))
        })
    }
}

impl<F: PrimeField, A> RRVerifier<(), A, F> for PlainTikCrypto<F>
where
    Standard: Distribution<F>,
{
    fn verify(&self, _mes: A, _sig: ()) -> bool {
        true
    }

    fn rerand(&self, rng: &mut (impl CryptoRng + RngCore)) -> (F, Self) {
        let mut out: F = rng.r#gen();
        while out > F::from_bigint(F::MODULUS_MINUS_ONE_DIV_TWO).unwrap() {
            out -= F::from_bigint(F::MODULUS_MINUS_ONE_DIV_TWO).unwrap();
        }
        (out, PlainTikCrypto(out))
    }
}

impl<F: PrimeField> CPACipher<F> for PlainTikCrypto<F>
where
    Standard: Distribution<F>,
{
    type M = F;
    type C = F;
    type MV = FpVar<F>;
    type CV = FpVar<F>;

    type KeyVar = PlainTikCryptoVar<F>;

    fn keygen(rng: &mut (impl CryptoRng + RngCore)) -> Self {
        let mut f: F = rng.r#gen();
        while f > F::from_bigint(F::MODULUS_MINUS_ONE_DIV_TWO).unwrap() {
            f -= F::from_bigint(F::MODULUS_MINUS_ONE_DIV_TWO).unwrap();
        }
        Self(f)
    }

    fn encrypt(&self, message: Self::M) -> Self::C {
        message + self.0
    }

    fn decrypt(&self, ciphertext: Self::C) -> Self::M {
        ciphertext - self.0
    }

    fn decrypt_in_zk(key: Self::KeyVar, ciphertext: Self::CV) -> Result<Self::MV, SynthesisError> {
        Ok(ciphertext - key.0)
    }
}

impl<F: PrimeField, A> RRSigner<(), A, F, PlainTikCrypto<F>> for PlainTikCrypto<F>
where
    Standard: Distribution<F>,
{
    fn new(_rng: &mut (impl CryptoRng + RngCore)) -> Self {
        PlainTikCrypto(F::zero())
    }

    fn sk_to_pk(&self) -> PlainTikCrypto<F> {
        self.clone()
    }

    fn sign_message(&self, _mes: &A) {}

    fn rerand(&self, rand: F) -> Self {
        PlainTikCrypto(rand)
    }
}

/// A fake signature public key.
///
/// This should be used when public keys are necessary. As signatures are not necessary in the
/// centralized setting, any public key can be used in an interaction when generating tickets.
///
/// Therefore, one should just use [`FakeSigPubkey::pk()`].
pub type FakeSigPubkey<F> = PlainTikCrypto<F>;

impl<F: PrimeField> FakeSigPubkey<F> {
    /// This is for use with [`FakeSigPubkey`]. This function just constructs a fake public verification key for rerandomization.
    pub fn pk() -> Self {
        FakeSigPubkey::new(F::from(0))
    }
}

/// The fake signature public key in-circuit.
pub type FakeSigPubkeyVar<F> = PlainTikCryptoVar<F>;

/// A fake signature private key.
///
/// This should be used when private keys are used. As signatures are not necessary in the
/// centralized setting, any private key can be used to verify tickets.
///
/// Therefore, one should just use [`FakeSigPrivkey::sk()`].
pub type FakeSigPrivkey<F> = PlainTikCrypto<F>;

impl<F: PrimeField> FakeSigPrivkey<F> {
    /// This is for use with [`FakeSigPrivkey`]. This function just constructs a fake signing key
    /// to verify interactions.
    pub fn sk() -> Self {
        FakeSigPrivkey::new(F::from(0))
    }
}

/// An OTP encryption key.
pub type OTPEncKey<F> = PlainTikCrypto<F>;

/// The OTP encryption key in-circuit.
pub type OTPEncKeyVar<F> = PlainTikCryptoVar<F>;

/// The type which implements AECipherSigZK. This uses an OTP for encryption of arguments, and
/// doesn't have any signatures.
///
/// This is what should be used whenever callback ticket
/// posting is necessary in the centralized setting. This should be used as an indicator type.
pub type NoSigOTP<F> = PlainTikCrypto<F>;

impl<F: PrimeField> AECipherSigZK<F, F> for NoSigOTP<F>
where
    Standard: Distribution<F>,
{
    type Sig = ();
    type SigPK = FakeSigPubkey<F>;
    type SigPKV = FakeSigPubkeyVar<F>;

    type SigSK = FakeSigPrivkey<F>;

    type AV = FpVar<F>;

    type Ct = F;

    type EncKey = OTPEncKey<F>;

    type EncKeyVar = OTPEncKeyVar<F>;

    type Rand = F;
}

/// A cipher which does no encryption. This is for centralized settings when encryption is not
/// necessary on arguments, if arguments can be public.
///
/// Note that this does lose some security even for a centralized system, as people can see
/// arguments passed to callbacks. However, in scenarios where argument hiding is not a concern,
/// this will behave as a cipher.
///
/// This still uses [`PlainTikCrypto`] for tickets, as tickets must still be plain random values.
#[derive(Clone)]
pub struct NoEnc<F, T, TVar>
where
    F: PrimeField,
    TVar: AllocVar<T, F>,
{
    _f: PhantomData<fn() -> F>,
    _msg: PhantomData<fn() -> T>,
    _var: PhantomData<fn() -> TVar>,
}

impl<F: PrimeField, T, TVar: AllocVar<T, F>> NoEnc<F, T, TVar> {
    /// Fetches a fake encryption or decryption key for the nonexistent cipher.
    pub fn key() -> Self {
        Self {
            _f: PhantomData,
            _msg: PhantomData,
            _var: PhantomData,
        }
    }
}

impl<F: PrimeField, T, TVar: AllocVar<T, F>> std::fmt::Debug for NoEnc<F, T, TVar> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "NoEnc")
    }
}

impl<F: PrimeField, T, TVar: AllocVar<T, F>> Default for NoEnc<F, T, TVar> {
    fn default() -> Self {
        Self {
            _f: PhantomData,
            _msg: PhantomData,
            _var: PhantomData,
        }
    }
}

impl<F: PrimeField, T, TVar: AllocVar<T, F>> PartialEq for NoEnc<F, T, TVar> {
    fn eq(&self, _other: &Self) -> bool {
        true
    }
}

impl<F: PrimeField, T, TVar: AllocVar<T, F>> Eq for NoEnc<F, T, TVar> {}

impl<F: PrimeField, T, TVar: AllocVar<T, F>> CanonicalSerialize for NoEnc<F, T, TVar> {
    fn serialize_with_mode<W: std::io::Write>(
        &self,
        _writer: W,
        _compress: ark_serialize::Compress,
    ) -> Result<(), ark_serialize::SerializationError> {
        Ok(())
    }

    fn serialized_size(&self, _compress: ark_serialize::Compress) -> usize {
        0
    }
}

impl<F: PrimeField, T, TVar: AllocVar<T, F>> Valid for NoEnc<F, T, TVar> {
    fn check(&self) -> Result<(), ark_serialize::SerializationError> {
        Ok(())
    }
}

impl<F: PrimeField, T, TVar: AllocVar<T, F>> CanonicalDeserialize for NoEnc<F, T, TVar> {
    fn deserialize_with_mode<R: std::io::Read>(
        _reader: R,
        _compress: ark_serialize::Compress,
        _validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        Ok(Self {
            _f: PhantomData,
            _msg: PhantomData,
            _var: PhantomData,
        })
    }
}

impl<F: PrimeField, T: Clone, TVar: AllocVar<T, F>> ToConstraintField<F> for NoEnc<F, T, TVar> {
    fn to_field_elements(&self) -> Option<Vec<F>> {
        Some(vec![])
    }
}

impl<F: PrimeField, T: Clone, TVar: AllocVar<T, F>> ToConstraintFieldGadget<F>
    for NoEnc<F, T, TVar>
{
    fn to_constraint_field(&self) -> Result<Vec<FpVar<F>>, SynthesisError> {
        Ok(vec![])
    }
}

impl<F: PrimeField, T, TVar: AllocVar<T, F>> AllocVar<NoEnc<F, T, TVar>, F> for NoEnc<F, T, TVar> {
    fn new_variable<Q: Borrow<NoEnc<F, T, TVar>>>(
        _cs: impl Into<Namespace<F>>,
        _f: impl FnOnce() -> Result<Q, SynthesisError>,
        _mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        Ok(Self {
            _f: PhantomData,
            _msg: PhantomData,
            _var: PhantomData,
        })
    }
}

impl<F: PrimeField, T: Clone, TVar: AllocVar<T, F> + Clone> CPACipher<F> for NoEnc<F, T, TVar> {
    type M = T;
    type C = T;
    type MV = TVar;
    type CV = TVar;

    type KeyVar = NoEnc<F, T, TVar>;

    fn keygen(_rng: &mut (impl CryptoRng + RngCore)) -> Self {
        Self {
            _f: PhantomData,
            _msg: PhantomData,
            _var: PhantomData,
        }
    }

    fn encrypt(&self, message: Self::M) -> Self::C {
        message
    }

    fn decrypt(&self, ciphertext: Self::C) -> Self::M {
        ciphertext
    }

    fn decrypt_in_zk(_key: Self::KeyVar, ciphertext: Self::CV) -> Result<Self::MV, SynthesisError> {
        Ok(ciphertext)
    }
}

impl<F: PrimeField, A: Clone + Default, AVar: AllocVar<A, F> + Clone> AECipherSigZK<F, A>
    for NoEnc<F, A, AVar>
where
    Standard: Distribution<F>,
{
    type Sig = ();
    type SigPK = FakeSigPubkey<F>;
    type SigPKV = FakeSigPubkeyVar<F>;

    type SigSK = FakeSigPrivkey<F>;

    type AV = AVar;

    type Ct = A;

    type EncKey = NoEnc<F, A, AVar>;

    type EncKeyVar = NoEnc<F, A, AVar>;

    type Rand = F;
}
