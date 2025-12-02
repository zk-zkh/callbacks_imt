use crate::{
    crypto::hash::{FieldHash, HasherZK},
    util::gen_poseidon_params,
};
use ark_crypto_primitives::{
    crh::{CRHScheme, CRHSchemeGadget, poseidon, poseidon::CRH},
    sponge::Absorb,
};
use ark_ff::PrimeField;
use ark_r1cs_std::fields::fp::FpVar;
use ark_relations::r1cs::SynthesisError;

#[cfg(feature = "circposeidon")]
#[cfg(any(feature = "circposeidon", doc))]
#[doc(cfg(feature = "circposeidon"))]
use circom_poseidon::get_poseidon_params;

/// The poseidon hash.
///
/// See the implementation of [`HasherZK`] and [`FieldHash`] for Poseidon.
#[derive(Clone, Default, Debug)]
pub struct Poseidon<const R: usize>();

impl<F: PrimeField + Absorb, const R: usize> HasherZK<F> for Poseidon<R> {
    type M = F;
    type C = F;
    type MV = FpVar<F>;
    type CV = FpVar<F>;

    fn hash(data: &[F]) -> F {
        CRH::evaluate(&gen_poseidon_params(R, false), data).unwrap()
    }

    fn hash_in_zk(data: &[FpVar<F>]) -> Result<FpVar<F>, SynthesisError> {
        let params = gen_poseidon_params(R, false);
        let params_var = poseidon::constraints::CRHParametersVar { parameters: params };

        poseidon::constraints::CRHGadget::evaluate(&params_var, data)
    }
}

impl<F: PrimeField + Absorb, const R: usize> FieldHash<F> for Poseidon<R> {}

/// A constant hash.
///
/// Hashes to a constant value. This is not a proper hash, this is only meant for testing.
#[derive(Clone, Default, Debug)]
pub struct ConstHash;

impl<F: PrimeField + Absorb> HasherZK<F> for ConstHash {
    type M = F;

    type C = F;

    type MV = FpVar<F>;

    type CV = FpVar<F>;

    fn hash(_data: &[Self::M]) -> Self::C {
        F::ZERO
    }

    fn hash_in_zk(_data: &[Self::MV]) -> Result<Self::CV, SynthesisError> {
        Ok(FpVar::Constant(F::ZERO))
    }
}

impl<F: PrimeField + Absorb> FieldHash<F> for ConstHash {}

/// A poseidon hash which works with Circom.
///
/// Note that this hash still doesn't natively work with Circom; a specialized `ArkPoseidon` must
/// be used in Circom as well.
#[cfg(feature = "circposeidon")]
#[cfg(any(feature = "circposeidon", doc))]
#[doc(cfg(feature = "circposeidon"))]
#[derive(Clone)]
pub struct CircPoseidon<const R: usize>();

#[cfg(feature = "circposeidon")]
#[cfg(any(feature = "circposeidon", doc))]
#[doc(cfg(feature = "circposeidon"))]
impl<F: PrimeField + Absorb, const R: usize> HasherZK<F> for CircPoseidon<R> {
    type M = F;
    type C = F;
    type MV = FpVar<F>;
    type CV = FpVar<F>;

    fn hash(data: &[F]) -> F {
        CRH::evaluate(&get_poseidon_params(R), data).unwrap()
    }

    fn hash_in_zk(data: &[FpVar<F>]) -> Result<FpVar<F>, SynthesisError> {
        let params = get_poseidon_params(R);
        let params_var = poseidon::constraints::CRHParametersVar { parameters: params };

        poseidon::constraints::CRHGadget::evaluate(&params_var, data)
    }
}

#[cfg(feature = "circposeidon")]
#[cfg(any(feature = "circposeidon", doc))]
#[doc(cfg(feature = "circposeidon"))]
impl<F: PrimeField + Absorb, const R: usize> FieldHash<F> for CircPoseidon<R> {}
