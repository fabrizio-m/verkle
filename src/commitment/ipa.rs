use super::CommitmentScheme;
use ark_ec::SWModelParameters;
pub use ipapc::{Commitment, Init, IpaScheme, Opening};

impl<P: SWModelParameters> CommitmentScheme<P> for IpaScheme<P>
where
    P: Eq + PartialEq + Clone,
{
    type Init = Init<P>;

    type Commitment = Commitment<P, false>;

    type Opening = Opening<P>;

    fn init(init: Self::Init, degree_bound: u8) -> Self {
        IpaScheme::init(init, degree_bound)
    }

    fn commit(&mut self, coefficients: impl Into<Vec<crate::Fr<P>>>) -> Self::Commitment {
        IpaScheme::commit(&self, coefficients.into())
    }

    fn open(
        &mut self,
        commitment: Self::Commitment,
        coeffs: &[crate::Fr<P>],
        point: crate::Fr<P>,
        eval: crate::Fr<P>,
    ) -> Self::Opening {
        IpaScheme::open(&self, commitment, coeffs, point, eval)
    }

    fn verify(
        &mut self,
        commitment: Self::Commitment,
        _point: crate::Fr<P>,
        _eval: crate::Fr<P>,
        opening: Self::Opening,
    ) -> bool {
        let verify = IpaScheme::verify(&self, commitment, opening);
        verify.is_some()
    }
}
