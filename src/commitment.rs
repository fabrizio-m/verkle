use crate::Fr;
use ark_ec::{short_weierstrass_jacobian::GroupAffine, SWModelParameters};
use ark_ff::{batch_inversion, FftField, Zero};
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain,
    UVPolynomial,
};
use std::{
    fmt::Debug,
    ops::{Add, Mul},
};

pub mod ipa;

pub trait CommitmentScheme<P: SWModelParameters>
where
    Fr<P>: Zero,
    GroupAffine<P>: Debug,
    Self::Commitment: Add<Output = Self::Commitment>
        + Mul<Fr<P>, Output = Self::Commitment>
        + Into<Vec<u8>>
        + Clone
        + Debug
        + Eq,
{
    type Init;
    type Commitment;
    type Opening;

    fn init(init: Self::Init, degree_bound: u8) -> Self;
    fn commit(&mut self, coefficients: impl Into<Vec<Fr<P>>>) -> Self::Commitment;
    fn open(
        &mut self,
        commitment: Self::Commitment,
        coeffs: &[Fr<P>],
        point: Fr<P>,
        eval: Fr<P>,
    ) -> Self::Opening;
    fn verify(
        &mut self,
        commitment: Self::Commitment,
        point: Fr<P>,
        eval: Fr<P>,
        opening: Self::Opening,
    ) -> bool;
    ///returns the commitment to the polynomial that evaluates to one for the ith element of the
    ///domain and zero for any other element
    fn lagrange_basis_commitments(
        &mut self,
        domain: &impl EvaluationDomain<Fr<P>>,
    ) -> Vec<Self::Commitment> {
        //let domain =
        //GeneralEvaluationDomain::<Fr<P>>::new(2_usize.pow(Self::LENGTH as u32)).unwrap();
        let weights = barycentric_weights(domain);
        domain
            .elements()
            .into_iter()
            .zip(weights.into_iter())
            .map(|(root, weight)| {
                let poly = lagrange_poly(domain, root, weight);
                let commitment = self.commit(poly.coeffs);
                commitment
            })
            .collect()
    }
    fn update_commitment(
        &mut self,
        commitment: Self::Commitment,
        lagrange_commitment: Self::Commitment,
        previous: Option<Fr<P>>,
        new: Fr<P>,
    ) -> Self::Commitment {
        let previous = previous.unwrap_or(Fr::<P>::zero());
        commitment + (lagrange_commitment * (new - previous))
    }

    fn commit_to_evals(
        &mut self,
        evals: Vec<Fr<P>>,
        domain: GeneralEvaluationDomain<Fr<P>>,
    ) -> Self::Commitment {
        let evals = Evaluations::from_vec_and_domain(evals, domain);
        let coeffs = evals.interpolate();

        self.commit(coeffs.coeffs)
    }
}

#[test]
fn lagrange() {
    use ark_ff::One;
    type F = ark_pallas::Fr;
    let domain = GeneralEvaluationDomain::<F>::new(8).unwrap();
    //let vanishing_poly = domain.vanishing_polynomial();

    let weights = barycentric_weights(&domain);
    let polys = domain
        .elements()
        .zip(weights.into_iter())
        .map(|(root, weight)| lagrange_poly(&domain, root, weight))
        .collect::<Vec<_>>();
    //let l3 = (&polys[3]).clone();
    for (i, poly) in polys.into_iter().enumerate() {
        let evals = poly.evaluate_over_domain(domain);
        for (j, eval) in evals.evals.iter().enumerate() {
            if i == j {
                assert!(eval.is_one());
            } else {
                assert!(eval.is_zero());
            }
        }
    }
}
pub(crate) fn barycentric_weights<F: FftField>(domain: &impl EvaluationDomain<F>) -> Vec<F> {
    let roots = domain.elements().collect::<Vec<_>>();
    let weight = |j, elem| {
        roots
            .iter()
            .enumerate()
            .map(
                |(index, root)| {
                    if index == j {
                        F::one()
                    } else {
                        elem - root
                    }
                },
            )
            .reduce(Mul::mul)
            .unwrap()
    };
    let mut weights = domain
        .elements()
        .enumerate()
        .map(|(index, elem)| weight(index, elem))
        .collect::<Vec<_>>();
    batch_inversion(&mut weights);

    weights
}
pub(crate) fn lagrange_poly<F: FftField>(
    domain: &impl EvaluationDomain<F>,
    root: F,
    inverted_weight: F,
) -> DensePolynomial<F> {
    let vanishing_poly = domain.vanishing_polynomial();
    let lhs = &DensePolynomial::<F>::from_coefficients_slice(&[-F::one()]) + &vanishing_poly;
    let rhs = DensePolynomial::from_coefficients_slice(&[-root, F::one()]);
    (&lhs / &rhs).mul(inverted_weight)
}
