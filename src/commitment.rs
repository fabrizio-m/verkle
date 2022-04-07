use crate::Fr;
use ark_ec::{short_weierstrass_jacobian::GroupAffine, SWModelParameters};
use ark_ff::{batch_inversion, FftField, Field, Zero};
use ark_poly::{
    univariate::DensePolynomial, EvaluationDomain, Evaluations, GeneralEvaluationDomain,
    Radix2EvaluationDomain, UVPolynomial,
};
use itertools::{izip, Itertools};
use std::{
    fmt::Debug,
    ops::{Add, Mul, Neg, Sub},
};

pub mod ipa;

pub trait CommitmentScheme<P: SWModelParameters>
where
    Fr<P>: Zero + Field,
    GroupAffine<P>: Debug,
    Self::Commitment: Add<Output = Self::Commitment>
        + Sub<Output = Self::Commitment>
        + Mul<Fr<P>, Output = Self::Commitment>
        + Neg
        + Into<Vec<u8>>
        + Clone
        + Debug
        + Eq,
{
    type Init;
    type Commitment;
    type Opening;

    fn init(init: Self::Init, degree_bound: u8) -> Self;
    fn commit(&self, coefficients: impl Into<Vec<Fr<P>>>) -> Self::Commitment;
    fn open(
        &self,
        commitment: Self::Commitment,
        coeffs: &[Fr<P>],
        point: Fr<P>,
        eval: Fr<P>,
    ) -> Self::Opening;
    fn verify(
        &self,
        commitment: Self::Commitment,
        point: Fr<P>,
        eval: Fr<P>,
        opening: Self::Opening,
    ) -> bool;
    ///returns the commitment to the polynomial that evaluates to one for the ith element of the
    ///domain and zero for any other element
    fn lagrange_basis_commitments(
        &self,
        domain: &impl EvaluationDomain<Fr<P>>,
    ) -> Vec<Self::Commitment>
    where
        Self: Sized,
    {
        match self.reference_string() {
            Some(string) => ifft_lagrange_commitment::<P, Self>(string),
            None => {
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
        }
    }
    fn update_commitment(
        &self,
        commitment: Self::Commitment,
        lagrange_commitment: Self::Commitment,
        previous: Option<Fr<P>>,
        new: Fr<P>,
    ) -> Self::Commitment {
        let previous = previous.unwrap_or(Fr::<P>::zero());
        commitment + (lagrange_commitment * (new - previous))
    }

    fn commit_to_evals(
        &self,
        evals: Vec<Fr<P>>,
        domain: GeneralEvaluationDomain<Fr<P>>,
    ) -> Self::Commitment {
        let evals = Evaluations::from_vec_and_domain(evals, domain);
        let coeffs = evals.interpolate();

        self.commit(coeffs.coeffs)
    }
    ///should return the commitments to the n monomials with coefficient 1, usually the reference string
    fn reference_string(&self) -> Option<Vec<Self::Commitment>> {
        None
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
    let size = domain.size_as_field_element();
    let mut weights = domain.elements().collect_vec();
    batch_inversion(&mut weights);
    let mut weights = weights
        .into_iter()
        .map(|weight| weight * size)
        .collect_vec();
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

///compute all lagrange commitments in n log(n)
fn ifft_lagrange_commitment<P, C>(unit_monomials: Vec<C::Commitment>) -> Vec<C::Commitment>
where
    P: SWModelParameters,
    C: CommitmentScheme<P>,
{
    let inverted_size = Radix2EvaluationDomain::<Fr<P>>::new(unit_monomials.len())
        .unwrap()
        .size_as_field_element()
        .inverse()
        .unwrap();
    let mut res = fft::<P, C>(unit_monomials).into_iter();
    let first = res.by_ref().next().unwrap();
    [first]
        .into_iter()
        .chain(res.rev())
        .map(|e| e * inverted_size)
        .collect_vec()
}

fn fft<P, C>(coeffs: Vec<C::Commitment>) -> Vec<C::Commitment>
where
    P: SWModelParameters,
    C: CommitmentScheme<P>,
{
    let len = coeffs.len();
    assert!(len.is_power_of_two());
    if coeffs.len() == 1 {
        return coeffs;
    }
    let (even, odd): (Vec<C::Commitment>, Vec<C::Commitment>) = coeffs
        .iter()
        .cloned()
        .enumerate()
        .partition_map(|(i, item)| match i % 2 == 0 {
            true => itertools::Either::Left(item),
            false => itertools::Either::Right(item),
        });
    let [even, odd] = [even, odd].map(|coeffs| fft::<P, C>(coeffs));
    let mut result = coeffs;
    let (left, right) = result.split_at_mut(len / 2);
    let domain = {
        let domain = Radix2EvaluationDomain::<Fr<P>>::new(len).unwrap();
        domain.elements()
    };
    for (even, odd, left, right, domain) in izip!(even, odd, left, right, domain) {
        let rhs = odd * domain;
        *left = even.clone() + rhs.clone();
        *right = even - rhs;
    }
    result
}
