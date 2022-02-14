use crate::{commitment::CommitmentScheme, hash_to_field, Fr};
use ark_ff::Zero;
use ark_pallas::PallasParameters;
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, Polynomial, UVPolynomial};
use std::{
    fmt::Debug,
    ops::{Add, Mul},
};

pub struct MockScheme {}

#[derive(Clone, PartialEq, Eq)]
pub struct MockCommitment {
    pub coefficients: Vec<Fr<PallasParameters>>,
    hash: Fr<PallasParameters>,
}

impl MockCommitment {
    pub fn print_evals(&self, domain: &impl EvaluationDomain<Fr<PallasParameters>>) {
        let coefficients = &self.coefficients;
        if coefficients.len() == 1 || domain.size() == 1 {
            println!("{}-{}", coefficients.len(), domain.size());
            //panic!();
        }
        let poly = DensePolynomial::from_coefficients_slice(&*coefficients);
        let evals = poly.evaluate_over_domain(*domain);
        for (i, eval) in evals.evals.iter().enumerate().take(8) {
            if !eval.is_zero() {
                println!("eval_{i}: {}", eval);
            }
        }
    }
}
pub struct MockOpening {
    valid: bool,
    point: Fr<PallasParameters>,
    eval: Fr<PallasParameters>,
}

impl Debug for MockOpening {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MockOpening")
            .field("valid", &self.valid)
            .field("point", &format!("{}", &self.point))
            .field("eval", &format!("{}", &self.eval))
            .finish()
    }
}

impl CommitmentScheme<PallasParameters> for MockScheme {
    type Init = ();
    type Commitment = MockCommitment;
    type Opening = MockOpening;

    const LENGTH: u8 = 8;

    fn init(_init: Self::Init) -> Self {
        Self {}
    }

    fn commit(
        &mut self,
        coefficients: impl Into<Vec<crate::Fr<PallasParameters>>>,
    ) -> Self::Commitment {
        let coefficients = coefficients.into();
        let poly = DensePolynomial::from_coefficients_vec(coefficients);
        let hash = poly.evaluate(&Fr::<PallasParameters>::from(2));
        let coefficients = poly.coeffs;

        Self::Commitment { hash, coefficients }
    }

    fn open(
        &mut self,
        commitment: Self::Commitment,
        point: crate::Fr<PallasParameters>,
        _eval: crate::Fr<PallasParameters>,
    ) -> Self::Opening {
        let eval = DensePolynomial::from_coefficients_vec(commitment.coefficients).evaluate(&point);
        println!("eval: {}", eval);
        let valid = eval == eval;
        Self::Opening { valid, eval, point }
    }

    fn verify(
        &mut self,
        _commitment: Self::Commitment,
        point: Fr<PallasParameters>,
        eval: Fr<PallasParameters>,
        opening: Self::Opening,
    ) -> bool {
        opening.valid && opening.point == point && opening.eval == eval
    }

    fn update_commitment(
        &mut self,
        commitment: Self::Commitment,
        lagrange_commitment: Self::Commitment,
        previous: Option<Fr<PallasParameters>>,
        new: Fr<PallasParameters>,
    ) -> Self::Commitment {
        let previous = previous.unwrap_or(Fr::<PallasParameters>::zero());
        commitment + (lagrange_commitment * (new - previous))
    }
}

impl Add for MockCommitment {
    type Output = Self;

    fn add(mut self, mut rhs: Self) -> Self::Output {
        let hash = self.hash + rhs.hash;
        //println!();
        //println!("homomorphic add");
        //let domain =
        //GeneralEvaluationDomain::<Fr<PallasParameters>>::new(self.coefficients.len()).unwrap();

        //println!("lhs:");
        //self.print_evals(&domain);
        //println!("rhs:");
        //rhs.print_evals(&domain);
        //make both same size filling with zeros
        if self.coefficients.len() < rhs.coefficients.len() {
            self.coefficients
                .resize(rhs.coefficients.len(), Fr::<PallasParameters>::zero());
        } else if self.coefficients.len() > rhs.coefficients.len() {
            rhs.coefficients
                .resize(self.coefficients.len(), Fr::<PallasParameters>::zero());
        }
        self.coefficients
            .iter_mut()
            .zip(rhs.coefficients.into_iter())
            .for_each(|(left, right)| {
                *left += right;
            });
        let coefficients = self.coefficients;
        //println!("result:");
        let c = Self { hash, coefficients };
        //c.print_evals(&domain);
        //println!("------------------------");
        c
    }
}
impl Mul<Fr<PallasParameters>> for MockCommitment {
    type Output = Self;

    fn mul(mut self, rhs: Fr<PallasParameters>) -> Self::Output {
        self.hash *= rhs;
        self.coefficients.iter_mut().for_each(|val| {
            *val *= rhs;
        });
        self
    }
}
impl Into<Vec<u8>> for MockCommitment {
    fn into(self) -> Vec<u8> {
        self.hash
            .0
            .as_ref()
            .iter()
            .flat_map(|limb| limb.to_le_bytes())
            .collect()
    }
}

impl Debug for MockCommitment {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let bytes: Vec<u8> = self.clone().into();
        let hash: Fr<PallasParameters> = hash_to_field::hash_to_field(&*bytes);
        let hash = format!("{}", hash);
        f.debug_struct("MockCommitment")
            .field("hash", &hash)
            .finish()
    }
}
impl From<MockOpening> for bool {
    fn from(opening: MockOpening) -> Self {
        opening.valid
    }
}
