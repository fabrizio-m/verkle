use crate::{
    commitment::CommitmentScheme, hash_to_field, Fr, Root, ToField, Tree, Verifier, VerkleTree,
};
use ark_ec::SWModelParameters;
use ark_ff::Zero;
use ark_pallas::PallasParameters;
use ark_poly::{EvaluationDomain, Evaluations, GeneralEvaluationDomain};
use bit_vec::BitVec;
#[cfg(test)]
use ipapc::IpaScheme;
use itertools::{EitherOrBoth, Itertools, Position};
use std::{collections::HashMap, fmt::Debug};

pub struct MembershipProof<P, C, V>
where
    P: SWModelParameters,
    C: CommitmentScheme<P>,
    V: ToField<P> + Clone + Debug,
    Fr<P>: From<i64>,
{
    key: BitVec,
    value: V,
    path: Vec<(C::Commitment, C::Opening)>,
    value_commitment: C::Commitment,
    value_opening: C::Opening,
}

impl<P, C, V> Debug for MembershipProof<P, C, V>
where
    P: SWModelParameters,
    C: CommitmentScheme<P>,
    V: ToField<P> + Clone + Debug,
    Fr<P>: From<i64>,
    C::Opening: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MembershipProof")
            .field("key", &self.key)
            .field("value", &self.value)
            .field("openings", &self.path)
            .field("value_commitment", &self.value_commitment)
            .field("value_opening", &self.value_opening)
            .finish()
    }
}

type TreeNode<T> = <T as Tree>::Node;

impl<P, C, K, V, const DEPTH: usize, const WIDTH: usize> VerkleTree<P, C, K, V, DEPTH, WIDTH>
where
    P: SWModelParameters,
    C: CommitmentScheme<P>,
    V: ToField<P> + Clone + Debug,
    Fr<P>: From<i64>,
    K: Into<BitVec>,
{
    pub fn prove(&mut self, key: K) -> Option<MembershipProof<P, C, V>> {
        let key = Self::to_key(key);
        let (_, last_key) = Self::stem_and_key(&key);
        let (path, (value, val_commit, last_poly)) = self.root.get_path(key.clone())?;

        let val_hash: Fr<P> = value.to_field();
        let point: Fr<P> = self.precomputation.domain().element(last_key);
        let last_poly = Self::sparse_to_dense_coeffs(last_poly);
        let value_proof = self
            .scheme
            .open(val_commit.clone(), &*last_poly, point, val_hash);

        let mut path = path.into_iter();
        let extension = path.by_ref().take(1).find_or_first(|_| true).unwrap();
        let extension_commitment = extension.0.clone();

        let domain = self.precomputation.domain();
        let openings = path
            .scan(extension_commitment, |prev, (commitment, segment, poly)| {
                let poly = Self::sparse_to_dense_coeffs(poly);
                let bytes: Vec<u8> = prev.clone().into();
                let hash: Fr<P> = hash_to_field::hash_to_field(&*bytes);
                let key = u32::from_le_bytes(segment);
                let point = domain.element(key as usize);
                let proof = self.scheme.open(commitment.clone(), &*poly, point, hash);
                let mut commitment = commitment;
                std::mem::swap(prev, &mut commitment);
                Some((commitment, proof))
            })
            .collect::<Vec<_>>();
        let proof = MembershipProof {
            key,
            value: value.clone(),
            path: openings,
            value_commitment: val_commit.clone(),
            value_opening: value_proof,
        };
        Some(proof)
    }
    ///turns evals into a dense vec of coefficients where missing evals are zero
    fn sparse_to_dense_coeffs(evals: HashMap<usize, Fr<P>>) -> Vec<Fr<P>> {
        let width = Self::width();
        let mut dense = Vec::with_capacity(width);
        dense.resize(width, Fr::<P>::zero());
        evals.into_iter().for_each(|(i, eval)| {
            dense[i] = eval;
        });

        let domain = GeneralEvaluationDomain::<Fr<P>>::new(width).unwrap();
        let evals = Evaluations::from_vec_and_domain(dense, domain);
        let coeffs = evals.interpolate();

        coeffs.coeffs
    }
    fn stem_and_key(full_key: &BitVec) -> (BitVec, usize) {
        let stem_size = Self::stem_size();
        let mut stem = full_key.clone();
        let key = stem.split_off(stem_size);
        let key = TreeNode::<Self>::bits_to_key(key);
        let key = u32::from_le_bytes(key);

        (stem, key as usize)
    }
    //make const when supported
    fn stem_size() -> usize {
        DEPTH * WIDTH
    }
    pub fn verify(
        root: Root<P, C>,
        proof: MembershipProof<P, C, V>,
        scheme: &mut C,
        domain: impl EvaluationDomain<Fr<P>>,
    ) -> Option<V> {
        let MembershipProof {
            key,
            value,
            path: openings,
            value_commitment,
            value_opening,
        } = proof;
        if openings.len() * WIDTH > Self::stem_size() {
            return None;
        }
        if openings.is_empty() {
            return None;
        }
        if key.len() != (DEPTH + 1) * WIDTH {
            return None;
        }
        let segments = key.iter().chunks(WIDTH);
        let (path, mut last) = segments
            .into_iter()
            .zip_longest(openings.into_iter().rev())
            .map(|pair| match pair {
                EitherOrBoth::Both(a, b) => (a, Some(b)),
                EitherOrBoth::Left(a) => (a, None),
                EitherOrBoth::Right(_) => unreachable!(),
            })
            .with_position()
            .filter(|position| match position {
                Position::First(a) | Position::Middle(a) => a.1.is_some(),
                Position::Last(_) => true,
                Position::Only(_) => unreachable!(),
            })
            .partition::<Vec<_>, _>(|elem| match elem {
                Position::Only(_) => unreachable!(),
                Position::Last(_) => false,
                _ => true,
            });
        let (last_commitment, valid) = path
            .into_iter()
            .filter_map(|pair| {
                let (segment, open) = pair.into_inner();
                open.map(|open| (BitVec::from_iter(segment), open))
            })
            .fold((root.0, true), |state, (segment, open)| {
                let (prev_commitment, valid) = state;
                let (commitment, opening) = open;
                let bytes = commitment.clone().into();
                let hash = hash_to_field::hash_to_field(&*bytes);
                let key = TreeNode::<Self>::bits_to_key(segment);
                let point = u32::from_le_bytes(key);
                let point = domain.element(point as usize);
                let check = scheme.verify(prev_commitment, point, hash, opening);
                (commitment, check && valid)
            });
        if !valid {
            return None;
        }
        let stem: BitVec = key.iter().take(DEPTH * WIDTH).collect();
        let stem_hash = hash_to_field::hash_to_field(&*stem.to_bytes());
        let bytes = value_commitment.clone().into();
        let suffix_commitment_hash = hash_to_field::hash_to_field(&*bytes);

        let extension_vec = vec![
            Fr::<P>::from(1),
            Fr::<P>::from(1),
            stem_hash,
            suffix_commitment_hash,
        ];
        let domain = GeneralEvaluationDomain::new(Self::width()).unwrap();
        let extension_commitment = scheme.commit_to_evals(extension_vec, domain);
        if extension_commitment != last_commitment {
            return None;
        }
        let val_hash = value.to_field();
        let last_key = last.pop().unwrap();
        let last_key: BitVec = last_key.into_inner().0.collect();
        let point = TreeNode::<Self>::bits_to_key(last_key);
        let point = u32::from_le_bytes(point);
        let point = domain.element(point as usize);
        if scheme.verify(value_commitment, point, val_hash, value_opening) {
            Some(value)
        } else {
            None
        }
    }
}
impl<P, C, K, V, const DEPTH: usize, const WIDTH: usize> Verifier<P, C, K, V, DEPTH, WIDTH>
where
    P: SWModelParameters,
    C: CommitmentScheme<P>,
    V: ToField<P> + Clone + Debug,
    Fr<P>: From<i64>,
    K: Into<BitVec>,
{
    pub fn verify(&mut self, root: Root<P, C>, proof: MembershipProof<P, C, V>) -> Option<V> {
        let mut scheme = &mut self.scheme;
        let domain = self.domain;
        VerkleTree::<P, C, K, V, DEPTH, WIDTH>::verify(root, proof, &mut scheme, domain)
    }
}

impl ToField<PallasParameters> for u128 {
    fn to_bytes_or_field(&self) -> crate::BytesOrField<Fr<PallasParameters>> {
        self.to_le_bytes().to_vec().into()
    }
}
#[cfg(test)]
type TestTree = VerkleTree<PallasParameters, IpaScheme<PallasParameters>, BitVec, u128, 3, 8>;
#[test]
fn prove() {
    let init = ipapc::Init::Seed(1);
    let mut tree = TestTree::new(init);

    let make_key = |key: [u8; 4]| BitVec::from_bytes(&key);
    /*let print_commit = |tree: &TestTree| {
        let e = &tree.root;
        match e {
            crate::node::Node::Internal { commitment, .. } => {
                println!();
                commitment.print_evals(&tree.precomputation.domain());
            }
            _ => unreachable!(),
        }
    };*/

    tree.set(make_key([0, 1, 2, 3]), 4);
    tree.set(make_key([0, 1, 2, 3]), 5);
    tree.set(make_key([0, 1, 2, 4]), 3);
    tree.set(make_key([0, 2, 8, 3]), 8);
    tree.set(make_key([0, 1, 3, 4]), 3);
    let root = tree.get_root();
    //tree.print();
    //print_commit(&tree);
    let proof = tree.prove(make_key([0, 1, 2, 3])).unwrap();
    let init = ipapc::Init::Seed(1);
    let mut verifier = TestTree::new_verifier(init);
    verifier.verify(root, proof).unwrap();
}
