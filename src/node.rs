use crate::{
    commitment::{barycentric_weights, lagrange_poly, CommitmentScheme},
    hash_to_field, Fr, ToField,
};
use ark_ec::SWModelParameters;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use bit_vec::BitVec;
use itertools::Itertools;
use std::{
    collections::HashMap,
    fmt::Debug,
    iter::{repeat, Iterator},
    ops::Add,
};

#[cfg(test)]
mod test;

pub(crate) enum Node<P, C, V, const DEPTH: usize, const WIDTH: usize>
where
    P: SWModelParameters,
    C: CommitmentScheme<P>,
    V: ToField<P> + Clone + Debug,
    Fr<P>: From<i64>,
{
    Internal {
        commitment: C::Commitment,
        children: HashMap<[u8; 4], Self>,
    },
    Value {
        commitment: C::Commitment,
        stem: BitVec,
        values_commitments: [C::Commitment; 1],
        values: HashMap<[u8; 4], V>,
    },
    ///for default, should not exit non ephemerally
    Default,
}

impl<P, C, V, const DEPTH: usize, const WIDTH: usize> Default for Node<P, C, V, DEPTH, WIDTH>
where
    P: SWModelParameters,
    Fr<P>: From<i64>,
    C: CommitmentScheme<P>,
    //todo clone is temporary
    V: ToField<P> + Clone + Debug,
{
    fn default() -> Self {
        Self::Default
    }
}
impl<P, C, V, const DEPTH: usize, const WIDTH: usize> Node<P, C, V, DEPTH, WIDTH>
where
    P: SWModelParameters,
    Fr<P>: From<i64>,
    C: CommitmentScheme<P>,
    //todo clone is temporary
    V: ToField<P> + Clone + Debug,
{
    pub(crate) fn new_root(scheme: &mut C) -> Self {
        let root = repeat(Fr::<P>::from(0))
            .take(2_usize.pow(WIDTH as u32))
            .collect::<Vec<_>>();
        println!("root size: {}", root.len());
        let root_commitment = scheme.commit(root);
        Self::Internal {
            commitment: root_commitment,
            children: Default::default(),
        }
    }
    pub(crate) fn get(&self, mut key: BitVec) -> Option<&V> {
        match self {
            Node::Internal { children, .. } => {
                let suffix = key.split_off(WIDTH);
                let mut stem = key.to_bytes();
                stem.resize(4, 0);
                let stem: [u8; 4] = stem.try_into().unwrap();
                children.get(&stem).map(|child| child.get(suffix)).flatten()
            }
            Node::Value { values, .. } => {
                let suffix = key.split_off(key.len() - WIDTH);
                debug_assert_eq!(suffix.len(), WIDTH);
                let mut suffix = suffix.to_bytes();
                suffix.resize(4, 0);
                let suffix: [u8; 4] = suffix.try_into().unwrap();
                values.get(&suffix)
            }
            _ => {
                unreachable!();
            }
        }
    }
    ///splits the full key in stem and last key
    fn stem_and_key(stem_so_far: &BitVec, key: &BitVec) -> (BitVec, BitVec) {
        let mut full_key = stem_so_far.clone();
        full_key.append(&mut key.clone());
        let stem_size = DEPTH * WIDTH;
        let mut stem = full_key;
        let last_key = stem.split_off(stem_size);
        (stem, last_key)
    }
    pub(crate) fn set(
        self,
        mut stem_so_far: BitVec,
        key: BitVec,
        value: V,
        scheme: &mut C,
        precomputation: &Precomputation<P, C>,
    ) -> Self {
        match self {
            Node::Internal {
                commitment,
                mut children,
            } => {
                let (full_stem, last_key) = Self::stem_and_key(&stem_so_far, &key);
                let mut prefix_bits = key;
                let suffix_bits = prefix_bits.split_off(WIDTH);
                let prefix = Self::bits_to_key(prefix_bits.clone());

                if children.contains_key(&prefix) {
                    let prev_hash = children.get(&prefix).unwrap().get_commitment_hash();
                    let position = u32::from_le_bytes(prefix) as usize;
                    let child = children
                        .entry(prefix)
                        .and_modify(|child| {
                            stem_so_far.append(&mut prefix_bits);
                            let old_child = std::mem::take(child);
                            let new_child = old_child.set(
                                stem_so_far,
                                suffix_bits,
                                value,
                                scheme,
                                precomputation,
                            );
                            *child = new_child;
                        })
                        .or_default();
                    let child_commitment_hash = child.get_commitment_hash();
                    let commitment = scheme.update_commitment(
                        commitment,
                        precomputation.get_lagrange_commitment(position).clone(),
                        Some(prev_hash),
                        child_commitment_hash,
                    );
                    Self::Internal {
                        commitment,
                        children,
                    }
                } else {
                    let key = prefix;
                    let last_key = Self::bits_to_key(last_key);
                    let position = u32::from_le_bytes(key) as usize;
                    let child =
                        Self::new_value_node(full_stem, last_key, value, scheme, precomputation);
                    let extension_hash = child.get_commitment_hash();
                    children.insert(key, child);
                    let commitment = scheme.update_commitment(
                        commitment,
                        precomputation.get_lagrange_commitment(position).clone(),
                        None,
                        extension_hash,
                    );
                    Self::Internal {
                        commitment,
                        children,
                    }
                }
            }
            Node::Value {
                commitment,
                stem,
                values_commitments,
                mut values,
            } => {
                let (new_stem, suffix) = Self::stem_and_key(&stem_so_far, &key);
                if stem == new_stem {
                    let key = Self::bits_to_key(suffix);
                    let position = u32::from_le_bytes(key) as usize;
                    let previous = values.get(&key).map(|val| val.to_field());
                    let prev_hash = Self::hash(&values_commitments[0]);
                    let values_commitments = scheme.update_commitment(
                        values_commitments[0].clone(),
                        precomputation.get_lagrange_commitment(position).clone(),
                        previous,
                        value.to_field(),
                    );
                    values.insert(key, value);
                    let values_commitment_hash = Self::hash(&values_commitments);
                    let commitment = scheme.update_commitment(
                        commitment,
                        precomputation.get_lagrange_commitment(3).clone(),
                        Some(prev_hash),
                        values_commitment_hash,
                    );
                    let values_commitments = [values_commitments];
                    Self::Value {
                        commitment,
                        stem: stem.clone(),
                        values_commitments,
                        values,
                    }
                } else {
                    let left = Self::Value {
                        commitment,
                        stem,
                        values_commitments,
                        values,
                    };
                    let key = Self::bits_to_key(suffix);
                    let right =
                        Self::new_value_node(new_stem.clone(), key, value, scheme, precomputation);
                    let new_node = Self::fix_collision(stem_so_far, left, right, precomputation);
                    new_node
                }
            }
            _ => {
                unreachable!();
            }
        }
    }
    fn new_value_node(
        stem: BitVec,
        key: [u8; 4],
        value: V,
        scheme: &mut C,
        precomputation: &Precomputation<P, C>,
    ) -> Self {
        let i = u32::from_le_bytes(key);
        let lagrange_commitment = precomputation.get_lagrange_commitment(i as usize).clone();
        //todo slice
        let suffix_commitment = lagrange_commitment * value.to_field();
        let bytes: Vec<u8> = suffix_commitment.clone().into();
        let suffix_commitment_hash: Fr<P> = hash_to_field::hash_to_field(&*bytes);
        let stem_hash: Fr<P> = hash_to_field::hash_to_field(&*stem.to_bytes());

        let extension_vec = vec![
            Fr::<P>::from(1),
            Fr::<P>::from(1),
            stem_hash,
            suffix_commitment_hash,
        ];
        //todo look at the size
        let extension_commitment = scheme.commit_to_evals(extension_vec);
        let mut values = HashMap::new();
        values.insert(key, value);

        Self::Value {
            commitment: extension_commitment,
            stem,
            values_commitments: [suffix_commitment],
            values,
        }
    }
    ///inserts the necessary internal nodes to fix a collision
    fn fix_collision(
        stem_so_far: BitVec,
        left: Self,
        right: Self,
        precomputation: &Precomputation<P, C>,
    ) -> Self {
        let [left_key, right_key] = [&left, &right].map(|node| {
            let key = node.get_stem().iter().skip(stem_so_far.len()).chunks(WIDTH);
            key.into_iter().map(BitVec::from_iter).collect::<Vec<_>>()
        });
        let sections = left_key.into_iter().zip(right_key.into_iter());
        let (common, difference) = sections.partition::<Vec<_>, _>(|(left, right)| left == right);
        let keys = difference.into_iter().find(|_| true).unwrap();

        let commitment = [(&keys.0, &left), (&keys.1, &right)]
            .map(|(bits, node)| {
                let key = Self::bits_to_key(bits.clone());
                let index = u32::from_le_bytes(key) as usize;
                let value_hash = node.get_commitment_hash();
                let lagrange = precomputation.get_lagrange_commitment(index).clone();
                lagrange * value_hash
            })
            .into_iter()
            .reduce(Add::add)
            .unwrap();
        let mut children = HashMap::new();

        children.insert(Self::bits_to_key(keys.0), left);
        children.insert(Self::bits_to_key(keys.1), right);
        let last_internal = Self::Internal {
            children,
            commitment,
        };
        common
            .into_iter()
            .rev()
            .map(|(a, _)| a)
            .fold(last_internal, |prev, bits| {
                let key = Self::bits_to_key(bits);
                let index = u32::from_le_bytes(key) as usize;
                let hash = prev.get_commitment_hash();
                let lagrange = precomputation.get_lagrange_commitment(index).clone();
                let commitment = lagrange * hash;
                let mut children = HashMap::with_capacity(1);
                children.insert(key, prev);
                Self::Internal {
                    children,
                    commitment,
                }
            })
    }
    fn get_stem(&self) -> &BitVec {
        match self {
            Node::Value { stem, .. } => stem,
            Node::Internal { .. } => {
                panic!("only for value nodes");
            }
            Node::Default => {
                unreachable!()
            }
        }
    }
    pub(crate) fn bits_to_key(bits: BitVec) -> [u8; 4] {
        debug_assert!(bits.blocks().len() <= 4);
        let mut bytes = bits.to_bytes();
        bytes.resize(4, 0);
        bytes.try_into().unwrap()
    }
    fn get_commitment_hash(&self) -> Fr<P> {
        let commitment = match self {
            Node::Internal { commitment, .. } => commitment,
            Node::Value { commitment, .. } => commitment,
            Node::Default => {
                unreachable!()
            }
        };
        let bytes: Vec<u8> = commitment.clone().into();
        hash_to_field::hash_to_field(&*bytes)
    }
    pub(crate) fn get_commitment(&self) -> C::Commitment {
        match self {
            Node::Internal { commitment, .. } | Node::Value { commitment, .. } => {
                commitment.clone()
            }
            Node::Default => unreachable!(),
        }
    }
    fn hash(commitment: &C::Commitment) -> Fr<P> {
        let bytes: Vec<u8> = commitment.clone().into();
        hash_to_field::hash_to_field(&*bytes)
    }
    pub fn get_path(
        &self,
        key: BitVec,
    ) -> Option<(Vec<(C::Commitment, [u8; 4])>, (&V, &C::Commitment))> {
        match self {
            Node::Internal {
                children,
                commitment,
            } => {
                let mut prefix = key;
                let suffix = prefix.split_off(WIDTH);
                let key = Self::bits_to_key(prefix);

                children
                    .get(&key)
                    .map(|child| child.get_path(suffix))
                    .flatten()
                    .map(|(mut path, val)| {
                        path.push((commitment.clone(), key));
                        (path, val)
                    })
            }
            Node::Value {
                values,
                stem,
                commitment,
                values_commitments,
            } => {
                let stem_size = (key.len() - 1) / WIDTH;
                let stem_size = stem_size * WIDTH;
                let mut common_stem = stem.clone();
                let mut stem = key;
                let key = stem.split_off(stem_size);
                common_stem = common_stem.split_off(common_stem.len() - stem_size);
                if common_stem == stem {
                    let key = Self::bits_to_key(key);
                    let val = values.get(&key);
                    val.map(|val| {
                        (
                            vec![(commitment.clone(), key)],
                            (val, &values_commitments[0]),
                        )
                    })
                } else {
                    None
                }
            }
            _ => {
                unreachable!();
            }
        }
    }
}

impl<P, C, V, const DEPTH: usize, const WIDTH: usize> Debug for Node<P, C, V, DEPTH, WIDTH>
where
    P: SWModelParameters,
    Fr<P>: From<i64>,
    C: CommitmentScheme<P>,
    //todo clone is temporary
    V: ToField<P> + Clone + Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Internal {
                commitment,
                children,
            } => f
                .debug_struct("Internal")
                .field("commitment", commitment)
                .field("children", children)
                .finish(),
            Self::Value {
                commitment,
                stem,
                values_commitments,
                values,
            } => f
                .debug_struct("Value")
                .field("commitment", commitment)
                .field("stem", stem)
                .field("values_commitments", values_commitments)
                .field("values", &values)
                .finish(),
            Node::Default => {
                unreachable!()
            }
        }
    }
}

pub(crate) struct Precomputation<P: SWModelParameters, C: CommitmentScheme<P>> {
    lagrange_commitments: Vec<C::Commitment>,
    domain: GeneralEvaluationDomain<Fr<P>>,
}

impl<P: SWModelParameters, C: CommitmentScheme<P>> Precomputation<P, C> {
    pub(crate) fn new(scheme: &mut C, domain: GeneralEvaluationDomain<Fr<P>>) -> Self {
        let weights = barycentric_weights(&domain);
        let lagrange_commitments = domain
            .elements()
            .into_iter()
            .zip(weights.into_iter())
            .map(|(root, weight)| {
                let poly = lagrange_poly(&domain, root, weight);
                scheme.commit(poly.coeffs)
            })
            .collect();
        Self {
            lagrange_commitments,
            domain,
        }
    }
    fn get_lagrange_commitment(&self, position: usize) -> &C::Commitment {
        &self.lagrange_commitments[position]
    }

    /// Get a reference to the precomputation's domain.
    pub(crate) fn domain(&self) -> GeneralEvaluationDomain<Fr<P>> {
        self.domain
    }
}
