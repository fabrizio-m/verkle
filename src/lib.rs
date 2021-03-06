use ark_ec::{models::short_weierstrass_jacobian::GroupAffine, AffineCurve, SWModelParameters};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use bit_vec::BitVec;
use commitment::CommitmentScheme;
use ipapc::IpaScheme;
use node::{Node, Precomputation};
pub use proving::MembershipProof;
use std::{fmt::Debug, marker::PhantomData};

pub mod commitment;
mod hash_to_field;
mod node;
mod proving;

type Fr<P> = <GroupAffine<P> as AffineCurve>::ScalarField;

pub struct VerkleTree<P, C, K, V, const DEPTH: usize, const WIDTH: usize>
where
    P: SWModelParameters,
    C: CommitmentScheme<P>,
    V: ToField<P> + Clone + Debug,
    Fr<P>: From<i64>,
    K: Into<BitVec>,
{
    scheme: C,
    root: Node<P, C, V, DEPTH, WIDTH>,
    key: PhantomData<K>,
    precomputation: Precomputation<P, C>,
}

pub type SimpleTree<P, K, V> = VerkleTree<P, IpaScheme<P>, K, V, 3, 8>;

impl<P, C, K, V, const DEPTH: usize, const WIDTH: usize> VerkleTree<P, C, K, V, DEPTH, WIDTH>
where
    P: SWModelParameters,
    C: CommitmentScheme<P>,
    V: ToField<P> + Clone + Debug,
    Fr<P>: From<i64>,
    K: Into<BitVec>,
{
    pub fn new(init: C::Init) -> Self {
        let mut scheme = C::init(init, WIDTH as u8);
        let root = Node::new_root(&mut scheme);
        let domain = GeneralEvaluationDomain::new(2_usize.pow(WIDTH as u32)).unwrap();
        let precomputation = Precomputation::new(&mut scheme, domain);
        Self {
            scheme,
            root,
            key: PhantomData::default(),
            precomputation,
        }
    }
    pub fn new_verifier(init: C::Init) -> Verifier<P, C, K, V, DEPTH, WIDTH> {
        let scheme = C::init(init, WIDTH as u8);
        let domain = GeneralEvaluationDomain::new(2_usize.pow(WIDTH as u32)).unwrap();
        Verifier {
            scheme,
            key: PhantomData::default(),
            value: PhantomData::default(),
            domain,
        }
    }
    ///width as a power
    fn width() -> usize {
        2_usize.pow(WIDTH as u32)
    }
    fn to_key(key: K) -> BitVec {
        let key = key.into();
        assert_eq!(key.len(), (DEPTH + 1) * WIDTH);
        key
    }
    pub fn get(&self, key: K) -> Option<&V> {
        let key = Self::to_key(key);
        self.root.get(key)
    }
    pub fn set(&mut self, key: K, value: V) {
        let scheme = &mut self.scheme;
        let precomputation = &self.precomputation;
        let root = &mut self.root;

        let stem_so_far = BitVec::new();
        let key = key.into();
        take_mut::take(root, |root| {
            root.set(stem_so_far, key, value, scheme, precomputation)
        });
    }
    pub fn get_root(&self) -> Root<P, C> {
        Root(self.root.get_commitment())
    }
    /*pub(crate) fn print(&self) {
        println!("tree:");
        println!("{:#?}", &self.root);
        println!();
    }*/
}

trait Tree {
    type Node;
    type Root;
    type Verifier;
}
pub struct Verifier<P, C, K, V, const DEPTH: usize, const WIDTH: usize>
where
    P: SWModelParameters,
    C: CommitmentScheme<P>,
    V: ToField<P> + Clone + Debug,
    Fr<P>: From<i64>,
    K: Into<BitVec>,
{
    scheme: C,
    key: PhantomData<K>,
    value: PhantomData<V>,
    domain: GeneralEvaluationDomain<Fr<P>>,
}

pub struct Root<P, C>(C::Commitment)
where
    C: CommitmentScheme<P>,
    P: SWModelParameters;

impl<P, C, K, V, const DEPTH: usize, const WIDTH: usize> Tree
    for VerkleTree<P, C, K, V, DEPTH, WIDTH>
where
    P: SWModelParameters,
    C: CommitmentScheme<P>,
    V: ToField<P> + Clone + Debug,
    Fr<P>: From<i64>,
    K: Into<BitVec>,
{
    type Node = node::Node<P, C, V, DEPTH, WIDTH>;
    type Root = Root<P, C>;
    type Verifier = Verifier<P, C, K, V, DEPTH, WIDTH>;
}

pub enum BytesOrField<F> {
    Bytes(Vec<u8>),
    Field(F),
}

impl<F> From<Vec<u8>> for BytesOrField<F> {
    fn from(bytes: Vec<u8>) -> Self {
        Self::Bytes(bytes)
    }
}
pub trait ToField<P: SWModelParameters> {
    ///turns the value directly into a field element, or into bytes for hash_to_field
    fn to_bytes_or_field(&self) -> BytesOrField<Fr<P>>;
    fn to_field(&self) -> Fr<P> {
        match self.to_bytes_or_field() {
            BytesOrField::Bytes(bytes) => hash_to_field::hash_to_field(&*bytes),
            BytesOrField::Field(field) => field,
        }
    }
}
