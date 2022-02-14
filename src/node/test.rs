use super::{Node, Precomputation};
use crate::commitment::{mock::MockScheme, CommitmentScheme};
use ark_pallas::PallasParameters;
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use bit_vec::BitVec;

type TestNode = Node<PallasParameters, MockScheme, u128, 3, 8>;

#[test]
fn test1() {
    let mut scheme = MockScheme::init(());
    let root = TestNode::new_root(&mut scheme);
    let bytes = [2_u8, 3, 8, 1];
    let domain = GeneralEvaluationDomain::new(255).unwrap();
    let precomputation = Precomputation::new(&mut scheme, domain);
    //println!("key: {:?}", &key);
    let mut update = move |val, node: TestNode, bytes| {
        let key = BitVec::from_bytes(bytes);
        let updated_root = node.set(
            BitVec::new(),
            key,
            val as u128,
            &mut scheme,
            &precomputation,
        );
        println!("root:");
        println!("{:#?}", &updated_root);
        updated_root
    };
    let node = update(8, root, &bytes);
    let node = update(9, node, &bytes);
    let node = update(8, node, &bytes);
    let bytes2 = [3_u8, 3, 1, 2];
    let node = update(3, node, &bytes2);
    let bytes2 = [2_u8, 3, 8, 3];
    let node = update(5, node, &bytes2);
    let key = BitVec::from_bytes(&bytes2);
    let path = node.get_path(key.clone());
    let val = node.get(key).unwrap();
    assert_eq!(val, &5);

    println!("{:#?}", path);
}
