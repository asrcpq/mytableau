extern crate mytableau;

use mytableau::prop_tree::PropTree;
use mytableau::truth_tree::TruthTree;

fn disp(string: &str) {
	let mut truth_tree = Default::default();
	let prop_list = string
		.split('\n')
		.map(|string| PropTree::from_string(string.trim(), &mut truth_tree, TruthTree::alloc_aid))
		.collect();
	println!("Final: {}", truth_tree.prove(prop_list));
	println!();
}
// |(b |(&(b !(a)) a))
// |(a !(a))
// =(>(a b) >(!(b) !(a)))
// &(a !(|(a b)))
// |(&(a c) |(!(a) b))

fn main() {
	for input_str in vec![
		std::include_str!("data/prop0").trim(),
		std::include_str!("data/prop1").trim(),
		std::include_str!("data/dl1").trim(),
		std::include_str!("data/dl2").trim(),
		std::include_str!("data/dl3").trim(),
		std::include_str!("data/dl4").trim(),
		std::include_str!("data/k_branch/tmp").trim(),
	] {
		if cfg!(debug_assertions) {
			println!("{}", input_str);
		} else {
			println!("{}", input_str.len());
		}
		disp(input_str);
	}
}
