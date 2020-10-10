extern crate mytableau;

use mytableau::prop_tree::PropTree;
use mytableau::truth_tree::TruthTree;

fn disp(string: &str) {
	let mut truth_tree = TruthTree::new();
	let prop_list = string
		.split('\n')
		.map(|string| PropTree::from_string(string.trim(), &mut truth_tree, TruthTree::alloc_aid))
		.collect();
	truth_tree.load(prop_list);
	println!("{}", truth_tree.prove());
	println!();
}
// |(b |(&(b !(a)) a))
// |(a !(a))
// =(>(a b) >(!(b) !(a)))
// &(a !(|(a b)))
// |(&(a c) |(!(a) b))

fn main() {
	for input_str in vec![
		// std::include_str!("data/prop0").trim(),
		// std::include_str!("data/prop1").trim(),
		// std::include_str!("data/dl1").trim(),
		// std::include_str!("data/dl2").trim(),
		// std::include_str!("data/dl3").trim(),
		std::include_str!("data/k_branch/tmp").trim(),
	] {
		println!("{}", input_str);
		disp(input_str);
	}
}
