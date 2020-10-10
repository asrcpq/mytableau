extern crate mytableau;

use mytableau::prop_tree::PropTree;
use mytableau::truth_tree::TruthTree;

fn disp(string: &str) {
	let prop_tree = PropTree::from_string(string);
	println!("{}", prop_tree.to_string());
	let mut truth_tree = TruthTree::new(vec![prop_tree]);
	println!("{}", truth_tree.prove());
	println!();
}
// |(b |(&(b !(a)) a))
// |(a !(a))
// =(>(a b) >(!(b) !(a)))
// &(a !(|(a b)))
// |(&(a c) |(!(a) b))

fn main() {
	let prop1 = std::include_str!("data/prop1");
	println!("{}", prop1);
	disp(prop1);
}
