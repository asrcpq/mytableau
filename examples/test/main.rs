extern crate mytableau;

use std::io::prelude::*;

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
	let mut strings = Vec::new();
	for arg in std::env::args().skip(1) {
		let mut string = "".to_string();
		let f = std::fs::File::open(arg).unwrap();
		let mut f = std::io::BufReader::new(f);
		f.read_to_string(&mut string).unwrap();
		strings.push(string.trim().to_string());
	}
	if strings.is_empty() {
		strings = vec![
			std::include_str!("data/prop0").trim().to_string(),
			std::include_str!("data/prop1").trim().to_string(),
			std::include_str!("data/dl1").trim().to_string(),
			std::include_str!("data/dl2").trim().to_string(),
			std::include_str!("data/dl3").trim().to_string(),
			std::include_str!("data/dl4").trim().to_string(),
		]
	}
	for input_str in strings {
		if cfg!(debug_assertions) {
			println!("{}", input_str);
		} else {
			println!("{}", input_str.len());
		}
		disp(&input_str);
	}
}
