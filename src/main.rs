#![feature(proc_macro_hygiene)]
extern crate plex;

mod prop_tree;
mod truth_tree;

use prop_tree::PropTree;
use truth_tree::TruthTree;

fn disp(string: &str) {
	let prop_tree = PropTree::from_string(string);
	println!("{}", prop_tree.to_string());
	let mut truth_tree = TruthTree::new(prop_tree);
	println!("{}", truth_tree.prove());
	println!();
}

fn main() {
	disp("|(b |(&(b !(a)) a))");
	disp("|(a !(a))");
	disp("=(>(a b) >(!(b) !(a)))");
	disp("&(a !(|(a b)))");
	disp("|(&(a c) |(!(a) b))");
}
