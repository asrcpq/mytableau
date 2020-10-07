use std::collections::VecDeque;

#[derive(Debug)]
struct PropTree {
	nodes: Vec<PropTreeNode>,
}

impl PropTree {
	// for clone subtree's new tree initialize
	fn new() -> PropTree {
		PropTree {
			nodes: Vec::new(),
		}
	}

	fn push_node(&mut self, l_unit: LexicalUnit) -> usize {
		let id = self.nodes.len();
		self.nodes.push(PropTreeNode {
			id,
			lexical_unit: l_unit,
		});
		id
	}

	fn from_string(string: &str) -> PropTree {
		let mut result: PropTree = PropTree { nodes: Vec::new() };
		enum TokenOrUnit {
			Token(char),
			Unit(usize),
		}
		let mut token_stack: VecDeque<TokenOrUnit> = VecDeque::new();
		for each_char in string.chars() {
			match each_char {
				'a'..='z' | '(' | '&' | '|' | '!' => {
					token_stack.push_back(TokenOrUnit::Token(each_char))
				}
				')' => {
					let mut id_list = Vec::new();
					loop {
						let tou = token_stack.pop_back().unwrap();
						match tou {
							TokenOrUnit::Token('(') => break,
							TokenOrUnit::Token(ch) => {
								id_list.push(result.push_node(LexicalUnit::Atom(ch)));
							}
							TokenOrUnit::Unit(id) => {
								id_list.push(id);
							}
						}
					}
					let new_id = match token_stack.pop_back().unwrap() {
						TokenOrUnit::Token('&') => {
							result.push_node(LexicalUnit::And(id_list[1], id_list[0]))
						}
						TokenOrUnit::Token('|') => {
							result.push_node(LexicalUnit::Or(id_list[1], id_list[0]))
						}
						TokenOrUnit::Token('!') => result.push_node(LexicalUnit::Not(id_list[0])),
						_ => unreachable!(),
					};
					token_stack.push_back(TokenOrUnit::Unit(new_id));
				}
				_ => {}
			}
		}
		result
	}

	fn to_string_recurse(&self, id: usize) -> String {
		match self.nodes[id].lexical_unit {
			LexicalUnit::And(a, b) => {
				"&(".to_string() +
				&self.to_string_recurse(a) +
				" " +
				&self.to_string_recurse(b) +
				")"
			},
			LexicalUnit::Or(a, b) => {
				"|(".to_string() +
				&self.to_string_recurse(a) +
				" " +
				&self.to_string_recurse(b) +
				")"
			},
			LexicalUnit::Not(a) => {
				"!".to_string() +
				&self.to_string_recurse(a)
			},
			LexicalUnit::Atom(ch) => {
				ch.to_string()
			}
		}
	}

	fn to_string(&self) -> String {
		self.to_string_recurse(self.nodes.len() - 1)
	}

	fn clone_subtree_recurse(&self, new_tree: &mut PropTree, id: usize) -> usize {
		match &self.nodes[id].lexical_unit {
			LexicalUnit::And(a, b) => {
				let a1 = self.clone_subtree_recurse(new_tree, *a);
				let b1 = self.clone_subtree_recurse(new_tree, *b);
				new_tree.push_node(LexicalUnit::And(a1, b1))
			},
			LexicalUnit::Or(a, b) => {
				let a1 = self.clone_subtree_recurse(new_tree, *a);
				let b1 = self.clone_subtree_recurse(new_tree, *b);
				new_tree.push_node(LexicalUnit::Or(a1, b1))
			}
			LexicalUnit::Not(a) => {
				let a1 = self.clone_subtree_recurse(new_tree, *a);
				new_tree.push_node(LexicalUnit::Not(a1))
			}
			atom => {
				new_tree.push_node(*atom)
			}
		}
	}

	fn clone_subtree(&self, id: usize) -> PropTree {
		let mut new_tree = Self::new();
		self.clone_subtree_recurse(&mut new_tree, id);
		new_tree
	}

	fn negate(mut self) -> PropTree {
		match self.nodes[self.nodes.len() - 1].lexical_unit {
			LexicalUnit::And(a, b) => {
				self.nodes.pop();
				let a1 = self.push_node(LexicalUnit::Not(a));
				let b1 = self.push_node(LexicalUnit::Not(b));
				self.push_node(LexicalUnit::Or(a1, b1));
			},
			LexicalUnit::Or(a, b) => {
				self.nodes.pop();
				let a1 = self.push_node(LexicalUnit::Not(a));
				let b1 = self.push_node(LexicalUnit::Not(b));
				self.push_node(LexicalUnit::And(a1, b1));
			},
			LexicalUnit::Not(a) => {
				self.nodes.pop();
			},
			LexicalUnit::Atom(ch) => {
				self.push_node(LexicalUnit::Not(
					self.nodes[self.nodes.len() - 1].id
				));
			}
		}
		self
	}
}

#[derive(Debug)]
struct PropTreeNode {
	id: usize,
	lexical_unit: LexicalUnit,
}

#[derive(Clone, Copy, Debug)]
enum LexicalUnit {
	And(usize, usize),
	Or(usize, usize),
	Not(usize),
	Atom(char),
}

struct TruthTree {
	nodes: Vec<TruthTreeNode>,
	leaf_list: Vec<usize>,
}

impl TruthTree {
	fn new(prop_tree: PropTree) -> TruthTree {
		TruthTree {
			nodes: vec![TruthTreeNode {
				id: 0,
				data: TruthTreeNodeData::Leaf(vec![prop_tree]),
				children: Vec::new(),
				parent: None,
			}],
			leaf_list: vec![0],
		}
	}

	fn prove(&mut self) -> bool {
		while !self.leaf_list.is_empty() {
			let mut truth_tree_node = self.nodes[self.leaf_list.pop().unwrap()];
			let prop_tree = match truth_tree_node.data {
				Stable(prop_tree) => {
					panic!("Not a leaf!");
				}
				Leaf(prop_tree_list) => {
					prop_tree_list.pop()
				}
			};
			let mut leaves = mem::replace(
				&mut truth_tree_node.data,
				prop_tree,
			)
		}
	}
}

struct TruthTreeNode {
	id: usize,
	data: TruthTreeNodeData,
	children: Vec<usize>,
	parent: Option<usize>,
}

enum TruthTreeNodeData {
	Leaf(Vec<PropTree>),
	Stable(PropTree),
}

fn main() {
	println!("{}", PropTree::from_string("|(b |(&(b !(a)) a))").clone_subtree(6).negate().to_string());
}
