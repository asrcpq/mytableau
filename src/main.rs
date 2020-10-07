use std::collections::VecDeque;

#[derive(Clone, Debug)]
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

	fn atom_check(&self, ch: char, neg: bool) -> bool {
		let lexical_unit = match self.nodes.last() {
			Some(node) => { node.lexical_unit },
			None => { return false },
		};
		match lexical_unit {
			LexicalUnit::Atom(ch2) => {
				neg == true && ch == ch2
			},
			LexicalUnit::Not(a) => {
				if let LexicalUnit::Atom(ch2) = self.nodes[a].lexical_unit {
					return ch == ch2
				}
				false
			}
			_ => {false}
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
				'a'..='z' | '(' | '&' | '|' | '!' | '>' | '=' => {
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
						TokenOrUnit::Token('>') => {
							let id = result.push_node(LexicalUnit::Not(id_list[1]));
							result.push_node(LexicalUnit::Or(id, id_list[0]))
						}
						TokenOrUnit::Token('=') => {
							let id1 = result.push_node(LexicalUnit::Not(id_list[1]));
							let id1 = result.push_node(LexicalUnit::Or(id1, id_list[0]));
							let id2 = result.push_node(LexicalUnit::Not(id_list[0]));
							let id2 = result.push_node(LexicalUnit::Or(id2, id_list[1]));
							result.push_node(LexicalUnit::And(id1, id2))
						}
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
		match self.nodes.last().unwrap().lexical_unit {
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
			LexicalUnit::Not(_) => {
				self.nodes.pop();
			},
			LexicalUnit::Atom(_) => {
				self.push_node(LexicalUnit::Not(
					self.nodes[self.nodes.len() - 1].id
				));
			}
		}
		self
	}
}

#[derive(Clone, Debug)]
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
}

impl TruthTree {
	fn new(prop_tree: PropTree) -> TruthTree {
		TruthTree {
			nodes: vec![TruthTreeNode {
				id: 0,
				data: TruthTreeNodeData::Leaf(VecDeque::from(vec![prop_tree.negate()])),
				parent: None,
			}],
		}
	}

	fn push_node(&mut self, parent_id: usize, data: TruthTreeNodeData) -> usize {
		let id = self.nodes.len();
		self.nodes.push(TruthTreeNode {
			id,
			data,
			parent: Some(parent_id),
		});
		id
	}

	fn upmatch(&self, id: usize, ch: char, neg: bool) -> bool {
		let mut id: Option<usize> = Some(id);
		loop {
			id = self.nodes[id.unwrap()].parent;
			match id {
				None => { return false },
				Some(id) => {
					if let TruthTreeNodeData::Stable(prop_tree) = &self.nodes[id].data {
						if prop_tree.atom_check(ch, neg) {
							return true
						}
					} else {
						panic!("Leaf not at leaf position!");
					}
				}
			}
		}
	}

	// id must point to a leaf
	fn prove_recurse(&mut self, id: usize) -> bool {
		// fetch last sentence in leaf
		let mut prop_tree = if let TruthTreeNodeData::Leaf(prop_tree_list) = &mut self.nodes[id].data {
			if prop_tree_list.len() == 0 {
				return false
			} else {
				prop_tree_list.pop_front().unwrap()
			}
		} else { unreachable!() };
		println!("{}", prop_tree.to_string());

		// drain leaf, this node will be stablized
		let mut leaf: VecDeque<PropTree> = match &mut self.nodes[id].data {
			TruthTreeNodeData::Leaf(prop_tree_list) => {prop_tree_list.drain(..).collect()},
			_ => {unreachable!()},
		};

		self.nodes[id].data = TruthTreeNodeData::Stable(prop_tree.clone());
		// break last sentence
		let lexical_unit = prop_tree.nodes.last().unwrap().lexical_unit;
		match lexical_unit {
			LexicalUnit::And(a, b) => {
				let tree_a = prop_tree.clone_subtree(a);
				let tree_b = prop_tree.clone_subtree(b);
				leaf.push_back(tree_a.clone());
				leaf.push_back(tree_b.clone());

				let id = self.push_node(id, TruthTreeNodeData::Leaf(leaf));
				self.prove_recurse(id)
			},
			LexicalUnit::Or(a, b) => {
				let tree_a = prop_tree.clone_subtree(a);
				let tree_b = prop_tree.clone_subtree(b);
				let mut leaf_a = leaf.clone();
				leaf_a.push_back(tree_a.clone());
				let mut leaf_b = leaf;
				leaf_b.push_back(tree_b.clone());

				let id_a = self.push_node(id, TruthTreeNodeData::Leaf(leaf_a));
				if !self.prove_recurse(id_a) { return false }
				let id_b = self.push_node(id, TruthTreeNodeData::Leaf(leaf_b));
				self.prove_recurse(id_b)
			},
			LexicalUnit::Not(a) => {
				let lexical_unit = prop_tree.nodes[a].lexical_unit;

				match lexical_unit {
					LexicalUnit::Atom(ch) => {
						if self.upmatch(id, ch, true) { return true }
					},
					_ => {
						prop_tree.nodes.pop();
						prop_tree = prop_tree.negate();
						leaf.push_back(prop_tree);
					}
				}
				let id = self.push_node(id, TruthTreeNodeData::Leaf(leaf));
				self.prove_recurse(id)
			},
			LexicalUnit::Atom(ch) => {
				if self.upmatch(id, ch, true) { return true }

				let id = self.push_node(id, TruthTreeNodeData::Leaf(leaf));
				self.prove_recurse(id)
			},
		}
	}

	fn prove(&mut self) -> bool {
		self.prove_recurse(0)
	}
}

struct TruthTreeNode {
	id: usize,
	data: TruthTreeNodeData,
	parent: Option<usize>,
}

enum TruthTreeNodeData {
	Leaf(VecDeque<PropTree>),
	Stable(PropTree),
}

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
}
