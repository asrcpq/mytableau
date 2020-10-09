#![feature(proc_macro_hygiene)]
extern crate plex;

use std::collections::VecDeque;

#[derive(Clone, Debug)]
struct PropTree {
	nodes: Vec<PropTreeNode>,
}

impl PropTree {
	// for clone subtree's new tree initialize
	fn new() -> PropTree {
		PropTree { nodes: Vec::new() }
	}

	fn atom_check(&self, name: &str, neg: bool) -> bool {
		let lexical_unit = &match self.nodes.last() {
			Some(node) => &node.lexical_unit,
			None => return false,
		};
		match lexical_unit {
			LexicalUnit::Atom(string) => neg && *name == *string,
			LexicalUnit::Not(a) => {
				if let LexicalUnit::Atom(string) = &self.nodes[*a].lexical_unit {
					return !neg && *name == *string;
				}
				false
			}
			_ => false,
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
		use plex::lexer;
		let mut result: PropTree = PropTree { nodes: Vec::new() };
		#[derive(Debug)]
		enum TokenOrUnit {
			Ident(String),
			LeftParenthesis,
			RightParenthesis,
			And,
			Or,
			Not,
			Imply,
			Xnor,
			Whitespace,
			Unit(usize),
		}
		lexer! {
			fn next_token(text: 'a) -> TokenOrUnit;

			r#"[ ]+"# => TokenOrUnit::Whitespace,
			r#"[A-Za-z]+"# => TokenOrUnit::Ident(text.to_owned()),
			r#"\("# => TokenOrUnit::LeftParenthesis,
			r#"\)"# => TokenOrUnit::RightParenthesis,
			r#"\&"# => TokenOrUnit::And,
			r#"\|"# => TokenOrUnit::Or,
			r#"!"# => TokenOrUnit::Not,
			r#">"# => TokenOrUnit::Imply,
			r#"="# => TokenOrUnit::Xnor,
			r#"."# => panic!("Unexpected character: {}", text),
		}
		let mut token_stack: VecDeque<TokenOrUnit> = VecDeque::new();
		let mut remaining = string;
		loop {
			if let Some((token, new_remaining)) = next_token(remaining) {
				match token {
					TokenOrUnit::Whitespace => {},
					TokenOrUnit::Unit(_) => unreachable!(),
					TokenOrUnit::RightParenthesis => {
						let mut id_list = Vec::new();
						loop {
							let tou = token_stack.pop_back().unwrap();
							match tou {
								TokenOrUnit::LeftParenthesis => break,
								TokenOrUnit::Ident(string) => {
									id_list.push(result.push_node(LexicalUnit::Atom(string)));
								}
								TokenOrUnit::Unit(id) => id_list.push(id),
								_ => panic!("Find operator during RPar collapsing"),
							}
						}
						let new_id = match token_stack.pop_back().unwrap() {
							TokenOrUnit::And => {
								result.push_node(LexicalUnit::And(id_list[1], id_list[0]))
							}
							TokenOrUnit::Or => {
								result.push_node(LexicalUnit::Or(id_list[1], id_list[0]))
							}
							TokenOrUnit::Not => {
								result.push_node(LexicalUnit::Not(id_list[0]))
							}
							TokenOrUnit::Imply => {
								let id = result.push_node(LexicalUnit::Not(id_list[1]));
								result.push_node(LexicalUnit::Or(id, id_list[0]))
							}
							TokenOrUnit::Xnor => {
								let id1 = result.push_node(LexicalUnit::Not(id_list[1]));
								let id1 = result.push_node(LexicalUnit::Or(id1, id_list[0]));
								let id2 = result.push_node(LexicalUnit::Not(id_list[0]));
								let id2 = result.push_node(LexicalUnit::Or(id2, id_list[1]));
								result.push_node(LexicalUnit::And(id1, id2))
							}
							_ => panic!("Function name invalid!"),
						};
						token_stack.push_back(TokenOrUnit::Unit(new_id));
					},
					any_token => {
						token_stack.push_back(any_token)
					},
				}
				remaining = new_remaining;
			} else {
				break result
			}
		}
	}

	fn to_string_recurse(&self, id: usize) -> String {
		match &self.nodes[id].lexical_unit {
			LexicalUnit::And(a, b) => {
				"&(".to_string()
					+ &self.to_string_recurse(*a)
					+ " " + &self.to_string_recurse(*b)
					+ ")"
			}
			LexicalUnit::Or(a, b) => {
				"|(".to_string()
					+ &self.to_string_recurse(*a)
					+ " " + &self.to_string_recurse(*b)
					+ ")"
			}
			LexicalUnit::Not(a) => "!".to_string() + &self.to_string_recurse(*a),
			LexicalUnit::Atom(ch) => ch.to_string(),
		}
	}

	fn clone_subtree_recurse(&self, new_tree: &mut PropTree, id: usize) -> usize {
		match &self.nodes[id].lexical_unit {
			LexicalUnit::And(a, b) => {
				let a1 = self.clone_subtree_recurse(new_tree, *a);
				let b1 = self.clone_subtree_recurse(new_tree, *b);
				new_tree.push_node(LexicalUnit::And(a1, b1))
			}
			LexicalUnit::Or(a, b) => {
				let a1 = self.clone_subtree_recurse(new_tree, *a);
				let b1 = self.clone_subtree_recurse(new_tree, *b);
				new_tree.push_node(LexicalUnit::Or(a1, b1))
			}
			LexicalUnit::Not(a) => {
				let a1 = self.clone_subtree_recurse(new_tree, *a);
				new_tree.push_node(LexicalUnit::Not(a1))
			}
			atom => new_tree.push_node(atom.clone()),
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
			}
			LexicalUnit::Or(a, b) => {
				self.nodes.pop();
				let a1 = self.push_node(LexicalUnit::Not(a));
				let b1 = self.push_node(LexicalUnit::Not(b));
				self.push_node(LexicalUnit::And(a1, b1));
			}
			LexicalUnit::Not(_) => {
				self.nodes.pop();
			}
			LexicalUnit::Atom(_) => {
				self.push_node(LexicalUnit::Not(self.nodes[self.nodes.len() - 1].id));
			}
		}
		self
	}
}

impl std::fmt::Display for PropTree {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{}", self.to_string_recurse(self.nodes.len() - 1))
	}
}

#[derive(Clone, Debug)]
struct PropTreeNode {
	id: usize,
	lexical_unit: LexicalUnit,
}

#[derive(Clone, Debug)]
enum LexicalUnit {
	And(usize, usize),
	Or(usize, usize),
	Not(usize),
	Atom(String),
}

struct TruthTree {
	nodes: Vec<TruthTreeNode>,
}

static mut INDENT: String = String::new();

impl TruthTree {
	fn new(prop_tree: PropTree) -> TruthTree {
		TruthTree {
			nodes: vec![TruthTreeNode {
				data: TruthTreeNodeData::Leaf(VecDeque::from(vec![prop_tree.negate()])),
				parent: None,
			}],
		}
	}

	fn push_node(&mut self, parent_id: usize, data: TruthTreeNodeData) -> usize {
		let id = self.nodes.len();
		self.nodes.push(TruthTreeNode {
			data,
			parent: Some(parent_id),
		});
		id
	}

	fn upmatch(&self, id: usize, string: &str, neg: bool) -> bool {
		let mut id: Option<usize> = Some(id);
		loop {
			id = self.nodes[id.unwrap()].parent;
			match id {
				None => return false,
				Some(id) => {
					if let TruthTreeNodeData::Stable(prop_tree) = &self.nodes[id].data {
						if prop_tree.atom_check(string, neg) {
							return true;
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
		unsafe {
			INDENT.push('│');
		}
		// fetch last sentence in leaf
		let mut prop_tree =
			if let TruthTreeNodeData::Leaf(prop_tree_list) = &mut self.nodes[id].data {
				if prop_tree_list.is_empty() {
					return false;
				} else {
					prop_tree_list.pop_front().unwrap()
				}
			} else {
				unreachable!()
			};
		unsafe {
			println!("{}{}", INDENT, prop_tree.to_string());
		}

		// drain leaf, this node will be stablized
		let mut leaf: VecDeque<PropTree> = match &mut self.nodes[id].data {
			TruthTreeNodeData::Leaf(prop_tree_list) => prop_tree_list.drain(..).collect(),
			_ => unreachable!(),
		};

		self.nodes[id].data = TruthTreeNodeData::Stable(prop_tree.clone());
		// break last sentence
		let lexical_unit = &(&prop_tree.nodes.last().unwrap().lexical_unit);
		let result = loop {
			match lexical_unit {
				LexicalUnit::And(a, b) => {
					let tree_a = prop_tree.clone_subtree(*a);
					let tree_b = prop_tree.clone_subtree(*b);
					leaf.push_back(tree_a);
					leaf.push_back(tree_b);

					let id = self.push_node(id, TruthTreeNodeData::Leaf(leaf));
					break self.prove_recurse(id);
				}
				LexicalUnit::Or(a, b) => {
					let tree_a = prop_tree.clone_subtree(*a);
					let tree_b = prop_tree.clone_subtree(*b);
					let mut leaf_a = leaf.clone();
					leaf_a.push_back(tree_a);
					let mut leaf_b = leaf;
					leaf_b.push_back(tree_b);

					let id_a = self.push_node(id, TruthTreeNodeData::Leaf(leaf_a));
					if !self.prove_recurse(id_a) {
						break false;
					}
					let id_b = self.push_node(id, TruthTreeNodeData::Leaf(leaf_b));
					break self.prove_recurse(id_b);
				}
				LexicalUnit::Not(a) => {
					let lexical_unit = &(&prop_tree.nodes[*a].lexical_unit);

					match lexical_unit {
						LexicalUnit::Atom(string) => {
							if self.upmatch(id, string, true) {
								break true;
							}
						}
						_ => {
							prop_tree.nodes.pop();
							prop_tree = prop_tree.negate();
							leaf.push_back(prop_tree);
						}
					}
					let id = self.push_node(id, TruthTreeNodeData::Leaf(leaf));
					break self.prove_recurse(id);
				}
				LexicalUnit::Atom(string) => {
					if self.upmatch(id, string, true) {
						break true;
					}

					let id = self.push_node(id, TruthTreeNodeData::Leaf(leaf));
					break self.prove_recurse(id);
				}
			}
		};
		unsafe {
			INDENT.pop();
			println!("{}{}", INDENT, result);
		}
		result
	}

	fn prove(&mut self) -> bool {
		self.prove_recurse(0)
	}
}

struct TruthTreeNode {
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
	unsafe {
		INDENT = String::new();
	}
	println!("{}", truth_tree.prove());
	println!();
}

fn main() {
	disp("|(b |(&(b !(a)) a))");
	disp("|(a !(a))");
	disp("=(>(a b) >(!(b) !(a)))");
	disp("&(a !(|(a b)))");
	disp("|(&(a c) |(!a b))");
}
