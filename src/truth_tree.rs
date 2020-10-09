use crate::prop_tree::PropTree;
use crate::prop_tree::LexicalUnit;
use std::collections::VecDeque;

pub struct TruthTree {
	nodes: Vec<TruthTreeNode>,
}

static mut INDENT: String = String::new();

impl TruthTree {
	pub fn new(prop_tree: PropTree) -> TruthTree {
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

		#[allow(clippy::never_loop)]
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

	pub fn prove(&mut self) -> bool {
		unsafe { INDENT = String::new(); }
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
