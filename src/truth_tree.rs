use crate::prop_tree::PropTree;
use crate::prop_tree::{Concept, Proposition};
use std::collections::VecDeque;

pub struct TruthTree {
	nodes: Vec<TruthTreeNode>,
}

static mut INDENT: String = String::new();

impl TruthTree {
	pub fn new(prop_tree: Vec<PropTree>) -> TruthTree {
		TruthTree {
			nodes: vec![TruthTreeNode {
				data: TruthTreeNodeData::Leaf(prop_tree.into_iter().map(|x| x.negate()).collect()),
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

	fn upmatch(&self, id: usize) -> bool {
		let mut id_upgoing: Option<usize> = Some(id);
		loop {
			id_upgoing = self.nodes[id_upgoing.unwrap()].parent;
			match id_upgoing {
				None => return false,
				Some(id_upgoing) => {
					if if let TruthTreeNodeData::Stable(prop) = &self.nodes[id_upgoing].data {
						prop
					} else {
						panic!("Leaf not at leaf position!")
					}
					.atom_check(
						if let TruthTreeNodeData::Stable(prop_atom) = &self.nodes[id].data {
							prop_atom
						} else {
							panic!("Leaf not at leaf position!")
						},
					) {
						return true;
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

		#[allow(clippy::never_loop)]
		let result = loop {
			if let Proposition::ARole(_, _, _) = prop_tree.root {
				if self.upmatch(id) {
					break true;
				}

				let id = self.push_node(id, TruthTreeNodeData::Leaf(leaf));
				break self.prove_recurse(id);
			}

			let concept_unit = &prop_tree.nodes.last().unwrap().data;
			match concept_unit {
				Concept::And(a, b) => {
					let tree_a = prop_tree.clone_subtree(*a);
					let tree_b = prop_tree.clone_subtree(*b);
					leaf.push_back(tree_a);
					leaf.push_back(tree_b);

					let id = self.push_node(id, TruthTreeNodeData::Leaf(leaf));
					break self.prove_recurse(id);
				}
				Concept::Or(a, b) => {
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
				Concept::Not(a) => {
					let concept_unit = &(&prop_tree.nodes[*a].data);

					match concept_unit {
						Concept::Atom(string) => {
							if self.upmatch(id) {
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
				Concept::Atom(string) => {
					if self.upmatch(id) {
						break true;
					}

					let id = self.push_node(id, TruthTreeNodeData::Leaf(leaf));
					break self.prove_recurse(id);
				}
				_ => {
					panic!("unsupported!");
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
		unsafe {
			INDENT = String::new();
		}
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
