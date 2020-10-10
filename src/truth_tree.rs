use crate::prop_tree::PropTree;
use crate::prop_tree::{Concept, Proposition};
use std::collections::VecDeque;

pub struct TruthTree {
	nodes: Vec<TruthTreeNode>,
	name_index: u32,
}

static mut INDENT: String = String::new();

impl TruthTree {
	pub fn new(prop_tree: Vec<PropTree>) -> TruthTree {
		TruthTree {
			nodes: vec![TruthTreeNode {
				data: TruthTreeNodeData::Leaf(VecDeque::from(prop_tree)),
				parent: None,
			}],
			name_index: 0,
		}
	}

	fn autoname(&mut self) -> String {
		self.name_index += 1;
		format!("Autoname{}", self.name_index)
	}

	fn push_node(&mut self, parent_id: usize, data: TruthTreeNodeData) -> usize {
		let id = self.nodes.len();
		self.nodes.push(TruthTreeNode {
			data,
			parent: Some(parent_id),
		});
		id
	}

	// Collision -> true
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

	// used for "for all"
	// role: true or false, ident, optional individual name x, for ABox Concept, return a list of y
	fn upmatch_role(&self, id: usize, role: (bool, &str, Option<String>)) -> Vec<String> {
		let mut id_upgoing: Option<usize> = Some(id);
		let mut result = Vec::new();
		loop {
			id_upgoing = self.nodes[id_upgoing.unwrap()].parent;
			match id_upgoing {
				None => return result,
				Some(id_upgoing) => {
					if let TruthTreeNodeData::Stable(prop) = &self.nodes[id_upgoing].data {
						if let Proposition::ARole(t, ident, ind1, ind2) = &prop.root {
							// println!("try: {:?} vs {:?}", prop.root, role);
							if role.0 == *t && role.1 == ident {
								if let Some(ref string) = role.2 {
									if string != ind1 {
										continue;
									}
								}
								result.push(ind2.clone());
							}
						}
					} else {
						panic!("Leaf not at leaf position!")
					}
				}
			}
			// Note there is a continue above
		}
	}

	// id must point to a leaf
	fn prove_recurse(&mut self, id: usize) -> bool {
		unsafe {
			if INDENT.chars().count() % 3 == 1 {
				INDENT.push('┼');
			} else {
				INDENT.push('─');
			}
		}

		// drain leaf, this node will be stablized
		let mut leaf: VecDeque<PropTree> = match &mut self.nodes[id].data {
			TruthTreeNodeData::Leaf(prop_tree_list) => prop_tree_list.drain(..).collect(),
			_ => unreachable!(),
		};
		let mut unmatched = VecDeque::new();
		let result = loop {
			// fetch last sentence in leaf
			let mut prop_tree = if leaf.is_empty() {
				return true;
			} else {
				leaf.pop_front().unwrap()
			};
			unsafe {
				//println!("{}{:?}", INDENT, prop_tree);
				println!("{}{}", INDENT, prop_tree.to_string());
			}

			self.nodes[id].data = TruthTreeNodeData::Stable(prop_tree.clone());

			if let Proposition::ARole(_, _, _, _) = prop_tree.root {
				if self.upmatch(id) {
					break false;
				}
				leaf.extend(unmatched.into_iter());
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
					leaf.extend(unmatched.into_iter());
					let id = self.push_node(id, TruthTreeNodeData::Leaf(leaf));
					break self.prove_recurse(id);
				}
				Concept::Or(a, b) => {
					let tree_a = prop_tree.clone_subtree(*a);
					let tree_b = prop_tree.clone_subtree(*b);
					let mut leaf_a = leaf.clone();
					leaf_a.push_back(tree_a);
					leaf_a.extend(unmatched.clone().into_iter());
					let id_a = self.push_node(id, TruthTreeNodeData::Leaf(leaf_a));
					if self.prove_recurse(id_a) {
						break true;
					}
					let mut leaf_b = leaf;
					leaf_b.push_back(tree_b);
					leaf_b.extend(unmatched.into_iter());
					let id_b = self.push_node(id, TruthTreeNodeData::Leaf(leaf_b));
					break self.prove_recurse(id_b);
				}
				Concept::Not(a) => {
					let concept_unit = &(&prop_tree.nodes[*a].data);

					match concept_unit {
						Concept::Atom(string) => {
							if string == "Top" {
								break false;
							}
							if string == "Bottom" {
								break true;
							}
							if self.upmatch(id) {
								break false;
							}
						}
						_ => {
							prop_tree.nodes.pop();
							prop_tree = prop_tree.negate();
							leaf.push_back(prop_tree);
							leaf.extend(unmatched.into_iter());
						}
					}
					let id = self.push_node(id, TruthTreeNodeData::Leaf(leaf));
					break self.prove_recurse(id);
				}
				Concept::Atom(string) => {
					if string == "Top" {
					} else if string == "Bottom" {
						if let Proposition::AConcept(_) = prop_tree.root {
							break false;
						}
					} else {
						if self.upmatch(id) {
							break false;
						}
						leaf.extend(unmatched.into_iter());
						let id = self.push_node(id, TruthTreeNodeData::Leaf(leaf));
						break self.prove_recurse(id);
					}
				}
				Concept::ForAll(string, _) => {
					let mut has_match = false;
					for each_y in self
						.upmatch_role(
							id,
							(
								true,
								string,
								match prop_tree.root {
									Proposition::TConcept => None,
									Proposition::AConcept(ref ind) => Some(ind.clone()),
									_ => unreachable!(),
								},
							),
						)
						.into_iter()
					{
						has_match = true;
						let mut prop_tree_new = prop_tree.clone();
						// remove quantifier
						prop_tree_new.nodes.pop();
						prop_tree_new.root = Proposition::AConcept(each_y);
						leaf.push_back(prop_tree_new);
					}
					if has_match {
						leaf.extend(unmatched.into_iter());
						let id = self.push_node(id, TruthTreeNodeData::Leaf(leaf));
						break self.prove_recurse(id);
					} else {
						unmatched.push_back(prop_tree);
					}
				}
				// x in TConcept can become a specific name
				// when we do not take neg role into consideration
				Concept::Exist(string, _) => {
					let x = self.autoname();
					let y = self.autoname();
					leaf.push_back(PropTree::new(&Proposition::ARole(
						true,
						string.clone(),
						x,
						y.clone(),
					)));
					// remove quantifier
					prop_tree.nodes.pop();
					prop_tree.root = Proposition::AConcept(y);
					leaf.push_back(prop_tree);
					leaf.extend(unmatched.into_iter());
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
