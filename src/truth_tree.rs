use crate::prop_tree::PropTree;
use crate::prop_tree::{Concept, Proposition};
use std::collections::{HashMap, VecDeque};

pub struct TruthTree {
	nodes: Vec<TruthTreeNode>,
	name_dict: HashMap<usize, String>,
	rev_dict: HashMap<String, usize>,
	aid_max: usize,
}

static mut INDENT: String = String::new();

impl Default for TruthTree {
	fn default() -> Self {
		let mut name_dict = HashMap::new();
		name_dict.insert(0, "Top".to_string());
		name_dict.insert(1, "Bottom".to_string());
		let mut rev_dict = HashMap::new();
		rev_dict.insert("Top".to_string(), 0);
		rev_dict.insert("Bottom".to_string(), 1);
		TruthTree {
			nodes: Vec::new(),
			name_dict,
			rev_dict,
			aid_max: 1,
		}
	}
}

impl TruthTree {
	pub fn get_name(&self, aid: usize) -> &str {
		match self.name_dict.get(&aid) {
			Some(string) => &string,
			None => "NotFound",
		}
	}

	pub fn alloc_aid(&mut self, string: Option<String>) -> usize {
		if let Some(string) = string.clone() {
			match &string[..] {
				"Top" => return 0,
				"Bottom" => return 1,
				_ => {}
			}
			if let Some(id) = self.rev_dict.get(&string) {
				return *id;
			}
		}

		self.aid_max += 1;
		self.name_dict.insert(
			self.aid_max,
			string
				.clone()
				.unwrap_or(format!("autoname{}", self.aid_max)),
		);
		self.rev_dict.insert(
			string.unwrap_or(format!("autoname{}", self.aid_max)),
			self.aid_max,
		);
		self.aid_max
	}

	fn push_node(&mut self, parent: Option<usize>, data: PropTree) -> usize {
		let id = self.nodes.len();
		self.nodes.push(TruthTreeNode { data, parent });
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
					if self.nodes[id_upgoing].data.atom_check(&self.nodes[id].data) {
						return true;
					}
				}
			}
		}
	}

	// Match at start point
	// used for "for all"
	// role: true or false, ident, optional individual name x, for ABox Concept, return a list of y
	fn upmatch_role(&self, id: usize, role: (bool, usize, Option<usize>)) -> Vec<usize> {
		let mut id_upgoing: Option<usize> = Some(id);
		let mut result = Vec::new();
		loop {
			match id_upgoing {
				None => return result,
				Some(id_upgoing) => {
					if let Proposition::ARole(t, ident, ind1, ind2) =
						&self.nodes[id_upgoing].data.root
					{
						// println!("try: {:?} vs {:?}", prop.root, role);
						if role.0 == *t && role.1 == *ident {
							if let Some(ref string) = role.2 {
								if string != ind1 {
									continue;
								}
							}
							result.push(*ind2);
						}
					}
				}
			}
			id_upgoing = self.nodes[id_upgoing.unwrap()].parent;
			// Note there is a continue above
		}
	}

	// id must point to a leaf
	fn prove_recurse(&mut self, id: Option<usize>, mut leaf: Vec<PropTree>) -> bool {
		if cfg!(debug_assertions) {
			unsafe {
				if INDENT.chars().count() % 3 == 1 {
					INDENT.push('┼');
				} else {
					INDENT.push('─');
				}
			}
		}

		let mut unmatched = VecDeque::new();
		let result = loop {
			// fetch last sentence in leaf
			let mut prop_tree = if leaf.is_empty() {
				return true;
			} else {
				leaf.pop().unwrap()
			};
			if cfg!(debug_assertions) {
				unsafe {
					// println!("{}{:?}", INDENT, prop_tree);
					println!("{}{}", INDENT, prop_tree.to_string(&self.name_dict));
				}
			}

			if let Proposition::ARole(_, _, _, _) = prop_tree.root {
				let id = self.push_node(id, prop_tree);
				if self.upmatch(id) {
					break false;
				}
				leaf.extend(unmatched.into_iter());
				break self.prove_recurse(Some(id), leaf);
			}

			let concept_unit = &prop_tree.nodes.last().unwrap().data;
			match concept_unit {
				Concept::And(a, b) => {
					let tree_a = prop_tree.clone_subtree(*a);
					let tree_b = prop_tree.clone_subtree(*b);
					leaf.push(tree_a);
					leaf.push(tree_b);
					leaf.extend(unmatched.into_iter());
					break self.prove_recurse(id, leaf);
				}
				Concept::Or(a, b) => {
					let tree_a = prop_tree.clone_subtree(*a);
					let tree_b = prop_tree.clone_subtree(*b);
					let mut leaf_a = leaf.clone();
					leaf_a.push(tree_a);
					leaf_a.extend(unmatched.clone().into_iter());
					if self.prove_recurse(id, leaf_a) {
						break true;
					}
					let mut leaf_b = leaf;
					leaf_b.push(tree_b);
					leaf_b.extend(unmatched.into_iter());
					break self.prove_recurse(id, leaf_b);
				}
				Concept::Not(a) => {
					let concept_unit = &(&prop_tree.nodes[*a].data);

					match concept_unit {
						Concept::Atom(aid) => {
							if *aid == 0 {
								// Top
								break false;
							}
							if *aid == 1 {
								// Bottom
								break true;
							}
							let new_id = self.push_node(id, prop_tree.clone());
							if self.upmatch(new_id) {
								break false;
							}
							break self.prove_recurse(Some(new_id), leaf);
						}
						_ => {
							prop_tree.nodes.pop();
							prop_tree = prop_tree.negate();
							leaf.push(prop_tree);
							leaf.extend(unmatched.into_iter());
							break self.prove_recurse(id, leaf);
						}
					}
				}
				Concept::Atom(aid) => {
					if *aid == 0 {
					} else if *aid == 1 {
						break false;
					// if let Proposition::AConcept(_) = prop_tree.root {
					// 	break false;
					// }
					} else {
						let id = self.push_node(id, prop_tree.clone());
						if self.upmatch(id) {
							break false;
						}
						leaf.extend(unmatched.into_iter());
						break self.prove_recurse(Some(id), leaf);
					}
				}
				Concept::ForAll(aid, _) => {
					let mut has_match = false;
					if let Some(id) = id {
						for each_y in self
							.upmatch_role(
								id,
								(
									true,
									*aid,
									match prop_tree.root {
										Proposition::TConcept => None,
										Proposition::AConcept(ind) => Some(ind),
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
							leaf.push(prop_tree_new);
						}
					}
					if has_match {
						leaf.extend(unmatched.into_iter());
						break self.prove_recurse(id, leaf);
					} else {
						unmatched.push_back(prop_tree);
					}
				}
				// x in TConcept can become a specific name
				// when we do not take neg role into consideration
				Concept::Exist(aid, _) => {
					let x = self.alloc_aid(None);
					let y = self.alloc_aid(None);
					leaf.push(PropTree::new(&Proposition::ARole(true, *aid, x, y)));
					// remove quantifier
					prop_tree.nodes.pop();
					prop_tree.root = Proposition::AConcept(y);
					leaf.push(prop_tree);
					leaf.extend(unmatched.into_iter());
					break self.prove_recurse(id, leaf);
				}
			}
		};
		if cfg!(debug_assertions) {
			unsafe {
				INDENT.pop();
				println!("{}{}", INDENT, if result { "#t" } else { "#f" });
			}
		}
		result
	}

	pub fn prove(&mut self, leaf: Vec<PropTree>) -> bool {
		unsafe {
			INDENT = String::new();
		}
		self.prove_recurse(None, leaf)
	}
}

struct TruthTreeNode {
	data: PropTree,
	parent: Option<usize>,
}
