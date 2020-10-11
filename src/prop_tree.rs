use crate::truth_tree::TruthTree;
use std::collections::{HashMap, VecDeque};

#[derive(Clone, Debug)]
pub struct PropTree {
	pub root: Proposition,
	pub nodes: Vec<PropTreeNode>,
}

impl PropTree {
	// for clone subtree's new tree initialize
	pub fn new(root: &Proposition) -> PropTree {
		PropTree {
			root: root.clone(),
			nodes: Vec::new(),
		}
	}

	// must be concept
	fn concept_atom_check(&self) -> Option<(bool, usize)> {
		match self.nodes.last().unwrap().data {
			Concept::Atom(aid) => Some((true, aid)),
			Concept::Not(a) => {
				if let Concept::Atom(aid) = &self.nodes[a].data {
					Some((false, *aid))
				} else {
					None
				}
			}
			_ => None,
		}
	}

	pub fn atom_check(&self, prop_b: &PropTree) -> bool {
		if let Proposition::AConcept(string) = &self.root {
			if let Proposition::AConcept(string2) = &prop_b.root {
				if string != string2 {
					return false;
				}
			}
		}

		if let Proposition::ARole(f, x, y, z) = &self.root {
			if let Proposition::ARole(f2, x2, y2, z2) = &prop_b.root {
				return f != f2 && x == x2 && y == y2 && z == z2;
			}
			return false;
		}
		if let Proposition::ARole(_, _, _, _) = prop_b.root {
			return false;
		}

		match self.nodes.last() {
			Some(node) => &node.data,
			// only Role has attribute of nodes.is_empty()
			None => return prop_b.nodes.is_empty(),
		};
		let (neg, aid) = if let Some(tuple) = self.concept_atom_check() {
			tuple
		} else {
			return false;
		};
		let (neg2, aid2) = if let Some(tuple) = prop_b.concept_atom_check() {
			tuple
		} else {
			return false;
		};
		neg ^ neg2 && aid == aid2
	}

	pub fn push_node(&mut self, concept: Concept) -> usize {
		let id = self.nodes.len();
		self.nodes.push(PropTreeNode { id, data: concept });
		id
	}

	// must be ident! or panic
	fn pop_ident(&mut self) -> usize {
		match self.nodes.pop() {
			Some(node) => {
				if let Concept::Atom(aid) = node.data {
					aid
				} else {
					panic!("pop_ident not string!")
				}
			}
			_ => unreachable!(),
		}
	}

	pub fn from_string<F>(string: &str, mut truth_tree: &mut TruthTree, alloc_aid: F) -> PropTree
	where
		F: Fn(&mut TruthTree, Option<String>) -> usize,
	{
		use plex::lexer;
		let mut result: PropTree = PropTree {
			root: Proposition::TConcept, // Temporary value
			nodes: Vec::new(),
		};
		#[derive(Debug)]
		pub enum TokenOrUnit {
			Ident(String),
			LeftParenthesis,
			RightParenthesis,
			And,
			Or,
			Not,
			Imply,
			Xnor,
			Whitespace,
			ForAll,
			Exist,
			Unit(usize),
		}
		lexer! {
			pub fn next_token(text: 'a) -> TokenOrUnit;

			r#"[ ]+"# => TokenOrUnit::Whitespace,
			r#"[A-Za-z0-9]+"# => TokenOrUnit::Ident(text.to_owned()),
			r#"\("# => TokenOrUnit::LeftParenthesis,
			r#"\)"# => TokenOrUnit::RightParenthesis,
			r#"\&"# => TokenOrUnit::And,
			r#"\|"# => TokenOrUnit::Or,
			r#"!"# => TokenOrUnit::Not,
			r#">"# => TokenOrUnit::Imply,
			r#"="# => TokenOrUnit::Xnor,
			r#"@"# => TokenOrUnit::ForAll,
			r#"#"# => TokenOrUnit::Exist,
			r#"."# => panic!("Unexpected character: {:?}", text),
		}
		let mut token_stack: VecDeque<TokenOrUnit> = VecDeque::new();
		let mut remaining = string;
		// A - B - C <<< D - TOKEN STACK
		// A - B >>> C - D - ID LIST(C at tail)(until matched bracket)
		while let Some((token, new_remaining)) = next_token(remaining) {
			match token {
				TokenOrUnit::Whitespace => {}
				TokenOrUnit::Unit(_) => unreachable!(),
				TokenOrUnit::RightParenthesis => {
					let mut id_list = Vec::new();
					loop {
						let tou = token_stack.pop_back().unwrap();
						match tou {
							TokenOrUnit::LeftParenthesis => break,
							TokenOrUnit::Ident(string) => {
								id_list.push(result.push_node(Concept::Atom(alloc_aid(
									&mut truth_tree,
									Some(string),
								))));
							}
							TokenOrUnit::Unit(id) => id_list.push(id),
							_ => panic!("Find operator during RPar collapsing"),
						}
					}
					let new_id = match token_stack.pop_back().unwrap() {
						TokenOrUnit::And => result.push_node(Concept::And(id_list[1], id_list[0])),
						TokenOrUnit::Or => result.push_node(Concept::Or(id_list[1], id_list[0])),
						TokenOrUnit::Not => result.push_node(Concept::Not(id_list[0])),
						TokenOrUnit::Imply => {
							let id = result.push_node(Concept::Not(id_list[1]));
							result.push_node(Concept::Or(id, id_list[0]))
						}
						TokenOrUnit::Xnor => {
							let id1 = result.push_node(Concept::Not(id_list[1]));
							let id1 = result.push_node(Concept::Or(id1, id_list[0]));
							let id2 = result.push_node(Concept::Not(id_list[0]));
							let id2 = result.push_node(Concept::Or(id2, id_list[1]));
							result.push_node(Concept::And(id1, id2))
						}
						TokenOrUnit::ForAll => {
							let arg = result.pop_ident();
							result.push_node(Concept::ForAll(arg, id_list[0]))
						}
						TokenOrUnit::Exist => {
							let arg = result.pop_ident();
							result.push_node(Concept::Exist(arg, id_list[0]))
						}
						// ABox found, will override root
						TokenOrUnit::Ident(string) => {
							match id_list.len() {
								1 => {
									result.root = Proposition::AConcept(result.pop_ident());
									result.push_node(Concept::Atom(alloc_aid(
										&mut truth_tree,
										Some(string),
									)));
								}
								2 => {
									let arg1 = result.pop_ident();
									let arg2 = result.pop_ident();
									// assume there is a not, without further check
									result.root = Proposition::ARole(
										match result.nodes.len() {
											0 => true,
											1 => false,
											_ => panic!("ABox role detect in middle of sentence"),
										},
										alloc_aid(&mut truth_tree, Some(string)),
										arg1,
										arg2,
									);
								}
								_ => {
									panic!("ABox not a concept or role!");
								}
							}
							// no need to read this sentence
							break;
						}
						_ => panic!("Unsupported token!"),
					};
					token_stack.push_back(TokenOrUnit::Unit(new_id));
				}
				any_token => token_stack.push_back(any_token),
			}
			remaining = new_remaining;
		}
		// tackle with root node
		if let Some(tou) = token_stack.pop_back() {
			match tou {
				TokenOrUnit::Unit(_) => {}
				TokenOrUnit::Ident(string) => {
					result.push_node(Concept::Atom(alloc_aid(&mut truth_tree, Some(string))));
				}
				_ => panic!("Trailing operator at beginning"),
			}
		}
		if !token_stack.is_empty() {
			panic!("Token remaining: {:?}", token_stack);
		}
		result
	}

	fn to_string_recurse(&self, id: usize, name_dict: &HashMap<usize, String>) -> String {
		match &self.nodes[id].data {
			Concept::And(a, b) => format!(
				"&({} {})",
				self.to_string_recurse(*a, name_dict),
				&self.to_string_recurse(*b, name_dict)
			),
			Concept::Or(a, b) => format!(
				"|({} {})",
				self.to_string_recurse(*a, name_dict),
				&self.to_string_recurse(*b, name_dict)
			),
			Concept::Not(a) => "!".to_string() + &self.to_string_recurse(*a, name_dict),
			Concept::Atom(ch) => name_dict.get(ch).unwrap().to_string(),
			Concept::ForAll(string, a) => {
				format!("@{}.{}", string, self.to_string_recurse(*a, name_dict))
			}
			Concept::Exist(string, a) => {
				format!("#{}.{}", string, self.to_string_recurse(*a, name_dict))
			}
		}
	}

	fn clone_subtree_recurse(&self, new_tree: &mut PropTree, id: usize) -> usize {
		match &self.nodes[id].data {
			Concept::And(a, b) => {
				let a1 = self.clone_subtree_recurse(new_tree, *a);
				let b1 = self.clone_subtree_recurse(new_tree, *b);
				new_tree.push_node(Concept::And(a1, b1))
			}
			Concept::Or(a, b) => {
				let a1 = self.clone_subtree_recurse(new_tree, *a);
				let b1 = self.clone_subtree_recurse(new_tree, *b);
				new_tree.push_node(Concept::Or(a1, b1))
			}
			Concept::Not(a) => {
				let a1 = self.clone_subtree_recurse(new_tree, *a);
				new_tree.push_node(Concept::Not(a1))
			}
			Concept::Atom(aid) => new_tree.push_node(Concept::Atom(*aid)),
			Concept::ForAll(aid, a) => {
				let a1 = self.clone_subtree_recurse(new_tree, *a);
				new_tree.push_node(Concept::ForAll(*aid, a1))
			}
			Concept::Exist(aid, a) => {
				let a1 = self.clone_subtree_recurse(new_tree, *a);
				new_tree.push_node(Concept::Exist(*aid, a1))
			}
		}
	}

	pub fn clone_subtree(&self, id: usize) -> PropTree {
		let mut new_tree = Self::new(&self.root);
		self.clone_subtree_recurse(&mut new_tree, id);
		new_tree
	}

	pub fn negate(mut self) -> PropTree {
		match self.nodes.last().unwrap().data {
			Concept::And(a, b) => {
				self.nodes.pop();
				let a1 = self.push_node(Concept::Not(a));
				let b1 = self.push_node(Concept::Not(b));
				self.push_node(Concept::Or(a1, b1));
			}
			Concept::Or(a, b) => {
				self.nodes.pop();
				let a1 = self.push_node(Concept::Not(a));
				let b1 = self.push_node(Concept::Not(b));
				self.push_node(Concept::And(a1, b1));
			}
			Concept::Not(_) => {
				self.nodes.pop();
			}
			Concept::Atom(_) => {
				self.push_node(Concept::Not(self.nodes[self.nodes.len() - 1].id));
			}
			Concept::Exist(_, _) => {
				if let Concept::Exist(string, a) = self.nodes.pop().unwrap().data {
					let a1 = self.push_node(Concept::Not(a));
					self.push_node(Concept::ForAll(string, a1));
				} else {
					unreachable!();
				}
			}
			Concept::ForAll(_, _) => {
				if let Concept::ForAll(string, a) = self.nodes.pop().unwrap().data {
					let a1 = self.push_node(Concept::Not(a));
					self.push_node(Concept::Exist(string, a1));
				} else {
					unreachable!();
				}
			}
		}
		self
	}

	pub fn to_string(&self, name_dict: &HashMap<usize, String>) -> String {
		let mut result = match &self.root {
			Proposition::ARole(t, ident, ind1, ind2) => {
				return format!(
					"{}{}({} {})",
					if !*t { "!" } else { "" },
					ident.clone(),
					&ind1,
					&ind2,
				)
			}
			_ => String::new(),
		};
		result += &self.to_string_recurse(self.nodes.len() - 1, name_dict);
		if let Proposition::AConcept(a) = &self.root {
			result = format!("{}({})", result, name_dict.get(&a).unwrap());
		}
		result
	}
}

#[derive(Clone, Debug)]
pub struct PropTreeNode {
	id: usize,
	pub data: Concept,
}

#[derive(Clone, Debug)]
pub enum Concept {
	And(usize, usize),
	Or(usize, usize),
	Not(usize),
	ForAll(usize, usize),
	Exist(usize, usize),
	Atom(usize),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Proposition {
	// For TBox concept, we need another concept
	TConcept,
	// For ABox concept, we need another concept and the name of individual
	// Note that concept name is not stored here!
	AConcept(usize),
	// For ABox role, we need three identifiers and negate flag
	ARole(bool, usize, usize, usize),
}

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn test_from_string_to_string() {
		assert_eq!(PropTree::from_string("!(&(a b))").to_string(), "!&(a b)");
		// ABox role
		assert_eq!(PropTree::from_string("a(b c)").to_string(), "a(b c)");
	}

	#[test]
	fn test_negate() {
		// Naive negate
		assert_eq!(PropTree::from_string("a").negate().to_string(), "!a");
		assert_eq!(
			PropTree::from_string("!(&(a b))").negate().to_string(),
			"&(a b)"
		);
		// Negate on and, or
		assert_eq!(
			PropTree::from_string("&(!(a) b)").negate().to_string(),
			"|(!!a !b)"
		);
		assert_eq!(
			PropTree::from_string("|(a &(b c))").negate().to_string(),
			"&(!a !&(b c))"
		);
		assert_eq!(
			PropTree::from_string("#(a !(b))").negate().to_string(),
			"@a.!!b"
		);
	}

	#[test]
	#[should_panic]
	fn test_from_string_failed() {
		println!("{}", PropTree::from_string("&(a b").to_string());
	}
}
