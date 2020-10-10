use std::collections::VecDeque;

#[derive(Clone, Debug)]
pub struct PropTree {
	pub root: Proposition,
	pub nodes: Vec<PropTreeNode>,
}

impl PropTree {
	// for clone subtree's new tree initialize
	pub fn new() -> PropTree {
		PropTree {
			root: Proposition::TConcept,
			nodes: Vec::new(),
		}
	}

	// must be concept
	fn concept_atom_check(&self) -> Option<(bool, &str)> {
		match self.nodes.last().unwrap().data {
			Concept::Atom(ref string) => Some((true, string)),
			Concept::Not(a) => {
				if let Concept::Atom(ref string) = &self.nodes[a].data {
					Some((false, string))
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
					return false
				}
			}
		}

		//let flag = false;
		//if let Proposition::ARole(x, y, z) == self.root {
		//	flag = !flag;
		//}
		//if let Proposition::ARole(x, y, z) == self.root {
		//	flag = !flag;
		//}
		//if flag { return false }

		match self.nodes.last() {
			Some(node) => &node.data,
			// only Role has attribute of nodes.is_empty()
			None => return prop_b.nodes.is_empty(),
		};
		let (neg, string) = if let Some(tuple) = self.concept_atom_check() {
			tuple
		} else {
			return false;
		};
		let (neg2, string2) = if let Some(tuple) = prop_b.concept_atom_check() {
			tuple
		} else {
			return false;
		};
		neg ^ neg2 && string == string2
	}

	pub fn push_node(&mut self, concept: Concept) -> usize {
		let id = self.nodes.len();
		self.nodes.push(PropTreeNode { id, data: concept });
		id
	}

	// must be ident! or panic
	fn pop_ident(&mut self) -> String {
		match self.nodes.pop() {
			Some(node) => {
				if let Concept::Atom(string) = node.data {
					string
				} else {
					panic!("pop_ident not string!")
				}
			}
			_ => unreachable!(),
		}
	}

	pub fn from_string(string: &str) -> PropTree {
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
			r#"[A-Za-z]+"# => TokenOrUnit::Ident(text.to_owned()),
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
								id_list.push(result.push_node(Concept::Atom(string)));
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
						// ABox found, will override root
						TokenOrUnit::Ident(string) => {
							match id_list.len() {
								1 => {
									result.root = Proposition::AConcept(result.pop_ident());
									result.push_node(Concept::Atom(string));
								}
								2 => {
									let arg2 = result.pop_ident();
									let arg1 = result.pop_ident();
									// assume there is a not, without further check
									if result.nodes.len() == 0 {
										result.root = Proposition::ARole(true, string, arg1, arg2);
									} else if result.nodes.len() == 1 {
										result.root = Proposition::ARole(false, string, arg1, arg2);
									} else {
										panic!("ABox role detect in middle of sentence")
									}
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
		result
	}

	pub fn to_string_recurse(&self, id: usize) -> String {
		match &self.nodes[id].data {
			Concept::And(a, b) => {
				"&(".to_string()
					+ &self.to_string_recurse(*a)
					+ " " + &self.to_string_recurse(*b)
					+ ")"
			}
			Concept::Or(a, b) => {
				"|(".to_string()
					+ &self.to_string_recurse(*a)
					+ " " + &self.to_string_recurse(*b)
					+ ")"
			}
			Concept::Not(a) => "!".to_string() + &self.to_string_recurse(*a),
			Concept::Atom(ch) => ch.to_string(),
			_ => panic!("Unsupported concept unit"),
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
			atom => new_tree.push_node(atom.clone()),
		}
	}

	pub fn clone_subtree(&self, id: usize) -> PropTree {
		let mut new_tree = Self::new();
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
			_ => panic!("Unsupported concept unit!"),
		}
		self
	}
}

impl std::fmt::Display for PropTree {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		let mut result = match &self.root {
			Proposition::ARole(t, a, b, c) => {
				return write!(f, "{}{}({}, {})", if *t {"!"} else {""}, a.clone(), &b, &c)
			}
			_ => {String::new()},
		};
		result += &self.to_string_recurse(self.nodes.len() - 1);
		if let Proposition::AConcept(a) = &self.root {
			result = format!("{}({})", result, a);
		}
		write!(f, "{}", result)
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
	ForAll(String, usize),
	Exist(String, usize),
	Atom(String),
}

#[derive(Clone, Debug, PartialEq)]
pub enum Proposition {
	// For TBox concept, we need another concept
	TConcept,
	// For ABox concept, we need another concept and the name of individual
	// Note that concept name is not stored here!
	AConcept(String),
	// For ABox role, we need three identifiers and negate flag
	ARole(bool, String, String, String),
}
