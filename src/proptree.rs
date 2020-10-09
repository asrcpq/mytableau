use std::collections::VecDeque;

#[derive(Clone, Debug)]
pub struct PropTree {
	pub nodes: Vec<PropTreeNode>,
}

impl PropTree {
	// for clone subtree's new tree initialize
	pub fn new() -> PropTree {
		PropTree { nodes: Vec::new() }
	}

	pub fn atom_check(&self, name: &str, neg: bool) -> bool {
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

	pub fn push_node(&mut self, l_unit: LexicalUnit) -> usize {
		let id = self.nodes.len();
		self.nodes.push(PropTreeNode {
			id,
			lexical_unit: l_unit,
		});
		id
	}

	pub fn from_string(string: &str) -> PropTree {
		use plex::lexer;
		let mut result: PropTree = PropTree { nodes: Vec::new() };
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

	pub fn to_string_recurse(&self, id: usize) -> String {
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

	pub fn clone_subtree_recurse(&self, new_tree: &mut PropTree, id: usize) -> usize {
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

	pub fn clone_subtree(&self, id: usize) -> PropTree {
		let mut new_tree = Self::new();
		self.clone_subtree_recurse(&mut new_tree, id);
		new_tree
	}

	pub fn negate(mut self) -> PropTree {
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
pub struct PropTreeNode {
	id: usize,
	pub lexical_unit: LexicalUnit,
}

#[derive(Clone, Debug)]
pub enum LexicalUnit {
	And(usize, usize),
	Or(usize, usize),
	Not(usize),
	Atom(String),
}
