use std::collections::VecDeque;

#[derive(Debug)]
struct PropTree {
	nodes: Vec<PropTreeNode>,
}

impl PropTree {
	fn push_node(&mut self, l_unit: LexicalUnit) -> u32 {
		let id = self.nodes.len() as u32;
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
			Unit(u32),
		}
		let mut token_stack: VecDeque<TokenOrUnit> = VecDeque::new();
		for each_char in string.chars() {
			match each_char {
				'a'..='z' | '(' | '&' | '|' | '!' => {
					token_stack.push_back(TokenOrUnit::Token(each_char))
				}
				')' => {
					let mut new_node: PropTreeNode;
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
}

#[derive(Debug)]
struct PropTreeNode {
	id: u32,
	lexical_unit: LexicalUnit,
}

#[derive(Debug)]
enum LexicalUnit {
	And(u32, u32),
	Or(u32, u32),
	Not(u32),
	Atom(char),
}

fn main() {
	println!("{:#?}", PropTree::from_string("|(a &(b !(a)))"));
}
