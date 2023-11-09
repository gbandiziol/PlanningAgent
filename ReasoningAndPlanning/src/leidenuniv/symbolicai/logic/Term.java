package leidenuniv.symbolicai.logic;

import java.util.HashMap;

public class Term {
	public String term;
	public Boolean var;
	
	public Term(String term) {
		//Takes a term as String and parses it.
		parse(term);
	}
	public void parse(String term) {
		//Write a function that parses a term, words that start with a capital are variables, others are constant symbols
		this.term=term;
		
		if (term.matches("[A-Z]\\w*")) 
			var=true;
		else
			var=false;
		
	}
	public boolean substitute(HashMap<String, String> s) {
		//If this term is a variable, and substitution s contains a key-value pair for this variable,
		//then substitute this term with the value. Return true if substitution has occurred.
		if (var && s.containsKey(term)) {
			term=s.get(term);
			var=false;
			return true;
		}
		return false;
	}
	
	public String toString() {
		return term;
	}
}
