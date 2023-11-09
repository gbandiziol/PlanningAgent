package leidenuniv.symbolicai.logic;

import java.util.HashMap;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Predicate {
	private String name;
	Vector<Term> terms;
	public boolean not;//means the predicate is the not equal operator
	public boolean eql;//means the predicate is the equal operator
	public boolean add;//means the predicate is an addition operator in the KB
	public boolean del;//means the predicate is a deletion operator in the KB
	public boolean act;//means this predicate is an intention operator
	public boolean adopt;//means this predicate is a goal addition operator
	public boolean drop;//means this predicate is a goal deletion operator
	public boolean neg;//means this predicate is a negated predicate.
	
	public Predicate(Sentence s) {
		//Attempts to create a single Predicate from a Sentence toString method.
		//Only works if the Sentence of course IS a single predicate :-)
		this(s.toString());
	}
	public Predicate(String sfol) {
		//takes as input a string in simplified first order logic
		terms=new Vector<Term>();
		parse(sfol);
	}
	public void parse(String sfol) {
		//Parse the string into the Predicate structure.
		//No need to go through this unless you want to understand how parsing goes, or want to extend your predicate
		try {
			sfol=sfol.trim();
			
			Pattern p=Pattern.compile("\\(\\w*(,\\w*)*\\)");//this is the regular expression that looks for (term,term,...)
			Matcher m=p.matcher(sfol);
			if (m.find()) {
				//if we have terms, we assume pred(term,term2,...) format
				//First parse the predicate itself (the name of the predicate)
				parsePred(sfol.substring(0, m.start()));
				
				//Then parse the terms 
				String[] args=sfol.substring(m.start()+1,m.end()-1).split(",");
				for (String term: args) {
					terms.add(new Term(term));
				}
			}else {
				//We have no terms, so we only parse the predicate itself (the name)
				parsePred(sfol);
			}
		} catch (Exception e) {
			System.out.println("Parse error: invalid predicate syntax " + sfol);
			System.exit(0);
		}
	}
	private void parsePred(String pred) {
		//This parses the predicate name
		//It figures out if the predicate is a reserved predicate; either a comparison (!= or =) or an operator (an addition or deletion to the BDI databases), and then parses the name
		if (pred.equals("!=")) {
			not=true;
			this.name="";
		} else if (pred.equals("=")) {
			eql=true;
			this.name="";
		} else {
			if (pred.startsWith("+")) {
				add=true;
				this.name=pred.substring(1, pred.length());
			} else if (pred.startsWith("-")) {
				del=true;
				this.name=pred.substring(1, pred.length());
			} else if (pred.startsWith("_")) {
				act=true;
				this.name=pred.substring(1, pred.length());
			} else if (pred.startsWith("*")) {
				adopt=true;
				this.name=pred.substring(1, pred.length());
			} else if (pred.startsWith("~")) {
				drop=true;
				this.name=pred.substring(1, pred.length());
			} else if (pred.startsWith("!")) {
				neg=true;
				this.name=pred.substring(1, pred.length());
			} else
				this.name=pred;
			if (!this.name.matches("([a-z]|[A-Z])+"))
			{	System.out.println("Parse error: invalid predicate name syntax "+pred);
				System.exit(0);
			}
		}
	}
	public boolean hasTerms() {
		return terms.size()>0;
	}
	public boolean not() {
		//Check if this is a special predicate ! and check for X!=Y, we use !(X,Y) prefix notation
		//Returns true if term1!=term2
		return not&&bound()&&!getTerm(0).term.equals(getTerm(1).term);
	}
	public boolean eql() {
		//Check if this is a special predicate =, to check for X=Y, we use =(X,Y) prefix notation
		//Returns true if term1==term2
		return eql&&bound()&&getTerm(0).term.equals(getTerm(1).term);
	}
	public boolean bound() {
		//Checks if this predicate is bound, i.e., a predicate that is fully instantiated contains no variables.
		if (hasTerms()) {
			//check if all terms are constants, if not return false
			for (Term t:terms) {
				if (t.var)
					return false;
			}
			return true;
		} else //no terms means this predicate is bound, because it does not have any variables
			return true;
	}
	public boolean isAction() {
		//returns true if this predicate is an operator
		//That is, intention, goal or fact addition/deletions (_/+/-/*/~)
		//The intended semantic is that such operators add or remove/facts to/from the intention, desire, or belief databases of the agent.
		return act|add|del|adopt|drop;
	}
	public Term getTerm(int i) {
		return terms.elementAt(i);
	}
	public  Vector<Term> getTerms(){
		return terms;
	}
	public String getName() {
		return name;
	}
	public String toString() {
		//Returns a string representation for this predicate
		//This is an important function as it is not only used for printing but also for generating copies of predicates
		//and to compare predicates with each other for unification (lexographically identical)
		//Behavior: new Predicate(pred.toString()).toString().equals(pred.toString())==true
		//It creates a copy of pred and string compares that copy with the original always resulting in true.
		String result=(neg?"!":adopt?"*":drop?"~":act?"_":not?"!=":eql?"=":add?"+":del?"-":"")+name;
		if (terms.size()>0) {
			result+="(";
			for (Term t: terms) {
				result+=t.toString()+",";
			}
			result=result.substring(0,result.length()-1)+")";
		}
		return result;
	}
	
}
