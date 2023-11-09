package leidenuniv.symbolicai.logic;

import java.util.Vector;

public class Sentence {
	//A sentence in our sfol language is a first order definite clause with one or more positive (no negation allowed) conclusion predicates
	//and zero or more positive condition predicates.
	//If no conditions are present, the conditions are assumed to be true. 
	//This is a way to specify facts in your knowledeg based.
	//A clause (rule) is e.g., a(X)&b(joost)&c>d(X,joost), with a-c predicates in the conditions,X a variable, joost a constant, and d(X,joost) the conclusion
	//Or: parent(peter,joost), which case this is a rule without condition, so it's conclusion is true.
	//Conclusions must be fully bound, otherwise your forward chaining inference in Agent will become very complex!
	//Conditions can NOT be action predicates (+-_)
	public Vector<Predicate> conditions;
	public Vector<Predicate> conclusions;

	
	public Sentence (String sent) {
		conditions=new Vector<Predicate>();
		conclusions=new Vector<Predicate>();
		parse(sent);
	}
	public void parse(String sent) {
		//A function that parses an sfol sentence
		String [] lr=sent.split(">");
		if (lr.length>1 && !lr[0].trim().isEmpty()) {
			//we found a rule with an implication
			String[] parts=lr[0].split("&");
			for (String cond: parts) {
				Predicate p=new Predicate(cond);
				if (p.isAction())
				{
					System.out.println("Parse error: actions can not be conditions: "+sent);
					System.exit(0);
				}
				conditions.add(new Predicate(cond));
				
			}
			parts=lr[1].split("&");
			for (String concl: parts) {
				conclusions.add(new Predicate(concl));

			}
		} else {
			//we only found a conclusion (no implication, so conditions are empty)
			String[] parts=lr[0].split("&");
			for (String cond: parts) {
				conclusions.add(new Predicate(cond));
			}
		}
	}
	public String toString() {
		String result="";
		if (conditions.size()>0) {
			for (Predicate cond: conditions)
				result+=cond.toString()+"&";
			result=result.substring(0,result.length()-1)+">";
		}
		for (Predicate concl: conclusions)
			result+=concl.toString()+"&";
		return result.substring(0,result.length()-1);
	}
}
