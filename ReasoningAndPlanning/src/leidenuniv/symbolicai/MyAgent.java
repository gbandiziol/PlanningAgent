package leidenuniv.symbolicai;

import java.util.Collection;
import java.util.HashMap;
import java.util.Vector;

import leidenuniv.symbolicai.environment.Maze;
import leidenuniv.symbolicai.logic.KB;
import leidenuniv.symbolicai.logic.Predicate;
import leidenuniv.symbolicai.logic.Sentence;
import leidenuniv.symbolicai.logic.Term;

public class MyAgent extends Agent {
	
	

	@Override
	public KB forwardChain(KB kb) {
		//This method should perform a forward chaining on the kb given as argument, until no new facts are added to the KB.
		//It starts with an empty list of facts. When ready, it returns a new KB of ground facts (bounded).
		//The resulting KB includes all deduced predicates, actions, additions and deletions, and goals.
		//These are then processed by processFacts() (which is already implemented for you)
		//HINT: You should assume that forwardChain only allows bound predicates to be added to the facts list for now.
		

		HashMap<String, Predicate> facts = new HashMap<String, Predicate>(); 
		Collection<Predicate> factsvector = new Vector<Predicate>();
		Collection<HashMap<String, String>> allSubstitutions = new Vector<HashMap<String, String>>();
		
		for (Sentence s : kb.rules()) { 
			//if the conditions vector is not empty you can add all the already known facts to the factsvector
			if (!s.conditions.isEmpty()) {
				for (Predicate t : s.conclusions) {
					facts.put(t.toString(), t);
					factsvector.add(t);
				}
			}
			//if there exist a substitution list it means there are legit facts you can add to the KB 
			if (findAllSubstitions(allSubstitutions, new HashMap<String, String>(), s.conditions, facts)) {
				for (HashMap<String, String> substitutions: allSubstitutions) {
					for (Predicate t : s.conclusions) {
						if (!t.add) { //exception
							Predicate bound = substitute(t, substitutions); //these need to be added to the KB							
							factsvector.add(bound);
							facts.put(bound.toString(), bound); //in this way you remember which fact is already added
						}
					}
				}
			}
		}
		//after all these loops have been done the factsvector can be inserted to a new KB
		KB newKB = new KB(factsvector); 
		return newKB;
	}

	@Override
	public boolean findAllSubstitions(Collection<HashMap<String, String>> allSubstitutions, HashMap<String, String> substitution, 
			Vector<Predicate> conditions, HashMap<String, Predicate> facts) {	
		//Recursive method to find all valid substitutions for a vector of conditions, given a set of facts		
		//The recursion is over Vector<Predicate> conditions (so this vector gets shorter and shorter, the farther you are with finding substitutions)		
		//It returns true if at least one substitution is found (can be the empty substitution, if nothing needs to be substituted to unify the conditions with the facts)		
		//allSubstitutions is a list of all substitutions that are found, which was passed by reference (so you use it build the list of substitutions)
		//substitution is the one we are currently building recursively.
		//conditions is the list of conditions you  still need to find a substitution for (this list shrinks the further you get in the recursion).		
		//facts is the list of predicates you need to match against (find substitutions so that a predicate from the conditions unifies with a fact)
		
		
		// Base case:
		if (conditions.isEmpty()) {
			allSubstitutions.add(substitution);
			return true;
		}
		
		HashMap <String, String> temp_sub = new HashMap <String, String>();
		Boolean found = false; // flag for if a substitution is found
		
		// Try to unify the leading condition to a fact
		for (String fact_key : facts.keySet()) {
			temp_sub = unifiesWith(conditions.elementAt(0), facts.get(fact_key));
			if (temp_sub == null) {
				continue;
			}
			else { // If unification is found...
				substitution.putAll(temp_sub);
				Vector<Predicate> conditions_copy = new Vector<Predicate>(conditions);
				Predicate conditions_check = conditions_copy.remove(0); // Remove condition from copy of conditions
				Predicate temp = substitute(conditions_copy.remove(0), substitution); //this remembers the variables of the checked condition
				// Recursive call with reduced conditions:
				if (findAllSubstitions(allSubstitutions, substitution, conditions_copy, facts)) {
					if (temp.not) { //check if the condition is != (X,Y)
						if (temp.not()) { //check if that's still the case after the substitution
							conditions_copy.add(0, conditions_check); //abort the removing of the element
						}
					}
					if (temp.eql) { //check if the condition is = (X,Y)
						if (temp.eql()) {
							conditions_copy.add(0, conditions_check);
						}
					}
					else {
						found = true;
					}
				}
				substitution.clear(); // Clear the hashmap substitution when starting to look for new substitution
			}
		}		
		return found;
	}

	@Override
	public HashMap<String, String> unifiesWith(Predicate p, Predicate f) {
		//Returns the valid substitution for which p predicate unifies with f
		//You may assume that Predicate f is fully bound (i.e., it has no variables anymore)
		//The result can be an empty substitution, if no subst is needed to unify p with f (e.g., if p and f contain the same constants or do not have any terms)
		//Please note because f is bound and p potentially contains the variables, unifiesWith is NOT symmetrical
		//So: unifiesWith("human(X)","human(joost)") returns X=joost, while unifiesWith("human(joost)","human(X)") returns null 
		//If no subst is found it returns null
		//If the predicate doesn't have the same amount of terms or it isn't the same predicate
		//then there's no unification possible
		if (p.getTerms().size() != f.getTerms().size() || p.getName() != f.getName()) { 
			return null;
		}
		
		HashMap<String, String> substitutions = new HashMap<String, String>();
		
		for (int i=0; i<p.getTerms().size(); i++) { // for all terms in predicate p:...
			if (p.getTerm(i).var) { // if the term is a variable...
				substitutions.put(p.getTerm(i).toString(), f.getTerm(i).toString()); 
			}
		}
		//predicate p has to be equal to predicate f before the substitution is really done
		if (substitute(p, substitutions).toString().equals(f.toString())) { 
			return substitutions;
		} 
		return null;
	}

	@Override
	public Predicate substitute(Predicate old, HashMap<String, String> s) {
		//Substitutes all variable terms in predicate <old> for values in substitution <s>
		//(only if a key is present in s matching the variable name of course)
		//Use Term.substitute(s)
		
		for (Term t : old.getTerms()) {
			t.substitute(s);
		}
		return old;
	}

	@Override
	public Plan idSearch(int maxDepth, KB kb, Predicate goal) {
		//The main iterative deepening loop
		//Returns a plan, when the depthFirst call returns a plan for depth d.
		//Ends at maxDepth
		//Predicate goal is the goal predicate to find a plan for.
		//Return null if no plan is found.

		for (int depth = 1; depth <= maxDepth; depth++) { //looping over over all depths to apply the dfs depth level per depth level
			Plan plan = depthFirst(depth, 0, kb, goal, new Plan());
			if (null != plan) { //returns plan if dfs finds a plan for the goal
				return plan;
			}
		}
		return null; //returns null if no plan is found
	}

	@Override
	public Plan depthFirst(int maxDepth, int depth, KB state, Predicate goal, Plan partialPlan) {
		//Performs a depthFirst search for a plan to get to Predicate goal
		//Is a recursive function, with each call a deeper action in the plan, building up the partialPlan
		//Caps when maxDepth=depth
		//Returns (bubbles back through recursion) the plan when the state entails the goal predicate
		//Returns null if capped or if there are no (more) actions to perform in one node (state)
		//HINT: make use of think() and act() using the local state for the node in the search you are in.
		
		if (depth > maxDepth) {
			return null;  //break condition
		}
	
		if (state.contains(goal)) {
			return partialPlan;  //base case, return solution
		}
	
		for (Sentence action: state.rules()) {//copying state to not overwrite
			
			KB newState = state;//.copy() does not work, a copy should be created here
			think(newState, desires, intentions);  //evaluate with think()
			//act("prison.txt", action, believes, desires);  // Update the new state by acting act(Maze w, Predicate action, KB b, KB d)
	
			//recursion on new state with plan
			Plan newPPlan = partialPlan; //.copy() does not work, a copy should be created here
			newPPlan.add(action);
			Plan result = depthFirst(maxDepth, depth + 1, newState, goal, newPPlan);
	
			if (result != null) {
				return result;  //goal found in recursive call
			}
		}
	
		return null;  //return null if there is no applicable plan
	}
		
}
