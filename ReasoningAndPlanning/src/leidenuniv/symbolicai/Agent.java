package leidenuniv.symbolicai;
import java.io.File;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Scanner;
import java.util.Vector;

import leidenuniv.symbolicai.environment.Maze;
import leidenuniv.symbolicai.logic.KB;
import leidenuniv.symbolicai.logic.Predicate;
import leidenuniv.symbolicai.logic.Sentence;
import leidenuniv.symbolicai.logic.Term;

public abstract class Agent {
	KB perceptRules,programRules,actionRules; //these are the static rules you get from loading your program
	KB believes,desires, intentions;//these are dynamic facts, believes are facts, intentions are actions that are possible, desires are goal predicates
	boolean HUMAN_DECISION=false;//change to false if you want the decide step to make the decision rather than you (check code there)
	//boolean HUMAN_DECISION=true;//change to false if you want the decide step to make the decision rather than you (check code there)
	//boolean DEBUG=true;
	boolean PLAN=true;
	boolean DEBUG=false;
	boolean VERBOSE=false;
	
	public Agent() {
		believes=new KB();
		intentions=new KB();
		desires=new KB();
		perceptRules=new KB();
		programRules=new KB();
		actionRules=new KB();
	}
	public void loadKnowledgeBase(String type, File f) {
		switch (type) {
			case "program":programRules= new KB(f);break;
			case "percepts":perceptRules= new KB(f);break;
			case "actions":actionRules= new KB(f);break;
		}
	}
	public void cycle(Maze w) {
		intentions=new KB(); //clear the list of intentions (=possible actions), as we start a cycle
		sense(w);
		think(believes,desires,intentions);
		act(w, decide(HUMAN_DECISION), believes, desires);
	}
	public void sense(Maze w) {
		//The world generates percepts for you every cycle
		//These are local percepts, hence: what you see is what you get :-)
		//Percepts are returned to you in the form of a KB
		//In the percept phase, your run your forward chaining algorithm on the union of the percept rules, the percepts and the believes 
		//Forward chain returns you ALL deduced predicates, including actions, additions, deletions and predicates
		//You process this list using Agent.processFacts()
		KB percepts=w.generatePercepts();
		if (DEBUG) System.out.println("PERCEPTS:\n"+percepts);
		KB result=forwardChain(perceptRules.union(percepts).union(believes)); 
		if (DEBUG) System.out.println("PERCEPT INFERENCE:\n"+result);//uncomment this if you want to know what facts your forward chaining inference produces
		processFacts(result, believes, desires, intentions);
	}
	public void think(KB b, KB d, KB i) {
		//In the think phase, your forward chaining algorithm runs on 
		//the union of the believes (given by b) and the program rules 
		//Forward chain returns you ALL deduced facts, including actions, additions, deletions and predicates
		//You process this list using Agent.processFacts(b,d,i). with b d i the KB's to update.
		//IMPORTANT: b d and i are changed as they are passed by reference.
		//IMPORTANT: the reason think has b d and i as parameters is so that you can make clever use of think() when you implement planning later.
		KB facts=forwardChain(programRules.union(b)); 
		if (DEBUG) System.out.println("THINK INFERENCE:\n"+facts);//uncomment this if you want to know what facts your forward chaining inference produces
		processFacts(facts, b, d, i);
	}
	public Predicate decide(boolean humanActor) {
		//Returns an action (so this method solves the action selection problem).
		//This method selects an action from the collection of action predicates in the agent's intentions KB
		//If humanActor=true, you should pick the action by typing a number.
		//If false the agent selects one using the planner you have to develop later.
		//To test what happens, you can play the agent choosing an action by typing in the action nr (1...n) in the Eclipse console.
		
		if (humanActor) {
			if (intentions.rules().size()<=0) {
				System.out.println("Warning: No actions");
				return null;
			}
			Scanner io= new Scanner(System.in);
			//Show the active intentions to the user
			System.out.println("INTENTIONS (type 1,2,... <enter> to select one):");
			System.out.println(intentions);
			//Input your own action (use this first for testing)
			String input = io.nextLine();
			try {//Return the selected action.
				return new Predicate(intentions.get(Integer.parseInt(input)-1));
			} catch (Exception e) {//return null cause the action selection failed
				System.out.println("Warning: action out of range" + input);
			}
			io.close();
			return null;		
			
		} else {
			Predicate action=null;
			if (PLAN) {
				if (VERBOSE) System.out.println("Planning");
				//First make a plan for each desire
				Vector<Plan> plans=new Vector<Plan>();
				for (Sentence d: desires.rules()) {
					Plan plan=idSearch(7,believes,new Predicate(d));//calls your iterative deepening search to find a okan for Predicate d, keep at 7 maxDepth, you don't need more
					if (VERBOSE) System.out.println("PLAN FOR:"+d+"\n" + plan);
					
					if (plan!=null && plan.size()>0) {
						plans.add(plan);
					}
				}
				//If there are plans, return the first plan action
				if (plans.size()>0)
					action = plans.get(0).get(0);
			}
			else if (action==null && intentions.rules().size()>0)//otherwise, return a random action from the set of intentions
			{	if (VERBOSE) System.out.println("No plan: random action selection from intentions");
				action= new Predicate(intentions.get((int)(Math.random()*(double)intentions.rules().size())));
			}
			else
			{
				System.out.println("Warning: No actions");
			}
			
			return action;
		}
	}
	public void act(Maze w, Predicate action, KB b, KB d) {
		//This method executes the action in the world, or simulates the action (w=null).
		//The actual action execution does not need to be implemented, this has been done already in World.
		//If successful (or if we simulate), it processes the action rules, so that action postconditions can be evaluated
		//IMPORTANT: b and d are changed by processFacts as they are passed by reference.
		//The reason you can switch between a real world or just mental simulation is so that you can use act() cleverly in your planner later
		try {
			if (VERBOSE) System.out.println("Trying action: "+action);
			
			
			if (action!=null && (w==null || w.executeAction(action))) {
				//Executed the action (or assume simulation), if successful process potential action post condition rules
				KB actionKB=new KB();
				actionKB.add(new Sentence(action.toString()));
				KB facts=forwardChain(actionRules.union(actionKB).union(b)); 
				if (DEBUG) System.out.println("ACTION INFERENCE:\n"+facts);//uncomment this if you want to know what facts your forward chaining inference produces
				processFacts(facts,b,d,null);
			} else {
				//action failed do nothing.
				System.out.println("Warning: action execution failed " + action);
			}
		} catch (Exception e) {

			System.out.println("Warning: action failed due to exception" + action);
		}
	}
	
	public void processFacts(KB facts, KB b, KB d, KB i) {
		//Processes the addition, deletion, action and goal predicates on the knowledge bases b,d,i (remove the -+ prefix)
		//It adds them to the appropriate knowledge basis (believes, desires, intentions) 
		//If b, d or i == null then ignore those facts
		if (facts!=null) {
			for (Sentence s: facts.rules())
			{	Predicate p=s.conclusions.elementAt(0);
				Sentence p_fact=new Sentence(p.toString().substring(1));//remove the operator
				if (p.add & b!=null) {
					b.add(p_fact);
					if (DEBUG) System.out.println("Asserting fact "+p);
					if (d!=null && d.contains(p_fact)) {//if the fact we add is also a desire, remove the desire!!
						d.del(p_fact);
						if (DEBUG) System.out.println("Dropping goal "+p);
					}
				} else 	if (p.del & b!=null) {
					b.del(p_fact);
					if (DEBUG) System.out.println("Retracting fact "+p);
				} else if (p.act & i!=null) {
					i.add(p_fact);
					if (DEBUG) System.out.println("Adding intention "+p);
				} else if (p.adopt & d!=null &!b.contains(p_fact)) {//only adopt a goal if the belief base does not contain it yet
					d.add(p_fact);
					if (DEBUG) System.out.println("Adopting goal "+p);
				} else if (p.drop & d!=null) {
					d.del(p_fact);
					if (DEBUG) System.out.println("Dropping goal "+p);
				}
			}
		}
	}
	public abstract KB forwardChain(KB kb);
	//This method should perform forward chaining on the kb given as argument, until no new facts can be added to the KB.
	//You start with an empty collection of facts. When ready, it returns a new KB of ground facts (bounded).
	//The resulting KB includes all deduced predicates, including operators (adding/removing intentions, facts and goals).
	//These are then processed by processFacts() (which is already implemented for you)
	//HINT: You should assume that forwardChain only allows *bound* predicates (i.e. without free variables) to be added to the facts list for now.
	
	public abstract boolean findAllSubstitions(Collection<HashMap<String,String>> allSubstitutions, HashMap<String,String> substitution, Vector<Predicate> conditions, HashMap<String,Predicate> facts);
	//Recursive method to find *all* valid substitutions for a vector of conditions for *one* rule, given a collection of facts
	//The recursion is over Vector<Predicate> conditions (so this vector gets shorter and shorter, the further you are with finding a substitution)
	//It returns true if at least one substitution is found (can be the empty substitution, if nothing needs to be substituted to unify the conditions with the facts)
	//<allSubstitutions> is a collection of all substitutions that are found, which is passed by reference.
	//Every time you find a valid substitution you add it to this collection. 
	//<substitution> is the one we are currently building recursively.
	//<conditions> is the remaining list of conditions for one rule you still need to find a subst for (this list shrinks the further you get in the recursion).
	//<facts> is your database of facts, the list of predicates you need to match against (find substitutions so that a predicate form the conditions unifies with a fact)
			
	public abstract HashMap<String, String> unifiesWith(Predicate p, Predicate f);
	//Returns the substitution for which p predicate unifies with f, or null when there us no such substitution
	//You may assume that Predicate f is fully bound (i.e., it has no variables anymore)
	//The result can be an empty substitution object, if no subst is needed to unify p with f (e.g., if p and f contain the same constants or do not have any terms)
	//Please note that because f is bound and p potentially contains the variables, unifiesWith is NOT symmetrical
	//For example: unifiesWith(new Predicate("human(X)"),new Predicate("human(joost))") returns X=joost, while unifiesWith(new Predicate("human(joost)"),new Predicate("human(X)")) returns null 
	
	public abstract Predicate substitute(Predicate old, HashMap<String, String> s);
	//Returns a copy of <old> in which all variable terms in predicate <old> are substituted for values 
	//according to the substitution <s> (only if a key is present in s matching the variable name in of course)
	//Use Term.substitute(s)
	
	public abstract Plan idSearch(int maxDepth, KB kb, Predicate goal);
	//Predicate <goal> is the goal predicate to find a plan for.
	//The iterative deepening loop tries to build depthFirst plans of depth d=1..maxDepth
	//It returns a plan, when the depthFirst call returns a plan for depth d.
	//Returns null if no plan is found at maxDepth
			
	public abstract Plan depthFirst(int maxDepth, int depth, KB state, Predicate goal, Plan partialPlan);
	//Performs a depthFirst search for a plan to make Predicate <goal> true (i.e., entailed by the state)
	//Is a recursive function, with each call a deeper action in the plan, building up the partialPlan
	//Caps when maxDepth=depth
	//Returns (bubbles back through recursion) the plan when the state entails the goal predicate
	//Returns null if capped or if there are no (more) actions to perform in one node (state)
	//HINT: make use of think() and act() using the local state for the node in the search you are in.
	
	
}
