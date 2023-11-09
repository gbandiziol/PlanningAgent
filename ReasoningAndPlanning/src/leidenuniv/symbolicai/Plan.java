package leidenuniv.symbolicai;

import java.util.Vector;

import leidenuniv.symbolicai.logic.Predicate;
import leidenuniv.symbolicai.logic.Sentence;

public class Plan extends Vector<Predicate>{
	//Helper class to define a plan as a vector of predicates
	public Plan() {
		super();
	}
	public Plan(Plan p) {
		super(p);
	}
	public void add(Sentence s) {
		add(new Predicate(s.toString()));
	}
}
