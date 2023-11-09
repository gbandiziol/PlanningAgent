package leidenuniv.symbolicai.logic;

import java.io.File;
import java.io.RandomAccessFile;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Vector;

public class KB {
	private Vector<Sentence> rules;
	private HashMap<String,Sentence> hash;
	
	public KB() {
		//create an empty KB
		rules=new Vector<Sentence>();
		hash=new HashMap<String,Sentence>();
	}
	
	public KB(File file) {
		//Reads a KB from a file
		rules=new Vector<Sentence>();
		hash=new HashMap<String,Sentence>();
		try {
			RandomAccessFile r=new RandomAccessFile(file, "r");
			System.out.println("Reading KB from "+file);
			String line=r.readLine();
			while (line!=null) {
				line=line.trim();
				if (!line.startsWith("#") && line.length()>0) {
					//only parse non-empty, non-comment lines
					Sentence temp=new Sentence(line);
					add(temp);
					System.out.println("Read sentence: "+temp);
					
				}
				line=r.readLine();
			}
			
		} catch (Exception e) {
			System.out.println("Error reading KB "+file);
			e.printStackTrace();
			System.exit(0);
		}
		System.out.println("Ready reading KB.");
	}
	public KB(Collection<Predicate> preds) {
		rules=new Vector<Sentence>();
		hash=new HashMap<String,Sentence>();
		for (Predicate p: preds) {
			add(new Sentence(p.toString()));
		}
	}
	public void add(Sentence r) {
		//Adds a sentence to the KB, if it is not already present (the HashMap is just there do to this fast, you coudl also look it up in the Vector rules).
		//Present means: Stringwise equal, i.e., if r unifies with KB without the need for any substitution, it is not added again 
		if (hash.containsKey(r.toString()))
			return;
		rules.add(r);
		hash.put(r.toString(), r);
	}
	public void del(Sentence r) {
		Sentence d=hash.remove(r.toString());
		if (d!=null)
			rules.remove(d);
		
	}
	public Vector<Sentence> rules(){
		return rules;
	}
	public Sentence get(int i) {
		return rules.get(i);
	}
	public boolean contains(Predicate p) {
		//returns true if the exact predicate is in the knowledge base
		return hash.containsKey(p.toString());
	}
	public boolean contains(Sentence s) {
		//returns true if the exact sentence is in the knowledge base
		return hash.containsKey(s.toString());
	}
	public KB union(KB kb1) {
		//Returns the union of this KB and kb1 as a new KB (containing refs(!) to the sentences in the two originals).
		//Refs means that whatever you do to the result set will not affect kb1 or rules, however, anything you do to the members of result
		//set will affect that member in other sets.
		KB union=new KB();
		for (Sentence s: rules)
			union.add(s);
		for (Sentence s: kb1.rules)
			union.add(s);
		return union;
	}
	
	public String toString() {
		//Returns this KB as a string, used for printing.
		String result="";
		for (Sentence s: rules)
			result+=s+"\n";
		return result;
	}
}
