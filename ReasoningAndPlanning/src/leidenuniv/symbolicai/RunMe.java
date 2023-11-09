package leidenuniv.symbolicai;

import java.io.File;
import java.util.Scanner;

import leidenuniv.symbolicai.environment.Maze;

public class RunMe {
	//This is our main program class
	// It loads a world, makes an agent and then keeps the agent alive by allowing it to complete it's sense think act cycle 
	public static void main(String[] args) {
		//Load a world
		Maze w=new Maze(new File("data/prison.txt"));
		//Create an agent
		Agent a=new MyAgent();
		a.HUMAN_DECISION=false;
		a.VERBOSE=true;
		//Load the rules and static knowledge for the different steps in the agent cycle
		a.loadKnowledgeBase("percepts", new File("data/percepts.txt"));
		a.loadKnowledgeBase("program", new File("data/program.txt"));
		a.loadKnowledgeBase("actions", new File("data/actions.txt"));
		
		
		//If you need to test on a simpler file, you may use this one and comment out all the other KBs:
		//a.loadKnowledgeBase("program", new File("data/family.txt"));
		
		
		Scanner io= new Scanner(System.in);
		
		while (true) {
			//have the agent run the sense-think-act loop.
			a.cycle(w);
			
			//wait for an enter 
			System.out.println("Press <enter> in the java console to continue next cycle");
			String input = io.nextLine();
			
		}
	}

}
