package leidenuniv.symbolicai.environment;
import java.io.File;
import java.io.RandomAccessFile;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;
import java.util.StringTokenizer;
import java.util.Vector;
import java.util.regex.*;

import leidenuniv.symbolicai.logic.KB;
import leidenuniv.symbolicai.logic.Predicate;
import leidenuniv.symbolicai.logic.Sentence;

public class Maze {
	//A simple maze world in which the agent can execute actions and receive percepts from
	//It mainly consists of a map of locations, with locations containing possible items and doors
	//The agent's coordinates are tracked in the "real world"
	//The inventory is a hashset that contains items you found (so that agent's can't cheat :-) )
	
	private int agentX, agentY;
	private Location[][] locs;
	private HashMap<String,Location> map;
	private HashSet<String> inventory;
	
	public Maze (File file) {
		//Initiates a world from a file and does some world inits and checks for the correctness of the file.
		//You can skip this part unless you want to figure out how to read in from files and do string parsing.
		
		inventory=new HashSet<String>();
		agentX=-1;
		agentY=-1;
		boolean foundExit=false;
		
		try {
			RandomAccessFile r=new RandomAccessFile(file, "r");
			StringTokenizer dims=new StringTokenizer(r.readLine(), " ");
			int w=Integer.parseInt(dims.nextToken());
			int h=Integer.parseInt(dims.nextToken());
			System.out.println("Reading "+w+"x"+h+" world from "+file);
			locs=new Location[h][w];
			map=new HashMap<String,Location>();
			
			HashSet<String> keycheck=new HashSet<String>();
			
			int y=0;
			String line=r.readLine();
			while (line!=null && !line.trim().equals("")) {
				if (y>=h)
				{
					System.out.println("Error reading maze file: nr of rows wrong");
					System.exit(0);
				}
				line=line.trim();
				if (line.length()!=w)
				{
					System.out.println("Error reading maze file: row of wrong length, "+line+" not length "+line.length());
					System.exit(0);
				}
				for (int x=0;x<line.length();x++)
				{	Location loc=new Location(""+line.charAt(x), x, y);
					locs[y][x]=loc;
					map.put(loc.toString(), loc);
					
					if (loc.isStart()) {
						agentX=x;
						agentY=y;
					}
					if (loc.isExit()) {
						foundExit=true;
					}
					if (loc.isLocked()) {//we found a lock
						if (keycheck.contains(loc.whichKey()))//if we found the key, then we are ok and remove the pair
							keycheck.remove(loc.whichKey());
						else//otherwise we add it to our list
							keycheck.add(loc.type);
						
					}
					if (loc.hasKey()!=null)//we found a key
						if (keycheck.contains(loc.hasKey().toUpperCase()))//if we have a lock the we are ok and remove the pair
							keycheck.remove(loc.hasKey().toUpperCase());
						else//otherwise we add the key.
							keycheck.add(loc.hasKey());
				}
				line=r.readLine();
				y++;
				
			}
			if (y!=h)
			{
				System.out.println("Error reading maze file: nr of rows wrong");
				System.exit(0);
			}
			if (!keycheck.isEmpty())
			{
				System.out.println("Error reading maze file:keys and locks dont match for following: "+ keycheck.toString());
				System.exit(0);
			}
		} catch (Exception e) {
			System.out.println("Error reading maze file "+file);
			e.printStackTrace();
			System.exit(0);
		}
		if (agentX==-1)
		{
			System.out.println("Error reading maze file, no start location in "+file);
			System.exit(0);
		}
		if (!foundExit)
		{
			System.out.println("Error reading maze file, no exit in "+file);
			System.exit(0);
		}
		System.out.println("Ready.");
	}
	
	public KB generatePercepts() {
		//generates a series of percepts as sentences in a knowledge base in our simplified first order logic (SFOL) based on the current
		//A percept is a fully instantiated predicate, for example "key(a)", "at(1-1)", "passage(2-1)", "locked(2-1, a)" 
		//meaning that the agent perceives to be at location "1-1", that there is a passage to "2-1",
		//that that location is locked with a door that needs an "a" key, and that such a key is present at the current location
		KB percepts=new KB();
		
		Location loc=locs[agentY][agentX];
		percepts.add(new Sentence("at("+loc.toString()+")"));
		
		if (loc.isExit())
			percepts.add(new Sentence("exit"));
		if (loc.hasKey()!=null)
			percepts.add(new Sentence("key("+loc.hasKey()+")"));
		for (Location l: passages()) {
			if (l.isLocked())//there is a closed door at loc
				percepts.add(new Sentence("locked("+l.type.toLowerCase()+")"));
			else//there is a passge to l
				percepts.add(new Sentence("passage("+l.toString()+")"));
		}
		return percepts;
	}
	
	public boolean executeAction(Predicate action) {
		//executes an action in the world. An action, for the world, is an SFOL predicate
		//The semantics of the predicate must of course be known to the world.
		//For example, "goto(1_1,2_1)" or "grab(2_2,a)" or "open(2_1,a)", or simply "look" to do nothing and wait a cycle (e.g. to get percepts)
		//It returns true if the action was successful, otherwise it returns false.
		boolean success=false;
		try {
			switch(action.getName()) {
				case "goto":success=goTo(map.get(action.getTerm(0).toString()), map.get(action.getTerm(1).toString()));break;
				case "grab":success=grab(map.get(action.getTerm(0).toString()), action.getTerm(1).toString());break;
				case "open":success=open(map.get(action.getTerm(0).toString()), action.getTerm(1).toString());break;
				case "look":success=look();break;
				default: success=false;//we don't know this command hence its a failure
			}
			
		} catch (Exception e) {
			System.out.println("Warning: exception in action execution, return false for "+action);
		}
		return success;
	}
	public boolean goTo(Location from, Location to) {
		//Assumes a valid Location in the world
		//if the location you want to go to is reachable (not a wall), and it is not locked then move the agent.
		if (from.x==agentX && from.y==agentY && passages().contains(to) && !to.isLocked()) {
			agentX=to.x;
			agentY=to.y;
			if (to.isExit()) {
				System.out.println("CONGRATULATIONS! YOU FOUND THE EXIT!");
				System.exit(0);
			}
			return true;
		} else
			return false;
	}
	
	public boolean grab(Location from, String item) {
		//If we successfully grab the item (keys in our case) add it to our inventory
		if (from.x==agentX && from.y==agentY && from.grab(item)) {
			inventory.add(item);
			return true;
		} else
			return false;
	}
	public boolean open(Location loc, String key) {
		//Tries to open all locations adjacent to this one with <key> if <key> in inventory, and agent at loc
		//If nothing can be opened it fails
		boolean result=false;
		if (locs[agentY][agentX]==loc) {
			for (Location l: passages()) {
				result=result|l.openLock(inventory);
			}
		}
		return result;
	}
	public boolean look() {
		//The action that does nothing
		return true;
	}
	public Set<Location> passages() {
		//Helper method to retrieve all possible passages as a Set of locations to travel to.
		Set<Location> result=new HashSet<Location>();
		if (!locs[agentY][agentX-1].isWall()) result.add(locs[agentY][agentX-1]);
		if (!locs[agentY][agentX+1].isWall()) result.add(locs[agentY][agentX+1]);
		if (!locs[agentY-1][agentX].isWall()) result.add(locs[agentY-1][agentX]);
		if (!locs[agentY+1][agentX].isWall()) result.add(locs[agentY+1][agentX]);
		return result;
	}
}
