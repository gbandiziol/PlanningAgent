package leidenuniv.symbolicai.environment;
import java.util.Set;
import java.util.regex.*;

public class Location {
	//The Location class represents one location in the world 
	public String type;	//The type of location (e.g., door, key, etc.., see below)
	int x,y; 			//where it is in the world (just for coding ease)
	
	public Location(String type, int x, int y) {
		//A Location is either walkable (space or any other character) or not (# character for wall)
		this.type=new String(type);
		this.x=x;this.y=y;
	}
	public String toString() {
		//returns this Location as a string (used e.g. for printing and for hashing in hashmaps)
		return x+"_"+y;
	}
	public boolean isWall() {
		//returns true if this is wall
		return type.equals("#");
	}
	public boolean isLocked() {
		//If there is a door token (letters A-Z) then the location is locked
		return Pattern.matches("[A-Z]", type);
	}
	public String whichKey() {
		//returns the key type needed for this lock (the lower case character of the door token)
		if (isLocked())
			return type.toLowerCase();
		else
			return null;
	}
	public boolean isExit() {
		//If this is the exit, the $, return true
		return type.equals("$");
	}
	public boolean isStart() {
		//If this is the exit, the *, return true
		return type.equals("*");
	}
	public String hasKey(){
		//If there is a key here, letter a-z, then the location contains of type <key>
		if (Pattern.matches("[a-z]", type))
			return type.toLowerCase();
		else
			return null;
	}
	
	public boolean grab(String item) {
		//checks if the item is here and removes it from the location then return true.
		if (item.equals(hasKey())) {
			type=" ";
			return true;
		} else
			return false;
	}
	public boolean openLock(Set<String> keys) {
		//checks if we are a locked location, and if the key fits the lock, then remove the lock on this location, return true.
		if (isLocked() && keys.contains(type.toLowerCase())){
			type=" ";
			return true;
		} else
			return false;
	}
}