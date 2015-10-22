package tool;

import java.util.HashMap;
import java.util.Map;

public class FreshStructure {
    private Map<String, Integer> freshSet;
    
    public FreshStructure() {
        freshSet = new HashMap<String, Integer>();
    }
    
    public int fresh(String variableName) {
        int nextIndex = freshSet.get(variableName);
        freshSet.put(variableName, nextIndex+1);
        return nextIndex;
    }
    
    public void addNewVar(String variableName) {
        freshSet.put(variableName, 0);
    }
}
