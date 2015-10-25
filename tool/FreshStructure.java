package tool;

import java.util.HashMap;
import java.util.Map;

public class FreshStructure {
    private Map<String, Integer> freshMap;
    
    public FreshStructure() {
        freshMap = new HashMap<String, Integer>();
    }
    
    public int fresh(String variableName) {
        int nextIndex = freshMap.get(variableName);
        freshMap.put(variableName, nextIndex+1);
        return nextIndex+1;
    }
    
    public void addNewVar(String variableName) {
        freshMap.put(variableName, 0);
    }
    
    public Map<String, Integer> getAllVariablesMappings(){
        return freshMap;
    }
}
