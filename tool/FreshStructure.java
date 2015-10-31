package tool;

import java.util.HashMap;
import java.util.Map;

public class FreshStructure {
    private Map<String, Integer> localFreshMap;
    private Map<String, Integer> globalFreshMap;
    
    public FreshStructure() {
        localFreshMap = new HashMap<String, Integer>();
        globalFreshMap = new HashMap<String, Integer>();
    }
    
    public int fresh(String variableName) {
        int nextIndex = -100;
        if(localFreshMap.containsKey(variableName)) {
            nextIndex = localFreshMap.get(variableName);
            localFreshMap.put(variableName, nextIndex+1);
        }
        else if(globalFreshMap.containsKey(variableName)) {
            nextIndex = globalFreshMap.get(variableName);
            globalFreshMap.put(variableName, nextIndex+1);
        }
        return nextIndex+1;
    }
    
    public void addNewLocal(String variableName) {
        localFreshMap.put(variableName, 0);
    }
    
    public void addNewGlobal(String variableName) {
        globalFreshMap.put(variableName, 0);
    }
    
    public Map<String, Integer> getAllLocalMappings(){
        return localFreshMap;
    }
    
    public Map<String, Integer> getAllGlobalMappings(){
        return globalFreshMap;
    }
}
