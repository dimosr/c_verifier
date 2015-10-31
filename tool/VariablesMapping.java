package tool;

import java.util.HashMap;
import java.util.Map;

public class VariablesMapping {
    private Map<String, Integer> localMapping;
    private Map<String, Integer> globalMapping;
    
    public VariablesMapping() {
        localMapping = new HashMap<String, Integer>();
        globalMapping = new HashMap<String, Integer>();
    }
    
    private VariablesMapping(Map<String, Integer> localMapping, Map<String, Integer>globalMapping) {
        this.localMapping = localMapping;
        this.globalMapping = globalMapping;
    }
    
    public VariablesMapping deepClone() {
        Map<String, Integer> localMapping = new HashMap<String, Integer>(this.getLocalMapping());
        Map<String, Integer> globalMapping = new HashMap<String, Integer>(this.getGlobalMapping());
        VariablesMapping clonedMapping = new VariablesMapping(localMapping, globalMapping);
        return clonedMapping;
    }
    
    public void addNewLocal(String variable) {
        localMapping.put(variable, 0);
    }
    
    public void addNewGlobal(String variable) {
        globalMapping.put(variable, 0);
    }
    
    public void updateExistingVar(String variable, Integer index) {
        if(localMapping.containsKey(variable)) {
            localMapping.put(variable, index);
        }
        else if(globalMapping.containsKey(variable)) {
            globalMapping.put(variable, index);
        }
    }
    
    public Integer getVarIndex(String variable) {
        Integer varIndex = -100;
        if(isLocal(variable)) {
            varIndex =  localMapping.get(variable);
        }
        else if(isGlobal(variable)) {
            varIndex = globalMapping.get(variable);
        }
        return varIndex;
    }
    
    //just used for \old in call summarization
    public Integer getGlobalIndex(String variable) {
        return globalMapping.get(variable);
    }
    
    public boolean isLocal(String variable) {
        return localMapping.containsKey(variable);
    }
    
    public boolean isGlobal(String variable) {
        return globalMapping.containsKey(variable);
    }
    
    private Map<String, Integer> getLocalMapping() {
        return localMapping;
    }
    
    private Map<String, Integer> getGlobalMapping() {
        return globalMapping;
    }
}
