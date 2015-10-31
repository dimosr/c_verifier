package tool;

import java.util.HashSet;
import java.util.Set;

public class ModifiedSet {
    private Set<String> localModSet;
    private Set<String> globalModSet;
    
    public ModifiedSet() {
        localModSet = new HashSet<String>();
        globalModSet = new HashSet<String>();
    }
    
    public void addLocal(String variableName) {
        localModSet.add(variableName);
    }
    
    public void addGlobal(String variableName) {
        globalModSet.add(variableName);
    }
    
    public Set<String> getLocalsModified() {
        return localModSet;
    }
    
    public Set<String> getGlobalsModified() {
        return globalModSet;
    }
    
    public ModifiedSet union(ModifiedSet set) {
        if(set == null) {
            return this;
        }
        Set<String> locals1 = this.getLocalsModified();
        Set<String> globals1 = this.getGlobalsModified();
        
        Set<String> locals2 = set.getLocalsModified();
        Set<String> globals2 = set.getGlobalsModified();
        
        ModifiedSet union = new ModifiedSet();
        
        for(String variable : locals1)
            union.addLocal(variable);
        for(String variable : locals2)
            union.addLocal(variable);
        
        for(String globalVar : globals1)
            union.addGlobal(globalVar);
        for(String globalVar : globals2)
            union.addGlobal(globalVar);
        
        return union;
    }
    
}
