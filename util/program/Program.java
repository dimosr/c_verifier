package util.program;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;


public class Program {
    public Set<String> globalVariables;
    public Map<String, Procedure> procedures;
    
    public Program(Set<String> globalVariables, Map<String, Procedure> procedures) {
        this.globalVariables = globalVariables;
        this.procedures = procedures; 
    }
    
    public void calculateAllModSets() {
        boolean modSetsFinalised;
        do {
            modSetsFinalised = true;
            for(Procedure procedure : procedures.values()) {
                Set<String> previousModSet = procedure.modifiedSet;
                Set<String> updatedModSet = procedure.getModifiedSet(this);
                if(updatedModSet.size() > previousModSet.size()) {
                    procedure.modifiedSet = updatedModSet;
                    modSetsFinalised = false;
                }
            }
        } while(!modSetsFinalised);
    }
}
