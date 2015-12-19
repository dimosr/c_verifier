/**
 *  Copyright 2016 by Dimos Raptis <raptis.dimos@yahoo.gr>
 *  Licensed under GNU General Public License 2.0 or later. 
 *  Some rights reserved. See LICENSE.
 *
 *  @license GPL-2.0 <http://spdx.org/licenses/GPL-2.0.html>
 */

package util.program;

import java.util.Map;
import java.util.Set;


public class Program {
    public Set<String> globalVariables;
    public Map<String, Procedure> procedures;
    public Map<String, Set<String>> calledBy;
    public boolean hasLoops;
    
    public Program(Set<String> globalVariables, Map<String, Procedure> procedures, Map<String, Set<String>> calledBy, boolean hasLoops) {
        this.globalVariables = globalVariables;
        this.procedures = procedures; 
        this.calledBy = calledBy;
        this.hasLoops = hasLoops;
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
    
    public boolean hasLoops() {
        return hasLoops;
    }
}
