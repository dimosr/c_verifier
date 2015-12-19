/**
 *  Copyright 2016 by Dimos Raptis <raptis.dimos@yahoo.gr>
 *  Licensed under GNU General Public License 2.0 or later. 
 *  Some rights reserved. See LICENSE.
 *
 *  @license GPL-2.0 <http://spdx.org/licenses/GPL-2.0.html>
 */

package tool.verif.structs;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public class VariablesMapping {
    private Map<String, Integer> localMapping;
    private Map<String, Integer> globalMapping;
    private Map<String, Integer> shadowedVariables;         //store old indexes for shadowing
    private Set<String> locallyScoped;                      //flag locally scoped variables - to discard them
    
    
    public VariablesMapping() {
        localMapping = new HashMap<String, Integer>();
        globalMapping = new HashMap<String, Integer>();
        shadowedVariables = new HashMap<String, Integer>();
        locallyScoped = new HashSet<String>();
    }
    
    private VariablesMapping(Map<String, Integer> localMapping, Map<String, Integer>globalMapping) {
        this.localMapping = localMapping;
        this.globalMapping = globalMapping;
        this.shadowedVariables = new HashMap<String, Integer>();
        this.locallyScoped = new HashSet<String>();
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
    
    public void addLocallyScopedVar(String variableName) {
        locallyScoped.add(variableName);
    }
    
    public boolean isLocallyScopedVar(String variableName) {
        return locallyScoped.contains(variableName);
    }
    
    public void addShadowedPreviousIndex(String variableName, int index) {
        shadowedVariables.put(variableName, index);
    }
    
    public boolean isShadowed(String variableName) {
        return shadowedVariables.containsKey(variableName);
    }
    
    public int getIndexBeforeShadowing(String variableName) {
        return shadowedVariables.get(variableName);
    }
}
