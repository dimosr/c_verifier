package tool;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import util.assertions.Assertion;
import util.assignments.Assignment;

public class SsaRepresentation {
    
    private List<Assignment> assignments;
    private List<Assertion> assertions;
    
    public SsaRepresentation() {
        assignments = new ArrayList();
        assertions = new ArrayList();
    }
    
    public void addAssertion(Assertion assertion) {
        assertions.add(assertion);
    }
    
    public void addAssignment(Assignment assignment) {
        assignments.add(assignment);
    }
    
    public List<Assignment> getAssignments(){
        return assignments;
    }
    
    public List<Assertion> getAssertions(){
        return assertions;
    }
    
    public String getText(FreshStructure fresh) {
        StringBuilder smtFormula = new StringBuilder();
            
        /**  variables declarations  **/
        Map<String, Integer> freshMapping = fresh.getAllVariablesMappings();
        for(String variableName : freshMapping.keySet() ) {
            for(int i = 0; i <= freshMapping.get(variableName); i++) {
                int index = freshMapping.get(variableName);
                smtFormula.append("int ").append(variableName).append(index).append("; \n");
            }
        }
            
        smtFormula.append("\n");
            
        /**   assignments - MUST use prefix operators **/
        for(Assignment assignment : this.getAssignments()) {
            smtFormula.append(" ( ").append(assignment.variableName).append(" == ");
            smtFormula.append(assignment.expression.toString());
            smtFormula.append(" ) ");
            smtFormula.append(" && ");
        }
            
        smtFormula.append("\n");
            
        /**  assertions **/
        for(Assertion assertion : this.getAssertions()) {
            smtFormula.append("assert ( ");
            smtFormula.append(assertion.expression.toString());
            smtFormula.append(" ); \n");
        }
        smtFormula.append(" ) ");
            
        return smtFormula.toString();
    }
    
    public String translateToSmt(FreshStructure fresh){
        StringBuilder smtFormula = new StringBuilder();
        
        /**  variables declarations  **/
        Map<String, Integer> freshMapping = fresh.getAllVariablesMappings();
        for(String variableName : freshMapping.keySet() ) {
            for(int i = 0; i <= freshMapping.get(variableName); i++) {
                int index = freshMapping.get(variableName);
                smtFormula.append("(declare-fun ").append(variableName).append(index).append(" () (_ BitVec 32)) \n");
            }
        }
        
        smtFormula.append("\n");
        
        /**   assignments - MUST use prefix operators **/
        
        smtFormula.append("\n");
            
        /**  assertions **/
        smtFormula.append(" !( ");
        for(Assertion assertion : this.getAssertions()) {
            smtFormula.append(" ( ");
            smtFormula.append(assertion.expression.toString());
            smtFormula.append(" ) ");
            smtFormula.append(" && ");
        }
        smtFormula.append(" ) ");
        
        return smtFormula.toString();
    }
    
}
