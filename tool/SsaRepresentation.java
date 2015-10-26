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
        StringBuilder ssaFormula = new StringBuilder();
            
        /**  variables declarations  **/
        Map<String, Integer> freshMapping = fresh.getAllVariablesMappings();
        for(String variableName : freshMapping.keySet() ) {
            Integer biggestIndex = freshMapping.get(variableName);
            for(int i = 0; i <= biggestIndex; i++) {
                ssaFormula.append("int ").append(variableName).append(i).append("; \n");
            }
        }
            
        ssaFormula.append("\n");
            
        /**   assignments - MUST use prefix operators **/
        for(Assignment assignment : this.getAssignments()) {
            ssaFormula.append(assignment.variableName).append(" = ");
            ssaFormula.append(assignment.expression.toString()).append("; \n");
        }
            
        ssaFormula.append("\n");
            
        /**  assertions **/
        for(Assertion assertion : this.getAssertions()) {
            ssaFormula.append("assert ( ");
            ssaFormula.append(assertion.expression.toString());
            ssaFormula.append(" ); \n");
        }
            
        return ssaFormula.toString();
    }
    
    public String translateToPseudoSmt(FreshStructure fresh){
        StringBuilder pseudoSMT = new StringBuilder();
        
        /**   assignments - MUST use prefix operators **/
        for(Assignment assignment : this.getAssignments()) {
            pseudoSMT.append("(").append(assignment.variableName).append(" == ");
            pseudoSMT.append(assignment.expression.toString()).append(") && \n");
        }
        pseudoSMT.append("\n");
            
        /**  assertions **/
        pseudoSMT.append(" !( \n");
        for(Assertion assertion : this.getAssertions()) {
            pseudoSMT.append("\t ( ");
            pseudoSMT.append(assertion.expression.toString());
            pseudoSMT.append(" ) ");
            pseudoSMT.append(" && \n");
        }
        pseudoSMT.append(" ) ");
        
        return pseudoSMT.toString();
    }
    
    public String translateToSmtFormula(FreshStructure fresh) {
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
            
        /**  assertions - MUST use prefix operators**/
        
        return smtFormula.toString();
    }
    
}
