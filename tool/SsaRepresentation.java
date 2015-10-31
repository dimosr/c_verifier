package tool;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import util.assertions.Assertion;
import util.assignments.Assignment;
import util.expressions.BinaryExpression;
import util.expressions.ConstantExpression;
import util.expressions.Expression;
import util.expressions.ExpressionType;
import util.expressions.ParenthesisExpression;
import util.expressions.TernaryExpression;
import util.expressions.UnaryExpression;
import util.expressions.VarRefExpression;
import util.misc.Tuple;
import util.operators.BinaryOperator;
import util.operators.BinaryOperatorType;
import util.operators.UnaryOperator;
import util.operators.UnaryOperatorType;

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
            ssaFormula.append(getExpressionSsa(assignment.expression)).append("; \n");
        }
            
        ssaFormula.append("\n");
            
        /**  assertions **/
        for(Assertion assertion : this.getAssertions()) {
            ssaFormula.append("assert ( ");
            ssaFormula.append(getExpressionSsa(assertion.expression));
            ssaFormula.append(" ); \n");
        }
            
        return ssaFormula.toString();
    }
    
    public String translateToPseudoSmt(FreshStructure fresh){
        StringBuilder pseudoSMT = new StringBuilder();
        
        /**   assignments - MUST use prefix operators **/
        for(Assignment assignment : this.getAssignments()) {
            pseudoSMT.append("( ").append(assignment.variableName).append(" == ");
            pseudoSMT.append(getExpressionSsa(assignment.expression)).append(") && \n");
        }
        pseudoSMT.append("\n");
            
        /**  assertions **/
        pseudoSMT.append(" !( \n");
        for(Assertion assertion : this.getAssertions()) {
            pseudoSMT.append("\t ( ");
            pseudoSMT.append("(tobool ").append(getExpressionSsa(assertion.expression)).append(" )");
            pseudoSMT.append(" ) ");
            // fix last &&
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
                smtFormula.append("(declare-fun ").append(variableName).append(i).append(" () (_ BitVec 32)) \n");
            }
        }
        
        smtFormula.append("\n");
        
        /**   assignments - MUST use prefix operators **/
      
        for(Assignment assignment : this.getAssignments()) {
            smtFormula.append("(assert (= ")
                      .append(assignment.variableName).append(" ");
            smtFormula.append(getExpressionSMT(assignment.expression)).append("))");
            // fix last &&
                 smtFormula.append(" \n");
        }

        smtFormula.append("\n");
            
        /**  assertions - MUST use prefix operators**/
        smtFormula.append("(assert (not (and \n");
        for(Assertion assertion : this.getAssertions()) { 
            smtFormula.append(getExpressionSMT(assertion.expression));
            smtFormula.append("\n");
        }
        smtFormula.append("\n) ) )");
        
        return smtFormula.toString();
    }
    
    private String getExpressionSsa(Expression expression) {
        StringBuilder ssaFormula = new StringBuilder();
        
        if(expression.getType() == ExpressionType.BINARY){
            BinaryExpression binExpr = (BinaryExpression) expression;
            ssaFormula.append(getExpressionSsa(binExpr.leftExpr)).append(" ");
            ssaFormula.append(binExpr.operator.opType.ssaForm()).append(" ");
            ssaFormula.append(getExpressionSsa(binExpr.rightExpr));
        }
        else if(expression.getType() == ExpressionType.CONSTANT) {
            ConstantExpression constExpr = (ConstantExpression) expression;
            ssaFormula.append(constExpr.intValue);
        }
        else if(expression.getType() == ExpressionType.OLD) {
            // TO DO
        }
        else if(expression.getType() == ExpressionType.PARENTHESIS){
            ParenthesisExpression parenExpr = (ParenthesisExpression) expression;
            ssaFormula.append("( ").append(getExpressionSsa(parenExpr.expr)).append(" )");
        }
        else if(expression.getType() == ExpressionType.TERNARY) {
            TernaryExpression ternaryExpr = (TernaryExpression) expression;
            ssaFormula.append(getExpressionSsa(ternaryExpr.condExpr)).append(" ? ");
            ssaFormula.append(getExpressionSsa(ternaryExpr.ifExpr)).append(" : ");
            ssaFormula.append(getExpressionSsa(ternaryExpr.elseExpr)).append(" ");
            
        }
        else if(expression.getType() == ExpressionType.UNARY) {
            UnaryExpression unaryExpr = (UnaryExpression) expression;
            
            for(UnaryOperator operator : unaryExpr.operators) {
                ssaFormula.append(operator.opType.ssaForm()).append(" ");
            }
            ssaFormula.append(getExpressionSsa(unaryExpr.expr));
        }
        else if(expression.getType() == ExpressionType.VARIABLE_REFERENCE) {
            VarRefExpression varRefExpr = (VarRefExpression) expression;
            ssaFormula.append(varRefExpr.variableName);
        }
        
        return ssaFormula.toString();
    }

    private String getExpressionSMT(Expression expression) {
        StringBuilder smtFormula = new StringBuilder();
        
        if(expression.getType() == ExpressionType.BINARY){
            BinaryExpression binExpr = (BinaryExpression) expression;
            if(binExpr.operator.opType.isNumInputNumOutput()) {
                smtFormula.append("(").append(binExpr.operator.opType.smtForm()).append(" ");
                smtFormula.append(getExpressionSMT(binExpr.leftExpr)).append(" ");
                smtFormula.append(getExpressionSMT(binExpr.rightExpr)).append(")");
            }
            else if(binExpr.operator.opType.isNumInputBoolOutput()){
                smtFormula.append("(tobv32 ");
                
                smtFormula.append("(").append(binExpr.operator.opType.smtForm()).append(" ");
                smtFormula.append(getExpressionSMT(binExpr.leftExpr)).append(" ");
                smtFormula.append(getExpressionSMT(binExpr.rightExpr)).append(" ");
                smtFormula.append(")");
                
                smtFormula.append(")");
            }
            else if(binExpr.operator.opType.isBoolInputBoolOutput()){
                smtFormula.append("(tobv32 ");
                
                smtFormula.append("(").append(binExpr.operator.opType.smtForm()).append(" ");
                
                smtFormula.append("(tobool ");
                smtFormula.append(getExpressionSMT(binExpr.leftExpr));
                smtFormula.append(" )");
                
                smtFormula.append("(tobool ");
                smtFormula.append(getExpressionSMT(binExpr.rightExpr));
                smtFormula.append(" )");
                
                smtFormula.append(") )");
            }
            
        }
        else if(expression.getType() == ExpressionType.CONSTANT) {
            ConstantExpression constExpr = (ConstantExpression) expression;
            smtFormula.append("(_ bv").append(constExpr.intValue).append(" 32)");
        }
        else if(expression.getType() == ExpressionType.OLD) {
            // TO DO
        }
        else if(expression.getType() == ExpressionType.PARENTHESIS){
            ParenthesisExpression parenExpr = (ParenthesisExpression) expression;
            smtFormula.append("( ").append(getExpressionSMT(parenExpr.expr)).append(" )");
        }
        else if(expression.getType() == ExpressionType.TERNARY) {
            TernaryExpression ternExpr = (TernaryExpression) expression;
            smtFormula.append("(ite ").append("(tobool (").append(getExpressionSMT(ternExpr.condExpr)).append(") ) ").append(getExpressionSMT(ternExpr.ifExpr)).append(" ").append(getExpressionSMT(ternExpr.elseExpr)).append(")");
        }
        else if(expression.getType() == ExpressionType.UNARY) {
            UnaryExpression unaryExpr = (UnaryExpression) expression;
            long parenthesesSum = 0;
            
            for(UnaryOperator operator : unaryExpr.operators) {
                if((operator.opType == UnaryOperatorType.PLUS) || (operator.opType == UnaryOperatorType.MINUS)){
                    smtFormula.append("(").append(operator.opType.smtForm());
                    parenthesesSum++;
                }
                else {
                    smtFormula.append("(tobv32 (").append(operator.opType.smtForm()).append(" (tobool ");
                    parenthesesSum += 3;
                }
                smtFormula.append(" ");
            }
            smtFormula.append(getExpressionSMT(unaryExpr.expr));
            for(int i = 0; i < parenthesesSum; i++)
                smtFormula.append(" )");
        }
        else if(expression.getType() == ExpressionType.VARIABLE_REFERENCE) {
            VarRefExpression varRefExpr = (VarRefExpression) expression;
            smtFormula.append(varRefExpr.variableName);
        }
        
        return smtFormula.toString();
    }
    
}
