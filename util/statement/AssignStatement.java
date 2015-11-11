package util.statement;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import util.expressions.Expression;
import util.program.Program;

public class AssignStatement extends Statement {
    public String variable;
    public Expression rightHandSideExpr;
    
    public AssignStatement(String variable, Expression expression) {
        this.variable = variable;
        this.rightHandSideExpr = expression;
    }
    
    public StatementType getType() {
        return StatementType.ASSIGN;
    }
    
    public Set<String> getModifiedSet(Program program, List<String> localVariables) {
        Set<String> modSet = new HashSet();
        modSet.add(variable);
        return modSet;
    }
}
