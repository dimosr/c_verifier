package util.statement;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import util.expressions.Expression;
import util.program.Program;

public class AssumeStatement extends Statement {
    public Expression expression;
    
    public AssumeStatement(Expression expression) {
        this.expression = expression;
    }
    
    public StatementType getType() {
        return StatementType.ASSUME;
    }
    
    public Set<String> getModifiedSet(Program program, List<String> localVariables) {
        return new HashSet();
    }
}
