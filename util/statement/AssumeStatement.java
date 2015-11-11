package util.statement;

import java.util.HashSet;
import java.util.Set;
import util.expressions.Expression;

public class AssumeStatement extends Statement {
    public Expression expression;
    
    public AssumeStatement(Expression expression) {
        this.expression = expression;
    }
    
    public StatementType getType() {
        return StatementType.ASSUME;
    }
    
    public Set<String> getModifiedSet() {
        return new HashSet();
    }
}
