package util.statement;

import java.util.HashSet;
import java.util.Set;
import util.expressions.Expression;


public class AssertStatement extends Statement {
    public Expression expression;
    
    public AssertStatement(Expression expression) {
        this.expression = expression;
    }
    
    public StatementType getType() {
        return StatementType.ASSERT;
    }
    
    public Set<String> getModifiedSet() {
        return new HashSet();
    }
}
