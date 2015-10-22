package util.assertions;

import util.conditions.Condition;
import util.expressions.Expression;

public class Assertion {
    public Expression expression;
    
    public Assertion(Expression expression) {
        this.expression = expression;
    }
}
