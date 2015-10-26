package util.expressions;

import java.util.ArrayList;
import java.util.List;
import util.misc.Tuple;

public class TernaryExpression extends Expression {
    
    public Expression conditionalExpression;
    public List<Tuple<Expression, Expression>> remainingExpr;
    
    public TernaryExpression(Expression conditionalExpression) {
        this.conditionalExpression = conditionalExpression;
        this.remainingExpr = new ArrayList<Tuple<Expression, Expression>>();
    }
    
    public void addRemainingExpr(Tuple<Expression, Expression> newTuple) {
        remainingExpr.add(newTuple);
    }
    
    public ExpressionType getType() {
        return ExpressionType.TERNARY;
    }
}
