package util.expressions;

import java.util.ArrayList;
import java.util.List;
import util.misc.Tuple;
import util.operators.BinaryOperator;

public class BinaryExpression extends Expression {
    
    public Expression leftExpr;
    public List<Tuple<BinaryOperator, Expression>> remainingExpr;
    
    public BinaryExpression(Expression leftExpr) {
        this.leftExpr = leftExpr;
        this.remainingExpr = new ArrayList<Tuple<BinaryOperator, Expression>>();
    }
    
    public void addRemainingExpr(Tuple<BinaryOperator, Expression> newTuple) {
        this.remainingExpr.add(newTuple);
    }
            
    public ExpressionType getType() {
        return ExpressionType.BINARY;
    }
}
