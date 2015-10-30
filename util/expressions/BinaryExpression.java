package util.expressions;

import java.util.ArrayList;
import java.util.List;
import util.misc.Tuple;
import util.operators.BinaryOperator;

public class BinaryExpression extends Expression {
    
    public Expression leftExpr;
    public BinaryOperator operator;
    public Expression rightExpr;
    
    public BinaryExpression(Expression left, BinaryOperator operator, Expression right) {
        this.leftExpr = left;
        this.operator = operator;
        this.rightExpr = right;
    }
            
    public ExpressionType getType() {
        return ExpressionType.BINARY;
    }
}
