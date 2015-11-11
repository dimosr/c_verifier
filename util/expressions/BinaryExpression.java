package util.expressions;

import java.util.ArrayList;
import java.util.List;
import tool.VariablesMapping;
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
    
    public Expression applyMappings(VariablesMapping mapping, boolean inSummarisation, Expression result) {
        Expression leftEval = leftExpr.applyMappings(mapping, inSummarisation, result);
        Expression rightEval = rightExpr.applyMappings(mapping, inSummarisation, result);
        
        return new BinaryExpression(leftEval, operator, rightEval);
    }
}
