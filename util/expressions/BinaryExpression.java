package util.expressions;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
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
    
    public Expression applyMappings(VariablesMapping mapping, Expression result) {
        Expression leftEval = leftExpr.applyMappings(mapping, result);
        Expression rightEval = rightExpr.applyMappings(mapping, result);
        
        return new BinaryExpression(leftEval, operator, rightEval);
    }
    
    public Expression applySummarisationMappings(VariablesMapping mapping, Map<String, Expression> parametersMapping, Expression resultExpr) {
        Expression leftSummarised = leftExpr.applySummarisationMappings(mapping, parametersMapping, resultExpr);
        Expression rightSummarised = rightExpr.applySummarisationMappings(mapping, parametersMapping, resultExpr);
        
        return new BinaryExpression(leftSummarised, operator, rightSummarised);
    }
}
