package util.expressions;

import java.util.ArrayList;
import java.util.List;
import tool.VariablesMapping;
import util.misc.Tuple;

public class TernaryExpression extends Expression {
    
    public Expression condExpr;
    public Expression ifExpr;
    public Expression elseExpr;
    
    public TernaryExpression(Expression leftExpr, Expression ifExpr, Expression elseExpr) {
        this.condExpr = leftExpr;
        this.ifExpr = ifExpr;
        this.elseExpr = elseExpr;
    }
    
    public ExpressionType getType() {
        return ExpressionType.TERNARY;
    }
    
    public Expression applyMappings(VariablesMapping mapping, boolean inSummarisation, Expression result) {
        Expression condEval = condExpr.applyMappings(mapping, inSummarisation, result);
        Expression ifEval = ifExpr.applyMappings(mapping, inSummarisation, result);
        Expression elseEval = elseExpr.applyMappings(mapping, inSummarisation, result);
        return new TernaryExpression(condEval, ifEval, elseEval);
    }
}
