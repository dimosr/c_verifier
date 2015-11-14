package util.expressions;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import tool.verif.structs.VariablesMapping;
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
    
    public Expression applyMappings(VariablesMapping mapping, Expression result) {
        Expression condEval = condExpr.applyMappings(mapping, result);
        Expression ifEval = ifExpr.applyMappings(mapping, result);
        Expression elseEval = elseExpr.applyMappings(mapping, result);
        return new TernaryExpression(condEval, ifEval, elseEval);
    }
    
    public Expression applySummarisationMappings(VariablesMapping mapping, Map<String, Expression> parametersMapping, Expression resultExpr) {
        Expression condEval = condExpr.applySummarisationMappings(mapping, parametersMapping, resultExpr);
        Expression ifEval = ifExpr.applySummarisationMappings(mapping, parametersMapping, resultExpr);
        Expression elseEval = elseExpr.applySummarisationMappings(mapping, parametersMapping, resultExpr);
        return new TernaryExpression(condEval, ifEval, elseEval);
    }
}
