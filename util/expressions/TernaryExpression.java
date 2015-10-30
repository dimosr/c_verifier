package util.expressions;

import java.util.ArrayList;
import java.util.List;
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
}
