package util.expressions;

import java.util.ArrayList;
import java.util.List;
import util.misc.Tuple;

public class TernaryExpression extends Expression {
    
    public Expression condExpr;
    
    public Expression ifExpr;
    public Expression elseExpr;
    
    public boolean isRecursive;
    
    public TernaryExpression(Expression leftExpr, Expression ifExpr, Expression elseExpr, boolean isRecursive) {
        this.condExpr = leftExpr;
        this.ifExpr = ifExpr;
        this.elseExpr = elseExpr;
        this.isRecursive = isRecursive;
    }
    
    public boolean isSimple() {
        return !isRecursive;
    }
    
    public ExpressionType getType() {
        return ExpressionType.TERNARY;
    }
}
