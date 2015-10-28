package util.expressions;

import java.util.ArrayList;
import java.util.List;
import util.operators.UnaryOperator;

public class UnaryExpression extends Expression {
    
    public List<UnaryOperator> operators;
    public Expression expr;
    
    public UnaryExpression(Expression expr) {
        this.operators = new ArrayList<UnaryOperator>();
        this.expr = expr;
    }
    
    public UnaryExpression(UnaryOperator op, Expression expr) {
        this(expr);
        operators.add(op);
    }
    
    public void addOperator(UnaryOperator op) {
        operators.add(op);
    }
    
    public ExpressionType getType() {
        return ExpressionType.UNARY;
    }
}
