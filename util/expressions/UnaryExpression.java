package util.expressions;

import java.util.ArrayList;
import java.util.List;
import tool.VariablesMapping;
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
    
    public Expression applyMappings(VariablesMapping mapping, boolean inSummarisation, Expression result) {
        Expression exprEval = expr.applyMappings(mapping, inSummarisation, result);
        UnaryExpression unaryEval = new UnaryExpression(exprEval);
        for(UnaryOperator op : operators)
            unaryEval.addOperator(op);
        return unaryEval;
    }
}
