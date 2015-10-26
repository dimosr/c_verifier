package util.expressions;

public class ConstantExpression extends Expression {
    
    public String intValue;    //string representation used
    
    public ConstantExpression(String value) {
        intValue = value;
    }
    
    public ExpressionType getType() {
        return ExpressionType.CONSTANT;
    }
}
