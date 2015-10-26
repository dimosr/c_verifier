package util.operators;

public class BinaryOperator extends Operator {
    
    public BinaryOperatorType operator;
    
    public BinaryOperator(BinaryOperatorType operator) {
        this.operator = operator;
    }
    
    public OperatorType getType() {
        return OperatorType.BINARY;
    }
}
