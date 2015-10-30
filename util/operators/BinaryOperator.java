package util.operators;

public class BinaryOperator extends Operator {
    
    public BinaryOperatorType opType;
    
    public BinaryOperator(BinaryOperatorType operator) {
        this.opType = operator;
    }
    
    public OperatorType getType() {
        return OperatorType.BINARY;
    }
}
