package util.conditions;

public class ComplexTwoSideCondition extends Condition {
    public Condition leftCondition;
    public LogicalOp operator;
    public Condition rightCondition;
    
    public ComplexTwoSideCondition(Condition left, LogicalOp op, Condition right) {
        leftCondition = left;
        operator = op;
        rightCondition = right;
    }
    
    public boolean isSimple(){
        return false;
    }
}
