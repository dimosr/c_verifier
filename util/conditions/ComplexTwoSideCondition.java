package util.conditions;

public class ComplexTwoSideCondition extends Condition {
    public Condition leftCondition;
    public LogicalOp operator;
    public Condition rightCondition;
            
    public boolean isSimple(){
        return false;
    }
}
