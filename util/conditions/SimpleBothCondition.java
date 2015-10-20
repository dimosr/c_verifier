package util.conditions;

public class SimpleBothCondition extends Condition{
    public String leftVariableName;
    public ComparisonOp operator;
    public String rightVariableName;
    
    public boolean isSimple(){
        return true;
    }
}
