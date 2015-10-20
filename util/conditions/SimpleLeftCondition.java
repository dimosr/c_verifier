package util.conditions;


public class SimpleLeftCondition extends Condition {
    public String variableName;
    public ComparisonOp operator;
    public int comparisonValue;
    
    public boolean isSimple(){
        return true;
    }
}
