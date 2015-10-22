package util.conditions;


public class SimpleLeftCondition extends Condition {
    public String variableName;
    public ComparisonOp operator;
    public int comparisonValue;
    
    public SimpleLeftCondition(String var, ComparisonOp op, int val) {
        variableName = var;
        operator = op;
        comparisonValue = val;
    }
    
    public boolean isSimple(){
        return true;
    }
}
