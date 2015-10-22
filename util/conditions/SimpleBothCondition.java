package util.conditions;

public class SimpleBothCondition extends Condition{
    public String leftVariableName;
    public ComparisonOp operator;
    public String rightVariableName;
    
    public SimpleBothCondition(String leftVar, ComparisonOp op, String rightVar){
        leftVariableName = leftVar;
        operator = op;
        rightVariableName = rightVar;
    }
    
    public boolean isSimple(){
        return true;
    }
}
