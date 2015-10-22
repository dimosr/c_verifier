package util.assignments;

public class SimpleVarAssignment extends Assignment{
    public String leftVariableName;
    public String rightVariableName;
    
    public SimpleVarAssignment(String leftVar, String rightVar){
        leftVariableName = leftVar;
        rightVariableName = rightVar;
    }
    
    public boolean isConditional() {
        return false;
    }
}
