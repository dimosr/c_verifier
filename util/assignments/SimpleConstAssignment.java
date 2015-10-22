package util.assignments;

public class SimpleConstAssignment extends Assignment {
    public String variableName;
    public int value;
    
    public SimpleConstAssignment(String var, int val) {
        variableName = var;
        value = val;
    }
    
    public boolean isConditional() {
        return false;
    }
}
