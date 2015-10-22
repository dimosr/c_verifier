package util.assignments;

import util.conditions.Condition;

public class ConditionalAssignment extends Assignment {
    public Condition condition;
    public Assignment assignment;
    
    public boolean isConditional() {
        return true;
    }
}
