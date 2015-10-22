package util.assignments;

import util.conditions.Condition;

public class ConditionalAssignment extends Assignment {
    public Condition condition;
    public Assignment assignment;
    
    public ConditionalAssignment(Condition condition, Assignment assignment) {
        this.condition = condition;
        this.assignment = assignment;
    }
    
    public boolean isConditional() {
        return true;
    }
}
