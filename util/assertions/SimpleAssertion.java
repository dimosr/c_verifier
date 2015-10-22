package util.assertions;

import util.conditions.Condition;

public class SimpleAssertion extends Assertion {
    public Condition condition;
    
    public SimpleAssertion(Condition condition) {
        this.condition = condition;
    }
    
    public boolean isSimple() {
        return true;
    }
}
