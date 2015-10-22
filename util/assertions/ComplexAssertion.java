package util.assertions;

import util.conditions.Condition;

/**
 * Assertion for representing (assert left ==> right)
 */
public class ComplexAssertion extends Assertion {
    public Condition leftCondition;
    public Condition rightCondition;
    
    public ComplexAssertion(Condition left, Condition right) {
        leftCondition = left;
        rightCondition = right;
    }
    
    public boolean isSimple() {
        return false;
    }
}
