package tool;

import java.util.ArrayList;
import java.util.List;


public class VerificationResult {
    
    private VerificationResultType resultType;
    private List<Integer> failingAssertionsIndexes;
    
    public enum VerificationResultType {
        CORRECT("CORRECT"), 
        INCORRECT("INCORRECT"), 
        UNKNOWN("UNKNOWN");
        
        private String value;
        VerificationResultType(String value) {
            this.value = value;
        }
         
        @Override
        public String toString() {
            return value;
        }
    };
    
    public VerificationResult(VerificationResultType resultType) {
        this.resultType = resultType;
        failingAssertionsIndexes = new ArrayList();
    }
    
    public boolean isCorrect() {
        return resultType == VerificationResultType.CORRECT;
    }
    
    public boolean isIncorrect() {
        return resultType == VerificationResultType.INCORRECT;
    }
    
    public boolean isUknown() {
        return resultType == VerificationResultType.UNKNOWN;
    }
    
    public void addFailingAssertionIndex(int index) {
        failingAssertionsIndexes.add(index);
    }
    
    public List<Integer> getFailingAssertionsIndexes() {
        return failingAssertionsIndexes;
    }
    
}
