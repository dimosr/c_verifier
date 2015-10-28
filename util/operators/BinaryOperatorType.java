package util.operators;

public enum BinaryOperatorType {
    LOR ("||", "lor"), 
    LAND ("&&", "land"), 
    BOR ("|", "bor"), 
    BXOR ("^", "bxor"), 
    BAND ("&", "band"), 
    EQUALS ("==", "equals"), 
    NOT_EQUALS ("!=", "not_equals"), 
    LESS ("<", "less"), 
    LESS_EQUAL ("<=", "less_equal"), 
    GREATER (">", "greater"), 
    GREATER_EQUAL (">=", "greater_equal"), 
    LEFT_SHIFT ("<<", "left_shift"), 
    RIGHT_SHIFT ("<<", "right_shift"), 
    PLUS ("+", "plus"), 
    MINUS ("-", "minus"), 
    MULT ("*", "mult"), 
    DIV ("/", "div"), 
    MOD ("%", "mod"),
    IMPLIES ("==>", "implies");
    
    private final String ssaForm;
    private final String smtForm;
    BinaryOperatorType(String ssaForm, String smtForm) {
        this.ssaForm = ssaForm;
        this.smtForm = smtForm;
    }
    
    public String ssaForm() {
        return ssaForm;
    }
    
    public String smtForm() {
        return smtForm;
    }
    
    public static BinaryOperatorType findBySsaForm(String ssaForm) {
        BinaryOperatorType[] operatorTypes = BinaryOperatorType.values();
        for(BinaryOperatorType op : operatorTypes) {
            if(op.ssaForm.equals(ssaForm))
                return op;
        }
        return null;
    }
    
    public static BinaryOperatorType findBySmtForm(String smtForm) {
        BinaryOperatorType[] operatorTypes = BinaryOperatorType.values();
        for(BinaryOperatorType op : operatorTypes) {
            if(op.smtForm.equals(smtForm))
                return op;
        }
        return null;
    }
}
