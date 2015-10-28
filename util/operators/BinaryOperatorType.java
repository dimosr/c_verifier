package util.operators;

public enum BinaryOperatorType {
    LOR ("||", "or"), 
    LAND ("&&", "and"), 
    BOR ("|", "bvor"), 
    BXOR ("^", "bvxor"), 
    BAND ("&", "bvand"), 
    EQUALS ("==", "="), 
    NOT_EQUALS ("!=", "!="), 
    LESS ("<", "bvslt"), 
    LESS_EQUAL ("<=", "bvsle"), 
    GREATER (">", "bvsgt"), 
    GREATER_EQUAL (">=", "bvsge"), 
    LEFT_SHIFT ("<<", "bvshl"), 
    RIGHT_SHIFT ("<<", "bvrshr"), 
    PLUS ("+", "bvadd"), 
    MINUS ("-", "bvsub"), 
    MULT ("*", "bvmul"), 
    DIV ("/", "bvsdiv"), 
    MOD ("%", "bvsmod") ;
    
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
