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
    RIGHT_SHIFT ("<<", "bvashr"), 
    PLUS ("+", "bvadd"), 
    MINUS ("-", "bvsub"), 
    MULT ("*", "bvmul"), 
    DIV ("/", "bvsdiv"), 
    MOD ("%", "bvsmod"),
    IMPLIES ("==>", "=>");

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
    
    public boolean isNumInputNumOutput() {
        return (this == BinaryOperatorType.LEFT_SHIFT ||
               this == BinaryOperatorType.RIGHT_SHIFT ||
               this == BinaryOperatorType.PLUS ||
               this == BinaryOperatorType.MINUS ||
               this == BinaryOperatorType.MULT ||
               this == BinaryOperatorType.DIV ||
               this == BinaryOperatorType.BOR ||
               this == BinaryOperatorType.BXOR ||
               this == BinaryOperatorType.BAND ||
               this == BinaryOperatorType.MOD);
    }
    
    public boolean isNumInputBoolOutput() {
        return (this == BinaryOperatorType.LESS ||
               this == BinaryOperatorType.LESS_EQUAL ||
               this == BinaryOperatorType.GREATER ||
               this == BinaryOperatorType.GREATER_EQUAL ||
               this == BinaryOperatorType.EQUALS ||
               this == BinaryOperatorType.NOT_EQUALS );
    }
    
    public boolean isBoolInputBoolOutput() {
        return (this == BinaryOperatorType.LOR ||
               this == BinaryOperatorType.LAND ||
               this == BinaryOperatorType.IMPLIES);
    }
}
