package util.operators;

public enum UnaryOperatorType {
    PLUS ("+", "+"),        //not added in SMT
    MINUS ("-", "bvneg"), 
    NOT ("!", "not"), 
    BNOT ("~", "bvnot");
    
    private final String ssaForm;
    private final String smtForm;
   
    UnaryOperatorType(String ssaForm, String smtForm) {
        this.ssaForm = ssaForm;
        this.smtForm = smtForm;
    }

    public String ssaForm() {
        return ssaForm;
    }
    
    public String smtForm() {
        return smtForm;
    }
    
    public static UnaryOperatorType findBySsaForm(String ssaForm) {
        UnaryOperatorType[] operatorTypes = UnaryOperatorType.values();
        for(UnaryOperatorType op : operatorTypes) {
            if(op.ssaForm.equals(ssaForm))
                return op;
        }
        return null;
    }
    
    public static UnaryOperatorType findBySmtForm(String smtForm) {
        UnaryOperatorType[] operatorTypes = UnaryOperatorType.values();
        for(UnaryOperatorType op : operatorTypes) {
            if(op.smtForm.equals(smtForm))
                return op;
        }
        return null;
    }
    
}
