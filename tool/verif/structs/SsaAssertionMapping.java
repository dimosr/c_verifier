package tool.verif.structs;

import java.util.List;


public class SsaAssertionMapping {
    public Object source;
    public List holder;
    public SourceType sourceType;
    
    public enum SourceType {
        ASSERT, INVARIANT, ENSURES, REQUIRES
    }
    
    public SsaAssertionMapping(Object source, List holder, SourceType sourceType) {
        this.source = source;
        this.holder = holder;
        this.sourceType = sourceType;
    }
}
