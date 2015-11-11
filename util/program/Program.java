package util.program;

import java.util.List;
import java.util.Set;


public class Program {
    public Set<String> globalVariables;
    public List<Procedure> procedures;
    
    public Program(Set<String> globalVariables, List<Procedure> procedures) {
        this.globalVariables = globalVariables;
        this.procedures = procedures;
    }
}
