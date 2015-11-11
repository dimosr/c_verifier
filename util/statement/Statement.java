package util.statement;

import java.util.List;
import java.util.Set;
import util.program.Program;

public abstract class Statement {
    public abstract StatementType getType();
    public abstract Set<String> getModifiedSet(Program program, List<String> localVariables);
}
