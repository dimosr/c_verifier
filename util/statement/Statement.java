package util.statement;

import java.util.Set;

public abstract class Statement {
    public abstract StatementType getType();
    public abstract Set<String> getModifiedSet();
}
