/**
 *  Copyright 2016 by Dimos Raptis <raptis.dimos@yahoo.gr>
 *  Licensed under GNU General Public License 2.0 or later. 
 *  Some rights reserved. See LICENSE.
 *
 *  @license GPL-2.0 <http://spdx.org/licenses/GPL-2.0.html>
 */

package util.statement;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import util.program.Program;


public class BlockStatement extends Statement {
    public List<Statement> statements;

    
    public BlockStatement(List<Statement> statements) {
        this.statements = statements;
    }
    
    public BlockStatement() {
        this.statements = new ArrayList();
    }
    
    public StatementType getType() {
        return StatementType.BLOCK;
    }
    
    public Set<String> getModifiedSet(Program program, List<String> localVariables) {
        Set<String> modSet = new HashSet();
        for(Statement statement : statements) {
            Set<String> stmtModSet = statement.getModifiedSet(program, localVariables);
            for(String variable : stmtModSet)
                modSet.add(variable);
        }
        return modSet;
    }
}
