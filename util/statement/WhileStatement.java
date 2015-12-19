/**
 *  Copyright 2016 by Dimos Raptis <raptis.dimos@yahoo.gr>
 *  Licensed under GNU General Public License 2.0 or later. 
 *  Some rights reserved. See LICENSE.
 *
 *  @license GPL-2.0 <http://spdx.org/licenses/GPL-2.0.html>
 */

package util.statement;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import util.expressions.Expression;
import util.program.Invariant;
import util.program.Program;


public class WhileStatement extends Statement {
    public Expression loopCondition;
    public List<Invariant> invariants;
    public BlockStatement blockStatement;
    
    public WhileStatement(Expression loopCondition, List<Invariant> invariants, BlockStatement blockStatement) {
        this.loopCondition = loopCondition;
        this.invariants = invariants;
        this.blockStatement = blockStatement;
    }
    
    public StatementType getType() {
        return StatementType.WHILE;
    }
    
    public Set<String> getModifiedSet(Program program, List<String> localVariables) {
        Set<String> modSet = new HashSet();
        Set<String> blockModSet = blockStatement.getModifiedSet(program, localVariables);
        for(String variable : blockModSet)
            if(program.globalVariables.contains(variable) || localVariables.contains(variable))
                modSet.add(variable); 
        return modSet;
    }
}
