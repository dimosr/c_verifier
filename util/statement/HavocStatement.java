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
import util.program.Program;


public class HavocStatement extends Statement {
    public String variable;
    
    public HavocStatement(String variable) {
        this.variable = variable;
    }
    
    public StatementType getType() {
        return StatementType.HAVOC;
    }
    
    public Set<String> getModifiedSet(Program program, List<String> localVariables) {
        Set<String> modSet = new HashSet();
        modSet.add(variable);
        return modSet;
    }
}
