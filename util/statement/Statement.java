/**
 *  Copyright 2016 by Dimos Raptis <raptis.dimos@yahoo.gr>
 *  Licensed under GNU General Public License 2.0 or later. 
 *  Some rights reserved. See LICENSE.
 *
 *  @license GPL-2.0 <http://spdx.org/licenses/GPL-2.0.html>
 */

package util.statement;

import java.util.List;
import java.util.Set;
import util.program.Program;

public abstract class Statement {
    public abstract StatementType getType();
    public abstract Set<String> getModifiedSet(Program program, List<String> localVariables);
}
