package tool;

import tool.verif.structs.SsaAssertionMapping;
import tool.verif.structs.VariablesMapping;
import tool.verif.structs.SsaRepresentation;
import tool.verif.structs.ModifiedSet;
import tool.verif.structs.FreshStructure;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.ProcedureDeclContext;
import tool.verif.structs.LoopStrategy;
import tool.verif.structs.SsaAssertionMapping.SourceType;
import util.expressions.BinaryExpression;
import util.expressions.ConstantExpression;
import util.expressions.Expression;
import util.expressions.TernaryExpression;
import util.expressions.UnaryExpression;
import util.expressions.VarRefExpression;
import util.operators.BinaryOperator;
import util.operators.BinaryOperatorType;
import util.operators.UnaryOperator;
import util.operators.UnaryOperatorType;
import util.program.Assertion;
import util.program.Assignment;
import util.program.EnsureCondition;
import util.program.Invariant;
import util.program.Procedure;
import util.program.Program;
import util.program.RequireCondition;
import util.statement.AssertStatement;
import util.statement.AssignStatement;
import util.statement.AssumeStatement;
import util.statement.BlockStatement;
import util.statement.CallStatement;
import util.statement.HavocStatement;
import util.statement.IfStatement;
import util.statement.Statement;
import util.statement.VarDeclStatement;
import util.statement.WhileStatement;


public class VerifierVisitor {
    
        private SsaRepresentation ssa;
        private FreshStructure freshStructure;
        
        private VariablesMapping mapping;
        private Expression predicate;
        private ModifiedSet modSet;
        private Expression assumption;
        
        private Set<String> globals;
        
        private Program program;
        private Procedure procedure;
        
        private boolean loopGeneratedIf = false;
        private List<Invariant> loopGeneratedInvariants;
        
        private LoopStrategy loopStrategy;
        private int unwindingDepth;
        
        public SsaRepresentation getSsa(){
            return ssa;
        }
        
        public FreshStructure getFreshStructure(){
            return freshStructure;
        }
        
        public VerifierVisitor(Program program) {
            globals = program.globalVariables;
            this.program = program;
        }
        
	public void visitProcedure(Procedure procedure, LoopStrategy loopStrategy, int unwindingDepth) {
            this.procedure = procedure;
            this.loopStrategy = loopStrategy;
            this.unwindingDepth = unwindingDepth;
            
            freshStructure = new FreshStructure();
            ssa = new SsaRepresentation();
            VariablesMapping currentMapping = new VariablesMapping();
            mapping = currentMapping;
            Expression initialPredicate = new ConstantExpression("1");    //true
            predicate = initialPredicate;
            modSet = new ModifiedSet();
            Expression initialAssumption = new ConstantExpression("1");    //true
            assumption = initialAssumption;
            
            for(String globalVar : globals) {
                freshStructure.addNewGlobal(globalVar);
                currentMapping.addNewGlobal(globalVar);
            }
            
            for(String parameter : procedure.parameters) {
                freshStructure.addNewLocal(parameter);
                currentMapping.addNewLocal(parameter);
            }
            
            for(RequireCondition require : procedure.preConditions) {
                executeAssumeExpression(require.expression.applyMappings(mapping, procedure.returnExpression));
            }
            
            for(Statement stmt : procedure.statements) {
                visitStmt(stmt);
            }
            
            for(EnsureCondition ensure : procedure.postConditions) {
                executeAssertionExpression(ensure.expression.applyMappings(mapping, procedure.returnExpression), ensure, procedure.postConditions, SourceType.ENSURES);
            }
            
        }
        
        
        public void executeAssumeExpression(Expression evaluatedExpression) {
            Expression previousAssumption = assumption;          
            
            Expression rightHandSide = new BinaryExpression(predicate, new BinaryOperator(BinaryOperatorType.IMPLIES), evaluatedExpression);
            Expression newAssumption = new BinaryExpression(previousAssumption, new BinaryOperator(BinaryOperatorType.LAND), rightHandSide);
            
            assumption = newAssumption;
        }
        
        public void executeAssertionExpression(Expression evaluatedExpression, Object sourceObject, List sourceHolder, SourceType sourceType) {
            Expression leftHandSide = new BinaryExpression(assumption, new BinaryOperator(BinaryOperatorType.LAND), predicate);
            BinaryExpression assertionExpr = new BinaryExpression(leftHandSide, new BinaryOperator(BinaryOperatorType.IMPLIES), evaluatedExpression);
            
            Assertion assertion = new Assertion(assertionExpr);
            SsaAssertionMapping mapping = new SsaAssertionMapping(sourceObject, sourceHolder, sourceType);
            ssa.addAssertion(assertion, mapping);
        }
        
        
        
        public void visitStmt(VarDeclStatement stmt) {
            String variableName = stmt.variable;
            if(mapping.isLocal(variableName) || (mapping.isGlobal(variableName))) {     //shadowing
                int previousIndex = mapping.getVarIndex(variableName);
                mapping.addShadowedPreviousIndex(variableName, previousIndex);
                int newIndex = freshStructure.fresh(variableName);
                mapping.updateExistingVar(variableName, newIndex);
            }
            else {          //locally scoped
                freshStructure.addNewLocal(variableName);
                mapping.addNewLocal(variableName);
                mapping.addLocallyScopedVar(variableName);
            }
        }
        
        public void visitStmt(AssignStatement stmt) {
            String variableName = stmt.variable;
            Integer newValue = freshStructure.fresh(variableName);
            String ssaVariableName = null;
            if(mapping.isLocal(variableName)){
                ssaVariableName = variableName + newValue;
                modSet.addLocal(variableName);
            }
            else if(mapping.isGlobal(variableName)){
                ssaVariableName = "G__" + variableName + newValue;
                modSet.addGlobal(variableName);
            } 
            
            Assignment assignment = new Assignment(ssaVariableName, stmt.rightHandSideExpr.applyMappings(mapping, procedure.returnExpression));
            ssa.addAssignment(assignment);
            
            mapping.updateExistingVar(variableName, newValue);
        }
        
        public void visitStmt(AssertStatement stmt) {
            executeAssertionExpression(stmt.expression.applyMappings(mapping, procedure.returnExpression), stmt, null, SourceType.ASSERT);
        }
        
        public void visitStmt(AssumeStatement stmt) {
            executeAssumeExpression(stmt.expression.applyMappings(mapping, procedure.returnExpression));
        }
        
        public void visitStmt(HavocStatement stmt) {
            String variableName = stmt.variable;
            int newIndex = freshStructure.fresh(variableName);
            mapping.updateExistingVar(variableName, newIndex);
        }
        
        public void visitStmt(CallStatement stmt) {   
            Procedure calledProcedure = program.procedures.get(stmt.procedureName);
            Map<String, Expression> formalActualParamsMapping = new HashMap();
            List<String> formalParams = calledProcedure.parameters;
            List<Expression> actualParams = stmt.parameters;
            VarRefExpression returnVariable = new VarRefExpression(calledProcedure.procedureName + "_ret");
            if(!mapping.isLocal(returnVariable.variableName)) {
                visitStmt(new VarDeclStatement(returnVariable.variableName));
            }
            for(int i = 0; i < formalParams.size(); i++) {
                formalActualParamsMapping.put(formalParams.get(i), actualParams.get(i));
            }
            
            /** Summarization pre-conditions **/
            for(RequireCondition require : calledProcedure.preConditions) {
                Expression expressionWithActualParams = require.expression.applySummarisationMappings(mapping, formalActualParamsMapping, returnVariable);
                Expression evaluatedExpr = expressionWithActualParams.applyMappings(mapping, returnVariable);
                executeAssertionExpression(evaluatedExpr, require, calledProcedure.preConditions, SourceType.ASSERT);
            }
            
            /** Summarization havocs **/
            for(String variable : calledProcedure.modifiedSet) {
                if(program.globalVariables.contains(variable) || procedure.localVariables.contains(variable))
                    visitStmt(new HavocStatement(variable));
            }
            visitStmt(new HavocStatement(returnVariable.variableName));
            
            /** Summarization post-conditions **/
            for(EnsureCondition ensure : calledProcedure.postConditions) {
                Expression expressionWithActualParams = ensure.expression.applySummarisationMappings(mapping, formalActualParamsMapping, returnVariable);
                Expression evaluatedExpr = expressionWithActualParams.applyMappings(mapping, returnVariable);
                executeAssumeExpression(evaluatedExpr);
            }
            
            visitStmt(new AssignStatement(stmt.variableName, returnVariable));
        }
        
        public void visitStmt(IfStatement stmt) {
            Expression currentPredicate = predicate;
            VariablesMapping currentMapping = mapping;
            ModifiedSet currentModSet = modSet;
            
            Expression newPredicate = stmt.ifCondition.applyMappings(mapping, procedure.returnExpression);
            VariablesMapping mapping1 = currentMapping.deepClone();
            VariablesMapping mapping2 = currentMapping.deepClone();
            
            BinaryExpression predicate1 = new BinaryExpression(predicate, new BinaryOperator(BinaryOperatorType.LAND), newPredicate);       //Pred && NewPred
            BinaryExpression predicate2 = new BinaryExpression(predicate,   new BinaryOperator(BinaryOperatorType.LAND)   ,    new UnaryExpression(new UnaryOperator(UnaryOperatorType.NOT), newPredicate)    );        //Pred && ! (NewPred)
            
            predicate = predicate1;
            mapping = mapping1;
            modSet = new ModifiedSet();
            visitStmt(stmt.ifStatement);
            if(loopGeneratedIf) {               /* loop summarization */
                for(Invariant invariant : loopGeneratedInvariants)
                    executeAssertionExpression(invariant.expression.applyMappings(mapping, procedure.returnExpression), invariant, loopGeneratedInvariants, SourceType.INVARIANT);
                executeAssumeExpression(new ConstantExpression("0"));
            }
            mapping1 = mapping;
            ModifiedSet modSet1 = modSet;
            
            ModifiedSet modSet2 = null;
            if(stmt.elseStatement != null) {
                predicate = predicate2;
                mapping = mapping2;
                modSet = new ModifiedSet();
                visitStmt(stmt.elseStatement);
                mapping2 = mapping;
                modSet2 = modSet;
            }
            
            ModifiedSet unionSet = modSet1.union(modSet2);
            for(String variable : unionSet.getLocalsModified()) {
                if( !mapping1.isLocallyScopedVar( variable) && !mapping2.isLocallyScopedVar(variable) ) {     //if it was not a locally scoped variable
                    currentModSet.addLocal(variable);
                
                    Integer freshIndex = freshStructure.fresh(variable);
                    currentMapping.updateExistingVar(variable, freshIndex);
                    String finalVariable = variable + freshIndex;
                
                    String ifVariable = null, elseVariable = null;
                    if(mapping1.isShadowed(variable))
                        ifVariable = variable + mapping1.getIndexBeforeShadowing(variable);
                    else
                        ifVariable = variable + mapping1.getVarIndex(variable);
                     
                    if(mapping2.isShadowed(variable))
                        elseVariable = variable + mapping2.getIndexBeforeShadowing(variable);
                    else
                        elseVariable = variable + mapping2.getVarIndex(variable);
                
                    TernaryExpression assignmentExpression = new TernaryExpression(newPredicate, new VarRefExpression(ifVariable), new VarRefExpression(elseVariable)) ;
                    Assignment branchResolutionAssignment = new Assignment(finalVariable, assignmentExpression);
                
                    ssa.addAssignment(branchResolutionAssignment);
                }
            }
            for(String variable : unionSet.getGlobalsModified()) {
                currentModSet.addGlobal(variable);
                
                Integer freshIndex = freshStructure.fresh(variable);
                currentMapping.updateExistingVar(variable, freshIndex);
                String finalVariable = "G__" + variable + freshIndex;
                
                String ifVariable = null, elseVariable = null;
                if(mapping1.isShadowed(variable))
                    ifVariable = "G__" + variable + mapping1.getIndexBeforeShadowing(variable);
                else
                    ifVariable = "G__" + variable + mapping1.getVarIndex(variable);
                     
                if(mapping2.isShadowed(variable))
                    elseVariable = "G__" + variable + mapping2.getIndexBeforeShadowing(variable);
                else
                    elseVariable = "G__" + variable + mapping2.getVarIndex(variable);

                
                TernaryExpression assignmentExpression = new TernaryExpression(newPredicate, new VarRefExpression(ifVariable), new VarRefExpression(elseVariable)) ;
                Assignment branchResolutionAssignment = new Assignment(finalVariable, assignmentExpression);
                
                ssa.addAssignment(branchResolutionAssignment);
            }
            
            predicate = currentPredicate;
            mapping = currentMapping;
            
            modSet = currentModSet;
        }
        
        public void visitStmt(BlockStatement stmt) {
            for(Statement innerStmt : stmt.statements)
                visitStmt(innerStmt);
        }
        
        public void visitStmt(WhileStatement stmt) { 
            if(loopStrategy == LoopStrategy.LOOP_SUMMARISATION) {
                for(Invariant invariant : stmt.invariants)
                    executeAssertionExpression(invariant.expression.applyMappings(mapping, procedure.returnExpression), invariant, stmt.invariants, SourceType.INVARIANT);
            
                Set<String> loopModSet = stmt.getModifiedSet(program, procedure.localVariables);
                for(String variable : loopModSet)
                    visitStmt(new HavocStatement(variable));
            
                for(Invariant invariant : stmt.invariants)
                    executeAssumeExpression(invariant.expression.applyMappings(mapping, procedure.returnExpression));
            
                BlockStatement generatedIfBlock = new BlockStatement(stmt.blockStatement.statements);
                loopGeneratedIf = true;
                loopGeneratedInvariants = stmt.invariants;
                IfStatement ifStmt = new IfStatement(stmt.loopCondition, generatedIfBlock);
                visitStmt(ifStmt);
                loopGeneratedIf = false;
            }
            else if(loopStrategy == LoopStrategy.SIMPLE_BMC) {
                
                /* Initialised block */
                AssumeStatement assumeFalse = new AssumeStatement(new ConstantExpression("0"));
                BlockStatement ifBlock = new BlockStatement();
                ifBlock.statements.add(assumeFalse);
                IfStatement ifStmt = new IfStatement(stmt.loopCondition, ifBlock);
                BlockStatement unwindingBlock = new BlockStatement();
                for(Invariant invariant : stmt.invariants) {
                    unwindingBlock.statements.add(new AssertStatement(invariant.expression));
                }
                unwindingBlock.statements.add(ifStmt);
                
                /* Loop unwinding */
                for(int i = 0; i < unwindingDepth; i++) {
                    ifBlock = new BlockStatement();
                    ifBlock.statements.add(stmt.blockStatement);
                    ifBlock.statements.add((Statement) unwindingBlock);
                    ifStmt = new IfStatement(stmt.loopCondition, ifBlock);
                    
                    unwindingBlock = new BlockStatement();
                    for(Invariant invariant : stmt.invariants) {
                        unwindingBlock.statements.add(new AssertStatement(invariant.expression));
                    }
                    unwindingBlock.statements.add(ifStmt);
                }
                visitStmt(unwindingBlock);
            }
        }
        
        public void visitStmt(Statement stmt) {
            if(stmt instanceof VarDeclStatement)
                visitStmt( (VarDeclStatement) stmt );
            else if(stmt instanceof AssignStatement)
                visitStmt( (AssignStatement) stmt );
            else if( stmt instanceof AssertStatement)
                visitStmt( (AssertStatement) stmt );
            else if( stmt instanceof AssumeStatement)
                visitStmt( (AssumeStatement) stmt );
            else if(stmt instanceof HavocStatement)
                visitStmt( (HavocStatement) stmt );
            else if(stmt instanceof CallStatement)
                visitStmt( (CallStatement) stmt );
            else if(stmt instanceof IfStatement)
                visitStmt( (IfStatement) stmt );
            else if(stmt instanceof BlockStatement)
                visitStmt( (BlockStatement) stmt );
            else if(stmt instanceof WhileStatement)
                visitStmt( (WhileStatement) stmt );  
        }
        
}
