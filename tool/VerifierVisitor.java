package tool;

import java.util.List;
import java.util.Set;
import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.ProcedureDeclContext;
import tool.SsaAssertionMapping.SourceType;
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
import util.program.Procedure;
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
        
        private Procedure procedure;
        
        public SsaRepresentation getSsa(){
            return ssa;
        }
        
        public FreshStructure getFreshStructure(){
            return freshStructure;
        }
        
        public VerifierVisitor(Set<String> globalVariables) {
            globals = globalVariables;
        }
        
	public void visitProcedure(Procedure procedure) {
            this.procedure = procedure;
            
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
                executeAssumeExpression(require.expression);
            }
            
            for(Statement stmt : procedure.statements) {
                visitStmt(stmt);
            }
            
            for(EnsureCondition ensure : procedure.postConditions) {
                executeAssertionExpression(ensure.expression, ensure, procedure.postConditions, SourceType.ENSURES);
            }
            
        }
        
        
        public void executeAssumeExpression(Expression expression) {
            Expression previousAssumption = assumption;          
            Expression evaluatedExpression = expression.applyMappings(mapping, false, procedure.returnExpression);
            
            Expression rightHandSide = new BinaryExpression(predicate, new BinaryOperator(BinaryOperatorType.IMPLIES), evaluatedExpression);
            Expression newAssumption = new BinaryExpression(previousAssumption, new BinaryOperator(BinaryOperatorType.LAND), rightHandSide);
            
            assumption = newAssumption;
        }
        
        public void executeAssertionExpression(Expression expression, Object sourceObject, List sourceHolder, SourceType sourceType) {
            Expression leftHandSide = new BinaryExpression(assumption, new BinaryOperator(BinaryOperatorType.LAND), predicate);
            BinaryExpression assertionExpr = new BinaryExpression(leftHandSide, new BinaryOperator(BinaryOperatorType.IMPLIES), expression.applyMappings(mapping, false, procedure.returnExpression));
            
            Assertion assertion = new Assertion(assertionExpr);
            SsaAssertionMapping mapping = new SsaAssertionMapping(sourceObject, sourceHolder, sourceType);
            ssa.addAssertion(assertion, mapping);
            expression = null;
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
            
            Assignment assignment = new Assignment(ssaVariableName, stmt.rightHandSideExpr.applyMappings(mapping, false, procedure.returnExpression));
            ssa.addAssignment(assignment);
            
            mapping.updateExistingVar(variableName, newValue);
        }
        
        public void visitStmt(AssertStatement stmt) {
            executeAssertionExpression(stmt.expression, stmt, null, SourceType.ASSERT);
        }
        
        public void visitStmt(AssumeStatement stmt) {
            executeAssumeExpression(stmt.expression);
        }
        
        public void visitStmt(HavocStatement stmt) {
            String variableName = stmt.variable;
            int newIndex = freshStructure.fresh(variableName);
            mapping.updateExistingVar(variableName, newIndex);
        }
        
        public void visitStmt(CallStatement stmt) {
            //inSummarization = true !
        }
        
        public void visitStmt(IfStatement stmt) {
            Expression currentPredicate = predicate;
            VariablesMapping currentMapping = mapping;
            ModifiedSet currentModSet = modSet;
            
            Expression newPredicate = stmt.ifCondition.applyMappings(mapping, false, procedure.returnExpression);
            VariablesMapping mapping1 = currentMapping.deepClone();
            VariablesMapping mapping2 = currentMapping.deepClone();
            
            BinaryExpression predicate1 = new BinaryExpression(predicate, new BinaryOperator(BinaryOperatorType.LAND), newPredicate);       //Pred && NewPred
            BinaryExpression predicate2 = new BinaryExpression(predicate,   new BinaryOperator(BinaryOperatorType.LAND)   ,    new UnaryExpression(new UnaryOperator(UnaryOperatorType.NOT), newPredicate)    );        //Pred && ! (NewPred)
            
            predicate = predicate1;
            mapping = mapping1;
            modSet = new ModifiedSet();
            visitStmt(stmt.ifStatement);
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
            //inSummarization = true !
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
