package tool;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.misc.Interval;
import org.antlr.v4.runtime.tree.TerminalNode;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser;
import parser.SimpleCParser.AddExprContext;
import parser.SimpleCParser.AssertStmtContext;
import parser.SimpleCParser.AssignStmtContext;
import parser.SimpleCParser.AssumeStmtContext;
import parser.SimpleCParser.AtomExprContext;
import parser.SimpleCParser.BandExprContext;
import parser.SimpleCParser.BlockStmtContext;
import parser.SimpleCParser.BorExprContext;
import parser.SimpleCParser.BxorExprContext;
import parser.SimpleCParser.CallStmtContext;
import parser.SimpleCParser.EnsuresContext;
import parser.SimpleCParser.EqualityExprContext;
import parser.SimpleCParser.ExprContext;
import parser.SimpleCParser.FormalParamContext;
import parser.SimpleCParser.HavocStmtContext;
import parser.SimpleCParser.IfStmtContext;
import parser.SimpleCParser.LandExprContext;
import parser.SimpleCParser.LorExprContext;
import parser.SimpleCParser.MulExprContext;
import parser.SimpleCParser.NumberExprContext;
import parser.SimpleCParser.OldExprContext;
import parser.SimpleCParser.ParenExprContext;
import parser.SimpleCParser.PrepostContext;
import parser.SimpleCParser.ProcedureDeclContext;
import parser.SimpleCParser.ProgramContext;
import parser.SimpleCParser.RelExprContext;
import parser.SimpleCParser.RequiresContext;
import parser.SimpleCParser.ResultExprContext;
import parser.SimpleCParser.ShiftExprContext;
import parser.SimpleCParser.TernExprContext;
import parser.SimpleCParser.UnaryExprContext;
import parser.SimpleCParser.VarDeclContext;
import parser.SimpleCParser.VarrefContext;
import parser.SimpleCParser.VarrefExprContext;
import util.assertions.Assertion;
import util.assignments.Assignment;
import util.expressions.BinaryExpression;
import util.expressions.ConstantExpression;
import util.expressions.Expression;
import util.expressions.ParenthesisExpression;
import util.expressions.TernaryExpression;
import util.expressions.UnaryExpression;
import util.expressions.VarRefExpression;
import util.misc.Tuple;
import util.operators.BinaryOperator;
import util.operators.BinaryOperatorType;
import util.operators.UnaryOperator;
import util.operators.UnaryOperatorType;


public class VerifierVisitor extends SimpleCBaseVisitor<Void> {
        private Map<String, Integer> expectedProcedures = new HashMap<>();

	private Map<String, Integer> actualProcedures = new HashMap<>();

	private Set<String> globals;

	private HashSet<String> parameters = null;
	
	private List<Set<String>> localsStack = new ArrayList<>();
	
	private boolean inEnsures = false;
        
        private SsaRepresentation ssa;
        
        private FreshStructure fresh;
        
        private Expression expression;
        
        private VariablesMapping mapping;
        
        private Expression predicate;
        
        private ModifiedSet modSet;
        
        private Expression assumption;
        
        private boolean nonSummarizationPreConditions;
        
        private boolean nonSummarizationPostConditions;
        
        Expression returnExpression;
        
        public VerifierVisitor(Set<String> globalVariables) {
            globals = globalVariables;
        }
        
        public SsaRepresentation getSsa(){
            return ssa;
        }
        
        public FreshStructure getFresh(){
            return fresh;
        }
	
	@Override
	public Void visitProcedureDecl(ProcedureDeclContext ctx) {
            fresh = new FreshStructure();
            ssa = new SsaRepresentation();
            VariablesMapping currentMapping = new VariablesMapping();
            mapping = currentMapping;
            Expression initialPredicate = new ConstantExpression("1");    //true
            predicate = initialPredicate;
            modSet = new ModifiedSet();
            Expression initialAssumption = new ConstantExpression("1");    //true
            assumption = initialAssumption;
            
            String name = ctx.name.getText();
            actualProcedures.put(name, ctx.formals.size());
            
            for(String globalVar : globals) {
                fresh.addNewGlobal(globalVar);
                currentMapping.addNewGlobal(globalVar);
            }
            
            parameters = new HashSet<>();
            pushLocalsStack();
            for(FormalParamContext fp : ctx.formals) {
		String formalParamName = fp.ident.name.getText();
		parameters.add(formalParamName);
                fresh.addNewLocal(formalParamName);
                currentMapping.addNewLocal(formalParamName);
            }
            
            nonSummarizationPreConditions = true;
            for(PrepostContext preOrPostCondition : ctx.contract){
                super.visitPrepost(preOrPostCondition);
            }
            nonSummarizationPreConditions = false;
            
            for(SimpleCParser.StmtContext statementCtx : ctx.stmts) {
                visitStmt(statementCtx);
            }
            
            super.visitExpr(ctx.returnExpr);
            returnExpression = expression;
            
            nonSummarizationPostConditions = true;
            for(PrepostContext preOrPostCondition : ctx.contract){
                super.visitPrepost(preOrPostCondition);
            }
            nonSummarizationPostConditions = false;
            
            popLocalsStack();
            parameters = null;
            return null;
	}
        
        //this method will only be called for local variables!!
        @Override
	public Void visitVarDecl(VarDeclContext ctx) {
		String variableName = ctx.ident.name.getText();
                if(mapping.isLocal(variableName) || (mapping.isGlobal(variableName))) {     //shadowing
                    int previousIndex = mapping.getVarIndex(variableName);
                    mapping.addShadowedPreviousIndex(variableName, previousIndex);
                    int newIndex = fresh.fresh(variableName);
                    mapping.updateExistingVar(variableName, newIndex);
                }
                else {          //locally scoped
                    fresh.addNewLocal(variableName);
                    mapping.addNewLocal(variableName);
                    mapping.addLocallyScopedVar(variableName);
                }
		
		peekLocalsStack().add(variableName);
		return null;
	}
        
        public Void executeAssertionExpression(Expression expression) {
            Expression leftHandSide = new BinaryExpression(assumption, new BinaryOperator(BinaryOperatorType.LAND), predicate);
            BinaryExpression assertionExpr = new BinaryExpression(leftHandSide, new BinaryOperator(BinaryOperatorType.IMPLIES), expression);
            
            Assertion assertion = new Assertion(assertionExpr);
            ssa.addAssertion(assertion);
            expression = null;
            return null;
        }
        
        @Override
        public Void visitAssertStmt(AssertStmtContext ctx) {
            super.visitExpr(ctx.condition);
            return executeAssertionExpression(expression);
        }
        
        @Override
	public Void visitAssignStmt(AssignStmtContext ctx) {
            String variableName = ctx.lhs.ident.name.getText();
            Integer newValue = fresh.fresh(variableName);
            String ssaVariableName = null;
            if(mapping.isLocal(variableName)){
                ssaVariableName = variableName + newValue;
                modSet.addLocal(variableName);
            }
            else if(mapping.isGlobal(variableName)){
                ssaVariableName = "G__" + variableName + newValue;
                modSet.addGlobal(variableName);
            }           
            
            super.visitExpr(ctx.rhs);
            Assignment assignment = new Assignment(ssaVariableName, expression);
            ssa.addAssignment(assignment);
           
            mapping.updateExistingVar(variableName, newValue);        
            expression = null;
            return null;
	}
        
        @Override
        public Void visitIfStmt(IfStmtContext ctx) {
            Expression currentPredicate = predicate;
            VariablesMapping currentMapping = mapping;
            ModifiedSet currentModSet = modSet;
            
            visitExpr(ctx.condition);
            Expression newPredicate = expression;
            
            VariablesMapping mapping1 = currentMapping.deepClone();
            VariablesMapping mapping2 = currentMapping.deepClone();
            
            BinaryExpression predicate1 = new BinaryExpression(predicate, new BinaryOperator(BinaryOperatorType.LAND), newPredicate);       //Pred && NewPred
            BinaryExpression predicate2 = new BinaryExpression(predicate,   new BinaryOperator(BinaryOperatorType.LAND)   ,    new UnaryExpression(new UnaryOperator(UnaryOperatorType.NOT), newPredicate)    );        //Pred && ! (NewPred)

            predicate = predicate1;
            mapping = mapping1;
            modSet = new ModifiedSet();
            super.visitBlockStmt(ctx.thenBlock);
            mapping1 = mapping;
            ModifiedSet modSet1 = modSet;
            
            ModifiedSet modSet2 = null;
            if(ctx.elseBlock != null) {
                predicate = predicate2;
                mapping = mapping2;
                modSet = new ModifiedSet();
                super.visitBlockStmt(ctx.elseBlock);
                mapping2 = mapping;
                modSet2 = modSet;
            }
            
            ModifiedSet unionSet = modSet1.union(modSet2);
            
            for(String variable : unionSet.getLocalsModified()) {
                if( !mapping1.isLocallyScopedVar( variable) && !mapping2.isLocallyScopedVar(variable) ) {     //if it was not a locally scoped variable
                    currentModSet.addLocal(variable);
                
                    Integer freshIndex = fresh.fresh(variable);
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
                
                Integer freshIndex = fresh.fresh(variable);
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
            
            return null;
        }
	
	/*@Override
	public Void visitCallStmt(CallStmtContext ctx) {
		String name = ctx.callee.getText();
		int numArgs = ctx.actuals.size();
                
		expectedProcedures.put(name, numArgs);
		return super.visitCallStmt(ctx);
	}*/
		
	private Set<String> peekLocalsStack() {
		return localsStack.get(localsStack.size() - 1);
	}
	
	private Set<String> popLocalsStack() {
		return localsStack.remove(localsStack.size() - 1);
	}

	private void pushLocalsStack() {
		pushLocalsStack(new HashSet<String>());
	}

	private void pushLocalsStack(Set<String> frame) {
		localsStack.add(frame);
	}

	@Override
	public Void visitHavocStmt(HavocStmtContext ctx) {
            String variableName = ctx.var.ident.getText();
            int newIndex = fresh.fresh(variableName);
            mapping.updateExistingVar(variableName, newIndex);
            return null;
	}
        
        public Void executeAssumeExpression(Expression expression) {
            Expression previousAssumption = assumption;          
            Expression evaluatedExpression = expression;
            
            Expression rightHandSide = new BinaryExpression(predicate, new BinaryOperator(BinaryOperatorType.IMPLIES), evaluatedExpression);
            Expression newAssumption = new BinaryExpression(previousAssumption, new BinaryOperator(BinaryOperatorType.LAND), rightHandSide);
            
            assumption = newAssumption;
            return null;
        }
        
        @Override
        public Void visitAssumeStmt(AssumeStmtContext ctx) {
            visitExpr(ctx.condition);
            return executeAssumeExpression(expression);
        }
        
        @Override
        public Void visitRequires(RequiresContext ctx) {
            if(nonSummarizationPreConditions) {
                visitExpr(ctx.condition);
                return executeAssumeExpression(expression);
            }
            return null;
        }
        
        @Override
        public Void visitEnsures(EnsuresContext ctx) {
            if(nonSummarizationPostConditions) {
                visitExpr(ctx.condition);
                return executeAssertionExpression(expression);
            }
            return null;
        }
        
        /* 
            Visitors for various expression types
        */
        
        @Override
        public Void visitTernExpr(TernExprContext ctx) {
            if(ctx.single != null) {
                visitLorExpr(ctx.single);
            }
            else{
                TernaryExpression ternaryExpression = null;
                if(ctx.args.size() == 3) {
                    visitLorExpr(ctx.args.get(0));
                    Expression condExpr = expression;
                    visitLorExpr(ctx.args.get(1));
                    Expression ifExpr = expression;
                    visitLorExpr(ctx.args.get(2));
                    Expression elseExpr = expression;
                    
                    ternaryExpression = new TernaryExpression(condExpr, ifExpr, elseExpr);
                }
                else {
                    long elementsSum = ctx.args.size();
                    visitLorExpr(ctx.args.get(0));
                    Expression condExpr = expression;
                    visitLorExpr(ctx.args.get(1));
                    Expression ifExpr = expression;
                    List<LorExprContext> sublist = ctx.args.subList(2, (int) elementsSum);
                    ctx.args = sublist;
                    visitTernExpr(ctx);
                    Expression elseExpr = expression;
                    
                    ternaryExpression = new TernaryExpression(condExpr, ifExpr, elseExpr);
                }
                expression = ternaryExpression;
            }
            return null;
        }
        
        @Override
        public Void visitLorExpr(LorExprContext ctx) {
            if(ctx.single != null) {
                visitLandExpr(ctx.single);
            }
            else {
                BinaryExpression binExpr = null;
                
                visitLandExpr(ctx.args.get(0));
                Expression leftExpr = expression;
                expression = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.LOR);
                    visitLandExpr(ctx.args.get(i));
                    Expression rightExpr = expression;
                    expression = null;
                    
                    binExpr = new BinaryExpression(leftExpr, op, rightExpr);
                }
                
                expression = binExpr;
            }
            return null;
        }
        
        @Override
        public Void visitLandExpr(LandExprContext ctx) {
            if(ctx.single != null) {
                visitBorExpr(ctx.single);
            }
            else {
                BinaryExpression binExpr = null;
                
                visitBorExpr(ctx.args.get(0));
                Expression leftExpr = expression;
                expression = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.LAND);
                    visitBorExpr(ctx.args.get(i));
                    Expression rightExpr = expression;
                    expression = null;
                    
                    binExpr = new BinaryExpression(leftExpr, op, rightExpr);
                }
                
                expression = binExpr;
            }
            return null;
        }
        
        @Override
        public Void visitBorExpr(BorExprContext ctx) {
            if(ctx.single != null) {
                visitBxorExpr(ctx.single);
            }
            else {
                BinaryExpression binExpr = null;
                
                visitBxorExpr(ctx.args.get(0));
                Expression leftExpr = expression;
                expression = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.BOR);
                    visitBxorExpr(ctx.args.get(i));
                    Expression rightExpr = expression;
                    expression = null;
                    
                    binExpr = new BinaryExpression(leftExpr, op, rightExpr);
                }
                
                expression = binExpr;
            }
            return null;
        }
        
        @Override
        public Void visitBxorExpr(BxorExprContext ctx) {
            if(ctx.single != null) {
                visitBandExpr(ctx.single);
            }
            else {
                BinaryExpression binExpr = null;
                
                visitBandExpr(ctx.args.get(0));
                Expression leftExpr = expression;
                expression = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.BXOR);
                    visitBandExpr(ctx.args.get(i));
                    Expression rightExpr = expression;
                    expression = null;
                    
                    binExpr = new BinaryExpression(leftExpr, op, rightExpr);
                }
                
                expression = binExpr;
            }
            return null;
        }
        
        @Override
        public Void visitBandExpr(BandExprContext ctx) {
            if(ctx.single != null) {
                visitEqualityExpr(ctx.single);
            }
            else{
                BinaryExpression binExpr = null;
                
                visitEqualityExpr(ctx.args.get(0));
                Expression leftExpr = expression;
                expression = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.BAND);
                    visitEqualityExpr(ctx.args.get(i));
                    Expression rightExpr = expression;
                    expression = null;
                    
                    binExpr = new BinaryExpression(leftExpr, op, rightExpr);
                }
                
                expression = binExpr;
            }
            return null;
        }
        
        @Override
        public Void visitEqualityExpr(EqualityExprContext ctx) {
            if(ctx.single != null) {
                visitRelExpr(ctx.single);
            }
            else {
                BinaryExpression binExpr = null;
                
                visitRelExpr(ctx.args.get(0));
                Expression leftExpr = expression;
                expression = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    String opString = ctx.ops.get(i-1).getText();
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.findBySsaForm(opString));
                    visitRelExpr(ctx.args.get(i));
                    Expression rightExpr = expression;
                    expression = null;
                    
                    binExpr = new BinaryExpression(leftExpr, op, rightExpr);
                }
                
                expression = binExpr;
            }
            return null;
        }
        
        @Override
        public Void visitRelExpr(RelExprContext ctx) {
            if(ctx.single != null) {
                visitShiftExpr(ctx.single);
            }
            else {
                BinaryExpression binExpr = null;
                
                visitShiftExpr(ctx.args.get(0));
                Expression leftExpr = expression;
                expression = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    String opString = ctx.ops.get(i-1).getText();
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.findBySsaForm(opString));
                    visitShiftExpr(ctx.args.get(i));
                    Expression rightExpr = expression;
                    expression = null;
                    
                    binExpr = new BinaryExpression(leftExpr, op, rightExpr);
                }
                
                expression = binExpr;
            }
            return null;
        }
        
        @Override
        public Void visitShiftExpr(ShiftExprContext ctx) {
            if(ctx.single != null) {
                visitAddExpr(ctx.single);
            }
            else {
                Expression binExpr = null;
                
                visitAddExpr(ctx.args.get(0));
                Expression leftExpr = expression;
                expression = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    String opString = ctx.ops.get(i-1).getText();
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.findBySsaForm(opString));
                    visitAddExpr(ctx.args.get(i));
                    Expression rightExpr = expression;
                    expression = null;
                    
                    binExpr = new BinaryExpression(leftExpr, op, rightExpr);
                    if(op.opType == BinaryOperatorType.LEFT_SHIFT || op.opType == BinaryOperatorType.RIGHT_SHIFT) {
                        BinaryExpression shiftExpr = new BinaryExpression(leftExpr, op, rightExpr);
                        BinaryExpression checkZeroExpr = new BinaryExpression(rightExpr, new BinaryOperator(BinaryOperatorType.GREATER), new ConstantExpression("32"));
                        ParenthesisExpression parenthesisExpr = new ParenthesisExpression(new TernaryExpression(checkZeroExpr, new ConstantExpression("0"), shiftExpr));
                        binExpr = parenthesisExpr;
                    }
                    else{
                        binExpr = new BinaryExpression(leftExpr, op, rightExpr);
                    }
                }
                
                expression = binExpr;
            }
            return null;
        }
        
        @Override
        public Void visitAddExpr(AddExprContext ctx) {
            if(ctx.single != null) {
                visitMulExpr(ctx.single);
            }
            else {
                BinaryExpression binExpr = null;
                
                visitMulExpr(ctx.args.get(0));
                Expression leftExpr = expression;
                expression = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    String opString = ctx.ops.get(i-1).getText();
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.findBySsaForm(opString));
                    visitMulExpr(ctx.args.get(i));
                    Expression rightExpr = expression;
                    expression = null;
                    
                    binExpr = new BinaryExpression(leftExpr, op, rightExpr);
                }
                
                expression = binExpr;
            }
            return null;
        }
        
        @Override
        public Void visitMulExpr(MulExprContext ctx) {
            
            if(ctx.single != null) {
                visitUnaryExpr(ctx.single);
            }
            else {
                Expression binExpr = null;
                
                visitUnaryExpr(ctx.args.get(0));
                Expression leftExpr = expression;
                expression = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    String opString = ctx.ops.get(i-1).getText();
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.findBySsaForm(opString));
                    visitUnaryExpr(ctx.args.get(i));
                    Expression rightExpr = expression;
                    expression = null;
                    
                    binExpr = new BinaryExpression(leftExpr, op, rightExpr);
                    if(op.opType == BinaryOperatorType.DIV || op.opType == BinaryOperatorType.MOD) {
                        BinaryExpression divExpr = new BinaryExpression(leftExpr, op, rightExpr);
                        BinaryExpression checkZeroExpr = new BinaryExpression(rightExpr, new BinaryOperator(BinaryOperatorType.EQUALS), new ConstantExpression("0"));
                        ParenthesisExpression parenthesisExpr = new ParenthesisExpression(new TernaryExpression(checkZeroExpr, leftExpr, divExpr));
                        binExpr = parenthesisExpr;
                    }
                    else{
                        binExpr = new BinaryExpression(leftExpr, op, rightExpr);
                    }
                }
                
                expression = binExpr;
            }
            return null;
        }
        
        @Override
        public Void visitUnaryExpr(UnaryExprContext ctx) {
            if(ctx.single != null) {
                super.visitAtomExpr(ctx.single);
            }
            else {
                UnaryExpression unaryExpr = null;
                
                // reverse visiting order just for the initialization
                super.visitAtomExpr(ctx.arg);
                Expression expr = expression;
                expression = null;
                unaryExpr = new UnaryExpression(expr);
                
                
                for(Token op : ctx.ops){
                    String opString = op.getText();
                    UnaryOperator operator = new UnaryOperator(UnaryOperatorType.findBySsaForm(opString));
                    unaryExpr.addOperator(operator);
                }
                
                expression = unaryExpr;
            }
            return null;
        }
        
        @Override
        public Void visitNumberExpr(NumberExprContext ctx) {
            String value = ctx.number.getText();
            ConstantExpression constantExpr = new ConstantExpression(value);
            expression = constantExpr;
            return null;
        }
        
        @Override
	public Void visitVarrefExpr(VarrefExprContext ctx) {
            String variableName = ctx.var.ident.name.getText();
            Integer variableIndex = mapping.getVarIndex(variableName);
            String variableSsaName = null;
            if(mapping.isLocal(variableName))        
                variableSsaName = variableName + variableIndex;
            else if(mapping.isGlobal(variableName)) {
                variableSsaName = "G__" + variableName + variableIndex;
            }
            VarRefExpression varRefExpr = new VarRefExpression(variableSsaName);
            expression = varRefExpr;
            return null;
        }
        
        @Override
        public Void visitParenExpr(ParenExprContext ctx) {
            visitExpr(ctx.arg);
            Expression innerExpr = expression;
            expression = null;
            ParenthesisExpression parenExpr = new ParenthesisExpression(innerExpr);
            expression = parenExpr;
            
            return null;
        }
        
        @Override
        public Void visitResultExpr(ResultExprContext ctx) {
            expression = returnExpression;
            return null;
        }
        
        @Override
        public Void visitOldExpr(OldExprContext ctx) {
            String variableName = ctx.arg.ident.name.getText();
            VarRefExpression oldExpr = null;
            if(nonSummarizationPreConditions){
                String ssaVariableName = "G__" + variableName + "0";
                oldExpr = new VarRefExpression(ssaVariableName);
            }
            else if(!nonSummarizationPostConditions){
                String ssaVariableName = "G__" + variableName + mapping.getGlobalIndex(variableName);
                oldExpr = new VarRefExpression(ssaVariableName);
            }
            expression = oldExpr;
            return null;
        }
        
}
