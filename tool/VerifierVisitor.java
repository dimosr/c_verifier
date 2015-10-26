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
import parser.SimpleCParser.LandExprContext;
import parser.SimpleCParser.LorExprContext;
import parser.SimpleCParser.MulExprContext;
import parser.SimpleCParser.NumberExprContext;
import parser.SimpleCParser.OldExprContext;
import parser.SimpleCParser.ParenExprContext;
import parser.SimpleCParser.ProcedureDeclContext;
import parser.SimpleCParser.ProgramContext;
import parser.SimpleCParser.RelExprContext;
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
import util.expressions.OldExpression;
import util.expressions.ParenthesisExpression;
import util.expressions.ResultExpression;
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
        
        private Map<String, Integer> mapping;
        
        private Expression expression;
        
        public VerifierVisitor(Set<String> globalVariables) {
            globals = globalVariables;
        }
        
        public SsaRepresentation getSsa(){
            return ssa;
        }
        
        public FreshStructure getFresh(){
            return fresh;
        }
	
	/*@Override
	public Void visitBlockStmt(BlockStmtContext ctx) {
		pushLocalsStack();
		Void result = super.visitBlockStmt(ctx);
		popLocalsStack();
		return result;
	}*/
	
	@Override
	public Void visitProcedureDecl(ProcedureDeclContext ctx) {
            fresh = new FreshStructure();
            ssa = new SsaRepresentation();
            mapping = new HashMap<String, Integer>();
            
            String name = ctx.name.getText();
            actualProcedures.put(name, ctx.formals.size());
            
            for(String globalVar : globals) {
                fresh.addNewVar(globalVar);
                mapping.put(globalVar, 0);
            }
            
            parameters = new HashSet<>();
            pushLocalsStack();
            for(FormalParamContext fp : ctx.formals) {
		String formalParamName = fp.ident.name.getText();
		parameters.add(formalParamName);
                fresh.addNewVar(formalParamName);
                mapping.put(formalParamName, 0);
            }
            
            for(SimpleCParser.StmtContext statementCtx : ctx.stmts) {
                visitStmt(statementCtx);
            }
            
            //TODO : visit return stmt
            
            popLocalsStack();
            parameters = null;
            return null;
	}
        
        @Override
	public Void visitVarDecl(VarDeclContext ctx) {
		String name = ctx.ident.name.getText();
                fresh.addNewVar(name);
                mapping.put(name, 0);
		
		peekLocalsStack().add(name);
		return null;
	}
        
        @Override
        public Void visitAssertStmt(AssertStmtContext ctx) {
            super.visitExpr(ctx.condition);
            
            Assertion assertion = new Assertion(expression);
            ssa.addAssertion(assertion);
            expression = null;
            return null;
        }
        
        @Override
	public Void visitAssignStmt(AssignStmtContext ctx) {
            
            super.visitExpr(ctx.rhs);
            
            String variableName = ctx.lhs.ident.name.getText();
            Integer newValue = fresh.fresh(variableName);
            String ssaVariableName = variableName + newValue;
            mapping.put(variableName, newValue);
            
            
            Assignment assignment = new Assignment(ssaVariableName, expression);
            ssa.addAssignment(assignment);
            expression = null;
            return null;
	}
	
	/*@Override
	public Void visitEnsures(EnsuresContext ctx) {
		inEnsures = true;
		Void result = super.visitEnsures(ctx);
		inEnsures = false;
		return result;
	}*/
	
	/*@Override
	public Void visitResultExpr(ResultExprContext ctx) {
		return super.visitResultExpr(ctx);
	}*/

	/*@Override
	public Void visitOldExpr(parser.SimpleCParser.OldExprContext ctx) {
		return super.visitOldExpr(ctx);
	}*/
	
	/*@Override
	public Void visitCallStmt(CallStmtContext ctx) {
		String name = ctx.callee.getText();
		int numArgs = ctx.actuals.size();
                
		expectedProcedures.put(name, numArgs);
		return super.visitCallStmt(ctx);
	}*/
	
	/*@Override
	public Void visitVarref(VarrefContext ctx) {
		String name = ctx.ident.name.getText();
		return super.visitVarref(ctx);
	}*/

	/*private boolean isLocalVariable(String name) {
		boolean foundLocally = false;
		for(int i = localsStack.size() - 1; i >= 0; i--) {
			if(localsStack.get(i).contains(name)) {
				foundLocally = true;
				break;
			}
		}
		return foundLocally;
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

	/*@Override
	public Void visitHavocStmt(HavocStmtContext ctx) {
		return super.visitHavocStmt(ctx);
	}*/
        
        /* 
            Visitors for various expression types
        */
        
        @Override
        public Void visitTernExpr(TernExprContext ctx) {
            if(ctx.single != null) {
                visitLorExpr(ctx.single);
            }
            else{
                TernaryExpression ternaryExpr = null;
                
                visitLorExpr(ctx.args.get(0));
                Expression conditionalExpr = expression;
                expression = null;
                ternaryExpr = new TernaryExpression(conditionalExpr);
                int index = 1;
                while(index < ctx.args.size()) {
                    visitLorExpr(ctx.args.get(index));
                    Expression ifExpr = expression;
                    expression = null;
                    index++;
                    visitLorExpr(ctx.args.get(index));
                    Expression thenExpr = expression;
                    expression = null;
                    index++;
                    
                    ternaryExpr.addRemainingExpr(new Tuple(ifExpr, thenExpr));
                }
                
                expression = ternaryExpr;
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
                binExpr = new BinaryExpression(leftExpr);
                for(int i = 1; i < ctx.args.size(); i++){
                    visitLandExpr(ctx.args.get(i));
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.LOR);
                    Expression rightExpr = expression;
                    expression = null;
                    binExpr.addRemainingExpr(new Tuple(op, rightExpr));
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
                binExpr = new BinaryExpression(leftExpr);
                for(int i = 1; i < ctx.args.size(); i++){
                    visitBorExpr(ctx.args.get(i));
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.LAND);
                    Expression rightExpr = expression;
                    expression = null;
                    binExpr.addRemainingExpr(new Tuple(op, rightExpr));
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
                binExpr = new BinaryExpression(leftExpr);
                for(int i = 1; i < ctx.args.size(); i++){
                    visitBxorExpr(ctx.args.get(i));
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.BOR);
                    Expression rightExpr = expression;
                    expression = null;
                    binExpr.addRemainingExpr(new Tuple(op, rightExpr));
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
                binExpr = new BinaryExpression(leftExpr);
                for(int i = 1; i < ctx.args.size(); i++){
                    visitBandExpr(ctx.args.get(i));
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.BXOR);
                    Expression rightExpr = expression;
                    expression = null;
                    binExpr.addRemainingExpr(new Tuple(op, rightExpr));
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
                binExpr = new BinaryExpression(leftExpr);
                for(int i = 1; i < ctx.args.size(); i++){
                    visitEqualityExpr(ctx.args.get(i));
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.BAND);
                    Expression rightExpr = expression;
                    expression = null;
                    binExpr.addRemainingExpr(new Tuple(op, rightExpr));
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
                binExpr = new BinaryExpression(leftExpr);
                for(int i = 1; i < ctx.args.size(); i++){
                    String opString = ctx.ops.get(i-1).getText();
                    visitRelExpr(ctx.args.get(i));
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.findBySsaForm(opString));
                    Expression rightExpr = expression;
                    expression = null;
                    binExpr.addRemainingExpr(new Tuple(op, rightExpr));
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
                binExpr = new BinaryExpression(leftExpr);
                for(int i = 1; i < ctx.args.size(); i++){
                    String opString = ctx.ops.get(i-1).getText();
                    visitShiftExpr(ctx.args.get(i));
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.findBySsaForm(opString));
                    Expression rightExpr = expression;
                    expression = null;
                    binExpr.addRemainingExpr(new Tuple(op, rightExpr));
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
                BinaryExpression binExpr = null;
                
                visitAddExpr(ctx.args.get(0));
                Expression leftExpr = expression;
                expression = null;
                binExpr = new BinaryExpression(leftExpr);
                for(int i = 1; i < ctx.args.size(); i++){
                    String opString = ctx.ops.get(i-1).getText();
                    visitAddExpr(ctx.args.get(i));
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.findBySsaForm(opString));
                    Expression rightExpr = expression;
                    expression = null;
                    binExpr.addRemainingExpr(new Tuple(op, rightExpr));
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
                binExpr = new BinaryExpression(leftExpr);
                for(int i = 1; i < ctx.args.size(); i++){
                    String opString = ctx.ops.get(i-1).getText();
                    visitMulExpr(ctx.args.get(i));
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.findBySsaForm(opString));
                    Expression rightExpr = expression;
                    expression = null;
                    binExpr.addRemainingExpr(new Tuple(op, rightExpr));
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
                BinaryExpression binExpr = null;
                
                visitUnaryExpr(ctx.args.get(0));
                Expression leftExpr = expression;
                expression = null;
                binExpr = new BinaryExpression(leftExpr);
                for(int i = 1; i < ctx.args.size(); i++){
                    String opString = ctx.ops.get(i-1).getText();
                    visitUnaryExpr(ctx.args.get(i));
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.findBySsaForm(opString));
                    Expression rightExpr = expression;
                    expression = null;
                    binExpr.addRemainingExpr(new Tuple(op, rightExpr));
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
        
        /** No need to override atomExpr, since we just want to visit the children without no "side-effect" **/
        
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
            Integer variableIndex = mapping.get(variableName);
            String variableSsaName = variableName + variableIndex;
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
            ResultExpression resultExpr = new ResultExpression();
            expression = resultExpr;
            return null;
        }
        
        @Override
        public Void visitOldExpr(OldExprContext ctx) {
            String variableName = ctx.arg.ident.name.getText();
            OldExpression oldExpr = new OldExpression(variableName);
            return null;
        }
        
}
