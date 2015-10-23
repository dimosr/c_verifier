package tool;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.antlr.v4.runtime.Token;

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
import util.expressions.Expression;


public class VerifierVisitor extends SimpleCBaseVisitor<Void> {
        private Map<String, Integer> expectedProcedures = new HashMap<>();

	private Map<String, Integer> actualProcedures = new HashMap<>();

	private Set<String> globals = new HashSet<>();

	private HashSet<String> parameters = null;
	
	private List<Set<String>> localsStack = new ArrayList<>();
	
	private boolean inEnsures = false;
        
        private SsaRepresentation ssa;
        
        private FreshStructure fresh;
        
        private Map<String, Integer> mapping;
        
        private Expression expression;
        
        public SsaRepresentation getSsa(){
            return ssa;
        }
        
        public FreshStructure getFresh(){
            return fresh;
        }

	/*@Override
	public Void visitProgram(ProgramContext ctx) {
		for(VarDeclContext varDecl : ctx.globals) {
			globals.add(varDecl.ident.name.getText());
		}
		
		for(ProcedureDeclContext proc : ctx.procedures) {
			visit(proc);
		}
		return null;
	}*/
	
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
            parameters = new HashSet<>();
            pushLocalsStack();
            for(FormalParamContext fp : ctx.formals) {
		String formalParamName = fp.ident.name.getText();
		parameters.add(formalParamName);
                fresh.addNewVar(formalParamName);
                mapping.put(formalParamName, 0);
            }
            Void result = super.visitProcedureDecl(ctx);
            popLocalsStack();
            parameters = null;
            return result;
	}
        
        @Override
	public Void visitVarDecl(VarDeclContext ctx) {
		String name = ctx.ident.name.getText();
                fresh.addNewVar(name);
                mapping.put(name, 0);
		
		peekLocalsStack().add(name);
		return super.visitVarDecl(ctx);
	}
        
        @Override
        public Void visitAssertStmt(AssertStmtContext ctx) {
            expression = new Expression();
            super.visitExpr(ctx.condition);
            
            Assertion assertion = new Assertion(expression);
            ssa.addAssertion(assertion);
            expression = null;
            return null;
        }
        
        @Override
	public Void visitAssignStmt(AssignStmtContext ctx) {
            expression = new Expression();
            
            String variableName = ctx.lhs.ident.name.getText();
            Integer newValue = fresh.fresh(variableName);
            variableName = variableName + newValue;
            mapping.put(variableName, newValue);
            super.visitExpr(ctx.rhs);
            
            Assignment assignment = new Assignment(variableName, expression);
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
                visitLorExpr(ctx.args.get(0));
                int index = 1;
                while(index < ctx.args.size()) {
                    expression.addElement(" ? ");
                    visitLorExpr(ctx.args.get(index));
                    index++;
                    expression.addElement(" : ");
                    visitLorExpr(ctx.args.get(index));
                    index++;
                }
            }
            return null;
        }
        
        @Override
        public Void visitLorExpr(LorExprContext ctx) {
            if(ctx.single != null) {
                visitLandExpr(ctx.single);
            }
            else {
                visitLandExpr(ctx.args.get(0)); 
                for(int i = 1; i < ctx.args.size(); i++){
                    expression.addElement(" || ");
                    visitLandExpr(ctx.args.get(i));
                }
            }
            return null;
        }
        
        @Override
        public Void visitLandExpr(LandExprContext ctx) {
            if(ctx.single != null) {
                visitBorExpr(ctx.single);
            }
            else {
                visitBorExpr(ctx.args.get(0)); 
                for(int i = 1; i < ctx.args.size(); i++){
                    expression.addElement(" && ");
                    visitBorExpr(ctx.args.get(i));
                }
            }
            return null;
        }
        
        @Override
        public Void visitBorExpr(BorExprContext ctx) {
            if(ctx.single != null) {
                visitBxorExpr(ctx.single);
            }
            else {
                visitBxorExpr(ctx.args.get(0)); 
                for(int i = 1; i < ctx.args.size(); i++){
                    expression.addElement(" | ");
                    visitBxorExpr(ctx.args.get(i));
                }
            }
            return null;
        }
        
        @Override
        public Void visitBxorExpr(BxorExprContext ctx) {
            if(ctx.single != null) {
                visitBandExpr(ctx.single);
            }
            else {
                visitBandExpr(ctx.args.get(0)); 
                for(int i = 1; i < ctx.args.size(); i++){
                    expression.addElement(" ^ ");
                    visitBandExpr(ctx.args.get(i));
                }
            }
            return null;
        }
        
        @Override
        public Void visitBandExpr(BandExprContext ctx) {
            if(ctx.single != null) {
                visitEqualityExpr(ctx.single);
            }
            else{
                visitEqualityExpr(ctx.args.get(0));
                for(int i = 1; i < ctx.args.size(); i++){
                    expression.addElement(" & ");
                    visitEqualityExpr(ctx.args.get(i));
                }
            }
            return null;
        }
        
        @Override
        public Void visitEqualityExpr(EqualityExprContext ctx) {
            if(ctx.single != null) {
                visitRelExpr(ctx.single);
            }
            else {
                visitRelExpr(ctx.args.get(0));
                for(int i = 1; i < ctx.args.size(); i++){
                    expression.addElement(" " + ctx.ops.get(i-1).getText() + " ");
                    visitRelExpr(ctx.args.get(i));
                }
            }
            return null;
        }
        
        @Override
        public Void visitRelExpr(RelExprContext ctx) {
            if(ctx.single != null) {
                visitShiftExpr(ctx.single);
            }
            else {
                visitShiftExpr(ctx.args.get(0));
                for(int i = 1; i < ctx.args.size(); i++){
                    expression.addElement(" " + ctx.ops.get(i-1).getText() + " ");
                    visitShiftExpr(ctx.args.get(i));
                }
            }
            return null;
        }
        
        @Override
        public Void visitShiftExpr(ShiftExprContext ctx) {
            if(ctx.single != null) {
                visitAddExpr(ctx.single);
            }
            else {
                visitAddExpr(ctx.args.get(0));
                for(int i = 1; i < ctx.args.size(); i++){
                    expression.addElement(" " + ctx.ops.get(i-1).getText() + " ");
                    visitAddExpr(ctx.args.get(i));
                }
            }
            return null;
        }
        
        @Override
        public Void visitAddExpr(AddExprContext ctx) {
            if(ctx.single != null) {
                visitMulExpr(ctx.single);
            }
            else {
                visitMulExpr(ctx.args.get(0));
                for(int i = 1; i < ctx.args.size(); i++){
                    expression.addElement(" " + ctx.ops.get(i-1).getText() + " ");
                    visitMulExpr(ctx.args.get(i));
                }
            }
            return null;
        }
        
        @Override
        public Void visitMulExpr(MulExprContext ctx) {
            if(ctx.single != null) {
                visitUnaryExpr(ctx.single);
            }
            else {
                visitUnaryExpr(ctx.args.get(0));
                for(int i = 1; i < ctx.args.size(); i++){
                    expression.addElement(" " + ctx.ops.get(i-1).getText() + " ");
                    visitUnaryExpr(ctx.args.get(i));
                }
            }
            return null;
        }
        
        @Override
        public Void visitUnaryExpr(UnaryExprContext ctx) {
            for(Token op : ctx.ops){
                expression.addElement(" " + op.getText() + " ");
            }
            visitAtomExpr(ctx.arg);
            return null;
        }
        
        /** No need to override atomExpr, since we just want to visit the children without no "side-effect" **/
        
        @Override
        public Void visitNumberExpr(NumberExprContext ctx) {
            expression.addElement(ctx.number.getText());
            return visitNumberExpr(ctx);
        }
        
        @Override
	public Void visitVarrefExpr(VarrefExprContext ctx) {
            String variableName = ctx.var.ident.name.getText();
            Integer variableIndex = mapping.get(variableName);
            expression.addElement(variableName + variableIndex);
            return visitVarrefExpr(ctx);
        }
        
        @Override
        public Void visitParenExpr(ParenExprContext ctx) {
            expression.addElement(" ( ");
            visitParenExpr(ctx);
            expression.addElement(" ) ");
            return null;
        }
        
        @Override
        public Void visitResultExpr(ResultExprContext ctx) {
            expression.addElement(ctx.resultTok.getText());
            return null;
        }
        
        @Override
        public Void visitOldExpr(OldExprContext ctx) {
            expression.addElement(ctx.oldTok.getText());
            expression.addElement(ctx.arg.ident.name.getText());
            return visitVarref(ctx.arg);
        }
        
}
