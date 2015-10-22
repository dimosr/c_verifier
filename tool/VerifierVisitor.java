package tool;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.AssignStmtContext;
import parser.SimpleCParser.BlockStmtContext;
import parser.SimpleCParser.CallStmtContext;
import parser.SimpleCParser.EnsuresContext;
import parser.SimpleCParser.FormalParamContext;
import parser.SimpleCParser.HavocStmtContext;
import parser.SimpleCParser.ProcedureDeclContext;
import parser.SimpleCParser.ProgramContext;
import parser.SimpleCParser.ResultExprContext;
import parser.SimpleCParser.VarDeclContext;
import parser.SimpleCParser.VarrefContext;


public class VerifierVisitor extends SimpleCBaseVisitor<Void> {
        private Map<String, Integer> expectedProcedures = new HashMap<>();

	private Map<String, Integer> actualProcedures = new HashMap<>();

	private Set<String> globals = new HashSet<>();

	private HashSet<String> parameters = null;
	
	private List<Set<String>> localsStack = new ArrayList<>();
	
	private boolean inEnsures = false;

	@Override
	public Void visitProgram(ProgramContext ctx) {
		for(VarDeclContext varDecl : ctx.globals) {
			globals.add(varDecl.ident.name.getText());
		}
		
		for(ProcedureDeclContext proc : ctx.procedures) {
			visit(proc);
		}
		return null;
	}

	@Override
	public Void visitVarDecl(VarDeclContext ctx) {
		String name = ctx.ident.name.getText();
		
		peekLocalsStack().add(name);
		return super.visitVarDecl(ctx);
	}
	
	@Override
	public Void visitBlockStmt(BlockStmtContext ctx) {
		pushLocalsStack();
		Void result = super.visitBlockStmt(ctx);
		popLocalsStack();
		return result;
	}
	
	@Override
	public Void visitProcedureDecl(ProcedureDeclContext ctx) {
		String name = ctx.name.getText();

		actualProcedures.put(name, ctx.formals.size());
		parameters = new HashSet<>();
		pushLocalsStack();
		for(FormalParamContext fp : ctx.formals) {
			String formalParamName = fp.ident.name.getText();
			parameters.add(formalParamName);
		}
		Void result = super.visitProcedureDecl(ctx);
		popLocalsStack();
		parameters = null;
		return result;
	}
	
	@Override
	public Void visitEnsures(EnsuresContext ctx) {
		inEnsures = true;
		Void result = super.visitEnsures(ctx);
		inEnsures = false;
		return result;
	}
	
	@Override
	public Void visitResultExpr(ResultExprContext ctx) {
		return super.visitResultExpr(ctx);
	}

	@Override
	public Void visitOldExpr(parser.SimpleCParser.OldExprContext ctx) {
		return super.visitOldExpr(ctx);
	}
	
	@Override
	public Void visitCallStmt(CallStmtContext ctx) {
		String name = ctx.callee.getText();
		int numArgs = ctx.actuals.size();
                
		expectedProcedures.put(name, numArgs);
		return super.visitCallStmt(ctx);
	}
	
	@Override
	public Void visitVarref(VarrefContext ctx) {
		String name = ctx.ident.name.getText();
		return super.visitVarref(ctx);
	}

	private boolean isLocalVariable(String name) {
		boolean foundLocally = false;
		for(int i = localsStack.size() - 1; i >= 0; i--) {
			if(localsStack.get(i).contains(name)) {
				foundLocally = true;
				break;
			}
		}
		return foundLocally;
	}
		
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
	public Void visitAssignStmt(AssignStmtContext ctx) {
		return super.visitAssignStmt(ctx);
	}

	@Override
	public Void visitHavocStmt(HavocStmtContext ctx) {
		return super.visitHavocStmt(ctx);
	}
	
}
