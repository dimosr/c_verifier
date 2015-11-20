package tool;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.antlr.v4.runtime.Token;
import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.*;
import util.expressions.BinaryExpression;
import util.expressions.ConstantExpression;

import util.expressions.Expression;
import util.expressions.ExpressionType;
import util.expressions.OldExpression;
import util.expressions.ParenthesisExpression;
import util.expressions.ResultExpression;
import util.expressions.TernaryExpression;
import util.expressions.UnaryExpression;
import util.expressions.VarRefExpression;
import util.operators.BinaryOperator;
import util.operators.BinaryOperatorType;
import util.operators.UnaryOperator;
import util.operators.UnaryOperatorType;
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

public class GeneratorVisitor extends SimpleCBaseVisitor<Void> {
        
        private Expression expressionHolder;
        private Statement statementHolder;
        private Procedure procedureHolder;
        
        private String prePostConditionType;
        private String invariantType;
        
        private Program program;
        private String procedureName;
        private Map<String, Set<String>> calledBy;
        private boolean hasLoops;
        
        private List<String> procedureLocalVariables;
        
        
        public Program getProgram() {
            return this.program;
        }

        @Override
        public Void visitProgram(ProgramContext ctx) {
            Set<String> globalVariables = new HashSet();
            calledBy = new HashMap();
            hasLoops = false;
            for(VarDeclContext varDecl : ctx.globals) {
		globalVariables.add(varDecl.ident.name.getText());
            }
            
            Map<String, Procedure> procedures = new HashMap();
            for(ProcedureDeclContext procedureCtx : ctx.procedures) {
                visitProcedureDecl(procedureCtx);
                procedures.put(procedureHolder.procedureName, procedureHolder);
            }
            
            program = new Program(globalVariables, procedures, calledBy, hasLoops);
            return null;
        }
        
        @Override
	public Void visitProcedureDecl(ProcedureDeclContext ctx) {
            procedureName = ctx.name.getText();
            List<String> parameters = new ArrayList();
            List<RequireCondition> preConditions = new ArrayList();
            List<EnsureCondition> postConditions = new ArrayList();
            procedureLocalVariables = new ArrayList();
            List<Statement> statements = new ArrayList();
            Expression returnExpression = null;
            
            /** Procedure Parameters retrieval **/
            for(FormalParamContext fp : ctx.formals) {
                String formalParamName = fp.ident.name.getText();
                parameters.add(formalParamName);
            }
            
            /** Procedure pre-conditions retrieval **/
            for(PrepostContext preOrPostCondition : ctx.contract){
                super.visitPrepost(preOrPostCondition);
                RequireCondition require = null;
                if(prePostConditionType.equals("requires") || prePostConditionType.equals("candidateRequires")) {
                    require = new RequireCondition(expressionHolder);
                    if(prePostConditionType.equals("candidateRequires")) {
                        require.setAsCandidate();
                    }
                    preConditions.add(require);
                }
            }
            
            /** Procedure statements retrieval **/
            for(StmtContext statementCtx : ctx.stmts) {
                visitStmt(statementCtx);
                statements.add(this.statementHolder);
            }
            
            /** Procedure post-conditions retrieval **/
            for(PrepostContext preOrPostCondition : ctx.contract){
                super.visitPrepost(preOrPostCondition);
                EnsureCondition ensure = null;
                if(prePostConditionType.equals("ensures") || prePostConditionType.equals("candidateEnsures")) {
                    ensure = new EnsureCondition(expressionHolder);
                    if(prePostConditionType.equals("candidateEnsures")) {
                        ensure.setAsCandidate();
                    }
                    postConditions.add(ensure);
                }
            }
            
            /** Procedure return expression retrieval **/
            super.visitExpr(ctx.returnExpr);
            returnExpression = this.expressionHolder;
            
            procedureHolder = new Procedure(procedureName, parameters, preConditions, postConditions, procedureLocalVariables, statements, returnExpression);
            return null; 
        }
        
        @Override 
        public Void visitRequires(RequiresContext ctx) {
            visitExpr(ctx.condition);
            prePostConditionType = "requires";
            return null;
        }
        
        @Override 
        public Void visitEnsures(EnsuresContext ctx) {
            visitExpr(ctx.condition);
            prePostConditionType = "ensures";
            return null;
        }
        
        @Override 
        public Void visitCandidateRequires(CandidateRequiresContext ctx) {
            visitExpr(ctx.condition);
            prePostConditionType = "candidateRequires";
            return null;
        }
        
        @Override 
        public Void visitCandidateEnsures(CandidateEnsuresContext ctx) {
            visitExpr(ctx.condition);
            prePostConditionType = "candidateEnsures";
            return null;
        }
        
        //this method will only be called for local variables!!
        @Override
	public Void visitVarDecl(VarDeclContext ctx) {
            String variableName = ctx.ident.name.getText();
            procedureLocalVariables.add(variableName);
            VarDeclStatement VarDeclStmt = new VarDeclStatement(variableName);
            statementHolder = VarDeclStmt;
            return null;
        }
        
        @Override
        public Void visitAssertStmt(AssertStmtContext ctx) {
            super.visitExpr(ctx.condition);
            AssertStatement assertStmt = new AssertStatement(this.expressionHolder);
            statementHolder = assertStmt;
            return null;
        }
        
        @Override
	public Void visitAssignStmt(AssignStmtContext ctx) {
            String variableName = ctx.lhs.ident.name.getText();
            super.visitExpr(ctx.rhs);
            AssignStatement assignStmt = new AssignStatement(variableName, this.expressionHolder);
            statementHolder = assignStmt;
            return null;
        }
        
        @Override
        public Void visitBlockStmt(BlockStmtContext ctx) {
            List<Statement> statements = new ArrayList();
            for(StmtContext stmtCtx : ctx.stmts) {
                visitStmt(stmtCtx);
                statements.add(this.statementHolder);
            }
            this.statementHolder = new BlockStatement(statements);
            return null;
        }
        
        @Override
        public Void visitIfStmt(IfStmtContext ctx) {
            visitExpr(ctx.condition);
            Expression ifCondition = this.expressionHolder;
            visitBlockStmt(ctx.thenBlock);
            BlockStatement ifBlock = (BlockStatement) this.statementHolder;
            BlockStatement elseBlock = null;
            if(ctx.elseBlock != null) {
                visitBlockStmt(ctx.elseBlock);
                elseBlock = (BlockStatement) this.statementHolder;
            }
            
            IfStatement ifStmt = null;
            if(ctx.elseBlock == null)
                ifStmt = new IfStatement(ifCondition, ifBlock);
            else
                ifStmt = new IfStatement(ifCondition, ifBlock, elseBlock);
            
            statementHolder = ifStmt;
            return null;
        }
        
        @Override
	public Void visitHavocStmt(HavocStmtContext ctx) {
            String variableName = ctx.var.ident.getText();
            HavocStatement havocStmt = new HavocStatement(variableName);
            statementHolder = havocStmt;
            return null;
        }
        
        @Override
        public Void visitAssumeStmt(AssumeStmtContext ctx) {
            visitExpr(ctx.condition);
            AssumeStatement assumeStmt = new AssumeStatement(this.expressionHolder);
            statementHolder = assumeStmt;
            return null;
        }
        
        @Override
        public Void visitTernExpr(TernExprContext ctx) {
            if(ctx.single != null) {
                visitLorExpr(ctx.single);
            }
            else{
                TernaryExpression ternaryExpression = null;
                if(ctx.args.size() == 3) {
                    visitLorExpr(ctx.args.get(0));
                    Expression condExpr = expressionHolder;
                    visitLorExpr(ctx.args.get(1));
                    Expression ifExpr = expressionHolder;
                    visitLorExpr(ctx.args.get(2));
                    Expression elseExpr = expressionHolder;
                    ternaryExpression = new TernaryExpression(condExpr, ifExpr, elseExpr);
                }
                else {
                    long elementsSum = ctx.args.size();
                    visitLorExpr(ctx.args.get(0));
                    Expression condExpr = expressionHolder;
                    visitLorExpr(ctx.args.get(1));
                    Expression ifExpr = expressionHolder;
                    List<LorExprContext> sublist = ctx.args.subList(2, (int) elementsSum);
                    ctx.args = sublist;
                    visitTernExpr(ctx);
                    Expression elseExpr = expressionHolder;
                    
                    ternaryExpression = new TernaryExpression(condExpr, ifExpr, elseExpr);
                }
                expressionHolder = ternaryExpression;
            }
            return null;
        }
        
        @Override
        public Void visitLorExpr(LorExprContext ctx) {
            if(ctx.single != null) {
                visitLandExpr(ctx.single);
            }
            else {
                Expression binExpr = null;
                
                visitLandExpr(ctx.args.get(0));
                binExpr = expressionHolder;
                if( ( binExpr.getType() == ExpressionType.CONSTANT ) && (((ConstantExpression)binExpr).intValue == "1") ) {
                    return null;    //short-circuit
                }
                expressionHolder = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.LOR);
                    visitLandExpr(ctx.args.get(i));
                    Expression rightExpr = expressionHolder;
                    expressionHolder = null;
                    
                    binExpr = new BinaryExpression(binExpr, op, rightExpr);
                }
                
                expressionHolder = binExpr;
            }
            return null;
        }
        
        @Override
        public Void visitLandExpr(LandExprContext ctx) {
            if(ctx.single != null) {
                visitBorExpr(ctx.single);
            }
            else {
                Expression binExpr = null;
                
                visitBorExpr(ctx.args.get(0));
                binExpr = expressionHolder;
                if( ( binExpr.getType() == ExpressionType.CONSTANT ) && (((ConstantExpression)binExpr).intValue == "0") ) {
                    return null;    //short-circuit
                }
                expressionHolder = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.LAND);
                    visitBorExpr(ctx.args.get(i));
                    Expression rightExpr = expressionHolder;
                    expressionHolder = null;
                    
                    binExpr = new BinaryExpression(binExpr, op, rightExpr);
                }
                
                expressionHolder = binExpr;
            }
            return null;
        }
        
        @Override
        public Void visitBorExpr(BorExprContext ctx) {
            if(ctx.single != null) {
                visitBxorExpr(ctx.single);
            }
            else {
                Expression binExpr = null;
                
                visitBxorExpr(ctx.args.get(0));
                binExpr = expressionHolder;
                expressionHolder = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.BOR);
                    visitBxorExpr(ctx.args.get(i));
                    Expression rightExpr = expressionHolder;
                    expressionHolder = null;
                    
                    binExpr = new BinaryExpression(binExpr, op, rightExpr);
                }
                
                expressionHolder = binExpr;
            }
            return null;
        }
        
        @Override
        public Void visitBxorExpr(BxorExprContext ctx) {
            if(ctx.single != null) {
                visitBandExpr(ctx.single);
            }
            else {
                Expression binExpr = null;
                
                visitBandExpr(ctx.args.get(0));
                binExpr = expressionHolder;
                expressionHolder = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.BXOR);
                    visitBandExpr(ctx.args.get(i));
                    Expression rightExpr = expressionHolder;
                    expressionHolder = null;
                    
                    binExpr = new BinaryExpression(binExpr, op, rightExpr);
                }
                
                expressionHolder = binExpr;
            }
            return null;
        }
        
        @Override
        public Void visitBandExpr(BandExprContext ctx) {
            if(ctx.single != null) {
                visitEqualityExpr(ctx.single);
            }
            else{
                Expression binExpr = null;
                
                visitEqualityExpr(ctx.args.get(0));
                binExpr = expressionHolder;
                expressionHolder = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.BAND);
                    visitEqualityExpr(ctx.args.get(i));
                    Expression rightExpr = expressionHolder;
                    expressionHolder = null;
                    
                    binExpr = new BinaryExpression(binExpr, op, rightExpr);
                }
                
                expressionHolder = binExpr;
            }
            return null;
        }
        
        @Override
        public Void visitEqualityExpr(EqualityExprContext ctx) {
            if(ctx.single != null) {
                visitRelExpr(ctx.single);
            }
            else {
                Expression binExpr = null;
                
                visitRelExpr(ctx.args.get(0));
                binExpr = expressionHolder;
                expressionHolder = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    String opString = ctx.ops.get(i-1).getText();
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.findBySsaForm(opString));
                    visitRelExpr(ctx.args.get(i));
                    Expression rightExpr = expressionHolder;
                    expressionHolder = null;
                    
                    binExpr = new BinaryExpression(binExpr, op, rightExpr);
                }
                
                expressionHolder = binExpr;
            }
            return null;
        }
        
        @Override
        public Void visitRelExpr(RelExprContext ctx) {
            if(ctx.single != null) {
                visitShiftExpr(ctx.single);
            }
            else {
                Expression binExpr = null;
                
                visitShiftExpr(ctx.args.get(0));
                binExpr = expressionHolder;
                expressionHolder = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    String opString = ctx.ops.get(i-1).getText();
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.findBySsaForm(opString));
                    visitShiftExpr(ctx.args.get(i));
                    Expression rightExpr = expressionHolder;
                    expressionHolder = null;
                    
                    binExpr = new BinaryExpression(binExpr, op, rightExpr);
                }
                
                expressionHolder = binExpr;
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
                binExpr = expressionHolder;
                expressionHolder = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    String opString = ctx.ops.get(i-1).getText();
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.findBySsaForm(opString));
                    visitAddExpr(ctx.args.get(i));
                    Expression rightExpr = expressionHolder;
                    expressionHolder = null;
                    
                    if(op.opType == BinaryOperatorType.LEFT_SHIFT || op.opType == BinaryOperatorType.RIGHT_SHIFT) {
                        BinaryExpression shiftExpr = new BinaryExpression(binExpr, op, rightExpr);
                        BinaryExpression checkZeroExpr = new BinaryExpression(rightExpr, new BinaryOperator(BinaryOperatorType.GREATER), new ConstantExpression("32"));
                        ParenthesisExpression parenthesisExpr = new ParenthesisExpression(new TernaryExpression(checkZeroExpr, new ConstantExpression("0"), shiftExpr));
                        binExpr = parenthesisExpr;
                    }
                    else{
                        binExpr = new BinaryExpression(binExpr, op, rightExpr);
                    }
                }
                
                expressionHolder = binExpr;
            }
            return null;
        }
        
        @Override
        public Void visitAddExpr(AddExprContext ctx) {
            if(ctx.single != null) {
                visitMulExpr(ctx.single);
            }
            else {
                Expression binExpr = null;
                
                visitMulExpr(ctx.args.get(0));
                binExpr = expressionHolder;
                expressionHolder = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    String opString = ctx.ops.get(i-1).getText();
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.findBySsaForm(opString));
                    visitMulExpr(ctx.args.get(i));
                    Expression rightExpr = expressionHolder;
                    expressionHolder = null;
                    
                    binExpr = new BinaryExpression(binExpr, op, rightExpr);
                }
                
                expressionHolder = binExpr;
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
                binExpr = expressionHolder;
                expressionHolder = null;
                for(int i = 1; i < ctx.args.size(); i++){
                    String opString = ctx.ops.get(i-1).getText();
                    BinaryOperator op = new BinaryOperator(BinaryOperatorType.findBySsaForm(opString));
                    visitUnaryExpr(ctx.args.get(i));
                    Expression rightExpr = expressionHolder;
                    expressionHolder = null;
                    
                    if(op.opType == BinaryOperatorType.DIV || op.opType == BinaryOperatorType.MOD) {
                        BinaryExpression divExpr = new BinaryExpression(binExpr, op, rightExpr);
                        BinaryExpression checkZeroExpr = new BinaryExpression(rightExpr, new BinaryOperator(BinaryOperatorType.EQUALS), new ConstantExpression("0"));
                        ParenthesisExpression parenthesisExpr = new ParenthesisExpression(new TernaryExpression(checkZeroExpr, binExpr, divExpr));
                        binExpr = parenthesisExpr;
                    }
                    else{
                        binExpr = new BinaryExpression(binExpr, op, rightExpr);
                    }
                }
                
                expressionHolder = binExpr;
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
                Expression expr = expressionHolder;
                expressionHolder = null;
                unaryExpr = new UnaryExpression(expr);
                
                
                for(Token op : ctx.ops){
                    String opString = op.getText();
                    UnaryOperator operator = new UnaryOperator(UnaryOperatorType.findBySsaForm(opString));
                    unaryExpr.addOperator(operator);
                }
                
                expressionHolder = unaryExpr;
            }
            return null;
        }
        
        @Override
        public Void visitNumberExpr(NumberExprContext ctx) {
            String value = ctx.number.getText();
            ConstantExpression constantExpr = new ConstantExpression(value);
            expressionHolder = constantExpr;
            return null;
        }
        
        @Override
	public Void visitVarrefExpr(VarrefExprContext ctx) {
            String variableName = ctx.var.ident.name.getText();
            VarRefExpression varRefExpr = new VarRefExpression(variableName);
            expressionHolder = varRefExpr;
            return null;
        }
        
        @Override
        public Void visitParenExpr(ParenExprContext ctx) {
            visitExpr(ctx.arg);
            Expression innerExpr = expressionHolder;
            expressionHolder = null;
            ParenthesisExpression parenExpr = new ParenthesisExpression(innerExpr);
            expressionHolder = parenExpr;
            return null;
        }
        
        @Override
        public Void visitResultExpr(ResultExprContext ctx) {
            expressionHolder = new ResultExpression();
            return null;
        }
        
        @Override
        public Void visitOldExpr(OldExprContext ctx) {
            String variableName = ctx.arg.ident.name.getText();
            OldExpression oldExpr = new OldExpression(variableName);
            expressionHolder = oldExpr;
            return null;
        }
        
        @Override
        public Void visitCallStmt(CallStmtContext ctx) {
            String variableName = ctx.lhs.ident.name.getText();
            String calledProcedureName = ctx.callee.getText();
            List<Expression> parameters = new ArrayList();
            for(ExprContext exprCtx : ctx.actuals) {
                visitExpr(exprCtx);
                parameters.add(expressionHolder);
            }
            CallStatement callStmt = new CallStatement(variableName, calledProcedureName, parameters);
            statementHolder = callStmt;
            
            if(!calledBy.containsKey(calledProcedureName)) {
                Set<String> callers = new HashSet();
                callers.add(procedureName);
                calledBy.put(calledProcedureName, callers);
            }
            else {
                 Set<String> callers = calledBy.get(calledProcedureName);
                 callers.add(procedureName);
            }
           
            return null;
        }
        
        @Override
        public Void visitWhileStmt(WhileStmtContext ctx) {
            hasLoops = true;
            visitExpr(ctx.condition);
            Expression loopCondition = expressionHolder;
            
            List<Invariant> invariants = new ArrayList();
            for(LoopInvariantContext loopInvCtx : ctx.invariantAnnotations) {
                visitLoopInvariant(loopInvCtx);
                Invariant invariant = new Invariant(expressionHolder);
                if(invariantType.equals("candidate")) {
                    invariant.setAsCandidate();
                }
                invariants.add(invariant);
            }
            
            visitBlockStmt(ctx.body);
            BlockStatement loopBody = (BlockStatement) statementHolder;
            
            WhileStatement whileStmt = new WhileStatement(loopCondition, invariants, loopBody);
            statementHolder = whileStmt;
            return null;
        }
        
        @Override
        public Void visitInvariant(InvariantContext ctx) {
            invariantType = "regular";
            visitExpr(ctx.condition);
            return null;
        }
        
        @Override
        public Void visitCandidateInvariant(CandidateInvariantContext ctx) {
            invariantType = "candidate";
            visitExpr(ctx.condition);
            return null;
        }
}
