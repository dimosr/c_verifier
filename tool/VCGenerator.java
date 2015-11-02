package tool;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.Map;
import java.util.Set;
import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.ProcedureDeclContext;
import util.assertions.Assertion;
import util.assignments.Assignment;

public class VCGenerator {

	private ProcedureDeclContext proc;
        
        private VerifierVisitor visitor;
	
	public VCGenerator(ProcedureDeclContext proc, VerifierVisitor visitor) {
		this.proc = proc;
                this.visitor = visitor;
	}
	
	public StringBuilder generateVC() throws FileNotFoundException {
                visitor.visitProcedureDecl(proc);
                FreshStructure fresh = visitor.getFresh();
                SsaRepresentation ssa = visitor.getSsa();
            
                try (PrintStream out = new PrintStream(new FileOutputStream("ssa_format.txt"))) {
                    out.print(ssa.getText(fresh));
                }
                
                try (PrintStream out = new PrintStream(new FileOutputStream("pseudo_smt.txt"))) {
                    out.print(ssa.translateToPseudoSmt(fresh));
                }
                
		StringBuilder result = new StringBuilder("(set-logic QF_BV)\n");
		result.append("(set-option :produce-models true)\n");
		result.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
		result.append("(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p (_ bv0 32)) false true))\n");
		
                result.append(ssa.translateToSmtFormula(fresh));
		
		result.append("\n(check-sat)\n");
                
                try (PrintStream out = new PrintStream(new FileOutputStream("smt_format.txt"))) {
                    out.print(result);
                }
                
		return result;
	}

}
