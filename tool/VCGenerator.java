package tool;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.util.Map;
import parser.SimpleCParser.ProcedureDeclContext;
import util.assertions.Assertion;
import util.assignments.Assignment;

public class VCGenerator {

	private ProcedureDeclContext proc;
        
        private VerifierVisitor verifierVisitor;
	
	public VCGenerator(ProcedureDeclContext proc) {
		this.proc = proc;
                verifierVisitor = new VerifierVisitor();
		// TODO: You will probably find it useful to add more fields and constructor arguments
	}
	
	public StringBuilder generateVC() throws FileNotFoundException {
                verifierVisitor.visitProcedureDecl(proc);
                FreshStructure fresh = verifierVisitor.getFresh();
                SsaRepresentation ssa = verifierVisitor.getSsa();
            
                System.out.print(ssa.getText(fresh));
            
		StringBuilder result = new StringBuilder("(set-logic QF_BV)\n");
		result.append("(set-option :produce-models true)\n");
		result.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
		result.append("(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p (_ bv0 32)) false true))\n");
		
                //result.append(ssa.translateToSmt(fresh));
		
		result.append("\n(check-sat)\n");
                System.out.println(result);
		return result;
	}

}
