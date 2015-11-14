package tool;
import tool.verif.structs.SsaRepresentation;
import tool.verif.structs.FreshStructure;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import util.program.Procedure;
import util.program.Program;

public class VCGenerator {

	private Procedure procedure;
        private Program program;
        
        private VerifierVisitor verifierVisitor;
        private boolean debugMode;
	
	public VCGenerator(Program program, Procedure procedureUnderVerification, VerifierVisitor verifierVisitor, boolean debugMode) {
		this.procedure = procedureUnderVerification;
                this.program = program;
                this.verifierVisitor = verifierVisitor;
                this.debugMode = debugMode;
	}
	
	public SsaRepresentation generateVC() throws FileNotFoundException, IOException {
                verifierVisitor.visitProcedure(procedure);
                FreshStructure fresh = verifierVisitor.getFreshStructure();
                SsaRepresentation ssa = verifierVisitor.getSsa();
                
		StringBuilder result = new StringBuilder("(set-logic QF_BV)\n");
		result.append("(set-option :produce-models true)\n");
		result.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
		result.append("(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p (_ bv0 32)) false true))\n");
		
                result.append(ssa.translateToSmtFormula(fresh, true));
                
                if(debugMode) {
                    String ssaFormatFile = "output" + File.separator + procedure.procedureName + "_ssa_format.txt";
                    try (PrintStream out = new PrintStream(new FileOutputStream(ssaFormatFile))) {
                        out.print(ssa.getText(fresh));
                    }
                
                    String pseudoSmtFile = "output" + File.separator + procedure.procedureName + "_pseudo_smt.txt";
                    try (PrintStream out = new PrintStream(new FileOutputStream(pseudoSmtFile))) {
                        out.print(ssa.translateToPseudoSmt(fresh));
                    }
                
                    String smtFile = "output" + File.separator + procedure.procedureName + "_smt_format.txt";
                    try (PrintStream out = new PrintStream(new FileOutputStream(smtFile))) {
                        out.print(result);
                    }
                }
                
                ssa.vc = result.toString();
		return ssa;
	}
        
        

}
