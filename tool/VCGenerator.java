package tool;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.PrintStream;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.Map;
import java.util.Set;
import parser.SimpleCBaseVisitor;
import parser.SimpleCParser.ProcedureDeclContext;
import util.program.Assertion;
import util.program.Assignment;
import util.program.Procedure;
import util.program.Program;

public class VCGenerator {
    
        private static final boolean DEBUG_MODE = true;

	private Procedure procedure;
        private Program program;
        
        private VerifierVisitor verifierVisitor;
	
	public VCGenerator(Program program, Procedure procedureUnderVerification, VerifierVisitor verifierVisitor) {
		this.procedure = procedureUnderVerification;
                this.program = program;
                this.verifierVisitor = verifierVisitor;
	}
	
	public StringBuilder generateVC() throws FileNotFoundException, IOException {
                verifierVisitor.visitProcedure(procedure);
                FreshStructure fresh = verifierVisitor.getFreshStructure();
                SsaRepresentation ssa = verifierVisitor.getSsa();
                
		StringBuilder result = new StringBuilder("(set-logic QF_BV)\n");
		result.append("(set-option :produce-models true)\n");
		result.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
		result.append("(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p (_ bv0 32)) false true))\n");
		
                result.append(ssa.translateToSmtFormula(fresh));
		
		result.append("\n(check-sat)\n");
                
                if(DEBUG_MODE) {
                    deleteDirectory(new File("output"));
                    Files.createDirectory(Paths.get("output"));
                    
                
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
                
		return result;
	}
        
        static public boolean deleteDirectory(File path) {
            if( path.exists() ) {
                File[] files = path.listFiles();
                for(int i=0; i<files.length; i++) {
                    if(files[i].isDirectory())
                        deleteDirectory(files[i]);
                    else
                        files[i].delete();
                }
            }
            return( path.delete() );
        }

}
