package tool;
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
	
	public StringBuilder generateVC() {
		StringBuilder result = new StringBuilder("(set-logic QF_BV)\n");
		result.append("(set-option :produce-models true)\n");
		result.append("(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
		result.append("(define-fun tobool ((p (_ BitVec 32))) Bool (ite (= p (_ bv0 32)) false true))\n");
		
		// TODO: generate the meat of the VC
                verifierVisitor.visitProcedureDecl(proc);
                SsaRepresentation ssa = verifierVisitor.getSsa();
                result.append(ssaToSmtTranslate(ssa));
		
		result.append("\n(check-sat)\n");
                System.out.println(result);
		return result;
	}
        
        private String ssaToSmtTranslate(SsaRepresentation ssa){
            StringBuilder smtFormula = new StringBuilder();
            
            Map<String, Integer> freshMapping = verifierVisitor.getFresh().getAllVariablesMappings();
            for(String variableName : freshMapping.keySet() ) {
                for(int i = 0; i <= freshMapping.get(variableName); i++) {
                    int index = freshMapping.get(variableName);
                    smtFormula.append("(declare-fun ").append(variableName).append(index).append(" () (_ BitVec 32))");
                }
            }
            
            smtFormula.append("\n");
            
            for(Assignment assignment : ssa.getAssignments()) {
                smtFormula.append(" ( ").append(assignment.variableName).append(" == ");
                smtFormula.append(assignment.expression.toString());
                smtFormula.append(" ) ");
                smtFormula.append(" && ");
            }
            
            smtFormula.append("\n");
            
            smtFormula.append(" !( ");
            for(Assertion assertion : ssa.getAssertions()) {
                smtFormula.append(" ( ");
                smtFormula.append(assertion.expression.toString());
                smtFormula.append(" ) ");
            }
            smtFormula.append(" ) ");
            
            return smtFormula.toString();
        }

}
