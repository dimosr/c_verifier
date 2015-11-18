package tool;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;
import java.util.Scanner;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import parser.SimpleCLexer;
import parser.SimpleCParser;
import parser.SimpleCParser.ProgramContext;
import tool.VerificationResult.VerificationResultType;
import tool.verif.structs.LoopStrategy;
import tool.verif.structs.SsaAssertionMapping;
import tool.verif.structs.SsaAssertionMapping.SourceType;
import tool.verif.structs.SsaRepresentation;
import util.ProcessExec;
import util.ProcessTimeoutException;
import util.program.Assertion;
import util.program.EnsureCondition;
import util.program.Invariant;
import util.program.Procedure;
import util.program.Program;
import util.program.RequireCondition;
import util.statement.AssertStatement;

public class SRTool {

    private static final int TIMEOUT = 30;
    private static final boolean DEBUG_MODE = false;
    private static final String Z3_PATH = "./z3";

	public static void main(String[] args) throws IOException, InterruptedException {
            
            try{
                String filename = args[0];
		ANTLRInputStream input = new ANTLRInputStream(new FileInputStream(filename));
                SimpleCLexer lexer = new SimpleCLexer(input);
		CommonTokenStream tokens = new CommonTokenStream(lexer);
		SimpleCParser parser = new SimpleCParser(tokens);
		ProgramContext ctx = parser.program();
		if(parser.getNumberOfSyntaxErrors() > 0) {
			System.exit(1);
		}
		Typechecker tc = new Typechecker();
		tc.visit(ctx);
		tc.resolve();
		if(tc.hasErrors()) {
			System.err.println("Errors were detected when typechecking " + filename + ":");
			for(String err : tc.getErrors()) {
				System.err.println("  " + err);
			}
			System.exit(1);
		}
                
                if(DEBUG_MODE) {
                    deleteDirectory(new File("output"));
                    Files.createDirectory(Paths.get("output"));
                }
		
                GeneratorVisitor generatorVisitor = new GeneratorVisitor();
                generatorVisitor.visitProgram(ctx);
                Program program = generatorVisitor.getProgram();
                program.calculateAllModSets();
		
                VerifierVisitor verifierVisitor = new VerifierVisitor(program);
                VerificationResult verificationResult;
                
                verificationResult = executeSimpleSummarisation(program, verifierVisitor);
                if(verificationResult.isCorrect()) {
                    System.out.println(VerificationResultType.CORRECT);
                    System.exit(0);
                }
                
                verificationResult = executeHoudiniAlgorithm(program, verifierVisitor);
                if(verificationResult.isCorrect()) {
                    System.out.println(VerificationResultType.CORRECT);
                    System.exit(0);
                }
                else if(verificationResult.isIncorrect()) {
                    if(!program.hasLoops()) {
                        System.out.println(VerificationResultType.INCORRECT);
                        System.exit(0);
                    } 
                    else {
                        verificationResult = incrementalSoundBoundModelChecking(program, verifierVisitor, 20, 160);
                        if(verificationResult.isIncorrect()) {
                            System.out.println(VerificationResultType.INCORRECT);
                            System.exit(0);
                        }
                        else if(verificationResult.isCorrect()) {
                            System.out.println(VerificationResultType.CORRECT);
                            System.exit(0);
                        }
                        else if(verificationResult.isUknown()){
                            System.out.println(VerificationResultType.UNKOWN);      //static verification has false positives
                            System.exit(1);
                        }
                        
                    }
                }
            } catch(Exception e) {
                System.out.println(VerificationResultType.UNKOWN);
		System.exit(1);
            }  
		
    }
        
    static private VerificationResult executeSimpleSummarisation(Program program, VerifierVisitor verifierVisitor) throws IOException, InterruptedException {
        VerificationResult verificationResult;
        ProcessExec process = new ProcessExec(Z3_PATH, "-smt2", "-in");
        for(Procedure procedure : program.procedures.values()) {
            verificationResult = null;
            VCGenerator vcgen = new VCGenerator(program, procedure, verifierVisitor, DEBUG_MODE);
            SsaRepresentation ssa = vcgen.generateVC(LoopStrategy.LOOP_SUMMARISATION, 0);
            String vc = ssa.vc;
            String queryResult = "";
            try {
		queryResult = process.execute(vc, TIMEOUT);
            } catch (ProcessTimeoutException e) {
		System.out.println(VerificationResultType.UNKOWN);
		System.exit(1);
            }
            
            if(verificationResult == null) {
                verificationResult = parseSmtSolverResponse(queryResult);
            }
            if(verificationResult.isIncorrect()) {
                verificationResult = new VerificationResult(VerificationResultType.INCORRECT);
                return verificationResult;
            }
            else if(verificationResult.isUknown()) {
                System.out.println(VerificationResultType.UNKOWN);
                System.err.println(queryResult);
                System.exit(1);
            }
        }
        verificationResult = new VerificationResult(VerificationResultType.CORRECT);
        return verificationResult;
    }
    
    /**
     * Verifies all procedures :
     *      - whenever a procedure fails due to candidate condition-invariant, remove it
     *      - if a procedure fails due to a regular condition-invariant, flag it as incorrect
     * Returns :
     *      - correct, having removed all failing candidates, leaving only the regular ones
     *      - incorrect (possible false positive, due to sound algorithm), having removed several candidates 
     */
    static private VerificationResult executeHoudiniAlgorithm(Program program, VerifierVisitor verifierVisitor) throws IOException, InterruptedException {
        boolean anyProcCandidateFailed, thisProcCandidateFailed, regularFailed;
        VerificationResult verificationResult;
        ProcessExec process = new ProcessExec(Z3_PATH, "-smt2", "-in");
        
        do {
            regularFailed = false;
            anyProcCandidateFailed = false;
            for(Procedure procedure : program.procedures.values()) {
                do {
                    thisProcCandidateFailed = false;
                    VCGenerator vcgen = new VCGenerator(program, procedure, verifierVisitor, false);
                    SsaRepresentation ssa = vcgen.generateVC(LoopStrategy.LOOP_SUMMARISATION, 0);
                    String vc = ssa.vc;
                    
                    String queryResult = "";
                    verificationResult = null;
                    try {
			queryResult = process.execute(vc, TIMEOUT);
                    } catch (ProcessTimeoutException e) {
			System.out.println(VerificationResultType.UNKOWN);
			System.exit(1);
                    }
                    
                    if(verificationResult == null) {
                        verificationResult = parseSmtSolverResponse(queryResult);
                    }
                        
                    if(verificationResult.isIncorrect()) {
                        int candidatesFailed = removeCandidateFailingAssertions(verificationResult.getFailingAssertionsIndexes(), ssa);
                        if(candidatesFailed > 0) {
                            thisProcCandidateFailed = true;
                            anyProcCandidateFailed = true;
                        }
                        else
                            regularFailed = true;
                    }
                    else if(verificationResult.isUknown()) {
                        System.out.println(VerificationResultType.UNKOWN);
                        System.err.println(queryResult);
                        System.exit(1);
                    }
                    
                } while(thisProcCandidateFailed);
            }
        } while(anyProcCandidateFailed);
        
        if(regularFailed) 
            verificationResult = new VerificationResult(VerificationResultType.INCORRECT);
        else
            verificationResult = new VerificationResult(VerificationResultType.CORRECT);
        
        return verificationResult;
    }
    
    static private VerificationResult executeBoundedModelChecking(Program program, VerifierVisitor verifierVisitor, int width) throws IOException, InterruptedException {
        VerificationResult verificationResult;
        
        ProcessExec process = new ProcessExec(Z3_PATH, "-smt2", "-in");
        for(Procedure procedure : program.procedures.values()) {
            verificationResult = null;
            VCGenerator vcgen = new VCGenerator(program, procedure, verifierVisitor, false);
            SsaRepresentation ssa = vcgen.generateVC(LoopStrategy.SOUND_BMC, width);
            String vc = ssa.vc;
            
            String queryResult = "";
            verificationResult = null;
            try {
		queryResult = process.execute(vc, TIMEOUT);
            } catch (ProcessTimeoutException e) {
		System.out.println(VerificationResultType.UNKOWN);
		System.exit(1);
            }
                    
            if(verificationResult == null) {
                verificationResult = parseSmtSolverResponse(queryResult);
            }
            
            if(verificationResult.isIncorrect()) {
                /*  If achieved full unwinding */
                if(verificationResult.getFailingAssertionsIndexes().size() == 1) {
                    Integer index = verificationResult.getFailingAssertionsIndexes().get(0);
                    SsaAssertionMapping assertionMapping = ssa.getAssertionMapping(index);
                    if(assertionMapping.sourceType == SourceType.ASSERT){
                        AssertStatement assertStmt = (AssertStatement) assertionMapping.source;
                        if(assertStmt.toString().equals(VerifierVisitor.BMC_SOUND_ASSERT.toString())) {
                            verificationResult = new VerificationResult(VerificationResultType.UNKOWN);
                            return verificationResult;
                        }
                    }
                }
                verificationResult = new VerificationResult(VerificationResultType.INCORRECT);
                return verificationResult;
            }
            else if(verificationResult.isUknown()) {
                System.out.println(VerificationResultType.UNKOWN);
                System.err.println(queryResult);
                System.exit(1);
            }
        }
        
        verificationResult = new VerificationResult(VerificationResultType.CORRECT);
        return verificationResult;
    }
    
    static private VerificationResult incrementalSoundBoundModelChecking(Program program, VerifierVisitor verifierVisitor, int startingWidth, int maxWidth) throws IOException, InterruptedException {
        VerificationResult verificationResult = null;
        int width = startingWidth;
        while(width <= maxWidth) {
            verificationResult = executeBoundedModelChecking(program, verifierVisitor, width);
            if(verificationResult.isCorrect())
                return verificationResult;
            if(verificationResult.isIncorrect())
                return verificationResult;
            width *= 2;
        }
        return verificationResult;          
    }
        
    static private VerificationResult parseSmtSolverResponse(String solverResponse) {
        VerificationResult verificationResult;
        Scanner scanner = new Scanner(solverResponse);
        String smtResult = scanner.nextLine();
        if(smtResult.equals("sat"))
            verificationResult = new VerificationResult(VerificationResultType.INCORRECT);
        else if(smtResult.equals("unsat"))
            verificationResult = new VerificationResult(VerificationResultType.CORRECT);
        else
            verificationResult = new VerificationResult(VerificationResultType.UNKOWN);
        
        if(verificationResult.isIncorrect()) {
            while(scanner.hasNextLine()) {
                String assertionValue = scanner.nextLine();
                String[] temp = assertionValue.split(" #x");
                String predicateName = temp[0];
                String predicateValue = temp[1];
                
                int assertionIndex = Integer.parseInt(predicateName.substring(predicateName.indexOf(SsaRepresentation.DEBUG_PRED_NAME) + SsaRepresentation.DEBUG_PRED_NAME.length()));
                boolean isPredFalse = predicateValue.contains("00000000");
                
                if(isPredFalse)
                    verificationResult.addFailingAssertionIndex(assertionIndex);
            }
        }
        
        return verificationResult;
    }
    
    static private int removeCandidateFailingAssertions(List<Integer> assertionsIndexes, SsaRepresentation ssa) {
        int removedSum = 0;
        for(Integer index : assertionsIndexes) {
            SsaAssertionMapping assertionMapping = ssa.getAssertionMapping(index);
            if(assertionMapping.sourceType == SourceType.ENSURES) {
                EnsureCondition ensure = (EnsureCondition) assertionMapping.source;
                if(ensure.isCandidate) {
                    List holder = assertionMapping.holder;
                    holder.remove(ensure);
                    removedSum++;
                }
            }
            else if(assertionMapping.sourceType == SourceType.INVARIANT){
                Invariant invariant = (Invariant) assertionMapping.source;
                if(invariant.isCandidate) {
                    List holder = assertionMapping.holder;
                    holder.remove(invariant);
                    removedSum++;
                }
            }
            else if(assertionMapping.sourceType == SourceType.REQUIRES){
                RequireCondition require = (RequireCondition) assertionMapping.source;
                if(require.isCandidate) {
                    List holder = assertionMapping.holder;
                    holder.remove(require);
                    removedSum++;
                }
            }
        }
        return removedSum;
    }
    
    static private void printFailingAssertions(List<Integer> assertionsIndexes, SsaRepresentation ssa) {
        StringBuilder errorOut = new StringBuilder();
        for(Integer index : assertionsIndexes) {
            SsaAssertionMapping assertionMapping = ssa.getAssertionMapping(index);
            if(assertionMapping.sourceType == SourceType.ASSERT) {
                AssertStatement assertion = (AssertStatement) assertionMapping.source;
                errorOut.append("Assertion ").append(ssa.getExpressionSsa(assertion.expression)).append(" failed \n");
            }
            else if(assertionMapping.sourceType == SourceType.ENSURES) {
                EnsureCondition ensure = (EnsureCondition) assertionMapping.source;
                errorOut.append("Pre-condition ").append(ssa.getExpressionSsa(ensure.expression)).append(" failed \n");
            }
            else if(assertionMapping.sourceType == SourceType.INVARIANT){
                Invariant invariant = (Invariant) assertionMapping.source;
                errorOut.append("Invariant ").append(ssa.getExpressionSsa(invariant.expression)).append(" failed \n");
            }
            else if(assertionMapping.sourceType == SourceType.REQUIRES){
                RequireCondition require = (RequireCondition) assertionMapping.source;
                errorOut.append("Require ").append(ssa.getExpressionSsa(require.expression)).append(" failed \n");
            }
        }
        System.err.println(errorOut);
    }
        
    static private boolean deleteDirectory(File path) {
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
