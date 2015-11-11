package tool;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.HashSet;
import java.util.Set;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import parser.SimpleCLexer;
import parser.SimpleCParser;
import parser.SimpleCParser.ProcedureDeclContext;
import parser.SimpleCParser.ProgramContext;
import parser.SimpleCParser.VarDeclContext;
import util.ProcessExec;
import util.ProcessTimeoutException;
import util.program.Procedure;
import util.program.Program;

public class SRTool {

    private static final int TIMEOUT = 30;
    private static final boolean DEBUG_MODE = true;

	public static void main(String[] args) throws IOException, InterruptedException {
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
		for(Procedure procedure : program.procedures.values()) {
			VCGenerator vcgen = new VCGenerator(program, procedure, verifierVisitor, DEBUG_MODE);
			String vc = vcgen.generateVC().toString();

			ProcessExec process = new ProcessExec("./z3", "-smt2", "-in");
			String queryResult = "";
			try {
				queryResult = process.execute(vc, TIMEOUT);
			} catch (ProcessTimeoutException e) {
				System.out.println("UNKNOWN");
				System.exit(1);
			}
			
			if (queryResult.startsWith("sat")) {
				System.out.println("INCORRECT");
				System.exit(0);
			}
			
			if (!queryResult.startsWith("unsat")) {
				System.out.println("UNKNOWN");
				System.out.println(queryResult);
				System.exit(1);
			}
		}
		
		System.out.println("CORRECT");
		System.exit(0);
		
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
