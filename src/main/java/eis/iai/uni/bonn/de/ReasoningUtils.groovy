package eis.iai.uni.bonn.de

import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.Property;
import org.apache.jena.rdf.model.RDFNode;
import org.apache.jena.rdf.model.Resource;
import org.apache.jena.rdf.model.Statement;
import org.apache.jena.rdf.model.StmtIterator;
import org.apache.jena.util.FileManager;

import edu.umd.cs.psl.groovy.*;
import edu.umd.cs.psl.core.*;

import edu.umd.cs.psl.ui.loading.*;
import edu.umd.cs.psl.util.database.*;
import edu.umd.cs.psl.database.DataStore;
import edu.umd.cs.psl.database.Database;
import edu.umd.cs.psl.database.DatabasePopulator;
import edu.umd.cs.psl.database.DatabaseQuery;
import edu.umd.cs.psl.database.Partition;
import edu.umd.cs.psl.database.rdbms.RDBMSDataStore;
import edu.umd.cs.psl.database.rdbms.driver.H2DatabaseDriver;
import edu.umd.cs.psl.database.rdbms.driver.H2DatabaseDriver.Type;
import edu.emory.mathcs.utils.ConcurrencyUtils;
import edu.umd.cs.psl.model.kernel.CompatibilityKernel;
import edu.umd.cs.psl.model.kernel.Kernel;
import edu.umd.cs.psl.model.predicate.Predicate;
import edu.umd.cs.psl.model.argument.GroundTerm
import edu.umd.cs.psl.model.atom.*;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.text.DecimalFormat;

class ReasoningUtils {

	def loadPredicateAtoms(datastore, predsAll, dataroot, targetPartition){
		for (Predicate p : predsAll) {
			//System.out.println p.getName();
			InserterUtils.loadDelimitedData(datastore.getInserter(p, targetPartition), dataroot+ p.getName().toLowerCase()+".txt");
		}
	}

	static def loadPredicateAtomsWithValue(datastore, predsAll, dataroot, targetPartition){
		for (Predicate p : predsAll) {
			InserterUtils.loadDelimitedDataTruth(datastore.getInserter(p,targetPartition), dataroot+ p.getName().toLowerCase()+".txt");
		}
	}


	/////////////////////////////////print///////////////////////////////////
	def print_results(testDB,openPredsAll ) {
		DecimalFormat formatter = new DecimalFormat("#.##");
		for (Predicate p : openPredsAll ) {

			for (GroundAtom atom : Queries.getAllAtoms(testDB, p)){
				int arity = atom.arity;
				String s = "";
				for (int i = 0; i < arity; i++) {
					GroundTerm term = atom.getArguments()[i];
					s += term.getValue() + ", ";
				}

				if (atom.getValue() > 0)
					println p.getName() +"(" + s.substring(0, s.length()-2) + ") : " + formatter.format(atom.getValue());
			}
			println "/////////////////////////////////////////";
		}
	}

	static def writeweights (PSLModel m, String filename) {
		String content = "";
//http://www.w3.org/1999/02/22-rdf-syntax-ns#type'
		String [] rules = ["( ( FROMDATASET(S, 'http://www.w3.org/1999/02...', B) & FROMSRCDATASET(S, 'http://www.w3.org/1999/02...', D) ) & NDISJOINTFROM(D, B) )",
			"( ( FROMDATASET(S, 'http://www.w3.org/1999/02...', B) & FROMTARDATASET(S, 'http://www.w3.org/1999/02...', D) ) & NDISJOINTFROM(D, B) )",
			"( ( ( DOMAINOF(A, B, UID1) & FROMDATASET(S, A, O) ) & FROMSRCDATASET(S, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( DOMAINOF(A, B, UID1) & FROMDATASET(S, A, O) ) & FROMTARDATASET(S, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( DOMAINOF(A, B, UID1) & FROMSRCDATASET(S, A, O) ) & FROMTARDATASET(S, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( DOMAINOF(A, B, UID1) & FROMTARDATASET(S, A, O) ) & FROMSRCDATASET(S, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( DOMAINOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMDATASET(S, C, O) ) & FROMSRCDATASET(S, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( DOMAINOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMDATASET(S, C, O) ) & FROMTARDATASET(S, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( DOMAINOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMSRCDATASET(S, C, O) ) & FROMTARDATASET(S, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( DOMAINOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMTARDATASET(S, C, O) ) & FROMSRCDATASET(S, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( RANGEOF(A, B, UID1) & FROMDATASET(S, A, O) ) & FROMSRCDATASET(O, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( RANGEOF(A, B, UID1) & FROMDATASET(S, A, O) ) & FROMTARDATASET(O, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( RANGEOF(A, B, UID1) & FROMSRCDATASET(S, A, O) ) & FROMTARDATASET(O, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( RANGEOF(A, B, UID1) & FROMTARDATASET(S, A, O) ) & FROMSRCDATASET(O, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( RANGEOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMDATASET(S, C, O) ) & FROMSRCDATASET(O, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( RANGEOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMDATASET(S, C, O) ) & FROMTARDATASET(O, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( RANGEOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMSRCDATASET(S, C, O) ) & FROMTARDATASET(O, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( RANGEOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMTARDATASET(S, C, O) ) & FROMSRCDATASET(O, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( RANGEOF(A, B, UID1) & FROMSRCDATASET(X, A, Y) ) & FROMTARDATASET(X, A, Z) ) & HASTYPE(Y, B) ) & NHASTYPE(Z, B) )",
			"( ( ( ( RANGEOF(A, B, UID1) & FROMSRCDATASET(X, A, Y) ) & FROMTARDATASET(X, A, Z) ) & HASTYPE(Z, B) ) & NHASTYPE(Y, B) )",
			"( ( INVFUNPROPERTY(A, UID) & FROMDATASET(R, A, O) ) & FROMSRCDATASET(S, A, O) )",
			"( ( INVFUNPROPERTY(A, UID) & FROMDATASET(R, A, O) ) & FROMTARDATASET(S, A, O) )",
			"( ( INVFUNPROPERTY(A, UID) & FROMSRCDATASET(R, A, O) ) & FROMTARDATASET(S, A, O) )",
			"( ( ( ( EQVPROPERTY(A, B, UID) & FROMDATASET(S, A, N) ) & FROMSRCDATASET(S, B, N) ) & FROMTARDATASET(S, B, O) ) & NSAME(N, O) ) ",
			"( ( ( ( EQVPROPERTY(A, B, UID) & FROMDATASET(S, A, N) ) & FROMTARDATASET(S, B, N) ) & FROMSRCDATASET(S, B, O) ) & NSAME(N, O) )",
			"( ( ( ( ( ( EQVPROPERTY(A, B, UID) & FROMDATASET(S, A, N) ) & FROMSRCDATASET(S, B, M) ) & FROMTARDATASET(S, B, O) ) & NSAME(N, M) ) & NSAME(N, O) ) & NSAME(M, O) )",
			"( ( ( ( ( ( EQVPROPERTY(A, B, UID) & FROMDATASET(S, A, N) ) & FROMTARDATASET(S, B, M) ) & FROMSRCDATASET(S, B, O) ) & NSAME(N, M) ) & NSAME(N, O) ) & NSAME(M, O) )",
			"( ( ( ( EQVPROPERTY(C, B, UID) & SUBPROPERTYOF(A, B, UID1) ) & FROMDATASET(S, C, N) ) & FROMSRCDATASET(S, A, N) ) & FROMTARDATASET(S, A, O) )",
			"( ( ( ( EQVPROPERTY(C, B, UID) & SUBPROPERTYOF(A, B, UID1) ) & FROMDATASET(S, C, N) ) & FROMTARDATASET(S, A, N) ) & FROMSRCDATASET(S, A, O) )",
			"( ( ( ( EQVPROPERTY(C, B, UID) & SUBPROPERTYOF(A, B, UID1) ) & FROMDATASET(S, C, N) ) & FROMSRCDATASET(S, A, M) ) & FROMTARDATASET(S, A, O) )",
			"( ( ( ( EQVPROPERTY(C, B, UID) & SUBPROPERTYOF(A, B, UID1) ) & FROMDATASET(S, C, N) ) & FROMTARDATASET(S, A, M) ) & FROMSRCDATASET(S, A, O) )",
			"( ( FROMSRCDATASET(S, A, N) & FROMTARDATASET(S, A, O) ) & SAMEAS(N, O) )",
			"( ( FROMDATASET(S, A, N) & FROMSRCDATASET(S, A, O) ) & SAMEAS(N, O) )",
			"( ( FROMDATASET(S, A, N) & FROMTARDATASET(S, A, O) ) & SAMEAS(N, O) )",
			"( ( ( FROMDATASET(T, A, N) & FROMSRCDATASET(S, A, N) ) & FROMTARDATASET(S, A, O) ) & SAMEAS(T, S) )",
			"( ( ( FROMDATASET(T, A, N) & FROMTARDATASET(S, A, N) ) & FROMSRCDATASET(S, A, O) ) & SAMEAS(T, S) )",
			"( ( ( FROMDATASET(T, A, N) & FROMSRCDATASET(S, A, M) ) & FROMTARDATASET(S, A, O) ) & SAMEAS(T, S) )",
			"( ( ( FROMDATASET(T, A, N) & FROMTARDATASET(S, A, M) ) & FROMSRCDATASET(S, A, O) ) & SAMEAS(T, S) )",
			"( ( ( ( SUBPROPERTYOF(A, B, UID) & FROMDATASET(S, B, N) ) & FROMSRCDATASET(S, A, N) ) & FROMTARDATASET(S, A, O) ) & NSAME(N, O) )",
			"( ( ( ( SUBPROPERTYOF(A, B, UID) & FROMDATASET(S, B, N) ) & FROMTARDATASET(S, A, N) ) & FROMSRCDATASET(S, A, O) ) & NSAME(N, O) )",
			"( ( ( ( ( ( SUBPROPERTYOF(A, B, UID) & FROMDATASET(S, B, N) ) & FROMSRCDATASET(S, A, M) ) & FROMTARDATASET(S, A, O) ) & NSAME(N, M) ) & NSAME(N, O) ) & NSAME(M, O) )",
			"( ( ( ( ( ( SUBPROPERTYOF(A, B, UID) & FROMDATASET(S, B, N) ) & FROMTARDATASET(S, A, M) ) & FROMSRCDATASET(S, A, O) ) & NSAME(N, M) ) & NSAME(N, O) ) & NSAME(M, O) )",
			"( ( ( ( SUBPROPERTYOF(A, B, UID) & FROMDATASET(S, B, N) ) & FROMSRCDATASET(S, A, N) ) & FROMTARDATASET(S, A, O) ) & DIFFROM(N, O) )",
			"( ( ( ( SUBPROPERTYOF(A, B, UID) & FROMDATASET(S, B, N) ) & FROMTARDATASET(S, A, N) ) & FROMSRCDATASET(S, A, O) ) & DIFFROM(N, O) )",
			"( ( ( ( ( ( SUBPROPERTYOF(A, B, UID) & FROMDATASET(S, B, N) ) & FROMSRCDATASET(S, A, M) ) & FROMTARDATASET(S, A, O) ) & DIFFROM(N, M) ) & DIFFROM(N, O) ) & DIFFROM(M, O) )",
			"( ( ( ( ( ( SUBPROPERTYOF(A, B, UID) & FROMDATASET(S, B, N) ) & FROMTARDATASET(S, A, M) ) & FROMSRCDATASET(S, A, O) ) & DIFFROM(N, M) ) & DIFFROM(N, O) ) & DIFFROM(M, O) )",
			"( ( ( ( EQVPROPERTY(A, B, UID) & FROMDATASET(S, A, N) ) & FROMSRCDATASET(S, B, N) ) & FROMTARDATASET(S, B, O) ) & DIFFROM(N, O) )",
			"( ( ( ( EQVPROPERTY(A, B, UID) & FROMDATASET(S, A, N) ) & FROMTARDATASET(S, B, N) ) & FROMSRCDATASET(S, B, O) ) & DIFFROM(N, O) )",
			"( ( ( ( ( ( EQVPROPERTY(A, B, UID) & FROMDATASET(S, A, N) ) & FROMSRCDATASET(S, B, M) ) & FROMTARDATASET(S, B, O) ) & DIFFROM(N, M) ) & DIFFROM(N, O) ) & DIFFROM(M, O) )",
			"( ( ( ( ( ( EQVPROPERTY(A, B, UID) & FROMDATASET(S, A, N) ) & FROMTARDATASET(S, B, M) ) & FROMSRCDATASET(S, B, O) ) & DIFFROM(N, M) ) & DIFFROM(N, O) ) & DIFFROM(M, O) )",
			"~( TYPE(X, B) )",
			"~( RELATEDTO(X, A, Z)",
			"~( ISSAME(Y, Z) )"];

		Iterable<Kernel> k = m.getKernels();
		for (Kernel gk : k) {
			try {
				CompatibilityKernel c = (CompatibilityKernel) gk;
				String s = c.toString();

				if (s.contains(rules[0]))
					content += "'sim1':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[1]))
					content += "'sim2':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[2]))
					content += "'dom1':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[3]))
					content += "'dom2':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[4]))
					content += "'dom3':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[5]))
					content += "'dom4':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[6]))
					content += "'dom5':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[7]))
					content += "'dom6':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[8]))
					content += "'dom7':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[9]))
					content += "'dom8':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[10]))
					content += "'ran1':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[11]))
					content += "'ran2':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[12]))
					content += "'ran3':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[13]))
					content += "'ran4':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[14]))
					content += "'ran5':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[15]))
					content += "'ran6':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[16]))
					content += "'ran7':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[17]))
					content += "'ran8':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[18]))
					content += "'ran9':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[19]))
					content += "'ran10':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[20]))
					content += "'ifp1':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[21]))
					content += "'ifp2':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[22]))
					content += "'ifp3':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[23]))
					content += "'ep1':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[24]))
					content += "'ep2':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[25]))
					content += "'ep3':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[26]))
					content += "'ep4':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[27]))
					content += "'ep5':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[28]))
					content += "'ep6':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[29]))
					content += "'ep7':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[30]))
					content += "'ep8':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[31]))
					content += "'sa1':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[32]))
					content += "'sa2':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[33]))
					content += "'sa3':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[34]))
					content += "'sa4':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[35]))
					content += "'sa5':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[36]))
					content += "'sa6':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[37]))
					content += "'sa7':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[38]))
					content += "'sp1':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[39]))
					content += "'sp2':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[40]))
					content += "'sp3':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[41]))
					content += "'sp4':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[42]))
					content += "'df1':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[43]))
					content += "'df2':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[44]))
					content += "'df3':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[45]))
					content += "'df4':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[46]))
					content += "'df5':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[47]))
					content += "'df6':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[48]))
					content += "'df7':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[49]))
					content += "'df8':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[50]))
					content += "'type':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[51]))
					content += "'isSame':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[52]))
					content += "'related':"+c.getWeight().getWeight() +"\n";
			} catch(org.codehaus.groovy.runtime.typehandling.GroovyCastException r) {
			}
		}
		writer (filename, content);
	}

	static def Map<String, Double> readweights (String filename) throws IOException {

		Map<String, Integer> weightMap = new HashMap<String, Double>();

		BufferedReader	br = new BufferedReader(new FileReader(filename));
		String line = null;
		while ((line = br.readLine()) != null) {
			int sep = line.indexOf(":");
			String x = line.substring(1, sep-1);
			Double y = line.subSequence(sep+1, line.length()).toDouble();
			//System.out.println x+"==================="+y
			weightMap.putAt (x, y);
		}
		br.close();
		return weightMap ;
	}

	static void RDF2txt(String ifilename, String ofilename, String filesyntax) throws IOException {

		Model model = FileManager.get().loadModel(ifilename, filesyntax);
		String content = "";

		StmtIterator iter1 = model.listStatements();
		while (iter1.hasNext()) {
			Statement stmt = iter1.next();
			Resource subject = stmt.getSubject();
			Property predicate = stmt.getPredicate();
			RDFNode object = stmt.getObject();

			if (object.isResource())
				content += subject.toString() +"\t"+ predicate.toString() + "\t" + object.asResource().toString() + "\n";
			else
				content += subject.toString() +"\t"+ predicate.toString() + "\t" + object.toString() + "\n";
		}
		writer (ofilename+".txt", content);
	}

	protected static void writer (String filename, String content) throws IOException{
		File file = new File(filename);
		if(!file.exists())
			file.createNewFile();
		else {
			file.delete();
			file.createNewFile();
		}

		FileWriter fw = new FileWriter(file.getAbsoluteFile(), true);
		BufferedWriter bw = new BufferedWriter(fw);
		bw.write(content);
		bw.close();
	}
}
