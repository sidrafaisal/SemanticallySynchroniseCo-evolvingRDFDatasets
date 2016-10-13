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
		String [] rules = ["FROMDATASET(S, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', B) & FROMSRCDATASET(S, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', D) ) & NDISJOINTFROM(D, B) )",
			"( ( FROMDATASET(S, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', B) & FROMTARDATASET(S, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', D) ) & NDISJOINTFROM(D, B) )",
			"( ( ( DOMAINOF(A, B, UID1) & FROMDATASET(S, A, O) ) & FROMSRCDATASET(S, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( DOMAINOF(A, B, UID1) & FROMDATASET(S, A, O) ) & FROMTARDATASET(S, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( DOMAINOF(A, B, UID1) & FROMSRCDATASET(S, A, O) ) & FROMTARDATASET(S, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( DOMAINOF(A, B, UID1) & FROMTARDATASET(S, A, O) ) & FROMSRCDATASET(S, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( DOMAINOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMDATASET(S, C, O) ) & FROMSRCDATASET(S, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( DOMAINOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMDATASET(S, C, O) ) & FROMTARDATASET(S, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( DOMAINOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMSRCDATASET(S, C, O) ) & FROMTARDATASET(S, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( DOMAINOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMTARDATASET(S, C, O) ) & FROMSRCDATASET(S, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( RANGEOF(A, B, UID1) & FROMDATASET(S, A, O) ) & FROMSRCDATASET(O, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( RANGEOF(A, B, UID1) & FROMDATASET(S, A, O) ) & FROMTARDATASET(O, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( RANGEOF(A, B, UID1) & FROMSRCDATASET(S, A, O) ) & FROMTARDATASET(O, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( RANGEOF(A, B, UID1) & FROMTARDATASET(S, A, O) ) & FROMSRCDATASET(O, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( RANGEOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMDATASET(S, C, O) ) & FROMSRCDATASET(O, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( RANGEOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMDATASET(S, C, O) ) & FROMTARDATASET(O, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( RANGEOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMSRCDATASET(S, C, O) ) & FROMTARDATASET(O, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( RANGEOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMTARDATASET(S, C, O) ) & FROMSRCDATASET(O, 'http://www.w3.org/1999/02/22-rdf-syntax-ns#type', D) ) & DISJOINTFROM(D, B) )",
			"( ( INVFUNPROPERTY(A, UID) & FROMDATASET(R, A, O) ) & FROMSRCDATASET(S, A, O) )",
			"( ( INVFUNPROPERTY(A, UID) & FROMDATASET(R, A, O) ) & FROMTARDATASET(S, A, O) )",
			"( ( INVFUNPROPERTY(A, UID) & FROMSRCDATASET(R, A, O) ) & FROMTARDATASET(S, A, O) )",
			"( ( ( INVFUNPROPERTY(A, UID) & FROMDATASET(R, A, O) ) & FROMSRCDATASET(S, A, N) ) & FROMTARDATASET(S, A, O) )",
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
					content += "'ifp1':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[19]))
					content += "'ifp2':"+c.getWeight().getWeight() +"\n";

				else if (s.contains(rules[20]))
					content += "'type':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[21]))
					content += "'related':"+c.getWeight().getWeight() +"\n";
				else if (s.contains(rules[22]))
					content += "'isSame':"+c.getWeight().getWeight() +"\n";
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
