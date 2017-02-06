package eis.iai.uni.bonn.de

import org.apache.jena.graph.Triple;
import org.apache.jena.rdf.model.Literal
import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.Property;
import org.apache.jena.rdf.model.RDFNode;
import org.apache.jena.rdf.model.Resource;
import org.apache.jena.rdf.model.ResourceFactory;
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
import edu.umd.cs.psl.model.kernel.GroundKernel;
import edu.umd.cs.psl.model.kernel.Kernel;
import edu.umd.cs.psl.model.predicate.Predicate;
import edu.umd.cs.psl.model.argument.GroundTerm;
import edu.umd.cs.psl.model.atom.*;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileOutputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.text.DecimalFormat;
import java.util.Map;

class InferenceUtils {

	private static String trainDir;
	private static String testDir;
	Model imodel, smodel, tmodel;
	String content = "", location="";

	public InferenceUtils (l, dir) {
		location = l;
		trainDir = dir+"train"+java.io.File.separator;
		testDir = dir+"test"+java.io.File.separator;
	}
	def loadPredicateAtoms(datastore, predsAll, dataroot, targetPartition){
		for (Predicate p : predsAll) 
			InserterUtils.loadDelimitedData(datastore.getInserter(p, targetPartition), dataroot+ p.getName().toLowerCase()+".txt");
	}

	def loadPredicateAtomsWithValue(datastore, predsAll, dataroot, targetPartition){
		for (Predicate p : predsAll) 
			InserterUtils.loadDelimitedDataTruth(datastore.getInserter(p,targetPartition), dataroot+ p.getName().toLowerCase()+".txt");		
	}

	/////get_ruleinference
	def get_inference(GroundAtom atom, Predicate p) {

		String s = "";
		int arity = atom.arity;
		for (int i = 0; i < arity; i++) 
			s += atom.getArguments()[i].getValue() + ", ";		

		//FORMATTING INFERENCE
		String sub="", pred="", obj="";
		if (p.getName()=="TYPE") {
			int sep = s.indexOf(",");
			sub = s.substring(0,sep);
			obj = s.substring(sep+2,s.length()-2);
			pred = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";
		}
		else if (p.getName()=="ISSAME") {
			int sep = s.indexOf(",");
			sub = s.substring(0,sep);
			obj = s.substring(sep+2,s.length()-2);
			pred = "http://www.w3.org/2002/07/owl#sameAs";
		}
		else if (p.getName()=="RELATEDTO") {
			int sep = s.indexOf(",");
			sub = s.substring(0,sep);

			String s1 = s.substring(sep+2,s.length());
			sep = s1.indexOf(",");
			pred = s1.substring(0,sep);
			obj = s1.substring(sep+2,s1.length()-2);
		}
		if(sub!="" && pred!="" &&  obj!=""){
			Property property = ResourceFactory.createProperty(pred);
			Resource subject = ResourceFactory.createResource(sub);
			if (obj.contains("http")) {
				RDFNode object = (RDFNode) ResourceFactory.createResource(obj);
				imodel.add(imodel.asStatement(Triple.create(subject.asNode(), property.asNode(), object.asNode())));
			} else {
				Literal object = imodel.createLiteral(obj);
				imodel.add(imodel.asStatement(Triple.create(subject.asNode(), property.asNode(), object.asNode())));
			}
		}
		return s;
	}

	////get_groundingsofaRule
	def get_groundingsofaRule(GroundAtom atom) {
		Iterator<GroundKernel> igk = atom.getRegisteredGroundKernels().iterator();		
		while(igk.hasNext()) { //gets rule instance			
			Triple triple1 = null, triple2 = null, triple3 = null;
			Iterator<GroundAtom> iga = igk.next().getAtoms().iterator();
			while (iga.hasNext()) { //gets predicate
				GroundAtom gatom = iga.next();
				if (gatom.toString().contains("FROMFRAGMENT") || gatom.toString().contains("FROMCONSUMER2") || gatom.toString().contains("FROMCONSUMER1")) {
					Triple triple = createtripleform(gatom);
					if (gatom.toString().contains("FROMFRAGMENT")) {
						triple1 = triple;
					} else if (gatom.toString().contains("FROMCONSUMER1")) {
						smodel.add(smodel.asStatement(triple));
						triple2 = triple;
					} else if (gatom.toString().contains("FROMCONSUMER2")) {
						tmodel.add(tmodel.asStatement(triple));
						triple3 = triple;
					}
				}
			}
			// FORMATTING rule's grounding
			String str1 = aligntriples(triple1, triple2, triple3);
			int count = str1.length();
			if(count != 0) {
				if (str1.charAt(count-1) == "|")
					str1 = str1.substring(0, count-1);
				if (!content.contains(str1))
					content += str1 + "\n";
			}
			}
	}

	def createtripleform(GroundAtom gatom) {
		Resource subject;
		Property predicate;
		String obj;
		Triple triple;

		int garity = gatom.arity;
		for (int i = 0; i < garity; i++) {
			GroundTerm term = gatom.getArguments()[i];
			if (i==0)
				subject = ResourceFactory.createResource(term.getValue());
			else if (i==1)
				predicate = ResourceFactory.createProperty(term.getValue());
			else if (i==2)
				obj = term.getValue();
		}
		if (obj.contains("http")) {
			RDFNode object = (RDFNode) ResourceFactory.createResource(obj);
			triple = Triple.create(subject.asNode(), predicate.asNode(), object.asNode());
		} else {
			Literal object = smodel.createLiteral(obj);
			triple = Triple.create(subject.asNode(), predicate.asNode(), object.asNode());
		}
		return triple;
	}

	/////////////// arrange triples in order for later calculating intersection.
	def aligntriples(Triple triple1, Triple triple2, Triple triple3) {
		String str1 = "";

		if (triple1!= null) {
			if (triple1.getObject().isURI()) {
				str1 = "<"+triple1.getSubject() +"> <" + triple1.getPredicate()+"> <" + triple1.getObject() + ">|";
			} else if (triple1.getObject().isLiteral())
				str1 = "<"+triple1.getSubject() +"> <" + triple1.getPredicate()+"> \"" + triple1.getObject() + "\"|";
		}
		if (triple2!= null) {
			if (triple2.getObject().isURI()) {
				str1 += "<"+triple2.getSubject() +"> <" + triple2.getPredicate()+"> <" + triple2.getObject() + ">|";
			} else if (triple2.getObject().isLiteral())
				str1 += "<"+triple2.getSubject() +"> <" + triple2.getPredicate()+"> \"" + triple2.getObject() + "\"|";
		}
		if (triple3!= null) {
			if (triple3.getObject().isURI()) {
				str1 += "<"+triple3.getSubject() +"> <" + triple3.getPredicate()+"> <" + triple3.getObject() + ">";
			} else if (triple3.getObject().isLiteral())
				str1 += "<"+triple3.getSubject() +"> <" + triple3.getPredicate()+"> \"" + triple3.getObject() + "\"";
		}
		return str1;
	}
	/////////////////////////////////print///////////////////////////////////
	def print_results(testDB,openPredsAll ) {
		String filename = location+"PSLinferedtriples";
		String filename1 = location+"PSLSrctriples";
		String filename2 = location+"PSLTartriples";

		createfile(filename);
		createfile(filename1);
		createfile(filename2);

		imodel =  FileManager.get().loadModel(filename, "NT");
		smodel =  FileManager.get().loadModel(filename1, "NT");
		tmodel =  FileManager.get().loadModel(filename2, "NT");

		DecimalFormat formatter = new DecimalFormat("#.##");

		for (Predicate p : openPredsAll) {
			if (p.getName()!="FROMFRAGMENT" && p.getName()!="DIFFROM" && p.getName()!="SAMEAS") {
				for (GroundAtom atom : Queries.getAllAtoms(testDB, p)){
					if (atom.getValue() > 0) {
						String s = get_inference(atom,p);
						get_groundingsofaRule(atom);
						println p.getName() +"(" + s.substring(0, s.length()-2) + ") : " + formatter.format(atom.getValue());
					}
				}
			}
			println "/////////////////////////////////////////";
		}

		imodel.write(new FileOutputStream(filename), "NT");
		imodel.close();
		smodel.write(new FileOutputStream(filename1), "NT");
		smodel.close();
		tmodel.write(new FileOutputStream(filename2), "NT");
		tmodel.close();
		writer (location+"conflict_combination_PSL", content);
	}

	static def writeweights (PSLModel m, String filename, Map<String, Double> weightMap) {

		//http://www.w3.org/1999/02/22-rdf-syntax-ns#type'
		String [] rules = ["( ( FROMFRAGMENT(S, 'http://www.w3.org/1999/02...', B) & FROMCONSUMER1(S, 'http://www.w3.org/1999/02...', D) ) & NDISJOINTFROM(D, B) )",
			"( ( FROMFRAGMENT(S, 'http://www.w3.org/1999/02...', B) & FROMCONSUMER2(S, 'http://www.w3.org/1999/02...', D) ) & NDISJOINTFROM(D, B) )",
			"( ( ( DOMAINOF(A, B, UID1) & FROMFRAGMENT(S, A, O) ) & FROMCONSUMER1(S, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( DOMAINOF(A, B, UID1) & FROMFRAGMENT(S, A, O) ) & FROMCONSUMER2(S, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( DOMAINOF(A, B, UID1) & FROMCONSUMER1(S, A, O) ) & FROMCONSUMER2(S, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( DOMAINOF(A, B, UID1) & FROMCONSUMER2(S, A, O) ) & FROMCONSUMER1(S, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( DOMAINOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMFRAGMENT(S, C, O) ) & FROMCONSUMER1(S, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( DOMAINOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMFRAGMENT(S, C, O) ) & FROMCONSUMER2(S, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( DOMAINOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMCONSUMER1(S, C, O) ) & FROMCONSUMER2(S, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( DOMAINOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMCONSUMER2(S, C, O) ) & FROMCONSUMER1(S, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( RANGEOF(A, B, UID1) & FROMFRAGMENT(S, A, O) ) & FROMCONSUMER1(O, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( RANGEOF(A, B, UID1) & FROMFRAGMENT(S, A, O) ) & FROMCONSUMER2(O, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( RANGEOF(A, B, UID1) & FROMCONSUMER1(S, A, O) ) & FROMCONSUMER2(O, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( RANGEOF(A, B, UID1) & FROMCONSUMER2(S, A, O) ) & FROMCONSUMER1(O, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( RANGEOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMFRAGMENT(S, C, O) ) & FROMCONSUMER1(O, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( RANGEOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMFRAGMENT(S, C, O) ) & FROMCONSUMER2(O, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( RANGEOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMCONSUMER1(S, C, O) ) & FROMCONSUMER2(O, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( RANGEOF(A, B, UID1) & SUBPROPERTYOF(C, A, UID2) ) & FROMCONSUMER2(S, C, O) ) & FROMCONSUMER1(O, 'http://www.w3.org/1999/02...', D) ) & DISJOINTFROM(D, B) )",
			"( ( ( ( RANGEOF(A, B, UID1) & FROMCONSUMER1(X, A, Y) ) & FROMCONSUMER2(X, A, Z) ) & HASTYPE(Y, B) ) & NHASTYPE(Z, B) )",
			"( ( ( ( RANGEOF(A, B, UID1) & FROMCONSUMER1(X, A, Y) ) & FROMCONSUMER2(X, A, Z) ) & HASTYPE(Z, B) ) & NHASTYPE(Y, B) )",
			"( ( INVFUNPROPERTY(A, UID) & FROMFRAGMENT(R, A, O) ) & FROMCONSUMER1(S, A, O) )",
			"( ( INVFUNPROPERTY(A, UID) & FROMFRAGMENT(R, A, O) ) & FROMCONSUMER2(S, A, O) )",
			"( ( INVFUNPROPERTY(A, UID) & FROMCONSUMER1(R, A, O) ) & FROMCONSUMER2(S, A, O) )",
			"( ( ( ( EQVPROPERTY(A, B, UID) & FROMFRAGMENT(S, A, N) ) & FROMCONSUMER1(S, B, N) ) & FROMCONSUMER2(S, B, O) ) & NSAME(N, O) ) ",
			"( ( ( ( EQVPROPERTY(A, B, UID) & FROMFRAGMENT(S, A, N) ) & FROMCONSUMER2(S, B, N) ) & FROMCONSUMER1(S, B, O) ) & NSAME(N, O) )",
			"( ( ( ( ( ( EQVPROPERTY(A, B, UID) & FROMFRAGMENT(S, A, N) ) & FROMCONSUMER1(S, B, M) ) & FROMCONSUMER2(S, B, O) ) & NSAME(N, M) ) & NSAME(N, O) ) & NSAME(M, O) )",
			"( ( ( ( ( ( EQVPROPERTY(A, B, UID) & FROMFRAGMENT(S, A, N) ) & FROMCONSUMER2(S, B, M) ) & FROMCONSUMER1(S, B, O) ) & NSAME(N, M) ) & NSAME(N, O) ) & NSAME(M, O) )",
			"( ( ( ( EQVPROPERTY(C, B, UID) & SUBPROPERTYOF(A, B, UID1) ) & FROMFRAGMENT(S, C, N) ) & FROMCONSUMER1(S, A, N) ) & FROMCONSUMER2(S, A, O) )",
			"( ( ( ( EQVPROPERTY(C, B, UID) & SUBPROPERTYOF(A, B, UID1) ) & FROMFRAGMENT(S, C, N) ) & FROMCONSUMER2(S, A, N) ) & FROMCONSUMER1(S, A, O) )",
			"( ( ( ( EQVPROPERTY(C, B, UID) & SUBPROPERTYOF(A, B, UID1) ) & FROMFRAGMENT(S, C, N) ) & FROMCONSUMER1(S, A, M) ) & FROMCONSUMER2(S, A, O) )",
			"( ( ( ( EQVPROPERTY(C, B, UID) & SUBPROPERTYOF(A, B, UID1) ) & FROMFRAGMENT(S, C, N) ) & FROMCONSUMER2(S, A, M) ) & FROMCONSUMER1(S, A, O) )",
			"( ( FROMCONSUMER1(S, A, N) & FROMCONSUMER2(S, A, O) ) & SAMEAS(N, O) )",
			"( ( FROMFRAGMENT(S, A, N) & FROMCONSUMER1(S, A, O) ) & SAMEAS(N, O) )",
			"( ( FROMFRAGMENT(S, A, N) & FROMCONSUMER2(S, A, O) ) & SAMEAS(N, O) )",
			"( ( ( FROMFRAGMENT(T, A, N) & FROMCONSUMER1(S, A, N) ) & FROMCONSUMER2(S, A, O) ) & SAMEAS(T, S) )",
			"( ( ( FROMFRAGMENT(T, A, N) & FROMCONSUMER2(S, A, N) ) & FROMCONSUMER1(S, A, O) ) & SAMEAS(T, S) )",
			"( ( ( FROMFRAGMENT(T, A, N) & FROMCONSUMER1(S, A, M) ) & FROMCONSUMER2(S, A, O) ) & SAMEAS(T, S) )",
			"( ( ( FROMFRAGMENT(T, A, N) & FROMCONSUMER2(S, A, M) ) & FROMCONSUMER1(S, A, O) ) & SAMEAS(T, S) )",
			"( ( ( ( SUBPROPERTYOF(A, B, UID) & FROMFRAGMENT(S, B, N) ) & FROMCONSUMER1(S, A, N) ) & FROMCONSUMER2(S, A, O) ) & NSAME(N, O) )",
			"( ( ( ( SUBPROPERTYOF(A, B, UID) & FROMFRAGMENT(S, B, N) ) & FROMCONSUMER2(S, A, N) ) & FROMCONSUMER1(S, A, O) ) & NSAME(N, O) )",
			"( ( ( ( ( ( SUBPROPERTYOF(A, B, UID) & FROMFRAGMENT(S, B, N) ) & FROMCONSUMER1(S, A, M) ) & FROMCONSUMER2(S, A, O) ) & NSAME(N, M) ) & NSAME(N, O) ) & NSAME(M, O) )",
			"( ( ( ( ( ( SUBPROPERTYOF(A, B, UID) & FROMFRAGMENT(S, B, N) ) & FROMCONSUMER2(S, A, M) ) & FROMCONSUMER1(S, A, O) ) & NSAME(N, M) ) & NSAME(N, O) ) & NSAME(M, O) )",
			"( ( ( ( SUBPROPERTYOF(A, B, UID) & FROMFRAGMENT(S, B, N) ) & FROMCONSUMER1(S, A, N) ) & FROMCONSUMER2(S, A, O) ) & DIFFROM(N, O) )",
			"( ( ( ( SUBPROPERTYOF(A, B, UID) & FROMFRAGMENT(S, B, N) ) & FROMCONSUMER2(S, A, N) ) & FROMCONSUMER1(S, A, O) ) & DIFFROM(N, O) )",
			"( ( ( ( ( ( SUBPROPERTYOF(A, B, UID) & FROMFRAGMENT(S, B, N) ) & FROMCONSUMER1(S, A, M) ) & FROMCONSUMER2(S, A, O) ) & DIFFROM(N, M) ) & DIFFROM(N, O) ) & DIFFROM(M, O) )",
			"( ( ( ( ( ( SUBPROPERTYOF(A, B, UID) & FROMFRAGMENT(S, B, N) ) & FROMCONSUMER2(S, A, M) ) & FROMCONSUMER1(S, A, O) ) & DIFFROM(N, M) ) & DIFFROM(N, O) ) & DIFFROM(M, O) )",
			"( ( ( ( EQVPROPERTY(A, B, UID) & FROMFRAGMENT(S, A, N) ) & FROMCONSUMER1(S, B, N) ) & FROMCONSUMER2(S, B, O) ) & DIFFROM(N, O) )",
			"( ( ( ( EQVPROPERTY(A, B, UID) & FROMFRAGMENT(S, A, N) ) & FROMCONSUMER2(S, B, N) ) & FROMCONSUMER1(S, B, O) ) & DIFFROM(N, O) )",
			"( ( ( ( ( ( EQVPROPERTY(A, B, UID) & FROMFRAGMENT(S, A, N) ) & FROMCONSUMER1(S, B, M) ) & FROMCONSUMER2(S, B, O) ) & DIFFROM(N, M) ) & DIFFROM(N, O) ) & DIFFROM(M, O) )",
			"( ( ( ( ( ( EQVPROPERTY(A, B, UID) & FROMFRAGMENT(S, A, N) ) & FROMCONSUMER2(S, B, M) ) & FROMCONSUMER1(S, B, O) ) & DIFFROM(N, M) ) & DIFFROM(N, O) ) & DIFFROM(M, O) )",
			"~( TYPE(X, A) )",
			"~( RELATEDTO(X, A, Z)",
			"~( ISSAME(Y, Z) )",
			"( ( ( ( FUNPROPERTY(A, UID) & FROMFRAGMENT(S, A, O) ) & FROMCONSUMER1(S, A, N) ) & RESOURCE(N) ) & RESOURCE(O) )",
			"( ( ( ( FUNPROPERTY(A, UID) & FROMFRAGMENT(S, A, O) ) & FROMCONSUMER2(S, A, N) ) & RESOURCE(N) ) & RESOURCE(O) )"
		];
		/*
		 * 			"( ( ( FUNPROPERTY(A, UID) & FROMFRAGMENT(S, A, O) ) & FROMCONSUMER1(S, A, N) ) & NDISJOINTFROM(O, N) )",
		 "( ( ( FUNPROPERTY(A, UID) & FROMFRAGMENT(S, A, O) ) & FROMCONSUMER2(S, A, N) ) & NDISJOINTFROM(O, N) )",
		 "( ( ( FUNPROPERTY(A, UID) & FROMCONSUMER1(S, A, O) ) & FROMCONSUMER2(S, A, N) ) & NDISJOINTFROM(O, N) )",
		 "( ( ( FUNPROPERTY(A, UID) & FROMCONSUMER1(S, A, O) ) & FROMCONSUMER2(S, A, N) ) & NDISJOINTFROM(O, N) )",
		 "( ( ( FUNPROPERTY(A, UID) & FROMFRAGMENT(S, A, O) ) & FROMCONSUMER1(S, A, N) ) & NDIFFROM(O, N) )",
		 "( ( ( FUNPROPERTY(A, UID) & FROMFRAGMENT(S, A, O) ) & FROMCONSUMER2(S, A, N) ) & NDIFFROM(O, N) )",
		 "( ( ( FUNPROPERTY(A, UID) & FROMCONSUMER1(S, A, O) ) & FROMCONSUMER2(S, A, N) ) & NDIFFROM(O, N) )",
		 "( ( ( FUNPROPERTY(A, UID) & FROMCONSUMER1(S, A, O) ) & FROMCONSUMER2(S, A, N) ) & NDIFFROM(O, N) )",
		 "( ( ( FUNPROPERTY(A, UID) & FROMFRAGMENT(S, A, O) ) & FROMCONSUMER1(S, A, N) ) & SAMEAS(O, N) )",
		 "( ( ( FUNPROPERTY(A, UID) & FROMFRAGMENT(S, A, O) ) & FROMCONSUMER2(S, A, N) ) & SAMEAS(O, N) )",
		 "( ( ( FUNPROPERTY(A, UID) & FROMCONSUMER1(S, A, O) ) & FROMCONSUMER2(S, A, N) ) & SAMEAS(O, N) )",
		 "( ( ( FUNPROPERTY(A, UID) & FROMCONSUMER1(S, A, O) ) & FROMCONSUMER2(S, A, N) ) & SAMEAS(O, N) )"
		 */

		Iterable<Kernel> k = m.getKernels();
		for (Kernel gk : k) {
			try {
				CompatibilityKernel c = (CompatibilityKernel) gk;
				String s = c.toString();

				if (s.contains(rules[0])) {
					weightMap.remove("sim1");
					weightMap.put("sim1", c.getWeight().getWeight());
				}
				else if (s.contains(rules[1])){
					weightMap.remove("sim2");
					weightMap.put("sim2", c.getWeight().getWeight());
				}
				else if (s.contains(rules[2])){
					weightMap.remove("dom1");
					weightMap.put("dom1", c.getWeight().getWeight());
				}
				else if (s.contains(rules[3])){
					weightMap.remove("dom2");
					weightMap.put("dom2", c.getWeight().getWeight());
				}
				else if (s.contains(rules[4])){
					weightMap.remove("dom3");
					weightMap.put("dom3", c.getWeight().getWeight());
				}
				else if (s.contains(rules[5])){
					weightMap.remove("dom4");
					weightMap.put("dom4", c.getWeight().getWeight());
				}
				else if (s.contains(rules[6])){
					weightMap.remove("dom5");
					weightMap.put("dom5", c.getWeight().getWeight());
				}
				else if (s.contains(rules[7])){
					weightMap.remove("dom6");
					weightMap.put("dom6", c.getWeight().getWeight());
				}
				else if (s.contains(rules[8])){
					weightMap.remove("dom7");
					weightMap.put("dom7", c.getWeight().getWeight());
				}
				else if (s.contains(rules[9])){
					weightMap.remove("dom8");
					weightMap.put("dom8", c.getWeight().getWeight());
				}
				else if (s.contains(rules[10])){
					weightMap.remove("ran1");
					weightMap.put("ran1", c.getWeight().getWeight());
				}
				else if (s.contains(rules[11])){
					weightMap.remove("ran2");
					weightMap.put("ran2", c.getWeight().getWeight());
				}
				else if (s.contains(rules[12])){
					weightMap.remove("ran3");
					weightMap.put("ran3", c.getWeight().getWeight());
				}
				else if (s.contains(rules[13])){
					weightMap.remove("ran4");
					weightMap.put("ran4", c.getWeight().getWeight());
				}
				else if (s.contains(rules[14])){
					weightMap.remove("ran5");
					weightMap.put("ran5", c.getWeight().getWeight());
				}
				else if (s.contains(rules[15])){
					weightMap.remove("ran6");
					weightMap.put("ran6", c.getWeight().getWeight());
				}
				else if (s.contains(rules[16])){
					weightMap.remove("ran7");
					weightMap.put("ran7", c.getWeight().getWeight());
				}
				else if (s.contains(rules[17])){
					weightMap.remove("ran8");
					weightMap.put("ran8", c.getWeight().getWeight());
				}
				else if (s.contains(rules[18])){
					weightMap.remove("ran9");
					weightMap.put("ran9", c.getWeight().getWeight());
				}
				else if (s.contains(rules[19])){
					weightMap.remove("ran10");
					weightMap.put("ran10", c.getWeight().getWeight());
				}
				else if (s.contains(rules[20])){
					weightMap.remove("ifp1");
					weightMap.put("ifp1", c.getWeight().getWeight());
				}
				else if (s.contains(rules[21])){
					weightMap.remove("ifp2");
					weightMap.put("ifp2", c.getWeight().getWeight());
				}
				else if (s.contains(rules[22])){
					weightMap.remove("ifp3");
					weightMap.put("ifp3", c.getWeight().getWeight());
				}
				else if (s.contains(rules[23])){
					weightMap.remove("ep1");
					weightMap.put("ep1", c.getWeight().getWeight());
				}
				else if (s.contains(rules[24])){
					weightMap.remove("ep2");
					weightMap.put("ep2", c.getWeight().getWeight());
				}
				else if (s.contains(rules[25])){
					weightMap.remove("ep3");
					weightMap.put("ep3", c.getWeight().getWeight());
				}
				else if (s.contains(rules[26])){
					weightMap.remove("ep4");
					weightMap.put("ep4", c.getWeight().getWeight());
				}
				else if (s.contains(rules[27])){
					weightMap.remove("ep5");
					weightMap.put("ep5", c.getWeight().getWeight());
				}
				else if (s.contains(rules[28])){
					weightMap.remove("ep6");
					weightMap.put("ep6", c.getWeight().getWeight());
				}
				else if (s.contains(rules[29])){
					weightMap.remove("ep7");
					weightMap.put("ep7", c.getWeight().getWeight());
				}
				else if (s.contains(rules[30])){
					weightMap.remove("ep8");
					weightMap.put("ep8", c.getWeight().getWeight());
				}
				else if (s.contains(rules[31])){
					weightMap.remove("sa1");
					weightMap.put("sa1", c.getWeight().getWeight());
				}
				else if (s.contains(rules[32])){
					weightMap.remove("sa2");
					weightMap.put("sa2", c.getWeight().getWeight());
				}
				else if (s.contains(rules[33])){
					weightMap.remove("sa3");
					weightMap.put("sa3", c.getWeight().getWeight());
				}
				else if (s.contains(rules[34])){
					weightMap.remove("sa4");
					weightMap.put("sa4", c.getWeight().getWeight());
				}
				else if (s.contains(rules[35])){
					weightMap.remove("sa5");
					weightMap.put("sa5", c.getWeight().getWeight());
				}
				else if (s.contains(rules[36])){
					weightMap.remove("sa6");
					weightMap.put("sa6", c.getWeight().getWeight());
				}
				else if (s.contains(rules[37])){
					weightMap.remove("sa7");
					weightMap.put("sa7", c.getWeight().getWeight());
				}
				else if (s.contains(rules[38])){
					weightMap.remove("sp1");
					weightMap.put("sp1", c.getWeight().getWeight());
				}
				else if (s.contains(rules[39])){
					weightMap.remove("sp2");
					weightMap.put("sp2", c.getWeight().getWeight());
				}
				else if (s.contains(rules[40])){
					weightMap.remove("sp3");
					weightMap.put("sp3", c.getWeight().getWeight());
				}
				else if (s.contains(rules[41])){
					weightMap.remove("sp4");
					weightMap.put("sp4", c.getWeight().getWeight());
				}
				else if (s.contains(rules[42])){
					weightMap.remove("df1");
					weightMap.put("df1", c.getWeight().getWeight());
				}
				else if (s.contains(rules[43])){
					weightMap.remove("df2");
					weightMap.put("df2", c.getWeight().getWeight());
				}
				else if (s.contains(rules[44])){
					weightMap.remove("df3");
					weightMap.put("df3", c.getWeight().getWeight());
				}
				else if (s.contains(rules[45])){
					weightMap.remove("df4");
					weightMap.put("df4", c.getWeight().getWeight());
				}
				else if (s.contains(rules[46])){
					weightMap.remove("df5");
					weightMap.put("df5", c.getWeight().getWeight());
				}
				else if (s.contains(rules[47])){
					weightMap.remove("df6");
					weightMap.put("df6", c.getWeight().getWeight());
				}
				else if (s.contains(rules[48])){
					weightMap.remove("df7");
					weightMap.put("df7", c.getWeight().getWeight());
				}
				else if (s.contains(rules[49])){
					weightMap.remove("df8");
					weightMap.put("df8", c.getWeight().getWeight());
				}
				else if (s.contains(rules[50])){
					weightMap.remove("type");
					weightMap.put("type", c.getWeight().getWeight());
				}
				else if (s.contains(rules[51])){
					weightMap.remove("isSame");
					weightMap.put("isSame", c.getWeight().getWeight());
				}
				else if (s.contains(rules[52])){
					weightMap.remove("related");
					weightMap.put("related", c.getWeight().getWeight());
				}
				else if (s.contains(rules[53])){
					weightMap.remove("fp1");
					weightMap.put("fp1", c.getWeight().getWeight());
				}
				else if (s.contains(rules[54])){
					weightMap.remove("fp2");
					weightMap.put("fp2", c.getWeight().getWeight());
				}
				/*	 else if (s.contains(rules[55])){
				 weightMap.remove("fp3");
				 weightMap.put("fp3", c.getWeight().getWeight());
				 }
				 else if (s.contains(rules[56])){
				 weightMap.remove("fp4");
				 weightMap.put("fp4", c.getWeight().getWeight());
				 }
				 else if (s.contains(rules[57])){
				 weightMap.remove("fp5");
				 weightMap.put("fp5", c.getWeight().getWeight());
				 }
				 else if (s.contains(rules[58])){
				 weightMap.remove("fp6");
				 weightMap.put("fp6", c.getWeight().getWeight());
				 };
				 else if (s.contains(rules[59])){
				 weightMap.remove("fp7");
				 weightMap.put("fp7", c.getWeight().getWeight());
				 }
				 else if (s.contains(rules[60])){
				 weightMap.remove("fp8");
				 weightMap.put("fp8", c.getWeight().getWeight());
				 }
				 else if (s.contains(rules[61])){
				 weightMap.remove("fp9");
				 weightMap.put("fp9", c.getWeight().getWeight());
				 }
				 else if (s.contains(rules[62])){
				 weightMap.remove("fp10");
				 weightMap.put("fp10", c.getWeight().getWeight());
				 }
				 else if (s.contains(rules[63])){
				 weightMap.remove("fp11");
				 weightMap.put("fp11", c.getWeight().getWeight());
				 }
				 else if (s.contains(rules[64])){
				 weightMap.remove("fp12");
				 weightMap.put("fp12", c.getWeight().getWeight());
				 }*/
			} catch(org.codehaus.groovy.runtime.typehandling.GroovyCastException r) {
			}
		}
		String content = "";
		Iterator<String> keys = weightMap.keySet().iterator();
		while(keys.hasNext()) {
			String key = keys.next();
			Double val = weightMap.get(key);
			content += "'" + key + "':" + val + "\n";
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
			weightMap.putAt (x, y);
		}
		br.close();
		return weightMap ;
	}

	protected static File createfile (String filename) {
		File file = new File(filename);
		if(!file.exists())
			file.createNewFile();
		else {
			file.delete();
			file.createNewFile();
		}
		return file;
	}
	protected static void writer (String filename, String content) throws IOException{
		File file = createfile(filename);
		FileWriter fw = new FileWriter(file.getAbsoluteFile(), true);
		BufferedWriter bw = new BufferedWriter(fw);
		bw.write(content);
		bw.close();
	}
	/////////////// write
	protected static void write (String filename, String content) throws IOException{
		writer(trainDir + filename, content);
		writer(testDir + filename, content);
	}	
}
