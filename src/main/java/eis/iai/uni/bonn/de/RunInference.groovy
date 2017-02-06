package eis.iai.uni.bonn.de;

import java.io.File;
import java.io.IOException;
import java.text.DecimalFormat;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import org.apache.jena.rdf.model.Model;
import org.apache.jena.util.FileManager;
import org.apache.jena.ontology.OntClass;
import org.apache.jena.rdf.model.Property;
import org.apache.jena.rdf.model.ResIterator;
import org.apache.jena.rdf.model.Resource;

import edu.umd.cs.psl.groovy.*;
import edu.umd.cs.psl.ui.loading.InserterUtils;
import edu.umd.cs.psl.util.database.Queries;
import edu.umd.cs.psl.model.argument.GroundTerm;
import edu.umd.cs.psl.model.predicate.Predicate;
import edu.umd.cs.psl.model.atom.GroundAtom;
import edu.umd.cs.psl.model.atom.RandomVariableAtom;
import edu.umd.cs.psl.application.inference.LazyMPEInference
import edu.umd.cs.psl.application.inference.MPEInference;
import edu.umd.cs.psl.application.learning.weight.maxlikelihood.MaxLikelihoodMPE;
import edu.umd.cs.psl.config.*;
import edu.umd.cs.psl.database.DataStore;
import edu.umd.cs.psl.database.Database;
import edu.umd.cs.psl.database.Partition;
import groovy.time.*;

class RunInference {

	HashSet openPredsAll = new HashSet<Predicate>();
	HashSet closedPredsAll= new HashSet<Predicate>();
	Set<String> res_set = new HashSet<String>();

	public RunInference(PSLModel m, String [] datasets) {
		// leave the predicates type,issame,relatedto open to infer its atoms' values.
		openPredsAll.addAll(m.getPredicate("type"), m.getPredicate("relatedTo"), m.getPredicate("isSame"), m.getPredicate("fromFragment"), 
			m.getPredicate("diffrom"), m.getPredicate("sameas"));
		
		//close all the predicates to treat those atoms as observed
		closedPredsAll.addAll(m.getPredicate("fromDataset"), m.getPredicate("fromConsumer1"), m.getPredicate("fromConsumer2"), 
			m.getPredicate("domainOf"), m.getPredicate("rangeOf"), m.getPredicate("subclassOf"), m.getPredicate("owlclass"), 
			m.getPredicate("eqvclass"), m.getPredicate("subpropertyOf"), m.getPredicate("eqvproperty"), m.getPredicate("funProperty"), 
			m.getPredicate("invFunProperty"), m.getPredicate("onproperty"), m.getPredicate("hasValue"), m.getPredicate("maxCardinality"));
		listResources(datasets);
	}

	/////////////////////////// test inference //////////////////////////////////
	void test (InferenceUtils r, PSLModel m, DataStore data, String dir, ConfigBundle config, String [] datasets) {
		Date testingInference_time = new Date();
		String testDir = dir+"test"+java.io.File.separator;
		Partition testObservations = new Partition(3);	//read partition
		Partition testPredictions = new Partition(4);	//write partition

		r.loadPredicateAtoms(data, closedPredsAll, testDir, testObservations);

		Database testDB = data.getDatabase(testPredictions, closedPredsAll, testObservations);
		//populateType(m, testDB, datasets);
		//populaterelatedTo(m, testDB);
		//populateisSame(m, testDB);
		populateFragment(m, testDB);

		System.out.println("INFERRING...");
		//LazyMPEInference inference = new LazyMPEInference(m, testDB, config);
		MPEInference inference = new MPEInference(m, testDB, config);
		inference.mpeInference();
		inference.close();
		Date testingInferencefinished_time = new Date();

		System.out.println("INFERENCE DONE");
		r.print_results(testDB,openPredsAll);
		testDB.close();
		System.out.println("Total testing time "+ TimeCategory.minus(testingInferencefinished_time, testingInference_time));
	}

	//////////////////////////// weight learning ///////////////////////////
	void learn (InferenceUtils r, PSLModel m, DataStore data, String dir, ConfigBundle config, String [] datasets) {
		Date trainingInference_time = new Date();
		/* Loads data */
		String trainDir = dir+"train"+java.io.File.separator;
		Partition trainObservations = new Partition(0);		//read partition
		r.loadPredicateAtoms(data, closedPredsAll, trainDir, trainObservations);

		/* We first create a second partition and open it as the write partition of a Database from the DataStore.
		 * We also include the evidence partition as a read partition.*/

		Partition trainPredictions = new Partition(1);	//write partition
		Database trainDB = data.getDatabase(trainPredictions, closedPredsAll, trainObservations);
	//	populateType(m, trainDB, datasets);
	//	populaterelatedTo(m, trainDB);
	//	populateisSame(m, trainDB);
		populateFragment(m, trainDB);	//fragment+dfrom

		Partition truth = new Partition(2);		//truth partition
		r.loadPredicateAtomsWithValue(data, openPredsAll, trainDir, truth);
		Database truthDB = data.getDatabase(truth, openPredsAll as Set);

		System.out.println("LEARNING WEIGHTS...");

		MaxLikelihoodMPE weightLearning = new MaxLikelihoodMPE(m, trainDB, truthDB, config);
		weightLearning.learn();
		weightLearning.close();

//		mpe = new LazyMPEInference(m, truthDB, config);
//		result = mpe.mpeInference();
		
		trainDB.close();
		truthDB.close();

		Date trainingInferencefinished_time = new Date();

		System.out.println("LEARNING WEIGHTS DONE \n" + m + "\n /////////////////////////////////////////");
		System.out.println("Total training time "+ TimeCategory.minus(trainingInferencefinished_time, trainingInference_time));
	}

	

	void listResources (String [] datasets) {	
		ResIterator bresiter = FileManager.get().loadModel(datasets[0], datasets[4]).listResourcesWithProperty((Property)null);
		while (bresiter.hasNext())
			res_set.add(bresiter.next().toString());
		
		ResIterator sresiter = FileManager.get().loadModel(datasets[1], datasets[4]).listResourcesWithProperty((Property)null);
		while (sresiter.hasNext())
			res_set.add(sresiter.next().toString());
		
		ResIterator tresiter = FileManager.get().loadModel(datasets[2], datasets[4]).listResourcesWithProperty((Property)null);
		while (tresiter.hasNext())
			res_set.add(tresiter.next().toString());
	}
	
	
	//////////////////////////////populate/////////////////////////////////////////
	void populateFragment(PSLModel m, Database db) {
		Set<GroundTerm> s1 = new HashSet<GroundTerm>();
		Set<GroundTerm> s2 = new HashSet<GroundTerm>();
	//	Set<GroundTerm> s = new HashSet<GroundTerm>();
	//	Set<GroundTerm> s0 = new HashSet<GroundTerm>();
		
		Set<GroundAtom> ds = Queries.getAllAtoms(db, m.getPredicate("fromDataset"));
		for (GroundAtom atom : ds) {
			GroundTerm term1 = atom.getArguments()[0];
			GroundTerm term2 = atom.getArguments()[1];
			GroundTerm term3 = atom.getArguments()[2];
			//relatedto
			((RandomVariableAtom) db.getAtom(m.getPredicate("relatedTo"),term1,term2,term3)).commitToDB();
			
			//type
			s1.add(term1);
			if (res_set.contains(term3.getValue()))
				s1.add(term3);
			//same
			//	s.add(term3);
			//frag	
			((RandomVariableAtom) db.getAtom(m.getPredicate("fromFragment"), term1, term2, term3)).commitToDB();
			if (term2.getValue() == "http://www.w3.org/2002/07/owl#differentFrom") {
				((RandomVariableAtom) db.getAtom(m.getPredicate("diffrom"), term1, term3)).commitToDB();
				((RandomVariableAtom) db.getAtom(m.getPredicate("diffrom"), term3, term1)).commitToDB();
			} else if (term2.getValue() == "http://www.w3.org/2002/07/owl#sameAs") {
				((RandomVariableAtom) db.getAtom(m.getPredicate("sameas"), term1, term3)).commitToDB();
				((RandomVariableAtom) db.getAtom(m.getPredicate("sameas"), term3, term1)).commitToDB();
			}
		}

		Set<GroundAtom> ds1 = Queries.getAllAtoms(db, m.getPredicate("fromConsumer1"));
		ds1.addAll(Queries.getAllAtoms(db, m.getPredicate("fromConsumer2")));
		for (GroundAtom atom : ds1) {
			GroundTerm term1 = atom.getArguments()[0];
			GroundTerm term2 = atom.getArguments()[1];
			GroundTerm term3 = atom.getArguments()[2];
			//relatedto
			((RandomVariableAtom) db.getAtom(m.getPredicate("relatedTo"),term1,term2,term3)).commitToDB();
			//type
			s1.add(term1);
			if (res_set.contains(term3.getValue()))
				s1.add(term3);
			//same
			//	s0.add(term3);
			//frag		
			if (term2.getValue() == "http://www.w3.org/2002/07/owl#differentFrom") {
				((RandomVariableAtom) db.getAtom(m.getPredicate("diffrom"), term1, term3)).commitToDB();
				((RandomVariableAtom) db.getAtom(m.getPredicate("diffrom"), term3, term1)).commitToDB();
			} else if (term2.getValue() == "http://www.w3.org/2002/07/owl#sameAs") {
				((RandomVariableAtom) db.getAtom(m.getPredicate("sameas"), term1, term3)).commitToDB();
				((RandomVariableAtom) db.getAtom(m.getPredicate("sameas"), term3, term1)).commitToDB();
			}
		}

		
		/// for same
		for (GroundTerm a : s1) {
			for (GroundTerm b : s1) {
				((RandomVariableAtom) db.getAtom(m.getPredicate("isSame"), a, b)).commitToDB();
				((RandomVariableAtom) db.getAtom(m.getPredicate("isSame"), b, a)).commitToDB();
			}
		}
	
		/// for type
		Set<GroundAtom> typeclass = Queries.getAllAtoms(db, m.getPredicate("owlclass"));
		for (GroundAtom atom : typeclass)
			s2.add(atom.getArguments()[0]);
		
		typeclass = Queries.getAllAtoms(db, m.getPredicate("domainOf"));
		typeclass.addAll(Queries.getAllAtoms(db, m.getPredicate("rangeOf")));
		for (GroundAtom atom : typeclass)
			s2.add(atom.getArguments()[1]);
		
		for (GroundTerm a : s1) {
			for (GroundTerm b : s2)
				((RandomVariableAtom) db.getAtom(m.getPredicate("type"), a, b)).commitToDB();
		}
		
		for (GroundAtom atom : ds1) {
			for (GroundAtom dsatom : ds)
				((RandomVariableAtom) db.getAtom(m.getPredicate("relatedTo"),atom.getArguments()[0],atom.getArguments()[1],dsatom.getArguments()[2])).commitToDB();
		}
	}
	/* Populates all the type atoms using the triple and domainOf predicates. */
/*	void populateType (PSLModel m, Database db, String [] datasets) {
		Set<GroundTerm> s1 = new HashSet<GroundTerm>();
		Set<GroundTerm> s2 = new HashSet<GroundTerm>();

		Set<GroundAtom> ds = Queries.getAllAtoms(db, m.getPredicate("fromDataset"));
		Set<GroundAtom> src = Queries.getAllAtoms(db, m.getPredicate("fromConsumer1"));
		Set<GroundAtom> tar = Queries.getAllAtoms(db, m.getPredicate("fromConsumer2"));

		for (GroundAtom atom : ds) {
			s1.add(atom.getArguments()[0]);
			GroundTerm term = atom.getArguments()[2];
			if (res_set.contains(term.getValue()))
				s1.add(term);
		}

		for (GroundAtom atom : src) {
			s1.add(atom.getArguments()[0]);
			GroundTerm term = atom.getArguments()[2];
			if (res_set.contains(term.getValue()))
				s1.add(term);
		}
		for (GroundAtom atom : tar) {
			s1.add(atom.getArguments()[0]);
			GroundTerm term = atom.getArguments()[2];
			if (res_set.contains(term.getValue()))
				s1.add(term);
		}

		Set<GroundAtom> typeclass = Queries.getAllAtoms(db, m.getPredicate("owlclass"));
		for (GroundAtom atom : typeclass) 
			s2.add(atom.getArguments()[0]);
		
		typeclass = Queries.getAllAtoms(db, m.getPredicate("domainOf"));
		for (GroundAtom atom : typeclass) 
			s2.add(atom.getArguments()[1]);
		
		typeclass = Queries.getAllAtoms(db, m.getPredicate("rangeOf"));
		for (GroundAtom atom : typeclass) 
			s2.add(atom.getArguments()[1]);
		
		for (GroundTerm a : s1) {
			for (GroundTerm b : s2)
				((RandomVariableAtom) db.getAtom(m.getPredicate("type"), a, b)).commitToDB();
		}
	}


	// Populates all the isSame atoms using the resources in datasets. 
	void populateisSame(PSLModel m, Database db) {
		Set<GroundAtom> ds = Queries.getAllAtoms(db, m.getPredicate("fromDataset"));
		Set<GroundAtom> src = Queries.getAllAtoms(db, m.getPredicate("fromConsumer1"));
		Set<GroundAtom> tar = Queries.getAllAtoms(db, m.getPredicate("fromConsumer2"));

		Set<GroundTerm> s = new HashSet<GroundTerm>();
		Set<GroundTerm> s0 = new HashSet<GroundTerm>();

		for (GroundAtom atom : src) 
			s.add(atom.getArguments()[2]);
		for (GroundAtom atom : tar) 
			s0.add(atom.getArguments()[2]);
		
		for (GroundTerm a : s) {
			for (GroundTerm b : s0) {
				((RandomVariableAtom) db.getAtom(m.getPredicate("isSame"), a, b)).commitToDB();
				((RandomVariableAtom) db.getAtom(m.getPredicate("isSame"), b, a)).commitToDB();
			}
		}

		Set<GroundTerm> s1 = new HashSet<GroundTerm>();
		Set<GroundTerm> s2 = new HashSet<GroundTerm>();
		for (GroundAtom atom : ds) 
			s1.add(atom.getArguments()[0]);
		for (GroundAtom atom : src) 
			s2.add(atom.getArguments()[0]);
		for (GroundAtom atom : tar) 
			s2.add(atom.getArguments()[0]);
		
		for (GroundTerm a : s1) {
			for (GroundTerm b : s2) {
				((RandomVariableAtom) db.getAtom(m.getPredicate("isSame"), a, b)).commitToDB();
				((RandomVariableAtom) db.getAtom(m.getPredicate("isSame"), b, a)).commitToDB();
			}
		}
	}

	// Populates all the relatedTo atoms using the resources in datasets. 

	void populaterelatedTo(PSLModel m, Database db) {
		Set<GroundAtom> ds = Queries.getAllAtoms(db, m.getPredicate("fromDataset"));
		Set<GroundAtom> src = Queries.getAllAtoms(db, m.getPredicate("fromConsumer1"));
		Set<GroundAtom> tar = Queries.getAllAtoms(db, m.getPredicate("fromConsumer2"));

		for (GroundAtom atom : ds) 
			((RandomVariableAtom) db.getAtom(m.getPredicate("relatedTo"),atom.getArguments()[0],atom.getArguments()[1],atom.getArguments()[2])).commitToDB();	
		for (GroundAtom atom : src) 
			((RandomVariableAtom) db.getAtom(m.getPredicate("relatedTo"),atom.getArguments()[0],atom.getArguments()[1],atom.getArguments()[2])).commitToDB();		
		for (GroundAtom atom : tar) 
			((RandomVariableAtom) db.getAtom(m.getPredicate("relatedTo"),atom.getArguments()[0],atom.getArguments()[1],atom.getArguments()[2])).commitToDB();

		for (GroundAtom atom : src) {
			for (GroundAtom dsatom : ds)
				((RandomVariableAtom) db.getAtom(m.getPredicate("relatedTo"),atom.getArguments()[0],atom.getArguments()[1],dsatom.getArguments()[2])).commitToDB();
		}
		for (GroundAtom atom : tar) {
			for (GroundAtom dsatom : ds)
				((RandomVariableAtom) db.getAtom(m.getPredicate("relatedTo"),atom.getArguments()[0],atom.getArguments()[1],dsatom.getArguments()[2])).commitToDB();
		}
	}*/
}
