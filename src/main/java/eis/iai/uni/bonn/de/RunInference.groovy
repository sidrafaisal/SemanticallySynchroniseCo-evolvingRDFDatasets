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
	
	public RunInference(PSLModel m) {
		/* We close all the predicates since we want to treat those atoms as observed, and leave the predicates
		 * type,issame,relatedto open to infer its atoms' values.*/
		
		openPredsAll.add(m.getPredicate("type"));
		openPredsAll.add(m.getPredicate("relatedTo"));
		openPredsAll.add(m.getPredicate("isSame"));
		
		closedPredsAll.add(m.getPredicate("fromFragment"));
		closedPredsAll.add(m.getPredicate("fromConsumer1"));
		closedPredsAll.add(m.getPredicate("fromConsumer2"));
		closedPredsAll.add(m.getPredicate("domainOf"));
		closedPredsAll.add(m.getPredicate("rangeOf"));
		closedPredsAll.add(m.getPredicate("subclassOf"));
		closedPredsAll.add(m.getPredicate("eqvclass"));
		closedPredsAll.add(m.getPredicate("subpropertyOf"));
		closedPredsAll.add(m.getPredicate("eqvproperty"));
		closedPredsAll.add(m.getPredicate("funProperty"));
		closedPredsAll.add(m.getPredicate("invFunProperty"));
		closedPredsAll.add(m.getPredicate("onproperty"));
		closedPredsAll.add(m.getPredicate("hasValue"));
		closedPredsAll.add(m.getPredicate("maxCardinality"));
	}
	
	/////////////////////////// test inference //////////////////////////////////
	void test (InferenceUtils r, PSLModel m, DataStore data, String dir, ConfigBundle config, String [] datasets, LoadData  l, LoadOntology lont) {
		Date testingInference_time = new Date();
		String testDir = dir+"test"+java.io.File.separator;
		Partition testObservations = new Partition(3);	//read partition
		Partition testPredictions = new Partition(4);	//write partition

		r.loadPredicateAtoms(data, closedPredsAll, testDir, testObservations);

		Database testDB = data.getDatabase(testPredictions, closedPredsAll, testObservations);
		populateType(m, testDB, datasets,l,lont);
		populaterelatedTo(m, testDB);
		populateisSame(m, testDB);

		System.out.println("INFERRING...");
		LazyMPEInference inference = new LazyMPEInference(m, testDB, config);
		//MPEInference inference = new MPEInference(m, testDB, config);
		inference.mpeInference();
		inference.close();
		Date testingInferencefinished_time = new Date();

		System.out.println("INFERENCE DONE");
		r.print_results(testDB,openPredsAll);
		testDB.close();

		TimeDuration td = TimeCategory.minus(testingInferencefinished_time, testingInference_time);
		System.out.println("Total testing time "+td);
	}

	//////////////////////////// weight learning ///////////////////////////	
	void learn (InferenceUtils r, PSLModel m, DataStore data, String dir, ConfigBundle config, String [] datasets, LoadData  l, LoadOntology lont) {
		Date trainingInference_time = new Date();
		/* Loads data */
		String trainDir = dir+"train"+java.io.File.separator;
		Partition trainObservations = new Partition(0);		//read partition
		r.loadPredicateAtoms(data, closedPredsAll, trainDir, trainObservations);

		/* We first create a second partition and open it as the write partition of a Database from the DataStore.
		 * We also include the evidence partition as a read partition.*/

		Partition trainPredictions = new Partition(1);	//write partition
		Database trainDB = data.getDatabase(trainPredictions, closedPredsAll, trainObservations);
		populateType(m, trainDB, datasets,l,lont);
		populaterelatedTo(m, trainDB);
		populateisSame(m, trainDB);

		Partition truth = new Partition(2);		//truth partition
		r.loadPredicateAtomsWithValue(data, openPredsAll, trainDir, truth);
		Database truthDB = data.getDatabase(truth, openPredsAll as Set);

		System.out.println("LEARNING WEIGHTS...");

		MaxLikelihoodMPE weightLearning = new MaxLikelihoodMPE(m, trainDB, truthDB, config);
		weightLearning.learn();
		weightLearning.close();

		trainDB.close();
		truthDB.close();

		Date trainingInferencefinished_time = new Date();

		System.out.println("LEARNING WEIGHTS DONE");
		System.out.println(m);
		System.out.println("/////////////////////////////////////////");
		TimeDuration td = TimeCategory.minus(trainingInferencefinished_time, trainingInference_time);
		System.out.println("Total training time "+td);
	}

	//////////////////////////////populate/////////////////////////////////////////

	/* Populates all the type atoms using the triple and domainOf predicates. */
	void populateType(PSLModel m, Database db, String [] datasets, LoadData l, LoadOntology lont) {

		Set<GroundTerm> s1 = new HashSet<GroundTerm>();
		Set<GroundTerm> s2 = new HashSet<GroundTerm>();
		Set<String> res_set = new HashSet<String>();

		Model bmodel = FileManager.get().loadModel(datasets[0], datasets[4]);
		Model smodel = FileManager.get().loadModel(datasets[1], datasets[4]);
		Model tmodel = FileManager.get().loadModel(datasets[2], datasets[4]);

		ResIterator bresiter = bmodel.listResourcesWithProperty((Property)null);
		ResIterator sresiter = smodel.listResourcesWithProperty((Property)null);
		ResIterator tresiter = tmodel.listResourcesWithProperty((Property)null);

		while (bresiter.hasNext()) {
			Resource res = bresiter.next();
			res_set.add(res.toString());
		}
		while (sresiter.hasNext()) {
			Resource res = sresiter.next();
			res_set.add(res.toString());
		}
		while (tresiter.hasNext()) {
			Resource res = tresiter.next();//	res_set.add("'"+res.toString()+"'");
			res_set.add(res.toString());
		}
		
		Set<GroundAtom> ds = Queries.getAllAtoms(db, m.getPredicate("fromFragment"));
		Set<GroundAtom> src = Queries.getAllAtoms(db, m.getPredicate("fromConsumer1"));
		Set<GroundAtom> tar = Queries.getAllAtoms(db, m.getPredicate("fromConsumer2"));

		Set<GroundAtom> belongsto0 = Queries.getAllAtoms(db, m.getPredicate("domainOf"));
		Set<GroundAtom> belongsto1 = Queries.getAllAtoms(db, m.getPredicate("rangeOf"));

		for (GroundAtom atom : ds) {
			GroundTerm term = atom.getArguments()[0];
			String value = term.getValue();
			if (res_set.contains(value))
				s1.add(term);

			term = atom.getArguments()[2];
			value = term.getValue();

			Resource x = l.model.getResource(value);
			if (x!=null) {
				OntClass sc = lont.omodel.getOntClass(x.toString());
				if (sc!=null)
					s2.add(term);
			}

			if (res_set.contains(value))
				s1.add(term);
		}
		for (GroundAtom atom : src) {
			GroundTerm term = atom.getArguments()[0];
			String value = term.getValue();
			if (res_set.contains(value))
				s1.add(term);

			term = atom.getArguments()[2];
			value = term.getValue();
			Resource x = l.model.getResource(value);
			if (x!=null) {
				OntClass sc = lont.omodel.getOntClass(x.toString());
				if (sc!=null)
					s2.add(term);
			}
			if (res_set.contains(value))
				s1.add(term);
		}
		for (GroundAtom atom : tar) {
			GroundTerm term = atom.getArguments()[0];
			String value = term.getValue();
			if (res_set.contains(value))
				s1.add(term);

			term = atom.getArguments()[2];
			value = term.getValue();
			Resource x = l.model.getResource(value);
			if (x!=null) {
				OntClass sc = lont.omodel.getOntClass(x.toString());
				if (sc!=null)
					s2.add(term);
			}
			if (res_set.contains(value))
				s1.add(term);
		}
		for (GroundAtom atom : belongsto0) {
			GroundTerm term = atom.getArguments()[1];
			s2.add(term);
		}
		for (GroundAtom atom : belongsto1) {
			GroundTerm term = atom.getArguments()[1];
			s2.add(term);
		}
		for (GroundTerm a : s1) {
			for (GroundTerm b : s2) {
				((RandomVariableAtom) db.getAtom(m.getPredicate("type"), a, b)).commitToDB();
			}
		}
	}


	/* Populates all the isSame atoms using the resources in datasets. */
	void populateisSame(PSLModel m, Database db) {
		Set<GroundAtom> ds = Queries.getAllAtoms(db, m.getPredicate("fromFragment"));
		Set<GroundAtom> src = Queries.getAllAtoms(db, m.getPredicate("fromConsumer1"));
		Set<GroundAtom> tar = Queries.getAllAtoms(db, m.getPredicate("fromConsumer2"));

		Set<GroundTerm> s = new HashSet<GroundTerm>();
		Set<GroundTerm> s0 = new HashSet<GroundTerm>();

		for (GroundAtom atom : src) {
			s.add(atom.getArguments()[2]);
		}
		for (GroundAtom atom : tar) {
			s0.add(atom.getArguments()[2]);
		}
		for (GroundTerm a : s) {
			for (GroundTerm b : s0) {
				((RandomVariableAtom) db.getAtom(m.getPredicate("isSame"), a, b)).commitToDB();
				((RandomVariableAtom) db.getAtom(m.getPredicate("isSame"), b, a)).commitToDB();
			}
		}

		Set<GroundTerm> s1 = new HashSet<GroundTerm>();
		Set<GroundTerm> s2 = new HashSet<GroundTerm>();
		for (GroundAtom atom : ds) {
			s1.add(atom.getArguments()[0]);
		}
		for (GroundAtom atom : src) {
			s2.add(atom.getArguments()[0]);
		}
		for (GroundAtom atom : tar) {
			s2.add(atom.getArguments()[0]);
		}
		for (GroundTerm a : s1) {
			for (GroundTerm b : s2) {
				((RandomVariableAtom) db.getAtom(m.getPredicate("isSame"), a, b)).commitToDB();
				((RandomVariableAtom) db.getAtom(m.getPredicate("isSame"), b, a)).commitToDB();
			}
		}
	}

	/* Populates all the relatedTo atoms using the resources in datasets. */

	void populaterelatedTo(PSLModel m, Database db) {
		Set<GroundAtom> ds = Queries.getAllAtoms(db, m.getPredicate("fromFragment"));
		Set<GroundAtom> src = Queries.getAllAtoms(db, m.getPredicate("fromConsumer1"));
		Set<GroundAtom> tar = Queries.getAllAtoms(db, m.getPredicate("fromConsumer2"));

		for (GroundAtom atom : ds) {
			GroundTerm s =atom.getArguments()[0];
			GroundTerm p = atom.getArguments()[1];
			GroundTerm o =atom.getArguments()[2];
			((RandomVariableAtom) db.getAtom(m.getPredicate("relatedTo"),s,p,o )).commitToDB();
		}
		for (GroundAtom atom : src) {
			GroundTerm s =atom.getArguments()[0];
			GroundTerm p = atom.getArguments()[1];
			GroundTerm o =atom.getArguments()[2];
			((RandomVariableAtom) db.getAtom(m.getPredicate("relatedTo"),s,p,o )).commitToDB();
		}
		for (GroundAtom atom : tar) {
			GroundTerm s =atom.getArguments()[0];
			GroundTerm p = atom.getArguments()[1];
			GroundTerm o =atom.getArguments()[2];
			((RandomVariableAtom) db.getAtom(m.getPredicate("relatedTo"),s,p,o )).commitToDB();
		}
		for (GroundAtom atom : src) {
			for (GroundAtom dsatom : ds) {
				GroundTerm s = atom.getArguments()[0];
				GroundTerm p = atom.getArguments()[1];
				GroundTerm o = dsatom.getArguments()[2];
				((RandomVariableAtom) db.getAtom(m.getPredicate("relatedTo"),s,p,o )).commitToDB();
			} }
		for (GroundAtom atom : tar) {
			for (GroundAtom dsatom : ds) {
				GroundTerm s = atom.getArguments()[0];
				GroundTerm p = atom.getArguments()[1];
				GroundTerm o = dsatom.getArguments()[2];
				((RandomVariableAtom) db.getAtom(m.getPredicate("relatedTo"),s,p,o )).commitToDB();
			}
		}
	}
}
