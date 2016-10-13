package eis.iai.uni.bonn.de;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import org.apache.jena.util.FileManager;
import org.apache.jena.rdf.model.Model
import org.apache.jena.rdf.model.Property;
import org.apache.jena.rdf.model.ResIterator;
import org.apache.jena.rdf.model.Resource;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import edu.umd.cs.psl.groovy.*;
import edu.umd.cs.psl.ui.loading.InserterUtils;
import edu.umd.cs.psl.util.database.Queries;
import edu.umd.cs.psl.model.argument.ArgumentType;
import edu.umd.cs.psl.model.argument.GroundTerm;
//import edu.umd.cs.psl.model.kernel.CompatibilityKernel
//import edu.umd.cs.psl.model.kernel.GroundKernel
import edu.umd.cs.psl.model.kernel.Kernel
import edu.umd.cs.psl.model.predicate.Predicate;
import edu.umd.cs.psl.model.predicate.StandardPredicate;
import edu.umd.cs.psl.model.argument.type.*;
import edu.umd.cs.psl.model.atom.GroundAtom;
import edu.umd.cs.psl.model.atom.RandomVariableAtom;
import edu.umd.cs.psl.model.formula.Rule
import edu.umd.cs.psl.model.function.ExternalFunction;
import edu.umd.cs.psl.model.predicate.type.*;
import edu.umd.cs.psl.application.inference.MPEInference;
import edu.umd.cs.psl.application.learning.weight.maxlikelihood.MaxLikelihoodMPE;
import edu.umd.cs.psl.config.*;
import edu.umd.cs.psl.database.DataStore;
import edu.umd.cs.psl.database.Database;
import edu.umd.cs.psl.database.Partition;
import edu.umd.cs.psl.database.ReadOnlyDatabase;
import edu.umd.cs.psl.database.rdbms.RDBMSDataStore;
import edu.umd.cs.psl.database.rdbms.driver.H2DatabaseDriver;
import edu.umd.cs.psl.database.rdbms.driver.H2DatabaseDriver.Type;
import groovy.time.*;

Logger log = LoggerFactory.getLogger(this.class);

//////////////////////////  configuration ////////////////////////
ConfigManager cm = ConfigManager.getManager()
ConfigBundle config = cm.getBundle("deductive-reasoning")
config.addProperty("admmreasoner.maxiterations",30000);
config.addProperty("lazympeinference.maxrounds",14);

//////////////////////////  storage settings ////////////////////////
def defaultPath = System.getProperty("java.io.tmpdir")
String dbpath = config.getString("dbpath", defaultPath + File.separator + "deductive-reasoning")
DataStore data = new RDBMSDataStore(new H2DatabaseDriver(Type.Disk, dbpath, true), config);
def dir = 'data'+java.io.File.separator+'deductive-reasoning'+java.io.File.separator;

//////////////////////////  model setup ////////////////////////

def PSLModel m = new PSLModel(this, data);
String [] datasets = ["slice", "srcChanges", "tarChanges", "dbpedia_2014.owl", "NT"];
LoadData l = new LoadData(datasets[0], datasets[4], dir, datasets); // to find e.g. sameAs and difffrom info
LoadOntology lont = new LoadOntology(datasets[0], datasets[4]);
lont.populateFiles(datasets[3], dir);

//////////////////////////  predicates declaration ////////////////////////
ReasoningUtils r = new ReasoningUtils();
def weightMap = r.readweights("weights.txt");
l.loadpredicates(m);
create_rules(m, weightMap);

//////////////////////////// learning and inference ///////////////////////
runInference(m, data, dir, config, datasets);
//r.writeweights (m,  "weights.txt");

//////////////////////////// Run inference ///////////////////////////
def runInference(m, data, dir, config, datasets) {	
	Date trainingInference_time = new Date();
	/* We close all the predicates since we want to treat those atoms as observed, and leave the predicate
	* type open to infer its atoms' values.*/
	HashSet closedPredsAll = new HashSet<Predicate>([fromDataset, fromSrcDataset, fromTarDataset, domainOf, rangeOf, subclassOf, eqvclass, 
		subpropertyOf, eqvproperty, invFunProperty, onproperty, hasValue, maxCardinality]);
	HashSet openPredsAll = new HashSet<Predicate>([type, relatedTo, isSame]);
	ReasoningUtils r =	new ReasoningUtils();

	/* Loads data */
	def trainDir = dir+'train'+java.io.File.separator;
	Partition trainObservations = new Partition(0);		//read partition
	r.loadPredicateAtoms(data, closedPredsAll, trainDir, trainObservations);

	/* We first create a second partition and open it as the write partition of a Database from the DataStore. 
	 * We also include the evidence partition as a read partition.*/

	Partition trainPredictions = new Partition(1);	//write partition
	Database trainDB = data.getDatabase(trainPredictions, closedPredsAll, trainObservations);
	populateType(trainDB, datasets);
	populaterelatedTo(trainDB);
	populateisSame(trainDB);

	Partition truth = new Partition(2);		//truth partition
	r.loadPredicateAtomsWithValue(data, openPredsAll, trainDir, truth);
	Database truthDB = data.getDatabase(truth, openPredsAll as Set);

	//////////////////////////// weight learning ///////////////////////////
	println "LEARNING WEIGHTS...";

	MaxLikelihoodMPE weightLearning = new MaxLikelihoodMPE(m, trainDB, truthDB, config);
	weightLearning.learn();
	weightLearning.close();

	trainDB.close();
	truthDB.close();

	Date trainingInferencefinished_time = new Date();
	
	println "LEARNING WEIGHTS DONE";	
	println m	
	println "/////////////////////////////////////////";
	
	/////////////////////////// test inference //////////////////////////////////
	Date testingInference_time = new Date();
	def testDir = dir+'test'+java.io.File.separator;
	Partition testObservations = new Partition(3);	//read partition
	Partition testPredictions = new Partition(4);	//write partition

	r.loadPredicateAtoms(data, closedPredsAll, testDir, testObservations);

	Database testDB = data.getDatabase(testPredictions, closedPredsAll, testObservations);
	populateType(testDB, datasets);
	populaterelatedTo(testDB);
	populateisSame(testDB);

	println "INFERRING...";
	MPEInference inference = new MPEInference(m, testDB, config);
	inference.mpeInference();
	inference.close();
	Date testingInferencefinished_time = new Date();
	
	println "INFERENCE DONE";
	r.print_results(testDB,openPredsAll);
	testDB.close();
	
	TimeDuration td = TimeCategory.minus(trainingInferencefinished_time, trainingInference_time);
	System.out.println "Total training time "+td;
	
	td = TimeCategory.minus(testingInferencefinished_time, testingInference_time);
	System.out.println "Total testing time "+td;
}

///////////////////////////////predicate declaration////////////////////////////////
def create_rules (m, weightMap) {	
	
	String rdftype = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type", 
	same = "http://www.w3.org/2002/07/owl#sameAs"; 
	
	m.add rule : ( fromDataset(S, rdftype, B) & fromSrcDataset(S, rdftype, D) & ndisjointfrom(D,B)) >> type(S,D), weight : weightMap["sim1"];
	m.add rule : ( fromDataset(S, rdftype, B) & fromTarDataset(S, rdftype, D) & ndisjointfrom(D,B)) >> type(S,D), weight : weightMap["sim2"];
	
	// domain 
	//1.1		
	m.add rule : ( domainOf(A, B, UID1) & fromDataset(S, A, O) & fromSrcDataset(S, rdftype, D) & disjointfrom(D,B)) >> type(S,B), weight : weightMap["dom1"];	
	m.add rule : ( domainOf(A, B, UID1) & fromDataset(S, A, O) & fromTarDataset(S, rdftype, D) & disjointfrom(D,B)) >> type(S,B), weight : weightMap["dom2"];	
	m.add rule : ( domainOf(A, B, UID1) & fromSrcDataset(S, A, O) & fromTarDataset(S, rdftype, D) & disjointfrom(D,B)) >> type(S,B), weight : weightMap["dom3"];
	m.add rule : ( domainOf(A, B, UID1) & fromTarDataset(S, A, O) & fromSrcDataset(S, rdftype, D) & disjointfrom(D,B)) >> type(S,B), weight : weightMap["dom4"];
	//1.2
	m.add rule : ( domainOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromDataset(S, C, O) & fromSrcDataset(S, rdftype, D) & disjointfrom(D,B)) >> type(S,B), weight : weightMap["dom5"];	
	m.add rule : ( domainOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromDataset(S, C, O) & fromTarDataset(S, rdftype, D) & disjointfrom(D,B)) >> type(S,B), weight : weightMap["dom6"];	
	m.add rule : ( domainOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromSrcDataset(S, C, O) & fromTarDataset(S, rdftype, D) & disjointfrom(D,B)) >> type(S,B), weight : weightMap["dom7"];
	m.add rule : ( domainOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromTarDataset(S, C, O) & fromSrcDataset(S, rdftype, D) & disjointfrom(D,B)) >> type(S,B), weight : weightMap["dom8"];

	// range 
	//2.1
	m.add rule : ( rangeOf(A, B, UID1) & fromDataset(S, A, O) & fromSrcDataset(O, rdftype, D) & disjointfrom(D,B)) >> type(O,B), weight : weightMap["ran1"];
	m.add rule : ( rangeOf(A, B, UID1) & fromDataset(S, A, O) & fromTarDataset(O, rdftype, D) & disjointfrom(D,B)) >> type(O,B), weight : weightMap["ran2"];
	m.add rule : ( rangeOf(A, B, UID1) & fromSrcDataset(S, A, O) & fromTarDataset(O, rdftype, D) & disjointfrom(D,B)) >> type(O,B), weight : weightMap["ran3"];
	m.add rule : ( rangeOf(A, B, UID1) & fromTarDataset(S, A, O) & fromSrcDataset(O, rdftype, D) & disjointfrom(D,B)) >> type(O,B), weight : weightMap["ran4"];
	//2.2
	m.add rule : ( rangeOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromDataset(S, C, O) & fromSrcDataset(O, rdftype, D) & disjointfrom(D,B)) >> type(O,B), weight : weightMap["ran5"];
	m.add rule : ( rangeOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromDataset(S, C, O) & fromTarDataset(O, rdftype, D) & disjointfrom(D,B)) >> type(O,B), weight : weightMap["ran6"];
	m.add rule : ( rangeOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromSrcDataset(S, C, O) & fromTarDataset(O, rdftype, D) & disjointfrom(D,B)) >> type(O,B), weight : weightMap["ran7"];
	m.add rule : ( rangeOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromTarDataset(S, C, O) & fromSrcDataset(O, rdftype, D) & disjointfrom(D,B)) >> type(O,B), weight : weightMap["ran8"];
	
	//2.3 - inferening instead of resolving conflicts 	
/*	m.add rule : ( rangeOf(A, B, T0, T1, UID1) & fromSrcDataset(S, A, O, T2, T0, T3) & fromTarDataset(S, A, N, T2, T0, T4) & resource(O)) >> type(O,B), weight : weightMap["ran9"];
	m.add rule : ( rangeOf(A, B, T0, T1, UID1) & fromSrcDataset(S, A, O, T2, T0, T3) & fromTarDataset(S, A, N, T2, T0, T4) & resource(N)) >> type(N,B), weight : weightMap["ran10"];
	m.add rule : ( rangeOf(A, B, T0, T1, UID1) & subpropertyOf(C, A, T2, T0, UID2) & fromSrcDataset(S, C, O, T3, T2, T4) & fromTarDataset(S, C, N, T3, T2, T5) & resource(O)) >> type(O,B), weightMap["ran12"];
	m.add rule : ( rangeOf(A, B, T0, T1, UID1) & subpropertyOf(C, A, T2, T0, UID2) & fromSrcDataset(S, C, O, T3, T2, T4) & fromTarDataset(S, C, N, T3, T2, T5) & resource(N)) >> type(N,B), weightMap["ran13"];
*/
	
		//m.add rule : ( rangeOf(A, B, T0, T1, UID1) & fromSrcDataset(S, A, O, T2, T0, T3) & fromTarDataset(S, A, N, T2, T0, T4) & disjointfrom(D,B)) >> isSame(O,N), weight : weightMap["ran11"];
//	m.add rule : ( rangeOf(A, B, T0, T1, UID1) & subpropertyOf(C, A, T2, T0, UID2) & fromSrcDataset(S, C, O, T3, T2, T4) & fromTarDataset(S, C, N, T3, T2, T5) & disjointfrom(D,B)) >> isSame(O,N), weightMap["ran14"];
	//2.4
	//?	m.add rule : ( rangeOf(A, B, T0, T1, UID1) & fromSrcDataset(X, A, Y, T2, T3, T4) & fromTarDataset(X, A, Z, T5, T6, T7) & hasType(Y,B) && !hasType(Z,B)) >> relatedTo(X,A,Y), weight : 10;
	//?	m.add rule : ( rangeOf(A, B, T0, T1, UID1) & fromSrcDataset(X, A, Y, T2, T3, T4) & fromTarDataset(X, A, Z, T5, T6, T7) & hasType(Z,B) && !hasType(Y,B)) >> relatedTo(X,A,Z), weight : 10;

	// inverse functional property 
	//3.1
	m.add rule : (invFunProperty(A, UID) & fromDataset(R, A, O) & fromSrcDataset(S, A, O)) >> isSame(R,S), weight : weightMap["ifp1"];	
	m.add rule : (invFunProperty(A, UID) & fromDataset(R, A, O) & fromTarDataset(S, A, O)) >> isSame(R,S), weight : weightMap["ifp2"];
	m.add rule : (invFunProperty(A, UID) & fromSrcDataset(R, A, O) & fromTarDataset(S, A, O)) >> isSame(S,R), weight: weightMap["ifp3"];
//	m.add rule : (invFunProperty(A, UID) & fromDataset(R, A, O) & fromSrcDataset(S, A, N) & fromTarDataset(S, A, O)) >> relatedTo(S,A,O), weight : weightMap["ifp1"];
//	m.add rule : (invFunProperty(A, UID) & fromDataset(R, A, O) & fromSrcDataset(S, A, N) & fromTarDataset(S, A, O)) >> isSame(S,R), weight: weightMap["ifp2"];

/*
	// restrictions	
	//4.1
	m.add rule : (onproperty(X,A) & maxCardinality(X,"1") & fromDataset(S, rdftype, X) & fromSrcDataset(S, A, O) & 
		fromTarDataset(S, A, N)) >> isSame(O,N), weight : 8;
	m.add rule : (onproperty(X,A) & maxCardinality(X,"1") & fromSrcDataset(S, rdftype, X) & fromSrcDataset(S, A, O) & 
		fromTarDataset(S, A, N)) >> isSame(O,N), weight : 8;
	m.add rule : (onproperty(X,A) & maxCardinality(X,"1") & fromTarDataset(S, rdftype, X) & fromSrcDataset(S, A, O) & 
		fromTarDataset(S, A, N)) >> isSame(O,N), weight : 8;
	//4.2
	m.add rule : (onproperty(X,A) & maxCardinality(X,"1") & hasValue(X,O) & fromDataset(S, rdftype, X) & fromSrcDataset(S, A, O) & 
		fromTarDataset(S, A, N)) >> relatedTo(S, A, O), weight : 8;
	m.add rule : (onproperty(X,A) & maxCardinality(X,"1") & hasValue(X,O) & fromDataset(S, rdftype, X) & fromTarDataset(S, A, O) & 
		fromSrcDataset(S, A, N)) >> relatedTo(S, A, O), weight : 8;
	m.add rule : (onproperty(X,A) & maxCardinality(X,"1") & hasValue(X,O) & fromDataset(S, rdftype, X) & fromTarDataset(S, A, O) & 
		fromSrcDataset(S, A, N)) >> isSame(O,N), weight : 5;	
	m.add rule : (onproperty(X,A) & maxCardinality(X,"1") & hasValue(X,O) & fromDataset(S, rdftype, X) & fromDataset(M, same, O) & 
		fromSrcDataset(S, A, M) & fromTarDataset(S, A, N)) >> relatedTo(S, A, M), weight : 8;
	m.add rule : (onproperty(X,A) & maxCardinality(X,"1") & hasValue(X,O) & fromDataset(S, rdftype, X) & fromDataset(M, same, O) & 
		fromTarDataset(S, A, M) & fromSrcDataset(S, A, N)) >> relatedTo(S, A, M), weight : 8;

	m.add rule : (onproperty(X,A) & maxCardinality(X,"1") & hasValue(X,O) & fromSrcDataset(S, rdftype, X) & fromSrcDataset(S, A, O) & 
		fromTarDataset(S, A, N)) >> relatedTo(S, A, O), weight : 8;
	m.add rule : (onproperty(X,A) & maxCardinality(X,"1") & hasValue(X,O) & fromSrcDataset(S, rdftype, X) & fromTarDataset(S, A, O) & 
		fromSrcDataset(S, A, N)) >> relatedTo(S, A, O), weight : 8;
	m.add rule : (onproperty(X,A) & maxCardinality(X,"1") & hasValue(X,O) & fromSrcDataset(S, rdftype, X) & fromTarDataset(S, A, O) & 
		fromSrcDataset(S, A, N)) >> isSame(O,N), weight : 5;
	m.add rule : (onproperty(X,A) & maxCardinality(X,"1") & hasValue(X,O) & fromSrcDataset(S, rdftype, X) & fromDataset(M, same, O) & 
		fromSrcDataset(S, A, M) & fromTarDataset(S, A, N)) >> relatedTo(S, A, M), weight : 8;
	m.add rule : (onproperty(X,A) & maxCardinality(X,"1") & hasValue(X,O) & fromSrcDataset(S, rdftype, X) & fromDataset(M, same, O) & 
		fromTarDataset(S, A, M) & fromSrcDataset(S, A, N)) >> relatedTo(S, A, M), weight : 8;

	m.add rule : (onproperty(X,A) & maxCardinality(X,"1") & hasValue(X,O) & fromTarDataset(S, rdftype, X) & fromSrcDataset(S, A, O) & 
		fromTarDataset(S, A, N)) >> relatedTo(S, A, O), weight : 8;
	m.add rule : (onproperty(X,A) & maxCardinality(X,"1") & hasValue(X,O) & fromTarDataset(S, rdftype, X) & fromTarDataset(S, A, O) & 
		fromSrcDataset(S, A, N)) >> relatedTo(S, A, O), weight : 8;
	m.add rule : (onproperty(X,A) & maxCardinality(X,"1") & hasValue(X,O) & fromTarDataset(S, rdftype, X) & fromTarDataset(S, A, O) & 
		fromSrcDataset(S, A, N)) >> isSame(O,N), weight : 5;
	m.add rule : (onproperty(X,A) & maxCardinality(X,"1") & hasValue(X,O) & fromTarDataset(S, rdftype, X) & fromDataset(M, same, O) & 
		fromSrcDataset(S, A, M) & fromTarDataset(S, A, N)) >> relatedTo(S, A, M), weight : 8;
	m.add rule : (onproperty(X,A) & maxCardinality(X,"1") & hasValue(X,O) & fromTarDataset(S, rdftype, X) & fromDataset(M, same, O) & 
		fromTarDataset(S, A, M) & fromSrcDataset(S, A, N)) >> relatedTo(S, A, M), weight : 8;

	//4.3
	m.add rule : (subclassOf(X,Y) & onproperty(Y,A) & hasValue(Y,O) & onproperty(X,A) & maxCardinality(X,"1") & 
		fromDataset(S, rdftype, X) & fromSrcDataset(S, A, O) & fromTarDataset(S, A, N)) >> relatedTo(S, A, O), weight : 8;
	m.add rule : (subclassOf(X,Y) & onproperty(Y,A) & hasValue(Y,O) & onproperty(X,A) & maxCardinality(X,"1") &
		 fromDataset(S, rdftype, X) & fromTarDataset(S, A, O) & fromSrcDataset(S, A, N)) >> relatedTo(S, A, O), weight : 8;
	m.add rule : (subclassOf(X,Y) & onproperty(Y,A) & hasValue(Y,O) & onproperty(X,A) & maxCardinality(X,"1") & 
		fromDataset(S, rdftype, X) & fromTarDataset(S, A, O) & fromSrcDataset(S, A, N)) >> isSame(O,N), weight : 5;
	m.add rule : (subclassOf(X,Y) & onproperty(Y,A) & hasValue(Y,O) & onproperty(X,A) & maxCardinality(X,"1") & fromDataset(S, rdftype, X) &  
		fromDataset(M, same, O) & fromSrcDataset(S, A, M) & fromTarDataset(S, A, N)) >> relatedTo(S, A, M), weight : 8;
	m.add rule : (subclassOf(X,Y) & onproperty(Y,A) & hasValue(Y,O) & onproperty(X,A) & maxCardinality(X,"1") & fromDataset(S, rdftype, X) & 
		fromDataset(M, same, O) & fromTarDataset(S, A, M) & fromSrcDataset(S, A, N)) >> relatedTo(S, A, M), weight : 8;

	m.add rule : (subclassOf(X,Y) & onproperty(Y,A) & hasValue(Y,O) & onproperty(X,A) & maxCardinality(X,"1") & 
		fromSrcDataset(S, rdftype, X) & fromSrcDataset(S, A, O) & fromTarDataset(S, A, N)) >> relatedTo(S, A, O), weight : 8;
	m.add rule : (subclassOf(X,Y) & onproperty(Y,A) & hasValue(Y,O) & onproperty(X,A) & maxCardinality(X,"1") & 
		fromSrcDataset(S, rdftype, X) & fromTarDataset(S, A, O) & fromSrcDataset(S, A, N)) >> relatedTo(S, A, O), weight : 8;
	m.add rule : (subclassOf(X,Y) & onproperty(Y,A) & hasValue(Y,O) & onproperty(X,A) & maxCardinality(X,"1") & 
		fromSrcDataset(S, rdftype, X) & fromTarDataset(S, A, O) & fromSrcDataset(S, A, N)) >> isSame(O,N), weight : 5;
	m.add rule : (subclassOf(X,Y) & onproperty(Y,A) & hasValue(Y,O) & onproperty(X,A) & maxCardinality(X,"1") & 
		fromSrcDataset(S, rdftype, X) & fromDataset(M, same, O) & fromSrcDataset(S, A, M) & 
		fromTarDataset(S, A, N)) >> relatedTo(S, A, M), weight : 8;
	m.add rule : (subclassOf(X,Y) & onproperty(Y,A) & hasValue(Y,O) & onproperty(X,A) & maxCardinality(X,"1") & fromSrcDataset(S, rdftype, X) & 
		fromDataset(M, same, O) & fromTarDataset(S, A, M) & fromSrcDataset(S, A, N)) >> relatedTo(S, A, M), weight : 8;

	m.add rule : (subclassOf(X,Y) & onproperty(Y,A) & hasValue(Y,O) & onproperty(X,A) & maxCardinality(X,"1") & 
		fromTarDataset(S, rdftype, X) & fromSrcDataset(S, A, O) & fromTarDataset(S, A, N)) >> relatedTo(S, A, O), weight : 8;
	m.add rule : (subclassOf(X,Y) & onproperty(Y,A) & hasValue(Y,O) & onproperty(X,A) & maxCardinality(X,"1") & 
		fromTarDataset(S, rdftype, X) & fromTarDataset(S, A, O) & fromSrcDataset(S, A, N)) >> relatedTo(S, A, O), weight : 8;
	m.add rule : (subclassOf(X,Y) & onproperty(Y,A) & hasValue(Y,O) & onproperty(X,A) & maxCardinality(X,"1") & 
		fromTarDataset(S, rdftype, X) & fromTarDataset(S, A, O) & fromSrcDataset(S, A, N)) >> isSame(O,N), weight : 5;
	m.add rule : (subclassOf(X,Y) & onproperty(Y,A) & hasValue(Y,O) & onproperty(X,A) & maxCardinality(X,"1") & fromTarDataset(S, rdftype, X) & 
		fromDataset(M, same, O) & fromSrcDataset(S, A, M) & fromTarDataset(S, A, N)) >> relatedTo(S, A, M), weight : 8;
	m.add rule : (subclassOf(X,Y) & onproperty(Y,A) & hasValue(Y,O) & onproperty(X,A) & maxCardinality(X,"1") & fromTarDataset(S, rdftype, X) & 
		fromDataset(M, same, O) & fromTarDataset(S, A, M) & fromSrcDataset(S, A, N)) >> relatedTo(S, A, M), weight : 8;

	//functional property
	//5.1
	m.add rule : (funProperty(A) & fromSrcDataset(S, A, N) & fromTarDataset(S, A, O)) >> isSame(N,O), weight : 5;

	//disjoint classes
	//6.1
	m.add rule : (ndisjointfrom(N,O) & fromSrcDataset(S, A, N) & fromTarDataset(S, A, O)) >> relatedTo(S, A, N), weight : 10;
	m.add rule : (ndisjointfrom(N,O) & fromSrcDataset(S, A, N) & fromTarDataset(S, A, O)) >> relatedTo(S, A, O), weight : 10;

	//6.2
	m.add rule : (ndisjointfrom(X,Z) & eqvclass(Y,Z) & fromSrcDataset(S, A, Y) & fromTarDataset(S, A, X)) >> relatedTo(S, A, Y), weight : 10;
	m.add rule : (ndisjointfrom(X,Z) & eqvclass(Y,Z) & fromSrcDataset(S, A, Y) & fromTarDataset(S, A, X)) >> relatedTo(S, A, X), weight : 10;
	m.add rule : (ndisjointfrom(X,Z) & eqvclass(Y,Z) & fromTarDataset(S, A, Y) & fromSrcDataset(S, A, X)) >> relatedTo(S, A, Y), weight : 10;
	m.add rule : (ndisjointfrom(X,Z) & eqvclass(Y,Z) & fromTarDataset(S, A, Y) & fromSrcDataset(S, A, X)) >> relatedTo(S, A, X), weight : 10;
*/
	//equivalent property
	//7.1
	m.add rule : (eqvproperty(A,B,UID) & fromDataset(S, A, N) & fromSrcDataset(S, B, N) & fromTarDataset(S, B, O)) >> relatedTo(S, B, N), weight : 10;
	m.add rule : (eqvproperty(A,B,UID) & fromDataset(S, A, N) & fromTarDataset(S, B, N) & fromSrcDataset(S, B, O)) >> relatedTo(S, B, N), weight : 10;
/*	m.add rule : (eqvproperty(A,B) & fromDataset(S, A, N) & fromSrcDataset(S, B, M) & fromTarDataset(S, B, O)) >> relatedTo(S, B, N), weight : 10;	
	m.add rule : (eqvproperty(A,B) & fromDataset(S, A, N) & fromTarDataset(S, B, M) & fromSrcDataset(S, B, O)) >> relatedTo(S, B, N), weight : 10;

	//7.2 	
	m.add rule : (subpropertyOf(A,B) & fromDataset(S, B, N) & fromSrcDataset(S, A, N) & fromTarDataset(S, A, O)) >> relatedTo(S, A, N), weight : 10;
	m.add rule : (subpropertyOf(A,B) & fromDataset(S, B, N) & fromTarDataset(S, A, N) & fromSrcDataset(S, A, O)) >> relatedTo(S, A, N), weight : 10;
	m.add rule : (subpropertyOf(A,B) & fromDataset(S, B, N) & fromSrcDataset(S, A, M) & fromTarDataset(S, A, O)) >> relatedTo(S, A, N), weight : 10;
	m.add rule : (subpropertyOf(A,B) & fromDataset(S, B, N) & fromTarDataset(S, A, M) & fromSrcDataset(S, A, O)) >> relatedTo(S, A, N), weight : 10;

	//7.3
	m.add rule : (eqvproperty(C,B) & subpropertyOf(A,B) & fromDataset(S, C, N) & fromSrcDataset(S, A, N) 
		& fromTarDataset(S, A, O)) >> relatedTo(S, A, N), weight : 10;
	m.add rule : (eqvproperty(C,B) & subpropertyOf(A,B) & fromDataset(S, C, N) & fromTarDataset(S, A, N) 
		& fromSrcDataset(S, A, O)) >> relatedTo(S, A, N), weight : 10;
	m.add rule : (eqvproperty(C,B) & subpropertyOf(A,B) & fromDataset(S, C, N) & fromSrcDataset(S, A, M) 
		& fromTarDataset(S, A, O)) >> relatedTo(S, A, N), weight : 10;
	m.add rule : (eqvproperty(C,B) & subpropertyOf(A,B) & fromDataset(S, C, N) & fromTarDataset(S, A, M) 
		& fromSrcDataset(S, A, O)) >> relatedTo(S, A, N), weight : 10;

	//same resources
	//8.1 (can be used in combination with other rules)
	m.add rule : (sameas(S1,S) & fromDataset(S1, A, N) & fromSrcDataset(S, A, N) & fromTarDataset(S, A, O)) >> relatedTo(S, A, N), weight : 10;
	m.add rule : (sameas(S1,S) & fromDataset(S1, A, N) & fromTarDataset(S, A, N) & fromSrcDataset(S, A, O)) >> relatedTo(S, A, N), weight : 10;
	m.add rule : (sameas(S1,S) & fromDataset(S1, A, N) & fromSrcDataset(S, A, M) & fromTarDataset(S, A, O)) >> relatedTo(S, A, N), weight : 10;
	m.add rule : (sameas(S1,S) & fromDataset(S1, A, N) & fromTarDataset(S, A, M) & fromSrcDataset(S, A, O)) >> relatedTo(S, A, N), weight : 10;
	
	//8.2
	m.add rule : (difffrom(M, O) & fromSrcDataset(S, A, M) & fromTarDataset(S, A, O)) >> relatedTo(S, A, M), weight : 10;
	m.add rule : (difffrom(M, O) & fromSrcDataset(S, A, M) & fromTarDataset(S, A, O)) >> relatedTo(S, A, O), weight : 10;
	m.add rule : (difffrom(M, O) & fromTarDataset(S, A, M) & fromSrcDataset(S, A, O)) >> relatedTo(S, A, M), weight : 10;
	m.add rule : (difffrom(M, O) & fromTarDataset(S, A, M) & fromSrcDataset(S, A, O)) >> relatedTo(S, A, O), weight : 10;
*/
	// constraints
	m.add PredicateConstraint.PartialFunctional , on : type;
//	m.add PredicateConstraint.PartialFunctional , on : relatedTo; support only binary predicates
	m.add PredicateConstraint.PartialFunctional , on : isSame;	
	m.add PredicateConstraint.PartialInverseFunctional , on : isSame;
	m.add PredicateConstraint.Symmetric , on : isSame;

	// prior
	m.add rule : ~type(X,B), weight: weightMap["type"];
	m.add rule : ~isSame(Y,Z), weight: weightMap["isSame"];
	m.add rule : ~relatedTo(X,A,Z), weight: weightMap["related"];
}


//////////////////////////////populate/////////////////////////////////////////

/* Populates all the type atoms using the triple and domainOf predicates. */
	def populateType(Database db, String [] datasets) {
		
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
		//	res_set.add("'"+res.toString()+"'");
			res_set.add(res.toString());
		}
			while (sresiter.hasNext()) {
			Resource res = sresiter.next();
		//	res_set.add("'"+res.toString()+"'");
			res_set.add(res.toString());
		}
			while (tresiter.hasNext()) {
				Resource res = tresiter.next();
		//	res_set.add("'"+res.toString()+"'");
			res_set.add(res.toString());
			}
		
			
			Set<GroundAtom> ds = Queries.getAllAtoms(db, fromDataset);
			Set<GroundAtom> src = Queries.getAllAtoms(db, fromSrcDataset);
			Set<GroundAtom> tar = Queries.getAllAtoms(db, fromTarDataset);
	
		Set<GroundAtom> belongsto0 = Queries.getAllAtoms(db, domainOf);
		Set<GroundAtom> belongsto1 = Queries.getAllAtoms(db, rangeOf);
	
	
		for (GroundAtom atom : ds) {
			GroundTerm term = atom.getArguments()[0];
			String value = term.getValue();		
			if (res_set.contains(value))
				s1.add(term);
				
			term = atom.getArguments()[2];
			value = term.getValue();
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
				((RandomVariableAtom) db.getAtom(type, a, b)).commitToDB();
			}
		}
	}


/* Populates all the isSame atoms using the resources in datasets. */
void populateisSame(Database db) {
	Set<GroundAtom> ds = Queries.getAllAtoms(db, fromDataset);
	Set<GroundAtom> src = Queries.getAllAtoms(db, fromSrcDataset);
	Set<GroundAtom> tar = Queries.getAllAtoms(db, fromTarDataset);

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
			((RandomVariableAtom) db.getAtom(isSame, a, b)).commitToDB();
			((RandomVariableAtom) db.getAtom(isSame, b, a)).commitToDB();
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
			((RandomVariableAtom) db.getAtom(isSame, a, b)).commitToDB();
			((RandomVariableAtom) db.getAtom(isSame, b, a)).commitToDB();
		}
	}
}

/* Populates all the relatedTo atoms using the resources in datasets. */

def populaterelatedTo(db) {
	Set<GroundAtom> ds = Queries.getAllAtoms(db, fromDataset);
	Set<GroundAtom> src = Queries.getAllAtoms(db, fromSrcDataset);//closedPredsAll[1]
	Set<GroundAtom> tar = Queries.getAllAtoms(db, fromTarDataset);
	
	for (GroundAtom atom : ds) {
		GroundTerm s =atom.getArguments()[0];
		GroundTerm p = atom.getArguments()[1];
		GroundTerm o =atom.getArguments()[2];
		((RandomVariableAtom) db.getAtom(relatedTo,s,p,o )).commitToDB();
	}
	for (GroundAtom atom : src) {
		GroundTerm s =atom.getArguments()[0];
		GroundTerm p = atom.getArguments()[1];
		GroundTerm o =atom.getArguments()[2];
		((RandomVariableAtom) db.getAtom(relatedTo,s,p,o )).commitToDB();
	}
	for (GroundAtom atom : tar) {
		GroundTerm s =atom.getArguments()[0];
		GroundTerm p = atom.getArguments()[1];
		GroundTerm o =atom.getArguments()[2];
		((RandomVariableAtom) db.getAtom(relatedTo,s,p,o )).commitToDB();
	}
	for (GroundAtom atom : src) {
		for (GroundAtom dsatom : ds) {
		GroundTerm s = atom.getArguments()[0];
		GroundTerm p = atom.getArguments()[1];
		GroundTerm o = dsatom.getArguments()[2];
		((RandomVariableAtom) db.getAtom(relatedTo,s,p,o )).commitToDB();
	} }
	for (GroundAtom atom : tar) {
		for (GroundAtom dsatom : ds) {
		GroundTerm s = atom.getArguments()[0];
		GroundTerm p = atom.getArguments()[1];		
		GroundTerm o = dsatom.getArguments()[2];
		((RandomVariableAtom) db.getAtom(relatedTo,s,p,o )).commitToDB();
	} }
}	


