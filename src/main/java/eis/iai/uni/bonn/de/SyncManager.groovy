package eis.iai.uni.bonn.de

import java.io.IOException;
import java.util.HashSet;
import java.util.Map;
import java.util.Scanner;

import org.semanticweb.owlapi.model.OWLOntologyCreationException;

import edu.umd.cs.psl.config.ConfigBundle
import edu.umd.cs.psl.config.ConfigManager
import edu.umd.cs.psl.database.DataStore
import edu.umd.cs.psl.database.rdbms.RDBMSDataStore
import edu.umd.cs.psl.database.rdbms.driver.H2DatabaseDriver
import edu.umd.cs.psl.groovy.PSLModel
import edu.umd.cs.psl.database.rdbms.driver.H2DatabaseDriver.Type;

String location = "ExperimentalData/" ;
//////////////////////////configuration ////////////////////////
ConfigManager cm = ConfigManager.getManager();
ConfigBundle config = cm.getBundle("deductive-reasoning");
config.addProperty("admmreasoner.maxiterations",30000);
config.addProperty("lazympeinference.maxrounds",14);

//////////////////////////storage settings ////////////////////////
String defaultPath = System.getProperty("java.io.tmpdir");
String dbpath = config.getString("dbpath", defaultPath + File.separator + "deductive-reasoning");
DataStore data = new RDBMSDataStore(new H2DatabaseDriver(Type.Disk, dbpath, true), config);
String dir = "data"+java.io.File.separator+"deductive-reasoning"+java.io.File.separator;
Scanner reader = new Scanner(System.in);

//////////////////////////model setup ////////////////////////
String [] datasets = [location+"train_slice", location+"train_srcChanges", location+"train_tarChanges", location+"dbpedia_2014.owl", "NT",
	location+"slice", location+"srcChanges", location+"tarChanges"];
InferenceUtils r = new InferenceUtils(location,dir);
LoadData l = new LoadData(dir, datasets, reader); 
LoadOntology.populateFiles(datasets[3], dir, reader);
reader.close();

Map<String, Double> weightMap = r.readweights("weights.txt");
PSLModel m = new LoadRules().createModel(r, data, weightMap, dir, l.model, l.smodel, l.tmodel);
////////////////////////////learning and inference ///////////////////////
RunInference d = new RunInference(m, datasets);
d.learn(r, m, data, dir, config, datasets);
d.test(r, m, data, dir, config, datasets);
//r.writeweights (m, "weights.txt", weightMap);	// don't overwrite weights again and again

// compute precision, recall, f-measure
Results result = new Results(location+"conflict_combination_PSL", location+"conflict_combination");
System.out.println("CG count: " + result.CG_file_size);
System.out.println("PSL count: " + result.PSL_file_size);
System.out.println("Intersection of PSL and CG count: " + result.intersect_count);
System.out.println("Results: ");
System.out.println("------------------------------------");
System.out.println("precision = " + result.precision);
System.out.println("recall = " + result.recall);
System.out.println("f-measure = " + result.f_measure);