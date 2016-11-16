package eis.iai.uni.bonn.de

import java.util.HashSet;
import java.util.Map;

import edu.umd.cs.psl.config.ConfigBundle
import edu.umd.cs.psl.config.ConfigManager
import edu.umd.cs.psl.database.DataStore
import edu.umd.cs.psl.database.rdbms.RDBMSDataStore
import edu.umd.cs.psl.database.rdbms.driver.H2DatabaseDriver
import edu.umd.cs.psl.groovy.PSLModel
import edu.umd.cs.psl.database.rdbms.driver.H2DatabaseDriver.Type;

//////////////////////////configuration ////////////////////////
ConfigManager cm = ConfigManager.getManager();
ConfigBundle config = cm.getBundle("deductive-reasoning");
config.addProperty("admmreasoner.maxiterations",5000);
config.addProperty("lazympeinference.maxrounds",14);

//////////////////////////storage settings ////////////////////////
String defaultPath = System.getProperty("java.io.tmpdir");
String dbpath = config.getString("dbpath", defaultPath + File.separator + "deductive-reasoning");
DataStore data = new RDBMSDataStore(new H2DatabaseDriver(Type.Disk, dbpath, true), config);
String dir = "data"+java.io.File.separator+"deductive-reasoning"+java.io.File.separator;

//////////////////////////model setup ////////////////////////
String [] datasets = ["slice", "srcChanges", "tarChanges", "dbpedia_2014.owl", "NT"];
LoadData l = new LoadData(dir, datasets); // to find e.g. sameAs and difffrom info
LoadOntology lont = new LoadOntology(datasets[0], datasets[4]);
lont.populateFiles(datasets[3], dir);

InferenceUtils r = new InferenceUtils();
Map<String, Double> weightMap = r.readweights("weights.txt");
PSLModel m = new LoadRules().createModel(r, data, weightMap, dir, l.model, l.smodel, l.tmodel);
////////////////////////////learning and inference ///////////////////////
RunInference d = new RunInference(m);
d.learn(r, m, data, dir, config, datasets, l, lont);
d.test(r, m, data, dir, config, datasets, l, lont);
r.writeweights (m, "weights.txt", weightMap);
