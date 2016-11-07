package eis.iai.uni.bonn.de

import java.io.BufferedReader;

import java.io.FileReader;
import java.util.ArrayList;
import java.util.List;

import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.Property;
import org.apache.jena.rdf.model.RDFNode;
import org.apache.jena.rdf.model.Resource;
import org.apache.jena.rdf.model.ResourceFactory;
import org.apache.jena.rdf.model.Statement;

import edu.umd.cs.psl.core.inference.*;
import edu.umd.cs.psl.database.ReadOnlyDatabase;
import edu.umd.cs.psl.database.rdbms.RDBMSDataStore;
import edu.umd.cs.psl.database.rdbms.driver.H2DatabaseDriver;
import edu.umd.cs.psl.database.rdbms.driver.H2DatabaseDriver.Type;
import edu.emory.mathcs.utils.ConcurrencyUtils;
import edu.umd.cs.psl.model.argument.ArgumentType;
import edu.umd.cs.psl.model.argument.GroundTerm;
import edu.umd.cs.psl.model.function.ExternalFunction;
import groovy.time.TimeDuration;
import org.apache.jena.util.FileManager;
import groovy.time.TimeCategory;

public class LoadData {
	String filename, filesyntax ;
	public Model model ;
	public Model smodel ;
	public Model tmodel ;
	private Object dir;
	
	public LoadData(String d, String [] datasets){
		filename = datasets[0];
		filesyntax = datasets[4];
		dir = d;
		model = FileManager.get().loadModel(filename, filesyntax);
		smodel = FileManager.get().loadModel(datasets[1], filesyntax);	
		tmodel = FileManager.get().loadModel(datasets[2], filesyntax);
		
		ReasoningUtils r =	new ReasoningUtils();
		Date datasetsloading_time = new Date();
		def testDir = dir+'test'+java.io.File.separator;
		r.RDF2txt(datasets[0], testDir+"fromdataset", filesyntax);
		r.RDF2txt(datasets[1], testDir+"fromsrcdataset", filesyntax);
		r.RDF2txt(datasets[2], testDir+"fromtardataset", filesyntax);

		def trainDir = dir+'train'+java.io.File.separator;
		r.RDF2txt(datasets[0], trainDir+"fromdataset", filesyntax);
		r.RDF2txt(datasets[1], trainDir+"fromsrcdataset", filesyntax);
		r.RDF2txt(datasets[2], trainDir+"fromtardataset", filesyntax);
		
		Date datasetsloadingfinished_time = new Date();
		TimeDuration td = TimeCategory.minus(datasetsloadingfinished_time, datasetsloading_time);
		System.out.println "Total datasets loading time "+td;
	}

	def loadpredicates(m) {
		System.out.println("loading predicates...");
		////////////////////////// predicate declaration ////////////////////////
		//inputs
		m.add predicate: "fromDataset" , types: [ArgumentType.String, ArgumentType.String, ArgumentType.String]
		m.add predicate: "fromSrcDataset"  , types: [ArgumentType.String, ArgumentType.String, ArgumentType.String]
		m.add predicate: "fromTarDataset"  , types: [ArgumentType.String, ArgumentType.String, ArgumentType.String]

		//from ontology
		m.add predicate: "subclassOf"    , types: [ArgumentType.String, ArgumentType.String, ArgumentType.UniqueID]		
		m.add predicate: "domainOf"    , types: [ArgumentType.String, ArgumentType.String, ArgumentType.UniqueID]
		m.add predicate: "subpropertyOf"    , types: [ArgumentType.String, ArgumentType.String, ArgumentType.UniqueID]
		m.add predicate: "rangeOf"     , types: [ArgumentType.String, ArgumentType.String, ArgumentType.UniqueID]
		m.add predicate: "invFunProperty"    , types: [ArgumentType.String, ArgumentType.UniqueID]
		m.add predicate: "eqvclass"    , types: [ArgumentType.String, ArgumentType.String, ArgumentType.UniqueID]
		m.add predicate: "onproperty"    , types: [ArgumentType.String, ArgumentType.String, ArgumentType.UniqueID]
		m.add predicate: "funProperty"    , types: [ArgumentType.String, ArgumentType.UniqueID]
		m.add predicate: "eqvproperty"    , types: [ArgumentType.String, ArgumentType.String, ArgumentType.UniqueID]
		m.add predicate: "hasValue"    , types: [ArgumentType.String, ArgumentType.String, ArgumentType.UniqueID]
		m.add predicate: "maxCardinality"    , types: [ArgumentType.String, ArgumentType.Integer, ArgumentType.UniqueID]
		
		//target predicate
		m.add predicate: "isSame"    , types: [ArgumentType.String, ArgumentType.String]
		m.add predicate: "type"     , types: [ArgumentType.String, ArgumentType.String]
		m.add predicate: "relatedTo"    , types: [ArgumentType.String, ArgumentType.String, ArgumentType.String]

		 //functions
		 m.add function: "hasType"     , implementation: new isType();
		 m.add function: "nhasType"     , implementation: new isnotType();
		 
		m.add function: "ndisjointfrom"     , implementation: new isnotDisjoint();
		m.add function: "disjointfrom"     , implementation: new isDisjoint();
		m.add function: "nsame"     , implementation: new isnotSame();
		m.add function: "sameas"     , implementation: new is_same();
		m.add function: "diffrom"     , implementation: new isDiff();//currently, straight but also possible sameas(M,N) & difffrom(N, O)
		 	}


	//////////////////////////////External functions//////////////////////////

	class isDiff implements ExternalFunction {

		@Override
		public int getArity() {
			return 2;
		}

		@Override
		public ArgumentType[] getArgumentTypes() {
			return [ArgumentType.String, ArgumentType.String].toArray();
		}

		@Override
		public double getValue(ReadOnlyDatabase db, GroundTerm... args) {
			double value = 0.0;
			Resource x = model.getResource(args[0].getValue());
			Resource y = model.getResource(args[1].getValue());
			
			Property p = ResourceFactory.createProperty("http://www.w3.org/2002/07/owl#differentFrom");
			Resource r1 = x.getPropertyResourceValue(p);

			if (r1.equals(y))
				value = 1.0;
			else {
					r1 = y.getPropertyResourceValue(p);
					if (r1.equals(x))
						value = 1.0;
				}
			return value;
		}
	}

	class is_same implements ExternalFunction {
		@Override
		public int getArity() {
			return 2;
		}

		@Override
		public ArgumentType[] getArgumentTypes() {
			return [ArgumentType.String, ArgumentType.String].toArray();
		}

		@Override
		public double getValue(ReadOnlyDatabase db, GroundTerm... args) {
			double value = 0.0;
			Resource x = model.getResource(args[0].getValue());
			Resource y = model.getResource(args[1].getValue());
			Property p = ResourceFactory.createProperty("http://www.w3.org/2002/07/owl#sameAs");
			Resource r1 = x.getPropertyResourceValue(p);

			if (r1.equals(y))
				value = 1.0;
			else {
				r1 = y.getPropertyResourceValue(p);
				if (r1.equals(x))
					value = 1.0;
			}
			//	System.out.print(""+value);
			return value;
		}
	}
	
	class isnotSame implements ExternalFunction {		
				@Override
				public int getArity() {
					return 2;
				}
		
				@Override
				public ArgumentType[] getArgumentTypes() {
					return [ArgumentType.String, ArgumentType.String].toArray();
				}
		
				@Override
				public double getValue(ReadOnlyDatabase db, GroundTerm... args) {
					double value = 1.0;
					Resource x = model.getResource(args[0].getValue());
					Resource y = model.getResource(args[1].getValue());
					Property p = ResourceFactory.createProperty("http://www.w3.org/2002/07/owl#sameAs");
					Resource r1 = x.getPropertyResourceValue(p);
		
					if (r1.equals(y))
						value = 0.0;
					else {
						r1 = y.getPropertyResourceValue(p);
						if (r1.equals(x))
							value = 0.0;
					}	
					//	System.out.print(""+value);
					return value;
				}
			}

	class isnotDisjoint implements ExternalFunction {

		@Override
		public int getArity() {
			return 2;
		}

		@Override
		public ArgumentType[] getArgumentTypes() {
			return [ArgumentType.String, ArgumentType.String].toArray();
		}

		@Override
		public double getValue(ReadOnlyDatabase db, GroundTerm... args) {
			double disjoint = 1.0;
			BufferedReader	br = new BufferedReader(new FileReader(dir+'train'+java.io.File.separator+"disjointfrom.txt"));
			String line = null;
			String str1 =args[0].getValue();
			String str2 = args[1].getValue();

			String input1 =  str1+ "\t" + str2;
			String input2 = str2 + "\t" + str1;
			while ((line = br.readLine()) != null) {
				if (line.equals(input1) || line.equals(input2)) {
					disjoint = 0.0;
					break;
				}
			}
			br.close();
			return disjoint;
		}
	}
	class isDisjoint implements ExternalFunction {

		@Override
		public int getArity() {
			return 2;
		}

		@Override
		public ArgumentType[] getArgumentTypes() {
			return [ArgumentType.String, ArgumentType.String].toArray();
		}

		@Override
		public double getValue(ReadOnlyDatabase db, GroundTerm... args) {
			double disjoint = 0.0;
			BufferedReader	br = new BufferedReader(new FileReader(dir+'train'+java.io.File.separator+"disjointfrom.txt"));
			String line = null;
			String str1 = args[0].getValue();
			String str2 = args[1].getValue();
			String input1 =  str1+ "\t" + str2;
			String input2 = str2 + "\t" + str1;
			while ((line = br.readLine()) != null) {
				if (line.equals(input1) || line.equals(input2)) {
					disjoint = 1.0;
					break;
				}
			}
			br.close();
			return disjoint;
		}
	}

	class isType implements ExternalFunction {
		@Override
		public int getArity() {
			return 2;
		}

		@Override
		public ArgumentType[] getArgumentTypes() {
			return [ArgumentType.String, ArgumentType.String].toArray();
		}

		@Override
		public double getValue(ReadOnlyDatabase db, GroundTerm... args) {
			double value = 0.0;
			Resource x = smodel.getResource(args[0].getValue());
			if (x==null)
				x = tmodel.getResource(args[0].getValue());
			Property type_property = ResourceFactory.createProperty("http://www.w3.org/1999/02/22-rdf-syntax-ns#type");
			RDFNode type = (RDFNode) ResourceFactory.createResource(args[1].getValue());

			if (smodel.contains(x, type_property, type) || tmodel.contains(x, type_property, type)) {
				value = 1.0;
			}
			return value;
		}
	}
	class isnotType implements ExternalFunction {
		@Override
		public int getArity() {
			return 2;
		}

		@Override
		public ArgumentType[] getArgumentTypes() {
			return [ArgumentType.String, ArgumentType.String].toArray();
		}

		@Override
		public double getValue(ReadOnlyDatabase db, GroundTerm... args) {
			double value = 1.0;
			Resource x = smodel.getResource(args[0].getValue());			
			if (x==null)
				x = tmodel.getResource(args[0].getValue());
			Property type_property = ResourceFactory.createProperty("http://www.w3.org/1999/02/22-rdf-syntax-ns#type");
			RDFNode type = (RDFNode) ResourceFactory.createResource(args[1].getValue());

			if (smodel.contains(x, type_property, type) || tmodel.contains(x, type_property, type)){
			value = 0.0;
			}
			return value;
		}
	}
}