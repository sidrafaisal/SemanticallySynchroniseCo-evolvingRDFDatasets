package eis.iai.uni.bonn.de

import java.io.BufferedReader;
import java.io.FileReader;
import java.util.Map;

import org.apache.jena.rdf.model.RDFNode;
import org.apache.jena.rdf.model.Resource;
import org.apache.jena.rdf.model.ResourceFactory;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.util.FileManager;
import org.apache.jena.ontology.OntClass;
import org.apache.jena.rdf.model.Property;
import org.apache.jena.rdf.model.ResIterator;

import edu.umd.cs.psl.database.ReadOnlyDatabase;
import edu.umd.cs.psl.groovy.PSLModel;
import edu.umd.cs.psl.model.argument.ArgumentType;
import edu.umd.cs.psl.model.argument.GroundTerm;
import edu.umd.cs.psl.model.function.ExternalFunction;
import edu.umd.cs.psl.groovy.*;
import edu.umd.cs.psl.util.database.Queries;
import edu.umd.cs.psl.model.atom.GroundAtom;
import edu.umd.cs.psl.model.atom.RandomVariableAtom;
import org.apache.jena.util.FileManager;


public class LoadRules {

	def createModel (r, data, weightMap) {
		PSLModel m = new PSLModel(this, data);
		loadPredicates(m);
		String rdftype = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type",
		same = "http://www.w3.org/2002/07/owl#sameAs";

		//disjiont classes
		m.add rule : ( fromFragment(S, rdftype, B) & fromConsumer1(S, rdftype, D) & ndisjointfrom(D,B)) >> type(S,D), weight : weightMap["sim1"];
		m.add rule : ( fromFragment(S, rdftype, B) & fromConsumer2(S, rdftype, D) & ndisjointfrom(D,B)) >> type(S,D), weight : weightMap["sim2"];

		// domain
		//1.1
		m.add rule : ( domainOf(A, B, UID1) & fromFragment(S, A, O) & fromConsumer1(S, rdftype, D) & disjointfrom(D,B)) >> type(S,B), weight : weightMap["dom1"];
		m.add rule : ( domainOf(A, B, UID1) & fromFragment(S, A, O) & fromConsumer2(S, rdftype, D) & disjointfrom(D,B)) >> type(S,B), weight : weightMap["dom2"];
		m.add rule : ( domainOf(A, B, UID1) & fromConsumer1(S, A, O) & fromConsumer2(S, rdftype, D) & disjointfrom(D,B)) >> type(S,B), weight : weightMap["dom3"];
		m.add rule : ( domainOf(A, B, UID1) & fromConsumer2(S, A, O) & fromConsumer1(S, rdftype, D) & disjointfrom(D,B)) >> type(S,B), weight : weightMap["dom4"];
		//1.2
		m.add rule : ( domainOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromFragment(S, C, O) & fromConsumer1(S, rdftype, D) & disjointfrom(D,B)) >> type(S,B), weight : weightMap["dom5"];
		m.add rule : ( domainOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromFragment(S, C, O) & fromConsumer2(S, rdftype, D) & disjointfrom(D,B)) >> type(S,B), weight : weightMap["dom6"];
		m.add rule : ( domainOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromConsumer1(S, C, O) & fromConsumer2(S, rdftype, D) & disjointfrom(D,B)) >> type(S,B), weight : weightMap["dom7"];
		m.add rule : ( domainOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromConsumer2(S, C, O) & fromConsumer1(S, rdftype, D) & disjointfrom(D,B)) >> type(S,B), weight : weightMap["dom8"];

		// range
		//2.1
		m.add rule : ( rangeOf(A, B, UID1) & fromFragment(S, A, O) & fromConsumer1(O, rdftype, D) & disjointfrom(D,B)) >> type(O,B), weight : weightMap["ran1"];
		m.add rule : ( rangeOf(A, B, UID1) & fromFragment(S, A, O) & fromConsumer2(O, rdftype, D) & disjointfrom(D,B)) >> type(O,B), weight : weightMap["ran2"];
		m.add rule : ( rangeOf(A, B, UID1) & fromConsumer1(S, A, O) & fromConsumer2(O, rdftype, D) & disjointfrom(D,B)) >> type(O,B), weight : weightMap["ran3"];
		m.add rule : ( rangeOf(A, B, UID1) & fromConsumer2(S, A, O) & fromConsumer1(O, rdftype, D) & disjointfrom(D,B)) >> type(O,B), weight : weightMap["ran4"];
		//2.2
		m.add rule : ( rangeOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromFragment(S, C, O) & fromConsumer1(O, rdftype, D) & disjointfrom(D,B)) >> type(O,B), weight : weightMap["ran5"];
		m.add rule : ( rangeOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromFragment(S, C, O) & fromConsumer2(O, rdftype, D) & disjointfrom(D,B)) >> type(O,B), weight : weightMap["ran6"];
		m.add rule : ( rangeOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromConsumer1(S, C, O) & fromConsumer2(O, rdftype, D) & disjointfrom(D,B)) >> type(O,B), weight : weightMap["ran7"];
		m.add rule : ( rangeOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromConsumer2(S, C, O) & fromConsumer1(O, rdftype, D) & disjointfrom(D,B)) >> type(O,B), weight : weightMap["ran8"];

		//2.3
		m.add rule : ( rangeOf(A, B, UID1) & fromConsumer1(X, A, Y) & fromConsumer2(X, A, Z) & hasType(Y,B) & nhasType(Z,B)) >> relatedTo(X,A,Y), weight : weightMap["ran9"];
		m.add rule : ( rangeOf(A, B, UID1) & fromConsumer1(X, A, Y) & fromConsumer2(X, A, Z) & hasType(Z,B) & nhasType(Y,B)) >> relatedTo(X,A,Z), weight : weightMap["ran10"];

		// inverse functional property
		//3.1
		m.add rule : (invFunProperty(A, UID) & fromFragment(R, A, O) & fromConsumer1(S, A, O)) >> isSame(R,S), weight : weightMap["ifp1"];
		m.add rule : (invFunProperty(A, UID) & fromFragment(R, A, O) & fromConsumer2(S, A, O)) >> isSame(R,S), weight : weightMap["ifp2"];
		m.add rule : (invFunProperty(A, UID) & fromConsumer1(R, A, O) & fromConsumer2(S, A, O)) >> isSame(S,R), weight: weightMap["ifp3"];

		// functional property
		//4.1
		m.add rule : (funProperty(A, UID) & fromFragment(S, A, O) & fromConsumer1(S, A, N) & resource(N) & resource(O) ) >> isSame(O,N), weight : weightMap["fp1"];
		
/*		m.add rule : (funProperty(A, UID) & fromFragment(S, A, O) & fromConsumer1(S, A, N) & ndisjointfrom(O,N)) >> relatedTo(S,A,N), weight : weightMap["fp1"];
		m.add rule : (funProperty(A, UID) & fromFragment(S, A, O) & fromConsumer2(S, A, N) & ndisjointfrom(O,N)) >> relatedTo(S,A,N), weight : weightMap["fp2"];
		m.add rule : (funProperty(A, UID) & fromConsumer1(S, A, O) & fromConsumer2(S, A, N) & ndisjointfrom(O,N)) >> relatedTo(S,A,N), weight : weightMap["fp3"];
		m.add rule : (funProperty(A, UID) & fromConsumer1(S, A, N) & fromConsumer2(S, A, O) & ndisjointfrom(O,N)) >> relatedTo(S,A,N), weight : weightMap["fp4"];
		
		//4.2
		m.add rule : (funProperty(A, UID) & fromFragment(S, A, O) & fromConsumer1(S, A, N) & ndiffrom(O,N)) >> relatedTo(S,A,N), weight : weightMap["fp5"];
		m.add rule : (funProperty(A, UID) & fromFragment(S, A, O) & fromConsumer2(S, A, N) & ndiffrom(O,N)) >> relatedTo(S,A,N), weight : weightMap["fp6"];
		m.add rule : (funProperty(A, UID) & fromConsumer1(S, A, O) & fromConsumer2(S, A, N) & ndiffrom(O,N)) >> relatedTo(S,A,N), weight : weightMap["fp7"];
		m.add rule : (funProperty(A, UID) & fromConsumer2(S, A, O) & fromConsumer1(S, A, N) & ndiffrom(O,N)) >> relatedTo(S,A,N), weight : weightMap["fp8"];
		
		//4.3
		m.add rule : (funProperty(A, UID) & fromFragment(S, A, O) & fromConsumer1(S, A, N) & sameas(O,N)) >> relatedTo(S,A,N), weight : weightMap["fp9"];
		m.add rule : (funProperty(A, UID) & fromFragment(S, A, O) & fromConsumer2(S, A, N) & sameas(O,N)) >> relatedTo(S,A,N), weight : weightMap["fp10"];
		m.add rule : (funProperty(A, UID) & fromConsumer1(S, A, O) & fromConsumer2(S, A, N) & sameas(O,N)) >> relatedTo(S,A,N), weight : weightMap["fp11"];
		m.add rule : (funProperty(A, UID) & fromConsumer2(S, A, O) & fromConsumer1(S, A, N) & sameas(O,N)) >> relatedTo(S,A,N), weight : weightMap["fp12"];
	*/
		//6.2

		//equivalent property
		//7.1
		m.add rule : (eqvproperty(A,B,UID) & fromFragment(S, A, N) & fromConsumer1(S, B, N) & fromConsumer2(S, B, O) & nsame(N,O)) >> relatedTo(S, B, N), weight : weightMap["ep1"];
		m.add rule : (eqvproperty(A,B,UID) & fromFragment(S, A, N) & fromConsumer2(S, B, N) & fromConsumer1(S, B, O) & nsame(N,O)) >> relatedTo(S, B, N), weight : weightMap["ep2"];
		m.add rule : (eqvproperty(A,B,UID) & fromFragment(S, A, N) & fromConsumer1(S, B, M) & fromConsumer2(S, B, O) & nsame(N,M) & nsame(N,O) & nsame(M,O)) >> relatedTo(S, B, N), weight : weightMap["ep3"];
		m.add rule : (eqvproperty(A,B,UID) & fromFragment(S, A, N) & fromConsumer2(S, B, M) & fromConsumer1(S, B, O) & nsame(N,M) & nsame(N,O) & nsame(M,O)) >> relatedTo(S, B, N), weight : weightMap["ep4"];

		//7.2
		m.add rule : (eqvproperty(C,B,UID) & subpropertyOf(A,B,UID1) & fromFragment(S, C, N) & fromConsumer1(S, A, N)
		& fromConsumer2(S, A, O)) >> relatedTo(S, A, N), weight : weightMap["ep5"];	// & nsame(N,O)
		m.add rule : (eqvproperty(C,B,UID) & subpropertyOf(A,B,UID1) & fromFragment(S, C, N) & fromConsumer2(S, A, N)
		& fromConsumer1(S, A, O)) >> relatedTo(S, A, N), weight : weightMap["ep6"];
		m.add rule : (eqvproperty(C,B,UID) & subpropertyOf(A,B,UID1) & fromFragment(S, C, N) & fromConsumer1(S, A, M)
		& fromConsumer2(S, A, O)) >> relatedTo(S, A, N), weight : weightMap["ep7"];
		m.add rule : (eqvproperty(C,B,UID) & subpropertyOf(A,B,UID1) & fromFragment(S, C, N) & fromConsumer2(S, A, M)
		& fromConsumer1(S, A, O)) >> relatedTo(S, A, N), weight : weightMap["ep8"];

		//same resources
		m.add rule : (fromConsumer1(S, A, N) & fromConsumer2(S, A, O) & sameas(N,O)) >> relatedTo(S, A, N), weight : weightMap["sa1"];
		m.add rule : (fromFragment(S, A, N) & fromConsumer1(S, A, O) & sameas(N,O)) >> relatedTo(S, A, O), weight : weightMap["sa2"];
		m.add rule : (fromFragment(S, A, N) & fromConsumer2(S, A, O) & sameas(N,O)) >> relatedTo(S, A, O), weight : weightMap["sa3"];

		//8.1 (can be used in combination with other rules??)
		m.add rule : (fromFragment(T, A, N) & fromConsumer1(S, A, N) & fromConsumer2(S, A, O) & sameas(T,S)) >> relatedTo(S, A, N), weight : weightMap["sa4"];
		m.add rule : (fromFragment(T, A, N) & fromConsumer2(S, A, N) & fromConsumer1(S, A, O) & sameas(T,S)) >> relatedTo(S, A, N), weight : weightMap["sa5"];
		m.add rule : (fromFragment(T, A, N) & fromConsumer1(S, A, M) & fromConsumer2(S, A, O) & sameas(T,S)) >> relatedTo(S, A, N), weight : weightMap["sa6"];
		m.add rule : (fromFragment(T, A, N) & fromConsumer2(S, A, M) & fromConsumer1(S, A, O) & sameas(T,S)) >> relatedTo(S, A, N), weight : weightMap["sa7"];

		//subproperty - can also be for literal object values
		//9.1
		m.add rule : (subpropertyOf(A,B,UID) & fromFragment(S, B, N) & fromConsumer1(S, A, N) & fromConsumer2(S, A, O) & nsame(N,O)) >> relatedTo(S, A, N), weight : weightMap["sp1"];
		m.add rule : (subpropertyOf(A,B,UID) & fromFragment(S, B, N) & fromConsumer2(S, A, N) & fromConsumer1(S, A, O) & nsame(N,O)) >> relatedTo(S, A, N), weight : weightMap["sp2"];
		m.add rule : (subpropertyOf(A,B,UID) & fromFragment(S, B, N) & fromConsumer1(S, A, M) & fromConsumer2(S, A, O) & nsame(N,M) & nsame(N,O) & nsame(M,O)) >> relatedTo(S, A, N), weight : weightMap["sp3"];
		m.add rule : (subpropertyOf(A,B,UID) & fromFragment(S, B, N) & fromConsumer2(S, A, M) & fromConsumer1(S, A, O) & nsame(N,M) & nsame(N,O) & nsame(M,O)) >> relatedTo(S, A, N), weight : weightMap["sp4"];

		// diff from
		//10.2
		m.add rule : (subpropertyOf(A,B,UID) & fromFragment(S, B, N) & fromConsumer1(S, A, N) & fromConsumer2(S, A, O) & diffrom(N,O)) >> relatedTo(S, A, N), weight : weightMap["df1"];
		m.add rule : (subpropertyOf(A,B,UID) & fromFragment(S, B, N) & fromConsumer2(S, A, N) & fromConsumer1(S, A, O) & diffrom(N,O)) >> relatedTo(S, A, N), weight : weightMap["df2"];
		m.add rule : (subpropertyOf(A,B,UID) & fromFragment(S, B, N) & fromConsumer1(S, A, M) & fromConsumer2(S, A, O) & diffrom(N,M) & diffrom(N,O) & diffrom(M,O)) >> relatedTo(S, A, N), weight : weightMap["df3"];
		m.add rule : (subpropertyOf(A,B,UID) & fromFragment(S, B, N) & fromConsumer2(S, A, M) & fromConsumer1(S, A, O) & diffrom(N,M) & diffrom(N,O) & diffrom(M,O)) >> relatedTo(S, A, N), weight : weightMap["df4"];
		//10.3
		m.add rule : (eqvproperty(A,B,UID) & fromFragment(S, A, N) & fromConsumer1(S, B, N) & fromConsumer2(S, B, O) & diffrom(N,O)) >> relatedTo(S, B, N), weight : weightMap["df5"];
		m.add rule : (eqvproperty(A,B,UID) & fromFragment(S, A, N) & fromConsumer2(S, B, N) & fromConsumer1(S, B, O) & diffrom(N,O)) >> relatedTo(S, B, N), weight : weightMap["df6"];
		m.add rule : (eqvproperty(A,B,UID) & fromFragment(S, A, N) & fromConsumer1(S, B, M) & fromConsumer2(S, B, O) & diffrom(N,M) & diffrom(N,O) & diffrom(M,O)) >> relatedTo(S, B, N), weight : weightMap["df7"];
		m.add rule : (eqvproperty(A,B,UID) & fromFragment(S, A, N) & fromConsumer2(S, B, M) & fromConsumer1(S, B, O) & diffrom(N,M) & diffrom(N,O) & diffrom(M,O)) >> relatedTo(S, B, N), weight : weightMap["df8"];

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

		return m;
	}

	////////////////////////// predicate declaration ////////////////////////
	def loadPredicates(m) {
		//inputs
		m.add predicate: "fromFragment" , types: [ArgumentType.String, ArgumentType.String, ArgumentType.String]
		m.add predicate: "fromConsumer1"  , types: [ArgumentType.String, ArgumentType.String, ArgumentType.String]
		m.add predicate: "fromConsumer2"  , types: [ArgumentType.String, ArgumentType.String, ArgumentType.String]

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
		m.add function: "resource"     , implementation: new isResource();
		
		m.add function: "ndisjointfrom"     , implementation: new isnotDisjoint();
		m.add function: "disjointfrom"     , implementation: new isDisjoint();
		m.add function: "nsame"     , implementation: new isnotSame();
		m.add function: "sameas"     , implementation: new is_same();
		m.add function: "diffrom"     , implementation: new isDiff();//currently, straight but also possible sameas(M,N) & difffrom(N, O)		
		m.add function: "ndiffrom"     , implementation: new isnotDiff();//currently, straight but also possible sameas(M,N) & difffrom(N, O)
	}


	//////////////////////////////External functions//////////////////////////
	class isnotDiff implements ExternalFunction {
		
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
		
					Property p = ResourceFactory.createProperty("http://www.w3.org/2002/07/owl#differentFrom");
					Resource r1 = x.getPropertyResourceValue(p);
		
					if (r1.equals(y))
						value = 0.0;
					else {
						r1 = y.getPropertyResourceValue(p);
						if (r1.equals(x))
							value = 0.0;
					}
					return value;
				}
			}
	
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

	class isResource implements ExternalFunction {
		@Override
		public int getArity() {
			return 1;
		}

		@Override
		public ArgumentType[] getArgumentTypes() {
			return [ArgumentType.String].toArray();
		}

		@Override
		public double getValue(ReadOnlyDatabase db, GroundTerm... args) {
			double value = 0.0;
			Resource x = model.getResource(args[0].getValue());	
			if (x!=null)
				value = 1.0;
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