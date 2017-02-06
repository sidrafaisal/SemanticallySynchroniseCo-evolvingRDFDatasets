package eis.iai.uni.bonn.de

import java.io.BufferedReader;
import java.io.FileReader;
import java.util.Map;

import org.apache.jena.rdf.model.RDFNode;
import org.apache.jena.rdf.model.Resource;
import org.apache.jena.rdf.model.ResourceFactory;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.Statement
import org.apache.jena.rdf.model.StmtIterator
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

	private static Model model, smodel, tmodel;
	String dir;

	def createModel (r, data, weightMap, d, mod, smod, tmod) {
		dir = d;
		model = mod;
		smodel = smod;
		tmodel = tmod;

		PSLModel m = new PSLModel(this, data);
		loadPredicates(m);
		String rdftype = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type",
		same = "http://www.w3.org/2002/07/owl#sameAs",
		dfrom = "http://www.w3.org/2002/07/owl#differentFrom";

		//	m.add rule : (fromDataset(S, A, O) & fromDataset(T, same, S)) >> fromFragment(T, A, O), constraint: true;
		//	m.add rule : (fromDataset(S, A, O) & fromDataset(S, same, T)) >> fromFragment(T, A, O), constraint: true;
		m.add rule : (fromDataset(S, A, O)) >> fromFragment(S, A, O), constraint: true;
		m.add rule : (fromDataset(S, dfrom, O)) >> diffrom (S, O), constraint: true;
		m.add rule : (fromConsumer1(S, dfrom, O)) >> diffrom (S, O), constraint: true;
		m.add rule : (fromConsumer2(S, dfrom, O)) >> diffrom (S, O), constraint: true;

		m.add rule : (fromDataset(S, dfrom, O)) >> diffrom (O, S), constraint: true;
		m.add rule : (fromConsumer1(S, dfrom, O)) >> diffrom (O, S), constraint: true;
		m.add rule : (fromConsumer2(S, dfrom, O)) >> diffrom (O, S), constraint: true;

		m.add rule : (fromDataset(S, same, O)) >> sameas (S, O), constraint: true;
		m.add rule : (fromConsumer1(S, same, O)) >> sameas (S, O), constraint: true;
		m.add rule : (fromConsumer2(S, same, O)) >> sameas (S, O), constraint: true;

		m.add rule : (fromDataset(S, same, O)) >> sameas (O, S), constraint: true;
		m.add rule : (fromConsumer1(S, same, O)) >> sameas (O, S), constraint: true;
		m.add rule : (fromConsumer2(S, same, O)) >> sameas (O, S), constraint: true;
		
		//	m.add rule : (fromdataset(S, A ,O) & nrepeat(A, same)) >> diffrom (S, O), constraint: true;

		//2.3 //hastype(B)
		//	m.add rule : ( rangeOf(A, B, UID1) & fromFragment(X, A, Y) & fromConsumer2(X, A, Z) & hasType(Y,B) & nhasType(Z,B)) >> relatedTo(X,A,Y), weight : weightMap["ran9"];
		//	m.add rule : ( rangeOf(A, B, UID1) & fromFragment(X, A, Y) & fromConsumer2(X, A, Z) & hasType(Z,B) & nhasType(Y,B)) >> relatedTo(X,A,Z), weight : weightMap["ran10"];
		
		 //disjiont classes
		 m.add rule : ( fromFragment(S, rdftype, B) & fromConsumer1(S, rdftype, D) & disjointfrom(D,B) & nrepeat(D,B)) >> type(S,B), weight : weightMap["sim1"];
		 m.add rule : ( fromFragment(S, rdftype, B) & fromConsumer2(S, rdftype, D) & disjointfrom(D,B) & nrepeat(D,B)) >> type(S,B), weight : weightMap["sim2"];
		 // domain
		 //1.1
		 m.add rule : ( domainOf(A, B, UID1) & fromFragment(S, A, O) & fromConsumer1(S, rdftype, D) & disjointfrom(D,B) & nrepeat(D,B)) >> type(S,B), weight : weightMap["dom1"];
		 m.add rule : ( domainOf(A, B, UID1) & fromFragment(S, A, O) & fromConsumer2(S, rdftype, D) & disjointfrom(D,B) & nrepeat(D,B)) >> type(S,B), weight : weightMap["dom2"];
		 // range
		 //2.1
		 m.add rule : ( rangeOf(A, B, UID1) & fromFragment(S, A, O) & fromConsumer1(O, rdftype, D) & disjointfrom(D,B) & nrepeat(D,B)) >> type(O,B), weight : weightMap["ran1"];
		 m.add rule : ( rangeOf(A, B, UID1) & fromFragment(S, A, O) & fromConsumer2(O, rdftype, D) & disjointfrom(D,B) & nrepeat(D,B)) >> type(O,B), weight : weightMap["ran2"];
		 //2.2//& notinFragment(S, A, O)
		 m.add rule : ( rangeOf(A, B, UID1) & fromConsumer1(S, A, O) & fromConsumer2(O, rdftype, D) & disjointfrom(D,B) & nrepeat(D,B)) >> type(O,B), weight : weightMap["ran3"];
		 m.add rule : ( rangeOf(A, B, UID1) & fromConsumer2(S, A, O) & fromConsumer1(O, rdftype, D) & disjointfrom(D,B) & nrepeat(D,B)) >> type(O,B), weight : weightMap["ran4"];
		 //equivalent property
		 //7.1
		 m.add rule : (eqvproperty(A,B,UID) & fromFragment(S, A, N) & fromConsumer1(S, B, N) & fromConsumer2(S, B, O) & nrepeat(A,B) & nrepeat(N,O) & nsame(N,O)) >> relatedTo(S, B, N), weight : weightMap["ep1"];
		 m.add rule : (eqvproperty(A,B,UID) & fromFragment(S, A, N) & fromConsumer2(S, B, N) & fromConsumer1(S, B, O) & nrepeat(A,B) & nrepeat(N,O) & nsame(N,O)) >> relatedTo(S, B, N), weight : weightMap["ep2"];
		 m.add rule : (eqvproperty(A,B,UID) & fromFragment(S, A, N) & fromConsumer1(S, B, M) & fromConsumer2(S, B, O) & nrepeat(A,B) & nrepeat(N,O) & nrepeat(N,M) & nrepeat(M,O) & nsame(N,M) & nsame(N,O) & nsame(M,O)) >> relatedTo(S, B, N), weight : weightMap["ep3"];
		 m.add rule : (eqvproperty(A,B,UID) & fromFragment(S, A, N) & fromConsumer2(S, B, M) & fromConsumer1(S, B, O) & nrepeat(A,B) & nrepeat(N,O) & nrepeat(N,M) & nrepeat(M,O) & nsame(N,M) & nsame(N,O) & nsame(M,O)) >> relatedTo(S, B, N), weight : weightMap["ep4"];
		 //7.2
		 m.add rule : (eqvproperty(C,B,UID) & subpropertyOf(A,B,UID1) & fromFragment(S, C, N) & fromConsumer1(S, A, N)
		 & fromConsumer2(S, A, O) & nrepeat(N,O) & nrepeat(C,B) & nrepeat(A,B) & nrepeat(A,C) ) >> relatedTo(S, A, N), weight : weightMap["ep5"];	// & nsame(N,O)
		 m.add rule : (eqvproperty(C,B,UID) & subpropertyOf(A,B,UID1) & fromFragment(S, C, N) & fromConsumer2(S, A, N)
		 & fromConsumer1(S, A, O) & nrepeat(N,O) & nrepeat(C,B) & nrepeat(A,B) & nrepeat(A,C) ) >> relatedTo(S, A, N), weight : weightMap["ep6"];
		 m.add rule : (eqvproperty(C,B,UID) & subpropertyOf(A,B,UID1) & fromFragment(S, C, N) & fromConsumer1(S, A, M)
		 & fromConsumer2(S, A, O) & nrepeat(N,O) & nrepeat(N,M) & nrepeat(M,O) & nrepeat(C,B) & nrepeat(A,B) & nrepeat(A,C) ) >> relatedTo(S, A, N), weight : weightMap["ep7"];
		 //subproperty - can also be for literal object values
		 //9.1
		 m.add rule : (subpropertyOf(A,B,UID) & fromFragment(S, B, N) & fromConsumer1(S, A, N) & fromConsumer2(S, A, O) & nrepeat(A,B) & nrepeat(N,O) & nsame(N,O)) >> relatedTo(S, A, N), weight : weightMap["sp1"];
		 m.add rule : (subpropertyOf(A,B,UID) & fromFragment(S, B, N) & fromConsumer2(S, A, N) & fromConsumer1(S, A, O) & nrepeat(A,B) & nrepeat(N,O) & nsame(N,O)) >> relatedTo(S, A, N), weight : weightMap["sp2"];
		 m.add rule : (subpropertyOf(A,B,UID) & fromFragment(S, B, N) & fromConsumer1(S, A, M) & fromConsumer2(S, A, O) & nrepeat(A,B) & nrepeat(N,O) & nrepeat(N,M) & nrepeat(M,O)& nsame(N,M) & nsame(N,O) & nsame(M,O)) >> relatedTo(S, A, N), weight : weightMap["sp3"];
		 m.add rule : (subpropertyOf(A,B,UID) & fromFragment(S, B, N) & fromConsumer2(S, A, M) & fromConsumer1(S, A, O) & nrepeat(A,B) & nsame(N,M)& nrepeat(N,O) & nrepeat(N,M) & nrepeat(M,O) & nsame(N,O) & nsame(M,O)) >> relatedTo(S, A, N), weight : weightMap["sp4"];
		 // diff from
		 //10.2
		 m.add rule : (subpropertyOf(A,B,UID) & fromFragment(S, B, N) & fromConsumer1(S, A, N) & fromConsumer2(S, A, O) & nrepeat(A,B) & nrepeat(N,O) & diffrom(N,O)) >> relatedTo(S, A, N), weight : weightMap["df1"];
		 m.add rule : (subpropertyOf(A,B,UID) & fromFragment(S, B, N) & fromConsumer2(S, A, N) & fromConsumer1(S, A, O) & nrepeat(A,B) & nrepeat(N,O) & diffrom(N,O)) >> relatedTo(S, A, N), weight : weightMap["df2"];
		 m.add rule : (subpropertyOf(A,B,UID) & fromFragment(S, B, N) & fromConsumer1(S, A, M) & fromConsumer2(S, A, O) & nrepeat(A,B) & nrepeat(N,O) & nrepeat(N,M) & nrepeat(M,O) & diffrom(N,M) & diffrom(N,O) & diffrom(M,O)) >> relatedTo(S, A, N), weight : weightMap["df3"];
		 m.add rule : (subpropertyOf(A,B,UID) & fromFragment(S, B, N) & fromConsumer2(S, A, M) & fromConsumer1(S, A, O) & nrepeat(A,B) & nrepeat(N,O) & nrepeat(N,M) & nrepeat(M,O) & diffrom(N,M) & diffrom(N,O) & diffrom(M,O)) >> relatedTo(S, A, N), weight : weightMap["df4"];
		 //10.3
		 m.add rule : (eqvproperty(A,B,UID) & fromFragment(S, A, N) & fromConsumer1(S, B, N) & fromConsumer2(S, B, O) & nrepeat(A,B) & nrepeat(N,O) & diffrom(N,O)) >> relatedTo(S, B, N), weight : weightMap["df5"];
		 m.add rule : (eqvproperty(A,B,UID) & fromFragment(S, A, N) & fromConsumer2(S, B, N) & fromConsumer1(S, B, O) & nrepeat(A,B) & nrepeat(N,O) & diffrom(N,O)) >> relatedTo(S, B, N), weight : weightMap["df6"];
		 m.add rule : (eqvproperty(A,B,UID) & fromFragment(S, A, N) & fromConsumer1(S, B, M) & fromConsumer2(S, B, O) & nrepeat(A,B) & nrepeat(N,O) & nrepeat(N,M) & nrepeat(M,O) & diffrom(N,M) & diffrom(N,O) & diffrom(M,O)) >> relatedTo(S, B, N), weight : weightMap["df7"];
		 m.add rule : (eqvproperty(A,B,UID) & fromFragment(S, A, N) & fromConsumer2(S, B, M) & fromConsumer1(S, B, O) & nrepeat(A,B) & nrepeat(N,O) & nrepeat(N,M) & nrepeat(M,O) & diffrom(N,M) & diffrom(N,O) & diffrom(M,O)) >> relatedTo(S, B, N), weight : weightMap["df8"];
		 
		//8.1 same resources(can be used in combination with other rules??)
		m.add rule : (fromFragment(T, A, N) & fromConsumer1(S, A, N) & fromConsumer2(S, A, O) & sameas(T,S) & nrepeat(T,S) & nrepeat(N,O) & diffrom(N,O)) >> relatedTo(S, A, N), weight : weightMap["sa4"];
		m.add rule : (fromFragment(T, A, N) & fromConsumer2(S, A, N) & fromConsumer1(S, A, O) & sameas(T,S) & nrepeat(T,S) & nrepeat(N,O) & diffrom(N,O)) >> relatedTo(S, A, N), weight : weightMap["sa5"];
		m.add rule : (fromFragment(T, A, N) & fromConsumer1(S, A, M) & fromConsumer2(S, A, O) & sameas(T,S) & nrepeat(T,S) & nrepeat(N,O) & nrepeat(M,N) & diffrom(N,O) & diffrom(M,N)) >> relatedTo(S, A, N), weight : weightMap["sa6"];
		m.add rule : (fromFragment(T, A, N) & fromConsumer2(S, A, M) & fromConsumer1(S, A, O) & sameas(T,S) & nrepeat(T,S) & nrepeat(N,O) & nrepeat(M,N) & diffrom(N,O) & diffrom(M,N)) >> relatedTo(S, A, N), weight : weightMap["sa7"];//& nrepeat(M,O) & diffrom(M,O)
		 
				
		/*		// inverse functional property
		 //3.1
		 m.add rule : (invFunProperty(A, UID) & fromFragment(R, A, O) & fromConsumer1(S, A, O) & nrepeat(S,R)) >> isSame(R,S), weight : weightMap["ifp1"];
		 m.add rule : (invFunProperty(A, UID) & fromFragment(R, A, O) & fromConsumer2(S, A, O) & nrepeat(S,R)) >> isSame(R,S), weight : weightMap["ifp2"];
		 m.add rule : (invFunProperty(A, UID) & fromConsumer1(R, A, O) & fromConsumer2(S, A, O)) >> isSame(S,R), weight: weightMap["ifp3"];
		 // functional property
		 //4.1
		 m.add rule : (funProperty(A, UID) & fromFragment(S, A, O) & fromConsumer1(S, A, N) & resource(N) & resource(O) & nrepeat(N,O)) >> isSame(O,N), weight : weightMap["fp1"];
		 m.add rule : (funProperty(A, UID) & fromFragment(S, A, O) & fromConsumer2(S, A, N) & resource(N) & resource(O) & nrepeat(N,O)) >> isSame(O,N), weight : weightMap["fp2"];
		 m.add rule : (funProperty(A, UID) & fromConsumer1(S, A, O) & fromConsumer2(S, A, N) & resource(N) & resource(O) & nrepeat(N,O)) >> isSame(O,N), weight : weightMap["fp3"];
		 //6.2*/

		//2.2
		/*		m.add rule : ( rangeOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromFragment(S, C, O) & fromConsumer1(O, rdftype, D) & disjointfrom(D,B) & nrepeat(D,B)) >> type(O,B), weight : weightMap["ran5"];
		 m.add rule : ( rangeOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromFragment(S, C, O) & fromConsumer2(O, rdftype, D) & disjointfrom(D,B) & nrepeat(D,B)) >> type(O,B), weight : weightMap["ran6"];
		 m.add rule : ( rangeOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromConsumer1(S, C, O) & fromConsumer2(O, rdftype, D) & disjointfrom(D,B) & nrepeat(D,B)) >> type(O,B), weight : weightMap["ran7"];
		 m.add rule : ( rangeOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromConsumer2(S, C, O) & fromConsumer1(O, rdftype, D) & disjointfrom(D,B) & nrepeat(D,B)) >> type(O,B), weight : weightMap["ran8"];
		 m.add rule : ( domainOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromFragment(S, C, O) & fromConsumer1(S, rdftype, D) & disjointfrom(D,B) & nrepeat(D,B)) >> type(S,B), weight : weightMap["dom5"];
		 m.add rule : ( domainOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromFragment(S, C, O) & fromConsumer2(S, rdftype, D) & disjointfrom(D,B) & nrepeat(D,B)) >> type(S,B), weight : weightMap["dom6"];
		 m.add rule : ( domainOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromConsumer1(S, C, O) & fromConsumer2(S, rdftype, D) & disjointfrom(D,B) & nrepeat(D,B)) >> type(S,B), weight : weightMap["dom7"];
		 m.add rule : ( domainOf(A, B, UID1) & subpropertyOf(C, A, UID2) & fromConsumer2(S, C, O) & fromConsumer1(S, rdftype, D) & disjointfrom(D,B) & nrepeat(D,B)) >> type(S,B), weight : weightMap["dom8"];
		 */

		//same resources //dont make sense
		/*		m.add rule : (fromConsumer1(S, A, N) & fromConsumer2(S, A, O) & sameas(N,O) & nrepeat(N,O)) >> relatedTo(S, A, O), weight : weightMap["sa1"];
		 m.add rule : (fromConsumer1(S, A, N) & fromConsumer2(S, A, O) & sameas(N,O) & nrepeat(N,O)) >> relatedTo(S, A, N), weight : weightMap["sa1"];
		 m.add rule : (fromFragment(S, A, N) & fromConsumer1(S, A, O) & sameas(N,O) & nrepeat(N,O)) >> relatedTo(S, A, O), weight : weightMap["sa2"];
		 m.add rule : (fromFragment(S, A, N) & fromConsumer2(S, A, O) & sameas(N,O) & nrepeat(N,O)) >> relatedTo(S, A, O), weight : weightMap["sa3"];
		 */
		/*		m.add rule : ( domainOf(A, B, UID1) & fromConsumer1(S, A, O) & fromConsumer2(S, rdftype, D) & disjointfrom(D,B) & nrepeat(D,B)) >> type(S,B), weight : weightMap["dom3"];
		 m.add rule : ( domainOf(A, B, UID1) & fromConsumer2(S, A, O) & fromConsumer1(S, rdftype, D) & disjointfrom(D,B) & nrepeat(D,B)) >> type(S,B), weight : weightMap["dom4"];
		 //1.2
		 */

		// constraints
		m.add PredicateConstraint.PartialFunctional , on : type;
		//	m.add PredicateConstraint.PartialFunctional , on : relatedTo; support only binary predicates
		m.add PredicateConstraint.PartialFunctional , on : isSame;
		m.add PredicateConstraint.PartialInverseFunctional , on : isSame;
		m.add PredicateConstraint.Symmetric , on : isSame;

		// prior
		m.add rule : ~type(X,D), weight: weightMap["type"];
		m.add rule : ~isSame(Y,Z), weight: weightMap["isSame"];
		m.add rule : ~relatedTo(X,A,Z), weight: weightMap["related"];

		return m;
	}

	////////////////////////// predicate declaration ////////////////////////
	def loadPredicates(m) {
		//inputs
		m.add predicate: "fromDataset" , types: [ArgumentType.String, ArgumentType.String, ArgumentType.String]

		m.add predicate: "fromFragment" , types: [ArgumentType.String, ArgumentType.String, ArgumentType.String]
		m.add predicate: "fromConsumer1"  , types: [ArgumentType.String, ArgumentType.String, ArgumentType.String]
		m.add predicate: "fromConsumer2"  , types: [ArgumentType.String, ArgumentType.String, ArgumentType.String]
		m.add predicate: "diffrom"  , types: [ArgumentType.String, ArgumentType.String]

		m.add predicate: "sameas"  , types: [ArgumentType.String, ArgumentType.String]
		
		//from ontology
		m.add predicate: "owlclass"    , types: [ArgumentType.String, ArgumentType.UniqueID]

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
		m.add function: "nrepeat"     , implementation: new isnotRepeat();
		m.add function: "ndisjointfrom"     , implementation: new isnotDisjoint();
		m.add function: "disjointfrom"     , implementation: new isDisjoint();
		m.add function: "nsame"     , implementation: new isnotSame();
	//	m.add function: "sameas"     , implementation: new is_same();
		m.add function: "notinFragment"     , implementation: new notinFragment();
		//		m.add function: "diffrom"     , implementation: new isDiff();//currently, straight but also possible sameas(M,N) & difffrom(N, O)
		//	m.add function: "ndiffrom"     , implementation: new isnotDiff();//currently, straight but also possible sameas(M,N) & difffrom(N, O)
	}


	//////////////////////////////External functions//////////////////////////
	class notinFragment implements ExternalFunction {

		@Override
		public int getArity() {
			return 3;
		}

		@Override
		public ArgumentType[] getArgumentTypes() {
			return [ArgumentType.String,ArgumentType.String,ArgumentType.String].toArray();
		}

		@Override
		public double getValue(ReadOnlyDatabase db, GroundTerm... args) {
			double value = 1.0;
			Resource s = model.getResource(args[0].getValue());
			Property p = ResourceFactory.createProperty(args[1].getValue());
			RDFNode o = (RDFNode) ResourceFactory.createResource(args[2].getValue());
			if(model.contains(s, p, o))
				value = 0.0;
			return value;
		}
	}

	class isnotRepeat implements ExternalFunction {

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
			if(args[0].getValue().equals(args[1].getValue()))
				value = 0.0;
			return value;
		}
	}

	/*	class isnotDiff implements ExternalFunction {
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
	 if (x == null)
	 x = smodel.getResource(args[0].getValue());
	 if (x == null)
	 x = tmodel.getResource(args[0].getValue());
	 Resource y = model.getResource(args[1].getValue());
	 if (y == null)
	 y = smodel.getResource(args[1].getValue());
	 if (y == null)
	 y = tmodel.getResource(args[1].getValue());
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
	 if (x == null)
	 x = smodel.getResource(args[0].getValue());
	 if (x == null)
	 x = tmodel.getResource(args[0].getValue());
	 Resource y = model.getResource(args[1].getValue());
	 if (y == null)
	 y = smodel.getResource(args[1].getValue());
	 if (y == null)
	 y = tmodel.getResource(args[1].getValue());
	 Property p = ResourceFactory.createProperty("http://www.w3.org/2002/07/owl#differentFrom");
	 Resource r1 = x.getPropertyResourceValue(p);
	 if (r1.equals(y))
	 value = 1.0;
	 else {
	 r1 = y.getPropertyResourceValue(p);
	 if (r1.equals(x))
	 value = 1.0;
	 }
	 //	if (value==1.0) {
	 //	System.out.println(x.toString()+",    "+y.toString());
	 //	}
	 return value;
	 }
	 }*/

/*	class is_same implements ExternalFunction {
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

			Property p = ResourceFactory.createProperty("http://www.w3.org/2002/07/owl#sameAs");

			Resource x = model.getResource(args[0].getValue());
			//if (x != null && model.listStatements(x,p,args[1].getValue()).toSet().size() > 0)
			//	return 1.0;
			if (x == null) {
				x = smodel.getResource(args[0].getValue());
			//	if (x != null && smodel.listStatements(x,p,args[1].getValue()).toSet().size() > 0)
			//		return 1.0;
			}
			if (x == null) {
				x = tmodel.getResource(args[0].getValue());
			//	if (x != null && tmodel.listStatements(x,p,args[1].getValue()).toSet().size() > 0)
			//		return 1.0;
			}


			Resource y = model.getResource(args[1].getValue());
		//	if (y != null && model.listStatements(y,p,args[0].getValue()).toSet().size() > 0)
		//		return 1.0;
			if (y == null) {
				y = smodel.getResource(args[1].getValue());
			//	if (y != null && smodel.listStatements(y,p,args[0].getValue()).toSet().size() > 0)
			//		return 1.0;
			}
			if (y == null) {
				y = tmodel.getResource(args[1].getValue());
			//	if (y != null && tmodel.listStatements(y,p,args[0].getValue()).toSet().size() > 0)
			//		return 1.0;
			}
			
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
	}*/

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
			if (x == null)
				x = smodel.getResource(args[0].getValue());
			if (x == null)
				x = tmodel.getResource(args[0].getValue());

			Resource y = model.getResource(args[1].getValue());
			if (y == null)
				y = smodel.getResource(args[1].getValue());
			if (y == null)
				y = tmodel.getResource(args[1].getValue());
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
			if (x==null)
				x = smodel.getResource(args[0].getValue());
			if (x==null)
				x = tmodel.getResource(args[0].getValue());
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
			double value = 1.0;
			//double value = 0.0;
			Resource x = smodel.getResource(args[0].getValue());
			if (x==null)
				x = tmodel.getResource(args[0].getValue());
			if (x==null)
				x = model.getResource(args[0].getValue());
			Property type_property = ResourceFactory.createProperty("http://www.w3.org/1999/02/22-rdf-syntax-ns#type");
			RDFNode type = (RDFNode) ResourceFactory.createResource(args[1].getValue());
			Set<String> shouldnotof_type =  new HashSet<String>();

			////disjoint check
			BufferedReader	br = new BufferedReader(new FileReader(dir+'train'+java.io.File.separator+"disjointfrom.txt"));
			String line = null;
			while ((line = br.readLine()) != null) {
				if (line.contains(type.toString())) {
					int sep = line.indexOf("\t");
					String class1 = line.substring(0, sep);
					String class2 = line.substring(sep+1, line.length());
					if (class1.equals(type.toString()))
						shouldnotof_type.add(class2);
					else if (class2.equals(type.toString()))
						shouldnotof_type.add(class1);
				}
			}
			br.close();
			///end

			Set<Statement> s_stmt = smodel.listStatements(x, type_property, (RDFNode)null).toSet();
			s_stmt.addAll(tmodel.listStatements(x, type_property, (RDFNode)null).toSet());
			s_stmt.addAll(model.listStatements(x, type_property, (RDFNode)null).toSet());

			Iterator<Statement> i_stmt = s_stmt.iterator();
			while (i_stmt.hasNext()) {
				Statement stmt = i_stmt.next();
				RDFNode object = stmt.getObject();
				if (shouldnotof_type.contains(object.toString()))
					value = 0.0;
			}
			/*	if (smodel.contains(x, type_property, type) || tmodel.contains(x, type_property, type) || model.contains(x, type_property, type)) {
			 value = 1.0;
			 }
			 */	
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

			double value = 0.0;
			Resource x = smodel.getResource(args[0].getValue());
			if (x==null)
				x = tmodel.getResource(args[0].getValue());
			if (x==null)
				x = model.getResource(args[0].getValue());
			Property type_property = ResourceFactory.createProperty("http://www.w3.org/1999/02/22-rdf-syntax-ns#type");
			RDFNode type = (RDFNode) ResourceFactory.createResource(args[1].getValue());
			Set<String> shouldnotof_type =  new HashSet();

			////disjoint check
			BufferedReader	br = new BufferedReader(new FileReader(dir+'train'+java.io.File.separator+"disjointfrom.txt"));
			String line = null;
			while ((line = br.readLine()) != null) {
				if (line.contains(type.toString())) {
					int sep = line.indexOf("\t");
					String class1 = line.substring(0, sep);
					String class2 = line.substring(sep+1, line.length());
					if (class1.equals(type.toString()))
						shouldnotof_type.add(class2);
					else if (class2.equals(type.toString()))
						shouldnotof_type.add(class1);
				}
			}
			br.close();
			///end

			Set<Statement> s_stmt = smodel.listStatements(x, type_property, (RDFNode)null).toSet();
			s_stmt.addAll(tmodel.listStatements(x, type_property, (RDFNode)null).toSet());
			s_stmt.addAll(model.listStatements(x, type_property, (RDFNode)null).toSet());

			Iterator<Statement> i_stmt = s_stmt.iterator();
			while (i_stmt.hasNext()) {
				Statement stmt = i_stmt.next();
				RDFNode object = stmt.getObject();
				if (shouldnotof_type.contains(object.toString()))
					value = 1.0;
			}

			/*	double value = 1.0;
			 Resource x = smodel.getResource(args[0].getValue());
			 if (x==null)
			 x = tmodel.getResource(args[0].getValue());
			 if (x==null)
			 x = model.getResource(args[0].getValue());
			 Property type_property = ResourceFactory.createProperty("http://www.w3.org/1999/02/22-rdf-syntax-ns#type");
			 RDFNode type = (RDFNode) ResourceFactory.createResource(args[1].getValue());
			 if (smodel.contains(x, type_property, type) || tmodel.contains(x, type_property, type) || model.contains(x, type_property, type)){
			 value = 0.0;
			 }*/
			return value;
		}
	}

}
