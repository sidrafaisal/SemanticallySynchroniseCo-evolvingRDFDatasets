package eis.iai.uni.bonn.de;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.util.Date;
import java.util.Iterator;
import java.util.Scanner;
import java.util.Set;

import org.apache.jena.ontology.FunctionalProperty;
import org.apache.jena.ontology.HasValueRestriction;
import org.apache.jena.ontology.InverseFunctionalProperty;
import org.apache.jena.ontology.MaxCardinalityRestriction;
import org.apache.jena.ontology.OntClass;
import org.apache.jena.ontology.OntModel;
import org.apache.jena.ontology.OntProperty;
import org.apache.jena.ontology.OntResource;
import org.apache.jena.ontology.Restriction;
import org.apache.jena.util.FileManager;
import org.apache.jena.util.iterator.ExtendedIterator;
import org.semanticweb.HermiT.Reasoner;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.reasoner.NodeSet;
import org.semanticweb.owlapi.reasoner.OWLReasoner;
import org.semanticweb.owlapi.reasoner.OWLReasonerFactory;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.rdf.model.Property;
import org.apache.jena.rdf.model.RDFNode;
import org.apache.jena.rdf.model.Resource;
import org.apache.jena.rdf.model.ResourceFactory;
import org.apache.jena.rdf.model.Statement;
import org.apache.jena.rdf.model.StmtIterator;
import org.apache.jena.ontology.OntModelSpec;

import groovy.time.TimeCategory;
import groovy.time.TimeDuration;
public class LoadOntology  {

	private static Model model ;
	private static String ont_filename;
	private static String trainDir;
	private static String testDir;
	public static OntModel omodel;
	private static String type = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";
	private static String sameas = "http://www.w3.org/2002/07/owl#sameAs";

	public LoadOntology (String filename, String filesyntax) {
		model = FileManager.get().loadModel(filename, filesyntax);
	}

	static void populateFiles (String f, String dir) {
		ont_filename = f;
		trainDir = dir+"train"+java.io.File.separator;
		testDir = dir+"test"+java.io.File.separator;
		omodel = ModelFactory.createOntologyModel(OntModelSpec.OWL_MEM_MICRO_RULE_INF);
		InputStream ins = FileManager.get().open(ont_filename);

		if (ins == null)
			throw new IllegalArgumentException("File: "+ont_filename+" not found");
		omodel.read(ins, null);
	
		Date loadingfiles_time = new Date();
		System.out.println("Do you want to reparse ontology");
		Scanner reader = new Scanner(System.in); 
		System.out.println("Enter y/n: ");
		String n = reader.next();

		if (n.equals("y")) {
			try {
				System.out.println("Parsing ontology....");			
				getPropertiesInfo(omodel);				
				getClassesInfo(omodel);
				getRestrictions(omodel);
			}catch (IOException e) {
				e.printStackTrace();
			} catch (OWLOntologyCreationException e) {
				e.printStackTrace();
			}
		}
		Date loadingfilesfinished_time = new Date();
		TimeDuration td = TimeCategory.minus(loadingfilesfinished_time, loadingfiles_time);
		System.out.println("Total ontology loading time "+ td);

		loadingfiles_time = new Date();
		System.out.println("Do you want to repopulate truth values"); 
		System.out.println("Enter y/n: ");
		n = reader.next();	
		if (n.equals("y")) {
			try	{
				System.out.println("Populating truth values....");
				///get truth values
				getSame();
				getType();
				getRelatedto();
			} catch (IOException e) {
				e.printStackTrace();
			} 
		}
		reader.close();
		loadingfilesfinished_time = new Date();
		td = TimeCategory.minus(loadingfilesfinished_time, loadingfiles_time);
		System.out.println("Total truth values loading time "+ td);
	}

	/////////////////////////////////Sub - Eqv Class	
	private static void getClassesInfo(OntModel model) throws IOException, OWLOntologyCreationException{
		String scontent = "", econtent = "";
		long scounter = 1, ecounter = 1;
		ExtendedIterator<OntClass> ocs = model.listClasses();

		while(ocs.hasNext()) {
			OntClass oc = ocs.next();	

			// subclass
			if(oc.hasSuperClass()) {
				OntClass sc = oc.getSuperClass();
				scontent += oc.toString() + "\t" + sc.toString() + "\t"+ scounter++ +"\n";
			}		
			//equivalent classes
			ExtendedIterator<OntClass> ecs = oc.listEquivalentClasses();
			while(ecs.hasNext()) {				
				OntClass ec = ecs.next();
				econtent += oc.toString() + "\t" + ec.toString() + "\t" + ecounter++ +"\n";
			}
		}
		write("subclassof.txt", scontent);
		write("eqvclass.txt", econtent);

		getDisjointClasses(model);		

	}

	/////////////////////////////////maxcardinality, hasvalue, on property
	private static void getRestrictions(OntModel model) throws IOException {
		String mc = "", hv = "", opr = "";
		long counter = 1;
		ExtendedIterator<OntClass> ocs = model.listClasses();
		while(ocs.hasNext()) {
			OntClass oc = ocs.next();	
			if(oc.isRestriction()) {
				Restriction r = oc.asRestriction();

				int c = getMaxCardinalityRestriction(r);
				if (c > 0)
					mc += oc.toString() + "\t" + c + "\t" + counter + "\n";

				RDFNode n = getHasValueRestriction(r);

				if (n!=null) {
					hv += oc.toString() + "\t" + n.asResource().toString() + "\t" + counter + "\n";

				}
				OntProperty p = getOnPropertyRestriction(r);
				if (p!=null)
					opr += oc.toString() + "\t" + p.toString() + "\t" + counter + "\n";
				counter++;
			}
		}
		write("maxcardinality.txt",mc);
		write("hasvalue.txt",hv);
		write("onproperty.txt",opr);
	}

	private static int getMaxCardinalityRestriction(Restriction r) {
		int mc = 0;
		if (r.isMaxCardinalityRestriction()){
			MaxCardinalityRestriction mcr = r.asMaxCardinalityRestriction();
			mc = mcr.getMaxCardinality();
		}
		return mc;
	}

	private static OntProperty getOnPropertyRestriction(Restriction r){
		OntProperty opr = null;
		if (r.getOnProperty()!=null)
			opr = r.getOnProperty();		
		return opr;
	}

	private static RDFNode getHasValueRestriction(Restriction r){
		RDFNode hv =null;
		if (r.isHasValueRestriction()) {
			HasValueRestriction hvr = r.asHasValueRestriction();
			hv = hvr.getHasValue();
		}
		return hv;
	}

	/////////////////////////////////functional properties
	private static void getFunProperties(OntModel model) throws IOException {
		String content = "";
		long counter = 1;
		ExtendedIterator<FunctionalProperty> fps = model.listFunctionalProperties();
		while(fps.hasNext()) {
			FunctionalProperty fp = fps.next();
			content += fp.toString() + "\t" + counter++ +"\n";
		}
		write("funproperty.txt", content);
	}

	/////////////////////////////////inverse functional properties
	private static void getInvFunProperties(OntModel model) throws IOException{
		String content = "";
		long counter = 1;
		ExtendedIterator<InverseFunctionalProperty> ifps = model.listInverseFunctionalProperties();
		while(ifps.hasNext()) {
			InverseFunctionalProperty ifp = ifps.next();			
			content += ifp.toString() + "\t" + counter++ +"\n";
		}
		write("invfunproperty.txt", content);
	}

	/////////////////////////////////property domain/range and eq properties

	private static void getPropertiesInfo(OntModel model) throws IOException, OWLOntologyCreationException{

		String dcontent = "", rcontent = "", econtent="", scontent = "";
		long dcounter = 1, rcounter = 1, ecounter = 1, scounter = 1;

		Set<OntProperty> s_ont = model.listAllOntProperties().toSet();
		Iterator<OntProperty> ont = s_ont.iterator();
		while(ont.hasNext()) {
			OntProperty p = ont.next();
			//domain
			if (p.getDomain()!=null) {
				ExtendedIterator<? extends OntResource> ds = p.listDomain();
				while(ds.hasNext()) {
					OntResource d = ds.next();
					dcontent += p.toString() + "\t" + d.toString() + "\t" + dcounter++ +"\n";				
				}
			}
			//range
			if (p.getRange()!=null) {			
				ExtendedIterator<? extends OntResource> ds = p.listRange();
				while(ds.hasNext()) {
					OntResource r = ds.next();
					rcontent += p.toString() +"\t" + r.toString() + "\t" + rcounter++ +"\n";
				}
			}
			//sub property
			if (p.getSuperProperty()!=null) {
				ExtendedIterator<? extends OntProperty> ds = p.listSuperProperties();
				while(ds.hasNext()) {
					OntProperty sp = ds.next();
					scontent += p.toString() + "\t"+ sp.toString() + "\t" + scounter++ + "\n";
				}
			}
			//equivalent property 
			ExtendedIterator<? extends OntProperty> eps = p.listEquivalentProperties();
			while(eps.hasNext()) {
				OntProperty ep = eps.next();			
				econtent += p.toString() + "\t" + ep.toString() + "\t" + ecounter++ +"\n";
			}
		}
		write("domainof.txt", dcontent);
		write("rangeof.txt", rcontent);
		write("subpropertyof.txt", scontent);
		write("eqvproperty.txt", econtent);

		getFunProperties(model);
		getInvFunProperties(model);
	}

	/////////////////////////////////disjoint class 
	private static void getDisjointClasses(OntModel model) throws OWLOntologyCreationException, IOException  {
		String content = "";
		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();

		File f = new File(ont_filename);
		OWLOntology ontology = manager.loadOntologyFromOntologyDocument(f);
		OWLReasonerFactory reasonerFactory = new Reasoner.ReasonerFactory();
		OWLReasoner reasoner = reasonerFactory.createNonBufferingReasoner(ontology);
		OWLDataFactory fac = manager.getOWLDataFactory();

		ExtendedIterator<OntClass> ocs = model.listClasses();
		while(ocs.hasNext()) {
			OntClass oc = ocs.next();
			OWLClass owlclass = fac.getOWLClass(IRI.create(oc.toString()));

			NodeSet<OWLClass> disclass = reasoner.getDisjointClasses(owlclass);
			for (OWLClass c : disclass.getFlattened()) {			
				IRI iri = c.getIRI();				
				content += oc.toString() + "\t" + iri.toString() + "\n";
			}			
		}
		reasoner.dispose();
		write("disjointfrom.txt", content);

	}

	///////////////populate truth types
	private static void getType() throws IOException {
		String content = "";
		Property property = ResourceFactory.createProperty(type);
		StmtIterator iter = model.listStatements((Resource)null, property, (RDFNode)null);
		while (iter.hasNext()){
			Statement stmt = iter.next();
			if (stmt.getObject().isResource()) {
				content +=  stmt.getSubject().toString() +"\t"+ stmt.getObject().asResource().toString() + "\t" + "1" + "\n";
			}
		}
		write ("type.txt", content);
	}

	///////////////populate truth same as
	private static void getSame() throws IOException {
		String content = "";				
		Property property = ResourceFactory.createProperty(sameas);
		StmtIterator iter = model.listStatements((Resource)null, property, (RDFNode)null);

		while (iter.hasNext()){
			Statement stmt = iter.next();

			if (stmt.getObject().isResource()) {
				content +=  stmt.getSubject().toString() +"\t"+ stmt.getObject().asResource().toString() + "\t" + "1" + "\n";
			} 			
		}
		write ("issame.txt", content);
	}

	///////////////populate truth triples
	private static void getRelatedto() throws IOException {
		String content = "";
		StmtIterator iter = model.listStatements();
		while (iter.hasNext()){
			Statement stmt = iter.next();

			if (stmt.getObject().isResource()) {
				content +=  stmt.getSubject().toString() +"\t" + stmt.getPredicate().toString() +"\t"+ stmt.getObject().asResource().toString() + "\t" + "1" + "\n";
			} else {
				content +=  stmt.getSubject().toString() +"\t" + stmt.getPredicate().toString() +"\t"+ stmt.getObject().toString() + "\t" + "1" + "\n";

			}
		}
		write ("relatedto.txt", content);
	}

	/////////////// write
	private static void write (String filename, String content) throws IOException{
		writer(trainDir + filename, content);
		writer(testDir + filename, content);
	}

	private static void writer (String filename, String content) throws IOException{
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
