package eis.iai.uni.bonn.de;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.Date;
import java.util.Iterator;
import java.util.Scanner;
import java.util.Set;

import org.apache.jena.ontology.HasValueRestriction;
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
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.rdf.model.RDFNode;
import org.apache.jena.ontology.OntModelSpec;

import groovy.time.TimeCategory;
public class LoadOntology  {
	private static String ont_filename;
	public static OntModel omodel;
	
	static void populateFiles (String f, String dir, Scanner reader) {		
		omodel = ModelFactory.createOntologyModel(OntModelSpec.OWL_MEM_MICRO_RULE_INF);
		InputStream ins = FileManager.get().open(ont_filename = f);
		if (ins == null)
			throw new IllegalArgumentException("File: "+ont_filename+" not found");
		omodel.read(ins, null);

		System.out.println("Do you want to reparse ontology. Enter y/n: ");
		String n = reader.next();
		Date loadingfiles_time = new Date();
		if (n.equals("y")) {
			try {
				System.out.println("Parsing ontology....");		
				getPropertiesInfo(omodel);				
				getClassesInfo(omodel);
				getOWLClasses(omodel);
			} catch (IOException|OWLOntologyCreationException e) {
				e.printStackTrace();
			}
		}
		System.out.println("Total ontology loading time "+ TimeCategory.minus(new Date(), loadingfiles_time) +"seconds");
	}


	private static void getOWLClasses(OntModel model) throws OWLOntologyCreationException, IOException  {
		String content = "";
		long counter = 1;	
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
			content += owlclass.toString() + "\t" + counter++ + "\n";			
		}
		reasoner.dispose();
		InferenceUtils.write("owlclass.txt", content);
	}
	
	/////////////////////////////////Sub - Eqv Class	
	private static void getClassesInfo(OntModel model) throws IOException, OWLOntologyCreationException{
		String scontent = "", econtent = "", mc = "", hv = "", opr = "";
		long scounter = 1, ecounter = 1, counter = 1;
		ExtendedIterator<OntClass> ocs = model.listClasses();
		while(ocs.hasNext()) {
			OntClass oc = ocs.next();
			
			//getRestrictions - maxcardinality, hasvalue, on property
			if(oc.isRestriction()) {
				Restriction r = oc.asRestriction();
				int c = getMaxCardinalityRestriction(r);
				if (c > 0)
					mc += oc.toString() + "\t" + c + "\t" + counter + "\n";

				RDFNode n = getHasValueRestriction(r);
				if (n!=null) 
					hv += oc.toString() + "\t" + n.asResource().toString() + "\t" + counter + "\n";

				OntProperty p = getOnPropertyRestriction(r);
				if (p!=null)
					opr += oc.toString() + "\t" + p.toString() + "\t" + counter + "\n";
				counter++;
			}
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
		InferenceUtils.write("subclassof.txt", scontent);
		InferenceUtils.write("eqvclass.txt", econtent);
		InferenceUtils.write("maxcardinality.txt",mc);
		InferenceUtils.write("hasvalue.txt",hv);
		InferenceUtils.write("onproperty.txt",opr);
		getDisjointClasses(model);		

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

	/////////////////////////////////property domain/range and eq properties
	private static void getPropertiesInfo(OntModel model) throws IOException, OWLOntologyCreationException{

		String dcontent = "", rcontent = "", econtent="", scontent = "", fcontent = "", ifcontent = "";
		long dcounter = 1, rcounter = 1, ecounter = 1, scounter = 1, fcounter = 1, ifcounter = 1;

		Set<OntProperty> s_ont = model.listAllOntProperties().toSet();
		Iterator<OntProperty> ont = s_ont.iterator();
		while(ont.hasNext()) {
			OntProperty p = ont.next();
			if (p.isFunctionalProperty())
				fcontent += p.toString() + "\t" + fcounter++ +"\n";
			if (p.isInverseFunctionalProperty())
				ifcontent += p.toString() + "\t" + ifcounter++ +"\n";
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
		InferenceUtils.write("domainof.txt", dcontent);
		InferenceUtils.write("rangeof.txt", rcontent);
		InferenceUtils.write("subpropertyof.txt", scontent);
		InferenceUtils.write("eqvproperty.txt", econtent);
		InferenceUtils.write("funproperty.txt", fcontent);
		InferenceUtils.write("invfunproperty.txt", ifcontent);
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
		InferenceUtils.write("disjointfrom.txt", content);
	}
}
