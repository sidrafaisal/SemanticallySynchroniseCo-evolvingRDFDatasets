package eis.iai.uni.bonn.de

import java.io.FileReader;
import java.io.IOException;
import java.io.InputStream;
import java.util.Date;
import java.util.Scanner;

import org.apache.jena.util.FileManager;
import org.apache.jena.ontology.OntModelSpec;
import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.rdf.model.RDFNode;
import org.apache.jena.rdf.model.Resource;
import org.apache.jena.rdf.model.ResourceFactory;
import org.apache.jena.rdf.model.Statement;
import org.apache.jena.rdf.model.StmtIterator;

import groovy.time.TimeCategory;

import org.apache.jena.rdf.model.Property;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;

public class LoadData {
	String filename, filesyntax;
	public Model smodel, tmodel;
	private Object dir;

	private static String type = "http://www.w3.org/1999/02/22-rdf-syntax-ns#type";
	private static String sameas = "http://www.w3.org/2002/07/owl#sameAs";
	private static String dfrom = "http://www.w3.org/2002/07/owl#differentFrom";
	private static Model model;

	public LoadData(String d, String [] datasets, Scanner reader){
		filename = datasets[0];
		filesyntax = datasets[4];
		dir = d;
		model = FileManager.get().loadModel(filename, filesyntax);
		smodel = FileManager.get().loadModel(datasets[1], filesyntax);
		tmodel = FileManager.get().loadModel(datasets[2], filesyntax);

		System.out.println ("-------------------");
		System.out.println ("No. of triples in Fragment/slice" + model.size());
		System.out.println ("No. of triples in consumer1_changes dataset" + smodel.size());
		System.out.println ("No. of triples in consumer2_changes dataset" + tmodel.size());
		System.out.println ("-------------------");

		Date datasetsloading_time = new Date();
		def testDir = dir+'test'+java.io.File.separator;
		RDF2txt(datasets[5], testDir+"fromdataset", filesyntax);
		RDF2txt(datasets[6], testDir+"fromconsumer1", filesyntax);
		RDF2txt(datasets[7], testDir+"fromconsumer2", filesyntax);

		def trainDir = dir+'train'+java.io.File.separator;
		RDF2txt(datasets[0], trainDir+"fromdataset", filesyntax);
		RDF2txt(datasets[1], trainDir+"fromconsumer1", filesyntax);
		RDF2txt(datasets[2], trainDir+"fromconsumer2", filesyntax);

		System.out.println ("Total datasets loading time "+ TimeCategory.minus(new Date(), datasetsloading_time));
		
		///////////////populate truth values
		System.out.println("Do you want to repopulate truth values. Enter y/n: ");
			String n = reader.next();
		Date loadingfiles_time = new Date();
		if (n.equals("y")) {
			try	{
				System.out.println("Populating truth values....");
				String sameas_content = getsameas();
				InferenceUtils.write("issame.txt", sameas_content); //function predicate
				InferenceUtils.write("sameas.txt", sameas_content); //target predicate
				InferenceUtils.write("type.txt", getType());
				InferenceUtils.write("relatedto.txt", getRelatedto());
				InferenceUtils.write("fromfragment.txt", getFragment());
				InferenceUtils.write("diffrom.txt", getdiffrom());
			} catch (IOException e) {
				e.printStackTrace();
			}
		}
		System.out.println("Total truth values loading time "+ TimeCategory.minus(new Date(), loadingfiles_time));
	}

	static void RDF2txt(String ifilename, String ofilename, String filesyntax) throws IOException {
		Model temp_model = FileManager.get().loadModel(ifilename, filesyntax);
		String content = "";

		StmtIterator iter1 = temp_model.listStatements();
		while (iter1.hasNext()) {
			Statement stmt = iter1.next();
			Resource subject = stmt.getSubject();
			Property predicate = stmt.getPredicate();
			RDFNode object = stmt.getObject();

			if (object.isResource())
				content += subject.toString() +"\t"+ predicate.toString() + "\t" + object.asResource().toString() + "\n";
			else
				content += subject.toString() +"\t"+ predicate.toString() + "\t" + object.toString() + "\n";
		}
		InferenceUtils.writer (ofilename+".txt", content);
		temp_model.close();
	}

	private static String getType() {
		String content = "";
		Property property = ResourceFactory.createProperty(type);
		StmtIterator iter = model.listStatements((Resource)null, property, (RDFNode)null);
		while (iter.hasNext()){
			Statement stmt = iter.next();
			if (stmt.getObject().isResource()) {
				content +=  stmt.getSubject().toString() +"\t"+ stmt.getObject().asResource().toString() + "\t" + "1" + "\n";
			}
		}
		return content;
	}

	private static String getFragment() {
		String content = "";
		StmtIterator iter = model.listStatements();
		while (iter.hasNext()){
			Statement stmt = iter.next();
			content +=  stmt.getSubject().toString() + "\t"+ stmt.getPredicate().toString() +"\t"+ stmt.getObject().toString() + "\t" + "1" + "\n";
		}
		return content;
	}


	private static String getdiffrom() {
		String content = "";
		Property property = ResourceFactory.createProperty(dfrom);
		StmtIterator iter = model.listStatements((Resource)null, property, (RDFNode)null);
		while (iter.hasNext()){
			Statement stmt = iter.next();
			content +=  stmt.getSubject().toString() + "\t"+ stmt.getObject().toString() + "\t" + "1" + "\n";
		}
		return content;
	}

	///////////////populate truth same as
	private static String getsameas() {
		String content = "";
		Property property = ResourceFactory.createProperty(sameas);
		StmtIterator iter = model.listStatements((Resource)null, property, (RDFNode)null);
		while (iter.hasNext()){
			Statement stmt = iter.next();
			content +=  stmt.getSubject().toString() + "\t"+ stmt.getObject().toString() + "\t" + "1" + "\n";
		}
		return content;
	}

	///////////////populate truth triples
	private static String getRelatedto() {
		String content = "";
		StmtIterator iter = model.listStatements();
		while (iter.hasNext()) {
			Statement stmt = iter.next();
			if (stmt.getObject().isResource())
				content +=  stmt.getSubject().toString() +"\t" + stmt.getPredicate().toString() +"\t"+ stmt.getObject().asResource().toString() + "\t" + "1" + "\n";
			else
				content +=  stmt.getSubject().toString() +"\t" + stmt.getPredicate().toString() +"\t"+ stmt.getObject().toString() + "\t" + "1" + "\n";
		}
		return content;
	}
}