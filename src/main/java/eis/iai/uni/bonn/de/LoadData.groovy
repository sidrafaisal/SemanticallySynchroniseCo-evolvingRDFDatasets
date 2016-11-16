package eis.iai.uni.bonn.de

import java.io.FileReader;
import org.apache.jena.util.FileManager;
import org.apache.jena.rdf.model.Model;
import groovy.time.TimeDuration;
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
		
		InferenceUtils r =	new InferenceUtils();
		Date datasetsloading_time = new Date();
		def testDir = dir+'test'+java.io.File.separator;
		r.RDF2txt(datasets[0], testDir+"fromfragment", filesyntax);
		r.RDF2txt(datasets[1], testDir+"fromconsumer1", filesyntax);
		r.RDF2txt(datasets[2], testDir+"fromconsumer2", filesyntax);

		def trainDir = dir+'train'+java.io.File.separator;
		r.RDF2txt(datasets[0], trainDir+"fromfragment", filesyntax);
		r.RDF2txt(datasets[1], trainDir+"fromconsumer1", filesyntax);
		r.RDF2txt(datasets[2], trainDir+"fromconsumer2", filesyntax);
		
		Date datasetsloadingfinished_time = new Date();
		TimeDuration td = TimeCategory.minus(datasetsloadingfinished_time, datasetsloading_time);
		System.out.println "Total datasets loading time "+td;
	}
}