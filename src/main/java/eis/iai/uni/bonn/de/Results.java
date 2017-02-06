package eis.iai.uni.bonn.de;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.HashSet;
import java.util.Set;

import com.google.common.collect.Sets;

public class Results {

	public static float precision;
	public static float recall;
	public static float f_measure;

	public static int intersect_count;
	public static int PSL_file_size;
	public static int CG_file_size;

	Results(String psl_file, String cg_file){	 	  
		compute_intersection(psl_file, cg_file);
		compute_precision();
		compute_recall();
		compute_fmeasure();
	}

	static void compute_precision() {
		precision = (float) intersect_count / PSL_file_size ;
	}

	static void compute_recall() {
		recall =  (float) intersect_count / CG_file_size;
	}

	static void compute_fmeasure() {
		f_measure = 2 * ((precision * recall) / (precision + recall)) ;
	}

	static void compute_intersection(String psl_file, String cg_file) {

		Set<String> set1 = read_files(psl_file);	
		PSL_file_size = set1.size();
		Set<String>  set2 = read_files(cg_file);
		CG_file_size = set2.size();
		Set<String> intersection;

	//	Iterator<String> set_diff_iter = null;
		if (PSL_file_size > CG_file_size) {
			intersection = Sets.intersection(set2, set1);
		//	set_diff_iter = Sets.difference(set2, set1).iterator();
		}
		else {
			intersection = Sets.intersection(set1, set2);
		//	set_diff_iter = Sets.difference(set1, set2).iterator();
		}
		
	/*	System.out.println("difference: ");
		while(set_diff_iter.hasNext()) {
			System.out.println(set_diff_iter.next());
		}
		System.out.println("---------------");
		*/
		intersect_count = intersection.size(); 	
	}

	static Set<String> read_files(String filename) {	
		Set<String> set = new HashSet<String>();		// read file and store content in a set 
		try {
			BufferedReader br = new BufferedReader(new FileReader(filename));
			String line = null;
			while ((line = br.readLine()) != null) {
				set.add(line);
			}
			br.close();
		} catch (IOException e) {
			e.printStackTrace();
		}
		return set;
	}
}
