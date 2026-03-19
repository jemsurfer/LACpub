import java.io.*;
import java.util.*;

public class ParseE0 {

    static StringTokenizer st;
    static String curr;

    /** read the next token into curr */
    static void next() {
	try {
	    curr=st.nextToken().intern();
	    // use of intern() allows us to check equality with ==.
	} catch( NoSuchElementException e) {
	    curr=null;
	}
    }

    static void error(String msg) {
	System.err.println(msg);
	System.exit(-1);
    }

    static void parseE() {
	// E -> T E1
	parseT();
	parseE1();
    }

    static void parseE1() {
	// E1 -> + T E1 | epsilon
	if (curr=="+") {
	    next();
	    parseT();
	    parseE1();
	} else if(curr==")" || curr=="$" ) {
	} else {
	    error("Unexpected :"+curr);
	}
    }

    static void parseT() {
	// T -> F T1
	parseF();
	parseT1();
    }

    static void parseT1() {
	// T1 -> * F T1 | epsilon
	if (curr=="*") {
	    next();
	    parseF();
	    parseT1();
	} else if(curr=="+" || curr==")" || curr=="$") {
	} else {
	    error("Unexpected :"+curr);
	}
    }
    
    static void parseF() {
	// F -> ( E ) | a
	if( curr=="(") {
	    next();
	    parseE();
	    if(curr==")") {
		next();
	    } else {
		error (") expected.");
	    }
	} else if(curr=="a") {
	    next();
	} else {
	    error("Unexpected :"+curr);
	}
    }

    public static void main(String args []) throws IOException {
	BufferedReader in = new BufferedReader(new InputStreamReader (System.in));
	String line=in.readLine();
	st = new StringTokenizer(line+" $");
	next();
	parseE();
	if(curr=="$") {
	    System.out.println("OK ");
	} else {
	    error("End expected");
	} 
    }
}
