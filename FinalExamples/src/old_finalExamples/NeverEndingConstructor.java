//package finalExamples;
//
//public class NeverEndingConstructor {
//
//	public final int finalValue;
//
//	// @ modifies(this.finalValue)
//	public NeverEndingConstructor() {
//		this.finalValue = foo();
//	}
//
//	/* @ pure @ */ private /*@ spec_public @*/ int foo() {
//		double d;	
//		while((d = Math.random()) < 2) {System.out.println(d);}
//		return 0;		
//	}
//
//	public static void main(String[] args) {
//		new NeverEndingConstructor();
//	}
//}