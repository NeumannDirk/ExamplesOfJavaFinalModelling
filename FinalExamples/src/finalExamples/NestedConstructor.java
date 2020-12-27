package finalExamples;

public class NestedConstructor {

	public final int finalValue;

	//@modifies(this.finalValue)
	//@assignable(this.finalValue)
	public NestedConstructor() {
		class Inner {
			/* @ pure @ */ public int foo(final int fooVal) {
				class EvenMoreInner {
					final private int innerFinal;

					// @ modifies(this.innerFinal)
					public EvenMoreInner(final int init) {
						this.innerFinal = init;
					}

					/* @ pure @ */ public int bar(final int barVal) {
						return fooVal + innerFinal + barVal;
					}
				}
				return new EvenMoreInner(fooVal).bar(fooVal);
			}
		}
		this.finalValue = new Inner().foo(1);
	}

	public static void main(String[] args) {
		System.out.println(new NestedConstructor().finalValue);
	}
}