package finalExamples;

public class IncrementTree {

	private final /* @ spec_public @ */ Node root;

	private /* @ spec_public @ */static class Node {
		public final Node left;
		public final Node right;
		public final int value;

		//@public normal_behaviour
		//@ensures retVal.value == this.value + 1;
		//@assignable \nothing;
		public Node increment() {
			Node newLeft = null;
			Node newRight = null;
			if (this.left != null) {
				newLeft = this.left.increment();
			}
			if (this.right != null) {
				newRight = this.right.increment();
			}
			Node retVal = new Node(this.value + 1, newRight, newLeft);
			return retVal;
		}

		//@assignable this.value;
		//@assignable this.left;
		//@assignable this.right;
		public Node(final int val, final Node left, final Node right) {
			this.value = val;
			this.left = left;
			this.right = right;
		}
	}

	public IncrementTree(Node root) {
		this.root = root;
	}

	//@public normal_behaviour
	//@assignable \nothing;
	//@ensures ((this.root ==null)&&(\return == null))||((this.root !=null)&&isBiggerByOne(this,\return));
	public IncrementTree increment() {
		if (this.root != null) {
			IncrementTree it = new IncrementTree(this.root.increment());
			return it;
		} else {
			return null;
		}
	}

	//@public normal_behaviour
	//@assignable \strictly_nothing;
	public static boolean isBiggerByOne(IncrementTree smal, IncrementTree big) {
		return isBiggerByOne(smal.root, big.root);
	}
	
	//@public normal_behaviour
	//@assignable \strictly_nothing;
	private static boolean isBiggerByOne(Node smal, Node big) {
		return smal.value == (big.value - 1) && isBiggerByOne(smal.left, big.left)
				&& isBiggerByOne(smal.right, big.right);
	}

	public void print() {
		this.print(this.root);
	}

	private void print(Node n) {
		if (n != null) {
			this.print(n.left);
			System.out.print(n.value + " ");
			this.print(n.right);
		}
	}

	//@public normal_behaviour
	//@ensures \true;
	public static void main(String[] args) {
		IncrementTree first = new IncrementTree(
				new Node(4, 
						new Node(2, 
								new Node(1, null, null), 
								new Node(3, null, null)),
						new Node(6, 
								new Node(5, null, null),
								new Node(7, null, null))
						)
				);
		IncrementTree second = first.increment();
		assert(isBiggerByOne(first,second));
	}
}
