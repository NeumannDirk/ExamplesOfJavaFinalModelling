package finalExamples;

public class IncrementTree {

	private /* @ spec_public @ */ Node root;
	private /* @ spec_public @ */ Node current;

	/* @public invariant \forall Node n: 
	 * */
	private /* @ spec_public @ */ class Node {
		public Node left;
		public Node right;
		public int value;

		void increment() {
			value++;
			if (this.left != null) {
				left.increment();
			}
			if (this.right != null) {
				right.increment();
			}
		}

		/* @ pure @ */ boolean isConstant(int v) {
			return value == v && left.isConstant(v) && right.isConstant(v);
		}

		// @ modifies(this.val)
		// @ modifies(this.left)
		// @ modifies(this.right)
		public Node(final int val, final Node right, final Node left) {
			this.value = val;
			this.right = right;
			this.left = left;
		}
	}

	public void insert(int val) {
		if (this.root == null) {
			this.root = new Node(val, null, null);
		} else {
			this.insert2(val, this.root);
		}
	}

	private /* @ spec_public @ */ void insert2(int val, Node n) {
		if (val < n.value) {
			if (n.left == null) {
				n.left = new Node(val, null, null);
			} else {
				this.insert2(val, n.left);
			}
		} else {
			if (n.right == null) {
				n.right = new Node(val, null, null);
			} else {
				this.insert2(val, n.right);
			}
		}
	}

	public void increment() {
		this.increment(this.root);
	}
	
	/* @ requires n.isConstant(x)
	 * @ ensures n.isConstant(x+1)
	 */
	private /* @ spec_public @ */ void increment(Node n) {
		if (n != null) {
			n.value++;
			this.increment(n.left);
			this.increment(n.right);
		}
	}

	/* @ pure @ */ public void print() {
		this.print(this.root);
	}

	/* @ pure @ */ private /* @ spec_public @ */ void print(Node n) {
		if (n != null) {
			this.print(n.left);
			System.out.print(n.value + " ");
			this.print(n.right);
		}
	}

	public static void main(String[] args) {
		IncrementTree it = new IncrementTree();
		int[] a = new int[] { 8, 4, 12, 2, 6, 10, 14, 1, 3, 5, 7, 9, 11, 13, 15 };
		for (int i : a) {
			it.insert(i);
		}
		it.print();
		System.out.println();
		it.increment();
		it.print();

	}
}
