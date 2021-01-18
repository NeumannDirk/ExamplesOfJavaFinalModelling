package finalExamples;

import java.util.ArrayList;

public class PrimeTree {

	private /*@ spec_public @*/ final Node root = new Node(1, 1, null);
	private /*@ spec_public @*/ Node current;

	private /*@ spec_public @*/ class Node {
		final public int data;
		final public int primeFactor;
		final public Node parent;
		final public ArrayList<Node> children = new ArrayList<Node>();


		// @ modifies(this.data)
		// @ modifies(this.primeFactor)
		// @ modifies(this.parent)
		Node(final int data, final int primeFactor, final Node parent) {
			this.primeFactor = primeFactor;
			this.data = data;
			this.parent = parent;
		}
	}
	
	
	public void insert(final int val) {
		this.current = this.root;
		this.insert(val, 1);
	}

	private /*@ spec_public @*/ void insert(final int remainder, final int multSoFar) {
		boolean remainderIsPrime = true;
		for (int i = 2; i <= remainder / 2; i++) {
			if (remainder % i == 0) {
				remainderIsPrime = false;
				boolean newNodeRequired = true;
				for (Node node : this.current.children) {
					if (node.primeFactor == i) {
						newNodeRequired = false;
						this.current = node;
						this.insert(remainder / i, multSoFar * i);
					}
				}
				if (newNodeRequired) {
					Node newNode = new Node(multSoFar * i, i, this.current);
					this.current.children.add(newNode);
					this.current = newNode;
					this.insert(remainder / i, multSoFar * i);
				}
				break;
			}
		}
		if (remainderIsPrime) {
			Node newNode = new Node(multSoFar * remainder, remainder, this.current);
			this.current.children.add(newNode);
		}
	}

	/* @ pure @ */ private /*@ spec_public @*/ void print() {
		System.out.println(this.stringify(this.root, 0));
	}

	/* @ pure @ */ private /*@ spec_public @*/ String stringify(final Node node, final int level) {
		StringBuilder s = new StringBuilder();
		s.append(node.data + "\n ");
		String prefix = "  ".repeat(level);
		for (Node child : node.children) {
			s.append(prefix + "*" + child.primeFactor + "=" + this.stringify(child, level + 1));
		}
		return s.toString();
	}
	
	public static void main(String[] args) {
		PrimeTree tree = new PrimeTree();
		for (int i = 2; i < 32; i++) {
			tree.insert(i);
		}
		tree.print();
	}
}
