package finalExamples;

public class IncrementTree {
	
	private final /* @ spec_public @ */ TreeNode root;

	public IncrementTree(TreeNode root) {
		this.root = root;
	}

	//@public normal_behaviour
	//@assignable \nothing;
	//@ensures ((this.root ==null)&&(\result == null))||((this.root !=null)&&isBiggerByOne(this,\result));
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
	private static boolean isBiggerByOne(TreeNode smal, TreeNode big) {
		return smal.value == (big.value - 1) && isBiggerByOne(smal.left, big.left)
				&& isBiggerByOne(smal.right, big.right);
	}

	public void print() {
		this.print(this.root);
	}

	private void print(TreeNode n) {
		if (n != null) {
			this.print(n.left);
			System.out.print(n.value + " ");
			this.print(n.right);
		}
	}

}	

class TreeNode {
	public final TreeNode left;
	public final TreeNode right;
	public final int value;

	//@public normal_behaviour
	//@ensures (\result).value == this.value + 1;
	//@assignable \nothing;
	public TreeNode increment() {
		TreeNode newLeft = null;
		TreeNode newRight = null;
		if (this.left != null) {
			newLeft = this.left.increment();
		}
		if (this.right != null) {
			newRight = this.right.increment();
		}
		TreeNode retVal = new TreeNode(this.value + 1, newRight, newLeft);
		return retVal;
	}

	//@assignable this.value;
	//@assignable this.left;
	//@assignable this.right;
	public TreeNode(final int val, final TreeNode left, final TreeNode right) {
		this.value = val;
		this.left = left;
		this.right = right;
	}
}

class TreeTest{
	//@public normal_behaviour
	//@ensures true;
	public static void main(String[] args) {
		IncrementTree first = new IncrementTree(
				new TreeNode(4, 
						new TreeNode(2, 
								new TreeNode(1, null, null), 
								new TreeNode(3, null, null)),
						new TreeNode(6, 
								new TreeNode(5, null, null),
								new TreeNode(7, null, null))
						)
				);
		IncrementTree second = first.increment();
		assert(IncrementTree.isBiggerByOne(first,second));
	}
	
}


