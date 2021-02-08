package old_finalExamples;
public final class IncrementTree {

	private final /*@nullable spec_public@*/ TreeNode root;

	/*@public normal_behaviour
	   ensures this.root == root;
	 */
	public IncrementTree(/*@nullable@*/TreeNode root) {
		this.root = root;
	}

	/*@public normal_behaviour
	   ensures (this.root == null) <==> (\result == null);
	   ensures (this.root != null) <==> isBiggerByOne(this,\result);
 	   assignable \nothing;	    
	 */
	public IncrementTree increment() {
		if (this.root != null) {
			IncrementTree it = new IncrementTree(this.root.increment());
			return it;
		} else {
			return null;
		}
	}

	/*@public normal_behaviour
	   ensures (small == null && big == null) ==> (\result == true);
	   ensures (small == null && big != null) ==> (\result == false);
	   ensures (small != null && big == null) ==> (\result == false);
	   ensures (small != null && big != null) ==> isBiggerByOne(small, big);
	   assignable \strictly_nothing;
	 */
	public static boolean isBiggerByOne(/*@nullable@*/IncrementTree small, /*@nullable@*/IncrementTree big) {
		if(small == null) {
			if(big == null) {
				return true;
			}
			else {
				return false;
			}
		}
		else {
			if(big.root == null) {
				return false;
			}
			else {
				return isBiggerByOne(small.root, big.root);
			}
		}
	}
	

	/*@public normal_behaviour
	   ensures (small == null && big == null) ==> (\result == true);
	   ensures (small == null && big != null) ==> (\result == false);
	   ensures (small != null && big == null) ==> (\result == false);
	   ensures (small != null && big != null) ==> isBiggerByOne(small, big);
	   assignable \strictly_nothing;
	 */
	public static boolean TreeBiggerByOne(/*@nullable@*/IncrementTree small, /*@nullable@*/IncrementTree big) {
//		Stack<TreeNode> s = new Stack<TreeNode>();
		while (true) {
			break;
		}
		return true;
	}

	/*@public normal_behaviour
	   ensures (small == null && big == null) ==> (\result == true);
	   ensures (small == null && big != null) ==> (\result == false);
	   ensures (small != null && big == null) ==> (\result == false);	   
	   ensures (small != null && big != null) ==> (
	   		((small.value != (big.value - 1)) ==> (\result == false)) &&
	   		((small.value == (big.value - 1)) ==> (isBiggerByOne(small.left, big.left) && isBiggerByOne(small.right, big.right)))
	   );	          
       ensures !isBiggerByOne(small.left, big.left) ==> (\result == false);
       ensures !isBiggerByOne(small.right, big.right) ==> (\result == false);       
	   assignable \strictly_nothing;
	 */
	public static boolean isBiggerByOne(/*@nullable@*/TreeNode small, /*@nullable@*/TreeNode big) {
		if(small == null) {
			if(big == null) {
				return true;
			}
			else {
				return false;				
			}
		}
		else {
			if(big == null) {
				return false;
			}
			else {				
				return small.value == (big.value - 1) && isBiggerByOne(small.left, big.left)
						&& isBiggerByOne(small.right, big.right);				
			}
		}
	}
}

final class TreeNode {
	public final /*@nullable@*/ TreeNode left;
	public final /*@nullable@*/ TreeNode right;
	public final int value;

	//@instance invariant ((this.left != null) ==> (this.left.value == this.value));
	//@instance invariant ((this.right != null) ==> (this.right.value == this.value));

	/*@public normal_behaviour
	   ensures (\result).value == this.value + 1;
	   ensures IncrementTree.isBiggerByOne(this.left, (\result).left);
	   ensures IncrementTree.isBiggerByOne(this.right, (\result).right);
	   assignable \nothing;
	 */
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

	/*@public normal_behaviour
	   requires ((left == null) || (val == left.value));
	   requires ((right == null) || (val == right.value));
	   assignable this.value;
	   assignable this.left;
	   assignable this.right; 
	 */
	public TreeNode(final int val, final /*@nullable@*/ TreeNode left, final /*@nullable@*/ TreeNode right) {
		this.value = val;
		this.left = left;
		this.right = right;
	}
}

class TreeTest {
	/*@public normal_behaviour
	   ensures true;
	   ensures (\result).root.left.value == 2;
	   ensures (\result).root.value == 2;
	   ensures (\result).root.right.value == 2;
	 */
	public static IncrementTree test() {
		IncrementTree first = new IncrementTree(new TreeNode(1, new TreeNode(1, null, null), new TreeNode(1, null, null)));
		IncrementTree second = first.increment();
		assert (IncrementTree.isBiggerByOne(first, second));
		return second;
	}

}

final class TreeNodeTuple{
	public final TreeNode small;
	public final TreeNode big;
	
	public TreeNodeTuple(final /*@nullable*/TreeNode s,final /*@nullable*/TreeNode b) {
		this.small = s;
		this.big = b;
	}
	
}
