package finalExamples;

public class LinkedList {
	//@public invariant this.elemNumber >= 0;
	
	private /*@nullable spec_public@*/ Node head = null;
	private /*@nullable spec_public@*/ Node current = null;
	// 0 = last position
	private /*@ spec_public @*/ int elemNumber = 0;

	static private /*@spec_public@*/ class Node {
		final public int data;
		final public Node next;
		final public int index;

		//@assignable this.data;
		//@assignable this.next;
		//@assignable this.index;
		Node(final int data, final Node next, final int index) {
			this.data = data;
			this.next = next;
			this.index = index;
		}
	}

	/*@public normal_behaviour
	  ensures this.elemNumber == \old(this.elemNumber) + 1;
	  ensures this.head.next == \old(this.head);
	  ensures this.head.data == val;
	  ensures this.head.index == this.elemNumber-1;
	  ensures (\forall int i; -1 < i && i < (this.elemNumber-1); this.getAtIndex(i) == \old(this.getAtIndex(i)));
	  ensures this.getAtIndex(this.elemNumber-1) == val;
	  
	  assignable this.head;
	 */	 
	public void push(final int val) {
		this.head = new Node(val, this.head, this.elemNumber++);
	}
	

	/* @ pure @ */ public int getLength() {
		return this.head.index + 1;
	}

	//@requires this.head != null;
	//@ensures this.elemNumber == \old(this.elemNumber)-1;
	public int pop() {
		if(this.head != null) {
			int retVal = this.head.data;
			this.head = this.head.next;
			this.elemNumber--;
			return retVal;			
		}
		throw new IndexOutOfBoundsException();
	}

	/* @ensures this.head == \old(this.head) &&
	 * @\forall Node n; n.next == \old(n.next) &&
	 * @\forall Node n; n.data == \old(n.data) &&
	 * @\forall Node n; n.index == \old(n.index);
	 */
	public void processAll() {
		for (this.current = this.head; this.current != null; this.current = this.current.next) {
			System.out.println(this.current.index + ": " + this.current.data);
		}
	}

	/*@public normal_behaviour
	   requires -1 < index && index < this.getLength();
	     
	   assignable \strictly_nothing;
	 */
	public int getAtIndex(final int index) {
		if (index < 0 || index > this.head.index) {
			throw new IndexOutOfBoundsException("Given index(" + index + "is out of list bounds.");
		} else {
			for (this.current = this.head; this.current.index != index; this.current = this.current.next);
			return this.current.data;
		}
	}
}

class Test{
	//@public normal_behaviour
	//@ensures true;
	public void test() {
		LinkedList ll = new LinkedList();
		ll.push(23);
		ll.push(42);
		ll.pop();
		assert(ll.pop()==23);
	}
}
