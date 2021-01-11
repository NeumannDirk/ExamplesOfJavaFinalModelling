package finalExamples;

public class LinkedList {
	//@public invariant this.elemNumber >= 0;
	
	private /*@nullable spec_public@*/ ListNode head = null;
	private /*@nullable spec_public@*/ ListNode current = null;
	// 0 = last position
	private /*@spec_public@*/ int elemNumber = 0;	

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
		this.head = new ListNode(val, this.head, this.elemNumber++);
	}
	
	/*@public normal_behaviour
	   ensures ((this.head == null)&&(\result == 0))||((this.head != null)&&(\result ==(this.head.index+1)));
	   assignable \strictly_nothing;
	 */
	public int getLength() {		
		if(this.head == null) {
			return 0;
		}
		else {
			return this.head.index + 1;
		}
	}

	/*@public normal_behaviour
	  requires this.head != null;
	  ensures \old(this.head.next) == this.head;
	  ensures \old(this.head.next.data) == this.head.data;
	  ensures \old(this.head.next.next) == this.head.next;
	  ensures \old(this.head.next.index) == this.head.index;
	  ensures this.elemNumber == \old(this.elemNumber)-1;
	  ensures \result == \old(this.head.data);
	  
	  also
	  
	  public exceptional_behavior 
	  requires this.head == null;
	  signals_only IndexOutOfBoundsException;
	 */
	public int pop() {
		if(this.head != null) {
			int retVal = this.head.data;
			this.head = this.head.next;
			this.elemNumber--;
			return retVal;			
		}
		throw new IndexOutOfBoundsException();
	}

	/*@public normal_behaviour
	   assignable \strictly_nothing;
	   assignable this.current;
	 */
	public void processAll() {
		for (this.current = this.head; this.current != null; this.current = this.current.next) {
			System.out.println(this.current.index + ": " + this.current.data);
		}		
	}

	/*@public normal_behaviour
	   requires -1 < index && index < this.getLength();	     
	   assignable \strictly_nothing;
	   
	   also
	   
	   public exceptional_behavior
	   requires index < 0 && this.getLength() <= index;
	   signals_only IndexOutOfBoundsException;
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

class ListNode {
	final public int data;
	final public ListNode next;
	final public int index;

	//@assignable this.data;
	//@assignable this.next;
	//@assignable this.index;
	ListNode(final int data, final ListNode next, final int index) {
		this.data = data;
		this.next = next;
		this.index = index;
	}
}

class ListTest{
	//@public normal_behaviour
	//@ensures true;
	public static void main(String[] args) {
		LinkedList ll = new LinkedList();
		ll.push(23);
		ll.push(42);
		ll.pop();
		assert(ll.pop()==23);
	}
}
