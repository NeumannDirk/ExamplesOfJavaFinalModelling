package finalExamples;

public class LinkedList {	
		
	private /*@nullable spec_public@*/ ListNode head = null;

	//@instance invariant this.getLength() > -1; 

	/*@public normal_behaviour
	  ensures this.head.next == \old(this.head);
	  ensures this.head.data == val;
	  ensures (\forall int i; -1 < i && i < this.getLength(); this.getAtIndex(i) == \old(this.getAtIndex(i)));
	  ensures this.getAtIndex(this.getLength()-1) == val;
	  
	  ensures this.getLength() == \old(this.getLength())+1;
	  ensures this.head.index == \old(this.getLength()); 
	  assignable this.head;
	 */	 
	public void push(final int val) {
		this.head = new ListNode(val, this.head);
	}
	
	/*@public normal_behaviour
	   ensures \invariant_for(this);
	   ensures ((this.head == null) ==> (\result == 0));
	   ensures ((this.head != null) ==> (\result ==(this.head.index+1)));
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
	  ensures this.getLength() == \old(this.getLength())-1;
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
			return retVal;			
		}
		throw new IndexOutOfBoundsException();
	}

	/*@public normal_behaviour
	   assignable \strictly_nothing;
	 */
	public void processAll() {
		for (ListNode current = this.head; current != null; current = current.next) {
			System.out.println(current.index + ": " + current.data);
		}		
	}

	/*@public normal_behaviour
	   requires -1 < index && index < this.getLength();	    
	   ensures \invariant_for(this);	   
	   assignable \strictly_nothing;
	   
	   also
	   
	   public exceptional_behavior
	   requires index < 0 && this.getLength() <= index;
	   signals_only IndexOutOfBoundsException;
	 */
	public int getAtIndex(final int index) {
		if (index < 0 || this.getLength() <= index) {
			throw new IndexOutOfBoundsException("Given index(" + index + "is out of list bounds.");
		} else {
			ListNode current;
			for (current = this.head; current.index != index; current = current.next);
			return current.data;
		}
	}
}

class ListNode {
	final public int data;
	final public /*@nullable@*/ ListNode next;
	final public int index;

	//@instance invariant (this.index > -1);
	//@instance invariant (this.next != null) ==> (this.index == this.next.index + 1);
	//@instance invariant (this.next == null) ==> (this.index == 0);

	  
	/*@public normal_behaviour
	  requires (nextp == null) || (nextp.index > -1);
	  ensures ((nextp != null) && (this.index == nextp.index + 1)) || ((nextp == null) && (this.index == 0));
	  ensures \invariant_for(this);
	  ensures true;
	  assignable this.data, this.next, this.index;
	 */
	public ListNode(final int data, final ListNode nextp) {
		this.data = data;
		this.next = nextp;
		if(nextp == null) {
			this.index = 0;
		}
		else {
			this.index = nextp.index+1;
		}		
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