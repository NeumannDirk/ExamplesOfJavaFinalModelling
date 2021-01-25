package finalExamples;

public final class LinkedList {	
		
	private /*@nullable spec_public@*/ ListNode head = null;

//	//@instance invariant this.getLength() > -1; 

	/*@public normal_behaviour
	  requires (this.head == null) || (this.head.index > -1);	  
	  ensures this.head.next == \old(this.head);
	  ensures this.head.data == val;
	  ensures this.head.index > -1;
	  ensures this.head.index == \old(this.getLength()); 
//	  ensures (\forall int i; -1 < i && i < this.getLength(); this.getAtIndex(i) == \old(this.getAtIndex(i)));
//	  ensures this.getAtIndex(this.getLength()-1) == val;
//	  ensures this.getLength() == \old(this.getLength())+1;
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
//	  ensures this.getLength() == \old(this.getLength())-1;
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
	   requires -1 < indexp && indexp < this.getLength();
	   requires (\exists ListNode n; n.index == indexp);
	   requires this.head != null;
	   ensures \result == indexp;	
	   
	   also
	   
	   public exceptional_behavior
	   requires indexp < 0 && this.getLength() <= indexp;
	   signals_only IndexOutOfBoundsException;
	 */
	public int getAtIndex(final int indexp) {
		if (indexp < 0 || this.getLength() <= indexp) {
			throw new IndexOutOfBoundsException("Given index(" + indexp + "is out of list bounds.");
		} else {
			ListNode current = this.head;
			for (; current.index != indexp; current = current.next);
			return indexp;
////			assert(current.index == indexp);
//			return current.index;
		}
	}
}

final class ListNode {
	final public int data;
	final public /*@nullable@*/ ListNode next;
	final public int index;

	//@instance invariant (this.index > -1);
	//@instance invariant (this.next != null) ==> (this.index == this.next.index + 1);
	//@instance invariant (this.next == null) <==> (this.index == 0);

	  
	/*@public normal_behaviour
	  requires (nextp == null) || (nextp.index > -1);
//	  ensures ((nextp != null) && (this.index == nextp.index + 1)) || ((nextp == null) && (this.index == 0));
//	  ensures \invariant_for(this);
	  ensures this.next == nextp;
	  ensures this.data == data;
	  ensures true;
	  assignable this.data, this.next, this.index;
	 */
	public ListNode(final int data, final /*@nullable@*/ListNode nextp) {
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
	/*@public normal_behaviour
	   ensures true;
	   ensures \result == 23;
	   
	   also
	   
	   public exceptional_behavior
	   signals_only IndexOutOfBoundsException;
	 */
	public static int test() {
		LinkedList ll = new LinkedList();
		ll.push(23);	
		ll.push(23);
		try {
			ll.pop();
//			assert(ll.pop() == 23);
//			return 23;
			return ll.pop();
			}
		catch(Exception e) {
			throw new IndexOutOfBoundsException();
		}
	}
}