package finalExamples;

public final class LinkedList {	
		
	private /*@nullable spec_public@*/ ListNode head = null;

//	//@instance invariant this.getLength() > -1; 

	/*@public normal_behaviour
	  requires (this.head == null) || (this.head.index > -1);	 
	  ensures this.head != null; 
	  ensures this.head.next == \old(this.head);
	  ensures this.head.data == val;
	  ensures this.head.index > -1;
	  ensures this.head.index == \old(this.getLength()); 
//	  ensures (\forall int i; -1 < i && i < this.getLength(); this.getAtIndex(i) == \old(this.getAtIndex(i)));
//	  ensures this.getAtIndex(this.getLength()-1) == val;
	  ensures this.getLength() == \old(this.getLength())+1;	   
	  assignable this.head;
	 */	 
	public void push(final int val) {
		this.head = new ListNode(val, this.head);
	}
	
	/*@public normal_behaviour
	   requires this.head != null;
	   requires \invariant_for(this.head);
	   ensures \result > 0;
	   ensures \result == (this.head.index+1);
	   assignable \strictly_nothing;
	   
	   also
	   
	   public normal_behaviour
	   requires this.head == null;
	   ensures ((this.head == null) <==> (\result == 0));
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

//	/*@public normal_behaviour
//	   requires -1 < indexp && indexp < this.getLength();
//	   requires (\exists ListNode n; n.index == indexp);
//	   requires this.head != null;
//	   requires \invariant_for(this.head);
//	   ensures (\result).index == indexp;
//	   
//	   also
//	   
//	   public exceptional_behavior
//	   requires indexp < 0 && this.getLength() <= indexp;
//	   signals_only IndexOutOfBoundsException;
//	 */
	public int getAtIndex(final int indexp) {
		if (indexp < 0 || this.getLength() <= indexp) {
			throw new IndexOutOfBoundsException("Given index(" + indexp + "is out of list bounds.");
		} else {
			ListNode x = this.getNode(indexp, this.head);
			if (x != null) {
				return x.data;
			}
			else {
				//Dieser Fall kann nicht auftreten, aber das kann momentan noch nicht bewiesen werden.
				throw new IndexOutOfBoundsException("Given index(" + indexp + "is out of list bounds."); 
			}
		}
	}	
	
	/*@public normal_behaviour
	   requires current != null;
	   requires (at >= 0 && at <= current.index);
	   requires \invariant_for(current);
	   requires \invariant_for(this.head);
//	   ensures (at >= 0 && at < this.getLength());
	   ensures ((\result).index == at);
       ensures true;         
	   assignable \strictly_nothing;
	   accessible \nothing;
	   
	   also
	   
	   public normal_behaviour
	   requires (at < 0 || at > current.index);
	   ensures \result == null;
	   assignable \strictly_nothing;
	   accessible \nothing;
	 */
	public /*@nullable*/ ListNode getNode(final int at, ListNode current) {
		if(at < 0 || at > current.index) {
			return null;
		}
		assert(current != null);		
		/*@maintaining (current != null);
		   maintaining \invariant_for(current);
		   maintaining (current.next != null || current.index == 0);
		   maintaining ((current.next != null) ==> (current.index == current.next.index + 1)); 
		   decreasing current.index;
		 */
		while((current.next != null) && (current.index!=at)) {
			//@assert(current.index == current.next.index + 1);
			//@assert(current.next != null);	
			current = current.next;
			//@assert(current != null);
		}
		assert(current != null);
		if(current.index==at) {
			return current; 
		}		
		assert(current.next == null);
		if(current.next == null && at == 0) {
			return current;//Hier kann ich nicht beweisen, dass die Invariante von current gilt.			
		}
		else {
			return null;
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
	/*@public normal_behaviour
	   requires (at < this.index && this.next != null);
	   ensures (at < this.index);  
	   accessible \nothing;     
	   assignable \strictly_nothing;
	   
	   also
	   
	   public normal_behaviour
	   requires (at == this.index);	     
	   ensures ((\result).index == at);
	   assignable \strictly_nothing;
	   accessible \nothing;
	   
	   also
	   
	   public normal_behaviour
	   requires (at < 0 || at > this.index || (at < this.index && this.next == null));
	   ensures \result == null;
	   ensures (at < 0 || at > this.index);
	   assignable \strictly_nothing;
	   accessible \nothing;
	 */
	final public /*@nullable*/ListNode get(final int at) {
		try {		
			if(at < 0 || at > this.index) {
				return null;
			}
			else if (at == this.index){
				return this;
			}
			else {
				if(this.next == null) {
					return null;
				}
				assert(at < this.index);
				assert(at <= this.next.index);
				assert(this.next != null);
				//@assert(\invariant_for(this.next));	 
				return this.next.get(at);	
			}		
		}
		catch (Throwable e) {
			return null;
		}
	}
}


class ListTest{
	/*@public normal_behaviour
	   ensures true;
	   ensures \result == 23;
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