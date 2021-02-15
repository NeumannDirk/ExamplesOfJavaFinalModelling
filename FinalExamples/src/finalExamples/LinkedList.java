package finalExamples;

public final class LinkedList {	
	public /*@nullable@*/ ListNode head = null;
    //@instance invariant (this.head != null) ==> \invariant_for(this.head); 
	
	/*@public normal_behaviour
	  ensures this.head != null; 
	  ensures this.head.next == \old(this.head);
	  ensures this.head.data == val;
	  ensures this.head.index == \old(this.getLength());   	 
	  ensures this.getLength() == \old(this.getLength())+1;
	  ensures (\forall ListNode n; n == \old(n) && n.index == \old(n.index) && n.next == \old(n.next) && n.data == \old(n.data));
	  ensures this.getAtIndex(this.head.index) == head; 
	  ensures (\old(this.head) != null) ==> (\old(this.getAtIndex(this.head.index)) == \old(this.head)); 
//	  ensures (\forall int i; i < this.head.index; \old(this.getAtIndex(i)) == this.getAtIndex(i));
	  assignable this.head;
	 */	 
	public void push(final int val) {
		this.head = new ListNode(val, this.head);
	}
	
	/*@public normal_behaviour
	   ensures this.head != null ==> (\result == (this.head.index+1));
	   ensures this.head == null <==> (\result == 0); 
	   ensures \result >= 0;
	   ensures (\forall ListNode n; n == \old(n) && n.index == \old(n.index) && n.next == \old(n.next) && n.data == \old(n.data));
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
	  ensures (\forall ListNode n;n!=this.head;n == \old(n) && n.index == \old(n.index) && n.next == \old(n.next) && n.data == \old(n.data));
	  assignable this.head;
	  
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
	   requires this.head != null;
	   requires (indexp >= 0) && (indexp <= this.head.index);	   
	   ensures (\result).index == indexp;
	   ensures (\result) == this.head.get(indexp); 
	   ensures (indexp == this.head.index) ==> \result == this.head; 
       ensures_free \result == this.head.get(indexp);
       ensures (\result) != null;
	   assignable \strictly_nothing;
	   
	   also
	   
       public exceptional_behaviour 
	   requires (this.head == null) || (indexp < 0) || (this.head.index < indexp);
	   signals_only IndexOutOfBoundsException;	 
	   assignable \nothing;
	 */
	public /*@nullable*/ListNode getAtIndex(final int indexp) {
		if((this.head == null) || (indexp < 0) || (this.head.index < indexp)){
			throw new IndexOutOfBoundsException();//this.exception;
		}
		else {
			assert(this.head != null);
			assert(indexp <= this.head.index);
			assert(indexp >= 0);		
			ListNode n = this.head.get(indexp);
			assert(n != null);
			assert(n.index == indexp);
			return n;
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
    //@instance invariant (this.next != null) ==> \invariant_for(next);
	//@accessible \inv: \nothing;  
	
	/*@public normal_behaviour
	  requires (nextp == null) || \invariant_for(nextp);
	  ensures this.next == nextp;
	  ensures this.data == data;
	  ensures true;	  
	  ensures (nextp == null) || \invariant_for(nextp);
	  ensures \invariant_for(this);
	  ensures (this.next == null) || \invariant_for(this.next);
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
       ensures at == index ==> \result == this;
       ensures 0 < at && at < index ==> \result == next.get(at);
       ensures 0 <= at && at <= index ==> \result != null;
       ensures 0 > at || at > index ==> \result == null;
       ensures \result != null ==> (\result).index == at;
       ensures_free \result == get(at);
       measured_by this.index;
       assignable \strictly_nothing;
       accessible \nothing;
     */
  final public /*@nullable*/ ListNode get(final int at) {
	  if(0 > at || at > this.index) {
		  return null;
	  }
	  else if(at == this.index) {
          return this;
      } else if(this.next != null) {
          return this.next.get(at);
      } else {
          return null;
      }
  }
}


class ListTest{
	/*@public normal_behaviour
	   ensures true;
	   ensures \result == 23;
	 */
	public static int test1() {
		LinkedList l = new LinkedList();
		
		l.push(23);
		assert(l.getLength() == 1);
		assert(l.head.index == 0);
		assert(l.getAtIndex(0) == l.head);
		assert(l.getAtIndex(0).data == 23);
		
		l.push(42);
		assert(l.getLength() == 2);
		assert(l.head.index == 1);
		assert(l.getAtIndex(1) == l.head);
		assert(l.getAtIndex(1).data == 42);
		assert(l.head.next.index == 0);
		assert(l.head.next.data == 23);
//		assert(l.getAtIndex(0).data == 23);
		
		try {
			l.pop();
			assert(l.head.index == 0);
			assert(l.head.get(0) == l.head);
			assert(l.getAtIndex(0).data == 23);
			return l.pop();
			}
		catch(Exception e) {
			throw new IndexOutOfBoundsException();
		}
	}
	/*@public normal_behaviour
	   ensures true;
	 */
	public void test2() {		
		LinkedList l = new LinkedList();
		l.push(100);
		{
			ListNode n = l.getAtIndex(0);
			if (n != null) {
				assert (n.data == 100);
			}
		}
		l.push(200);
		{
			ListNode n = l.getAtIndex(0);
			if (n != null) {
//				assert (n.data == 100);
			}
		}
	}	
}