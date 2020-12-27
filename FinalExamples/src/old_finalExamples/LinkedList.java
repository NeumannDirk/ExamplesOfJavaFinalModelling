package old_finalExamples;

public class LinkedList {
	private Node head = null;
	private Node current = null;
	// 0 = last position
	private int elemNumber = 0;

	private class Node {
		final public int data;
		final public Node next;
		final public int index;

		Node(final int data, final Node next, final int index) {
			this.data = data;
			this.next = next;
			this.index = index;
		}
	}

	public void insertAtFront(final int val) {
		this.head = new Node(val, this.head, this.elemNumber++);
	}

	public int getLength() {
		return this.head.index + 1;
	}

	public int pop() {
		int retVal = this.head.data;
		this.head = this.head.next;
		this.elemNumber--;
		return retVal;
	}

	public void processAll() {
		for (this.current = this.head; this.current != null; this.current = this.current.next) {
			System.out.println(this.current.index + ": " + this.current.data);
		}
	}

	public int getAtIndex(final int index) {
		if (index < 0 || index > this.head.index) {
			throw new IndexOutOfBoundsException("Given index(" + index + "is out of list bounds.");
		} else {
			for (this.current = this.head; this.current.index != index; this.current = this.current.next)
				;
			return this.current.data;
		}
	}
}
