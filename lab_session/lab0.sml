(* datatype definition for binary tree*)
datatype 'a Tree = Null
									| Node of 'a Tree * 'a * 'a Tree ;
								


(*function for inorder traversal in a tree*)							
fun inorder(Null) = []
	  |inorder(Node(left, key , right)) = inorder(left) @ key :: inorder(right);
	  

(*function to rotate a tree anticlock wise*)
fun  anticlock(Node(left, key , Node(left_child, right, right_child))) = 
												Node(Node(left, key, left_child), right, right_child)
		|anticlock(x) = x;
