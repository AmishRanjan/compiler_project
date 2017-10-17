(* structure for key of the map *)
structure IntKey =
struct
    type ord_key = int
    fun compare(x, y) = Int.compare(x, y)
end; 

structure MapAdj_List = RedBlackMapFn(IntKey);

structure SetNode = RedBlackSetFn(IntKey)

val pred = MapAdj_List.empty;
val succ = MapAdj_List.empty;

fun insert(map, key, value) =  MapAdj_List.insert(map, key, SetNode.add(MapAdj_List.lookup(map, key), value))

fun newNode(pred, succ, node) = (MapAdj_List.insert(pred, node, SetNode.empty),
				 MapAdj_List.insert(succ, node, SetNode.empty))
				 
fun addEdge(pred, succ,node1, node2) = (insert(pred,node2,node1), insert(succ, node1, node2));

val (pred, succ) = newNode(pred, succ, 1);
val (pred, succ) = newNode(pred, succ, 2);
val (pred, succ) = newNode(pred, succ, 3);
val node = [1,2,3];
val (pred, succ) = addEdge(pred, succ, 1, 2);
val (pred, succ) = addEdge(pred, succ, 2, 3);


fun basicBlock(map, [], d, [node1]) = [] 
  | basicBlock(map, [node], d, [node1]) = if(SetNode.member(MapAdj_List.lookup(map, node), node1) = true) then [node]
										  else if(SetNode.numItems(MapAdj_List.lookup(succ, node)) > 1 andalso d = 0) 
                                          then basicBlock(succ, SetNode.listItems(MapAdj_List.lookup(succ, node1)),1, [node1])
										  else if(SetNode.numItems(MapAdj_List.lookup(map, node)) <> 1 andalso d = 0) 
                                          then node::basicBlock(succ, SetNode.listItems(MapAdj_List.lookup(succ, node1)),1, [node1])
                           else if(SetNode.numItems(MapAdj_List.lookup(pred, node)) > 1 andalso d = 1) 
				           		   		    then []
                                else if(SetNode.numItems(MapAdj_List.lookup(map, node)) <> 1 andalso d = 1) 
				           		   		          then [node]
		            		                 else node::basicBlock(map,SetNode.listItems(MapAdj_List.lookup(map, node)),d,[node1]);
		            		               
val blocks = MapAdj_List.empty;

fun makeSet(set,[]) = set
  | makeSet(set,x::xs) = SetNode.add(makeSet(set,xs), x);
  
fun allBlock(map, []) = map  
  | allBlock(map, x::xs) = MapAdj_List.insert(allBlock(map, xs), x, makeSet(SetNode.empty,basicBlock(pred,[x],0,[x])));

val blocks = allBlock(blocks, node);

SetNode.listItems(MapAdj_List.lookup(blocks, 2));
SetNode.listItems(MapAdj_List.lookup(blocks, 3));
SetNode.listItems(MapAdj_List.lookup(blocks, 1));



(*fun pBasicBlock([preNode],[node]) = if(SetNode.member(MapAdj_List.lookup(pred, preNode), node) = true) then [preNode]
								    else if(SetNode.numItems(MapAdj_List.lookup(succ, preNode)) > 1) then []
								         else if(SetNode.numItems(MapAdj_List.lookup(pred, preNode)) <> 1) then [preNode]
										   	  else pBasicBlock(SetNode.listItems(MapAdj_List.lookup(pred, preNode)),[node])@[preNode];
											
fun sBasicBlock([sucNode],[node]) = if(SetNode.member(MapAdj_List.lookup(succ, sucNode), node) = true) then [sucNode]
								    else if(SetNode.numItems(MapAdj_List.lookup(pred, sucNode)) > 1) then []
								    else if(SetNode.numItems(MapAdj_List.lookup(succ, sucNode)) <> 1) then [sucNode]
					                     else node::sBasicBlock(SetNode.listItems(MapAdj_List.lookup(succ, sucNode)),[node]);

fun basicBlock([node]) = if(SetNode.numItems(MapAdj_List.lookup(pred, node)) <> 1 
                          andalso 
                          SetNode.numItems(MapAdj_List.lookup(succ, node)) <> 1) then [node]
                        else if( SetNode.numItems(MapAdj_List.lookup(pred, node)) <> 1) 
                               then node::sBasicBlock(SetNode.listItems(MapAdj_List.lookup(succ, node)),[node])
                             else if( SetNode.numItems(MapAdj_List.lookup(succ, node)) <> 1) 
                                     then pBasicBlock(SetNode.listItems(MapAdj_List.lookup(pred, node)), [node])@[node]
                                  else pBasicBlock(SetNode.listItems(MapAdj_List.lookup(pred, node)), [node])
                                       @[node]@
                                       sBasicBlock(SetNode.listItems(MapAdj_List.lookup(succ, node)),[node]); *)
                               
