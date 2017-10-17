(* structure for key of the map *)
structure IntKey =
struct
    type ord_key = int
    fun compare(x, y) = Int.compare(x, y)
end; 

structure Map = RedBlackMapFn(IntKey);
structure Set = RedBlackSetFn(IntKey);

val pred = Map.empty;
val succ = Map.empty;

fun is_present(x, [])    = false
  | is_present(x, y::xs) = if(x = y) then true
                           else is_present(x, xs);
                           
fun remove(x, y) = Set.listItems(Set.difference(Set.fromList(x), Set.fromList(y)));
fun concat(x::xs, w, y) = if(is_present(x, y) =true) then w@y
                          else (x::xs)@w@y;

fun pre(map1, map2, [node1], [node]) = if(node = node1) then []
                                       else if(List.length(Map.lookup(map1, node1)) = 1 
                                               andalso List.length(Map.lookup(map2, node1)) = 1) then
                                               pre(map1, map2, Map.lookup(map1, node1) , [node])@[node1]
                                       else if(List.length(Map.lookup(map2, node1)) = 1) then
                                                [node1]        
                                       else []

fun suc(map1, map2, [node1], [node]) = if(node = node1) then []
                                       else if(List.length(Map.lookup(map1, node1)) = 1 
                                               andalso List.length(Map.lookup(map2, node1)) = 1) then
                                               node1::suc(map1, map2, Map.lookup(map2, node1) , [node])
                                       else if(List.length(Map.lookup(map1, node1)) = 1) then
                                                [node1]        
                                       else []
                                       
fun basicBlock(map1, map2, [node]) = if(List.length(Map.lookup(map1, node)) = 1 
                                      andalso List.length(Map.lookup(map2, node)) = 1) 
                                     then
                                       concat(pre(map1, map2, Map.lookup(map1, node),[node]),[node]
                                       ,suc(map1, map2, Map.lookup(map2, node), [node]))
                                     else if(List.length(Map.lookup(map1, node)) = 1) then 
                                          pre(map1, map2, Map.lookup(map1, node),[node])@[node]
                                     else if(List.length(Map.lookup(map2, node)) = 1) then 
                                          [node]@suc(map1, map2, Map.lookup(map2, node), [node])
                                     else [node]
                                     

                                       
(*fun basicBlock(map1, map2, [], d, [node1]) = [] 
  | basicBlock(map1, map2, [node], d, [node1]) = 
                 if(is_present(node1, Map.lookup(map1, node)) = true) then [node]
								 else if(List.length(Map.lookup(map2, node)) > 1 andalso d = 0) 
                 then basicBlock(map2, map1, Map.lookup(map1, node1), 1, [node1])
								 else if(List.length(Map.lookup(map1, node)) <> 1 andalso d = 0) 
                 then node::basicBlock(map2, map1, Map.lookup(map1, node1), 1, [node1])
                 else if(List.length(Map.lookup(map2, node)) > 1 andalso d = 1) 
				         then []
                 else if(List.length(Map.lookup(map1, node)) <> 1 andalso d = 1) 
				         then [node]
		             else node::basicBlock(map1, map2, Map.lookup(map1, node), d, [node1]);*)
		            		               
fun unionAll([], inst_, inst)    = []
  | unionAll(x::xs, inst_, inst) = Map.lookup(inst, x)::unionAll(xs, inst_, inst);
  
fun allBlock(inst, pred, succ, [], succ_, pred_, inst_, nodes_) = (succ_, pred_, inst_, nodes_)   
  | allBlock(inst, pred, succ, x::xs, succ_, pred_, inst_, nodes_) = 
                 let
                    val up_nodes = basicBlock(pred, succ, [x])
                    val nodes    = remove(xs, up_nodes)
                    val succ_    = Map.insert(succ_, x, Map.lookup(succ, List.last(up_nodes)))
                    val pred_    = Map.insert(pred_, x, Map.lookup(pred, List.hd(up_nodes)))
                    val inst_    = Map.insert(inst_, x, unionAll(up_nodes, inst_, inst))
                    val nodes_   = nodes_@[x] 
                 in  allBlock(inst, pred, succ, nodes, succ_, pred_, inst_, nodes_) 
                 end;

fun toAtom (lhs, rhs)   = (Atom.atom(lhs), AtomSet.fromList(List.map (Atom.atom) rhs)) 
fun lToAtom (x)         = List.map (toAtom) x

fun toString(x)         = List.map (Atom.toString) (AtomSet.listItems(x))

val instMap = Map.empty;
val instMap = Map.insert(instMap, 1, toAtom("a", []));
val instMap = Map.insert(instMap, 2, toAtom("b", ["a"]));
val instMap = Map.insert(instMap, 3, toAtom("c", ["b", "c"]));
val instMap = Map.insert(instMap, 4, toAtom("a", ["b"]));
val instMap = Map.insert(instMap, 5, toAtom("", ["a"]));
val instMap = Map.insert(instMap, 6, toAtom("", ["c"]));
val pred = Map.empty;
val pred = Map.insert(pred, 2, [1, 5]);
val pred = Map.insert(pred, 1, []);
val pred = Map.insert(pred, 3, [2]);
val pred = Map.insert(pred, 4, [3]);
val pred = Map.insert(pred, 5, [4]);
val pred = Map.insert(pred, 6, [5]) 
val succ = Map.empty;
val succ = Map.insert(succ, 1, [2]);
val succ = Map.insert(succ, 2, [3]);
val succ = Map.insert(succ, 3, [4]);
val succ = Map.insert(succ, 4, [5]);
val succ = Map.insert(succ, 5, [6,2]);
val succ = Map.insert(succ, 6, []) 
val nodes = [1,2,3,4,5,6];
basicBlock(pred, succ, [1]);
basicBlock(pred, succ, [2]);
val graph = (instMap, pred, succ, nodes);
val  (succ_, pred_, inst_, nodes_) = allBlock( instMap, pred, succ, nodes, Map.empty, Map.empty, Map.empty, []);
nodes_;
Map.lookup(succ_, 1 );
Map.lookup(pred_, 1);
Map.lookup(succ_, 2 );
Map.lookup(pred_, 2);
Map.lookup(succ_, 6 );
Map.lookup(pred_, 6);


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
                               
