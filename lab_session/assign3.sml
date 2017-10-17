(* int key for map of succesor, predecessor, in set, out set *)
structure IntKey =
struct
    type ord_key = int
    fun compare(x, y) = Int.compare(x, y)
end;


(* map for in set, out set, def set and use set  *) 
structure Map = RedBlackMapFn(IntKey);
val inSet = Map.empty;
val outSet = Map.empty;
val useSet = Map.empty;
val defSet = Map.empty;


 
(* signature for bot single node and basic block *)
signature Instruction =
sig
    type inst
    val useSet : inst -> AtomSet.set (* Get the use set of an instruction *)
    val defSet : inst -> AtomSet.set (* Get the def set of an instruction *)
end;


(*structure for holding single node *)
structure singleNode : Instruction =
struct
      type inst                    = Atom.atom * AtomSet.set     
      fun useSet (lhs, rhs)        = rhs      
      fun defSet (lhs, rhs)        = AtomSet.singleton(lhs)
end;


(* structure for holding multiple nodes i.e. basic blocks *)
structure basicBlock : Instruction =
struct
      type inst                    = singleNode.inst list    
      fun useSet  ( [] )           = AtomSet.empty
        | useSet (x::xs)           = AtomSet.union(singleNode.useSet(x), AtomSet.difference(useSet(xs), singleNode.defSet(x)))      
      fun defSet ([])              = AtomSet.empty
        | defSet (x::xs)           = AtomSet.union(singleNode.defSet(x), defSet(xs))
end;


(* functor for calculating genset and killset of node (either single instruction or basic block) *)
functor calSet(X : Instruction) = 
struct
      type inst                 = X.inst
      fun genSet(x)             = X.useSet(x)
      fun killSet(x)            = X.defSet(x)
end;


(* structuure with all the functions required for calculating inset and outset of single node graph *)
structure setCalculation = 
struct
			                             
		  fun cal_def_use_Set(map, [], insMap, f)    = map
			  | cal_def_use_Set(map, x::xs, insMap, f) = 
			                         let
			                            val map = Map.insert(map, x, f(Map.lookup(insMap, x)))
			                          in
			                            cal_def_use_Set(map, xs, insMap, f)
			                           end;
     
     fun is_equal(set1, set2, [])    = true
       | is_equal(set1, set2, x::xs) = if(AtomSet.equal(Map.lookup(set1, x), Map.lookup(set2, x)) = false) then
                                           false
                                       else is_equal(set1, set2, xs);
     
     fun initialize(map, [], value)    = map
       | initialize(map, x::xs, value) = initialize(Map.insert(map, x, value), xs, value);
     
     fun union_succ(map, [])    = AtomSet.empty
       | union_succ(map, x::xs) = AtomSet.union(Map.lookup(map, x), union_succ(map, xs));
       
     fun in_out_Cal(succ, [], inSet, outSet, useSet, defSet) = (inSet, outSet) 
       | in_out_Cal(succ, x::xs, inSet, outSet, useSet, defSet) = 
                               let 
                                  val inSet     = Map.insert(inSet, x, AtomSet.union(Map.lookup(useSet, x) , 
                                                  AtomSet.difference(Map.lookup(outSet, x), Map.lookup(defSet,x)))) 
                                  val outSet    = Map.insert(outSet, x, union_succ(inSet, Map.lookup(succ, x)))
                                in
                                  in_out_Cal(succ, xs, inSet, outSet, useSet, defSet)
                                 end;
                                                  
		 fun fixedPoint(succ, nodes, inSet, outSet, useSet, defSet) = 
                               let 
                                  val (up_inset, up_outset) = in_out_Cal(succ, nodes, inSet, outSet, useSet, defSet)
                                in 
                                   if ( is_equal(inSet, up_inset, nodes) = true andalso is_equal(outSet, up_outset,nodes) = true) 
                                       then  (inSet, outSet)
                                   else fixedPoint(succ, nodes, up_inset, up_outset, useSet, defSet)
                                 end;
                                 
     fun in_out_cal( insMap, pred, succ, nodes) = 
                              let
                                 val inSet  = initialize(inSet, nodes, AtomSet.empty)
                                 val outSet = initialize(outSet, nodes, AtomSet.empty) 
                                 val useSet = cal_def_use_Set(useSet, nodes, insMap, singleNode.useSet)       
                                 val defSet = cal_def_use_Set(useSet, nodes, insMap, singleNode.defSet)
                               in                             
                                 fixedPoint(succ, nodes, inSet, outSet, useSet, defSet)
                                end;
                                
     fun in_out_cal2( insMap, pred, succ, nodes) = 
                        let
                           val inSet  = initialize(inSet, nodes, AtomSet.empty)
                           val outSet = initialize(outSet, nodes, AtomSet.empty) 
                           val useSet = cal_def_use_Set(useSet, nodes, insMap, basicBlock.useSet)       
                           val defSet = cal_def_use_Set(useSet, nodes, insMap, basicBlock.defSet)
                         in                             
                           fixedPoint(succ, nodes, inSet, outSet, useSet, defSet)
                          end;           
                                             
end;


(* the basic block part *)                             
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
                                     
		            		               
fun unionAll([], inst_, inst)    = []
  | unionAll(x::xs, inst_, inst) = Map.lookup(inst, x)::unionAll(xs, inst_, inst);
  
fun allBlock(inst, pred, succ, [], succ_, pred_, inst_, nodes_) = (inst_, pred_, succ_,  nodes_)   
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
                             










(***************************************************************************************************************************)
(******************for demonstration purpose **************)
(***************************************************************************************************************************) 
fun toAtom (lhs, rhs)   = (Atom.atom(lhs), AtomSet.fromList(List.map (Atom.atom) rhs)) 
fun lToAtom (x)         = List.map (toAtom) x

fun toString(x)         = List.map (Atom.toString) (AtomSet.listItems(x))
  
structure sn = calSet(singleNode);
structure bb = calSet(basicBlock);
val a = sn.genSet(toAtom("a", ["b","c"]));
val b = bb.killSet(lToAtom([("b", ["b"]),("a",["a"])]));
val a = toString(a);
val b = toString(b); 

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
val succ = Map.insert(succ, 5, [6, 2]);
val succ = Map.insert(succ, 6, []) 
val nodes = [1,2,3,4,5,6];
val graph = (instMap, pred, succ, nodes);
val basicGraph = allBlock( instMap, pred, succ, nodes, Map.empty, Map.empty, Map.empty, []);
val (inSet, outSet) = setCalculation.in_out_cal2(basicGraph);

toString(Map.lookup(inSet, 2));
toString(Map.lookup(inSet, 1));

toString(Map.lookup(inSet, 6));

toString(Map.lookup(outSet, 1));
toString(Map.lookup(outSet, 2));

toString(Map.lookup(outSet, 6));
