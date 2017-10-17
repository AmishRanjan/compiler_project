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



structure setCalculation = 
struct
			                             
		  fun cal_def_use_Set(map, [], insMap, f)    = map
			  | cal_def_use_Set(map, x::xs, insMap, f) = 
			                         let
			                            val map = Map.insert(map, x, f(Map.lookup(insMap, x)))
			                          in
			                            cal_defSet(map, xs, insMap, f)
     
     fun initialize(map, [], value) = map
       | initialize(map, x::xs, value) = initialize(Map.insert(map, x, value), xs, value);
 
     fun in_out_cal( (pred, succ, nodes), insMap) = 
                              let
                                 val inSet  = initialize(inSet, nodes, AtomSet.empty)
                                 val outSet = initialize(outSet, nodes, AtomSet.empty) 
                                 val useSet = cal_def_use_Set(useSet, nodes, insMap, singleNode.useSet)       
                                 val defSet = cal_def_use_Set(useSet, nodes, insMap, singleNode.defSet)
                               in                             
                                 fixedPoint(succ, nodes, inSet, outSet, useSet, defSet);

     fun in_out_Cal(succ, [], inSet, outSet, useSet, defSet) = (inSet, outSet) 
       | in_out_Cal(succ, x::xs, inSet, outSet, full_nodes, useSet, defSet) = 
                               let 
                                  val inSet     = Map.insert(inSet, x, AtomSet.union(Map.lookup(useSet, x) , 
                                                  AtomSet.difference(Map.lookup(outSet, x), Map.lookup(defSet,x)))) 
                                  val outSet    = List.foldl AtomSet.union Map.lookup inSet AtomSet.empty Map.lookup(suuc, x)
                                in
                                  in_out_Cal(succ, xs, inSet, outSet, useSet, defSet);
                                                  
		 fun fixedPoint(succ, nodes, inSet, outSet, useSet, defSet) = 
                               let 
                                  val (up_inset, up_outset) = in_out_Cal(succ, nodes, inSet, outSet, useSet, defSet)
                                in 
                                   if ( inSet = up_inset andalso outSet = up_outset) 
                                       then  (inSet, outSet)
                                   else in_out_Cal(succ, nodes, inSet, outSet, useSet, defSet);
                              
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



 
