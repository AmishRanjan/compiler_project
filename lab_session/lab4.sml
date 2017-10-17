type Terminal = string;
type NonTerminal = string;

datatype Variable = T of Terminal
							    | NT of NonTerminal

datatype Rule = Transition of NonTerminal * Variable list; 
type Grammar = Rule list;

structure StringKey =
struct
    type ord_key = Variable
    fun compare(NT x, NT y) = String.compare(x, y) 
    	 | compare(T x, NT y) = String.compare(x, y)
    	 | compare(T x, T y) = String.compare(x, y)
    	 | compare(NT x, T y) = String.compare(x, y)
end;

structure TableKey =
struct
    type ord_key = string list
    fun compare([],[]) = EQUAL
      | compare([],_) = LESS
      | compare(_,[]) = GREATER 
    	| compare(x::xs, y::ys)	= if(String.compare(x,y) = GREATER) then GREATER
    															else if(String.compare(x,y) = LESS) then LESS
    															else compare(xs,ys)										    		
end;
 
val rule1 = Transition( "A" , [T"a"]);
val rule2= Transition( "A" , [NT"B"]);
val rule3 = Transition( "B" , [T"c"]);
val rule4 = Transition( "B" , [T"E"]);
val rule5 = Transition( "C" , [T"d"]);
val rule6 = Transition( "C" , [NT"A",NT"B",NT"C"]);

val gr1 = [rule1,rule2,rule3,rule4,rule5,rule6];
val emptystring = []:string list;

structure Mapfst = RedBlackMapFn(StringKey);
structure Mapll = RedBlackMapFn(TableKey);

(*grammar definition ends *)
fun present(x,[]) = false
	| present(x, y::ys) = if(x = y) then true
												else  present(x,ys)
													
fun equate([],[]) = []
	| equate([],y) = y
	| equate(x,[]) = x
	| equate(x::xs,y::ys) = if(x = y) then x::equate(xs,ys)
													else if(present(x,ys) = true) then  equate(xs,y::ys)
														    else x::equate(xs,y::ys)	
fun nonTer([]) = [] 
  | nonTer(Transition(x,y)::Transition(x1,y1)::xs) = if(x1 = x) then nonTer(Transition(x1,y1)::xs)
  																										 else NT x::nonTer(Transition(x1,y1)::xs)
  | nonTer(Transition(x,y)::xs) =  NT x::nonTer(xs);
val nonTerminal = nonTer(gr1);  

fun ter([]) = [] 
  | ter(Transition(x,[])::xs) = ter(xs)
	|	ter(Transition(x,y::ys)::xs) = 
	           if(present(y , nonTerminal) = false andalso y <> T "E" ) then equate([y] , ter(Transition(x,ys)::xs))
						 else ter(Transition(x,ys)::xs)

fun length([]) =0
	| length(x::xs) = length(xs) + 1;
val terminal = ter(gr1);
val l = length(nonTerminal);
fun loop(func, map, grm, symbol, l) = if(l = 0) then map
											                else loop(func, func(grm, symbol, grm, map), grm, symbol, l-1);

fun initiate([], map) = map
	|	initiate((T x)::xs,map) = Mapfst.insert(initiate(xs,map),T x, [x]) 
	|	initiate( x::xs,map) = Mapfst.insert(initiate(xs,map), x, emptystring);
	
fun mapInsert(mapName, key_, val_) = Mapfst.insert(mapName, key_, equate(val_,Mapfst.lookup(mapName, key_))) 
fun mapInsertl(mapName, key_, val_) = Mapll.insert(mapName, key_, val_@Mapll.lookup(mapName, key_));

(* defining a map from variable to boolean for nullable *)
structure MapNlbl = RedBlackMapFn(StringKey);
val nlbl= MapNlbl.empty;

fun initiateNlbl([],nlbl) = nlbl 
	|	initiateNlbl( x::xs,nlbl) = MapNlbl.insert(initiateNlbl(xs,nlbl), x, false);
	
val nlbl = initiateNlbl(nonTerminal,nlbl);
val nlbl = initiateNlbl(terminal,nlbl);
val nlbl = MapNlbl.insert(nlbl, T"E", true);

fun null([],nlbl) = true
	| null(y::ys,nlbl) = (MapNlbl.lookup(nlbl,y) andalso null(ys,nlbl));
	
fun nullable(_,[],grmr,nlbl) = nlbl
	| nullable([],p::ps,grmr,nlbl) = nullable(grmr, ps,grmr,nlbl)   
  | nullable(Transition(x,y)::xs, p::ps, grmr,nlbl) =
      if(p = NT x andalso null(y,nlbl) = true ) then
				MapNlbl.insert(nullable(grmr, ps, grmr,nlbl), p, true)
			else
				nullable(xs, p::ps, grmr,nlbl) ;
val nlbl = loop(nullable, nlbl, gr1, nonTerminal, l);

(* defining a map from variable to terminal for first *)
val first= Mapfst.empty;
val first = Mapfst.insert(first, T"E", emptystring);

val first = initiate(terminal,first);	
val first = initiate(nonTerminal,first);
													
fun firstLook([],first) = []
	| firstLook(y::ys,first) = if(MapNlbl.lookup(nlbl, y) = true) then
	               							 equate(Mapfst.lookup(first,y) , firstLook(ys,first))
	               						 else Mapfst.lookup(first,y);
																	 
fun calFirst(_,[],grmr,first) = first
	| calFirst([],p::ps,grmr,first) = calFirst(grmr, ps,grmr,first)   
  | calFirst(Transition(x,y)::xs, p::ps, grmr,first) =
      if(p = NT x ) then
				mapInsert(calFirst(xs, p::ps, grmr,first), p, firstLook(y,first))
			else
				calFirst(xs, p::ps, grmr,first) ;
val first = loop(calFirst, first, gr1, nonTerminal, l);	

(* defining map from variable to terminal for follow setr calculation *)
val follow= Mapfst.empty;
val follow = initiate(nonTerminal,follow);
																	 
fun calFlw(_,[],grmr,follow) = follow
	| calFlw([],p::ps,grmr,follow) = calFlw(grmr, ps,grmr,follow)
	| calFlw(Transition(x,[])::xs, p::ps, grmr,follow) = calFlw(xs, p::ps,grmr,follow)
  | calFlw(Transition(x,y::ys)::xs, p::ps, grmr,follow) =
      if( y = p ) then
      	if(null(ys, nlbl) = true) then
				 mapInsert(calFlw(Transition(x,ys)::xs, p::ps, grmr,follow), p, firstLook(ys,first))
				else 
				 mapInsert(calFlw(Transition(x,ys)::xs, p::ps, grmr,follow), p, firstLook(ys,first))
			else
				calFlw(Transition(x,ys)::xs, p::ps, grmr,follow) ;												            			
val follow = loop(calFlw, follow, gr1, nonTerminal, l);

(* defining map from (non terminal,terminal) to rule for LR1*)
val llTable = Mapll.empty;
val emptystring = [] : string list;

fun initiateTable([],_,terminal) = llTable
  | initiateTable(y::ys,[],terminal) = initiateTable(ys, terminal,terminal)
  | initiateTable((NT y)::ys,(T x)::xs,terminal) = Mapll.insert(initiateTable((NT y)::ys, xs,terminal),[y,x],emptystring);
  
val llTable = initiateTable(nonTerminal,terminal,terminal); 

fun stringof([]) = [" "]
  | stringof((T y)::ys) = y::stringof(ys)
	| stringof((NT y)::ys) = y::stringof(ys)
	
fun createTable([], ter, llTable, terminal) = llTable
  | createTable(Transition(x,y)::xs, [], llTable, terminal) = createTable(xs,terminal, llTable,terminal)
	| createTable(Transition(x,y)::xs,(T t)::ts, llTable,terminal) = 
			 if(present(t, firstLook(y,first)) = true orelse (null(y,nlbl) = true 
			 andalso 
			    present(t, Mapfst.lookup(follow, NT x)) = true) ) 
			 then
					 mapInsertl(createTable(Transition(x,y)::xs,ts, llTable,terminal), [x ,t], (x::"->"::stringof(y))) 
			 else 
			     createTable(Transition(x,y)::xs, ts, llTable,terminal);
				  
val llTable = createTable(gr1, terminal, llTable, terminal);

MapNlbl.listItemsi(nlbl);	
Mapfst.listItemsi(first);	
Mapfst.listItemsi(follow);
Mapll.listItemsi(llTable);


 
  




(* 

fun repeat(true) = calNlbl(nlbl)
	| repeat(false) = nlbl;
	
fun calNlbl(grmr, nonTerminals)      

type Grammar = Rule list;
							   
val rule1 = (NT("A") , Nil);
val gr1 = [rule1];

fun Nullable (grm,var) =



;
(*structure MapT = RedBlackMapFn (struct
								type ord_key = string
								val compare = String.compare;
								end) *)
val nlbl= MapT.insert(nlbl, "A", false);							
val nlbl= MapT.insert(nlbl, "B", true);
MapT.find(nlbl, "A");
val (nlbl,p:bool) = MapT.remove(nlbl, "A");
MapT.listItemsi(nlbl);


(*fun Nullable (grm,var) = *)   *)


(*defining a map from Terminal to Variable for grammar 
structure MapGrmr = RedBlackMapFn(GrammarKey);
val grammar = MapGrmr.empty;

val grammar = MapGrmr.insert(grammar, "A", Nil);
val grammar = MapGrmr.insert(grammar, "A", NT("b"));

MapGrmr.listItemsi(grammar);*)
 

							     
