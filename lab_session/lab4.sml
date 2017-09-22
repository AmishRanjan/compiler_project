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

(*grammar definition ends *)
fun present(x,[]) = false
	| present(x, y::ys) = if(x = y) then true
												else  present(x,ys)
													
fun equate([],[]) = []
	| equate([],y) = y
	| equate(x,[]) = x
	| equate(x::xs,y::ys) = if(x = y) 
														then x::equate(xs,ys)
													else 
														if(present(x,ys) = true) then
															equate(xs,y::ys)
														else x::equate(xs,y::ys)
	
fun nonTer([]) = [] 
  | nonTer(Transition(x,y)::Transition(x1,y1)::xs) = if(x1 = x) then
  																											  nonTer(Transition(x1,y1)::xs)
  																										 else 
  																												NT x::nonTer(Transition(x1,y1)::xs)
  | nonTer(Transition(x,y)::xs) =  NT x::nonTer(xs);

val nonTerminal = nonTer(gr1);
	  
fun ter([]) = [] 
  | ter(Transition(x,[])::xs) = ter(xs)
	|	ter(Transition(x,y::ys)::xs) = if(present(y , nonTerminal) = false andalso y <> T "E" ) then 
																				equate([y] , ter(Transition(x,ys)::xs))
																	else ter(Transition(x,ys)::xs)
val terminal = ter(gr1);
   
fun length([]) =0
	| length(x::xs) = length(xs) + 1;
val l = length(nonTerminal);
														
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


fun loop(nlbl,gr1,nonTerminal,l) = if(l = 0) then
																		nlbl
											            else loop(nullable( gr1, nonTerminal,gr1,nlbl),gr1,nonTerminal,l-1);

val nlbl = loop(nlbl,gr1, nonTerminal,l);

MapNlbl.listItemsi(nlbl);
(* defining a map from variable to terminal for first *)
structure Mapfst = RedBlackMapFn(StringKey);
val first= Mapfst.empty;
val emptystring = []:string list;
val first = Mapfst.insert(first, T"E", emptystring);
fun initiatefst([],first) = first
	|	initiatefst((T x)::xs,first) = Mapfst.insert(initiatefst(xs,first),T x, [x]) 
	|	initiatefst( x::xs,first) = Mapfst.insert(initiatefst(xs,first), x, emptystring);
	
val first = initiatefst(nonTerminal,first);
val first = initiatefst(terminal,first);
Mapfst.listItemsi(first);
													
fun firstLook([],first) = []
	| firstLook(y::ys,first) = if(MapNlbl.lookup(nlbl, y) = true) then
	               							 equate(Mapfst.lookup(first,y) , firstLook(ys,first))
	               						 else Mapfst.lookup(first,y);
																	 
fun calFirst(_,[],grmr,first) = first
	| calFirst([],p::ps,grmr,first) = calFirst(grmr, ps,grmr,first)   
  | calFirst(Transition(x,y)::xs, p::ps, grmr,first) =
      if(p = NT x ) then
				Mapfst.insert(calFirst(xs, p::ps, grmr,first), p, equate(Mapfst.lookup(calFirst(xs, p::ps, grmr,first), p),firstLook(y,first)))
			else
				calFirst(xs, p::ps, grmr,first) ;
				
fun loopfirst(first,gr1,nonTerminal,l) = if(l = 0) then
																						first
											     				       else loopfirst(calFirst( gr1, nonTerminal,gr1,first),gr1,nonTerminal,l-1);	
								            			
val first = loopfirst(first,gr1, nonTerminal,l);

(* defining map from variable to terminal for follow setr calculation *)
structure Mapflw = RedBlackMapFn(StringKey);
val follow= Mapflw.empty;

val emptyString = []:string list;
fun initiateflw([]) = follow 
	|	initiateflw( x::xs) = Mapflw.insert(initiateflw(xs), x, emptyString);
	
val follow = initiateflw(nonTerminal);
																	 
fun calFlw(_,[],grmr,follow) = follow
	| calFlw([],p::ps,grmr,follow) = calFlw(grmr, ps,grmr,follow)
	| calFlw(Transition(x,[])::xs, p::ps, grmr,follow) = calFlw(xs, p::ps,grmr,follow)
  | calFlw(Transition(x,y::ys)::xs, p::ps, grmr,follow) =
      if( y = p ) then
      	if(null(ys, nlbl) = true) then
				 Mapflw.insert(calFlw(Transition(x,ys)::xs, p::ps, grmr,follow), p, equate(Mapflw.lookup(follow, NT x),firstLook(ys,first)))
				else 
				 Mapflw.insert(calFlw(Transition(x,ys)::xs, p::ps, grmr,follow), p, equate(Mapflw.lookup(calFlw(Transition(x,ys)::xs, p::ps, grmr,follow),y),firstLook(ys,first)))
			else
				calFlw(Transition(x,ys)::xs, p::ps, grmr,follow) ;
				
fun loopflw(follow,gr1,nonTerminal,l) = if(l = 0) then
																						follow
											     				       else loopflw(calFlw( gr1, nonTerminal,gr1,follow),gr1,nonTerminal,l-1);	
								            			
val follow = loopflw(follow,gr1,nonTerminal,l);

(* defining map from (non terminal,terminal) to rule for LR1*)

structure Mapll = RedBlackMapFn(TableKey);

val llTable = Mapll.empty;
val emptystring = [] : string list;

fun initiateTable([],_,terminal) = llTable
  | initiateTable(y::ys,[],terminal) = initiateTable(ys, terminal,terminal)
  | initiateTable((NT y)::ys,(T x)::xs,terminal) = Mapll.insert(initiateTable((NT y)::ys, xs,terminal),[y,x],emptystring);
  
val llTable = initiateTable(nonTerminal,terminal,terminal); 
Mapll.listItemsi(llTable);

fun stringof([]) = [" "]
  | stringof((T y)::ys) = y::stringof(ys)
	| stringof((NT y)::ys) = y::stringof(ys)
	
fun createTable([], ter, llTable, terminal) = llTable
  | createTable(Transition(x,y)::xs, [], llTable, terminal) = createTable(xs,terminal, llTable,terminal)
	| createTable(Transition(x,y)::xs,(T t)::ts, llTable,terminal) = 
					if(present(t, firstLook(y,first)) = false) then 
						createTable(Transition(x,y)::xs, ts, llTable,terminal)
					else 
					  Mapll.insert(createTable(Transition(x,y)::xs,ts, llTable,terminal), [x ,t], (x::"->"::stringof(y))@Mapll.lookup(createTable(Transition(x,y)::xs,ts, llTable,terminal), [x,t])) ;

val llTable = createTable(gr1,terminal, llTable,terminal);
					  
fun addTable([], ter, llTable, terminal) = llTable
  | addTable(Transition(x,y)::xs, [], llTable, terminal) = addTable(xs,terminal, llTable,terminal)
	| addTable(Transition(x,y)::xs,(T t)::ts, llTable,terminal) = 
					if(null(y,nlbl) = false)  then 
						addTable(xs, terminal, llTable,terminal)
					else if (present(t, Mapflw.lookup(follow, NT x)) = true) then 
					  Mapll.insert(addTable(Transition(x,y)::xs,ts, llTable,terminal), [x ,t], (x::"->"::stringof(y))@Mapll.lookup(addTable(Transition(x,y)::xs,ts, llTable,terminal), [x,t])) 
					 else addTable(Transition(x,y)::xs,ts, llTable,terminal);
		
val llTable = addTable(gr1,terminal, llTable,terminal);




MapNlbl.listItemsi(nlbl);	
Mapfst.listItemsi(first);	
Mapflw.listItemsi(follow);
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
 

							     
