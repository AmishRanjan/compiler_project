
fun  helper (SOME x) =   x  (*same thing as above *) 
    |helper NONE = nil  ;
fun  helper a =  valOf a ;

datatype sym =   ter of string 
               | nonter of string ;
            
fun compare_ (ter x ,ter y) = String.compare(x , y ) 
   |compare_ (ter x , nonter y) = String.compare(x , y ) 
   |compare_ (nonter x ,ter y ) = String.compare( x , y )
   |compare_ (nonter x ,nonter y ) = String.compare(x,y) ;
            
               
structure Key =
  struct
    type ord_key = sym
    val compare = compare_
  end 

(* just for testing the helper and  inserting function
val nul = first.insert(first.empty , "start" , [4]) ;

val nul = first.insert(nul , "start" , helper (first.find(nul , "start")) @ [5]);

first.find(nul , "start") ;

*)

val a =[(nonter("S"),[nonter("A") ,nonter("B")]),(nonter("B"),[ter("b")]),(nonter("A"),[ter("a") ]),(nonter("A"),[ter("E") ])] ;

val a =[(nonter("S"),[nonter("B") ]),(nonter("S"),[ter("a")]),(nonter("B"),[ter("E")]),(nonter("B"),[ter("c")]),(nonter("C"),[ter("d") ]),(nonter("C"),[nonter("S") ,nonter("B"),nonter("C")])] ;


fun  g_list [] =[] 
    |g_list ((a,b)::xs) = ( a :: b ) @ g_list xs 
    
    
structure nul_str = RedBlackMapFn (Key)

fun check (ter x ) = true 
    | check (nonter x) = false ;
 
fun init ([] , nul_map ) = nul_map 
   |init ((x::xs)  , nul_map )=init(xs, nul_str.insert(nul_map,x,false)) 
                               
                           
val li =   (g_list a) ;        

val nul_map = nul_str.insert(nul_str.empty,ter "E" , true) ;
val nul_map = init (li ,nul_map );
nul_str.listItemsi(nul_map) ;

val nul_map = nul_str.insert(nul_map,ter "E" , true) ;


fun check_prod_null ([] , nul_map ) = true |
               check_prod_null ( (y::ys) ,nul_map ) = if ( nul_str.lookup(nul_map , y)=false)
                                               then false 
                                             else check_prod_null (  ys , nul_map) ;    
fun  nullable   [] nul_map = nul_map 
               |nullable ((b,bs )::by) nul_map = if( check_prod_null ( bs ,nul_map) = true ) then                       
                                                        nul_str.insert( nullable by nul_map,b ,true) 
                                     
                                                else 
                                                         nullable by  nul_map ;
                                     
              
val term_and_nonterm = g_list a ;
              
                    
 
                                   
fun loopnull ([] , nul_map) = nul_map 
    |loopnull (x::xs ,  nul_map ) =  loopnull(xs, nullable a nul_map) ;
    

              

val nul_map =loopnull (term_and_nonterm , nul_map );
nul_str.listItemsi(nul_map) ;

(*     -----------------------------------------first _______---------______________________________________----------------______________________--------------________*)

structure firstStruct = RedBlackMapFn (Key)
structure firstStruct = RedBlackMapFn (Key)
val first = firstStruct.empty
val follow = firstStruct.empty
 
fun initg ([] , first ) = first 
   |initg ((x::xs)  , first )=initg(xs, firstStruct.insert(first,x,[]:(sym list))) 

 
  
val first = initg(  (g_list a ) , firstStruct.empty  ) ;


val follow = initg(  (g_list a ) , firstStruct.empty  )  ;        


  (*                    

(*for each production *)
fun check_prod  ([] , first ) = first
   | check_prod ( (y::ys):yz ,first ) =  pass(yx ,first)
                                          val before = [y] 

*) 

val grm = a ;

(*checking on the basis of constructor *)
fun check (ter x ) = true 
    | check (nonter x) = false ;

(*initialising first of terminals*)
fun init_term ( [] , first ) = first 
    |init_term ( (x::xs ) ,first ) = if ( check x ) then init_term (xs ,firstStruct.insert(first , x , [x]) )
                                     else init_term (xs ,first) ;
                                  
val first =init_term( term_and_nonterm , first ) ;
val follow =init_term( term_and_nonterm , follow ) ;

firstStruct.listItemsi(follow) ;(*
(***for each production ****)
fun loop1 ([] , first ,_) = first
   |loop1 (((a,( []:sym list))::ys),first ,_)  =loop1 (ys,first ,[])
   |loop1 (((a,(x::xs))::ys),first ,Y) =
                                   if 
                                   (check_prod_null ( Y , nul_map )=true)then
                                
                                   loop1 (((a,(xs))::ys),firstStruct.insert(first , a, firstStruct.lookup(first ,a ) @ firstStruct.lookup(first ,x ))    ,x::Y)  
                                         
                
                                   else
                                     loop1 (((a,(xs))::ys),first ,x::Y)  ;
                                     
                             
fun loopfirst ([] , first,grm) = first 
    |loopfirst (x::xs ,  first ,grm ) =  loopfirst(xs, loop1 (grm ,first,[]),grm) ;

val first = loopfirst( term_and_nonterm,first ,grm ) ; 
firstStruct.listItemsi(first) ;
                              
                              
*)
(*fun loop1 ([] , first ,Y) = first
   |loop1 ((a,( [])::ys,first ,_)  =loop1 (a,ys,first ,[])
   |loop1 ((a,(x::xs))::ys,first ,Y) =if (Y=[] andalso nul_str.lookup(nul_map , x )=true)then
                                firstStruct.insert(first , a, x::firstStruct.lookup(first ,hd xs ))
                                else (
                                   if (check_prod_null ( Y , nul_map )=true)then
                                        firstStruct.insert(first , a, firstStruct.lookup(first ,hd xs ))                   else
                                     loop1 ((a,(xs))::ys,first ,x::Y)  ;
                              )
*)

(*-----------------------follow ---------------------*)
(*including yi *)

fun loop3 ([]:sym list ,s ,key ) = s 
    |loop3 ((x::xs) , s ,key)  =if( nul_str.lookup(nul_map , x ) = true ) then 
                        firstStruct.insert(s ,key , (firstStruct.lookup(first , x ) @ firstStruct.lookup(loop3(xs , s,key),key))) 
                        else
                          s ;


fun loop2 ([] , follow ) = follow
   |loop2 (((a,( []:sym list))::ys),follow )  =loop2 (ys,follow )
   |loop2 (((a,(x::xs))::ys),follow ) =
                                   if 
                                   (check_prod_null ( xs , nul_map )=true)then
                                    loop2 (((a,(xs))::ys),   firstStruct.insert(follow , x, firstStruct.lookup(follow ,x ) @ firstStruct.lookup(follow ,a )@ firstStruct.lookup(loop3 (xs , firstStruct.empty,x),x  )) ) 
                                        
                
                                   else
                                     firstStruct.insert(loop2 (((a,(xs))::ys),follow  ),x,firstStruct.lookup( loop2 (((a,(xs))::ys),follow  ) ,x ) @ firstStruct.lookup(loop3 (xs , firstStruct.empty,x),x)   )  ;
                                     
                                     
                                     
                                     
                             
fun loopfollow ([] , follow) = follow 
    |loopfollow (x::xs ,  follow  ) =  loopfollow(xs, loop2 (grm ,follow)) ;

val follow = loopfollow( term_and_nonterm,follow  ) ; 
firstStruct.listItemsi(follow) ;








