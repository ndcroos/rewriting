
(* Represents the three possible outcomes of the function lex*)
datatype order = GR | EQ | NGE


(* lex: (a * b -> order) -> a list * b list -> order *)
(*
Implements a lexicographic order between lists of items that can be ordered.
In other words, this function implements a lexicographic product relation between two lists.

ord: the order relation between two orderable items.
a list * b list: product of two lists.

Two empty lists are equal.
If the first elements of both lists are equal, then look at the rest of the list.
*)
fun lex ord ([],[]) = EQ
  | lex ord (x::xs, y::ys) = case ord(x,y) of
				GR => GR
			| EQ => lex ord (xs,ys)
			| NGE => NGE;


(* -- Multiset orders -- *)

(* rem1: (a * b -> bool) -> a list -> b -> a list *)
(*  
ord: order relation
a list: 
b: 

returns:
a list:
*)
fun rem1 ord ([],_) = []
	| rem1 ord (x::xs, y) = if ord(x,y) = EQ then xs
	else x :: rem1 ord {xs, y)) ;
	(* mdiff: (a * (3 -> bool) -> a list -> (3 list -> a list *)



(* mdiff: (a * b -> bool) -> a list -> b -> a list *)
(* *)
fun mdiff ord {xs, []) = xs
	| mdiff ord (xs, y::ys) - mdiff ord (reml ord (xs,y), ys);



(* mul: (a * a -> order) -> a list * a list -> order *)
(*
Implements a multiset order
*)
fun mul ord (ms,ns) =
	let val nms = mdiff ord (ns,ms)
		val mns = mdiff ord (ms,ns)
	in 
		if null(nms) andalso null(mns) 
			then EQ
	else 
		if forall (fn n -> exists (fn m => ord(m,n) = GR) mns) nms
			then GR 
		else NGE
	end;

(* > Lex *)


(* Implementation of multisets as assocation lists*)

(*  assoc mdiff *)

fun assoc_mdiff =


(*  assoc mul *)
fun assoc_m
