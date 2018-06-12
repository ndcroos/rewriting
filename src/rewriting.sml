
(* Represents outcomes *)
datatype order = GR | EQ | NGE


(* lex: (a * (3 -> order) -> a list * (3 list -> order *)
fun lex ord ([],[]) = EQ
| lex ord (x::xs, y::ys) = case ord(x,y) of
	GR => GR
	| EQ => lex ord (xs,ys)
	| NGE => NGE;



(* reml: {a * (3 -> booD -> a list -> (3 -> a list *)
fun reml ord ([],_) = []
| reml ord (x::xs, y) = if ord(x,y) = EQ then xs
else x :: reml ord {xs, y)) ;
(* mdiff: (a * (3 -> bool) -> a list -> (3 list -> a list *)
fun mdiff ord {xs, []) = xs
| mdiff ord (xs, y::ys) - mdiff ord (reml ord (xs,y), ys);

(* mul: (a * a -> order) -> a list * a list -> order *)
fun mul ord (ms,ns) =
let val nms = mdiff ord (ns,ms)
val mns = mdiff ord (ms,ns)
in if null(nms) andalso null(mns) then EQ
else if forall (fn n -> exists (fn m => ord(m,n) = GR) mns) nms
then GR else NGE
end;

(* > Lex */


(* Implementation of multisets as assocation lists*)