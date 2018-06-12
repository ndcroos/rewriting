
(* Type abbreviation. *)
type eqf = term * term -> bool


(* mkLazy: eqf-> (eqf -> eqf) *)
fun mkLazy eagerEq subEq (s,t) =
let val (s', t') = Abstract alien subterms of s and t modulo subEq by new variables
in eagerEq (s',t') end;

fun cfeq (s,t) = (theory s = theory t) andalso (eq (theory s) cfeq (s,t));

fun eqE (s,t) = cfeq (collapse s, collapse t);

(* collapse: term -> term *)
fun collapse t =
let fun collAliens k t = (case t of
V _ => *
| T(f,ts) => if theory(t) <> k then coll t
else T(f, map (collAliens k) ts))
and coll s =
let val k = theory s
val t = collAliens k s
fun try [] = t
| try (u::us) = if eq k cfeq (t,u) then u else try us
in try (aliens k t) end
in coll t end;

(* aliens: int -> term -> terra Zisi *)
fun aliens k t = if theory (t) <> k then [t]
else case t of V _ => []
| T(_,ts) => concat(map (aliens k) ts);


fun theory( V _) = 0
| theory(T(f,_)) = case f of "f" => 1 | "g" => 2 | "h" => 3;


fun eq 0 = varEq
| eq 1 = commEq
| eq 2 = assocEq
| eq 3 = idempEq;

fun varEq _ (x,y) = s*y;

fun assocEq eq (s,t) =
let fun fringe(T("g", [s,t])) = (fringe s) @ (fringe t)
| fringe(t) = [t];
val fs = fringe s;
val ft = fringe t
in (length fs = length ft) andalso forall eq (zip(fs,ft)) end;

