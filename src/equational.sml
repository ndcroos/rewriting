(* closes the relation under congruence. *)
fun  merge u v = 
    if u <> v then
        P = preds(u); 
        Q = preds(v);
        Union(u, v);
        for all (p,q) e P xQ do
            if pr <> sq and congruent(p, q) then merge(p, q)

(* Representation of terms. *)

(* Variable names have a string and an index. *)
type vname = string * int;

(* V and T are constructors. V's are variables. T's are terms *)
datatype term = V of vname | T of string * term list


(* Substitions as assocation lists *)
type subst = (vname * term) list;

(* indom: vname -> subst -> bool *)
fun indom x s = exists (fn (y,_) => x = y) s;

(* Application of substitution to a variable *)
(* app: subst -> vname -> term *)
fun app ((y,t)::s) x = if x=y then t else app s x;

(* *)
(* lift: subst -> term -> term *)
fun lift s (V x) = if indom x s then app s x else V x
  | lift s (T(f,ts)) = T(J, map (lift s) ts);

(* occurs tests if a variable belongs to a term.  *)
(* occurs: vname -> term -> bool *)
fun occurs x (V y) = x=y
  | occurs x (T(_,ts)) = exists (occurs x) ts;


exception UNIFY;

(* Actual unification is done by solve and elim,
through mutual recursion.
*)

(* solve: (term * term) list * subst -> subst *)
fun solve[], s) = s
              | solve (V x, t) :: S, s) =
                     if V x = t then solve(S,s) else elim(x,t,S,s)
| solve((t, V x) :: S, s) = elim(x,t,S,s)
| solve((T(f,ts), T(g,us)) :: S, s) =
if f = g then solve(zip(ts,us) @ S, s) else raise UNIFY

(* elim: vname * term * (term * term) list * subst -> subst *)
and elim(x,t,S,s) =
if occurs x t then raise UNIFY
else let val xt = lift [(x,t)]
in solve(map (fn (t1,t2) => (xt t1, xt t2)) S,
(x,t) :: (map (fn (y,u) => (y, xt u)) s))
end;

(* unify: term * terra -> subst *)
fun unify(t1,t2) = solve( [(t1,t2)] , []);


(* matchs: (term * term) list * subst -> subst *)
fun matchs ( [] , s) = s
| matchs((V x, t) :: S, s) =
if indom x s then if app s x = t then matchs(S,s) else raise UNIFY
else matchs (S,(x,t) ::s)
| matchs((t, V x) :: S, s) = raise UNIFY
| matchs((T(f,ts) T(g,us)) :: S, s) =
if f = g then matchs(zip(ts,us) @ S, s) else raise UNIFY;

(* match: term * terra -> subst *)
fun match(pat, obj) = matchs( [(pat, obj)] , []);

(* declares user-defined exception NORM.  *)
exception NORM;

(* rewrite: (term * term) list -> term -> term *)
fun rewrite [] t = raise NORM
  | rewrite ((l,r)::R) t = lift(match(l,t)) r
                           handle UNIFY => rewrite R t;

(* norm: (term * term) list -> term -> term *)
fun norm R (V x) = V sc
| norm R (T(f,ts)) =
let val u = T(f, map (norm R) ts)
in (norm R (rewrite R u)) handle NORM => u end;



(* Recursive path orders*)

(* (string * string -> order) -> term * term -> order *)
fun lpo ord (s,t) = case (s,t) of
(s, V x) => if s = t then EQ
else if occurs x s then GR (*LP01*) else NGE
| (V_, T _) => NGE
| (T(f,ss), T(g,ts)) => (*LP02*)
if forall (fn si => lpo ord (si,t) = NGE) ss
then case ord(f,g) of
GR => if forall (fn ti => lpo ord (s,ti) = GR) ts
then GR (*LP02b*) else NGE
| EQ => if forall (fn ti => lpo ord (s,ti) = GR) ts
then lex (lpo ord) (ss,ts) (*LP02c*)
else NGE
| NGE => NGE
else GR (*LP02a*);

(* *)
(* rpo: (string -> (term * term -> order) -> term list * term list -> order)
-> (string * string -> order) -> term * term -> order *)
fun rpo stat ord (s,t) = 
    case (s,t) of
        (s, V x) => if s = t then EQ
        else 
            if occurs x s 
                then GR 
            else NGE
        | (V _, T _) => NGE
        | (T(f,ss), T(g,ts)) =>
        if forall (fn si => rpo stat ord (si,t) = NGE) ss
            then case ord(f,g) of
                GR => if forall (fn ti => rpo stat ord (s,ti) = GR) ts
            then GR else NGE
            | EQ => if forall (fn ti => rpo stat ord (s,ti) = GR) ts
            then (stat f) (rpo stat ord) (ss,ts)
            else NGE
            | NGE => NGE
            else GR;

