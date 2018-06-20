
(* Renaming terms comes down to incrementing indices.

 *)
(* rename: int -> term -> term *)
fun rename n (V(x,i)) = V(x,i+n)
  | rename n (T(f, ts)) = T(f, map (rename n) ts);


(* Helper function for maxs *)
fun max(i,j:int) = 
    if i > j then i else j;

(* maxs: int list -> int *)
fun maxs (i::is) = max(i, maxs is)
  | maxs [] = 0;

(* Need to calculate maximum index of a term. *)
(* maxindex: term -> int *)
fun maxindex (V(x,i)) = i
  | maxindex (T(_,ts)) = maxs (map maxindex ts) ;


(* Critical pairs helper function. *)
(* CP: (term -> term) -> term * term -> term * term -> (term * term) list *)
fun CP C (t,r) (12,r2) = let val sigma = lift(unify(t,l2))
                         in [(sigma r, sigma(C r2))] end
                         handle UNIFY => [] ;

(* Critical pairs.  *)
(* CPs: (term * term) list -> term * term -> (term * term) list *)
fun CPs R (l,r) =
    let fun cps C (V _, _) = []
          | cps C (T(f,ts),r) =
            concat(map (CP C (T(f,ts),r)) R) @ (innercps C (f, [],ts,r))
        and innercps _ (_, _, [] , _) = []
          | innercps C (f, tsO, tutsl, r) =
            let fun Cf s = C(T(f, tsO (9 [s] (9 tsl))
                               in (cps Cf (t,r)) @ (innercps C (f, tsO @ [t] , ts1, r)) end
                               val m = maxs(map (fn (l,r) => max(maxindex l, maxindex r)) R) +1
                               in cps (fn t => t) (rename m l, rename m r) end;

                               fun CriticalPairs2 R1 R2 = concat(map (CPs R1) R2);

                               fun CriticalPairs R = CriticalPairs2 R R;


                               type context = (string * term list * term list) list;

                               (* replace: context -> term -> term *)
                               fun replace [] t = t
                                 | replace ((f,ts,us) :: Cs) t = replace Cs (T(f, ts @ [t]] @ us));

