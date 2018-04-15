(* addPP: polynomial * polynomial -> polynomial *)
fun addPP(p,[]) = p
| addPP([],q) = q
| addPPim(m::p,n::q) = (case Lex ordVar (m,n) of
GR => n::addPP(m::p,q)
| EQ => addPP(p,q)
| NGE => m::addPP(p,n::q));

(* mulMM: monomial * monomial -> monomial *)
fun mulMMi([],n) = n
| mulMM(m,[]) = m
| mulMM(a::m,b::n) = (case ordVar(a,b) of
EQ => a::mulMM(m,n)
| GR => b::mulMM(a::m,n)
| NGE => a::mulMM(m,b::n));

(* mulMP: monomial * polynomial -> polynomial *)
fun mulMP(m,[]) = []
| mulMP(m,n::p) = addPP([mulMM(m,n)], mulMP(m,p));

(* mulPP: polynomial * polynomial -> polynomial *)
fun mulPP([],p) = []
| mulPPi(m::p,q) = addPP (mulMP (m,q), mulPP(p,c)) ;

type subst = (int * polynomial) list;

(* substM: subst * monomial -> polynomial *)
fun substM(a,[]) = [[]]
| substM(s,i::m) = if indom i s then mulPP(app s i, substM(s,m))
else mulMP([i], substM(s,m) ) ;

(* substP: subst * polynomial -> polynomial *)
fun substP(s, []) = []
| substP(s,m::p) = addPP(substM(s,m),substP(s,p));

exception BUnify;
fun bu [] = []
| bu [[]] = raise BUnify
| bu t =
let val (x,(r,s)) = decomp t
val rl = addPP([[]],r)
val u = bu(mulPP(rl,S))
val rlu = substP(u,rl)
val su = substP(u,s)
in (x,addPP(mulMP([x] ,rlu) ,su)) :: u end;

(* decomp2: int * polynomial * polynomial * polynomial
-> polynomial * polynomial *)
fun decomp2(_, [], r, s) = (r,s)
| decomp2(x, (y::m)::p, r, s) =
if x=y then decomp2(x, p, r@[m] , s) else (r, s@(y::m)::p);

(* decomp: polynomial -> int * (polynomial * polynomial) *)
fun decomp ([]:: (x::m)::p) = (x, decomp2(x,p,[m],[[]]))
| decomp ((x::m)::p) = (x, decomp2(x,p,[m],[]));

