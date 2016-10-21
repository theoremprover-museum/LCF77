
(DML tokofint(N) N (int /-/> tok))
(DML intoftok(TOK)
 (COND ((NUMBERP TOK) TOK) (T (ERR @intoftok)))
 (tok /-/> int)
)

(TML)

let juxt(tok1,tok2) = implode( explode tok1 @ explode tok2) ;;

mlinfix `orf`;;
mlinfix `andf`;;
mlinfix `o`;;
mlinfix `orelsef`;;

mlinfix `#`;;
mlinfix `commaf`;;
mlinfix `oo`;;
mlinfix `o2`;;


let $orf(p,q)x = p x or q x ;;

let $andf(p,q)x = p x & q x ;;

let notf p x = not p x ;;

let $o(f,g)x = f(g x) ;;

let $orelsef(f,g)x = f x ? g x ;;

let condf(p,f,g)x = p x => f x | g x ;;

let can f x = (f x ; true) ? false ;;

let assert p x = p x => x | fail ;;


let $# (f,g) (x,y) = (f x, g y);;

let $commaf (f,g) x = (f x, g x);;

let $oo (f,(g,h)) x = f(g x, h x);;

let $o2 (f,g) x y = f(g x y);;

let pair x y = (x,y);;

let eqfst x (y,z) = (x=y)
and eqsnd x (y,z) = (x=z);;

let I x = x;;

let K x y = x;;
