
(TML)

let suboccs nll tt'l =
     substoccsinform (map (\(nl,t,t').(t,nl,t')) (combine(nll,tt'l))) ;;

let GSUBS substfn thl th =
     let thxl = thxpairs thl  in
       let w = substfn (xlhspairs thxl) (concl th)  in
         SUBST thxl w th  ;;

let SUBS thl th = GSUBS substinform thl th ? failwith `SUBS` 

and SUBSOCCS nlthl th =
     let nll,thl = split nlthl  in
       GSUBS (suboccs nll) thl th ? failwith `SUBSOCCS` ;;

let SIMP ss th = p th where (),p,() = simpform ss (concl th) ;;

let FIX th = (SUBS [SYM th] (FIXPT fun)
              where fix,fun = destcomb(snd(equivpair th))
             )? failwith `FIX` ;;
