
(TML)

deftype goal = form # ( simpset # form list) 
   and proof = thm list -> thm  ;;

deftype tactic = goal -> goal list # proof ;;

let CASESTAC tm :tactic (fm,ss,fml) =
  (let asstt,assff,assuu = eqtt tm, eqff tm, equu tm  in
   ([fm, ssadd(ASSUME asstt)ss, asstt.fml 
    ;fm, ssadd(ASSUME assff)ss, assff.fml 
    ;fm, ssadd(ASSUME assuu)ss, assuu.fml
    ],
    (CASES tm o threeof)
  )) ? failwith `CASESTAC` ;;

let findterminterm p =
  letrec findtm tm =
    p tm => tm |
  ((let (),tm = destabs tm in findtm tm )
       ??  ``destabs``
   ((let tm,tm'= destcomb tm in (findtm tm ? findtm tm') )
       ??  ``destcomb``
    failwith `findterminterm`
  ))
  in findtm ;;

let findterminform p =
  letrec findtm fm =
   ((let (),fm = destquant fm in findtm fm)
         ?? ``destquant``
    ((let fm,fm' = destimp fm ? destconj fm in(findtm fm ? findtm fm'))
         ?? ``destconj``
     let tm,tm' = destequiv fm ? destinequiv fm in
           (findterminterm p tm ? findterminterm p tm')
    )
   )       ? failwith `findterminform`
  in findtm;;

let ANYCASESTAC :tactic (fm, ss,fml) =
  let tm = findterminform(\tm. typeof tm = ":TR" & freeinform[tm]fm)fm
           ? failwith `ANYCASESTAC`
  in CASESTAC tm (fm, ss,fml) ;;


let GENTAC:tactic (fm, ss,fml) =
   let x,fm' = destquant fm ? failwith `GENTAC`  in
      let x' = variant(x, formlfrees(fm.fml)) in
       ( [ substinform[x',x]fm', ss,fml ]  ,  (GEN x' o hd) )  ;;


let SIMPTAC:tactic (fm, ss,fml) =
   let fm',(),pr' = simpform ss fm in
   (fm'="TRUTH" 
    => ( [], K(pr' AXTRUTH) )
    |  ( [ fm', ss,fml ] , (pr' o hd) )  
   ) ;;


let GSUBSTAC substfn thl :tactic (fm,ss,fml) =
     let thxl = thxpairs thl  in
       let w = substfn (xlhspairs thxl) fm   in
         [ substinform(rhsxpairs thxl)w, ss,fml ] ,
         (SUBST(map(SYM # I)thxl)w o hd)    ;;

let SUBSTAC thl g = GSUBSTAC substinform thl g ? failwith `SUBSTAC`

and SUBSOCCSTAC nlthl g =
     let nll,thl = split nlthl   in
       GSUBSTAC (suboccs nll) thl g ? failwith `SUBSOCCSTAC` ;;

	% Alternative definitions:

	  let SUBSTAC thl (fm,ss,fml) =
               (let fm' = substinform(map equivpair thl)fm  in
                  [fm',ss,fml], (SUBS(map SYM thl) o hd)
               ) ? failwith `SUBSTAC` 

	  and SUBSOCCSTAC nlthl (fm,ss,fml) =
	       (let nll,thl = split nlthl  in
	          let fm' = suboccs nll (map equivpair thl fm   in
                    [fm',ss,fml], (SUBSOCCS(map(I # SYM)nlthl) o hd) ;;
	%



letref genindvarprefix = `INDVAR` ;;

let genindvar(n,ty) = mkvar(juxt(genindvarprefix,tokofint n), ty) ;;

let GINDUCTAC substfn thl :tactic (fm,ss,fml) =
     let goalfrees = formlfrees(fm.fml)
     in
     let x'of = letref n=0 in
	   \t.(n := n+1 ;
	       let x = isvar t => t | genindvar(n,typeof t)
	       in variant(x,goalfrees)  )
     in
     let thx'l = map (\th.(th, x'of(lhs(concl th)))) thl
     in
     let fm' = substfn (xlhspairs thx'l) fm
     and funx'l = map (\(th,x').(funof th, x')) thx'l
                  where funof th =
                        let fix,fun = destcomb(snd(destequiv(concl th)))
                        in  fst(destconst fix)=`FIX` => fun | fail
     in
       [ substinform(uupairs funx'l)fm', ss, fml
       ; substinform(steppairs funx'l)fm', ss, fm'.fml
       ] ,
       (SUBST(map(SYM # I)thx'l)fm' o INDUCT funx'l fm' o twoof)  ;;

let INDUCTAC thl g = GINDUCTAC substinform thl g ? failwith `INDUCTAC`

and INDUCOCCSTAC nlthl g =
     let nll,thl = split nlthl   in
       GINDUCTAC (suboccs nll) thl g ? failwith `INDUCOCCSTACS`  ;;
