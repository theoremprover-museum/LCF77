COMMENT ⊗   VALID 00006 PAGES
C REC  PAGE   DESCRIPTION
C00001 00001
C00002 00002	% OL2.ML, THYFNS.ML, PPLAMB.ML, DRUL.ML, TCL.ML %
C00006 00003	% GEN.ML %
C00008 00004	% LIS.ML, PCRUL.ML %
C00013 00005	% OL3.ML %
C00018 00006	% TAC.ML %
C00024 ENDMK
C⊗;
% OL2.ML, THYFNS.ML, PPLAMB.ML, DRUL.ML, TCL.ML %

% OL2.ML %

(TML)

let substinterm l t = substinterm(l,t)
and substinform l f = substinform(l,f)
and substoccsinterm l t = substoccsinterm(l,t)
and substoccsinform l f = substoccsinform(l,f)
and freeinterm l t = freeinterm(l,t)
and freeinform l f = freeinform(l,f)  ;;


% THYFNS.ML %

(TML)

let AXIOM tok1 tok2 = AXIOM(tok1,tok2);;
let FACT  tok1 tok2 = FACT (tok1,tok2);;


% PPLAMB.ML %

(TML)

newtypes [``.``; ``TR = tr``] ;;

map newconstant [
 `()` , ":." ;
 `TT` , ":TR";
 `FF` , ":TR";
 `UU` , ":*" ;
 `FIX`, ":(*->*)->*" ;
`COND`, ":TR->*->*->*" ;
`PAIR`, ":*->**->(*#**)" ;
`FST` , ":*#**->*" ;
`SND` , ":*#**->**" ;
`INL` , ":*->*+**" ;
`INR` , ":**->*+**" ;
`OUTL`, ":*+**->*" ;
`OUTR`, ":*+**->**" ;
`ISL` , ":*+**->TR";
`ISR` , ":*+**->TR"
]  ;;


% DRUL.ML %

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


% TCL.ML %

(TML)


letrec chop(n,l) = n=0 => (nil,l)
    | let m,l' = chop(n-1, tl l) in  hd l . m , l' ;;

letrec mapshape nl fl l =  null nl => nil
    | let m,l = chop(hd nl,l) in (hd fl)m . mapshape(tl nl)(tl fl)l ;;

mlinfix`THEN` ;;
mlinfix`THENL` ;;
mlinfix`ORELSE` ;;

let $THEN (f1,f2) g =
   let gl,p=f1 g in
      let gll,pl = split(map f2 gl) in
         flat gll ,  (p o mapshape(map length gll)pl) ;;

let $THENL (f1,f2l) g =
   let gl,p = f1 g  in
      let gll,pl = split(map (\(f2,g).f2 g) f2gl)
                   where f2gl = combine(f2l,gl) ? failwith `THENL`
      in
         flat gll  ,  (p o mapshape(map length gll)pl)  ;;

let $ORELSE (f1,f2) g = f1 g ? f2 g ;;

let IDTAC g = [g],hd;;

letrec REPEAT f g = ((f THEN REPEAT f) ORELSE IDTAC ) g ;;

% GEN.ML %

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

% LIS.ML, PCRUL.ML %

% LIS.ML %

(TML)

let mem x l = mem(x,l);;

let map f l = map(f,l);;

let exists p l = exists(p,l);;
let forall p l = forall(p,l);;

let genmem p x = exists(\y.p(x,y));;

let itlist f l x = revitlist(f, rev l, x);;
let revitlist f l x = revitlist(f,l,x);;

let find p l = find(p,l);;
let tryfind f l = tryfind(f,l);;
let filter p l = filter(p,l);;
let mapfilter f l = mapfilter(f,l);;

let assoc x = find(eqfst x);;
let revassoc x = find(eqsnd x);;

let intersect(l1,l2) = filter (\x. mem x l2) l1 ;;
let subtract(l1,l2) = filter (\x. not mem x l2) l1 ;;
let union(l1,l2) = l1 @ subtract(l2,l1) ;;

letrec split l = (let (x1,x2).l' = l  in
                    (x1.l1',x2.l2') where l1',l2' = split l'
                 )? (nil,nil)  ;;

letrec combine(l1,l2) = (let (x1.l1'),(x2.l2') = l1,l2  in
                           (x1,x2).combine(l1',l2')
                        )?(null l1 & null l2 => nil|failwith`combine`);;


% PCRUL.ML %

(TML)

let CONJ(th1,th2) = mkthm( union(hyp th1, hyp th2) ,
			   mkconj(concl th1, concl th2) ) ;;

let SEL1 , SEL2 = SEL 1 , SEL 2
		  where SEL n th =
			let w1,w2 = destconj(concl th)
				     ? failwith (n=1=>`SEL1`|`SEL2`)
			in mkthm(hyp th, (n=1=>w1|w2))  ;;

let DISCH w th = mkthm( disch(w,hyp th) , mkimp(w,concl th) ) ;;

let destconj1 w = destconj w  ? (istruth w => fail | (w,truth) ) ;;

let destconjimp w =
         let w,w' = destimp w  in
            let w1,w2 = destconj1 w  in
               w1,mkimp(w2,w') ;;

letrec wmp wi w : form =
        (let (wa,wc),(w1,w2) = (destconjimp wi, destconj1 w)
			       ? failwith `dest`
         in aconvform(wa,w1) => wmp wc w2 | failwith `MP`
        )??``dest`` wi  ;;
 
let MP thi th = mkthm( union(hyp thi, hyp th) ,
		       wmp(concl thi)(concl th) ) ;;

let GEN x th = exists (freeinform[x]) (hyp th) => failwith `GEN`
                 | mkthm( hyp th , mkquant(x, concl th) ) ;;
 
let SPEC t th =  let x,w = destquant(concl th) ? failwith `SPEC`
		 in mkthm( hyp th , substinform[t,x]w )  ;;

let ASSUME w = mkthm([w],w);;
 
let AXTRUTH = mkfreethm truth ;;

let INSTTYPE insttylist th = null insttylist => th |
    (let wl,w = destthm th
     and tyvl = map (assert isvartype o snd) insttylist   in
       exists (typesinform tyvl) wl => fail
        | mkthm(wl, outr(geninstintmfm(formlvars wl)insttylist(inr w)))
    ) ? failwith `INSTTYPE`  ;;

let INST instlist th = null instlist => th |
    (let wl,w = destthm th
     and xl = map (assert isvar o snd) instlist    in
       exists (freeinform xl) wl => fail
        | mkthm(wl, substinform instlist w)
    ) ? failwith `INST`  ;;

% OL3.ML %

(TML)

let typesinterm tyl t = typesinterm(tyl,t)
and typesinform tyl w = typesinform(tyl,w)
and typesintype tyl ty = typesintype(tyl,ty) ;;

let formlfrees,formlvars,formltyvars =
      fun formfrees , fun formvars , fun formtyvars
      where fun f wl = itlist (\w.\xl.union(f w, xl)) wl nil  ;;

let instintype insttylist ty = inst ty whererec inst ty =
     fst(revassoc ty insttylist)
     ?(failwith phylumoftype ty
	??``consttype vartype`` ty
	??``funtype`` mkfuntype((inst # inst)(destfuntype ty))
	??``sumtype`` mksumtype((inst # inst)(destsumtype ty))
	??``prodtype`` mkprodtype((inst # inst)(destprodtype ty))
      )  ;;


let geninstintmfm vars insttylist tmfm =

   let insttylist' = filter ($not o $=) insttylist
   in
   let insttokty = I # instintype insttylist'
   in
   let instvar =
        (\x.snd(assoc x changedpairs) ? x)
        where changedpairs =
               let unchangedvars,changedvars =
                    itlist (f (map snd insttylist'))
                           (tmfmvars tmfm)
                           (nil,nil)
                    where f tyl x (l1,l2) = typesinterm tyl x
                                                => (l1, x.l2)
                                                |  (x.l1, l2)
               in
               letref vars' = union(unchangedvars,vars)
               in
               let instvariant x =
                   let xinst = mkvar(insttokty(destvar(variant(x,nil))))
                   in  hd(vars' := variant(xinst,vars').vars')
               in
                 map (\x.(x, instvariant x)) changedvars
   in
   letrec insttm t =
	    failwith phylumofterm t
              ??``var`` instvar t
	      ??``const`` mkconst(insttokty(destconst t))
	      ??``comb`` mkcomb((insttm # insttm)(destcomb t))
	      ??``abs``  mkabs((instvar # insttm)(destabs t))
   in
     isl tmfm => inl(insttm(outl tmfm))
       |letrec instfm w =
	    failwith phylumofform w
              ??``truth`` w
	      ??``quant`` mkquant((instvar # instfm)(destquant w))
	      ??``conj`` mkconj((instfm # instfm)(destconj w))
	      ??``imp`` mkimp((instfm # instfm)(destimp w))
	      ??``equiv`` mkequiv((insttm # insttm)(destequiv w))
	      ??``inequiv`` mkinequiv((insttm # insttm)(destinequiv w))
	in  inr(instfm(outr tmfm)) ;;

let instinterm insttylist t =
       outl(geninstintmfm nil insttylist (inl t))
and instinform insttylist w =
       outr(geninstintmfm nil insttylist (inr w))  ;;


let disch(w,wl) = filter (\w'.not aconvform(w,w')) wl ;;

let lhsxpairs = map (\(th,x).(fst(equivpair th),x))
and rhsxpairs = map (\(th,x).(snd(equivpair th),x))
and xlhspairs = map (\(th,x).(x,fst(equivpair th)))
and xrhspairs = map (\(th,x).(x,snd(equivpair th)))  ;;

let uupairs = map (\(fun,x).(mkconst(`UU`,typeof x),x))
and steppairs = map (\(fun,x).(mkcomb(fun,x),x))
and fixpairs = map (\(fun,x).("FIX ↑fun",x)) ;;

let thxpairs = map (\th.(th,genvar(typeof(fst(equivpair th))))) ;;

% TAC.ML %

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

