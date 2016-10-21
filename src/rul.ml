
(TML)

let admitsinduction(w,x) = isvar x  &   ad(true,w) whererec ad(t,w) =
  (failwith phylumofform w
   ?? ``equiv inequiv``  t or easytype(typeof(rhs w)) or
                  not(isequiv w => freeinform[x]w | freeinterm[x](rhs w))
   ?? ``truth`` true
   ?? ``conj`` (ad(t,w) & ad(t,w') where w,w' = destconj w)
   ?? ``imp`` (ad(not t,w) & ad(t,w') where w,w' = destimp w)
   ?? ``quant`` not freeinform[x]w or
           ((t or finitetype(typeof y)) & ad(t,w')
            where y,w' = destquant w )
   ?  failwith`admitsinduction`
  )  ;;

let SYNTH(th1,th2) =
     (let u1,v1 = inequivpair th1
      and v2,u2 = inequivpair th2  in
	not(aconvterm(u1,u2) & aconvterm(v2,v1)) => fail
	 | mkthm( union(hyp th1, hyp th2) , mkequiv(u1,v1) )
     )? failwith `SYNTH` ;;

let ANAL th = mkthm(hyp th, mkconj(mkinequiv(u,v),mkinequiv(v,u)) )
	      where u,v = equivpair th ? failwith `ANAL` ;;

let HALF1, HALF2 = (SEL1 o ANAL), (SEL2 o ANAL) ;;

let REFL t = mkfreethm(mkequiv(t,t)) ;;

let SYM th = mkthm(hyp th, mkequiv(v,u))
	     where u,v = equivpair th ? failwith `SYM`  ;;

let TRANS(th1,th2) =
     (let mk1,t1,t2 = destaform(concl th1)
      and mk2,t2',t3 = destaform(concl th2) in
	not aconvterm(t2,t2') => fail
	 | mkthm( union(hyp th1, hyp th2) ,
	          (mk1=mkinequiv=>mk1|mk2)(t1,t3) )
     )? failwith `TRANS` ;;

let SUBST thxl w lhsthm =
     (aconvform(substinform(lhsxpairs thxl)w, concl lhsthm)
       => mkthm( itlist (\(th,x).\wl.union(hyp th, wl))
                        thxl (hyp lhsthm) ,
                 substinform(rhsxpairs thxl)w )
       | fail
     )? failwith `SUBST` ;;



let EXT th =
     (let x,w = destquant(concl th) in
	let mk,t1,t2 = destaform w in
	  let u,x' = destcomb t1
	  and v,x'' = destcomb t2 in
	    not(x=x' & x=x'')
	    or freeinterm[x]u
	    or freeinterm[x]v  => fail
	     | mkthm( hyp th , mk(u,v) )
     )? failwith `EXT` ;;

let BETACONV t =
     (let f,v = destcomb t in
	let x,u = destabs f in
	  mkfreethm(mkequiv(t,substinterm[v,x]u))
     )? failwith `BETACONV` ;;

let ETACONV t =
     (let x,t' = destabs t in
	let u,x' = destcomb t' in
	  not x=x' or freeinterm[x]u => fail
	   | mkfreethm(mkequiv(t,u))
     )? failwith `ETACONV` ;;

let ABS x th =
     (let mk,u,t = destaform(concl th) in
	let f,x' = destcomb u in
	  not x=x'
	  or freeinterm[x]f
	  or exists(freeinform[x])(hyp th)  => fail
	   | mkthm( hyp th , mk(f,mkabs(x,t)) )
     )? failwith `ABS` ;;



let APTERM t th =
     (let mk,u,v = destaform(concl th) in
        mkthm( hyp th , mk(mkcomb(t,u),mkcomb(t,v)) )
     )? failwith `APTERM` ;;

let APTHM th t =
     (let mk,u,v = destaform(concl th) in
        mkthm( hyp th , mk(mkcomb(u,t),mkcomb(v,t)) )
     )? failwith `APTHM` ;;

let LAMGEN x th =
       (exists(freeinform[x])(hyp th) => fail
	 | mkthm( hyp th , mk(mkabs(x,u),mkabs(x,v)) )
			   where mk,u,v = destaform(concl th)
       )? failwith `LAMGEN`  ;;



let MIN t = mkfreethm(mkinequiv(mkconst(`UU`,typeof t), t)) ;;

let MINAP t =
     not isUU(fst(destcomb t)) => failwith `MINAP`
      | mkfreethm(mkequiv(t,mkconst(`UU`,typeof t))) ;;

let MINFN t =
     not isUU(snd(destabs t)) => failwith `MINFN`
      | mkfreethm(mkequiv(t,mkconst(`UU`,typeof t))) ;;



let FIXPT f = mkfreethm(mkequiv(t,mkcomb(f,t)))
				where t = "FIX ↑f"
					  ? failwith `FIXPT`  ;;

let INDUCT funxl w (th1,th2) =
    let wl' = disch(w, hyp th2) in
      (forall(\(fun,x).admitsinduction(w,x))funxl
       & aconvform(concl th1, substinform(uupairs funxl)w)
       & aconvform(concl th2, substinform(steppairs funxl)w)
       & not exists(freeinform(map snd funxl))wl'
              => mkthm( union(hyp th1, wl') ,
                        substinform(fixpairs funxl)w  )
              | fail
      )? failwith `INDUCT`  ;;


let SELCONV t = (mkfreethm(mkequiv(t,t'))
		 where t' = tok=`FST`=>t1|tok=`SND`=>t2|fail
			    where (tok,()),(t1,t2)
				    = (destconst # destpair)(destcomb t)
		)? failwith `SELCONV` ;;

let PAIRCONV t =
    (let u1,u2 = destpair t in
       isUU u1 & isUU u2 => (isUU t => fail
	                       | let uu = mkconst(`UU`, typeof t) in
	                         mkfreethm(mkequiv(t,uu))
	                    )
       |let sel1,t1 = destcomb u1
        and sel2,t2 = destcomb u2 in
          let tok1,() = destconst sel1
          and tok2,() = destconst sel2 in
            tok1=`FST` & tok2=`SND` & aconvterm(t1,t2)
		      => mkfreethm(mkequiv(t,t1))
		      | fail
    )? failwith `PAIRCONV`  ;;



let CONDCONV t = (mkfreethm(mkequiv(t,t'))
		  where t' = let tr,t1,t2 = destcond t in
			      let tok,() = destconst tr in
			       tok=`TT` => t1 |
			       tok=`FF` => t2 |
			       tok=`UU` => mkconst(`UU`,typeof t)
					| fail
		 )? failwith `CONDCONV`;;

let CONDTRCONV t =
     (let cond,c = destcomb t in
      not(fst(destconst cond))=`COND` => fail
       |(mkfreethm(mkequiv(t,t'))
	 where t' =  let tok,() = destconst c in
		      tok=`UU` => mkconst(`UU`, typeof t)
		       | let x,y = mkvar(`X`,ty),mkvar(`Y`,ty)
				   where ty,() = destfuntype(typeof t)
		         in mkabs(x,mkabs(y,(tok=`TT` => x |
				             tok=`FF` => y | fail) ))
	)
     )? failwith `CONDTRCONV` ;;

let CASES t (th1,th2,th3) =
      let wl1,w1 = destthm th1
      and wl2,w2 = destthm th2
      and wl3,w3 = destthm th3 in
	not(aconvform(w1,w2) & aconvform(w1,w3)) => failwith `CASES`
	 |( mkthm( union(wl1',union(wl2',wl3')) , w1)
			where wl1' = disch(eqtt t, wl1)
			  and wl2' = disch(eqff t, wl2)
			  and wl3' = disch(equu t, wl3) ) ;;


%
CONTR : form -> thm -> thm
         w

   A ]- t1 =< t2
---------------------
   A ]- w

Provided: (1) t1 and t2 are both members of {"UU:tr","TT","FF"⎇ 
          (2) t1 and t2 are different
          (3) if t1="UU" then the connective isn't <<.
%

let CONTR w th =
(let fml,f = destthm th
 in
 let (),t1,t2 = destaform f
 and trl      = [tt;ff;uutr]
 in
 if   t1=t2
 then fail
 if   mem t1 trl & mem t2 trl & (isequiv f or not(t1=uutr))
 then mkthm(fml,w)
 else fail)
?
failwith `CONTR`;;


let ISCONV,OUTCONV =
     let destlr (ltok,rtok) t = (let tok,() = destconst t in
				   tok=ltok => `L` |
				   tok=rtok => `R` | fail )
     in
     let destISlr = destlr(`ISL`,`ISR`)
     and destOUTlr = destlr(`OUTL`,`OUTR`)
     and destINlr = destlr(`INL`,`INR`)
     in
     let ISorOUT (tok,dest) t =
	  (let t' = (let c1,v = destcomb t in
		     let lr1 = dest c1 in
		       isUU v => mkconst(`UU`, typeof t)
		       |(let c2,t' = destcomb v in
			 let lr2 = destINlr c2 in
			   tok = `ISCONV`
			     => (lr1=lr2 => tt|ff)
			     |  (lr1=lr2 => t'|mkconst(`UU`,typeof t))
		    ))
	   in mkfreethm(mkequiv(t,t'))
	  )? failwith tok
     in
     ( ISorOUT(`ISCONV`,destISlr), ISorOUT(`OUTCONV`,destOUTlr) )  ;;


let INRULE th =
   (let t1,t2 = equivpair th  in
     let (istok,()),t = (destconst # I)(destcomb t1)
     and trtok,() = destconst t2   in
      not(istok=`ISL` or istok=`ISR`) => fail
       | let w' = trtok=`UU` => "↑t == UU" |
		  istok=(trtok=`TT`=>`ISL`|trtok=`FF`=>`ISR`|fail)
		     => "INL(OUTL ↑t) == ↑t"
		     |  "INR(OUTR ↑t) == ↑t"
         in mkthm( hyp th , w' )
   )? failwith `INRULE` ;;


let DOT t =  typeof t = dottype => mkfreethm(mkequiv(t,uudot))
				| failwith `DOT` ;;
