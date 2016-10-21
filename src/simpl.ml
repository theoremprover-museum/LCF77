
(TML)

let termmatch (vars,tyvars) p = termmatch(vars,tyvars,p) ;;




let KAXTRUTH = K AXTRUTH;;

let XTRANS (th1,th2) = \th3.TRANS(th1,TRANS(th3,th2)) ;;

	% DEDUCE :  (w,pww')  :-->   ..]-w IMP w'

	 IMPP: (wa,paa',pc'c) :--> ..]-wa' IMP wc' :--> ..]-wa IMP wc   

	 QUANTP :  (x,pww')  :-->  ..]-!x.w  :-->  ..]-!x.w'   %

let DEDUCE(w,p) = DISCH w (p(ASSUME w)) ;;

let IMPP(w,p1,p2) = \th.DEDUCE(w,(p2 o (MP th) o p1)) ;;

let QUANTP(x,p) = ((GEN x) o p o (SPEC x)) ;;



let ALPHA w th =               % for use in tautaform %
      let wl,w' = destthm th  in
        aconvform(w,w') => mkthm(wl,w) | failwith `ALPHA`  ;;

let ALPHABV x t =          % fails unless t is a \-abstraction %
      let x' = variant(x,termfrees t)  in
        ABS x' (BETACONV(mkcomb(t,x')))

and ALPHAQ x th =          % fails unless concl(th) is quantified %
      let x' = variant(x,formfrees(concl th))  in
        MP (DEDUCE(concl th,(GEN x' o SPEC x'))) th   ;;

let SPECQ th = 
      let wl,w = destthm th  in
	let x,() = destquant w  in
	  SPEC (variant(x,formlfrees(w.wl))) th   ;;



let INSTFN(instlist,insttylist) = INST instlist o INSTTYPE insttylist ;;

let destimpequiv w =  let wa,wc = destimp w ? (truth,w)
                      in  (wa, destequiv wc)  ;;

let disjsrvars th =
     let hypfrees = formlfrees(hyp th)
     and (),p,() = destimpequiv(concl th)
     in
     let instvars = subtract(termfrees p, hypfrees)
     in
       INST (map(\x.(genvar(typeof x),x))instvars) th   ;;

let gensrinfo th =
     let srthm = disjsrvars th
     in let hypfrees = formlfrees(hyp srthm)
        and hyptyvars = formltyvars(hyp srthm)
        and (),p,() = destimpequiv(concl srthm)
        in  srthm , termmatch(hypfrees,hyptyvars)p  ;;

let equivsimpof th =
     let srthm,matchp = gensrinfo th
     in
       \t. let th' = INSTFN (matchp t) srthm
           in  snd(equivpair th') , th'      ;;



deftype var = term;;
deftype term = var;;

deftype repsimpset = (term -> (term # thm)) list  ;;

letref SS = []:repsimpset              % for rebinding dynamically %
   and CBL = []:var list  ;;           % during simplification     %

let BindSS (ss:repsimpset, f:.->*) =
      let SS' = SS  in
	(let res = SS:=ss ; f()
	 in  SS:=SS' ; res
	)?\tok (SS:=SS' ; failwith tok)

and BindCBL (cbl:var list, f:.->*) =
      let CBL' = CBL  in
	(let res = CBL:=cbl ; f()
	 in  CBL:=CBL' ; res
	)?\tok (CBL:=CBL' ; failwith tok)  ;;

let BindSSandCBL(ss,cbl,f) = BindSS(ss,(\().BindCBL(cbl,f))) ;;

let searchsimp t =
	letref ss = SS  in
	   hd ss t ! (().ss := ss) ;;

let itsearchsimp t =
	letref t',th = searchsimp t in
	   (loop  t',th := (t'',TRANS(th,th')
			    where t'',th' = searchsimp t')
	   )? (t',th) ;;

letrec fullsimp t = topsimp t ? subsimp t

and topsimp t =
	   let t',th = itsearchsimp t in
	     (let t'',th' = subsimp t' in
		 (t'',TRANS(th,th'))
	     ) ? (t',th)

and subsimp t =
      failwith phylumofterm t
	??``comb``
	   (let u,v = destcomb t in
	     (let u',thuu' = fullsimp u in
	      let t1,th1 = mkcomb(u',v), APTHM thuu' v in
	       (let t2,th2 = topsimp t1 ? randsimp (u',v) in
		   (t2, TRANS(th1,th2) )
	       ) ? (t1, th1)
	     )?
	     randsimp (u,v)  )
	??``abs``
	   (let x,u = destabs t in
	    let y = genvar(typeof x) in
	    let v = substinterm[y,x]u in
	      let v',thvv' = BindCBL(y.CBL,(\().fullsimp v)) in
	        let tht1t2 = LAMGEN y thvv' in
		let t1,t2 = destequiv(concl tht1t2) in
		  transtopsimp(TRANS(SYM(ALPHABV x t1),
				     TRANS(tht1t2,ALPHABV x t2))) )

and randsimp (u,v) =
	   let v',thvv' = fullsimp v in
	      transtopsimp(APTERM u thvv')

and transtopsimp th =
	   let t = rhs(concl th) in
	     (let t',th' = topsimp t in
		 (t',TRANS(th,th'))
	     ) ? (t,th)            ;;

let simptm t = fullsimp t ? (t,REFL t)  ;;



	% tautineq :   (t1,t2)   :-->    ]- t1 << t2
		    provided this follows by monotonicity and
		    transitivity from the minimality of UU

	  tautaform :      w    :-->    ]- w
		    provided w is an atomic formula provable by
		    tautineq, or by reflexivity or alpha-conversion %

letrec tautineq (t1,t2) =
	t1=t2 => HALF1(REFL t1)
	 |(failwith phylumofterm t1
	     ??``const`` (isUU t1 => MIN t2 | fail)
	     ??``comb`` (let u1,v1 = destcomb t1
			 and u2,v2 = destcomb t2 in
			   let th1 = tautineq(u1,u2)
			   and th2 = tautineq(v1,v2) in
			     TRANS(APTHM th1 v1, APTERM u2 th2) )
	     ??``abs`` (let x1,u1 = destabs t1
		        and x2,u2 = destabs t2 in
			  LAMGEN x1 (tautineq(u1,substinterm[x1,x2]u2))
	  )            )   ;;

let tautaform w =
      ALPHA w (REFL(fst(destequiv w)) ? tautineq(destinequiv w)) ;;



	% trivcontr(wa,wc):   ..]-wa   :-->   ..]-wc
			   provided a standard contradiction (see CONTR)
			   is contained in and provable from wa     %

let trivcontr(wa,wc) = triv wa whererec triv wa =
      failwith phylumofform wa
	??``quant`` (triv wb o SPEC x
		     where x,wb = destquant wa )
	??``conj`` ((triv w1 o SEL1) ? (triv w2 o SEL2)
		    where w1,w2 = destconj wa )
	??``equiv inequiv`` MP (DEDUCE(wa,CONTR wc))  ;;



	% trivimp1(wa,wc1): returns that composition of SEL1 and SEL2
			    which when applied to "..]-wa" yields
			    "..]-wc1" , provided wc1 (assumed not to be
			    a conjunction) is a conjunct of wa

	  trivimp(wa,wc):   ..]-wa  :-->  ..]-wc
		    provided every conjunct of wc is a conjunct of wa %

letrec trivimp1(wa,wc1) =
	     let wa1,wa' = destconj1 wa ? fail in
		aconvform(wa1,wc1) => (istruth wa' => I | SEL1)
				    |  (trivimp1(wa',wc1) o SEL2) ;;

letrec trivimp(wa,wc) =
	     istruth wc => KAXTRUTH
	      |let wc1,wc' = destconj1 wc in
	       let p1,p' = trivimp1(wa,wc1), trivimp(wa,wc') in
		 (CONJ oo (p1,p'))   ;;



let SSaddante w = add (ASSUME w) SS whererec add th ss =
      failwith phylumofform(concl th)
	??``quant`` add (SPECQ th) ss
	??``conj`` add (SEL1 th) (add (SEL2 th) ss)
	??``equiv``(let t1,t2 = destequiv(concl th) in
		      isconst t2 => equivsimpof th .ss |
		      isconst t1 => equivsimpof(SYM th).ss | ss )
	? ss   ;;



let simpaform (mk,u,v) =
        let u',thuu' = simptm u
	and v',thvv' = simptm v in
          let w' = mk(u',v')
	  and pww' = XTRANS(SYM thuu', thvv')
	  and pw'w = XTRANS(thuu', SYM thvv') in
	        (let thw' = tautaform w' in
		    ( truth , KAXTRUTH , K(pw'w thw') )
		) ? ( w' , pww' , pw'w )   ;;

letrec simpfm w =
	 failwith phylumofform w
	   ??``equiv inequiv``  simpaform (destaform w)
	   ??``conj``  simpconj (destconj w)
	   ??``imp``  simpimp (destimp w)
	   ??``quant``  simpquant (destquant w)
	   ??``truth``  (truth, KAXTRUTH, KAXTRUTH)

and simpconj (w1,w2) =
	let w1',p11',p1'1 = simpfm w1
	and w2',p22',p2'2 = simpfm w2 in
	  ( mkconj(w1',w2') ,
	    (CONJ oo ((p11' o SEL1),(p22' o SEL2))) ,
	    (CONJ oo ((p1'1 o sel1'),(p2'2 o sel2')))
	    	     where sel1',sel2'
			    = istruth w1' => (KAXTRUTH,I) |
			      istruth w2' => (I,KAXTRUTH) | (SEL1,SEL2)
	  )

and simpimp (wa,wc) =
	let wa',paa',pa'a = simpfm wa in
	 (let pa'c = trivcontr(wa',wc) in
	    ( truth , KAXTRUTH , K(DEDUCE(wa,(pa'c o paa'))) )
	 )?
	  (let wc',pcc',pc'c = BindSS(SSaddante wa',(\().simpfm wc))
	   in
	   let paca'c' = IMPP(wa',I,pcc') o IMPP(wa',pa'a,I)
	   and pa'c'ac = IMPP(wa,paa',I) o IMPP(wa',I,pc'c)
	   in
	     (let pa'c' = trivimp(wa',wc') in
		( truth , KAXTRUTH , K(pa'c'ac(DEDUCE(wa',pa'c'))) )
	     )?
		( mkimp(wa',wc') , paca'c' , pa'c'ac )
          )

and simpquant (x,wb) =
	let y = genvar(typeof x) in
	let w1 = substinform[y,x]wb in
	let w1',p11',p1'1 = BindCBL(y.CBL,(\().simpfm w1)) in
	  istruth w1'
	   => ( truth , KAXTRUTH , (ALPHAQ x o GEN y o p1'1) )
	   | let x' = variant(x,formfrees(mkquant(y,w1'))) in
	       ( mkquant(x',substinform[x',y]w1') ,
	         (ALPHAQ x' o QUANTP(y,p11')) ,
	         (ALPHAQ x o QUANTP(y,p1'1))
	       )  ;;




let condsimpof th =
     let srthm,matchp = gensrinfo th
     in
     let testinstpair =
          (\(u,x).mem(fst(destvar x))toks & freeinterm CBL u)
	  where toks =
		 let w,p,() = destimpequiv(concl srthm) in
		 let instvars = subtract(termfrees p,
					 formlfrees(hyp srthm)) in
		   map (fst o destvar) (intersect(formfrees w,instvars))
     in
        \t.(let instlist,insttylist = matchp t  in
              exists testinstpair instlist => fail
                | (let th' = INSTFN(instlist,insttylist)srthm
                   in let winst',(),s' = simpfm(fst(destimp(concl th')))
                      in  not istruth winst' => fail
                            | let th'' = MP th' (s' AXTRUTH)
                              in  snd(equivpair th'') , th''    )) ;;

letrec simpof th = 
         failwith phylumofform(concl th)
           ??``equiv`` equivsimpof th
           ??``imp`` condsimpof th
           ??``quant`` simpof(SPECQ th)    ;;

let quicksimpof thscheme =
      \t.let th = thscheme t in  snd(equivpair th) , th  ;;

let BETASIMP = quicksimpof BETACONV ;;
let ETASIMP = quicksimpof ETACONV ;;
let MINAPSIMP = quicksimpof MINAP ;;
let MINFNSIMP = quicksimpof MINFN ;;
let SELSIMP = quicksimpof SELCONV ;;
let PAIRSIMP = quicksimpof PAIRCONV ;;
let CONDSIMP = quicksimpof CONDCONV ;;
let CONDTRSIMP = quicksimpof CONDTRCONV ;;
let ISSIMP = quicksimpof ISCONV ;;
let OUTSIMP = quicksimpof OUTCONV ;;

let INSIMP t =
     let (intok,()),((outtok,()),t')
           = (destconst # ((destconst # I) o destcomb))(destcomb t)
     in
     let ttffL,ttffR = intok=`INL` & outtok=`OUTL` => (tt,ff) |
                       intok=`INR` & outtok=`OUTR` => (ff,tt) | fail
     in
       not eqtype(t,t') or freeinterm CBL t' => fail
        | let th = prove("ISL ↑t'",ttffL) ? prove("ISR ↑t'",ttffR)
                   where prove(u,ttff)
                              = (let u',th = simptm u
                                 in  u'=ttff => th | fail  )
          in  t' , INRULE th  ;;

letrec NBETASIMP n t =
     n=1 => BETASIMP t
     |(let u,v = destcomb t  in
        let u',thuu' = NBETASIMP (n-1) u   in
         let t1,th1 = mkcomb(u',v), APTHM thuu' v   in
          (let t2,th2 = BETASIMP t1   in
             (t2, TRANS(th1,th2))
          )? (t1,th1)
      );;

let simpcaseof t = failwith ( fst(destconst t) ? phylumofterm t )  ;;

let BASICSIMP t =
     failwith phylumofterm t
      ??``comb``
	 (simpcaseof (fst(destcomb t))
	   ??``abs`` BETASIMP
           ??``comb`` (letref n,t'=2,fst(destcomb(fst(destcomb t))) in
                       simpcaseof t'
                        !!``comb`` (n,t' := n+1,fst(destcomb t'))
                        ??``abs`` NBETASIMP n
			??``PAIR`` (n=2 => PAIRSIMP | fail)
			??``COND`` (n=3 => CONDSIMP | fail)   )
	   ??``UU`` MINAPSIMP
	   ??``COND`` CONDTRSIMP
	   ??``FST SND`` SELSIMP
	   ??``ISL ISR`` ISSIMP
           ??``INL INR`` INSIMP
	   ??``OUTL OUTR`` OUTSIMP    ) t
      ??``abs``
	 (simpcaseof (snd(destabs t))
	   ??``UU`` MINFNSIMP
	   ??``comb`` ETASIMP   ) t      ;;




abstype simpset = repsimpset

   with BASICSS = abssimpset [BASICSIMP]

    and EMPTYSS = abssimpset []

    and ssadd th ss = abssimpset( simpof th . repsimpset ss )

    and ssunion ss1 ss2 = abssimpset(repsimpset ss1 @ repsimpset ss2)

    and simpterm ss t = BindSSandCBL(repsimpset ss,nil,(\().simptm t))

    and simpform ss w = BindSSandCBL(repsimpset ss,nil,(\().simpfm w))
;;
