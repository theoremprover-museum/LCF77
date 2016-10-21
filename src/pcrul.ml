
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
