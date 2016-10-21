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
