
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
