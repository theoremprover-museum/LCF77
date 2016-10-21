
let vary wl v = variant (v, formlfrees wl) ;;


let NEXPINDUCTAC e (F,ss,Fl) =
 ((  [  w "UU:NEXP" , ss , Fl ; w "mkncon↑n" , ss , Fl ;
       w "mkiden↑i" , ss , Fl ; 
       w "mkcnexp(↑nop,↑e1,↑e2)" , ss , w1.w2.Fl  ] ,
  \[th1;th2;th3;th4] .  NEXPINDUCT(n,i,nop,e1,e2)e F 
                        [th1;th2;th3;DISCH w1 (DISCH w2 th4)] 
   ) where w1,w2 = w e1, w e2  )
  where  w t = substinform[t,e] F
  and [n;i;nop;e1;e2] = map(vary(F.Fl))
             [ "n:NCON" ; "i:IDEN" ; "nop:NOP" ; "e1:NEXP";"e2:NEXP"] ;;



let CONTRTAC g =
 (let w1,w2 = destimp(fst g) in
  let th = CONTR w2 (ASSUME w1) in [], K(DISCH w1 th)
 ) ?
 ( [g], hd) ;;

let ADDSIMPTAC swl (w,ss,wl) =
 SIMPTAC(w, itlist f swl ss, wl) where  f sw = ssadd(ASSUME sw) ;;

let ANTETAC(w,ss,wl) =
 (let w1,w2 = destimp w  in
  [ w2, ssadd(ASSUME w1)ss, w1.wl] , DISCH w1 o hd
 ) ?
 ( [w,ss,wl] , hd ) ;;

let CONDCASESTAC(fm,ss,fml) =
 let tm = findterminform p fm
   where p t = iscomb t &
     (let t1,t2 = destcomb t in  isconst t1 & fst(destconst t1)=`COND`
                     & freeinform[t2]fm )
 in CASESTAC(snd(destcomb tm))(fm,ss,fml)  ;;

let STEPTAC g = (SIMPTAC THEN (CONDCASESTAC ORELSE IDTAC) THEN SIMPTAC
                  THEN CONTRTAC THEN ANTETAC
                THEN ADDSIMPTAC[w1;w2])g  where (),(),w1.w2.() = g ;;

let SIMPANTETAC = SIMPTAC THEN ANTETAC THEN SIMPTAC ;;

let NEXPINDUCTAC' e = NEXPINDUCTAC e THENL
          [SIMPANTETAC;SIMPANTETAC;SIMPANTETAC; STEPTAC] ;;

