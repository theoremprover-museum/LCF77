
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
