





	THEORY PROPT


newconstant ( `NOTP` , ":tr->tr" ) ;;

newconstant ( `ORP` , ":tr->(tr->tr)" ) ;;

NEWAXIOMS();;

AXNOTP  "NOTP == \p:tr.p=>FF|TT"

AXORP  "ORP == \p:tr.\q:tr.p=>(q=>TT|TT)|q"
