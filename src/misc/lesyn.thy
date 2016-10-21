





	THEORY LESYN


newtypes [ ``NEXP = NCON + NEXP'`` ;
	   ``NEXP' = IDEN + CNEXP`` ;
	   ``CNEXP = NOP # NEXPPR`` ;
	   ``NEXPPR = NEXP # NEXP`` ] ;;

newtypes [ ``TEXP = TCON + CTEXP`` ;
	   ``CTEXP = TOP # NEXPPR`` ] ;;

newconstant ( `isncon` , ":NEXP->tr" ) ;;

newconstant ( `isiden` , ":NEXP->tr" ) ;;

newconstant ( `iscnexp` , ":NEXP->tr" ) ;;

newconstant ( `mkncon` , ":NCON->NEXP" ) ;;

newconstant ( `mkiden` , ":IDEN->NEXP" ) ;;

newconstant ( `mkcnexp` , ":CNEXP->NEXP" ) ;;

newconstant ( `destncon` , ":NEXP->NCON" ) ;;

newconstant ( `destiden` , ":NEXP->IDEN" ) ;;

newconstant ( `destcnexp` , ":NEXP->CNEXP" ) ;;

newconstant ( `expfun` , ":(NEXP->NEXP)->(NEXP->NEXP)" ) ;;

NEWAXIOMS();;

isn  "!e:NEXP. isncon e == ISL e :tr"

isi  "!e:NEXP. isiden e == ISL e=>FF|ISL(OUTR e :NEXP') :tr"

isc  "!e:NEXP. iscnexp e == ISL e=>FF|ISR(OUTR e :NEXP') :tr"

mkn  "!n:NCON. mkncon n == INL n :NEXP"

mki  "!i:IDEN. mkiden i == INR(INL i :NEXP') :NEXP"

mkc  "!c:CNEXP. mkcnexp c == INR(INR c :NEXP') :NEXP"

destn  "!e:NEXP. destncon e == OUTL e :NCON"

desti  "!e:NEXP. destiden e == OUTL(OUTR e :NEXP') :IDEN"

destc  "!e:NEXP. destcnexp e == OUTR(OUTR e :NEXP') :CNEXP"

expax1  "!e:NEXP. FIX expfun e == e"

expax2  "!e:NEXP. !f:NEXP->NEXP. expfun f e == isncon e=>mkncon(destncon e)|(isiden e=>mkiden(destiden e)|(iscne~
xp e=>mkcnexp(FST(destcnexp e), (f(FST(SND(destcnexp e) :NEXPPR)), f(SND(SND(destcnexp e) :NEXPPR))))|UU:NEXP))"
