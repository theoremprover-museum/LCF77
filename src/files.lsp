COMMENT ⊗   VALID 00011 PAGES
C REC  PAGE   DESCRIPTION
C00001 00001
C00002 00002	% TYPEML.LSP, PPLAMB.LSP, TRAN.LSP, SIMPL.LSP, TRACE.LSP, TML.LSP %
C00005 00003	% LCFO.LSP %
C00007 00004	% LCFM.LSP %
C00015 00005	% DML.LSP %
C00019 00006	% WRITML.LSP %
C00023 00007	% THYFNS.LSP %
C00027 00008	% LIS.LSP %
C00030 00009	% OL0.LSP %
C00037 00010	% OL1.LSP %
C00044 00011	% OL2.LSP, OL3.LSP %
C00048 ENDMK
C⊗;
% TYPEML.LSP, PPLAMB.LSP, TRAN.LSP, SIMPL.LSP, TRACE.LSP, TML.LSP %

% TYPEML.LSP %

(INITMLTYPENV)


% PPLAMB.LSP %

(DEFPROP /. FINITE TYPECLASS)
(DEFPROP tr FINITE TYPECLASS)
(DEFPROP TR FINITE TYPECLASS)

(SETQ %CURRENT COR)


% TRAN.LSP %

(SETQ ISOMCLOSURE (CONS (FUNCTION CAR) (QUOTE ISOMCLOSURE)))
(SETQ ISOM (QUOTE %ISOM))
(SETQ DUMMY (QUOTE %DUMMY))
(SETQ EMPTY (QUOTE %EMPTY))
(SETQ NILL (QUOTE %NIL))
(SETQ TZERO
      (QUOTE
       (NIL (CAR (CAAR (CAAAR (CAAAAR) (CDAAAR)) (CDAAR (CADAAR) (CDDAAR)))
		 (CDAR (CADAR (CAADAR) (CDADAR)) (CDDAR (CADDAR) (CDDDAR))))
	    (CDR (CADR (CAADR (CAAADR) (CDAADR)) (CDADR (CADADR) (CDDADR)))
		 (CDDR (CADDR (CAADDR) (CDADDR)) (CDDDR (CADDDR) (CDDDDR)))))))


% SIMPL.LSP %

(DML' termmatch
      3
      MATCHCLOSURE
      (((term list) # ((type list) # term)) /-> (term /-> (((term # term) list) # ((type # type) list)))))


% TRACE.LSP %

(SETQ TRACELIST NIL)
(PUTPROP (QUOTE TRACE) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE TRACE)
	 (MKTIDY (QUOTE (((%a /-> %b) /-> ((%a /-> %b) # %c)) /-> ((%a /-> %b) /-> %c))))
	 (QUOTE MLTYPE))
(PUTPROP (QUOTE UNTRACE) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE UNTRACE) (MKTIDY (QUOTE ((%a /-> %b) /-> bool))) (QUOTE MLTYPE))


% TML.LSP %

(SETQ INITSECTION (QUOTE %MUSTBEATOM))
(SETQ %%P (SETQ %%E (SETQ INITENV (CONS INITSECTION NILL))))
(SETQ SECRET (ASCII 52))
(DEFPROP MK/-BEGIN begin TMLOP)
(DEFPROP MK/-END end TMLOP)
(SETQ %DUMP NIL)


% LCFO.LSP %

(SETQ LANG1 @OL1)
(SETQ LANG2 @OL2)
(SETQ LANGLP @OLLP)


(PUTPROP ENDCNRTOK 0 @OLLP)
(PUTPROP RPAREN 0 @OLLP)
(PUTPROP @/; 0 @OLLP)
(UNOP LPAREN @(LPARRTN))


(UNOP TRUTHTOK @(QUOTE (mk=truth)))
(UNOP QUANTTOK @(QUANTRTN))
(BINOP IMPTOK 10 @(WFFRTN (QUOTE IMPLICATION) (QUOTE mk=imp)
                          ARG1 (POP 10)))
(BINOP CONJTOK 20 @(WFFRTN (QUOTE CONJUNCTION) (QUOTE mk=conj)
                           ARG1 (POP 20)))


(BINOP EQTOK 30 @(TERMRTN (QUOTE EQUALITY) (QUOTE mk=equiv) ARG1 (POP 30)))
(BINOP INEQTOK 30 @(TERMRTN (QUOTE INEQUALITY) (QUOTE mk=inequiv)
                            ARG1 (POP 30)))


(BINOP COMMA 65 @(TERMRTN (QUOTE TUPLING) (QUOTE mk=pair)
                           ARG1 (POP 60)))
(UNOP LAMTOK @(LAMRTN))
(BINOP CONDLTOK 55 @(CONDLRTN ARG1))
(PUTPROP ELSETOK 50 @OLLP)

(BINOP COLON 75 @(OLTYPRTN))
(UNOP ANTICNRTOK @(METACALL))


(UNOP EXFIXSYM @(PROG2 (GNT) (MKOLATOM PTOKEN)))

(SETQ OLINPREC 70)

% LCFM.LSP %

(SETQ BASTYPES NIL)
(SETQ LANG1 (QUOTE ML1))
(SETQ LANG2 (QUOTE ML2))
(SETQ LANGLP (QUOTE MLLP))
(SETQ METAPREC 20)
(UNOP (QUOTE begin) (QUOTE (SECRTN (QUOTE MK/-BEGIN))))
(UNOP (QUOTE end) (QUOTE (SECRTN (QUOTE MK/-END))))
(UNOP TMLSYM (QUOTE (FAIL (QUOTE (STUFF MISSING)))))
(UNOP (QUOTE true) (QUOTE (QUOTE (MK/-BOOLCONST T))))
(UNOP (QUOTE false) (QUOTE (QUOTE (MK/-BOOLCONST NIL))))
(UNOP (QUOTE fail) (QUOTE (QUOTE (MK/-FAIL))))
(UNOP EXFIXSYM (QUOTE (EXFIXRTN)))
(UNOP TCNSTSYM (QUOTE (PROG2 (GNT) (LIST (QUOTE MK/-TOKCONST) PTOKEN))))
(UNOP LPAREN (QUOTE (LPARENRTN)))
(UNOP (QUOTE do) (QUOTE (LIST (QUOTE MK/-UNOP) (QUOTE do) (POP 410))))
(UNOP (QUOTE test) (QUOTE (TESTRTN)))
(UNOP (QUOTE if) (QUOTE (TESTRTN)))
(UNOP (QUOTE loop) (QUOTE (LIST (QUOTE MK/-TEST) NIL (CONS (QUOTE ITER) (POP 320)))))
(UNOP (QUOTE else) (QUOTE (LIST (QUOTE MK/-TEST) NIL (CONS (QUOTE ONCE) (POP 320)))))
(BNOP TP1SYM (QUOTE (LIST (QUOTE MK/-TRAP) ARG1 NIL (CONS (QUOTE ONCE) (POP 240)))))
(BNOP TP2SYM (QUOTE (LIST (QUOTE MK/-TRAP) ARG1 NIL (CONS (QUOTE ITER) (POP 240)))))
(BNOP TP3SYM (QUOTE (TRAPRTN (QUOTE ONCE))))
(BNOP TP4SYM (QUOTE (TRAPRTN (QUOTE ITER))))
(BNOP TP5SYM (QUOTE (TRAPBINDRTN (QUOTE ONCE))))
(BNOP TP6SYM (QUOTE (TRAPBINDRTN (QUOTE ITER))))
(UNOP LBRKT (QUOTE (LISTRTN)))
(BNOP SCOLON (QUOTE (SEQRTN)))
(UNOP (QUOTE let) (QUOTE (LETRTN (QUOTE MK/-LET))))
(UNOP (QUOTE letrec) (QUOTE (LETRTN (QUOTE MK/-LETREC))))
(UNOP (QUOTE letref) (QUOTE (LETRTN (QUOTE MK/-LETREF))))
(UNOP (QUOTE deftype) (QUOTE (LETRTN (QUOTE MK/-DEFTYPE))))
(UNOP (QUOTE lettype) (QUOTE (LETRTN (QUOTE MK/-DEFTYPE))))
(UNOP (QUOTE letrectype) (QUOTE (LETRTN (QUOTE MK/-DEFRECTYPE))))
(UNOP (QUOTE abstype) (QUOTE (LETRTN (QUOTE MK/-ABSTYPE))))
(UNOP (QUOTE absrectype) (QUOTE (LETRTN (QUOTE MK/-ABSRECTYPE))))
(BNOP (QUOTE in) (QUOTE (INRTN)))
(BNOP (QUOTE where) (QUOTE (WHERERTN (QUOTE MK/-LET))))
(BNOP (QUOTE whererec) (QUOTE (WHERERTN (QUOTE MK/-LETREC))))
(BNOP (QUOTE whereref) (QUOTE (WHERERTN (QUOTE MK/-LETREF))))
(BNOP (QUOTE wheretype) (QUOTE (WHERERTN (QUOTE MK/-DEFTYPE))))
(BNOP (QUOTE whererectype) (QUOTE (WHERERTN (QUOTE MK/-DEFRECTYPE))))
(BNOP (QUOTE whereabstype) (QUOTE (WHERERTN (QUOTE MK/-ABSTYPE))))
(BNOP (QUOTE whereabsrectype) (QUOTE (WHERERTN (QUOTE MK/-ABSRECTYPE))))
(UNOP LAMSYM (QUOTE (LAMBRTN)))
(BNOP ASGNSYM (QUOTE (ASSIGNRTN)))
(BNOP COMMA (QUOTE (DUPLRTN)))
(BNOP CONDLSYM (QUOTE (CONDRTN)))
(BNOP DISJSYM (QUOTE (APPLRTN 470 (QUOTE %or))))
(BNOP CONJSYM (QUOTE (APPLRTN 510 (QUOTE %&))))
(UNOP (QUOTE failwith) (QUOTE (FAILWITHRTN)))
(UNOP (QUOTE not) (QUOTE (LIST (QUOTE MK/-UNOP) (QUOTE not) (POP 530))))
(BNOP EQSYM (QUOTE (APPLRTN 550 EQSYM)))
(BNOP LTSYM (QUOTE (APPLRTN 610 LTSYM)))
(BNOP GTSYM (QUOTE (APPLRTN 570 GTSYM)))
(BNOP CONCSYM (QUOTE (APPLRTN 620 CONCSYM)))
(BNOP PERIOD (QUOTE (APPLRTN 640 PERIOD)))
(BNOP PLUSSYM (QUOTE (APPLRTN 710 PLUSSYM)))
(BNOP MNSSYM (QUOTE (APPLRTN 670 MNSSYM)))
(UNOP MNSSYM (QUOTE (LIST (QUOTE MK/-UNOP) (QUOTE %/-) (POP 760))))
(BNOP MULSYM (QUOTE (APPLRTN 750 MULSYM)))
(BNOP DIVSYM (QUOTE (APPLRTN 730 DIVSYM)))
(BNOP COLON (QUOTE (MLTYPRTN)))
(UNOP CNRSYM (QUOTE (CNRRTN)))
(PUTPROP TMLSYM 0 LANGLP)
(PUTPROP RPAREN 10 LANGLP)
(PUTPROP (QUOTE EQINDEC) 30 LANGLP)
(PUTPROP (QUOTE in) 60 LANGLP)
(PUTPROP (QUOTE and) 70 LANGLP)
(PUTPROP (QUOTE PERINLAM) 140 LANGLP)
(PUTPROP SCOLON 150 LANGLP)
(PUTPROP RBRKT 110 LANGLP)
(PUTPROP (QUOTE where) 200 LANGLP)
(PUTPROP (QUOTE whereref) 200 LANGLP)
(PUTPROP (QUOTE whererec) 200 LANGLP)
(PUTPROP (QUOTE wheretype) 200 LANGLP)
(PUTPROP (QUOTE whererectype) 200 LANGLP)
(PUTPROP (QUOTE whereabstype) 200 LANGLP)
(PUTPROP (QUOTE whereabsrectype) 200 LANGLP)
(PUTPROP (QUOTE PERINVS) 220 LANGLP)
(PUTPROP TP1SYM 250 LANGLP)
(PUTPROP TP2SYM 250 LANGLP)
(PUTPROP TP3SYM 260 LANGLP)
(PUTPROP TP4SYM 260 LANGLP)
(PUTPROP TP5SYM 260 LANGLP)
(PUTPROP TP6SYM 260 LANGLP)
(PUTPROP (QUOTE loop) 300 LANGLP)
(PUTPROP (QUOTE else) 300 LANGLP)
(PUTPROP (QUOTE then) 300 LANGLP)
(PUTPROP (QUOTE test) 310 LANGLP)
(PUTPROP (QUOTE if) 310 LANGLP)
(PUTPROP ASGNSYM 360 LANGLP)
(PUTPROP COMMA 400 LANGLP)
(PUTPROP ELSESYM 40 LANGLP)
(PUTPROP CONDLSYM 440 LANGLP)
(PUTPROP (QUOTE MLINFIX) 450 LANGLP)
(PUTPROP (QUOTE or) 500 LANGLP)
(PUTPROP CONJSYM 520 LANGLP)
(PUTPROP GTSYM 560 LANGLP)
(PUTPROP LTSYM 600 LANGLP)
(PUTPROP EQSYM 540 LANGLP)
(PUTPROP CONCSYM 630 LANGLP)
(PUTPROP PERIOD 650 LANGLP)
(PUTPROP MNSSYM 660 LANGLP)
(PUTPROP PLUSSYM 700 LANGLP)
(PUTPROP DIVSYM 720 LANGLP)
(PUTPROP MULSYM 740 LANGLP)
(PUTPROP COLON 770 LANGLP)
(PUTPROP (QUOTE PRIMARY) 1010 LANGLP)
% DML.LSP %

(MAPC (FUNCTION (LAMBDA (A) (EVLIST (QUOTE DML') (CAR A) 2 (CADR A) (CDDR A))))
      (QUOTE
       ((* *TIMES (int # int) /-> int)
	(// DIV (int # int) /-> int)
	(/+ *PLUS (int # int) /-> int)
	(/- *DIF (int # int) /-> int)
	(= EQUAL (%a # %a) /-> bool)
	(< *LESS (int # int) /-> bool)
	(> *GREAT (int # int) /-> bool)
	(%& AND (bool # bool) /-> bool)
	(%or OR (bool # bool) /-> bool)
	(/@ *APPEND ((%a list) # (%a list)) /-> (%a list))
	(/. CONS (%a # (%a list)) /-> (%a list)))))
(MAPC (FUNCTION (LAMBDA (A) (EVLIST (QUOTE DML') (CAR A) 1 (CADR A) (CDDR A))))
      (QUOTE
       ((%/- MINUS int /-> int)
	(not NOT bool /-> bool)
	(null NULL (%a list) /-> bool)
	(fst CAR (%a # %b) /-> %a)
	(snd CDR (%a # %b) /-> %b))))
(DMLC nil NIL (%a list))
(PUTPROP (QUOTE do) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE do) (MKTIDY (QUOTE (%a /-> /.))) (QUOTE MLTYPE))
(PUTPROP (QUOTE hd) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE hd) (MKTIDY (QUOTE ((%a list) /-> %a))) (QUOTE MLTYPE))
(PUTPROP (QUOTE tl) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE tl) (MKTIDY (QUOTE ((%a list) /-> (%a list)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE isl) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE isl) (MKTIDY (QUOTE ((%a /+ %b) /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE isr) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE isr) (MKTIDY (QUOTE ((%a /+ %b) /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE outl) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE outl) (MKTIDY (QUOTE ((%a /+ %b) /-> %a))) (QUOTE MLTYPE))
(PUTPROP (QUOTE outr) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE outr) (MKTIDY (QUOTE ((%a /+ %b) /-> %b))) (QUOTE MLTYPE))
(PUTPROP (QUOTE inl) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE inl) (MKTIDY (QUOTE (%a /-> (%a /+ %b)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE inr) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE inr) (MKTIDY (QUOTE (%b /-> (%a /+ %b)))) (QUOTE MLTYPE))
(SETQ EMPTYTOK (GENSYM))
(PUTPROP (QUOTE explode) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE explode) (MKTIDY (QUOTE (token /-> (token list)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE implode) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE implode) (MKTIDY (QUOTE ((token list) /-> token))) (QUOTE MLTYPE))
(PUTPROP (QUOTE mlinfix) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE mlinfix) (MKTIDY (QUOTE (token /-> /.))) (QUOTE MLTYPE))
(PUTPROP (QUOTE mlcinfix) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE mlcinfix) (MKTIDY (QUOTE (token /-> /.))) (QUOTE MLTYPE))
(DML' gentok 0 GENSYM (/. /-> tok))
(PUTPROP (QUOTE mlin) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE mlin) (MKTIDY (QUOTE ((token # bool) /-> /.))) (QUOTE MLTYPE))

% WRITML.LSP %

(PUTPROP (QUOTE typemode) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE typemode) (MKTIDY (QUOTE (bool /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE printint) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE printint) (MKTIDY (QUOTE (int /-> int))) (QUOTE MLTYPE))
(PUTPROP (QUOTE printtok) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE printtok) (MKTIDY (QUOTE (token /-> token))) (QUOTE MLTYPE))
(PUTPROP (QUOTE printbool) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE printbool) (MKTIDY (QUOTE (bool /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE printdot) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE printdot) (MKTIDY (QUOTE (/. /-> /.))) (QUOTE MLTYPE))
(PUTPROP (QUOTE printterm) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE printterm) (MKTIDY (QUOTE (term /-> term))) (QUOTE MLTYPE))
(PUTPROP (QUOTE printform) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE printform) (MKTIDY (QUOTE (form /-> form))) (QUOTE MLTYPE))
(PUTPROP (QUOTE printthm) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE printthm) (MKTIDY (QUOTE (thm /-> thm))) (QUOTE MLTYPE))
(PUTPROP (QUOTE printtype) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE printtype) (MKTIDY (QUOTE (type /-> type))) (QUOTE MLTYPE))
(MAPCAR	(FUNCTION (LAMBDA (X) (PUTPROP (CAR X) (CDR X) (QUOTE CLOSES))))
	(QUOTE
	 ((imp quant1 imp) (conj quant1 imp)
			   (pair abs1 pair)
			   (cond1 cond1)
			   (cond2 abs1 cond1 pair)
			   (listcomb abs1 listcomb infcomb cond1 pair typed)
			   (infcomb abs1 listcomb infcomb cond1 pair typed)
			   (funtype funtype)
			   (sumtype sumtype funtype)
			   (prodtype prodtype sumtype funtype))))
(MAPCAR	(FUNCTION (LAMBDA (X) (PUTPROP (CAR X) (CDR X) (QUOTE PRINFIX))))
	(LIST (CONS (QUOTE typed) COLON)
	      (CONS (QUOTE quant1) (RSPACED PERIOD))
	      (CONS (QUOTE abs1) PERIOD)
	      (CONS (QUOTE imp) (SPACED IMPTOK))
	      (CONS (QUOTE conj) (SPACED CONJTOK))
	      (CONS (QUOTE equiv) (SPACED EQTOK))
	      (CONS (QUOTE inequiv) (SPACED INEQTOK))
	      (CONS (QUOTE pair) (RSPACED COMMA))
	      (CONS (QUOTE cond1) CONDLTOK)
	      (CONS (QUOTE cond2) ELSETOK)
	      (CONS (QUOTE funtype) ARROWTOK)
	      (CONS (QUOTE prodtype) PRODTOK)
	      (CONS (QUOTE sumtype) SUMTOK)))
(SETQ EMPTYPRINT EMPTYTOK)
(SETQ %PRINTTYPES NIL)
% THYFNS.LSP %

(PUTPROP (QUOTE easytype) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE easytype) (MKTIDY (QUOTE (type /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE finitetype) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE finitetype) (MKTIDY (QUOTE (type /-> bool))) (QUOTE MLTYPE))
(SETQ COR (SETQ DASH (QUOTE /-)))
(PUTPROP (QUOTE draftin) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE draftin) (MKTIDY (QUOTE (token /-> /.))) (QUOTE MLTYPE))
(PUTPROP (QUOTE newparent) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE newparent) (MKTIDY (QUOTE (token /-> /.))) (QUOTE MLTYPE))
(PUTPROP (QUOTE newtypes) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE newtypes) (MKTIDY (QUOTE (((token list) list) /-> /.))) (QUOTE MLTYPE))
(PUTPROP (QUOTE newconstant) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE newconstant) (MKTIDY (QUOTE ((token # type) /-> /.))) (QUOTE MLTYPE))
(PUTPROP (QUOTE newolinfix) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE newolinfix) (MKTIDY (QUOTE ((token # type) /-> /.))) (QUOTE MLTYPE))
(PUTPROP (QUOTE newolcinfix) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE newolcinfix) (MKTIDY (QUOTE ((token # type) /-> /.))) (QUOTE MLTYPE))
(PUTPROP (QUOTE NEWAXIOMS) 0 (QUOTE NUMARGS))
(PUTPROP (QUOTE NEWAXIOMS) (MKTIDY (QUOTE (/. /-> /.))) (QUOTE MLTYPE))
(PUTPROP (QUOTE newaxiom) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE newaxiom) (MKTIDY (QUOTE ((token # form) /-> thm))) (QUOTE MLTYPE))
(PUTPROP (QUOTE newfact) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE newfact) (MKTIDY (QUOTE ((token # thm) /-> thm))) (QUOTE MLTYPE))
(PUTPROP (QUOTE AXIOM) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE AXIOM) (MKTIDY (QUOTE ((token # token) /-> thm))) (QUOTE MLTYPE))
(PUTPROP (QUOTE FACT) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE FACT) (MKTIDY (QUOTE ((token # token) /-> thm))) (QUOTE MLTYPE))
(PUTPROP (QUOTE firm) 0 (QUOTE NUMARGS))
(PUTPROP (QUOTE firm) (MKTIDY (QUOTE (/. /-> /.))) (QUOTE MLTYPE))
(PUTPROP (QUOTE maketheory) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE maketheory) (MKTIDY (QUOTE (token /-> /.))) (QUOTE MLTYPE))

% LIS.LSP %

(DML' length 1 LENGTH ((%a list) /-> int))
(PUTPROP (QUOTE twoof) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE twoof) (MKTIDY (QUOTE ((%a list) /-> (%a # %a)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE threeof) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE threeof) (MKTIDY (QUOTE ((%a list) /-> (%a # (%a # %a))))) (QUOTE MLTYPE))
(DML' rev 1 REVERSE ((%a list) /-> (%a list)))
(DML' mem 2 MEMBER ((%a # (%a list)) /-> bool))
(PUTPROP (QUOTE flat) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE flat) (MKTIDY (QUOTE (((%a list) list) /-> (%a list)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE map) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE map) (MKTIDY (QUOTE (((%a /-> %b) # (%a list)) /-> (%b list)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE exists) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE exists) (MKTIDY (QUOTE (((%a /-> bool) # (%a list)) /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE forall) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE forall) (MKTIDY (QUOTE (((%a /-> bool) # (%a list)) /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE revitlist) 3 (QUOTE NUMARGS))
(PUTPROP (QUOTE revitlist) (MKTIDY (QUOTE (((%a /-> (%b /-> %b)) # ((%a list) # %b)) /-> %b))) (QUOTE MLTYPE))
(PUTPROP (QUOTE find) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE find) (MKTIDY (QUOTE (((%a /-> bool) # (%a list)) /-> %a))) (QUOTE MLTYPE))
(PUTPROP (QUOTE tryfind) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE tryfind) (MKTIDY (QUOTE (((%a /-> %b) # (%a list)) /-> %b))) (QUOTE MLTYPE))
(PUTPROP (QUOTE filter) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE filter) (MKTIDY (QUOTE (((%a /-> bool) # (%a list)) /-> (%a list)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE mapfilter) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE mapfilter) (MKTIDY (QUOTE (((%a /-> %b) # (%a list)) /-> (%b list)))) (QUOTE MLTYPE))

% OL0.LSP %

(PUTPROP (QUOTE mkquant) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE mkquant) (MKTIDY (QUOTE ((term # form) /-> form))) (QUOTE MLTYPE))
(DML' mkimp 2 mk=imp ((form # form) /-> form))
(DML' mkconj 2 mk=conj ((form # form) /-> form))
(PUTPROP (QUOTE mkequiv) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE mkequiv) (MKTIDY (QUOTE ((term # term) /-> form))) (QUOTE MLTYPE))
(PUTPROP (QUOTE mkinequiv) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE mkinequiv) (MKTIDY (QUOTE ((term # term) /-> form))) (QUOTE MLTYPE))
(DML' mktruth 0 mk=truth (/. /-> form))
(PUTPROP (QUOTE destquant) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE destquant) (MKTIDY (QUOTE (form /-> (term # form)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE destimp) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE destimp) (MKTIDY (QUOTE (form /-> (form # form)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE destconj) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE destconj) (MKTIDY (QUOTE (form /-> (form # form)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE destequiv) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE destequiv) (MKTIDY (QUOTE (form /-> (term # term)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE destinequiv) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE destinequiv) (MKTIDY (QUOTE (form /-> (term # term)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE desttruth) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE desttruth) (MKTIDY (QUOTE (form /-> /.))) (QUOTE MLTYPE))
(PUTPROP (QUOTE mkabs) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE mkabs) (MKTIDY (QUOTE ((term # term) /-> term))) (QUOTE MLTYPE))
(PUTPROP (QUOTE mkcomb) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE mkcomb) (MKTIDY (QUOTE ((term # term) /-> term))) (QUOTE MLTYPE))
(PUTPROP (QUOTE mkvar) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE mkvar) (MKTIDY (QUOTE ((token # type) /-> term))) (QUOTE MLTYPE))
(PUTPROP (QUOTE mkconst) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE mkconst) (MKTIDY (QUOTE ((token # type) /-> term))) (QUOTE MLTYPE))
(PUTPROP (QUOTE destabs) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE destabs) (MKTIDY (QUOTE (term /-> (term # term)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE destcomb) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE destcomb) (MKTIDY (QUOTE (term /-> (term # term)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE destvar) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE destvar) (MKTIDY (QUOTE (term /-> (token # type)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE destconst) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE destconst) (MKTIDY (QUOTE (term /-> (token # type)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE typeof) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE typeof) (MKTIDY (QUOTE (term /-> type))) (QUOTE MLTYPE))
(DML' mksumtype 2 mk=sumtype ((type # type) /-> type))
(DML' mkprodtype 2 mk=prodtype ((type # type) /-> type))
(DML' mkfuntype 2 mk=funtype ((type # type) /-> type))
(PUTPROP (QUOTE mkconsttype) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE mkconsttype) (MKTIDY (QUOTE (token /-> type))) (QUOTE MLTYPE))
(PUTPROP (QUOTE mkvartype) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE mkvartype) (MKTIDY (QUOTE (token /-> type))) (QUOTE MLTYPE))
(PUTPROP (QUOTE destsumtype) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE destsumtype) (MKTIDY (QUOTE (type /-> (type # type)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE destprodtype) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE destprodtype) (MKTIDY (QUOTE (type /-> (type # type)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE destfuntype) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE destfuntype) (MKTIDY (QUOTE (type /-> (type # type)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE destconsttype) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE destconsttype) (MKTIDY (QUOTE (type /-> token))) (QUOTE MLTYPE))
(PUTPROP (QUOTE destvartype) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE destvartype) (MKTIDY (QUOTE (type /-> token))) (QUOTE MLTYPE))
(PUTPROP (QUOTE mkthm) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE mkthm) (MKTIDY (QUOTE (((form list) # form) /-> thm))) (QUOTE MLTYPE))
(PUTPROP (QUOTE destthm) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE destthm) (MKTIDY (QUOTE (thm /-> ((form list) # form)))) (QUOTE MLTYPE))

% OL1.LSP %

(PUTPROP (QUOTE isquant) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE isquant) (MKTIDY (QUOTE (form /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE isimp) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE isimp) (MKTIDY (QUOTE (form /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE isconj) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE isconj) (MKTIDY (QUOTE (form /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE isequiv) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE isequiv) (MKTIDY (QUOTE (form /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE isinequiv) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE isinequiv) (MKTIDY (QUOTE (form /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE istruth) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE istruth) (MKTIDY (QUOTE (form /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE issumtype) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE issumtype) (MKTIDY (QUOTE (type /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE isprodtype) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE isprodtype) (MKTIDY (QUOTE (type /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE isfuntype) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE isfuntype) (MKTIDY (QUOTE (type /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE isconsttype) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE isconsttype) (MKTIDY (QUOTE (type /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE isvartype) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE isvartype) (MKTIDY (QUOTE (type /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE isabs) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE isabs) (MKTIDY (QUOTE (term /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE iscomb) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE iscomb) (MKTIDY (QUOTE (term /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE isvar) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE isvar) (MKTIDY (QUOTE (term /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE isconst) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE isconst) (MKTIDY (QUOTE (term /-> bool))) (QUOTE MLTYPE))
(DML' phylumofterm 1 CAR (term /-> token))
(DML' phylumofform 1 CAR (form /-> token))
(DML' phylumoftype 1 CAR (type /-> token))
(DMLC dottype (GET (QUOTE /.) (QUOTE CANON)) type)
(DMLC trtype (GET (QUOTE TR) (QUOTE CANON)) type)
(DMLC tt (mkconst (QUOTE TT) (GET (QUOTE trtype) (QUOTE MLVAL))) term)
(DMLC ff (mkconst (QUOTE FF) (GET (QUOTE trtype) (QUOTE MLVAL))) term)
(DMLC uutr (mkconst (QUOTE UU) (GET (QUOTE trtype) (QUOTE MLVAL))) term)
(DMLC uudot (mkconst (QUOTE UU) (GET (QUOTE dottype) (QUOTE MLVAL))) term)
(DMLC truth (mk=truth) form)
(SETQ %mkequivclosure (CLOSURE (QUOTE mkequiv)))
(SETQ %mkinequivclosure (CLOSURE (QUOTE mkinequiv)))
(PUTPROP (QUOTE destaform) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE destaform) (MKTIDY (QUOTE (form /-> (((term # term) /-> form) # (term # term))))) (QUOTE MLTYPE))
(PUTPROP (QUOTE mkcond) 3 (QUOTE NUMARGS))
(PUTPROP (QUOTE mkcond) (MKTIDY (QUOTE ((term # (term # term)) /-> term))) (QUOTE MLTYPE))
(PUTPROP (QUOTE mkpair) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE mkpair) (MKTIDY (QUOTE ((term # term) /-> term))) (QUOTE MLTYPE))
(PUTPROP (QUOTE destcond) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE destcond) (MKTIDY (QUOTE (term /-> (term # (term # term))))) (QUOTE MLTYPE))
(PUTPROP (QUOTE destpair) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE destpair) (MKTIDY (QUOTE (term /-> (term # term)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE isUU) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE isUU) (MKTIDY (QUOTE (term /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE lhs) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE lhs) (MKTIDY (QUOTE (form /-> term))) (QUOTE MLTYPE))
(PUTPROP (QUOTE rhs) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE rhs) (MKTIDY (QUOTE (form /-> term))) (QUOTE MLTYPE))
(DML' hyp 1 CAR (thm /-> (form list)))
(DML' concl 1 CDR (thm /-> form))
(PUTPROP (QUOTE mkfreethm) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE mkfreethm) (MKTIDY (QUOTE (form /-> thm))) (QUOTE MLTYPE))
(PUTPROP (QUOTE eqtt) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE eqtt) (MKTIDY (QUOTE (term /-> form))) (QUOTE MLTYPE))
(PUTPROP (QUOTE eqff) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE eqff) (MKTIDY (QUOTE (term /-> form))) (QUOTE MLTYPE))
(PUTPROP (QUOTE equu) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE equu) (MKTIDY (QUOTE (term /-> form))) (QUOTE MLTYPE))

% OL2.LSP, OL3.LSP %

% OL2.LSP %

(PUTPROP (QUOTE variant) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE variant) (MKTIDY (QUOTE ((term # (term list)) /-> term))) (QUOTE MLTYPE))
(DML' aconvform 2 ALPHACONV ((form # form) /-> bool))
(DML' aconvterm 2 ALPHACONV ((term # term) /-> bool))
(DML' termfrees 1 FREEVARS (term /-> (term list)))
(DML' formfrees 1 FREEVARS (form /-> (term list)))
(DML' substinterm 2 SUBSTITUTE ((((term # term) list) # term) /-> term))
(DML' substinform 2 SUBSTITUTE ((((term # term) list) # form) /-> form))
(DML' substoccsinterm 2 SUBSTITUTEOCCS ((((term # ((int list) # term)) list) # term) /-> term))
(DML' substoccsinform 2 SUBSTITUTEOCCS ((((term # ((int list) # term)) list) # form) /-> form))
(DML' freeinterm 2 FREEIN (((term list) # term) /-> bool))
(DML' freeinform 2 FREEIN (((term list) # form) /-> bool))


% OL3.LSP %

(PUTPROP (QUOTE eqtype) 2 (QUOTE NUMARGS))
(PUTPROP (QUOTE eqtype) (MKTIDY (QUOTE ((term # term) /-> bool))) (QUOTE MLTYPE))
(PUTPROP (QUOTE genvar) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE genvar) (MKTIDY (QUOTE (type /-> term))) (QUOTE MLTYPE))
(PUTPROP (QUOTE equivpair) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE equivpair) (MKTIDY (QUOTE (thm /-> (term # term)))) (QUOTE MLTYPE))
(PUTPROP (QUOTE inequivpair) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE inequivpair) (MKTIDY (QUOTE (thm /-> (term # term)))) (QUOTE MLTYPE))
(DML' termvars 1 ALLVARS (term /-> (term list)))
(DML' formvars 1 ALLVARS (form /-> (term list)))
(PUTPROP (QUOTE tmfmvars) 1 (QUOTE NUMARGS))
(PUTPROP (QUOTE tmfmvars) (MKTIDY (QUOTE ((term /+ form) /-> (term list)))) (QUOTE MLTYPE))
(DML' typesinterm 2 TYPESIN (((type list) # term) /-> bool))
(DML' typesinform 2 TYPESIN (((type list) # form) /-> bool))
(DML' typesintype 2 TYPESIN (((type list) # type) /-> bool))
(DML' typetyvars 1 TYVARS (type /-> (type list)))
(DML' termtyvars 1 TYVARS (term /-> (type list)))
(DML' formtyvars 1 TYVARS (form /-> (type list)))

