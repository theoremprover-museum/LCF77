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