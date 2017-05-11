
(declare-datatypes () 
	((JSIL_Type 
		UndefinedType NullType EmptyType NoneType BooleanType
		NumberType CharType StringType ObjectType ListType TypeType SetType)))

(declare-datatypes () 
	((JSIL_Literal 
		Undefined 
		Null
		Empty
		(Bool (bValue Bool))
		(Num (nValue Real))
		(Loc (locValue Int))
		(Type (tValue JSIL_Type))
		(List (listValue JSIL_Literal_List))
		None)
	(JSIL_Literal_List 
		Nil 
		 (Cons 
			(head JSIL_Literal)
			(tail JSIL_Literal_List)))))

(define-sort JSIL_Literal_Set () (Array JSIL_Literal Bool))

(declare-const _lvar_295 JSIL_Literal)
(declare-const _lvar_296 JSIL_Literal_Set)
(declare-const _lvar_353 JSIL_Literal_Set)
(declare-const |#v| JSIL_Literal)

(assert 
	(forall ((|#x| JSIL_Literal))
  		(let ((a!1 (not (is-Num |#x|)))
        	(a!2 (not (<= (nValue |#x|) (nValue _lvar_295)))))
    	(or a!1 (not (select _lvar_296 |#x|)) a!2))))
      
(assert 
  (and 
    (is-Num _lvar_295)
    (is-Num |#v|)
  )
)

(assert (< (nValue |#v|) (nValue _lvar_295)))

(assert
(forall ((_lvar_353 JSIL_Literal_Set))
  (let ((a!1 (forall ((|#x| JSIL_Literal))
               (let ((a!1 (not (is-Num |#x|)))
                     (a!2 (not (<= (nValue |#x|)
                                   (nValue |#v|)))))
                 (or a!1 (not (select _lvar_353 |#x|)) a!2))))
        (a!2 (= ((_ map (or (Bool Bool) Bool))
                  _lvar_353
                  (store ((as const (Array JSIL_Literal Bool)) false)
                         |#v|
                         true))
                ((_ map (or (Bool Bool) Bool))
                  _lvar_296
                  ((_ map (or (Bool Bool) Bool))
                    (store ((as const (Array JSIL_Literal Bool)) false)
                         |#v|
                         true)
                    (store ((as const (Array JSIL_Literal Bool)) false)
                         _lvar_295
                         true))
                         ))))
    (or (not a!1) (not a!2)))))

(check-sat)
