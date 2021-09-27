(defconstant +bicond+ '<=>)
(defconstant +cond+ '=>)
(defconstant +and+ '^)
(defconstant +or+ 'v)
(defconstant +not+ '¬)

(defun truth-value-p (x)
  (or (eql x T) (eql x NIL)))

(defun unary-connector-p (x)
  (eql x +not+))

(defun binary-connector-p (x)
  (or (eql x +bicond+)
      (eql x +cond+)))

(defun n-ary-connector-p (x)
  (or (eql x +and+)
      (eql x +or+)))

(defun connector-p (x)
  (or (unary-connector-p x)
      (binary-connector-p x)
      (n-ary-connector-p x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
;; EJERCICIO 1.1 (from https://github.com/bertuccio/inferencia-logica-proposicional)
;; Predicate to determine if an expression in LISP
;; is a positive literal  
;; 
;; RECIBE   : expresión  
;; EVALÚA A : T si la expresión es un literal positivo,  
;;            NIL en caso contrario.  
;;
(defun positive-literal-p (x) 
  (if (and (atom x) (not (connector-p x)) (not (truth-value-p x)))
      T
    nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
;; EJERCICIO 1.2 (from https://github.com/bertuccio/inferencia-logica-proposicional)
;; Predicate to determine if an expression in LISP
;; is a negative literal   
;; 
;;RECEIVE: expression x
;; EVALUATE A: T if the expression is a negative literal,  
;;  
(defun negative-literal-p (x)
  (and (listp x)
       ;; needs to be a list
       (eql +not+ (first x)) ;; whose first element is the connector not
       (null (rest (rest x))) ;; with only two elements
       (positive-literal-p (second x)))) ;; second element is a positive literal
;;; T
;;;
;;; MANDATORY THE ¬ MUST BE SEPARATED FROM THE LITERAL
;;;
(negative-literal-p '(¬ p))
;;;NIL 
(negative-literal-p '(¬ p x z))


;;;(from https://github.com/bertuccio/inferencia-logica-proposicional)
(defun extract-positive-literals (cnf)
  (unless (null cnf)
    (union (positivize-literals (first cnf))
           (extract-positive-literals (rest cnf)))))

;;;(from https://github.com/bertuccio/inferencia-logica-proposicional)
(defun positivize-literals (k)
  (unless (null k)
    (if (negative-literal-p (first k))
        (append (list (second (first k))) (positivize-literals (rest k)))
      (append (list (first k)) (positivize-literals (rest k))))))

;;; You have to change the T for X, otherwise it gives a strange behavior. Is it because it considers T as true?
( setq cnfpru '(( P (¬ Q) R (¬ S) (¬ X))  ( P  R  S  X ) ( P (¬ R) S) (P R (¬ S) X) (P (¬ R) (¬ S)) ((¬ P) (¬ Q)) ((¬ Q) R S (¬ X)) (S (¬ X))))
(extract-positive-literals cnfpru)

;;; T
(setq cnf '( (A B C) (D E F) ((¬ A) G H)))
(extract-positive-literals cnf)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; EJERCICIO 3.1.1 (from https://github.com/bertuccio/inferencia-logica-proposicional)
;; removal of repeated literals a clause
;;
;; RECEIVE: K - clause (list of literals, implicit disjunction)
;; EVALUATE A: equivalent clause without repeated literals
;;
(defun repeated-literal-p (lit lst)
  (unless (null lst)
    (if (equal lit (first lst))
        T
      (repeated-literal-p lit (rest lst)))))


(defun eliminate-repeated-literals (k) 
  (unless (null k)
    (if (repeated-literal-p (first k) (rest k))
        (eliminate-repeated-literals (rest k))
      (append (list (first k)) (eliminate-repeated-literals (rest k))))))

(setq k '(v A B B C C C))
(eliminate-repeated-literals k)
(setq k '(v A B (¬ B) C C C))
(eliminate-repeated-literals k)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
;; EJERCICIO 3.1.2 (from https://github.com/bertuccio/inferencia-logica-proposicional)
;; elimination of repeated clauses in an FNC  
;;  
;; RECEIVE: cnf - FBF in FNC (clause list, implicit conjunction) 
;; EVALUATE A: equivalent FNC without repeated clauses  
;; 
(defun eliminate-repeated-clauses (cnf) 
  (eliminate-repeated-clauses-aux-2 (eliminate-repeated-clauses-aux cnf)))

(defun eliminate-repeated-clauses-aux (cnf)
  (unless (null cnf)
    (append (list (eliminate-repeated-literals (first cnf)))
            (eliminate-repeated-clauses-aux(rest cnf)))))

(defun eliminate-repeated-clauses-aux-2 (cnf)
  (unless (null cnf)
    (if (search-for-element (first cnf) (rest cnf))
        (eliminate-repeated-clauses-aux-2 (rest cnf))
      (append (list (first cnf))(eliminate-repeated-clauses-aux-2 (rest cnf))))))
(defun search-for-element (elem lst)
  (unless (null lst)
    (if (search-for-element-aux elem (first lst))
        (if (search-for-element-aux (first lst) elem)
            T
          (search-for-element elem (rest lst)))
      (search-for-element elem (rest lst)))))

(defun search-for-element-aux (elem1 elem2)
  (if (null elem1)
      T
    (if (repeated-literal-p (first elem1) elem2)
        (search-for-element-aux (rest elem1) elem2)
      nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; 
;;; END OF FUNCTIONS OBTAINED FROM https://github.com/bertuccio/inferencia-logica-proposicional
;;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; DPLL receives a clause in literal list format without connectors
;;; returns the solutions or interpretations that are satisfied
;;; after calling the DPLL-aux and subsequent functions
;;;
;;; A detailed description of the DPLL algorithm can be found at http://www.cs.us.es/~fsancho/?e=120
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun DPLL (cnf)
  
(setq camino_literal '())
(setq camino_seguido '())

     (DPLL-aux  cnf camino_seguido camino_literal  )

  
)

(defun DPLL-aux ( cnf_recibido camino_seguido camino_literal )
  (setq cnf (remove nil cnf_recibido))
  
;;; Finds if in the list there is a list with only one element or not
(setq list-o-lit1 ( buscar-literal cnf ))
                  (if (eql list-o-lit1 nil)
                   ;;; si no hay una lista con un solo elemento, extrae todos los literales de la lista
                     (setq list-o-lit (first (extract-positive-literals cnf)) )
                   (setq list-o-lit list-o-lit1)
                   )
(setq swBuscaLiteralOpuesto 0)

;;; In case it had found a list with only one element it looks for if
;;; there would also be a list with only that element and negated,
;;; which would give an impossible solution

(cond ( (positive-literal-p list-o-lit1)
       (setq lista-A-Buscar (list (cons +not+ (list  list-o-lit1))))
       (if ( buscar-literal-opuesto lista-A-Buscar cnf)
           (setq swBuscaLiteralOpuesto 1)
           (setq swBuscaLiteralOpuesto 0)
        )

       )
      ( (negative-literal-p list-o-lit1)
       (setq lista-A-Buscar (list (second list-o-lit1)))
       (if ( buscar-literal-opuesto lista-A-Buscar cnf)
           (setq swBuscaLiteralOpuesto 1)
           (setq swBuscaLiteralOpuesto 0)
        )

       )

      (t
       (setq swBuscaLiteralOpuesto 0)
       
       )
)

  (cond ((or (null cnf)  (null list-o-lit) (eq cnf '(NIL))  (eq cnf '((NIL))) (eq swBuscaLiteralOpuesto 1))
          (if (eq swBuscaLiteralOpuesto 1)
              (format t "ENDS with impossible condition finds the negated of ~a in cnf ~a~% " list-o-lit1 cnf)
            ()
         )
           ()
               )
         (t
          ;;; if list-o-lit1 is null, it is a sign that search-literal has returned null, that is, there is no single literal
          ;;; only clauses, so list-o-lit is chosen which is the first in the list of variables
          ;;; and cnf is treated as if it had added the literal and it is considered another expression with its negated, actually it is enough to apply
          ;;; subsuncion (elimination of the clauses in which the literal negated was)
          ;;; and realization (elimination of the literal in the clauses in which it was)
          ;;; All this is done in the DPLL-aux-Ant function
          
               (cond ((or (null list-o-lit1))
                
                 (DPLL-aux-Ant  list-o-lit cnf_recibido  camino_seguido camino_literal )
                      )
                     (t
                      

                      ;;; as there is only one literal, only subsuncion (elimination of the clauses in which the literal negated was)
                      ;;;  and realization (elimination of the literal in the clauses in which it was) 
                      ;;; the literal can be negative
                      
                       (if (negative-literal-p list-o-lit) 
                         (DPLL-aux-nega  list-o-lit cnf_recibido camino_seguido camino_literal)
                        (DPLL-aux-posi  list-o-lit cnf_recibido camino_seguido camino_literal)
                        )

                      )
                     )
  

                 )
        )
)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; Function that searches if in a set of clauses there is a single literal
;;; in a list, returning the literal or NIL
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; 
(defun buscar-literal (cnf)

     (cond( (null cnf)
        ()
        )
           ( (and (negative-literal-p (first (first cnf))) (eq (list-length (first cnf)) 1))
      
              (first (first cnf))
          
            
         )
         ( ( and (positive-literal-p (first (first cnf))) (eq (list-length (first cnf)) 1))
       
         (first  (first cnf))
          
         )
        (t 
          (buscar-literal (rest cnf))

         )
           ))

;;; Result must b q
(setq cnf '( (p q r) (q) ( (¬ p) q r) ))
(buscar-literal cnf)

;;; ojo en algunos ejemplos figura el lieral V, lo que se confunde
;;; con el signo de unión
( setq cnfp1 '(((¬ X) W) ((¬ W) U) ((¬ X) Q) ((¬ U))))
( buscar-literal cnfp1 )

(extract-positive-literals cnfp1)
;;; Debe dar (¬ q) 
(setq cnf '( (p q r) ((¬ q)) ( (¬ p) q r) ))
(buscar-literal cnf)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Function that receives a literal and determines if the opposite literal is in a cnf expression
;;; what determines an impossible condition, case (L) ((¬ L)) 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun buscar-literal-opuesto (literal cnf)
  (cond( (null cnf)
        ()
        )
        (t
         
       
         (if (equal literal (first cnf))
                  T
                  (buscar-literal-opuesto literal (rest cnf))
        )
  )
)
  )  
(setq lite '(L))
(setq lite2 '(L))
(equal lite lite2)
(setq cnfp4 '((A B L) (C D) (E D (¬ L)) (L) ((¬ L))))
(buscar-literal-opuesto lite cnfp4)
(setq lite3 '((¬ L)))
(buscar-literal-opuesto lite3 cnfp4)

(setq cnfp4 '((A B L) (C D) (E D (¬ L)) ((¬ L)) (L) (P A) ))
(buscar-literal-opuesto lite2 cnfp4)

(setq cnfp4 '((A B L) (C D) (E D (¬ L)) (L) ((¬ L))))
(setq lite3 '((¬ L)))
(buscar-literal-opuesto lite3 cnfp4)

(setq cnfp5 '((P Q) ((¬ P) Q)))
(setq lite5 '((¬ P)))
(buscar-literal-opuesto lite5 cnfp5)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Funcion that receives a positive literal list-o-lit1 and a cnf
;;; applies subsuncion (elimination of the clauses  of cnf in which the literal list-o-lit1 negated was)
;;; and realization (elimination of the literal in the clauses in which it was)
;;; All this is done in the DPLL-aux-Ant function


(defun DPLL-aux-posi ( list-o-lit cnf camino_seguido camino_literal)
  
  ;;; Subsumption, the clauses that have the positive literal are removed         
  (setq cnf-subsuncion-unitaria (subdivision_literal_negativo_de_lista cnf  list-o-lit   ))
  

           
  ;;;Unit resolution, the negative literal is removed from all the clauses
  (setq lista-A-Quita (cons +not+ (list  list-o-lit)))
           
                 (setq cnf-resolucion (elimina_literal_negativo_de_lista  cnf-subsuncion-unitaria  lista-A-Quita))
                 (setq cnf-resolucion-sin-repetidos ( eliminate-repeated-clauses cnf-resolucion))
  

 
            (setq camino_posi ( cons 1 camino_seguido))
            (setq camino_literal ( cons list-o-lit camino_literal))

           

                 ( if (and  (eql (list-length cnf-resolucion-sin-repetidos) 1) ( not (null (first  cnf-resolucion-sin-repetidos ) )))
                   (format t "Found a solution with literal in a single clause, order literals  ~a , in the positiv path ~a comes to ~a~%" (reverse camino_literal) (reverse camino_posi)  cnf-resolucion-sin-repetidos)
                ()
                   )
  
             
                 (DPLL-aux   cnf-resolucion-sin-repetidos camino_posi camino_literal)

                 
  
  )
;;; Te same as DPLL-aux-nega with a negative literal
(defun DPLL-aux-nega ( list-o-lit cnf camino_seguido camino_literal)

  ;;; The negative branch
             
                  (setq lista-A-Quita   list-o-lit)

  
  
                 ;;; unitary subsumption, now all the clauses that contain the negative letter are eliminated
                 (setq cnf-LC-subsubsuncion (subdivision_literal_negativo_de_lista  cnf  lista-A-Quita))
             
                 ;;; Unit resolution, the positive literal is eliminated from all the clauses
                 (setq cnf-LC-resolucion  (maplist #'(lambda (x) (remove (second  list-o-lit) (first x))) cnf-LC-subsubsuncion))
                 (setq cnf-LC-resolucion-sin-repetidos ( eliminate-repeated-clauses cnf-LC-resolucion))
       

                 
       
  (setq camino_nega ( cons 0 camino_seguido))
  (setq camino_literal ( cons list-o-lit camino_literal))

 ( if (eql (list-length  cnf-LC-resolucion-sin-repetidos) 1)
       (format t "Found a solution with literal in a single clause, order literals  ~a on the negative path ~a comes to ~a~%" ( reverse camino_literal) ( reverse camino_nega) cnf-LC-resolucion-sin-repetidos)
                ()
                )

  
  (DPLL-aux   cnf-LC-resolucion-sin-repetidos camino_nega camino_literal)



  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;; 
;;; Funcion that receives list-o-lit  which is the first in the list of variables
;;; and a cnf wich is treated as if it had added the literal and it is considered another expression with its negated, actually it is enough to apply
;;;  subsuncion (elimination of the clauses in which the literal negated was)
;;;  and realization (elimination of the literal in the clauses in which it was)
;;; 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun DPLL-aux-Ant ( list-o-lit cnf camino_seguido camino_literal )
 
            (setq camino_literal ( cons list-o-lit camino_literal))

  
                   ;;; subsumption, the clauses that have the positive literal are removed          
                 (setq cnf-subsuncion-unitaria (subdivision_literal_negativo_de_lista cnf  list-o-lit   ))
           
                 ;;;; Unit resolution, the negative literal is removed from all clauses
                  (setq lista-A-Quita (cons +not+ (list  list-o-lit)))
           
                 (setq cnf-resolucion (elimina_literal_negativo_de_lista  cnf-subsuncion-unitaria  lista-A-Quita))
                 (setq cnf-resolucion-sin-repetidos ( eliminate-repeated-clauses cnf-resolucion))
          
                 (setq camino_posi ( cons 1 camino_seguido))
          
  
  ;;; WHEN FINDING A SOLUTION, IT DOES NOT ONLY DETECT IT, BUT IT PRESENTS TWO ARRAYS, ONE WITH THE VALUES OF THE VARIABLES INVOLVED
  ;;; IN ORDER UNTIL YOU REACH THE SOLUTION AND ANOTHER, NOTING IF ITS VALUE IS ZERO OR ONE, IN THE LITERALS THE LITERAL APPEARS SOMETIMES DENIED, IT MUST REPRESENT THE 
  ;;; LITERAL WITH ZERO VALUE. ZERO OR ONE VALUE COMES IN THE SECURITIES ARRAY. WHEN IT ENDS WITH A SINGLE LITERAL EXPRESSION 
  ;;; THE VALUE CORRESPONDS TO THE LITERAL, FOR EXAMPLE (Q) WOULD BE THAT THE VALUE OF Q IS 1 REGARDLESS OF THE OTHER VALUES
  ;;; IF IT APPEARS AT THE END AS A SOLUTION ((¬ Q) R) IT WOULD BE EQUIVALENT TO ALL COMBINATIONS FOR WHICH IT IS TRUE, OR BE: Q = 0, R = 1; Q = 0 R = 0; Q = 1, R = 1.
  ( if (or (eql (list-length cnf-resolucion-sin-repetidos) 1) ( null (first  cnf-resolucion-sin-repetidos ) ))
      (format t "Found a solution, order literals ~a on the positive path ~a comes to ~a~%" (reverse camino_literal) (reverse camino_posi)  cnf-resolucion-sin-repetidos)
     ;;; (format t "Found a solution, order literals ~a  comes to ~a~%" (reverse camino_literal)   cnf-resolucion-sin-repetidos)

                ()
                )

                
                 (DPLL-aux   cnf-resolucion-sin-repetidos camino_posi camino_literal)
                 
          
                 ;;; The negative branch
                 (setq lista-A-Quita (cons +not+ (list  list-o-lit)))
            
                 (setq cnf-LC-subsubsuncion (subdivision_literal_negativo_de_lista  cnf  lista-A-Quita))
            

                 ;;;Unitary resolution, the positive literal is eliminated from all the clauses
                 (setq cnf-LC-resolucion  (maplist #'(lambda (x) (remove   list-o-lit (first x))) cnf-LC-subsubsuncion))
                 (setq cnf-LC-resolucion-sin-repetidos ( eliminate-repeated-clauses cnf-LC-resolucion))
                      
       
   (setq camino_nega ( cons 0 camino_seguido))
              
( if (or  (eql (list-length  cnf-LC-resolucion-sin-repetidos) 1) ( null (first  cnf-LC-resolucion-sin-repetidos ) ))
       (format t "Found a solution, order literals ~a  on the negative path ~a comes to ~a~%" ( reverse camino_literal) ( reverse camino_nega) cnf-LC-resolucion-sin-repetidos)
   
                 ()
                )

  (DPLL-aux    cnf-LC-resolucion-sin-repetidos camino_nega camino_literal )
  

)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Subsuncion_unitaria, function that eliminates all the clauses of a list
;;; that contain a certain literal within the procedure to implement the DPLL algorithm
;;; 
;;; NOT USED; IT IS IMPLEMENTED THROUGH A SIMPLE MAPCAR
;;; ( setq cnf-L  (maplist #'(lambda (x) (remove  (first list-o-lit) (first x))) cnf))
;;;   
;;; en DPLL-aux-Ant
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun subsuncion_unitaria (literal lista)
  
  ( unless (null (first lista))
   (append (list (subsuncion_unitaria_aux literal (first lista)  )) (subsuncion_unitaria literal (rest lista)))
            
    )
  )

(defun subsuncion_unitaria_aux ( literal lista)
   ( unless (null (first lista))
                  (if  (eql (first lista) literal)
                  (subsuncion_unitaria_aux  literal (rest lista) )
                  (append (list (first lista)) (subsuncion_unitaria_aux  literal (rest lista) ))
               )
                        
             )
         
  
  )

(defun subdivision_literal_negativo_de_lista ( lista  literal_negativo)
  
  ( unless (null (first lista))
    (if ( member literal_negativo (first lista):test #'equal)
        (subdivision_literal_negativo_de_lista (rest lista)  literal_negativo)
   (append (list  (first lista)) (subdivision_literal_negativo_de_lista (rest lista)  literal_negativo))
            
    )
    )
  )

(defun subdivision_literal_de_lista ( lista  literal)
  
  ( unless (null (first lista))
    (if ( member literal (first lista))
        (subdivision_literal_de_lista (rest lista)  literal)
   (append (list  (first lista)) (subdivision_literal_de_lista (rest lista)  literal))
            
    )
    )
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Function that receives a list and a list within that list to delete
;;; in principle, it will be a negative literal
;;;; Receive the list with the negative literal to delete
;;;; Returns the list without the negative literal
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(defun elimina_literal_negativo_de_lista ( lista  literal_negativo)
  
  ( unless (null (first lista))
   (append (list (elimina_literal_negativo_de_lista_aux (first lista)  literal_negativo))(elimina_literal_negativo_de_lista (rest lista)  literal_negativo))
            
    )
  )

(defun elimina_literal_negativo_de_lista_aux( lista  literal_negativo)
 ;;; (format t "lista a quitar ~a~% " (first lista))

  ( unless (null (first lista))
    ( cond  (  (listp (first lista)) 
              (if ( and (eql (first(first lista)) ( first literal_negativo)) (eql (second(first lista)) ( second literal_negativo)))
                  (elimina_literal_negativo_de_lista_aux (rest lista)  literal_negativo)
                  (append (list (first lista)) (elimina_literal_negativo_de_lista_aux (rest lista)  literal_negativo))
               )
                        
             )
          (t 
           (append (list (first lista)) (elimina_literal_negativo_de_lista_aux (rest lista)  literal_negativo))
           )

  )

    )
  )
( setq lista '((¬ P) Q (¬ R) ))
(setq lista-A-Quita (cons +not+ '(R)))
(elimina_literal_negativo_de_lista_aux  lista  lista-A-Quita)
(if (null (first lista)) 
  (setqPP=2)
  ()
  )


(setq lista-A-Quita (cons +not+ '(R)))
( setq cnf-nega '(((¬ P) Q (¬ R)) ((¬ P) (¬ Q) (¬ R))))
(elimina_literal_negativo_de_lista  cnf-nega  lista-A-Quita)


;;; solución r=1 q =0 p=0 
(setq cnfpp '( (p q r) ( (¬ p) q r) (p (¬ q)) (p r) ((¬ p) (¬ q) r) ((¬ p) q (¬ r)) ((¬ p) (¬ q) (¬ r)) ))
(DPLL cnfpp)
;;; Expresion imposible
(setq cnfp4 '((A B L) (C D) (E D (¬ L)) (L) ((¬ L))))
(setq cnfp4 '((A B L) (C D) (E D (¬ L)) ((¬ L)) (L) (P A) ))
(setq cnfp4 '((A B L) (C D) (E D (¬ L)) ))

(time (DPLL cnfp4))

(list-length cnf)
(eq (list-length cnf) 1)
(setq cnf-L '(((¬ Q))))
( if (eql (list-length cnf-L) 1)
       (format t "Encontrada una solución,  en el camino  llega a ~a~%"  cnf-L)
                 ()
                 )
cnf-L

(setq cnfp0 '((P Q) ((¬ P) Q) (P)))
(time (DPLL cnfp0))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; TESTS
;;; With the examples of the link to netlogo that appears in http://www.cs.us.es/~fsancho/?e=120 
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Example 0 of netlogo in  http://www.cs.us.es/~fsancho/?e=120.
;;; It is fulfilled for q=1
;;; 
(setq cnfp0 '((P Q) ((¬ P) Q)))
(time (DPLL cnfp0))

;;; Example 1 of netlogo in  http://www.cs.us.es/~fsancho/?e=120 Can't find a solution
(setq cnfp1 '( ( P Q ) ( (¬ P) Q ) ((¬ Q))))
(time (DPLL cnfp1))

;;; Example 2 of netlogo in  http://www.cs.us.es/~fsancho/?e=120- Can't find a solution
(setq cnfp2 '( ( P Q ) ( (¬ P)   Q ) ( P (¬ Q) ) ((¬ P) (¬ Q))))
(time (DPLL cnfp2))

;;; Example 3 of netlogo in  http://www.cs.us.es/~fsancho/?e=120
;;; P=1, Q=0, S=1, X=0 fulfills it
;;; P=1, Q=0, S=1, x=1 fulfills it
;;; P=0, Q=0, S=1, X=1, R=0 fulfills it 
;;; Changed T to X, in another case it gives a strange behavior, perhaps because it considers T as true
( setq cnfp3 '(( P (¬ Q) R (¬ S) (¬ X))  ( P  R  S  X ) ( P (¬ R) S) (P R (¬ S) X) (P (¬ R) (¬ S)) ((¬ P) (¬ Q)) ((¬ Q) R S (¬ X)) (S (¬ X))))
(time (DPLL cnfp3))

;;;;;;  Example 4 of netlogo http://www.cs.us.es/~fsancho/?e=120. Can't find a solution
(setq cnfp4 '((P Q R) ((¬ P) Q) ((¬ Q) R) ((¬ P)) (P R)))
(time (DPLL cnfp4))

;;; Example 5 of netlogo in http://www.cs.us.es/~fsancho/?e=120. Can't find a solution
;;; Changed T to X, in another case it gives a strange behavior, perhaps because it considers T as true
(setq cnfp5 '(((¬ P)  (¬ Q)  R ) ((¬ S) X) ((¬ X)  P) (S) ((¬ S) U) ((¬ U) Q ) ((¬ R))))
(time (DPLL cnfp5))

;;; Example 6 of netlogo in http://www.cs.us.es/~fsancho/?e=120 No encuentra solución 
(setq cnfp6 '((P Q) (Q R) (R W)  ((¬ R) (¬ P)) ((¬ W) (¬ Q)) ((¬ Q) (¬ R))))
(time (DPLL cnfp6))


;;; Example 7 of netlogo in  http://www.cs.us.es/~fsancho/?e=120
;;; Solutión P=1 U=0 W=0 X=0,R=1  and  P=1 U=0 W=0 X=0,Q=0
( setq cnfp7 '(((¬ P) (¬ Q) R) ((¬ P) (¬ X) W) ((¬ P) (¬ W) U)  ((¬ X) Q) (P) ((¬ U))))
(time (DPLL cnfp7))

;;;************************************************************************************************
;;;
;;; Interface with the project that can be downloaded from
;;; https://github.com/bertuccio/inferencia-logica-proposicional
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Added function to get the total FNC of several FBC from a list
;;; Receive: FBF list
;;; Returns: the list of FBFs converted to FNC
;;;
;;;
;;;(defun pasa-lista-FBF-a-lista-FNC (wFBF)
  
;;;  ( cond ((not (null (first wFBF)))
       
;;;    (setq wff ( first wFBF ))
;;;    (setq wff1 (eliminate-bicondicional wff))
;;;    (setq wff2 (eliminate-condicional wff1))
;;;    (setq wff3 (reduce-scope-of-negation wff2))
;;;    (setq wff4 (cnf wff3))     
;;;    (setq wff5 (eliminate-connectors wff4))
;;;    (setq wff6 (eliminate-repeated-literals wff5))
;;;
;;;    (append wff6 (pasa-lista-FBF-a-lista-FNC (rest wFBF)) )
  

;;;  )
    
  
;;;  )
 ;;; )
;;; (setq wFBF '((<=> P  (^ A  H))))
;;;(pasa-lista-FBF-a-lista-FNC wFBF)

;;; (setq wFBF '((=> A  (¬ H)) ( <=>  P(^ A  H)) (=> H  P)))
;;; (pasa-lista-FBF-a-lista-FNC wFBF)



