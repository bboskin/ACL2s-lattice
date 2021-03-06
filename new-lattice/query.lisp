
(defunc bottomp (e)
  :input-contract t
  :output-contract (booleanp (bottomp e))
  (if e nil nil))
:q

(in-package "ACL2S")
(load "~/quicklisp/setup.lisp")
(ql:quickload :trivia)
(ql:quickload :cl-ppcre)
(ql:quickload :let-plus)
(setf ppcre:*allow-named-registers* t)

;; dealing with function symbols
(defun guards->exp (exp)
  (if (listp exp)
      `(and . ,(mapcar #'(lambda (x) `(or . ,x)) exp))
    exp))

(defun get-guards (form)
  (ld `((mv-let
	  (a b)
	  (acl2s::guard-obligation ',form nil nil 'top-level state)
	  (declare (ignore a))
	  (assign result b))))
  (guards->exp (cadr (@ result))))



(defpackage :lattice (:use :cl :trivia :ppcre :let-plus :acl2 :acl2s))
(in-package :lattice)

(load "lattice.lisp")
(load "simplification.lisp")

;; Next, we perform queries on the lattice, assuming that it's
;; complete (Latticep L) = T

(defun form-constantp (e)
  (or (numberp e) (stringp e) (characterp e)
      (and (consp e) (equal (car e) 'quote))))

(defun free-vars (exp nl)
  (cond
   ((form-constantp exp) nil)
   ((literalp exp)
    (cond
     ((symbolp exp) (list exp))
     ((VarInDomainp (car exp) nl) nil)
     (t (list exp))))
   ((listp exp)
    (reduce #'(lambda (x ans) (append (free-vars x nl) ans)) (cdr exp)
	    :initial-value nil :from-end t))
   (t (error "invalid formula ~a" exp))))

;; returns a list of the free variables in e, along with the simplified
;; and completed form
(defun make-expr-for-lattice (e nl)
  (let* ((e (p-reduce e))
	 (hyps (acl2s::get-guards e))
	 (vars (free-vars e nl)))
    (list vars (p-reduce `(and ,hyps ,e)))))


;; Querying the lattice, asking if a single type is Valid, Unsat, or Sat
(defun satisfied? (ls nl found-bot found-non-bot)
  (cond
   ((endp ls) (and found-bot found-non-bot))
   ((equal (car ls) 'acl2s::Bottomp)
    (if (equal (car nl) 'acl2s::Bottomp)
	(satisfied? (cdr ls) (cdr nl) found-bot found-non-bot)
      (satisfied? (cdr ls) (cdr nl) t found-non-bot)))
   (t (satisfied? (cdr ls) (cdr nl) found-bot t))))

(defun test-type-in-Lattice (ty L)
  (let ((nl (car L)))
    (let ((meets (mapcar #'(lambda (x) (getMeet x ty L)) nl)))
      (cond
       ((equal nl meets) 'VALID)
       ((satisfied? meets nl nil nil) 'SAT)
       ((endp (remove 'acl2s::Bottomp meets)) 'UNSAT)
       (t (error "Unsure about ~s" ty))))))
#|
(assert (equal 'SAT   (test-type-in-lattice 'A      *L1*)))
(assert (equal 'SAT   (test-type-in-lattice 'B      *L1*)))
(assert (equal 'UNSAT (test-type-in-lattice 'acl2s::Bottomp *L1*)))
(assert (equal 'VALID (test-type-in-lattice 'Allp    *L1*)))
|#
;; This takes a formula, and tells if it is VALID, UNSAT, or SAT,
;; where SAT means SAT and falsifiable

(defun nil-meet (v L)
  (let ((nl (car L)))
    (remove-if-not
     #'(lambda (x)
	 (equal 'acl2s::Bottomp (getMeet v x L)))
     nl)))

(defun binary (ls tag sink)
  (cond
   ((endp ls) sink)
   ((endp (cdr ls)) `(,(car ls) X))
   (t `(,tag (,(car ls) X) ,(binary (cdr ls) tag sink)))))

(defun formula->type (form L)
  (match form
    ((list 'and t1 t2)
     (let ((t1 (formula->type t1 L))
	   (t2 (formula->type t2 L)))
       (getMeet t1 t2 L)))
    ((list 'or t1 t2)
     (let ((t1 (formula->type t1 L))
	   (t2 (formula->type t2 L)))
       (getJoin t1 t2 L)))
    ((list 'not t1)
     (let ((t1 (formula->type t1 L)))
       (formula->type (binary (nil-meet t1 L) 'or 'acl2s::bottomp) L)))
    (f
     (let ((pred (car f)))
       (if (not (VarInDomainp pred (car L)))
	   'acl2s::Bottomp pred)))))

(defun test-formula-in-Lattice (form L)
  (let ((ty (formula->type form L)))
    (test-type-in-Lattice ty L)))

(defun answer-query (q L)
  (if (not (Latticep L))
      (error "Invalid Lattice provided")
    (let ((nl (car L)))
      (let ((formula (make-expr-for-lattice q nl)))
	(let ((free-vars (car formula))
	      (formula (cadr formula)))
	  (test-formula-in-Lattice formula L))))))

;;;;;;;;;;;;;;;;;;;;;;;
;; An example to use for queries
;;;;;;;;;;;;;;;;;;;;;;

(defparameter *INTEGER-LATTICE*
  '((acl2s::Allp acl2s::Bottomp acl2s::Negp acl2s::Natp)

    
    ((acl2s::Allp    . acl2s::Allp)    (acl2s::Bottomp . acl2s::Allp)
     (acl2s::Negp    . acl2s::Allp)    (acl2s::Natp    . acl2s::Allp))
    ((acl2s::Bottomp . acl2s::Allp)    (acl2s::Bottomp . acl2s::Bottomp)
     (acl2s::Bottomp . acl2s::Negp)    (acl2s::Bottomp . acl2s::Natp))
    ((acl2s::Negp    . acl2s::Allp)    (acl2s::Bottomp . acl2s::Negp)
     (acl2s::Negp    . acl2s::Negp)    (acl2s::Bottomp . acl2s::Allp))
    ((acl2s::Natp    . acl2s::Allp)    (acl2s::Bottomp . acl2s::Natp)
     (acl2s::Bottomp . acl2s::Allp)    (acl2s::Natp    . acl2s::Natp))))

(assert (equal 'acl2s::Bottomp
	       (getMeet 'acl2s::Allp 'acl2s::Bottomp *INTEGER-LATTICE*)))
(assert (equal 'acl2s::Bottomp
	       (getMeet 'acl2s::Natp 'acl2s::Negp *INTEGER-LATTICE*)))
(assert (equal 'acl2s::Allp
	       (getJoin 'acl2s::Negp 'acl2s::Natp *INTEGER-LATTICE*)))
(assert (equal 'acl2s::Natp
	       (getJoin 'acl2s::Natp 'acl2s::Natp *INTEGER-LATTICE*)))

(assert (VarInDomainp 'acl2s::Allp (car *INTEGER-LATTICE*)))
(assert (VarInDomainp 'acl2s::Natp (car *INTEGER-LATTICE*)))
(assert (VarInDomainp 'acl2s::Negp (car *INTEGER-LATTICE*)))
(assert (VarInDomainp 'acl2s::Bottomp (car *INTEGER-LATTICE*)))
(assert (not (VarInDomainp 'Consp (car *INTEGER-LATTICE*))))


(assert (equal 'VALID (answer-query '(allp e) *INTEGER-LATTICE*)))
(assert (equal 'UNSAT (answer-query '(bottomp e) *INTEGER-LATTICE*)))
(assert (equal 'SAT (answer-query '(natp e) *INTEGER-LATTICE*)))
(assert (equal 'SAT (answer-query '(negp e) *INTEGER-LATTICE*)))

(assert (equal 'VALID (answer-query '(or (natp e) (negp e)) *INTEGER-LATTICE*)))
(assert (equal 'UNSAT (answer-query '(and (natp e) (negp e)) *INTEGER-LATTICE*)))
(assert (equal 'UNSAT (answer-query '(not (allp e)) *INTEGER-LATTICE*)))
(assert (equal 'UNSAT (answer-query '(iff (bottomp e) (not (allp e)))
				    *INTEGER-LATTICE*)))
(assert (equal 'VALID (answer-query '(iff (natp e) (not (negp e)))
				    *INTEGER-LATTICE*)))
(assert (equal 'SAT (answer-query '(iff (bottomp e) (negp e))
				  *INTEGER-LATTICE*)))
(assert (equal 'UNSAT (answer-query '(if (natp e) (negp e) (bottomp e))
				    *INTEGER-LATTICE*)))


;; A Bigger Lattice

#|
           RATIONAL
              |
            BOTTOM

           RATIONAL
             /  \
           Int  Frac
             \  /               
            BOTTOM


           RATIONAL
             /  \
           Int  Frac
                 / \  
             \  PF NF            
            BOTTOM

 






           Rational
           /     \
        PR+I    NR+I
        /  |   /   \
   PosRat  Int   NegRat
       \   / \   /
        Nat   Neg
       / \
    Zero Pos


         BOTTOM
|#


#|
TODOs:

make it so that there can be meets not explicitly in lattice.

Here, if there is no meet, then we simply split. If the result is SAT,
we say: It might be valid, but I don't know enough about the union of _ and _
to say if it's valid or not. (this means changing the meaning of SAT)



|#
(defparameter *Rationals*
  '((acl2s::Allp acl2s::po acl2s::integerp
		 acl2s::integerp acl2s::Negp
		 acl2s::Natp acl2s::zerop acl2s::posp)

    
    ((acl2s::Allp    . acl2s::Allp)    (acl2s::Bottomp . acl2s::Allp)
     (acl2s::Negp    . acl2s::Allp)    (acl2s::Natp    . acl2s::Allp))
    ((acl2s::Bottomp . acl2s::Allp)    (acl2s::Bottomp . acl2s::Bottomp)
     (acl2s::Bottomp . acl2s::Negp)    (acl2s::Bottomp . acl2s::Natp))
    ((acl2s::Negp    . acl2s::Allp)    (acl2s::Bottomp . acl2s::Negp)
     (acl2s::Negp    . acl2s::Negp)    (acl2s::Bottomp . acl2s::Allp))
    ((acl2s::Natp    . acl2s::Allp)    (acl2s::Bottomp . acl2s::Natp)
     (acl2s::Bottomp . acl2s::Allp)    (acl2s::Natp    . acl2s::Natp))))
