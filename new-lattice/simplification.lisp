(in-package :lattice)

(defun literalp (e)
  (or (symbolp e)
      (and (consp e)
	   (not (in (car e) '(not and or if implies iff))))))

(defun has-variable-and-negation (ls)
  (cond
   ((endp ls) nil)
   ((literalp (car ls))
    (or (and (in `(not ,(car ls)) (cdr ls)) t)
	(has-variable-and-negation (cdr ls))))
   ((and (consp (car ls))
	 (equal (caar ls) 'not)
	 (literalp (cadar ls)))
    (or (and (in (cadar ls) (cdr ls)) t)
	(has-variable-and-negation (cdr ls))))
   (t (has-variable-and-negation (cdr ls)))))

(defun remove-redundancies (ls ig sym)
  (cond
   ((endp ls) nil)
   ((in (car ls) (cdr ls))
    (remove-redundancies (cdr ls) ig sym))
   ((equal (car ls) ig)
    (remove-redundancies (cdr ls) ig sym))
   ((and (consp (car ls))
	 (equal (caar ls) sym))
    (remove-redundancies (append (cdar ls) (cdr ls)) ig sym))
   (t (cons (car ls)
	    (remove-redundancies (cdr ls) ig sym)))))

(defun remove-redundancies/and (ls)
  (remove-redundancies ls t 'and))
(defun remove-redundancies/or (ls)
  (remove-redundancies ls nil 'or))

;;;;;
; Helper functions for each form

(defun safely-negate (f)
  (cond
   ((equal f t) nil)
   ((equal f nil) t)
   ((and (consp f)
	 (equal (car f) 'not))
    (cadr f))
   (t `(not ,f))))

(defun simplify-not (f2)
  (let ((v (p-simplify f2)))
    (safely-negate v)))

(defun simplify-implies (e1 e2)
  (let ((e1 (p-simplify e1))
	(e2 (p-simplify e2)))
    (p-simplify `(or (not ,e1) ,e2))))

(defun simplify-if (e1 e2 e3)
  (let ((e1 (p-simplify e1)))
    (p-simplify
     `(and
       (or (not ,e1) ,e2)
       (or ,e1 ,e3)))))

(defun simplify-iff (iff)
  (let ((e1 (p-simplify (cadr iff)))
	(e2 (p-simplify (caddr iff))))
    (p-simplify `(and (or (not ,e1) ,e2)
		      (or (not ,e2) ,e1)))))

(defun dissolve-iff (es)
  (cond
   ((endp es) t)
   ((endp (cdr es)) (car es))
   (t `(iff ,(car es) ,(dissolve-iff (cdr es))))))

(defun simplify-and (args)
  (let ((recs (remove-redundancies/and (mapcar #'p-simplify args))))
    (cond
     ((equal (length recs) 0) t)
     ((equal (length recs) 1) (car recs))
     ((in nil recs) nil)
     ((has-variable-and-negation recs) nil)
     (t `(and . ,recs)))))

(defun simplify-or (args)
  (let ((recs (remove-redundancies/or (mapcar #'p-simplify args))))
    (cond
     ((equal (length recs) 0) nil)
     ((equal (length recs) 1) (car recs))
     ((in t recs) t)
     ((has-variable-and-negation recs) t)
     (t `(or . ,recs)))))

(defun p-simplify (f)
  (match f
   ((type boolean) f)
   ((type symbol) f)
   ((list 'not f2)
    (simplify-not f2))
   ((list 'implies e1 e2)
    (simplify-implies e1 e2))
   ((list 'if e1 e2 e3)
    (simplify-if e1 e2 e3))
   ((list* 'and args)
    (simplify-and args))
   ((list* 'or args)
    (simplify-or args))
   ((list* 'iff es)
    (let ((e (dissolve-iff es)))
      (if (and (consp e) (equal (car e) 'iff) (equal (length e) 3))
	  (simplify-iff e)
	(p-simplify e))))   
   ((type cons)
    (if (literalp f)
	(if (consp f)
	    (cons (acl2::intern-in-package-of-symbol
		   (symbol-name (car f)) 'acl2s::allp)
		  (cdr f)))
      (error (list "Invalid formula" f))))))


(defun dual (e)
  (cond
   ((equal e 'and) 'or)
   ((equal e 'or) 'and)))

(defun push-down-implies (f)
  (let ((e1 (cadr f))
	(e2 (caddr f)))
    (let ((not-e1 (push-down-nots `(not ,e1)))
	  (e2 (push-down-nots e2)))
      `(or ,not-e1 ,e2))))

(defun push-down-if (f)
  (let ((e1 (cadr f))
	(e2 (caddr f))
	(e3 (cadddr f)))
    (let ((e1 (push-down-nots e1))
	  (not-e1 (push-down-nots `(not ,e1)))
	  (e2 (push-down-nots e2))
	  (e3 (push-down-nots e3)))
      `(or (and ,e1 ,e2)
	   (and ,not-e1 ,e3)))))

(defun push-down-iff (f)
  (let ((e1 (cadr f))
	(e2 (caddr f)))
    `(and ,(push-down-implies `(implies ,e1 ,e2))
	  ,(push-down-implies `(implies ,e2 ,e1)))))


(defun push-down-nots (f)
  (match f
   ((type boolean) f)
   ((type symbol) f)
   ((list 'if test cons alt)
    (push-down-if f))
   ((list* 'iff fs)
    (let ((e (dissolve-iff fs)))
      (match e
	((list 'iff e1 e2) (push-down-iff e))
        (e (push-down-nots e)))))
   ((list 'implies a b)
    (push-down-implies f))
   ((list* tag es)
    (cond
     ((in tag '(and or))
      `(,tag . ,(mapcar #'push-down-nots es)))
     ((equal tag 'not)
      (let ((f (push-down-nots (car es))))
	(cond
	 ((literalp f) (safely-negate f))
	 ((equal (car f) 'not) (cadr f))
	 (t (let ((new-tag (dual (car f))))
	      `(,new-tag . ,(mapcar #'(lambda (e)
					(push-down-nots `(not ,e)))
				    (cdr f))))))))
     ((literalp f) f)))
   (t (error "Invalid formula: ~a" f))))

(defun p-reduce (f)
  (p-simplify (push-down-nots f)))
