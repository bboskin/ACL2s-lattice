(in-package :lattice)

#|
(defdata nodelist (listof var))
(defdata mpair (cons symbol symbol))
(defdata mrow (listof mpair))
(defdata mrow+ (cons mpair mrow))
(defdata matrix (listof mrow))
;; A Lattice has a nodelist and a matrix, but deeper properties
(defdata Lattice- (cons nodelist matrix))
|#
;; Is this a valid Lattice?
;; it needs to be such that
;; every mrow has the right length
;; every symbol occurring in each pair is in the nodelist
;; the length of the matrix = the length of the nodelist

(defun in (x ls)
  (cond
   ((endp ls) nil)
   ((equal x (car ls)) t)
   (t (in x (cdr ls)))))

(defun snoc (x ls)
  (cond
   ((endp ls) (list x))
   (t (cons (car ls) (snoc x (cdr ls))))))


(defun row-non-nil (row)
  (reduce #'(lambda (x ans) (and ans (car x) (cdr x)))
	  row
	  :initial-value t
	  :from-end t))

(defun all-non-nilp (lat)
  (reduce #'(lambda (x ans) (and ans (row-non-nil x)))
	  lat
	  :initial-value t
	  :from-end t))

(defun all-have-len (n lat)
  (reduce #'(lambda (x ans) (and ans (equal (length x) n)))
	  lat
	  :initial-value t
	  :from-end t))

(defun row-is-valid (row l)
  (reduce #'(lambda (x ans) (and ans (in (car x) l) (in (cdr x) l)))
	  row
	  :initial-value t
	  :from-end t))

(defun matrix-has-proper-rows (m l)
  (reduce #'(lambda (x ans) (and ans (row-is-valid x l)))
	  m
	  :initial-value t
	  :from-end t))

(defun nodelistp (r)
  (reduce #'(lambda (x ans) (and ans (symbolp x)))
	  r
	  :initial-value t))

(defun mrowp (r)
  (reduce #'(lambda (x ans) (and ans (consp x)
				 (symbolp (car x))
				 (symbolp (cdr x))))
	  r
	  :initial-value t
	  :from-end t))

(defun lattice-p (l)
  (and (consp l)
       (listp l)
       (reduce #'(lambda (x ans) (and ans (mrowp x)))
	       (cdr l)
	       :initial-value t
	       :from-end t)))

; tells if values are within the domain of the lattice
(defun VarInDomainp (v nl)
  (and (symbolp v) (in v nl)))


;; Fundamental methods for Lattice.
;; The operations are:

;; Here, Node really just means symbol

;; addNode(v, L) : Node Lattice -> Lattice                       DONE
;; setMeet(u, v, m, L) : Node Node Node Lattice -> Lattice       DONE
;; setJoin(u, v, j, L) : Node Node Node Lattice -> Lattice       DONE
;; getMeet(u, v, L) : Node Node Lattice -> Node                  DONE
;; getJoin(u, v, L) : Node Node Lattice -> Node                  DONE
;; Latticep(L) : Lattice -> Boolean                              DONE

;; This tells whether or not l is a complete Lattice
(defun Latticep (l)
  (and (lattice-p l)
    (let* ((nl (car l))
	   (matrix (cdr l))
	   (numvars (length nl)))
      (and (equal (length matrix) numvars)
	   (all-non-nilp matrix)
	   (all-have-len numvars matrix)
	   (matrix-has-proper-rows matrix nl)))))

#|
(defthm Lattice-len=
  (implies (and (nodelistp nl)
		(matrixp lat)
		(Latticep (cons nl lat)))
	   (equal (len nl) (len lat))))

(defthm Lattice-rowlen=
  (implies (and (nodelistp nl)
		(matrixp lat)
		(Latticep (cons nl lat))
		(true-listp x)
		(in x lat))
	   (equal (len x) (len nl))))
|#
#| L1 looks like:

    All
   /   \
  A    B
  \   /
  Bottomp

|#



;; The first list is the node names and its index is
;; where that node is represented in the Matrix

;; Then, we have the adjacencty matrix. It contains pairs, where the car of
;; each pair is the meet of the two given 
(defparameter *L1*
  ;; vars w/ indices
  '((Allp A B Bottomp) .
   ;; (Meet . Join) for all variables
    (((Allp . Allp)    (A . Allp)    (B . Allp)      (Bottomp . Allp))
     ((A . Allp)      (A . A)      (Bottomp . Allp) (Bottomp . A))
     ((B . Allp)      (Bottomp . Allp)    (B . B)        (Bottomp . B))
     ((Bottomp . Allp) (Bottomp . A) (Bottomp . B)   (Bottomp . Bottomp)))))

(assert (latticep *L1*))

;; Helpers for getMeet, getJoin

(defun getRow (nl u lat)
  (cond
   ((endp nl) nil)
   ((endp lat) nil)
   ((equal (car nl) u) (car lat))
   (t (getRow (cdr nl) u (cdr lat)))))

(defun getPair- (nl v row)
  (cond
   ((endp nl) nil)
   ((endp row) nil)
   ((equal (car nl) v) (car row))
   (t (getPair- (cdr nl) v (cdr row)))))

#|
(defthm getPair-pair
  (implies (and (nodelistp nl) (mrowp row)
		(equal (len nl) (len row))
		(VarInDomainp v nl)
		(not (in nil row)))
	   (mpairp (getPair- nl v row))))

(defthm in-lat-len
  (implies (and (nodelistp nl) (matrixp lat)
		(Latticep (cons nl lat))
		(mrowp x)
		(in x lat))
	   (equal (len x) (len nl))))

(defthm in-lat-non-nil
  (implies (and (matrixp lat)
		(all-non-nilp lat)
		(true-listp x)
		(in x lat))
	   (not (in nil x))))

(defthm getRow-in-lat
  (implies (and (nodelistp nl) (matrixp lat)
		(Latticep (cons nl lat))
		(VarInDomainp v nl))
	   (in (getRow nl v lat) lat)))

(defthm getRow-non-nil
  (implies (and (nodelistp nl) (matrixp lat)
		(Latticep (cons nl lat))
		(VarInDomainp v nl))
	   (not (in nil (getRow nl v lat))))
  :hints (("Goal" :use (getRow-in-lat in-lat-non-nil))))

(defthm getPair-correct
  (implies (and (nodelistp nl) (matrixp lat)
		(Latticep (cons nl lat))
		(VarInDomainp u nl)
		(VarInDomainp v nl))
	   (mpairp (getPair- nl u (getRow nl v lat))))
  :hints (("Goal" :do-not-induct t)))
|#


(defun getPair (u v nl lat)
  (getPair- nl v (getRow nl u lat)))


(defun getMeet (u v L)
  (if (not (and (Lattice-p L)
		(VarInDomainp v (car L))
		(VarInDomainp u (car L))))
      nil
    (car (getPair u v (car L) (cdr L)))))

(defun getJoin (u v L)
  (if (not (and (Lattice-p L)
		(VarInDomainp v (car L))
		(VarInDomainp u (car L))))
      nil
    (cdr (getPair u v (car L) (cdr L)))))

(assert (equal 'Bottomp (getMeet 'Bottomp 'Bottomp *L1*)))
(assert (equal 'Allp (getJoin 'A 'B *L1*)))
(assert (equal 'A (getMeet 'A 'A *L1*)))
(assert (equal 'Allp (getJoin 'Allp 'Bottomp *L1*)))


;; Helpers for setMeet, setJoin

(defun setCoordRow (nl v w row b)
  (cond
   ((endp row) nil)
   ((endp nl) nil)
   ((equal (car nl) v)
    (let ((meet (caar row))
	  (join (cdar row)))
      (cons (if b `(,w . ,join) `(,meet . ,w)) (cdr row))))
   (t (cons (car row) (setCoordRow (cdr nl) v w (cdr row) b)))))

(defun setCoord- (nl u v w lat b init-nl)
  (cond
   ((endp lat) nil)
   ((endp nl) nil)
   ((equal (car nl) u) (cons (setCoordRow init-nl v w (car lat) b) (cdr lat)))
   (t (cons (car lat) (setCoord- (cdr nl) u v w (cdr lat) b init-nl)))))


(defun setCoord (u v w nl lat b)
  (if (or (not (nodelistp nl))
	  (not (Lattice-p (cons nl lat)))
	  (not (in b '(t nil)))
	  (not (VarInDomainp u nl))
	  (not (VarInDomainp v nl))
	  (not (VarInDomainp w nl)))
      nil
    (setCoord- nl u v w lat b nl)))

(defun setMeet (u v w L)
  (if (not (Lattice-p L)) L
    (let ((nl (car L))
	  (lat (cdr L)))
      (cons nl (setCoord u v w nl
			 (setCoord v u w nl lat t) t)))))

(defun setJoin (u v w L)
  (if (not (Lattice-p L)) L
    (let ((nl (car L))
	  (lat (cdr L)))
      (cons nl (setCoord u v w nl
			 (setCoord v u w nl lat nil) nil)))))

(assert (equal 'A (getJoin 'Allp 'Bottomp (setJoin 'Allp 'Bottomp 'A *L1*))))
(assert (equal 'Bottomp (getMeet 'Allp 'B (setMeet 'Allp 'B 'Bottomp *L1*))))


;; helpers for addNode

(defun newRow (len)
  (cond
   ((zerop len) nil)
   (t (cons (cons nil nil) (newRow (- len 1))))))

(defun addNode (v L)
  (if (or (not (Lattice-p L))
	  (VarInDomainp v (car L)))
      L
    (let* ((nl (car L))
	   (lat (cdr L))
	   (new-nl (snoc v nl))
	   (nl-len (length new-nl))
	   (new-lat (mapcar #'(lambda (x) (snoc (cons nil nil) x)) lat))
	   (new-lat (snoc (newRow nl-len) new-lat))
	   (res (cons new-nl new-lat))
	   (res (setJoin v v v res))
	   (res (setMeet v v v res))
	   (res (setJoin 'acl2s::Allp v 'acl2s::Allp res))
	   (res (setMeet 'acl2s::Allp v v res))
	   (res (setJoin 'acl2s::Bottomp v v res))
	   (res (setMeet 'acl2s::Bottomp v 'acl2s::Bottomp res)))
      res)))
#|
(assert (equal *L1* (addNode 'Allp *L1*)))
(assert (equal (cons 7 *L1*) (addNode 'Allp (cons 7 *L1*))))
(assert (Lattice-p (addNode 'Intp *L1*)))
(assert (equal 'Intp (getMeet 'Allp 'Intp (addNode 'Intp *L1*))))
(assert (equal 'Allp (getJoin 'Intp 'Allp (addNode 'Intp *L1*))))
(assert (equal 'Bottomp (getMeet 'Intp 'Bottomp (addNode 'Intp *L1*))))
(assert (equal 'Intp (getJoin 'Bottomp 'Intp (addNode 'Intp *L1*))))
(assert (equal nil (getMeet 'A 'Intp (addNode 'Intp *L1*))))
|#
