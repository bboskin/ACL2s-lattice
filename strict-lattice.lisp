(defdata nodelist (listof var))
(defdata mpair (cons var var))
(defdata mrow (listof (oneof mpair nil)))
(defdata mrow+ (cons mpair mrow))
(defdata matrix (listof mrow))
;; A Lattice has a nodelist and a matrix, but deeper properties
(defdata Lattice- (cons nodelist matrix))

;; Is this a valid Lattice?
;; it needs to be such that
;; every mrow has the right length
;; every symbol occurring in each pair is in the nodelist
;; the length of the matrix = the length of the nodelist

(defunc in (x ls)
  :input-contract (true-listp ls)
  :output-contract (booleanp (in x ls))
  (cond
   ((endp ls) nil)
   ((equal x (car ls)) t)
   (t (in x (cdr ls)))))

(defunc all-non-nilp (lat)
  :input-contract (matrixp lat)
  :output-contract (booleanp (all-non-nilp lat))
  (cond
   ((endp lat) t)
   ((in nil (car lat)) nil)
   (t (all-non-nilp (cdr lat)))))

(defunc all-have-len (n lat)
  :input-contract (and (natp n) (matrixp lat))
  :output-contract (booleanp (all-have-len n lat))
  (cond
   ((endp lat) t)
   ((equal (len (car lat)) n)
    (all-have-len n (cdr lat)))
   (t nil)))

(defunc row-is-valid (row l)
  :input-contract (and (mrowp row) (nodelistp l))
  :output-contract (booleanp (row-is-valid row l))
  (cond
   ((endp row) t)
   (t (let ((curr (car row)))
	(and (in (car curr) l) (in (cdr curr) l)
	     (row-is-valid (cdr row) l))))))

(defunc matrix-has-proper-rows (m l)
  :input-contract (and (matrixp m) (nodelistp l))
  :output-contract (booleanp (matrix-has-proper-rows m l))
  (cond
   ((endp m) t)
   (t (and (row-is-valid (car m) l)
	   (matrix-has-proper-rows (cdr m) l)))))


;; This tells whether or not l is a complete Lattice
(defunc Latticep (l)
  :input-contract t
  :output-contract (booleanp (Latticep l))
  (if (not (lattice-p l)) nil
    (let* ((nl (car l))
	   (matrix (cdr l))
	   (numvars (len nl)))
      (and (equal (len matrix) numvars)
	   (all-non-nilp matrix)
	   (all-have-len numvars matrix)
	   (matrix-has-proper-rows matrix nl)))))

(defunc VarInDomainp (v nl)
  :input-contract  (nodelistp nl)
  :output-contract (booleanp (VarInDomainp v nl))
  (and (varp v) (in v nl)))

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

#| L1 looks like:

    All
   /   \
  A    B
  \   /
  Bottom

|#



;; The first list is the node names and its index is
;; where that node is represented in the Matrix

;; Then, we have the adjacencty matrix. It contains pairs, where the car of
;; each pair is the meet of the two given 
(defconst *L1*
  ;; vars w/ indices
  '((All A B Bottom) .
   ;; (Meet . Join) for all variables
    (((All . All)    (A . All)    (B . All)      (Bottom . All))
     ((A . All)      (A . A)      (Bottom . All) (Bottom . A))
     ((B . All)      (B . All)    (B . B)        (Bottom . B))
     ((Bottom . All) (Bottom . A) (Bottom . B)   (Bottom . Bottom)))))

(lattice-p *L1*)
(check= t (Latticep *L1*))
(check= nil (Latticep (cons '(All Bottom) '())))

(defunc getRow (nl u lat)
  :input-contract (and (nodelistp nl) (matrixp lat)
		       (equal (len nl) (len lat))
		       (VarInDomainp u nl))
  :output-contract (and (mrowp (getRow nl u lat))
			(in (getRow nl u lat) lat))
  (cond
   ((equal (car nl) u) (car lat))
   (t (getRow (cdr nl) u (cdr lat)))))

(defunc getPair- (nl v row)
  :input-contract (and (nodelistp nl) (mrowp row)
		       (equal (len nl) (len row))
		       (VarInDomainp v nl))
  :output-contract (or (equal (getPair- nl v row) nil)
		       (mpairp (getPair- nl v row)))
  (cond
   ((equal (car nl) v) (car row))
   (t (getPair- (cdr nl) v (cdr row)))))

(defthm getPair-pair
  (implies (and (nodelistp nl) (mrowp row)
		(equal (len nl) (len row))
		(VarInDomainp v nl)
		(not (in nil row)))
	   (mpairp (getPair- nl v row))))
#|
(defthm in-lat-len
  (implies (and (nodelistp nl) (matrixp lat)
		(Latticep (cons nl lat))
		(mrowp x)
		(in x lat))
	   (equal (len x) (len nl))))
|#

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
#|
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

(defunc getPair (u v nl lat)
  :input-contract (and (nodelistp nl) (matrixp lat)
		       (Latticep (cons nl lat))
		       (VarInDomainp u nl)
		       (VarInDomainp v nl))
  :output-contract (or (equal nil (getPair u v nl lat))
		       (mpairp (getPair u v nl lat)))
  (getPair- nl v (getRow nl u lat)))

(defthm getPair-with-Lattice
  (implies (and (Latticep (cons nl l))
		(varp u) (varp v)
		(in u nl) (in v nl))
	   (mpairp (getPair u v l))))

;; Fundamental methods for Lattice.
;; The operations are:

;; addNode
;; setMeet(u, v, m, L) : Node Node Node Lattice -> Lattice
;; setJoin(u, v, j, L) : Node Node Node Lattice -> Lattice
;; replaceMeet(u, v, m, L) : Node Node Node Lattice -> Lattice
;; replaceJoin(u, v, j, L) : Node Node Node Lattice -> Lattice

;; getMeet(u, v, L) : Node Node Lattice -> Node
;; getJoin(u, v, L) : Node Node Lattice -> Node
;; Latticep(L) : Lattice -> Boolean




(defun getMeet (u v L)
  #|:input-contract (and (varp u) (varp v) (Latticep L))
  :output-contract (or (equal (getMeet u v L) nil)
		       (varp (getMeet u v L)))|#
  (let ((v (getPair u v L)))
    (if v (car v) nil)))

(defun getJoin (u v L)
  #|:input-contract (and (varp u) (varp v) (Latticep L))
  :output-contract (or (equal (getJoin u v L) nil)
		       (varp (getJoin u v L)))|#
  (let ((v (getPair u v L)))
    (if v (cdr v) nil)))


(defunc getIndex (u nl)
  :input-contract (and (nodelistp nl) (VarInDomainp u nl))
  :output-contract (natp (getIndex u nl))
  (cond
   ((endp nl) 0)
   ((equal u (car nl)) 0)
   (t (+ 1 (getIndex u (cdr nl))))))

(defunc setCoordRow (m w row b)
  :input-contract (and (natp m) (varp w) (mrowp row) (booleanp b))
  :output-contract (mrowp (setCoordRow m w row b))
  (cond
   ((endp row) nil)
   ((zerop m)
    (let ((meet (caar row))
	  (join (cdar row)))
      (cons (if b `(,w . ,join) `(,meet . ,w)) (cdr row))))
   (t (cons (car row) (setCoordRow (- m 1) w (cdr row) b)))))

(defunc setCoord- (n m w lat b)
  :input-contract (and (natp n) (natp m) (varp w)
		       (matrixp lat) (booleanp b))
  :output-contract (matrixp (setCoord- n m w lat b))
  (cond
   ((endp lat) nil)
   ((zerop n) (cons (setCoordRow m w (car lat) b) (cdr lat)))
   (t (cons (car lat) (setCoord- (- n 1) m w (cdr lat) b)))))


(defunc setCoord (u v w L b)
  :input-contract (and (Latticep L)
		       (VarInDomainp u (car L))
		       (VarInDomainp v (car L))
		       (VarInDomainp w (car L))
		       (booleanp b))
  :output-contract (Lattice-p (setCoord u v w L b))
  (let ((nl (car L))
	(lat (cdr L)))
    (let ((u-i (getIndex u nl))
	  (v-i (getIndex v nl)))
      (cons nl (setCoord- u-i v-i w lat b)))))



(defunc setMeet (u v w L)
  :input-contract (and (Latticep L)
		       (VarInDomainp u (car L))
		       (VarInDomainp v (car L))
		       (VarInDomainp w (car L)))
  :output-contract (Lattice-p (setMeet u v w L))
  (setCoord u v w L t))

(defunc setJoin (u v w L)
  :input-contract (and (Latticep L)
		       (VarInDomainp u (car L))
		       (VarInDomainp v (car L))
		       (VarInDomainp w (car L)))
  :output-contract (Lattice-p (setJoin u v w L))
  (setCoord u v w L nil))

