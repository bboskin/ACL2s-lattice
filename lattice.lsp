#|Symbol Creation (thanks, Pete)|#
(defun symbol-string-app (l)
  (if (endp l)
      ""
    (concatenate 'string (symbol-name (car l))
                 (symbol-string-app (cdr l)))))

(defun make-symbl (l)
  (intern-in-package-of-symbol
   (symbol-string-app l)
   'acl2s::allp))

#|
Graphs have 2 Kinds of edges:
- Edges that denote subtypes and supertypes
- Edges that denote intersecting types

So, all vertices that are:
- not parents or children of one another via subtype edges
- are not connected, or do not have subtypes that are
  connected via intersection edges

are disjoint types.
|#

;; simple graph operations

;; Find the direct children of a node
(defun children (n g)
  (cond
   ((endp g) nil)
   ((equal (caar g) n)
    (cadar g))
   (t (children n (cdr g)))))

;; Takes a key, either 'subtype or 'intersects, and gives
;; the edges of that genre from a list of edges
(defun choose-children (key ls)
  (cond
   ((endp ls) nil)
   ((equal key (caar ls))
    (cons (cadar ls) (choose-children key (cdr ls))))
   (t (choose-children key (cdr ls)))))

(defun subtypes (n g)
  (choose-children 'subtype (children n g)))

(defun intersections (n g)
  (choose-children 'intersects (children n g)))

(progn (defun dfs-help (dest froms g visited key)
	 (cond
	  ((endp froms) nil)
	  ((endp g) nil)
	  ((>= (len visited) (len g)) nil)
	  (t 
	   (let ((next (car froms)))
	     (or (and (not (member next visited))
		      (dfs-inner dest next g (cons next visited) key))
		 (dfs-help dest (cdr froms) g (cons next visited) key))))))
       (defun dfs-inner (dest from g visited key)
	 (or (equal dest from)
	     (let ((e (choose-children key (children from g))))
	       (dfs-help dest e g visited key)))))

;; To determine if child is a subtype of parent in g
(defun subtype? (child parent g)
  (dfs-inner child parent g nil 'subtype))

(defun remove-supertypes (e s g)
  (cond
   ((endp s) (list e))
   (t (let ((a (car s))
	    (res (remove-supertypes e (cdr s) g)))
	(if (subtype? e a g) res
	  (cons a res))))))

(defun scons (a s)
  (cond
   ((endp s) (list a))
   ((equal a (car s)) s)
   (t (cons (car s) (scons a (cdr s))))))

(defun sunion (s1 s2)
  (cond
   ((endp s1) s2)
   (t (sunion (cdr s1) (scons (car s1) s2)))))

(defun difference (s1 s2)
  (cond
   ((endp s2) s1)
   ((member (car s2) s1)
    (difference (remove (car s2) s1) (cdr s2)))
   (t (difference s1 (cdr s2)))))

(defun set-intersection (s1 s2)
  (cond
   ((endp s1) nil)
   ((member (car s1) s2)
    (scons (car s1)
	   (set-intersection (cdr s1) s2)))
   (t (set-intersection (cdr s1) s2))))

(defun acl2s-last-result ()
  (let ((state *the-live-state*))
    (@ result)))

(defun acl2s-query (q)
  (let ((state *the-live-state*))
    (ld `((mv-let
           (erp val state)
           (acl2::trans-eval ',q 'acl2s-query state t)
           (assign result (list erp (cdr val))))))
    (acl2s-last-result)))

(defun acl2s-event (e)
  (let ((state *the-live-state*))
    (ld `((mv-let
           (erp val state)
           ,e
           (assign result (list erp val)))))
    (acl2s-last-result)))

(defun create-recognizer (sym)
  (make-symbl (list sym 'p)))

(defun is-subtype? (a b)
  (let ((r1 (create-recognizer a))
	(r2 (create-recognizer b)))
    (progn (acl2s-query `(thm (implies (,r1 e) (,r2 e))))
	   (let ((v (acl2s-last-result)))
	     (not (caadr v))))))

(defun intersects? (a b)
  (let ((r1 (create-recognizer a))
	(r2 (create-recognizer b)))
    (progn (acl2s-query `(thm (implies (,r1 e) (not (,r2 e)))))
	   (let ((v (acl2s-last-result)))
	     (caadr v)))))

;; splits syms into two lists:
;; first is the types that syms is not a subtype of
;; second is the types that syms is a subtype of
(defun split-subtypes (ty syms state)
  (cond
   ((endp syms) (list nil nil))
   (t (let ((a (car syms))
	    (d (cdr syms)))
	(let ((good? (is-subtype? a ty)))
	  (let ((v (split-subtypes ty d state)))
	    (let ((ks (car v))
		  (ds (cadr v)))
	      (if good?
		  (list ks (cons a ds))
		(list (cons a ks) ds)))))))))

; These three functions can be greatly optimized
(defun add-edge (p c mode g)
  (cond
   ((endp g) (list (list p (list mode c))))
   ((equal (caar g) p)
    (cons (list p (cons (list mode c) (cadar g)))
	  (cdr g)))
   (t (cons (car g) (add-edge p c mode (cdr g))))))

(defun add-parent-edges (ty pars g)
  (cond
   ((endp pars) g)
   (t (add-parent-edges ty (cdr pars)
			(add-edge (car pars) ty 'subtype g)))))

(defun add-intersection-edges (ty pars g)
  (cond
   ((endp pars) g)
   (t (let* ((g (add-edge ty (car pars) 'intersects g))
	     (g (add-edge (car pars) ty 'intersects g)))
	(add-intersection-edges ty (cdr pars) g)))))


(defun make-edges (mode es)
  (cond
   ((endp es) nil)
   (t (cons (list mode (car es))
	    (make-edges mode (cdr es))))))

(defun add-child-edges (ty edges g)
  (cond
   ((endp g) (list (list ty edges)))
   ((equal (caar g) ty)
    (cons (list ty (append (cadar g) edges)) (cdr g)))
   (t (cons (car g)
	    (add-child-edges ty edges (cdr g))))))


(defun remove-all-children (kids ls)
  (cond
   ((endp ls) nil)
   ((and (equal (caar ls) 'subtype)
	 (member (cadar ls) kids))
    (remove-all-children kids (cdr ls)))
   (t (cons (car ls)
	    (remove-all-children kids (cdr ls))))))

(defun remove-parent-edges (pars kids g)
  (cond
   ((endp g) nil)
   ((member (caar g) pars)
    (cons (list (caar g) (remove-all-children kids (cadar g)))
	  (remove-parent-edges pars kids (cdr g))))
   (t (cons (car g)
	    (remove-parent-edges pars kids (cdr g))))))

(defun place-wrt-subtypes-help
     (ty candidates saved-pars saved-kids g visited state)
   (cond
    ((>= (len visited) (len g)) (list saved-pars saved-kids))
    ((endp candidates) (list saved-pars saved-kids))
    ((endp g) (list saved-pars saved-kids))
    (t (let ((next (car candidates)))
	 (if (member next visited)
	     (place-wrt-subtypes-help ty (cdr candidates)
				      saved-pars saved-kids
				      g visited state)
	   (let ((v (place-wrt-subtypes1 ty next
					 saved-pars saved-kids
					 g (cons next visited) state)))
	     (let ((new-pars (car v))
		   (new-kids (cadr v)))
	       (place-wrt-subtypes-help ty (cdr candidates)
					new-pars new-kids
					g visited state))))))))

; 2 mutually-recursive fns
(defun place-wrt-subtypes1
    (ty par saved-pars saved-kids g visited state)
  (let ((good? (is-subtype? ty par)))
    (if good?
	(let ((next (subtypes par g)))
	  (let ((pr (split-subtypes ty next state)))
	    (let ((saved-kids (sunion saved-kids (cadr pr)))
		  (next (car pr))
		  (saved-pars (remove-supertypes par saved-pars g)))
	      (place-wrt-subtypes-help ty next
				       saved-pars saved-kids
				       g visited state))))
      (list saved-pars saved-kids))))

(defun place-wrt-subtypes (ty g state)
  (let ((v (place-wrt-subtypes1 ty (*TOP*) (list (*TOP*)) nil g nil state)))
    (let ((parents (car v))
	  (children (cadr v)))
      (let* ((g (add-parent-edges ty parents g))
	     (g (remove-parent-edges parents children g))
	     (g (add-child-edges ty (make-edges 'subtype children) g)))
	(list g parents children)))))


#|
To add a type T to the universe,
we need to:
 -- put it in the right spot in terms of subtype edges
    -- for each node T2, if it can be proven that T ∈ T2,
       then T will have a subtype edge connecting it to T2, or a descendant to T2.
    Only the lowest descendent gets the edge
 -- check for intersections:
    -- for each of T2's subtypes, all intersection edges are added for T2
    -- for each intersection that T2's parent has,
       which is not intersecting with a child of T2
       (because those were already added), a check is needed
|#

(defun all-ints (c g)
  (cond
   ((endp c) nil)
   (t (sunion (intersections (car c) g)
	      (all-ints (cdr c) g)))))

(defun all-subs (c g)
  (cond
   ((endp c) nil)
   (t (sunion (subtypes (car c) g)
	      (all-subs (cdr c) g)))))

(defun filter-inters (ty todo g state)
  (cond
   ((endp todo) nil)
   (t (let ((yes? (intersects? ty (car todo))))
	(let ((res (filter-inters ty (cdr todo) g state)))
	    (if yes? (cons (car todo) res) res))))))

(defun add-intersect-edges (ty todo g state)
  (add-intersection-edges
   ty (filter-inters ty todo g state) g))

(defun add-to-universe (ty g state)
  (let ((v (place-wrt-subtypes ty g state)))
    (let* ((g (car v))
	   (parents (cadr v))
	   (children (caddr v))
	   (child-ints (all-ints children g))
	   (g (add-intersection-edges ty child-ints g))
	   (par-intersects (all-ints parents g))
	   (par-children (all-subs parents g ))
	   (to-examine (difference (sunion par-children par-intersects)
				   (sunion child-ints (list ty)))))
      (add-intersect-edges ty to-examine g state))))

(defun test-addition (ty)
  (let ((v (add-to-universe ty (*G*) state)))
    (progn (defun *G* () v)
	   (*G*))))

;; using all!
(defun *TOP* () 'All)
(defun *G* () '((All nil)))
(test-addition 'cons)
(test-addition 'nat)
(test-addition 'true-list)
(test-addition 'boolean)
(test-addition 'rational)
(test-addition 'integer)
(test-addition 'neg)
(test-addition 'end)
(test-addition 'symbol)
(test-addition 'var)
;;; Queries about ^, v, ~


(defun is-supertype-of-any? (e ls g)
  (cond
   ((endp ls) nil)
   ((subtype? (car ls) e g) t)
   (t (is-supertype-of-any? e (cdr ls) g))))

(defun remove-supers (ls seen g)
  (cond
   ((endp ls) seen)
   ((is-supertype-of-any? (car ls) (append (cdr ls) seen) g)
    (remove-supers (cdr ls) seen g))
   (t (remove-supers (cdr ls) (cons (car ls) seen) g))))

(defun keep-small (ls g)
  (remove-supers ls nil g))


(defun has-intersection-with-some (e1 es2 g)
  (cond
   ((endp es2) nil)
   ((has-intersection e1 (car es2) g) t)
   (t (has-intersection-with-some e1 (cdr es2) g))))

(defun any-intersect (es1 es2 g)
  (cond
   ((endp es1) nil)
   (t (or (has-intersection-with-some (car es1) es2 g)
	  (any-intersect (cdr es1) es2 g)))))

(defun has-intersection (e1 e2 g)
  (or (and (member e1 (intersections e2 g)) t)
      (subtype? e1 e2 g)
      (subtype? e2 e1 g)
      (any-intersect (subtypes e1 g)
		     (subtypes e2 g)
		     g)))

;;;;;;;;;;
; More useful high-level operations used below
;;;;;;;;;;

(defun get-keys (g)
  (cond
   ((endp g) nil)
   (t (cons (caar g) (get-keys (cdr g))))))

(defun find-common-parents (t1 t2 ks g)
  (cond
   ((endp ks) nil)
   ((and (subtype? t1 (car ks) g)
	 (subtype? t2 (car ks) g))
    (cons (car ks) (find-common-parents t1 t2 (cdr ks) g)))
   (t (find-common-parents t1 t2 (cdr ks) g))))

(defun find-common-subtypes (t1 t2 ks g)
  (cond
   ((endp ks) nil)
   ((and (subtype? (car ks) t1 g)
	 (subtype? (car ks) t2 g))
    (cons (car ks) (find-common-subtypes t1 t2 (cdr ks) g)))
   (t (find-common-subtypes t1 t2 (cdr ks) g))))

(defun find-disjoint-types (t1 ks g)
  (cond
   ((endp ks) nil)
   ((has-intersection t1 (car ks) g)
    (find-disjoint-types t1 (cdr ks) g))
   (t (cons (car ks)
	    (find-disjoint-types t1 (cdr ks) g)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Naive implementations:                                       ;;
;; what's the best we can do without ever creating              ;;
;; a new type, returning a group of types?,                     ;;
;; or knowing the relative cardinalities of each type           ;;
;; other than that subtypes must be leq in size to their parents;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;
;; Intersection

#|
Suppose that we want a type S such that for two types T₁ and T₂,
it is guaranteed that S ⊆ {T₁ ∩ T₂}. If T₁ ⊆ T₂ or T₂ ⊆ T₁, then
we can get a precise S: either T₁ or T₂ is such a set. However,
if this is not the case, then there are two options: T₁ has no
intersection with T₂, which is determinable from our graph, so we can
again get a precise S.

However, when T₁ and T₂ have an unknown intersection, without using
more than the information currently in the lattice, there is no type
S guaranteed to have the property.

Now suppose that we want a type S such that for two types T₁ and T₂ 
it is guaranteed that {T₁ ∩ T₂} ⊆ S. Here, again, if T₁ ⊆ T₂, T₂ ⊆ T₁, or 
T₁ ∩ T₂ = ∅, then we can knowingly give a precise S. Otherwise, the best we
can suggest, withhout introducing new types, is simply one of the types given.
We arbitrarily choose the first one.
|#

;; When mode is non-nil, this macro offers an S such that {T₁ ∩ T₂} ⊆ S.
;; Otherwise, it offers an S such that S ⊆ {T₁ ∩ T₂}.
(defmacro find-intersection (t1 t2 &rest mode)
  `(let ((g (*G*)))
     (cond
      ((subtype? ',t1 ',t2 g) ',t1)
      ((subtype? ',t2 ',t1 g) ',t2)
      ((has-intersection ',t1 ',t2 g)
       (list "Help!" (if ',mode ',t1 nil)))
      (t nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;
;; Union

#|
Suppose that we want a type S such that for two types T₁ and T₂,
it is guaranteed that S ⊆ {T₁ ∪ T₂}. If T₁ ⊆ T₂ or T₂ ⊆ T₁, then
we can get a precise S: either T₁ or T₂ is such a set.

However, if this is not the case, and our goal is to provide a
single type that is in the lattice, then we need to arbitrarily
choose a type: we can choose T₁, T₂, or some subset of a mix of them.

We will choose to provide a type that is a subtype of both T₁ and T₂,
if one exists, and otherwise to provide T₁.

Now suppose that we want a type S such that for two types T₁ and T₂ 
it is guaranteed that {T₁ ∪ T₂} ⊆ S. Here, again, if T₁ ⊆ T₂, T₂ ⊆ T₁, or 
T₁ ∩ T₂ = ∅, then we can knowingly give a precise S. Otherwise, the best we
can suggest, withhout introducing new types, is simply one of the types given.
We arbitrarily choose the first one.
|#

(defmacro find-union (t1 t2 &rest mode)
  `(let ((g (*G*)))
    (cond
      ((subtype? ',t1 ',t2 g) ',t2)
      ((subtype? ',t2 ',t1 g) ',t1)
      (',mode
       (let ((parents
	      (keep-small
	       (find-common-parents ',t1 ',t2 (get-keys g) g) g))))
       (car parents))
      (t (let ((subs (keep-small
		   (find-common-subtypes ',t1 ',t2 (get-keys g) g) g)))
	   (if subs (car subs) ',t1))))))


;;;;;;;;;;;;;;;;;;;;;;;;;
;; Negation

#|
Suppose that we want a type S such that S ⊆ ¬T.

Here, if we were going to offer a single type, we would just use some
type that doesn't intersect T. Fine.  Because this already begs for
something better, and we can do better by offering a union, we will:
The union of all types S such that {S ∩ T} = ∅.
|#

(defmacro find-negation (t1)
  `(let ((g (*G*)))
     (let ((res (keep-large
		 (find-disjoint-types ',t1 (get-keys g) g) g)))
       (if (> (len res) 1)
	   (cons 'union-of res)
	 (car res)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Now, we want to consider what we               ;;
;; can do if we create a new type.                ;;
;; These programs will, if a tight bound          ;;
;; exists in the lattice, return that type,       ;;
;; and otherwise give the program a predicate     ;;
;; and enumerator that would let the user define  ;;
;; such a type                                    ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;
;; Intersection

#|
The method of creating an intersection is straightforward:

For the recognizer, it is simply the conjunction of the two previous recognizers.
For the enumerator, consider the intersection T of types T1 and T2.
(nth-T n) = (nth-T1 n) if (T2p (nth-T1 n)), else (nth-T2 n) if (T1p (nth-T2 n))
            and otherwise (nth-T1 (+ n 1))

However, consider the intersection of two infinite types which only have one common element, which can be achieved by (nth-T1 K) and (nth-T2 J). When nth-T is called with
N where N > K ^  N > J, then nth-T will not terminate. So, when N > 10,000, we reset 
N to zero in recursion. Because ACL2s has guaranteed, in this case, that there
is a non-empty intersection between T1 and T2, although it is possible that it is only reachable where K > 10,000 and J > 10,000, this is unlikely. (and so this solution is likely okay for now)
|#
(defun create-intersection-type (t1 t2)
  (let ((t1-rec (make-symbl `(,t1 p)))
	(t2-rec (make-symbl `(,t2 p)))
	(t1-enum (make-symbl `(nth- ,t1)))
	(t2-enum (make-symbl `(nth- ,t2)))
	(new-name (make-symbl `(,t1 -intersect- ,t2))))
    (let ((new-rec (make-symbl `(,new-name p)))
	  (new-enum (make-symbl `(,new-name -enum))))
      `(progn
	 (defun ,new-rec (e)
	   (and (,t1-rec e)
		(,t2-rec e)))
	 (defun ,new-enum (n)
	   (if (> n 10000)
	       (,new-enum 0)
	     (let ((e1 (,t1-enum n)))
	       (if (,t2-rec e1) e1
		 (let ((e2 (,t2-enum n)))
		   (if (,t1-rec e2) e2
		     (,new-enum (+ n 1))))))))
	 (acl2s::register-type ,new-name
			       :predicate ,new-rec
			       :enumerator ,new-enum)))))


(defmacro find-intersection2 (t1 t2)
  `(let ((g (*G*)))
     (cond
      ((subtype? ',t1 ',t2 g) ',t1)
      ((subtype? ',t2 ',t1 g) ',t2)
      ;; the case below is the only
      ;; one that changes from the definition above
      ((has-intersection ',t1 ',t2 g)
       (list "Try this definition:"
	     (create-intersection-type ',t1 ',t2)))
      (t nil))))

;;;;;;;;;;;;;;;;;
;; Union

#|
Union is pretty simple. There is already a type if
T1 or T2 is a subtype of the other.
T1 + T2 = their parent
Otherwise, an interleaving of their  
|#

(defun create-union-type (t1 t2)
  (let ((t1-rec (make-symbl `(,t1 p)))
	(t2-rec (make-symbl `(,t2 p)))
	(t1-enum (make-symbl `(nth- ,t1)))
	(t2-enum (make-symbl `(nth- ,t2)))
	(new-name (make-symbl `(,t1 -union- ,t2))))
    (let ((new-rec (make-symbl `(,new-name p)))
	  (new-enum (make-symbl `(,new-name -enum))))
      `(progn
	 (defun ,new-rec (e)
	   (or (,t1-rec e)
	       (,t2-rec e)))
	 (defun ,new-enum (n)
	   (if (evenp n)
	       (,t1-enum (/ n 2))
	     (,t2-enum (/ (- n 1) 2))))
	 (acl2s::register-type ,new-name
			       :predicate ,new-rec
			       :enumerator ,new-enum)))))

(defun test-parents (a b pars)
  (cond
   ((endp pars) nil)
   (t (let ((r1 (create-recognizer a))
	    (r2 (create-recognizer b))
	    (parent (create-recognizer (car pars))))
	(progn (acl2s-query `(thm (implies (,parent e) (or (,r1 e) (,r2 e)))))
	       (let ((v (acl2s-last-result)))
		 (if (caadr v)
		     (test-parents a b (cdr pars))
		   (car pars))))))))

(defmacro find-union (t1 t2)
  `(let ((g (*G*)))
    (cond
      ((subtype? ',t1 ',t2 g) ',t2)
      ((subtype? ',t2 ',t1 g) ',t1)
      (t (let ((possibles
		(keep-small
		 (find-common-parents ',t1 ',t2 (get-keys g) g) g)))
	   (let ((already-have-a-type? (test-parents ',t1 ',t2 possibles)))
	     (if already-have-a-type?
		 already-have-a-type?
	       (create-union-type ',t1 ',t2))))))))


;;;;;;;;;;;;;;;;;
;; Negation


(defun create-negation-type (ty)
  (let ((rec (make-symbl `(,ty p)))
	(enum (make-symbl `(nth- ,ty))))))


(defmacro find-negation (t1)
  `(let ((g (*G*)))
     (let ((res (keep-large
		 (find-disjoint-types ',t1 (get-keys g) g) g)))
       (cond
	((endp res) NIL)
	(t ()))
       (if (> (len res) 1)
	   (cons 'union-of res)
	 (car res)))))
