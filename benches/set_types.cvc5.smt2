
(set-logic ALL)
(set-option :produce-models true)

;; Sets are represented internally by Z3 as arrays from String to Bool
;; a[elem] = True if the set 'a' contains element 'elem'

(declare-const empty (Set String))
(declare-const x (Set String))
(declare-const y (Set String))
(declare-const z (Set String))

;; Don't know how to encode this just yet.
(assert (= empty (as set.empty (Set String))))

;; HACK!
;; (assert (= empty (set.minus (set.singleton "a") (set.singleton "a"))))

; x is the set containing elements "Baz", "Bar", and "Foo"
(assert (= x (set.insert "Baz" "Bar" "Foo" empty)))

; should return SAT!
(check-sat)
(get-model)

; these should be true!
(echo "Does x contain `Bar` and `Baz`?")
(assert (set.member "Bar" x))
(assert (set.member "Baz" x))
(check-sat)
(get-model)

;; should return UNSAT!
;;(push)
;;(echo "Does x contain `Quung`?")
;;(assert (set.member "Quung" x))
;;(check-sat)
;;(pop)

; y is the set containing elements "Bar" and "Quung"
;;(assert (= y (set.insert "Bar" "Quung" empty)))

; Z is the set containing "Bar"
;;(assert (= z (set.insert "Bar" empty)))

; Z is the intersection of x and y.  
;;(assert (= (set.inter x y) z))

;;(echo "Is `Bar` the intersection between x and y?")
;;(check-sat)


; If there is one, this command returns the assignment of the variables.
;;(get-model)
