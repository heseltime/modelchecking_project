; 2023-01-08, Modelchecking Project, Merel and Jack
;
; This code is based on the tutorial files' SMT example from December 15th (Adrian Rebola Pardo, JKU):
; As described in the project description, we needed this basis to work from to hand in a solution, i.e.
; the logic/level of abstraction and specification are largely the same, 
; but the encoding of buggy.c was adapted.
;

;
; BASICS AND SHORT fun_defs
;

(declare-datatypes ((State 0)) ((
    (locked (attempts Int))
    (unlocked)
    (open)
    (blocked))))

(define-fun valid_state ((s State)) Bool (=>
    ((_ is locked) s)
    (and (<= 0 (attempts s)) (< (attempts s) 3))))

(declare-datatypes ((Argument 0)) ((
    (partialpin)
    (correctpin)
    (wrongpin)
    (accept)
    (skip))))

(declare-fun keypadstate (Int) State)
(declare-fun keypresses (Int) Argument)

(define-fun is_open ((i Int)) Bool
    ((_ is open) (keypadstate i)))

(define-fun start () Int 0)
(define-fun end () Int 30)

;
; SPECIFICATION ENCODING
;

(define-fun partial_pin_locked_or_unlocked ((i Int)) Bool (=>
    (and
        ((_ is partialpin) (keypresses i))
        (or ((_ is locked) (keypadstate i)) ((_ is unlocked) (keypadstate i))))
    (= (keypadstate (+ i 1)) (keypadstate i))))

(define-fun correct_pin_locked ((i Int)) Bool (=>
    (and
        ((_ is correctpin) (keypresses i))
        ((_ is locked) (keypadstate i)))
    (= (keypadstate (+ i 1)) unlocked)))

(define-fun wrong_pin_locked ((i Int)) Bool (=>
    (and
        ((_ is wrongpin) (keypresses i))
        ((_ is locked) (keypadstate i)))
    (and
        (=> (< (attempts (keypadstate i)) 2)
            (= (keypadstate (+ i 1)) (locked (+ (attempts (keypadstate i)) 1))))
        (=> (>= (attempts (keypadstate i)) 2)
            (= (keypadstate (+ i 1)) blocked)))))

(define-fun complete_pin_unlocked ((i Int)) Bool (=>
    (and
        (or ((_ is correctpin) (keypresses i)) ((_ is wrongpin) (keypresses i)))
        ((_ is unlocked) (keypadstate i)))
    (= (keypadstate (+ i 1)) (locked 0))))

(define-fun open_unlocked ((i Int)) Bool (=>
    (and
        ((_ is accept) (keypresses i))
        ((_ is unlocked) (keypadstate i)))
    (= (keypadstate (+ i 1)) open)))

(define-fun keypress_open ((i Int)) Bool (=>
    ((_ is open) (keypadstate i))
    (and
        (=> ((_ is partialpin) (keypresses i))
            (= (keypadstate (+ i 1)) (locked 0)))
        (=> (not ((_ is partialpin) (keypresses i)))
            (= (keypadstate (+ i 1)) (keypadstate i))))))

(define-fun keypress_blocked ((i Int)) Bool (=>
    ((_ is blocked) (keypadstate i))
    (= (keypadstate (+ i 1)) blocked)))

(define-fun ignore_accept ((i Int)) Bool (=>
    (and
        ((_ is accept) (keypresses i))
        (not ((_ is unlocked) (keypadstate i)))) ; edited: now unlocked, was open
    (= (keypadstate (+ i 1)) (keypadstate i))))

(define-fun ignore_skip ((i Int)) Bool (=>
    ((_ is skip) (keypresses i))
    (= (keypadstate (+ i 1)) (keypadstate i))))

;
; START EDIT HERE:
; POTENTIAL BUG ENCODING COMES HERE (1)
;

; bug: The door can be opened after introducing three incorrect PIN
(define-fun open_in_blocked_state ((i Int)) Bool (=>
    ((_ is blocked) (keypadstate i)) ; if the door is blocked
    (= (keypadstate (+ i 1)) (keypadstate 0)) ; it opens 
))

;
;
;
;

; check attempts are correct (valid_state)
(assert (forall ((i Int)) (=>
    (and (<= start i) (<= i end))
    (valid_state (keypadstate i))
)))

; initial state: locked with zero attempts
(assert (= (keypadstate 0) (locked 0)))

(assert (forall ((i Int)) (=> (and
    (<= start i) (< i end))
    (and
        (partial_pin_locked_or_unlocked i)
        (correct_pin_locked i)
        (wrong_pin_locked i)
        (complete_pin_unlocked i)
        (open_unlocked i)
        (keypress_open i)
        (keypress_blocked i)
        (ignore_accept i)
        (ignore_skip i)
        ;
        ; BUG ENCODING REFERENCE COMES HERE (2)
        ;
        (open_in_blocked_state i)
        ;
        ;
        ;
    ))))

;
; END OF EDIT HERE
;

;
; IMPLEMENTATION ENCODING
;

(declare-fun implstate (Int) Int)

(define-fun impl_is_open ((i Int)) Bool
    (= (implstate i) 0))

;
;

(define-fun impl_partial_pin ((i Int)) Bool (and
    (=> (= (implstate i) 5)
        (= (implstate (+ i 1)) 1))
    (=> (not (= (implstate i) 5))
        (= (implstate (+ i 1)) (implstate i)))))

(define-fun impl_correct_pin ((i Int)) Bool (and
    (=> (<= (implstate i) 4)
        (and
            (=> (= (implstate i) 0)
                (= (implstate (+ i 1)) 1)) ; edited
            (=> (not (= (implstate i) 0))
                (= (implstate (+ i 1)) 0))))
    (=> (> (implstate i) 4)
        (= (implstate (+ i 1)) (implstate i)))))

(define-fun impl_wrong_pin ((i Int)) Bool (and
    (=> (<= (implstate i) 4)
        (and
            (=> (= (implstate i) 0)
                (= (implstate (+ i 1)) 1)) ; edited
            (=> (not (= (implstate i) 0))
                (= (implstate (+ i 1)) (+ (implstate i) 1)))))
    (=> (> (implstate i) 4)
        (= (implstate (+ i 1)) (implstate i)))))

(define-fun impl_accept ((i Int)) Bool (and
    (=> (= (implstate i) 0)
        (= (implstate (+ i 1)) 5))
    (=> (not (= (implstate i) 0))
        (= (implstate (+ i 1)) (implstate i)))))

(define-fun impl_skip ((i Int)) Bool
    (= (implstate (+ i 1)) (implstate i)))


(define-fun impl_keypress ((i Int)) Bool (and
    (=> ((_ is partialpin) (keypresses i)) (impl_partial_pin i))
    (=> ((_ is correctpin) (keypresses i)) (impl_correct_pin i))
    (=> ((_ is wrongpin) (keypresses i)) (impl_wrong_pin i))
    (=> ((_ is accept) (keypresses i)) (impl_accept i))
    (=> ((_ is skip) (keypresses i)) (impl_skip i)))) 


; coded state-start is 1
(assert (= (implstate 0) 1))

(assert (forall ((i Int)) (=>
    (and (<= start i) (< i end))
    (impl_keypress i))))

;
; COUNTERMODEL: failure (state!) is open/closed according to specification
;   but implementation is closed/open, i.e. the other one
;

(declare-fun failure () Int)

; "input that ... results in the door being open when it should have been closed"

(assert (and
    (<= start failure)
    (<= failure end)
    (not (= (is_open failure) (impl_is_open failure)))))

(check-sat)

(get-model)

(eval (keypresses 0))
(eval (keypresses 1))
(eval (keypresses 2))
(eval (keypresses 3))
(eval (keypresses 4))
(eval (keypresses 5))
(eval (keypresses 6))
(eval (keypresses 7))
(eval (keypresses 8))
(eval (keypresses 9))
(eval (keypresses 10))
(eval (keypresses 11))
(eval (keypresses 12))
(eval (keypresses 13))
(eval (keypresses 14))
(eval (keypresses 15))
(eval (keypresses 16))
(eval (keypresses 17))
(eval (keypresses 18))
(eval (keypresses 19))
(eval (keypresses 20))
(eval (keypresses 21))
(eval (keypresses 22))
(eval (keypresses 23))
(eval (keypresses 24))
(eval (keypresses 25))
(eval (keypresses 26))
(eval (keypresses 27))
(eval (keypresses 28))
(eval (keypresses 29))

(exit)