(declare-datatypes ((State 0)) ((
    (locked (attempts Int))
    (unlocked)
    (open)
    (blocked))))
; enumeration of states

(define-fun valid_state ((s State)) Bool (=>
    ((_ is locked) s)
    (and (<= 0 (attempts s)) (< (attempts s) 3))))
; state locked in terms of attempts

(declare-datatypes ((Argument 0)) ((
    (partialpin)
    (correctpin)
    (wrongpin)
    (accept)
    (skip))))
; keypresses

(declare-fun keypadstate (Int) State)
(declare-fun keypresses (Int) Argument)

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
        (not ((_ is open) (keypadstate i))))
    (= (keypadstate (+ i 1)) (keypadstate i))))

(define-fun ignore_skip ((i Int)) Bool (=>
    ((_ is skip) (keypresses i))
    (= (keypadstate (+ i 1)) (keypadstate i))))

(define-fun is_open ((i Int)) Bool
    ((_ is open) (keypadstate i)))

(define-fun start () Int 0)
(define-fun end () Int 6)

(assert (forall ((i Int)) (=>
    (and (<= start i) (<= i end))
    (valid_state (keypadstate i))
)))
; see above: valid state concerns attempts

(assert (= (keypadstate 0) (locked 0)))
; starting point

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
        (ignore_skip i)))))
; above definitions

(declare-fun implstate (Int) Int)
; state transitions encoded in c

; implementation state descriptions:
(define-fun impl_partial_pin ((i Int)) Bool (and
    (=> (= (implstate i) 5)
        (= (implstate (+ i 1)) 1))
    (=> (not (= (implstate i) 5))
        (= (implstate (+ i 1)) (implstate i)))))

(define-fun impl_correct_pin ((i Int)) Bool (and
    (=> (<= (implstate i) 4)
        (and
            (=> (= (implstate i) 0)
                (= (implstate (+ i 1)) (+ (implstate i) 1)))
            (=> (not (= (implstate i) 0))
                (= (implstate (+ i 1)) 0))))
    (=> (> (implstate i) 4)
        (= (implstate (+ i 1)) (implstate i)))))

(define-fun impl_wrong_pin ((i Int)) Bool (and
    (=> (<= (implstate i) 4)
        (and
            (=> (= (implstate i) 0)
                (= (implstate (+ i 1)) (+ (implstate i) 1)))
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
; calling implementation state descriptions

(define-fun impl_is_open ((i Int)) Bool
    (= (implstate i) 0))

(assert (= (implstate 0) 1))

(assert (forall ((i Int)) (=>
    (and (<= start i) (< i end))
    ; 
    (impl_keypress i))))
    ; all the implementation checks

(declare-fun failure () Int)

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
(exit)
