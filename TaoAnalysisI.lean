import Mathlib.Tactic.Contrapose

open Classical

-- Section 2.1 The Peano axioms

-- Axiom 2.1. 0 is a natural number.
-- Axiom 2.2. If n is a natural number, then n++ is also a natural number.
inductive nat : Type | zero : nat | succ : nat → nat

namespace nat

-- Definition 2.1.3.
def one : nat := succ nat.zero
def two : nat := succ one
def three : nat := succ two
def four : nat := succ three
def five : nat := succ four
def six : nat := succ five

-- Proposition 2.1.4. 3 is a natural number.
#check three

-- Axiom 2.3. 0 is not the successor of any natural number; i.e.,
-- we have n++ ̸= 0 for every natural number n.
axiom zero_not_succ : ∀ n : nat, zero ≠ succ n

-- Proposition 2.1.6. 4 is not equal to 0.
theorem four_not_zero : four ≠ zero := by simp [four]
-- Wow

-- Axiom 2.4. Different natural numbers must have 
-- different successors; i.e., if n, m are natural 
-- numbers and n ≠ m, then n++ ≠ m++. Equivalently, 
-- if n++ = m++, then we must have n = m.
-- Lean actually generates this for us.
-- axiom succ_inj : ∀ n : nat, ∀ m : nat, n ≠ m → succ n ≠ succ m

-- Proposition 2.1.8. 6 is not equal to 2.
theorem six_not_two : six ≠ two := by
  simp [six, two, five, one]
  exact four_not_zero

-- Axiom 2.5 (Principle of mathematical induction). Let 
-- P(n) be any property pertaining to a natural number n. 
-- Suppose that P(0) is true, and suppose that whenever 
-- P(n) is true, P(n++) is also true. Then P(n) is true 
-- for every natural number n.
axiom induction : ∀ P : nat → Prop, P zero → (∀ n : nat, P n → P (succ n)) → ∀ n : nat, P n

-- Remark: It appears Axiom 2.5 is unneded for Lean.

-- Section 2.2 Addition
def add : nat → nat → nat
| zero, m => m
| succ n, m => succ (add n m)

-- Get to use the plus operator
instance : Add nat where add := add

-- Lemma 2.2.2. For any natural number n, n + 0 = n.
theorem add_zero (n : nat) : add n zero = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [add, ih]

-- Lemma 2.2.3. For any natural numbers n and m, 
-- n + (m++) = (n + m)++.
theorem add_succ (n m : nat) : n + (succ m) = succ (n + m) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : succ n + succ m = succ (n + succ m) := rfl
    repeat rw [h1, ih]
    rfl

-- Proposition 2.2.4 (Addition is commutative). For any natural 
-- numbers n and m, n + m = m + n.
theorem add_comm (n m : nat) : n + m = m + n := by
  induction n with
  | zero => 
      have h1 : zero + m = m := by rfl
      have h2 : m + zero = m := by apply add_zero
      rw [h1, h2]
  | succ n ih =>
      have h1 : succ n + m = succ (n + m) := by rfl
      have h2 : m + succ n = succ (m + n) := by apply add_succ
      rw [h1, ih, h2]

-- Proposition 2.2.5 (Addition is associative). For any natural 
-- numbers a,b,c, we have (a+b)+c=a+(b+c).
theorem add_assoc (a b c : nat) : (a + b) + c = a + (b + c) := by
  induction a with
  | zero =>
      have h1 : (zero + b) + c = b + c := by rfl
      have h2 : zero + (b + c) =  b + c := by rfl
      rw [h1, h2]
  | succ a ih =>
      have h1 : succ a + (b + c) = succ (a + (b + c)) := by rfl
      have h2 : succ a + b + c = succ ((a + b) + c) := by rfl
      rw [h2, ih, h1]

-- Proposition 2.2.6 (Cancellation law). Let a,b,c be natural 
-- numbers such that a+b=a+c. Then we have b=c.
theorem cancellation_law (a b c : nat) : (a + b) = (a + c) → b = c := by
  intro h
  induction a with
  | zero =>
    have h1 : b = zero + b := by rfl
    have h2 : c = zero + c := by rfl
    rw [h1, h2]
    exact h
  | succ a ih =>
    have h1 : succ a + b = succ (a + b) := by rfl
    have h2 : succ a + c = succ (a + c) := by rfl
    rw [h1,h2] at h
    apply ih
    apply succ.inj
    exact h

def is_positive : nat → Bool 
| zero => false
| succ _ => true 

-- Proposition 2.2.8. If a is positive and b is a natural number, then 
-- a+b is positive (and hence b + a is also, by Proposition 2.2.4).
theorem positive_add_stable (a b : nat) : is_positive a → is_positive (a + b) := by
cases a with
| zero => 
  intro h
  contradiction
| succ a =>
  intro _
  calc
    is_positive (succ a + b) = is_positive (succ (a + b)) := rfl
    _ = true := by simp [is_positive]

-- Corollary 2.2.9. If a and b are natural numbers such that a + b = 0, then a=0 and b=0.
theorem only_zeros_sum_to_zero (a b : nat) : a + b = zero → And (a = zero) (b = zero) := by
intros h0
have h1 : a + b = zero + zero := calc
  a + b = zero := h0
  _ = zero + zero := rfl








end nat