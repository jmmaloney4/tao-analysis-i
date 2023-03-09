open Classical

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
theorem four_not_zero : four ≠ zero :=
  have h1 : succ three = four := rfl
  have h2 : zero ≠ succ three := zero_not_succ three
  have h3 : zero ≠ four := Eq.symm h1 ▸ h2
  show four ≠ zero from Ne.symm h3

-- Axiom 2.4. Different natural numbers must have 
-- different successors; i.e., if n, m are natural 
-- numbers and n ≠ m, then n++ ≠ m++. Equivalently, 
-- if n++ = m++, then we must have n = m.
axiom succ_inj : ∀ n : nat, ∀ m : nat, n ≠ m → succ n ≠ succ m

-- Proposition 2.1.8. 6 is not equal to 2.
theorem six_not_two : six ≠ two :=
    have h1 : four ≠ zero := four_not_zero
    have h2 : succ four ≠ succ zero := succ_inj four zero h1
    have h3 : succ (succ four) ≠ succ (succ zero) := succ_inj (succ four) (succ zero) h2 
    show six ≠ two from h3

end nat