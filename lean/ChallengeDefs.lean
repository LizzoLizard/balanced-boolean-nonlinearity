/-
  ChallengeDefs.lean: the definitions used in the statements of `Challenge.lean`.

  No imports (Lean core only). This file and `Challenge.lean` are the trusted part:
  a reader only needs to check that these definitions mean what they say.
-/

namespace EvenBalancedChallenge

/-- Boolean vectors `F_2^n`, as functions `Fin n → Bool`. -/
abbrev Vec (n : Nat) := Fin n → Bool

/-- The zero vector. -/
def zeroVec {n : Nat} : Vec n := fun _ => false

/-- Prepend a coordinate. -/
def consVec {n : Nat} (b : Bool) (v : Vec n) : Vec (n + 1) :=
  fun i => match i with
    | ⟨0, _⟩ => b
    | ⟨k + 1, h⟩ => v ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- Drop the first coordinate. -/
def tailVec {n : Nat} (v : Vec (n + 1)) : Vec n :=
  fun i => v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

/-- Sum of an integer-valued function over all `2^n` vectors of `F_2^n`. -/
def sumVecs : {n : Nat} → (Vec n → Int) → Int
  | 0, g => g (fun i => Fin.elim0 i)
  | _ + 1, g =>
    sumVecs (fun v => g (consVec false v)) +
    sumVecs (fun v => g (consVec true v))

/-- Inner product `a · x` modulo 2. -/
def dot : {n : Nat} → Vec n → Vec n → Bool
  | 0, _, _ => false
  | _ + 1, a, x =>
    xor (a ⟨0, Nat.zero_lt_succ _⟩ && x ⟨0, Nat.zero_lt_succ _⟩)
        (dot (tailVec a) (tailVec x))

/-- Hamming weight `|{x : F(x) = true}|`. -/
def hammingWeight {n : Nat} (F : Vec n → Bool) : Int :=
  sumVecs (fun x => if F x then 1 else 0)

/-- Hamming distance `|{x : F(x) ≠ G(x)}|`. -/
def hammingDist {n : Nat} (F G : Vec n → Bool) : Int :=
  sumVecs (fun x => if F x != G x then 1 else 0)

/-- The affine function `x ↦ (a · x) ⊕ c`. -/
def affine {n : Nat} (a : Vec n) (c : Bool) (x : Vec n) : Bool :=
  xor (dot a x) c

/-- `F` is balanced: it takes the value `true` exactly `2^(n-1)` times. -/
def isBalanced (n : Nat) (F : Vec n → Bool) : Prop :=
  2 * hammingWeight F = (2 : Int) ^ n

/-- `nl(F) ≥ d`: `F` is at Hamming distance at least `d` from every affine function. -/
def hasNonlinearityAtLeast (n : Nat) (F : Vec n → Bool) (d : Int) : Prop :=
  ∀ (a : Vec n) (c : Bool), d ≤ hammingDist F (affine a c)

/-- An `(n, r)` S-box is balanced if every nonzero component `x ↦ v · F(x)` is balanced. -/
def isBalancedSBox (n r : Nat) (F : Vec n → Vec r) : Prop :=
  ∀ v : Vec r, v ≠ zeroVec → isBalanced n (fun x => dot v (F x))

/-- An `(n, r)` S-box has nonlinearity `≥ d` if every nonzero component does. -/
def hasVectorialNonlinearityAtLeast (n r : Nat) (F : Vec n → Vec r) (d : Int) : Prop :=
  ∀ v : Vec r, v ≠ zeroVec → hasNonlinearityAtLeast n (fun x => dot v (F x)) d

end EvenBalancedChallenge
