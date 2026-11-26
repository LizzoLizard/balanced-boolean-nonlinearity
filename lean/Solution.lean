/-
  Solution.lean: proofs of the statements in `Challenge.lean`.

  The proofs come from `EvenBalanced8Bound.lean`. Its definitions are written out separately
  from `ChallengeDefs.lean`, so the first section shows the two sets of definitions agree.
-/
import ChallengeDefs
import EvenBalanced8Bound

namespace EvenBalancedChallenge

/-! ## Bridge: the challenge definitions agree with those of `EvenBalanced8Bound` -/

private theorem sumVecs_eq : ∀ {n : Nat} (g : Vec n → Int), sumVecs g = EvenBalanced8Bound.sumVecs g
  | 0, _ => rfl
  | _ + 1, g => by
    rw [sumVecs, EvenBalanced8Bound.sumVecs, sumVecs_eq, sumVecs_eq]; rfl

private theorem dot_eq : ∀ {n : Nat} (a x : Vec n), dot a x = EvenBalanced8Bound.dot a x
  | 0, _, _ => rfl
  | _ + 1, a, x => by
    rw [dot, EvenBalanced8Bound.dot, dot_eq]; rfl

private theorem bal_iff {n : Nat} {F : Vec n → Bool} :
    isBalanced n F ↔ EvenBalanced8Bound.isBalanced n F := by
  unfold isBalanced EvenBalanced8Bound.isBalanced hammingWeight EvenBalanced8Bound.hammingWeight
  rw [sumVecs_eq]

private theorem nl_iff {n : Nat} {F : Vec n → Bool} {d : Int} :
    hasNonlinearityAtLeast n F d ↔ EvenBalanced8Bound.hasNonlinearityAtLeast n F d := by
  unfold hasNonlinearityAtLeast EvenBalanced8Bound.hasNonlinearityAtLeast hammingDist EvenBalanced8Bound.hammingDist
  have ha : ∀ (a : Vec n) (c : Bool), affine a c = EvenBalanced8Bound.affine a c := by
    intro a c; funext x; unfold affine EvenBalanced8Bound.affine; rw [dot_eq]
  simp only [sumVecs_eq, ha]

private theorem zero_eq {r : Nat} : (zeroVec : Vec r) = EvenBalanced8Bound.zeroVec := rfl

private theorem comp_eq {n r : Nat} (F : Vec n → Vec r) (v : Vec r) :
    (fun x => dot v (F x)) = (fun x => EvenBalanced8Bound.dot v (F x)) := by
  funext x; rw [dot_eq]

private theorem sbox_bal_iff {n r : Nat} {F : Vec n → Vec r} :
    isBalancedSBox n r F ↔ EvenBalanced8Bound.isBalancedSBox n r F := by
  unfold isBalancedSBox EvenBalanced8Bound.isBalancedSBox
  simp only [comp_eq, bal_iff, zero_eq]

private theorem vnl_iff {n r : Nat} {F : Vec n → Vec r} {d : Int} :
    hasVectorialNonlinearityAtLeast n r F d ↔ EvenBalanced8Bound.hasVectorialNonlinearityAtLeast n r F d := by
  unfold hasVectorialNonlinearityAtLeast EvenBalanced8Bound.hasVectorialNonlinearityAtLeast
  simp only [comp_eq, nl_iff, zero_eq]

/-! ## The challenge statements -/

/-- Main theorem. For `m ≥ 4`, every balanced function on `2m` variables has
    `nl(F) ≤ 2^(2m-1) - 2^(m-1) - 4`, i.e. it cannot reach `2^(2m-1) - 2^(m-1) - 3`. -/
theorem even_balanced_nl_le (m : Nat) (hm : 4 ≤ m)
    (F : Vec (2 * m) → Bool) (hbal : isBalanced (2 * m) F) :
    ¬ hasNonlinearityAtLeast (2 * m) F ((2 : Int) ^ (2 * m - 1) - (2 : Int) ^ (m - 1) - 3) := by
  intro h
  exact EvenBalanced8Bound.even_balanced_nl_le_from8 m hm (fun x => F x) (bal_iff.mp hbal) (nl_iff.mp h)

/-- `n = 8`: every balanced function has `nl(F) ≤ 116`. -/
theorem balanced_8_nl_le_116 (F : Vec 8 → Bool) (hbal : isBalanced 8 F) :
    ¬ hasNonlinearityAtLeast 8 F 117 := even_balanced_nl_le 4 (by decide) F hbal

/-- `n = 10`: every balanced function has `nl(F) ≤ 492`. -/
theorem balanced_10_nl_le_492 (F : Vec 10 → Bool) (hbal : isBalanced 10 F) :
    ¬ hasNonlinearityAtLeast 10 F 493 := even_balanced_nl_le 5 (by decide) F hbal

/-- `n = 12`: every balanced function has `nl(F) ≤ 2012`. -/
theorem balanced_12_nl_le_2012 (F : Vec 12 → Bool) (hbal : isBalanced 12 F) :
    ¬ hasNonlinearityAtLeast 12 F 2013 := even_balanced_nl_le 6 (by decide) F hbal

/-- `n = 14`: every balanced function has `nl(F) ≤ 8124`. -/
theorem balanced_14_nl_le_8124 (F : Vec 14 → Bool) (hbal : isBalanced 14 F) :
    ¬ hasNonlinearityAtLeast 14 F 8125 := even_balanced_nl_le 7 (by decide) F hbal

/-- `n = 16`: every balanced function has `nl(F) ≤ 32636`. -/
theorem balanced_16_nl_le_32636 (F : Vec 16 → Bool) (hbal : isBalanced 16 F) :
    ¬ hasNonlinearityAtLeast 16 F 32637 := even_balanced_nl_le 8 (by decide) F hbal

/-- Balanced `(2m, r)` S-boxes, `m ≥ 4`, `r ≥ 1`: some nonzero component has
    `nl ≤ 2^(2m-1) - 2^(m-1) - 4`. -/
theorem sbox_even_nl_le (m r : Nat) (hm : 4 ≤ m) (hr : 1 ≤ r)
    (F : Vec (2 * m) → Vec r) (hbal : isBalancedSBox (2 * m) r F) :
    ¬ hasVectorialNonlinearityAtLeast (2 * m) r F
        ((2 : Int) ^ (2 * m - 1) - (2 : Int) ^ (m - 1) - 3) := by
  intro h
  exact EvenBalanced8Bound.sbox_even_nl_le_from8 m r hm hr F (sbox_bal_iff.mp hbal) (vnl_iff.mp h)

/-- Permutations of `F_2^(2m)`, `m ≥ 4` (`G` is the inverse of `F`). -/
theorem permutation_even_nl_le (m : Nat) (hm : 4 ≤ m)
    (F G : Vec (2 * m) → Vec (2 * m))
    (hGF : ∀ x, G (F x) = x) (hFG : ∀ y, F (G y) = y) :
    ¬ hasVectorialNonlinearityAtLeast (2 * m) (2 * m) F
        ((2 : Int) ^ (2 * m - 1) - (2 : Int) ^ (m - 1) - 3) := by
  intro h
  exact EvenBalanced8Bound.permutation_even_nl_le_from8 m hm F G hGF hFG (vnl_iff.mp h)

end EvenBalancedChallenge
