/-
  Challenge.lean: the statements that `Solution.lean` proves, with `sorry` as placeholder.

  Imports only `ChallengeDefs`. The comparator check (`config.json`, `check_comparator.sh`)
  confirms that `Solution.lean` proves exactly these statements, over the same definitions,
  using only the axioms `propext`, `Classical.choice` and `Quot.sound`.
-/
import ChallengeDefs

namespace EvenBalancedChallenge

/-- Main theorem. For `m ≥ 4`, every balanced function on `2m` variables has
    `nl(F) ≤ 2^(2m-1) - 2^(m-1) - 4`, i.e. it cannot reach `2^(2m-1) - 2^(m-1) - 3`. -/
theorem even_balanced_nl_le (m : Nat) (hm : 4 ≤ m)
    (F : Vec (2 * m) → Bool) (hbal : isBalanced (2 * m) F) :
    ¬ hasNonlinearityAtLeast (2 * m) F ((2 : Int) ^ (2 * m - 1) - (2 : Int) ^ (m - 1) - 3) := sorry

/-- `n = 8`: every balanced function has `nl(F) ≤ 116`. -/
theorem balanced_8_nl_le_116 (F : Vec 8 → Bool) (hbal : isBalanced 8 F) :
    ¬ hasNonlinearityAtLeast 8 F 117 := sorry

/-- `n = 10`: every balanced function has `nl(F) ≤ 492`. -/
theorem balanced_10_nl_le_492 (F : Vec 10 → Bool) (hbal : isBalanced 10 F) :
    ¬ hasNonlinearityAtLeast 10 F 493 := sorry

/-- `n = 12`: every balanced function has `nl(F) ≤ 2012`. -/
theorem balanced_12_nl_le_2012 (F : Vec 12 → Bool) (hbal : isBalanced 12 F) :
    ¬ hasNonlinearityAtLeast 12 F 2013 := sorry

/-- `n = 14`: every balanced function has `nl(F) ≤ 8124`. -/
theorem balanced_14_nl_le_8124 (F : Vec 14 → Bool) (hbal : isBalanced 14 F) :
    ¬ hasNonlinearityAtLeast 14 F 8125 := sorry

/-- `n = 16`: every balanced function has `nl(F) ≤ 32636`. -/
theorem balanced_16_nl_le_32636 (F : Vec 16 → Bool) (hbal : isBalanced 16 F) :
    ¬ hasNonlinearityAtLeast 16 F 32637 := sorry

/-- Balanced `(2m, r)` S-boxes, `m ≥ 4`, `r ≥ 1`: some nonzero component has
    `nl ≤ 2^(2m-1) - 2^(m-1) - 4`. -/
theorem sbox_even_nl_le (m r : Nat) (hm : 4 ≤ m) (hr : 1 ≤ r)
    (F : Vec (2 * m) → Vec r) (hbal : isBalancedSBox (2 * m) r F) :
    ¬ hasVectorialNonlinearityAtLeast (2 * m) r F
        ((2 : Int) ^ (2 * m - 1) - (2 : Int) ^ (m - 1) - 3) := sorry

/-- Permutations of `F_2^(2m)`, `m ≥ 4` (`G` is the inverse of `F`). -/
theorem permutation_even_nl_le (m : Nat) (hm : 4 ≤ m)
    (F G : Vec (2 * m) → Vec (2 * m))
    (hGF : ∀ x, G (F x) = x) (hFG : ∀ y, F (G y) = y) :
    ¬ hasVectorialNonlinearityAtLeast (2 * m) (2 * m) F
        ((2 : Int) ^ (2 * m - 1) - (2 : Int) ^ (m - 1) - 3) := sorry

end EvenBalancedChallenge
