/-
  EvenBalanced8Bound.lean
  =======================
  A standalone Lean 4.15.0 formalization (no imports, no Mathlib) of:
    1. For every m ≥ 4 and every balanced Boolean function F on 2m variables,
         `nl(F) ≤ 2^(2m - 1) - 2^(m - 1) - 4`.
       This answers Open Problem 4 of Lou–Xu–Wang (arXiv:2610.17897).
    2. The cases n = 8 and n = 10: no balanced function has nonlinearity ≥ 118
       (resp. ≥ 494). With Dobbertin's construction these give `nl_bal(8) = 116`
       and `nl_bal(10) = 492`. These values were first established by
       Yuan et al. (IACR ePrint 2026/1687) and Lou–Xu–Wang for n = 8, and by
       Xu–Wang (IACR ePrint 2026/2797) for n = 10; the proof here is independent
       and does not use a computer search.
    3. The same bounds for every component of a balanced (2m, r)-S-box and for
       2m-bit permutations, m ≥ 4 (`sbox_8bit_nl_le_116`, `permutation_8bit_nl_le_116`,
       `sbox_10bit_nl_le_492`, `permutation_10bit_nl_le_492`).
    4. A proof of the known Sarkar–Maitra (2000) divisibility theorem
       (`2^(t + 2) ∣ W_F(a)` for every t-resilient function on n ≥ t + 2 variables)
       and the resulting known nonlinearity bounds for t-resilient functions
       (`t + 2 ≤ m` in even dimension, and `t + 2 ≤ n` in general).

  No imports, no `sorry`, no added axioms. The main theorems depend only on
  `[propext, Classical.choice, Quot.sound]`.
-/

namespace EvenBalanced8Bound

/-! ## Section 0: Pure-`Init` Arithmetic Helpers -/

private theorem int_pow_add (a : Int) (m : Nat) : ∀ k : Nat, a ^ (m + k) = a ^ m * a ^ k
  | 0 => by change a ^ m = a ^ m * 1; rw [Int.mul_one]
  | k + 1 => by
    have : m + (k + 1) = (m + k) + 1 := by omega
    rw [this, Int.pow_succ, int_pow_add a m k, Int.pow_succ, Int.mul_assoc]

private theorem two_pow_pos (k : Nat) : (0 : Int) < (2 : Int) ^ k := by
  induction k with
  | zero => decide
  | succ k ih => rw [Int.pow_succ]; omega

private theorem two_pow_le_of_le {a b : Nat} (h : a ≤ b) : (2 : Int) ^ a ≤ (2 : Int) ^ b := by
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0
    exact Int.le_refl _
  | succ b ih =>
    by_cases heq : a = b + 1
    · subst heq; exact Int.le_refl _
    · have h1 := ih (by omega)
      have h2 := two_pow_pos b
      rw [Int.pow_succ]; omega

private theorem two_pow_dvd_of_le {a b : Nat} (h : a ≤ b) : (2 : Int) ^ a ∣ (2 : Int) ^ b := by
  have : b = a + (b - a) := by omega
  conv => rhs; rw [this, int_pow_add]
  exact ⟨(2 : Int) ^ (b - a), rfl⟩

private theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  cases Int.le_total 0 x with
  | inl h => exact Int.mul_nonneg h h
  | inr h =>
    have h1 := Int.mul_nonneg (show 0 ≤ -x by omega) (show 0 ≤ -x by omega)
    rw [Int.neg_mul, Int.mul_neg, Int.neg_neg] at h1
    exact h1

private theorem sq_le_of_abs_le {z B : Int} (hlo : -B ≤ z) (hhi : z ≤ B) : z * z ≤ B * B := by
  have h := Int.mul_nonneg (show 0 ≤ B - z by omega) (show 0 ≤ B + z by omega)
  simp only [Int.sub_mul, Int.mul_add, Int.mul_comm z B] at h
  omega

private theorem int_sq_eq_iff {x y : Int} (h : x * x = y * y) : x = y ∨ x = -y := by
  have h1 : (x - y) * (x + y) = 0 := by
    simp only [Int.sub_mul, Int.mul_add, Int.mul_comm y x]
    omega
  cases Int.mul_eq_zero.mp h1 with
  | inl hl => left; omega
  | inr hr => right; omega

private theorem sq_ne_two_mul_sq : ∀ (a b : Nat), 0 < b → a * a ≠ 2 * (b * b) := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro b hb heq
    have ha_even : a % 2 = 0 := by
      by_cases h : a % 2 = 0
      · exact h
      · have hmod : a = 2 * (a / 2) + 1 := by omega
        let k := a / 2
        have hsq : a * a = 2 * (2 * (k * k) + 2 * k) + 1 := by
          have ha' : a = 2 * k + 1 := hmod
          rw [ha', Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.one_mul, Nat.mul_one]
          have h4 : 2 * k * (2 * k) = 4 * (k * k) := by
            rw [Nat.mul_assoc, Nat.mul_left_comm k 2 k, ← Nat.mul_assoc]
          omega
        omega
    let a' := a / 2
    have ha : a = 2 * a' := by omega
    have hb_eq : b * b = 2 * (a' * a') := by
      rw [ha] at heq
      have : 2 * a' * (2 * a') = 4 * (a' * a') := by
        rw [Nat.mul_assoc, Nat.mul_left_comm a' 2 a', ← Nat.mul_assoc]
      omega
    have ha'_pos : 0 < a' := by
      by_cases h0 : a' = 0
      · rw [h0] at hb_eq; simp at hb_eq
        have : 0 < b * b := Nat.mul_pos hb hb
        omega
      · omega
    have hb_lt : b < a := by
      by_cases hle : a ≤ b
      · have h1 : a * a ≤ b * b := Nat.mul_le_mul hle hle
        have h2 : 0 < b * b := Nat.mul_pos hb hb
        omega
      · omega
    exact ih b hb_lt a' ha'_pos hb_eq

private theorem int_sq_ne_odd_two_pow (x : Int) (s : Nat) :
    x * x ≠ (2 : Int) ^ (2 * s + 1) := by
  intro h
  have ha : (x.natAbs : Int) * (x.natAbs : Int) = x * x := by
    have := Int.natAbs_mul_self (a := x)
    exact this
  have h2 : (2 : Int) ^ (2 * s + 1) = 2 * ((2 : Int) ^ s * (2 : Int) ^ s) := by
    have he : 2 * s + 1 = (s + s) + 1 := by omega
    rw [he, Int.pow_succ, int_pow_add, Int.mul_comm _ 2]
  have hnat : x.natAbs * x.natAbs = 2 * (2 ^ s * 2 ^ s) := by
    have hc : ((x.natAbs * x.natAbs : Nat) : Int) = ((2 * (2 ^ s * 2 ^ s) : Nat) : Int) := by
      push_cast
      rw [ha, h, h2]
    exact Int.ofNat.inj hc
  have hpos : 0 < 2 ^ s := Nat.pow_pos (by decide : 0 < 2)
  exact sq_ne_two_mul_sq x.natAbs (2 ^ s) hpos hnat

/-! ## Section 1: Textbook Definitions & Walsh-Hadamard Algebra -/

/-- Boolean vectors `F_2^n`. -/
abbrev Vec (n : Nat) := Fin n → Bool

/-- Sign encoding: `false ↦ +1`, `true ↦ -1`. -/
def sign (b : Bool) : Int := if b then -1 else 1

/-- Zero vector in `F_2^n`. -/
def zeroVec {n : Nat} : Vec n := fun _ => false

/-- Bitwise XOR on `F_2^n`. -/
def xorVec {n : Nat} (a b : Vec n) : Vec n := fun i => xor (a i) (b i)

/-- Standard basis vector `e_p` in `F_2^n`. -/
def basisVec {n : Nat} (p : Fin n) : Vec n := fun i => decide (i = p)

/-- Prepend a Boolean coordinate to a vector in `F_2^n`. -/
def consVec {n : Nat} (b : Bool) (v : Vec n) : Vec (n + 1) :=
  fun i => match i with
    | ⟨0, _⟩ => b
    | ⟨k + 1, h⟩ => v ⟨k, Nat.lt_of_succ_lt_succ h⟩

/-- Drop the first coordinate of a vector in `F_2^(n+1)`. -/
def tailVec {n : Nat} (v : Vec (n + 1)) : Vec n :=
  fun i => v ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

/-- Computable zero-vector test. -/
def isZeroVec : {n : Nat} → Vec n → Bool
  | 0, _ => true
  | _ + 1, v => !(v ⟨0, Nat.zero_lt_succ _⟩) && isZeroVec (tailVec v)

/-- Computable universal quantifier over `F_2^n`. -/
def allVecs : {n : Nat} → (Vec n → Bool) → Bool
  | 0, P => P (fun i => Fin.elim0 i)
  | _ + 1, P => allVecs (fun v => P (consVec false v)) && allVecs (fun v => P (consVec true v))

/-- Sum of an integer-valued function over all `2^n` vectors of `F_2^n`. -/
def sumVecs : {n : Nat} → (Vec n → Int) → Int
  | 0, g => g (fun i => Fin.elim0 i)
  | _ + 1, g =>
    sumVecs (fun v => g (consVec false v)) +
    sumVecs (fun v => g (consVec true v))

/-- Inner product modulo 2 on `F_2^n`. -/
def dot : {n : Nat} → Vec n → Vec n → Bool
  | 0, _, _ => false
  | _ + 1, a, x =>
    xor (a ⟨0, Nat.zero_lt_succ _⟩ && x ⟨0, Nat.zero_lt_succ _⟩)
        (dot (tailVec a) (tailVec x))

/-- Hamming weight `|{x ∈ F_2^n : F(x) = true}|`. -/
def hammingWeight {n : Nat} (F : Vec n → Bool) : Int :=
  sumVecs (fun x => if F x then 1 else 0)

/-- Hamming distance `|{x ∈ F_2^n : F(x) ≠ G(x)}|`. -/
def hammingDist {n : Nat} (F G : Vec n → Bool) : Int :=
  sumVecs (fun x => if F x != G x then 1 else 0)

/-- Affine Boolean function `x ↦ (a · x) ⊕ c`. -/
def affine {n : Nat} (a : Vec n) (c : Bool) (x : Vec n) : Bool :=
  xor (dot a x) c

/-- Balancedness: `2 * hammingWeight F = 2^n`. -/
def isBalanced (n : Nat) (F : Vec n → Bool) : Prop :=
  2 * hammingWeight F = (2 : Int) ^ n

/-- Nonlinearity at least `d`: distance to every affine function is `≥ d`. -/
def hasNonlinearityAtLeast (n : Nat) (F : Vec n → Bool) (d : Int) : Prop :=
  ∀ (a : Vec n) (c : Bool), d ≤ hammingDist F (affine a c)

/-- Walsh–Hadamard transform `W_g(a) = ∑_{x ∈ F_2^n} g(x) (-1)^{a · x}`. -/
def walsh {n : Nat} (g : Vec n → Int) (a : Vec n) : Int :=
  sumVecs (fun x => g x * sign (dot a x))

/-- Walsh–Hadamard transform of a Boolean function `F`. -/
def walshBool {n : Nat} (F : Vec n → Bool) (a : Vec n) : Int :=
  walsh (fun x => sign (F x)) a

/-! ### Elementary `Vec`, `allVecs`, `dot`, and `sumVecs` Lemmas -/

private theorem consVec_head {n : Nat} (b : Bool) (v : Vec n) :
    consVec b v ⟨0, Nat.zero_lt_succ n⟩ = b := rfl

private theorem tailVec_cons {n : Nat} (b : Bool) (v : Vec n) :
    tailVec (consVec b v) = v := by
  funext ⟨k, hk⟩; rfl

private theorem tailVec_zeroVec {n : Nat} :
    tailVec (zeroVec : Vec (n + 1)) = (zeroVec : Vec n) := rfl

private theorem consVec_eta {n : Nat} (v : Vec (n + 1)) :
    consVec (v ⟨0, Nat.zero_lt_succ n⟩) (tailVec v) = v := by
  funext ⟨k, hk⟩; cases k <;> rfl

private theorem zeroVec_cons {n : Nat} :
    (zeroVec : Vec (n + 1)) = consVec false zeroVec := by
  funext ⟨k, hk⟩; cases k <;> rfl

private theorem isZeroVec_true_iff : {n : Nat} → (a : Vec n) →
    (isZeroVec a = true ↔ a = zeroVec)
  | 0, a => by
    constructor
    · intro _; funext i; exact Fin.elim0 i
    · intro _; rfl
  | n + 1, a => by
    constructor
    · intro h
      simp only [isZeroVec, Bool.and_eq_true, Bool.not_eq_true'] at h
      have ht := (isZeroVec_true_iff (tailVec a)).mp h.2
      funext ⟨k, hk⟩
      cases k with
      | zero => exact h.1
      | succ k' => exact congrFun ht ⟨k', Nat.lt_of_succ_lt_succ hk⟩
    · intro h; subst h
      simp only [isZeroVec, zeroVec, tailVec_zeroVec, Bool.not_false, Bool.true_and]
      exact (isZeroVec_true_iff (zeroVec : Vec n)).mpr rfl

private theorem allVecs_true_iff : {n : Nat} → (P : Vec n → Bool) →
    (allVecs P = true ↔ ∀ x : Vec n, P x = true)
  | 0, P => by
    constructor
    · intro h x
      have hx : x = fun i => Fin.elim0 i := by funext i; exact Fin.elim0 i
      rw [hx]; exact h
    · intro h; exact h _
  | n + 1, P => by
    simp only [allVecs, Bool.and_eq_true, allVecs_true_iff]
    constructor
    · rintro ⟨h0, h1⟩ x
      rw [← consVec_eta x]
      cases x ⟨0, Nat.zero_lt_succ n⟩
      · exact h0 (tailVec x)
      · exact h1 (tailVec x)
    · intro h
      exact ⟨fun v => h (consVec false v), fun v => h (consVec true v)⟩

private theorem xorVec_cons {n : Nat} (b1 b2 : Bool) (v1 v2 : Vec n) :
    xorVec (consVec b1 v1) (consVec b2 v2) = consVec (xor b1 b2) (xorVec v1 v2) := by
  funext ⟨k, hk⟩; cases k <;> rfl

private theorem xorVec_comm {n : Nat} (a b : Vec n) : xorVec a b = xorVec b a := by
  funext i; exact Bool.xor_comm (a i) (b i)

private theorem xorVec_assoc {n : Nat} (a b c : Vec n) :
    xorVec (xorVec a b) c = xorVec a (xorVec b c) := by
  funext i; exact Bool.xor_assoc (a i) (b i) (c i)

private theorem xorVec_self {n : Nat} (a : Vec n) : xorVec a a = zeroVec := by
  funext i; simp [xorVec, zeroVec]

private theorem xorVec_zero_right {n : Nat} (a : Vec n) : xorVec a zeroVec = a := by
  funext i; simp [xorVec, zeroVec]

private theorem xorVec_zero_left {n : Nat} (a : Vec n) : xorVec zeroVec a = a := by
  funext i; simp [xorVec, zeroVec]

private theorem tailVec_xorVec {n : Nat} (a b : Vec (n + 1)) :
    tailVec (xorVec a b) = xorVec (tailVec a) (tailVec b) := rfl

private theorem dot_cons {n : Nat} (b1 b2 : Bool) (v1 v2 : Vec n) :
    dot (consVec b1 v1) (consVec b2 v2) = xor (b1 && b2) (dot v1 v2) := rfl

private theorem dot_zero_left : {n : Nat} → (x : Vec n) → dot zeroVec x = false
  | 0, _ => rfl
  | _ + 1, x => by
    unfold dot
    rw [tailVec_zeroVec, dot_zero_left (tailVec x)]
    rfl

private theorem dot_zero_right : {n : Nat} → (a : Vec n) → dot a zeroVec = false
  | 0, _ => rfl
  | _ + 1, a => by
    unfold dot
    rw [tailVec_zeroVec, dot_zero_right (tailVec a)]
    simp [zeroVec]

private theorem dot_comm : {n : Nat} → (a b : Vec n) → dot a b = dot b a
  | 0, _, _ => rfl
  | _ + 1, a, b => by
    unfold dot
    rw [Bool.and_comm, dot_comm (tailVec a) (tailVec b)]

private theorem dot_xor_left : {n : Nat} → (a b x : Vec n) →
    dot (xorVec a b) x = xor (dot a x) (dot b x)
  | 0, _, _, _ => rfl
  | _ + 1, a, b, x => by
    have ih := dot_xor_left (tailVec a) (tailVec b) (tailVec x)
    unfold dot
    rw [tailVec_xorVec, ih]
    change xor (xor (a ⟨0, Nat.zero_lt_succ _⟩) (b ⟨0, Nat.zero_lt_succ _⟩) && x ⟨0, Nat.zero_lt_succ _⟩)
               (xor (dot (tailVec a) (tailVec x)) (dot (tailVec b) (tailVec x))) =
           xor (xor (a ⟨0, Nat.zero_lt_succ _⟩ && x ⟨0, Nat.zero_lt_succ _⟩) (dot (tailVec a) (tailVec x)))
               (xor (b ⟨0, Nat.zero_lt_succ _⟩ && x ⟨0, Nat.zero_lt_succ _⟩) (dot (tailVec b) (tailVec x)))
    cases a ⟨0, Nat.zero_lt_succ _⟩ <;> cases b ⟨0, Nat.zero_lt_succ _⟩ <;>
      cases x ⟨0, Nat.zero_lt_succ _⟩ <;> cases dot (tailVec a) (tailVec x) <;>
      cases dot (tailVec b) (tailVec x) <;> rfl

private theorem dot_xor_right {n : Nat} (a x y : Vec n) :
    dot a (xorVec x y) = xor (dot a x) (dot a y) := by
  rw [dot_comm, dot_xor_left, dot_comm x a, dot_comm y a]

private theorem dot_basisVec : {n : Nat} → (a : Vec n) → (p : Fin n) →
    dot a (basisVec p) = a p
  | 0, _, p => Fin.elim0 p
  | m + 1, a, ⟨0, hk⟩ => by
    have h0 : basisVec ⟨0, hk⟩ ⟨0, Nat.zero_lt_succ m⟩ = true := by simp [basisVec]
    have ht : tailVec (basisVec ⟨0, hk⟩) = (zeroVec : Vec m) := by
      funext ⟨j, hj⟩
      have hne : (⟨j + 1, Nat.succ_lt_succ hj⟩ : Fin (m + 1)) ≠ ⟨0, hk⟩ := by
        intro h; have := congrArg Fin.val h; simp at this
      simp only [tailVec, basisVec, zeroVec, hne, decide_false]
    unfold dot
    rw [h0, ht, dot_zero_right, Bool.and_true, Bool.xor_false]
  | m + 1, a, ⟨k + 1, hk⟩ => by
    have h0 : basisVec ⟨k + 1, hk⟩ ⟨0, Nat.zero_lt_succ m⟩ = false := by
      have hne : (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) ≠ ⟨k + 1, hk⟩ := by
        intro h; have := congrArg Fin.val h; simp at this
      simp only [basisVec, hne, decide_false]
    have ht : tailVec (basisVec ⟨k + 1, hk⟩) = basisVec ⟨k, Nat.lt_of_succ_lt_succ hk⟩ := by
      funext ⟨j, hj⟩; simp [tailVec, basisVec, Fin.ext_iff]
    unfold dot
    rw [h0, ht, Bool.and_false, Bool.false_xor]
    exact dot_basisVec (tailVec a) ⟨k, Nat.lt_of_succ_lt_succ hk⟩

private theorem sign_xor (b c : Bool) : sign (xor b c) = sign b * sign c := by
  cases b <;> cases c <;> rfl

private theorem sign_sq (b : Bool) : sign b * sign b = 1 := by
  cases b <;> rfl

private theorem sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> rfl

private theorem sumVecs_congr : {n : Nat} → {f g : Vec n → Int} →
    (∀ x, f x = g x) → sumVecs f = sumVecs g
  | 0, _, _, h => h _
  | _ + 1, _, _, h => by
    simp only [sumVecs]
    rw [sumVecs_congr (fun v => h (consVec false v)),
        sumVecs_congr (fun v => h (consVec true v))]

private theorem sumVecs_add : {n : Nat} → (f g : Vec n → Int) →
    sumVecs (fun x => f x + g x) = sumVecs f + sumVecs g
  | 0, _, _ => rfl
  | _ + 1, f, g => by simp only [sumVecs, sumVecs_add]; omega

private theorem sumVecs_sub : {n : Nat} → (f g : Vec n → Int) →
    sumVecs (fun x => f x - g x) = sumVecs f - sumVecs g
  | 0, _, _ => rfl
  | _ + 1, f, g => by simp only [sumVecs, sumVecs_sub]; omega

private theorem sumVecs_mul_left : {n : Nat} → (c : Int) → (f : Vec n → Int) →
    sumVecs (fun x => c * f x) = c * sumVecs f
  | 0, _, _ => rfl
  | _ + 1, c, f => by simp only [sumVecs, sumVecs_mul_left, Int.mul_add]

private theorem sumVecs_mul_right {n : Nat} (f : Vec n → Int) (c : Int) :
    sumVecs (fun x => f x * c) = sumVecs f * c := by
  rw [sumVecs_congr (fun x => Int.mul_comm (f x) c), sumVecs_mul_left, Int.mul_comm]

private theorem sumVecs_const : {n : Nat} → (c : Int) →
    sumVecs (n := n) (fun _ => c) = (2 : Int) ^ n * c
  | 0, c => by simp [sumVecs]
  | n + 1, c => by
    simp only [sumVecs, sumVecs_const, Int.pow_succ]
    rw [Int.mul_comm ((2 : Int) ^ n) 2, Int.mul_assoc]
    omega

private theorem sumVecs_mono : {n : Nat} → {f g : Vec n → Int} →
    (∀ x, f x ≤ g x) → sumVecs f ≤ sumVecs g
  | 0, _, _, h => h _
  | _ + 1, _, _, h =>
    Int.add_le_add (sumVecs_mono (fun v => h (consVec false v)))
                   (sumVecs_mono (fun v => h (consVec true v)))

private theorem sumVecs_nonneg {n : Nat} {f : Vec n → Int} (h : ∀ x, 0 ≤ f x) :
    0 ≤ sumVecs f := by
  have h0 : sumVecs (n := n) (fun _ => (0 : Int)) = 0 := by rw [sumVecs_const, Int.mul_zero]
  rw [← h0]; exact sumVecs_mono h

private theorem sumVecs_eq_zero_of_nonneg : {n : Nat} → {f : Vec n → Int} →
    (∀ x, 0 ≤ f x) → sumVecs f = 0 → ∀ x, f x = 0
  | 0, f, _, hsum, x => by
    have hx : x = fun i => Fin.elim0 i := by funext i; exact Fin.elim0 i
    rw [hx]; exact hsum
  | n + 1, f, hnn, hsum, x => by
    simp only [sumVecs] at hsum
    have h0nn : 0 ≤ sumVecs (fun v => f (consVec false v)) :=
      sumVecs_nonneg (fun v => hnn (consVec false v))
    have h1nn : 0 ≤ sumVecs (fun v => f (consVec true v)) :=
      sumVecs_nonneg (fun v => hnn (consVec true v))
    have h0z : sumVecs (fun v => f (consVec false v)) = 0 := by omega
    have h1z : sumVecs (fun v => f (consVec true v)) = 0 := by omega
    rw [← consVec_eta x]
    cases x ⟨0, Nat.zero_lt_succ n⟩
    · exact sumVecs_eq_zero_of_nonneg (fun v => hnn (consVec false v)) h0z (tailVec x)
    · exact sumVecs_eq_zero_of_nonneg (fun v => hnn (consVec true v)) h1z (tailVec x)

private theorem sumVecs_swap : {n m : Nat} → (f : Vec n → Vec m → Int) →
    sumVecs (fun x => sumVecs (fun y => f x y)) =
    sumVecs (fun y => sumVecs (fun x => f x y))
  | 0, _, f => by simp [sumVecs]
  | _ + 1, _, f => by
    simp only [sumVecs]
    rw [sumVecs_swap (fun v y => f (consVec false v) y),
        sumVecs_swap (fun v y => f (consVec true v) y),
        ← sumVecs_add]

private theorem sumVecs_delta_zero : {n : Nat} → (c : Int) →
    sumVecs (n := n) (fun a => if isZeroVec a then c else 0) = c
  | 0, c => by simp [sumVecs, isZeroVec]
  | n + 1, c => by
    simp only [sumVecs]
    have s1 : sumVecs (fun v : Vec n => if isZeroVec (consVec false v) then c else 0) =
        sumVecs (fun v : Vec n => if isZeroVec v then c else 0) :=
      sumVecs_congr (fun _ => rfl)
    have s2 : sumVecs (fun v : Vec n => if isZeroVec (consVec true v) then c else 0) =
        sumVecs (n := n) (fun _ => (0 : Int)) :=
      sumVecs_congr (fun _ => rfl)
    rw [s1, s2, sumVecs_delta_zero c, sumVecs_const]; simp

private theorem sumVecs_xor_shift : {n : Nat} → (d : Vec n) → (f : Vec n → Int) →
    sumVecs (fun x => f (xorVec x d)) = sumVecs f
  | 0, _, f => by
    simp only [sumVecs]; congr 1; funext i; exact Fin.elim0 i
  | _ + 1, d, f => by
    simp only [sumVecs]
    have hcons : ∀ b (v : Vec _),
        xorVec (consVec b v) d =
          consVec (xor b (d ⟨0, Nat.zero_lt_succ _⟩)) (xorVec v (tailVec d)) := by
      intro b v
      conv => lhs; rw [← consVec_eta d, xorVec_cons]
    cases hd : d ⟨0, Nat.zero_lt_succ _⟩
    · simp only [hcons, hd, Bool.xor_false]
      rw [sumVecs_xor_shift (tailVec d) (fun v => f (consVec false v)),
          sumVecs_xor_shift (tailVec d) (fun v => f (consVec true v))]
    · have hf : ∀ v, f (xorVec (consVec false v) d) = f (consVec true (xorVec v (tailVec d))) := by
        intro v; rw [hcons, hd]; rfl
      have ht : ∀ v, f (xorVec (consVec true v) d) = f (consVec false (xorVec v (tailVec d))) := by
        intro v; rw [hcons, hd]; rfl
      rw [sumVecs_congr hf, sumVecs_congr ht,
          sumVecs_xor_shift (tailVec d) (fun v => f (consVec true v)),
          sumVecs_xor_shift (tailVec d) (fun v => f (consVec false v)),
          Int.add_comm]

/-! ### Walsh Transform: Plancherel, Parseval, Inversion, Balance, Nonlinearity -/

private theorem walsh_cons {n : Nat} (g : Vec (n + 1) → Int) (b : Bool) (a : Vec n) :
    walsh g (consVec b a) =
      walsh (fun v => g (consVec false v)) a +
      sign b * walsh (fun v => g (consVec true v)) a := by
  simp only [walsh, sumVecs]
  congr 1
  · apply sumVecs_congr; intro v
    rw [dot_cons]; simp [Bool.and_false, Bool.false_xor]
  · rw [← sumVecs_mul_left]
    apply sumVecs_congr; intro v
    rw [dot_cons, Bool.and_true, sign_xor]
    simp only [Int.mul_assoc, Int.mul_left_comm]

private theorem walsh_adjoint {n : Nat} (f g : Vec n → Int) :
    sumVecs (fun a => walsh f a * g a) = sumVecs (fun x => f x * walsh g x) := by
  calc
    sumVecs (fun a => walsh f a * g a)
        = sumVecs (fun a => sumVecs (fun x => f x * sign (dot a x) * g a)) := by
          apply sumVecs_congr; intro a
          exact (sumVecs_mul_right (fun x => f x * sign (dot a x)) (g a)).symm
    _ = sumVecs (fun x => sumVecs (fun a => f x * sign (dot a x) * g a)) :=
          sumVecs_swap (fun a x => f x * sign (dot a x) * g a)
    _ = sumVecs (fun x => f x * walsh g x) := by
          apply sumVecs_congr; intro x
          unfold walsh
          rw [← sumVecs_mul_left]
          apply sumVecs_congr; intro a
          rw [dot_comm a x, Int.mul_assoc, Int.mul_comm (sign (dot x a)) (g a)]

/-- Plancherel's identity: `∑_a W_f(a) W_g(a) = 2^n ∑_x f(x) g(x)`. -/
theorem walsh_plancherel : {n : Nat} → (f g : Vec n → Int) →
    sumVecs (fun a => walsh f a * walsh g a) = (2 : Int) ^ n * sumVecs (fun x => f x * g x)
  | 0, f, g => by simp [sumVecs, walsh, dot, sign]
  | n + 1, f, g => by
    let f0 : Vec n → Int := fun v => f (consVec false v)
    let f1 : Vec n → Int := fun v => f (consVec true v)
    let g0 : Vec n → Int := fun v => g (consVec false v)
    let g1 : Vec n → Int := fun v => g (consVec true v)
    have hstep : ∀ a : Vec n,
        walsh f (consVec false a) * walsh g (consVec false a) +
        walsh f (consVec true a) * walsh g (consVec true a) =
        2 * (walsh f0 a * walsh g0 a + walsh f1 a * walsh g1 a) := by
      intro a
      rw [walsh_cons f false a, walsh_cons g false a, walsh_cons f true a, walsh_cons g true a]
      simp only [sign, Bool.false_eq_true, ↓reduceIte, Int.one_mul, Int.neg_mul]
      let u0 := walsh f0 a; let u1 := walsh f1 a
      let v0 := walsh g0 a; let v1 := walsh g1 a
      change (u0 + u1) * (v0 + v1) + (u0 + -u1) * (v0 + -v1) = 2 * (u0 * v0 + u1 * v1)
      simp only [Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg, Int.neg_neg]
      omega
    calc
      sumVecs (fun a => walsh f a * walsh g a)
          = sumVecs (fun a => walsh f (consVec false a) * walsh g (consVec false a) +
                              walsh f (consVec true a) * walsh g (consVec true a)) := by
            simp only [sumVecs, sumVecs_add]
      _ = sumVecs (fun a => 2 * (walsh f0 a * walsh g0 a + walsh f1 a * walsh g1 a)) :=
            sumVecs_congr hstep
      _ = 2 * (sumVecs (fun a => walsh f0 a * walsh g0 a) +
               sumVecs (fun a => walsh f1 a * walsh g1 a)) := by
            rw [sumVecs_mul_left, sumVecs_add]
      _ = 2 * ((2 : Int) ^ n * sumVecs (fun x => f0 x * g0 x) +
               (2 : Int) ^ n * sumVecs (fun x => f1 x * g1 x)) := by
            rw [walsh_plancherel f0 g0, walsh_plancherel f1 g1]
      _ = (2 : Int) ^ (n + 1) * sumVecs (fun x => f x * g x) := by
            rw [Int.pow_succ, Int.mul_comm ((2 : Int) ^ n) 2, Int.mul_assoc, ← Int.mul_add]
            rfl

/-- Parseval's identity for arbitrary integer tables on `F_2^n`. -/
theorem walsh_parseval {n : Nat} (g : Vec n → Int) :
    sumVecs (fun a => walsh g a * walsh g a) = (2 : Int) ^ n * sumVecs (fun x => g x * g x) :=
  walsh_plancherel g g

/-- Walsh inversion: `W_{W_g}(x) = 2^n g(x)`. -/
theorem walsh_inversion : {n : Nat} → (g : Vec n → Int) → (x : Vec n) →
    walsh (walsh g) x = (2 : Int) ^ n * g x
  | 0, g, x => by
    have hx : x = fun i => Fin.elim0 i := by funext i; exact Fin.elim0 i
    rw [hx]; simp [walsh, sumVecs, dot, sign]
  | n + 1, g, x => by
    let g0 : Vec n → Int := fun v => g (consVec false v)
    let g1 : Vec n → Int := fun v => g (consVec true v)
    let b := x ⟨0, Nat.zero_lt_succ n⟩
    let x' := tailVec x
    have hx : x = consVec b x' := (consVec_eta x).symm
    rw [hx, walsh_cons (walsh g) b x']
    have h0 : walsh (fun v => walsh g (consVec false v)) x' =
        walsh (walsh g0) x' + walsh (walsh g1) x' := by
      change sumVecs (fun a' => walsh g (consVec false a') * sign (dot x' a')) =
             sumVecs (fun a' => walsh g0 a' * sign (dot x' a')) +
             sumVecs (fun a' => walsh g1 a' * sign (dot x' a'))
      rw [← sumVecs_add]
      apply sumVecs_congr; intro a'
      rw [walsh_cons g false a']
      simp only [sign, Bool.false_eq_true, ↓reduceIte, Int.one_mul, Int.add_mul]
    have h1 : walsh (fun v => walsh g (consVec true v)) x' =
        walsh (walsh g0) x' - walsh (walsh g1) x' := by
      change sumVecs (fun a' => walsh g (consVec true a') * sign (dot x' a')) =
             sumVecs (fun a' => walsh g0 a' * sign (dot x' a')) -
             sumVecs (fun a' => walsh g1 a' * sign (dot x' a'))
      rw [← sumVecs_sub]
      apply sumVecs_congr; intro a'
      rw [walsh_cons g true a']
      dsimp only [g0, g1]
      simp only [sign, ↓reduceIte, Int.neg_mul, Int.one_mul, Int.add_mul]
      omega
    rw [h0, h1, walsh_inversion g0 x', walsh_inversion g1 x', Int.pow_succ]
    cases b
    · simp only [sign, Bool.false_eq_true, ↓reduceIte, Int.one_mul]
      dsimp only [g0]; rw [Int.mul_comm ((2 : Int) ^ n) 2, Int.mul_assoc]; omega
    · simp only [sign, ↓reduceIte, Int.neg_mul, Int.one_mul]
      dsimp only [g1]; rw [Int.mul_comm ((2 : Int) ^ n) 2, Int.mul_assoc]; omega

/-- Parseval's identity for Boolean functions: `∑_a W_F(a)^2 = 2^(2n)`. -/
theorem walshBool_parseval {n : Nat} (F : Vec n → Bool) :
    sumVecs (fun a => walshBool F a * walshBool F a) = (2 : Int) ^ (2 * n) := by
  unfold walshBool
  rw [walsh_parseval]
  have h1 : ∀ x : Vec n, sign (F x) * sign (F x) = 1 := fun x => sign_sq (F x)
  rw [sumVecs_congr h1, sumVecs_const, Int.mul_one, ← int_pow_add]
  have : n + n = 2 * n := by omega
  rw [this]

/-- `W_F(0) = 0` when `F` is balanced. -/
theorem walshBool_zero_of_balanced {n : Nat} (F : Vec n → Bool) (hbal : isBalanced n F) :
    walshBool F zeroVec = 0 := by
  unfold walshBool walsh
  have h1 : ∀ x : Vec n, sign (F x) * sign (dot zeroVec x) =
      1 - 2 * (if F x then 1 else 0) := by
    intro x; rw [dot_zero_left]; cases F x <;> rfl
  rw [sumVecs_congr h1, sumVecs_sub, sumVecs_const, sumVecs_mul_left, Int.mul_one]
  unfold isBalanced hammingWeight at hbal
  omega

private theorem walshBool_zero_eq_wt {n : Nat} (F : Vec n → Bool) :
    walshBool F zeroVec = (2 : Int) ^ n - 2 * hammingWeight F := by
  unfold walshBool walsh hammingWeight
  have h1 : ∀ x : Vec n, sign (F x) * sign (dot zeroVec x) =
      1 - 2 * (if F x then 1 else 0) := by
    intro x; rw [dot_zero_left]; cases F x <;> rfl
  rw [sumVecs_congr h1, sumVecs_sub, sumVecs_const, sumVecs_mul_left, Int.mul_one]

private theorem walshBool_eq_dist_false {n : Nat} (F : Vec n → Bool) (a : Vec n) :
    walshBool F a = (2 : Int) ^ n - 2 * hammingDist F (affine a false) := by
  unfold walshBool walsh hammingDist affine
  have h1 : ∀ x : Vec n, sign (F x) * sign (dot a x) =
      1 - 2 * (if F x != xor (dot a x) false then 1 else 0) := by
    intro x; cases F x <;> cases dot a x <;> rfl
  rw [sumVecs_congr h1, sumVecs_sub, sumVecs_const, sumVecs_mul_left, Int.mul_one]

private theorem walshBool_eq_dist_true {n : Nat} (F : Vec n → Bool) (a : Vec n) :
    -walshBool F a = (2 : Int) ^ n - 2 * hammingDist F (affine a true) := by
  unfold walshBool walsh hammingDist affine
  have h1 : ∀ x : Vec n, -(sign (F x) * sign (dot a x)) =
      1 - 2 * (if F x != xor (dot a x) true then 1 else 0) := by
    intro x; cases F x <;> cases dot a x <;> rfl
  have hneg : -sumVecs (fun x => sign (F x) * sign (dot a x)) =
      sumVecs (fun x => -(sign (F x) * sign (dot a x))) := by
    have := sumVecs_mul_left (-1) (fun x => sign (F x) * sign (dot a x))
    simp only [Int.neg_mul, Int.one_mul] at this
    exact this.symm
  rw [hneg, sumVecs_congr h1, sumVecs_sub, sumVecs_const, sumVecs_mul_left, Int.mul_one]

/-- Nonlinearity `≥ d` implies `|W_F(a)| ≤ 2^n - 2d` for all `a`. -/
theorem abs_walshBool_le_of_nl {n : Nat} (F : Vec n → Bool) (d B : Int)
    (hnl : hasNonlinearityAtLeast n F d) (hB : (2 : Int) ^ n - 2 * d ≤ B) :
    ∀ a : Vec n, -B ≤ walshBool F a ∧ walshBool F a ≤ B := by
  intro a
  have h0 := hnl a false
  have h1 := hnl a true
  have e0 := walshBool_eq_dist_false F a
  have e1 := walshBool_eq_dist_true F a
  omega

private theorem walsh_const_one_ne_zero {n : Nat} (a : Vec n) (hne : a ≠ zeroVec) :
    walsh (fun _ => (1 : Int)) a = 0 := by
  have hex : ∃ p : Fin n, a p = true := by
    apply Classical.byContradiction; intro h; apply hne; funext i
    cases hai : a i with
    | false => rfl
    | true => exact False.elim (h ⟨i, hai⟩)
  obtain ⟨p, hp⟩ := hex
  have hbp : dot a (basisVec p) = true := by rw [dot_basisVec, hp]
  have hshift := sumVecs_xor_shift (basisVec p) (fun x => sign (dot a x))
  have hflip : ∀ x : Vec n, sign (dot a (xorVec x (basisVec p))) = -sign (dot a x) := by
    intro x; rw [dot_xor_right, hbp, sign_xor]; cases dot a x <;> rfl
  have hneg : sumVecs (fun x => -sign (dot a x)) = -sumVecs (fun x => sign (dot a x)) := by
    have := sumVecs_mul_left (-1) (fun x => sign (dot a x))
    simp only [Int.neg_mul, Int.one_mul] at this; exact this
  have hw : walsh (fun _ => (1 : Int)) a = sumVecs (fun x => sign (dot a x)) :=
    sumVecs_congr (fun x => Int.one_mul _)
  rw [hw]
  rw [sumVecs_congr hflip, hneg] at hshift
  omega

/-! ## Section 2: Involutive Linear Transforms (`swap0`, `shear`, `shearT`) -/

private def swap0 {n : Nat} (p : Fin (n + 1)) (x : Vec (n + 1)) : Vec (n + 1) :=
  fun i => if i = ⟨0, Nat.zero_lt_succ n⟩ then x p
           else if i = p then x ⟨0, Nat.zero_lt_succ n⟩
           else x i

private theorem swap0_invol {n : Nat} (p : Fin (n + 1)) (x : Vec (n + 1)) :
    swap0 p (swap0 p x) = x := by
  funext i; unfold swap0
  by_cases hi0 : i = ⟨0, Nat.zero_lt_succ n⟩
  · subst hi0
    by_cases hp0 : p = ⟨0, Nat.zero_lt_succ n⟩
    · subst hp0; simp only [↓reduceIte]
    · simp only [↓reduceIte, hp0]
  · by_cases hip : i = p
    · subst hip; simp only [hi0, ↓reduceIte]
    · simp only [hi0, hip, ↓reduceIte]

private theorem swap0_xor {n : Nat} (p : Fin (n + 1)) (x y : Vec (n + 1)) :
    swap0 p (xorVec x y) = xorVec (swap0 p x) (swap0 p y) := by
  funext i; unfold swap0 xorVec
  by_cases hi0 : i = ⟨0, Nat.zero_lt_succ n⟩
  · simp only [hi0, ↓reduceIte]
  · by_cases hip : i = p
    · subst hip; simp only [hi0, ↓reduceIte]
    · simp only [hi0, hip, ↓reduceIte]

private theorem dot_update {m : Nat} (q : Fin m) (u v : Vec m) (bu bv : Bool) :
    dot (fun i => if i = q then bu else u i) (fun i => if i = q then bv else v i) =
    xor (xor (bu && bv) (u q && v q)) (dot u v) := by
  induction m with
  | zero => exact Fin.elim0 q
  | succ m ih =>
    cases q with
    | mk j hj =>
      cases j with
      | zero =>
        have htail1 : tailVec (fun i => if i = ⟨0, hj⟩ then bu else u i) = tailVec u := by
          funext ⟨r, hr⟩
          have hne : (⟨r + 1, Nat.succ_lt_succ hr⟩ : Fin (m + 1)) ≠ ⟨0, hj⟩ := by
            intro h; have := congrArg Fin.val h; simp at this
          simp only [tailVec, hne, ↓reduceIte]
        have htail2 : tailVec (fun i => if i = ⟨0, hj⟩ then bv else v i) = tailVec v := by
          funext ⟨r, hr⟩
          have hne : (⟨r + 1, Nat.succ_lt_succ hr⟩ : Fin (m + 1)) ≠ ⟨0, hj⟩ := by
            intro h; have := congrArg Fin.val h; simp at this
          simp only [tailVec, hne, ↓reduceIte]
        unfold dot
        rw [htail1, htail2]
        simp only [↓reduceIte]
        cases bu <;> cases bv <;> cases u ⟨0, hj⟩ <;> cases v ⟨0, hj⟩ <;>
          cases dot (tailVec u) (tailVec v) <;> rfl
      | succ j' =>
        have h0 : (⟨0, Nat.zero_lt_succ m⟩ : Fin (m + 1)) ≠ ⟨j' + 1, hj⟩ := by
          intro h; cases h
        have htail1 : tailVec (fun i => if i = ⟨j' + 1, hj⟩ then bu else u i) =
            (fun i => if i = ⟨j', Nat.lt_of_succ_lt_succ hj⟩ then bu else tailVec u i) := by
          funext ⟨r, hr⟩
          simp only [tailVec]
          by_cases heq : r = j'
          · subst heq; simp
          · have hne1 : (⟨r + 1, Nat.succ_lt_succ hr⟩ : Fin (m + 1)) ≠ ⟨j' + 1, hj⟩ := by
              intro h; exact heq (Nat.succ.inj (Fin.mk.inj h))
            have hne2 : (⟨r, hr⟩ : Fin m) ≠ ⟨j', Nat.lt_of_succ_lt_succ hj⟩ := by
              intro h; exact heq (Fin.mk.inj h)
            simp [hne1, hne2]
        have htail2 : tailVec (fun i => if i = ⟨j' + 1, hj⟩ then bv else v i) =
            (fun i => if i = ⟨j', Nat.lt_of_succ_lt_succ hj⟩ then bv else tailVec v i) := by
          funext ⟨r, hr⟩
          simp only [tailVec]
          by_cases heq : r = j'
          · subst heq; simp
          · have hne1 : (⟨r + 1, Nat.succ_lt_succ hr⟩ : Fin (m + 1)) ≠ ⟨j' + 1, hj⟩ := by
              intro h; exact heq (Nat.succ.inj (Fin.mk.inj h))
            have hne2 : (⟨r, hr⟩ : Fin m) ≠ ⟨j', Nat.lt_of_succ_lt_succ hj⟩ := by
              intro h; exact heq (Fin.mk.inj h)
            simp [hne1, hne2]
        unfold dot
        rw [htail1, htail2]
        simp only [h0, ↓reduceIte]
        rw [ih ⟨j', Nat.lt_of_succ_lt_succ hj⟩ (tailVec u) (tailVec v)]
        change xor (u ⟨0, Nat.zero_lt_succ m⟩ && v ⟨0, Nat.zero_lt_succ m⟩)
               (xor (xor (bu && bv) (u ⟨j' + 1, hj⟩ && v ⟨j' + 1, hj⟩))
                    (dot (tailVec u) (tailVec v))) =
               xor (xor (bu && bv) (u ⟨j' + 1, hj⟩ && v ⟨j' + 1, hj⟩))
               (xor (u ⟨0, Nat.zero_lt_succ m⟩ && v ⟨0, Nat.zero_lt_succ m⟩)
                    (dot (tailVec u) (tailVec v)))
        cases (u ⟨0, Nat.zero_lt_succ m⟩ && v ⟨0, Nat.zero_lt_succ m⟩) <;>
          cases (xor (bu && bv) (u ⟨j' + 1, hj⟩ && v ⟨j' + 1, hj⟩)) <;>
          cases dot (tailVec u) (tailVec v) <;> rfl

private theorem swap0_dot {n : Nat} (p : Fin (n + 1)) (a x : Vec (n + 1)) :
    dot (swap0 p a) (swap0 p x) = dot a x := by
  cases p with
  | mk k hk =>
    cases k with
    | zero =>
      have hId : ∀ v : Vec (n + 1), swap0 ⟨0, hk⟩ v = v := by
        intro v; funext i; unfold swap0
        by_cases h : i = ⟨0, hk⟩
        · subst h; simp only [↓reduceIte]
        · simp only [h, ↓reduceIte]
      rw [hId a, hId x]
    | succ k' =>
      let q : Fin n := ⟨k', Nat.lt_of_succ_lt_succ hk⟩
      have htSwap : ∀ v : Vec (n + 1),
          tailVec (swap0 ⟨k' + 1, hk⟩ v) =
          (fun i => if i = q then v ⟨0, Nat.zero_lt_succ n⟩ else tailVec v i) := by
        intro v; funext ⟨r, hr⟩
        simp only [tailVec, swap0]
        have hne0 : (⟨r + 1, Nat.succ_lt_succ hr⟩ : Fin (n + 1)) ≠ ⟨0, Nat.zero_lt_succ n⟩ := by
          intro h; cases h
        simp only [hne0, ↓reduceIte]
        by_cases heq : r = k'
        · subst heq; simp [q]
        · have h1 : (⟨r + 1, Nat.succ_lt_succ hr⟩ : Fin (n + 1)) ≠ ⟨k' + 1, hk⟩ := by
            intro h; exact heq (Nat.succ.inj (Fin.mk.inj h))
          have h2 : (⟨r, hr⟩ : Fin n) ≠ q := by
            intro h; exact heq (Fin.mk.inj h)
          simp [h1, h2]
      unfold dot
      rw [htSwap a, htSwap x, dot_update q (tailVec a) (tailVec x)]
      simp only [swap0, ↓reduceIte]
      change xor (a ⟨k' + 1, hk⟩ && x ⟨k' + 1, hk⟩)
             (xor (xor (a ⟨0, Nat.zero_lt_succ n⟩ && x ⟨0, Nat.zero_lt_succ n⟩)
                       (a ⟨k' + 1, hk⟩ && x ⟨k' + 1, hk⟩))
                  (dot (tailVec a) (tailVec x))) =
             xor (a ⟨0, Nat.zero_lt_succ n⟩ && x ⟨0, Nat.zero_lt_succ n⟩)
                 (dot (tailVec a) (tailVec x))
      cases (a ⟨k' + 1, hk⟩ && x ⟨k' + 1, hk⟩) <;>
        cases (a ⟨0, Nat.zero_lt_succ n⟩ && x ⟨0, Nat.zero_lt_succ n⟩) <;>
        cases dot (tailVec a) (tailVec x) <;> rfl

private theorem sumVecs_swap0 {n : Nat} (p : Fin (n + 1)) (f : Vec (n + 1) → Int) :
    sumVecs (fun x => f (swap0 p x)) = sumVecs f := by
  cases p with
  | mk k hk =>
    cases k with
    | zero =>
      apply sumVecs_congr; intro x
      have hId : swap0 ⟨0, hk⟩ x = x := by
        funext i; unfold swap0
        by_cases h : i = ⟨0, hk⟩
        · subst h; simp only [↓reduceIte]
        · simp only [h, ↓reduceIte]
      rw [hId]
    | succ k' =>
      let q : Fin n := ⟨k', Nat.lt_of_succ_lt_succ hk⟩
      have hsplit : ∀ (m : Nat) (q : Fin m) (h : Bool → Vec m → Int),
          sumVecs (fun v : Vec m => h (v q) (fun i => if i = q then false else v i)) +
          sumVecs (fun v : Vec m => h (v q) (fun i => if i = q then true else v i)) =
          sumVecs (fun v : Vec m => h false v) + sumVecs (fun v : Vec m => h true v) := by
        intro m; induction m with
        | zero => intro q; exact Fin.elim0 q
        | succ m ih =>
          intro q h
          cases q with
          | mk j hj =>
            cases j with
            | zero =>
              simp only [sumVecs]
              have hc : ∀ (b1 b2 : Bool) (w : Vec m),
                  (fun i : Fin (m + 1) => if i = ⟨0, hj⟩ then b2 else consVec b1 w i) =
                  consVec b2 w := by
                intro b1 b2 w; funext ⟨r, hr⟩; cases r <;> rfl
              simp only [consVec_head, hc]; omega
            | succ j' =>
              let q' : Fin m := ⟨j', Nat.lt_of_succ_lt_succ hj⟩
              simp only [sumVecs]
              have hc : ∀ (b1 b2 : Bool) (w : Vec m),
                  (fun i : Fin (m + 1) => if i = ⟨j' + 1, hj⟩ then b2 else consVec b1 w i) =
                  consVec b1 (fun i => if i = q' then b2 else w i) := by
                intro b1 b2 w; funext ⟨r, hr⟩
                cases r with
                | zero => rfl
                | succ r' =>
                  simp only [consVec]
                  by_cases heq : r' = j'
                  · subst heq; simp [q']
                  · have h1 : (⟨r' + 1, hr⟩ : Fin (m + 1)) ≠ ⟨j' + 1, hj⟩ := by
                      intro h; exact heq (Nat.succ.inj (Fin.mk.inj h))
                    have h2 : (⟨r', Nat.lt_of_succ_lt_succ hr⟩ : Fin m) ≠ q' := by
                      intro h; exact heq (Fin.mk.inj h)
                    simp [h1, h2]
              have hval : ∀ (b1 : Bool) (w : Vec m), consVec b1 w ⟨j' + 1, hj⟩ = w q' := fun _ _ => rfl
              simp only [hc, hval]
              have ih0 := ih q' (fun b w => h b (consVec false w))
              have ih1 := ih q' (fun b w => h b (consVec true w))
              omega
      have hswap_eq : ∀ (b : Bool) (v : Vec n),
          swap0 ⟨k' + 1, hk⟩ (consVec b v) =
          consVec (v q) (fun i => if i = q then b else v i) := by
        intro b v; funext ⟨r, hr⟩
        cases r with
        | zero => simp [swap0, consVec, q]
        | succ r' =>
          simp only [swap0, consVec]
          have hne0 : (⟨r' + 1, hr⟩ : Fin (n + 1)) ≠ ⟨0, Nat.zero_lt_succ n⟩ := by
            intro h; cases h
          simp only [hne0, ↓reduceIte]
          by_cases heq : r' = k'
          · subst heq; simp [q]
          · have h1 : (⟨r' + 1, hr⟩ : Fin (n + 1)) ≠ ⟨k' + 1, hk⟩ := by
              intro h; exact heq (Nat.succ.inj (Fin.mk.inj h))
            have h2 : (⟨r', Nat.lt_of_succ_lt_succ hr⟩ : Fin n) ≠ q := by
              intro h; exact heq (Fin.mk.inj h)
            simp [h1, h2]
      simp only [sumVecs, hswap_eq]
      exact hsplit n q (fun b v => f (consVec b v))

private def shear {n : Nat} (s : Vec (n + 1)) (x : Vec (n + 1)) : Vec (n + 1) :=
  consVec (dot s x) (tailVec x)

private def shearT {n : Nat} (s : Vec (n + 1)) (a : Vec (n + 1)) : Vec (n + 1) :=
  consVec (a ⟨0, Nat.zero_lt_succ n⟩)
          (if a ⟨0, Nat.zero_lt_succ n⟩ then xorVec (tailVec a) (tailVec s) else tailVec a)

private theorem shear_dot {n : Nat} (s a x : Vec (n + 1))
    (hs : s ⟨0, Nat.zero_lt_succ n⟩ = true) :
    dot a (shearT s x) = dot (shear s a) x := by
  have hs0 : dot s a = xor (a ⟨0, Nat.zero_lt_succ n⟩) (dot (tailVec s) (tailVec a)) := by
    conv => lhs; rw [← consVec_eta s, ← consVec_eta a, dot_cons, hs, Bool.true_and]
  unfold shear shearT
  conv => lhs; rw [← consVec_eta a, dot_cons]
  conv => rhs; rw [← consVec_eta x, dot_cons, hs0]
  cases hx0 : x ⟨0, Nat.zero_lt_succ n⟩
  · simp only [Bool.and_false, Bool.false_xor, Bool.false_eq_true, ↓reduceIte]
  · simp only [Bool.and_true, ↓reduceIte, dot_xor_right, dot_comm (tailVec a) (tailVec s)]
    cases a ⟨0, Nat.zero_lt_succ n⟩ <;> cases dot (tailVec s) (tailVec a) <;>
      cases dot (tailVec a) (tailVec x) <;> rfl

private theorem shearT_invol {n : Nat} (s x : Vec (n + 1)) :
    shearT s (shearT s x) = x := by
  unfold shearT
  cases hx0 : x ⟨0, Nat.zero_lt_succ n⟩
  · simp only [consVec_head, tailVec_cons, Bool.false_eq_true, ↓reduceIte]
    rw [← hx0, consVec_eta]
  · simp only [consVec_head, tailVec_cons, ↓reduceIte, xorVec_assoc, xorVec_self, xorVec_zero_right]
    rw [← hx0, consVec_eta]

private theorem shearT_xor {n : Nat} (s a b : Vec (n + 1)) :
    shearT s (xorVec a b) = xorVec (shearT s a) (shearT s b) := by
  unfold shearT
  have hhd : xorVec a b ⟨0, Nat.zero_lt_succ n⟩ = xor (a ⟨0, Nat.zero_lt_succ n⟩) (b ⟨0, Nat.zero_lt_succ n⟩) := rfl
  rw [hhd, tailVec_xorVec, xorVec_cons]
  cases a ⟨0, Nat.zero_lt_succ n⟩ <;> cases b ⟨0, Nat.zero_lt_succ n⟩
  · simp only [Bool.xor_false, Bool.false_eq_true, ↓reduceIte]
  · simp only [Bool.false_xor, Bool.false_eq_true, ↓reduceIte, xorVec_assoc]
  · simp only [Bool.xor_false, Bool.false_eq_true, ↓reduceIte]
    apply congrArg (consVec true); funext j; unfold xorVec
    cases tailVec a j <;> cases tailVec b j <;> cases tailVec s j <;> rfl
  · simp only [Bool.xor_self, Bool.false_eq_true, ↓reduceIte]
    apply congrArg (consVec false); funext j; unfold xorVec
    cases tailVec a j <;> cases tailVec b j <;> cases tailVec s j <;> rfl

private theorem shear_dot_s {n : Nat} (s : Vec (n + 1))
    (hs : s ⟨0, Nat.zero_lt_succ n⟩ = true) (b : Bool) (a' : Vec n) :
    dot (shear s (consVec b a')) s = b := by
  have h1 : dot s (consVec b a') = xor b (dot (tailVec s) a') := by
    conv => lhs; rw [← consVec_eta s, dot_cons, hs, Bool.true_and]
  unfold shear
  rw [tailVec_cons, h1]
  conv => lhs; arg 2; rw [← consVec_eta s]
  rw [dot_cons, hs, Bool.and_true, dot_comm a' (tailVec s)]
  cases b <;> cases dot (tailVec s) a' <;> rfl

private theorem shear_invol {n : Nat} (s a : Vec (n + 1))
    (hs : s ⟨0, Nat.zero_lt_succ n⟩ = true) :
    shear s (shear s a) = a := by
  have hhd : dot s (shear s a) = a ⟨0, Nat.zero_lt_succ n⟩ := by
    rw [dot_comm, ← consVec_eta a]
    exact shear_dot_s s hs (a ⟨0, Nat.zero_lt_succ n⟩) (tailVec a)
  unfold shear at hhd ⊢
  rw [tailVec_cons, hhd, consVec_eta]

private theorem sumVecs_shearT {n : Nat} (s : Vec (n + 1)) (f : Vec (n + 1) → Int) :
    sumVecs (fun x => f (shearT s x)) = sumVecs f := by
  have h0 : ∀ v : Vec n, shearT s (consVec false v) = consVec false v := fun _ => rfl
  have h1 : ∀ v : Vec n, shearT s (consVec true v) = consVec true (xorVec v (tailVec s)) := fun _ => rfl
  simp only [sumVecs, h0, h1]
  rw [sumVecs_xor_shift (tailVec s) (fun v => f (consVec true v))]

private theorem sumVecs_shear {n : Nat} (s : Vec (n + 1)) (hs : s ⟨0, Nat.zero_lt_succ n⟩ = true)
    (f : Vec (n + 1) → Int) :
    sumVecs (fun x => f (shear s x)) = sumVecs f := by
  have h0 : ∀ v : Vec n, shear s (consVec false v) = consVec (dot (tailVec s) v) v := by
    intro v; unfold shear; rw [tailVec_cons]
    have hd : dot s (consVec false v) = dot (tailVec s) v := by
      conv => lhs; rw [← consVec_eta s]
      rw [dot_cons, hs, Bool.and_false, Bool.false_xor]
    rw [hd]
  have h1 : ∀ v : Vec n, shear s (consVec true v) = consVec (!(dot (tailVec s) v)) v := by
    intro v; unfold shear; rw [tailVec_cons]
    have hd : dot s (consVec true v) = !(dot (tailVec s) v) := by
      conv => lhs; rw [← consVec_eta s]
      rw [dot_cons, hs, Bool.and_true]
      cases dot (tailVec s) v <;> rfl
    rw [hd]
  simp only [sumVecs, h0, h1, ← sumVecs_add]
  apply sumVecs_congr; intro v
  cases dot (tailVec s) v <;> simp [Int.add_comm]

private theorem shearT_e0 {n : Nat} (s : Vec (n + 1)) (hs : s ⟨0, Nat.zero_lt_succ n⟩ = true) :
    shearT s (consVec true zeroVec) = s := by
  unfold shearT
  simp only [consVec_head, tailVec_cons, ↓reduceIte, xorVec_zero_left]
  conv => rhs; rw [← consVec_eta s, hs]

private theorem walsh_swap0 {n : Nat} (p : Fin (n + 1)) (g : Vec (n + 1) → Int) (a : Vec (n + 1)) :
    walsh (fun x => g (swap0 p x)) a = walsh g (swap0 p a) := by
  unfold walsh
  rw [← sumVecs_swap0 p (fun x => g (swap0 p x) * sign (dot a x))]
  apply sumVecs_congr; intro x
  rw [swap0_invol, ← swap0_dot p a (swap0 p x), swap0_invol]

private theorem walsh_shearT {n : Nat} (s : Vec (n + 1)) (hs : s ⟨0, Nat.zero_lt_succ n⟩ = true)
    (g : Vec (n + 1) → Int) (a : Vec (n + 1)) :
    walsh (fun x => g (shearT s x)) a = walsh g (shear s a) := by
  unfold walsh
  rw [← sumVecs_shearT s (fun x => g (shearT s x) * sign (dot a x))]
  apply sumVecs_congr; intro x
  rw [shearT_invol, shear_dot s a x hs]

private theorem walsh_shear {n : Nat} (s : Vec (n + 1)) (hs : s ⟨0, Nat.zero_lt_succ n⟩ = true)
    (g : Vec (n + 1) → Int) (a : Vec (n + 1)) :
    walsh (fun x => g (shear s x)) a = walsh g (shearT s a) := by
  unfold walsh
  rw [← sumVecs_shear s hs (fun x => g (shear s x) * sign (dot a x))]
  apply sumVecs_congr; intro x
  rw [shear_invol s x hs, dot_comm a (shear s x), ← shear_dot s x a hs, dot_comm x (shearT s a)]

/-! ## Section 3: Support-XOR Mod-8 Law & Mod-16 Quadratic Theorem -/

/-- Support intersection count `N_F(a) = |{x ∈ F_2^n : F(x) = true ∧ a · x = true}|`. -/
def suppDotCount {n : Nat} (F : Vec n → Bool) (a : Vec n) : Int :=
  sumVecs (fun x => if F x && dot a x then 1 else 0)

/-- Support-XOR vector `v = ⊕_{F(x)=true} x`. -/
def supportXor {n : Nat} (F : Vec n → Bool) : Vec n :=
  fun i => decide (sumVecs (fun x => if F x && x i then 1 else 0) % 2 = 1)

/-- Mod-2 binomial quadratic `Q_F(a) = C(N_F(a), 2) mod 2`. -/
def quadMod2 {n : Nat} (F : Vec n → Bool) (a : Vec n) : Bool :=
  decide (((suppDotCount F a * (suppDotCount F a - 1)) / 2) % 2 = 1)

/-- Degree-`≤ 2` predicate via vanishing 3rd-order discrete derivative. -/
def isQuadratic {k : Nat} (q : Vec k → Bool) : Prop :=
  ∀ a b c : Vec k,
    xor (xor (xor (q (xorVec (xorVec a b) c)) (q (xorVec a b)))
             (xor (q (xorVec a c)) (q (xorVec b c))))
        (xor (xor (q a) (q b)) (xor (q c) (q zeroVec))) = false

private theorem suppDotCount_mod2 : {n : Nat} → (F : Vec n → Bool) → (a : Vec n) →
    suppDotCount F a % 2 = if dot (supportXor F) a then 1 else 0
  | 0, F, a => by
    simp [suppDotCount, sumVecs, dot]
  | n + 1, F, a => by
    let F0 : Vec n → Bool := fun v => F (consVec false v)
    let F1 : Vec n → Bool := fun v => F (consVec true v)
    have ih0 := suppDotCount_mod2 F0 (tailVec a)
    have ih1 := suppDotCount_mod2 F1 (tailVec a)
    have hhead : supportXor F ⟨0, Nat.zero_lt_succ n⟩ = decide (hammingWeight F1 % 2 = 1) := by
      have hsum : sumVecs (fun x : Vec (n + 1) => if F x && x ⟨0, Nat.zero_lt_succ n⟩ then (1 : Int) else 0) =
          hammingWeight F1 := by
        unfold hammingWeight
        simp only [sumVecs, consVec_head, Bool.and_false, Bool.and_true]
        have h0 : sumVecs (fun _ : Vec n => (if false = true then (1 : Int) else 0)) = 0 := by
          have : (fun _ : Vec n => (if false = true then (1 : Int) else 0)) = (fun _ => 0) := rfl
          rw [this, sumVecs_const, Int.mul_zero]
        rw [h0, Int.zero_add]
      unfold supportXor
      rw [hsum]
    have htail : tailVec (supportXor F) = xorVec (supportXor F0) (supportXor F1) := by
      funext i
      unfold tailVec supportXor xorVec
      have hsplit_i :
          sumVecs (fun x : Vec (n + 1) => if F x && x ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ then (1 : Int) else 0) =
          sumVecs (fun v => if F0 v && v i then (1 : Int) else 0) +
          sumVecs (fun v => if F1 v && v i then (1 : Int) else 0) := rfl
      rw [hsplit_i]
      let s0 := sumVecs (fun v => if F0 v && v i then (1 : Int) else 0)
      let s1 := sumVecs (fun v => if F1 v && v i then (1 : Int) else 0)
      change decide ((s0 + s1) % 2 = 1) = xor (decide (s0 % 2 = 1)) (decide (s1 % 2 = 1))
      by_cases hb0 : s0 % 2 = 1 <;> by_cases hb1 : s1 % 2 = 1 <;> simp [hb0, hb1] <;> omega
    have hdot : dot (supportXor F) a =
        xor (supportXor F ⟨0, Nat.zero_lt_succ n⟩ && a ⟨0, Nat.zero_lt_succ n⟩)
            (xor (dot (supportXor F0) (tailVec a)) (dot (supportXor F1) (tailVec a))) := by
      conv => lhs; unfold dot
      rw [htail, dot_xor_left]
    have hsplit : suppDotCount F a =
        suppDotCount F0 (tailVec a) +
        (if a ⟨0, Nat.zero_lt_succ n⟩ then hammingWeight F1 - suppDotCount F1 (tailVec a)
         else suppDotCount F1 (tailVec a)) := by
      unfold suppDotCount hammingWeight
      simp only [sumVecs]
      congr 1
      · apply sumVecs_congr; intro v
        have hd : dot a (consVec false v) = dot (tailVec a) v := by
          conv => lhs; rw [← consVec_eta a]
          rw [dot_cons, Bool.and_false, Bool.false_xor]
        rw [hd]
      · cases ha0 : a ⟨0, Nat.zero_lt_succ n⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]
          apply sumVecs_congr; intro v
          have hd : dot a (consVec true v) = dot (tailVec a) v := by
            conv => lhs; rw [← consVec_eta a]
            rw [ha0, dot_cons, Bool.false_and, Bool.false_xor]
          rw [hd]
        · simp only [↓reduceIte, ← sumVecs_sub]
          apply sumVecs_congr; intro v
          have hd : dot a (consVec true v) = !(dot (tailVec a) v) := by
            conv => lhs; rw [← consVec_eta a]
            rw [ha0, dot_cons, Bool.and_true]
            cases dot (tailVec a) v <;> rfl
          rw [hd]; dsimp only [F1]
          cases F (consVec true v) <;> cases dot (tailVec a) v <;> rfl
    rw [hsplit, hdot, hhead]
    cases ha0 : a ⟨0, Nat.zero_lt_succ n⟩
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.false_xor]
      cases hd0 : dot (supportXor F0) (tailVec a) <;>
        cases hd1 : dot (supportXor F1) (tailVec a) <;>
        simp [hd0, hd1] at ih0 ih1 ⊢ <;> omega
    · simp only [↓reduceIte, Bool.and_true]
      by_cases hw : hammingWeight F1 % 2 = 1 <;>
        cases hd0 : dot (supportXor F0) (tailVec a) <;>
        cases hd1 : dot (supportXor F1) (tailVec a) <;>
        simp [hw, hd0, hd1] at ih0 ih1 ⊢ <;> omega

private theorem walshBool_eq_four_suppDotCount {n : Nat} (F : Vec n → Bool)
    (hbal : isBalanced n F) (a : Vec n) (hne : a ≠ zeroVec) :
    walshBool F a = 4 * suppDotCount F a - (2 : Int) ^ n := by
  have hwa : sumVecs (fun x => if dot a x then (1 : Int) else 0) = (2 : Int) ^ n / 2 := by
    have h0 := walsh_const_one_ne_zero a hne
    unfold walsh at h0
    have h1 : ∀ x : Vec n, (1 : Int) * sign (dot a x) = 1 - 2 * (if dot a x then 1 else 0) := by
      intro x; cases dot a x <;> rfl
    rw [sumVecs_congr h1, sumVecs_sub, sumVecs_const, sumVecs_mul_left, Int.mul_one] at h0
    omega
  have hwt2 : 2 * sumVecs (fun x => if dot a x then (1 : Int) else 0) = (2 : Int) ^ n := by
    have h0 := walsh_const_one_ne_zero a hne
    unfold walsh at h0
    have h1 : ∀ x : Vec n, (1 : Int) * sign (dot a x) = 1 - 2 * (if dot a x then 1 else 0) := by
      intro x; cases dot a x <;> rfl
    rw [sumVecs_congr h1, sumVecs_sub, sumVecs_const, sumVecs_mul_left, Int.mul_one] at h0
    omega
  unfold walshBool walsh suppDotCount
  have hpw : ∀ x : Vec n, sign (F x) * sign (dot a x) =
      1 - 2 * (if F x then 1 else 0) - 2 * (if dot a x then 1 else 0) +
      4 * (if F x && dot a x then 1 else 0) := by
    intro x; cases F x <;> cases dot a x <;> rfl
  rw [sumVecs_congr hpw, sumVecs_add, sumVecs_sub, sumVecs_sub,
      sumVecs_const, sumVecs_mul_left, sumVecs_mul_left, sumVecs_mul_left, Int.mul_one]
  unfold isBalanced hammingWeight at hbal
  omega

/-- Mod-16 law: for `n ≥ 4` and balanced `F`, `W_F(a) ≡ 4 * N_F(a) (mod 16)` for all `a`. -/
private theorem walshBool_mod16_eq {n : Nat} (hn : 4 ≤ n) (F : Vec n → Bool)
    (hbal : isBalanced n F) (a : Vec n) :
    (16 : Int) ∣ (walshBool F a - 4 * suppDotCount F a) := by
  by_cases ha : a = zeroVec
  · subst ha
    have h0 := walshBool_zero_of_balanced F hbal
    have hn0 : suppDotCount F zeroVec = 0 := by
      unfold suppDotCount
      have hz : ∀ x : Vec n, (if F x && dot zeroVec x then (1 : Int) else 0) = 0 := by
        intro x; rw [dot_zero_left, Bool.and_false]; rfl
      rw [sumVecs_congr hz, sumVecs_const, Int.mul_zero]
    rw [h0, hn0]; exact ⟨0, by omega⟩
  · rw [walshBool_eq_four_suppDotCount F hbal a ha]
    obtain ⟨t, ht⟩ := two_pow_dvd_of_le hn
    exact ⟨-t, by change 4 * suppDotCount F a - (2 : Int) ^ n - 4 * suppDotCount F a = 16 * -t
                  rw [ht]; change _ = _; omega⟩

/-- Mod-8 law: for `n ≥ 4` and balanced `F`, `W_F(a) ≡ 4 (a · supportXor F) (mod 8)`. -/
private theorem walshBool_mod8 {n : Nat} (hn : 4 ≤ n) (F : Vec n → Bool)
    (hbal : isBalanced n F) (a : Vec n) :
    walshBool F a % 8 = if dot (supportXor F) a then 4 else 0 := by
  obtain ⟨k, hk⟩ := walshBool_mod16_eq hn F hbal a
  have hmod2 := suppDotCount_mod2 F a
  cases hd : dot (supportXor F) a <;> simp [hd] at hmod2 ⊢ <;> omega

/-- Exact mod-16 signature of `W_F(a)` via `supportXor F` and `quadMod2 F`. -/
private theorem walshBool_mod16_quad {n : Nat} (hn : 4 ≤ n) (F : Vec n → Bool)
    (hbal : isBalanced n F) (a : Vec n) :
    walshBool F a % 16 =
      (if dot (supportXor F) a then 4 else 0) + (if quadMod2 F a then 8 else 0) := by
  obtain ⟨k, hk⟩ := walshBool_mod16_eq hn F hbal a
  have hmod2 := suppDotCount_mod2 F a
  let N := suppDotCount F a
  have hN : N = 4 * (N / 4) + N % 4 := by omega
  have hr : N % 4 = 0 ∨ N % 4 = 1 ∨ N % 4 = 2 ∨ N % 4 = 3 := by omega
  unfold quadMod2
  change walshBool F a % 16 =
    (if dot (supportXor F) a then 4 else 0) + (if decide ((N * (N - 1) / 2) % 2 = 1) then 8 else 0)
  have hpair : (N * (N - 1) / 2) % 2 = if (N % 4 = 2 ∨ N % 4 = 3) then 1 else 0 := by
    let q := N / 4
    rcases hr with h0 | h1 | h2 | h3
    · have hN0 : N = 4 * q := by omega
      have hprod : N * (N - 1) = 2 * (2 * q * (4 * q - 1)) := by
        rw [hN0]; simp only [Int.mul_sub, Int.mul_one, Int.mul_assoc]; omega
      have hdiv : N * (N - 1) / 2 = 2 * q * (4 * q - 1) := by
        rw [hprod, Int.mul_ediv_cancel_left _ (by decide)]
      have hev : (2 * q * (4 * q - 1)) % 2 = 0 := by
        rw [Int.mul_assoc]; omega
      rw [hdiv, hev]; simp [h0]
    · have hN1 : N = 4 * q + 1 := by omega
      have hprod : N * (N - 1) = 2 * ((4 * q + 1) * (2 * q)) := by
        rw [hN1, show (4 * q + 1 - 1 : Int) = 2 * (2 * q) by omega, Int.mul_left_comm]
      have hdiv : N * (N - 1) / 2 = (4 * q + 1) * (2 * q) := by
        rw [hprod, Int.mul_ediv_cancel_left _ (by decide)]
      have hev : ((4 * q + 1) * (2 * q)) % 2 = 0 := by
        rw [Int.mul_comm, Int.mul_assoc]; omega
      rw [hdiv, hev]; simp [h1]
    · have hN2 : N = 4 * q + 2 := by omega
      have hprod : N * (N - 1) = 2 * ((2 * q + 1) * (4 * q + 1)) := by
        rw [hN2, show (4 * q + 2 - 1 : Int) = 4 * q + 1 by omega,
            show (4 * q + 2 : Int) = 2 * (2 * q + 1) by omega, Int.mul_assoc]
      have hdiv : N * (N - 1) / 2 = (2 * q + 1) * (4 * q + 1) := by
        rw [hprod, Int.mul_ediv_cancel_left _ (by decide)]
      have hodd : ((2 * q + 1) * (4 * q + 1)) % 2 = 1 := by
        rw [Int.mul_emod, show (2 * q + 1) % 2 = 1 by omega, show (4 * q + 1) % 2 = 1 by omega]; rfl
      rw [hdiv, hodd]; simp [h2]
    · have hN3 : N = 4 * q + 3 := by omega
      have hprod : N * (N - 1) = 2 * ((4 * q + 3) * (2 * q + 1)) := by
        rw [hN3, show (4 * q + 3 - 1 : Int) = 2 * (2 * q + 1) by omega, Int.mul_left_comm]
      have hdiv : N * (N - 1) / 2 = (4 * q + 3) * (2 * q + 1) := by
        rw [hprod, Int.mul_ediv_cancel_left _ (by decide)]
      have hodd : ((4 * q + 3) * (2 * q + 1)) % 2 = 1 := by
        rw [Int.mul_emod, show (4 * q + 3) % 2 = 1 by omega, show (2 * q + 1) % 2 = 1 by omega]; rfl
      rw [hdiv, hodd]; simp [h3]
  rw [hpair]
  rcases hr with h0 | h1 | h2 | h3
  · have hf : ¬(N % 4 = 2 ∨ N % 4 = 3) := by omega
    rw [if_neg hf]
    have hdec : (if decide ((0 : Int) = 1) = true then (8 : Int) else 0) = 0 := rfl
    rw [hdec, Int.add_zero]
    cases hd : dot (supportXor F) a <;> simp [hd] at hmod2 ⊢ <;> omega
  · have hf : ¬(N % 4 = 2 ∨ N % 4 = 3) := by omega
    rw [if_neg hf]
    have hdec : (if decide ((0 : Int) = 1) = true then (8 : Int) else 0) = 0 := rfl
    rw [hdec, Int.add_zero]
    cases hd : dot (supportXor F) a <;> simp [hd] at hmod2 ⊢ <;> omega
  · have ht : (N % 4 = 2 ∨ N % 4 = 3) := Or.inl h2
    rw [if_pos ht]
    have hdec : (if decide ((1 : Int) = 1) = true then (8 : Int) else 0) = 8 := rfl
    rw [hdec]
    cases hd : dot (supportXor F) a <;> simp [hd] at hmod2 ⊢ <;> omega
  · have ht : (N % 4 = 2 ∨ N % 4 = 3) := Or.inr h3
    rw [if_pos ht]
    have hdec : (if decide ((1 : Int) = 1) = true then (8 : Int) else 0) = 8 := rfl
    rw [hdec]
    cases hd : dot (supportXor F) a <;> simp [hd] at hmod2 ⊢ <;> omega

/-! ### Proof that `quadMod2 F` is Always Quadratic (`deg ≤ 2`) -/

private theorem isQuadratic_const {k : Nat} (c : Bool) : isQuadratic (k := k) (fun _ => c) := by
  intro a b c'; cases c <;> rfl

private theorem isQuadratic_xor {k : Nat} {p q : Vec k → Bool}
    (hp : isQuadratic p) (hq : isQuadratic q) :
    isQuadratic (fun a => xor (p a) (q a)) := by
  intro a b c
  dsimp only
  have h1 := hp a b c
  have h2 := hq a b c
  generalize p (xorVec (xorVec a b) c) = p123 at h1 ⊢
  generalize p (xorVec a b) = p12 at h1 ⊢
  generalize p (xorVec a c) = p13 at h1 ⊢
  generalize p (xorVec b c) = p23 at h1 ⊢
  generalize p a = p1 at h1 ⊢
  generalize p b = p2 at h1 ⊢
  generalize p c = p3 at h1 ⊢
  generalize p zeroVec = p0 at h1 ⊢
  generalize q (xorVec (xorVec a b) c) = q123 at h2 ⊢
  generalize q (xorVec a b) = q12 at h2 ⊢
  generalize q (xorVec a c) = q13 at h2 ⊢
  generalize q (xorVec b c) = q23 at h2 ⊢
  generalize q a = q1 at h2 ⊢
  generalize q b = q2 at h2 ⊢
  generalize q c = q3 at h2 ⊢
  generalize q zeroVec = q0 at h2 ⊢
  have hrearr :
      xor (xor (xor (xor p123 q123) (xor p12 q12)) (xor (xor p13 q13) (xor p23 q23)))
          (xor (xor (xor p1 q1) (xor p2 q2)) (xor (xor p3 q3) (xor p0 q0))) =
      xor (xor (xor (xor p123 p12) (xor p13 p23)) (xor (xor p1 p2) (xor p3 p0)))
          (xor (xor (xor q123 q12) (xor q13 q23)) (xor (xor q1 q2) (xor q3 q0))) := by
    have h4 : ∀ x1 y1 x2 y2 : Bool, xor (xor x1 y1) (xor x2 y2) = xor (xor x1 x2) (xor y1 y2) := by
      intro x1 y1 x2 y2; cases x1 <;> cases y1 <;> cases x2 <;> cases y2 <;> rfl
    rw [h4 p123 q123 p12 q12, h4 p13 q13 p23 q23, h4 p1 q1 p2 q2, h4 p3 q3 p0 q0,
        h4 (xor p123 p12) (xor q123 q12) (xor p13 p23) (xor q13 q23),
        h4 (xor p1 p2) (xor q1 q2) (xor p3 p0) (xor q3 q0),
        h4]
  rw [hrearr, h1, h2]; rfl

private theorem isQuadratic_linear {k : Nat} (u : Vec k) : isQuadratic (fun a => dot u a) := by
  intro a b c
  simp only [dot_xor_right, dot_zero_right]
  cases dot u a <;> cases dot u b <;> cases dot u c <;> rfl

private theorem isQuadratic_prod_linear {k : Nat} (u v : Vec k) :
    isQuadratic (fun a => dot u a && dot v a) := by
  intro a b c
  simp only [dot_xor_right, dot_zero_right]
  cases dot u a <;> cases dot u b <;> cases dot u c <;>
    cases dot v a <;> cases dot v b <;> cases dot v c <;> rfl

private theorem isQuadratic_tail {k : Nat} {q : Vec k → Bool} (hq : isQuadratic q) :
    isQuadratic (fun a : Vec (k + 1) => q (tailVec a)) := by
  intro a b c
  have h := hq (tailVec a) (tailVec b) (tailVec c)
  simpa only [tailVec_xorVec, tailVec_zeroVec] using h

private theorem decide_mod2_add (a b : Int) :
    decide ((a + b) % 2 = 1) = xor (decide (a % 2 = 1)) (decide (b % 2 = 1)) := by
  by_cases ha : a % 2 = 1 <;> by_cases hb : b % 2 = 1 <;> simp [ha, hb] <;> omega

private theorem decide_mod2_if (b : Bool) (x : Int) (hx : x % 2 = if b then 1 else 0) :
    decide (x % 2 = 1) = b := by
  cases b <;> simp [hx]

private theorem two_dvd_mul_pred (X : Int) : (2 : Int) ∣ X * (X - 1) := by
  by_cases h : X % 2 = 0
  · have hX : X = 2 * (X / 2) := by omega
    refine ⟨(X / 2) * (X - 1), ?_⟩
    conv => lhs; arg 1; rw [hX]
    rw [Int.mul_assoc]
  · have hX : X - 1 = 2 * ((X - 1) / 2) := by omega
    refine ⟨X * ((X - 1) / 2), ?_⟩
    conv => lhs; arg 2; rw [hX]
    rw [Int.mul_left_comm]

private theorem binom2_add (M N : Int) :
    (M + N) * (M + N - 1) / 2 = M * (M - 1) / 2 + N * (N - 1) / 2 + M * N := by
  obtain ⟨a, ha⟩ := two_dvd_mul_pred (M + N)
  obtain ⟨b, hb⟩ := two_dvd_mul_pred M
  obtain ⟨c, hc⟩ := two_dvd_mul_pred N
  have h1 : (M + N) * (M + N - 1) = M * (M - 1) + N * (N - 1) + 2 * (M * N) := by
    simp only [Int.add_mul, Int.mul_add, Int.mul_sub, Int.sub_mul, Int.mul_one, Int.one_mul, Int.mul_comm N M]
    omega
  rw [ha, hb, hc, Int.mul_ediv_cancel_left _ (by decide),
      Int.mul_ediv_cancel_left _ (by decide), Int.mul_ediv_cancel_left _ (by decide)]
  omega

private theorem binom2_sub (W K : Int) :
    (W - K) * (W - K - 1) / 2 = W * (W - 1) / 2 + K * (K - 1) / 2 + K * (1 - W) := by
  obtain ⟨a, ha⟩ := two_dvd_mul_pred (W - K)
  obtain ⟨b, hb⟩ := two_dvd_mul_pred W
  obtain ⟨c, hc⟩ := two_dvd_mul_pred K
  have h1 : (W - K) * (W - K - 1) = W * (W - 1) + K * (K - 1) + 2 * (K * (1 - W)) := by
    simp only [Int.sub_mul, Int.mul_sub, Int.mul_one, Int.one_mul, Int.mul_comm K W]
    omega
  rw [ha, hb, hc, Int.mul_ediv_cancel_left _ (by decide),
      Int.mul_ediv_cancel_left _ (by decide), Int.mul_ediv_cancel_left _ (by decide)]
  omega

/-- `quadMod2 F` has algebraic degree `≤ 2` for every Boolean function `F`. -/
theorem quadMod2_isQuadratic : {n : Nat} → (F : Vec n → Bool) → isQuadratic (quadMod2 F)
  | 0, F => by
    have hconst : quadMod2 F = fun _ => false := by
      funext a; simp [quadMod2, suppDotCount, sumVecs, dot]
    rw [hconst]; exact isQuadratic_const false
  | n + 1, F => by
    let F0 : Vec n → Bool := fun v => F (consVec false v)
    let F1 : Vec n → Bool := fun v => F (consVec true v)
    let W : Int := hammingWeight F1
    let e0 : Vec (n + 1) := consVec true zeroVec
    let u0 : Vec (n + 1) := consVec false (supportXor F0)
    let u1 : Vec (n + 1) := consVec (decide (W % 2 = 1)) (supportXor F1)
    let v1 : Vec (n + 1) := consVec false (supportXor F1)
    let cW : Bool := decide ((W * (W - 1) / 2) % 2 = 1)
    let cW1 : Bool := decide ((1 - W) % 2 = 1)
    have hdecomp : ∀ a : Vec (n + 1),
        quadMod2 F a =
          xor (xor (quadMod2 F0 (tailVec a)) (quadMod2 F1 (tailVec a)))
              (xor (dot u0 a && dot u1 a)
                   (xor (if cW then dot e0 a else false)
                        (if cW1 then (dot e0 a && dot v1 a) else false))) := by
      intro a
      let M := suppDotCount F0 (tailVec a)
      let K := suppDotCount F1 (tailVec a)
      let N' := if a ⟨0, Nat.zero_lt_succ n⟩ then W - K else K
      have hsplit : suppDotCount F a = M + N' := by
        unfold suppDotCount
        simp only [sumVecs]
        congr 1
        · apply sumVecs_congr; intro v
          have hd : dot a (consVec false v) = dot (tailVec a) v := by
            conv => lhs; rw [← consVec_eta a]
            rw [dot_cons, Bool.and_false, Bool.false_xor]
          rw [hd]
        · dsimp only [N', W, K, hammingWeight, suppDotCount]
          cases ha0 : a ⟨0, Nat.zero_lt_succ n⟩
          · simp only [Bool.false_eq_true, ↓reduceIte]
            apply sumVecs_congr; intro v
            have hd : dot a (consVec true v) = dot (tailVec a) v := by
              conv => lhs; rw [← consVec_eta a]
              rw [ha0, dot_cons, Bool.false_and, Bool.false_xor]
            rw [hd]
          · simp only [↓reduceIte, ← sumVecs_sub]
            apply sumVecs_congr; intro v
            have hd : dot a (consVec true v) = !(dot (tailVec a) v) := by
              conv => lhs; rw [← consVec_eta a]
              rw [ha0, dot_cons, Bool.and_true]
              cases dot (tailVec a) v <;> rfl
            rw [hd]; dsimp only [F1]
            cases F (consVec true v) <;> cases dot (tailVec a) v <;> rfl
      have hM2 : M % 2 = if dot u0 a then 1 else 0 := by
        have h := suppDotCount_mod2 F0 (tailVec a)
        have hdot : dot u0 a = dot (supportXor F0) (tailVec a) := by
          conv => lhs; rw [← consVec_eta a]; unfold u0; rw [dot_cons, Bool.false_and, Bool.false_xor]
        rw [hdot]; exact h
      have hK2 : K % 2 = if dot v1 a then 1 else 0 := by
        have h := suppDotCount_mod2 F1 (tailVec a)
        have hdot : dot v1 a = dot (supportXor F1) (tailVec a) := by
          conv => lhs; rw [← consVec_eta a]; unfold v1; rw [dot_cons, Bool.false_and, Bool.false_xor]
        rw [hdot]; exact h
      have hN'2 : N' % 2 = if dot u1 a then 1 else 0 := by
        have hdot : dot u1 a = xor (decide (W % 2 = 1) && a ⟨0, Nat.zero_lt_succ n⟩)
                                   (dot (supportXor F1) (tailVec a)) := by
          conv => lhs; rw [← consVec_eta a]; unfold u1; rw [dot_cons]
        have h := suppDotCount_mod2 F1 (tailVec a)
        rw [hdot]; dsimp only [N']
        cases ha0 : a ⟨0, Nat.zero_lt_succ n⟩
        · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.false_xor]; exact h
        · simp only [↓reduceIte, Bool.and_true]
          by_cases hw : W % 2 = 1 <;> cases hd : dot (supportXor F1) (tailVec a) <;>
            simp [hw, hd] at h ⊢ <;> omega
      have he0 : dot e0 a = a ⟨0, Nat.zero_lt_succ n⟩ := by
        conv => lhs; rw [← consVec_eta a]; unfold e0
        rw [dot_cons, dot_zero_left, Bool.true_and, Bool.xor_false]
      have hMN : decide ((M * N') % 2 = 1) = (dot u0 a && dot u1 a) := by
        apply decide_mod2_if
        rw [Int.mul_emod, hM2, hN'2]
        cases dot u0 a <;> cases dot u1 a <;> rfl
      have hK1W : decide ((K * (1 - W)) % 2 = 1) = (cW1 && dot v1 a) := by
        apply decide_mod2_if
        rw [Int.mul_emod, hK2]
        by_cases h1w : (1 - W) % 2 = 1 <;> cases hv : dot v1 a <;> simp [cW1, h1w, hv] <;> omega
      unfold quadMod2
      rw [hsplit, binom2_add M N', decide_mod2_add, decide_mod2_add, hMN, he0]
      change xor (xor (quadMod2 F0 (tailVec a)) (decide ((N' * (N' - 1) / 2) % 2 = 1)))
                 (dot u0 a && dot u1 a) = _
      cases ha0 : a ⟨0, Nat.zero_lt_succ n⟩
      · have hN'eq : N' = K := by dsimp only [N']; rw [ha0]; rfl
        rw [hN'eq]
        change xor (xor (quadMod2 F0 (tailVec a)) (quadMod2 F1 (tailVec a))) (dot u0 a && dot u1 a) =
               xor (xor (quadMod2 F0 (tailVec a)) (quadMod2 F1 (tailVec a)))
                   (xor (dot u0 a && dot u1 a) (xor (if cW then false else false) (if cW1 then (false && dot v1 a) else false)))
        simp only [ite_self, Bool.false_and, Bool.xor_false]
      · have hN'eq : N' = W - K := by dsimp only [N']; rw [ha0]; rfl
        rw [hN'eq, binom2_sub W K, decide_mod2_add, decide_mod2_add, hK1W]
        change xor (xor (quadMod2 F0 (tailVec a))
                        (xor (xor cW (quadMod2 F1 (tailVec a))) (cW1 && dot v1 a)))
                   (dot u0 a && dot u1 a) =
               xor (xor (quadMod2 F0 (tailVec a)) (quadMod2 F1 (tailVec a)))
                   (xor (dot u0 a && dot u1 a)
                        (xor (if cW then true else false)
                             (if cW1 then (true && dot v1 a) else false)))
        have hcw_eq : (if cW then true else false) = cW := by cases cW <;> rfl
        have hcw1_eq : (if cW1 then (true && dot v1 a) else false) = (cW1 && dot v1 a) := by
          cases cW1 <;> cases dot v1 a <;> rfl
        rw [hcw_eq, hcw1_eq]
        generalize quadMod2 F0 (tailVec a) = a0
        generalize quadMod2 F1 (tailVec a) = a1
        generalize (dot u0 a && dot u1 a) = p1
        generalize (cW1 && dot v1 a) = p2
        cases a0 <;> cases a1 <;> cases p1 <;> cases cW <;> cases p2 <;> rfl
    have heq_fn : quadMod2 F = fun a =>
        xor (xor (quadMod2 F0 (tailVec a)) (quadMod2 F1 (tailVec a)))
            (xor (dot u0 a && dot u1 a)
                 (xor (if cW then dot e0 a else false)
                      (if cW1 then (dot e0 a && dot v1 a) else false))) :=
      funext hdecomp
    rw [heq_fn]
    refine isQuadratic_xor
      (isQuadratic_xor (isQuadratic_tail (quadMod2_isQuadratic F0))
                       (isQuadratic_tail (quadMod2_isQuadratic F1)))
      (isQuadratic_xor (isQuadratic_prod_linear u0 u1)
        (isQuadratic_xor
          (by cases cW; exact isQuadratic_const false; exact isQuadratic_linear e0)
          (by cases cW1; exact isQuadratic_const false; exact isQuadratic_prod_linear e0 v1)))

/-! ## Section 4: Coordinate-Free Quadratic Autocorrelation & Subspace Cardinality -/

/-- Computable membership in the radical of a quadratic Boolean function `q`. -/
def isRad {k : Nat} (q : Vec k → Bool) (u : Vec k) : Bool :=
  allVecs (fun a => (xor (q (xorVec a u)) (q a)) == (xor (q u) (q zeroVec)))

/-- Cardinality `|Rad(q)|`. -/
def radSize {k : Nat} (q : Vec k → Bool) : Int :=
  sumVecs (fun u => if isRad q u then 1 else 0)

private theorem isRad_true_iff {k : Nat} (q : Vec k → Bool) (u : Vec k) :
    isRad q u = true ↔ ∀ a : Vec k, xor (q (xorVec a u)) (q a) = xor (q u) (q zeroVec) := by
  unfold isRad
  rw [allVecs_true_iff]
  constructor
  · intro h a; exact beq_iff_eq.mp (h a)
  · intro h a; exact beq_iff_eq.mpr (h a)

private theorem isRad_zero {k : Nat} (q : Vec k → Bool) : isRad q zeroVec = true := by
  rw [isRad_true_iff]; intro a; simp [xorVec_zero_right]

private theorem isRad_xor {k : Nat} {q : Vec k → Bool}
    (u v : Vec k) (hu : isRad q u = true) (hv : isRad q v = true) :
    isRad q (xorVec u v) = true := by
  rw [isRad_true_iff] at hu hv ⊢
  intro a
  have h1 := hv (xorVec a u)
  have h2 := hu a
  have h3 := hv u
  rw [xorVec_assoc] at h1
  generalize q (xorVec a (xorVec u v)) = x1 at h1 ⊢
  generalize q (xorVec a u) = x2 at h1 h2
  generalize q (xorVec u v) = x3 at h3 ⊢
  generalize q u = x4 at h2 h3
  generalize q v = x5 at h1 h3
  generalize q a = x6 at h2 ⊢
  generalize q zeroVec = x0 at h1 h2 h3 ⊢
  cases x0 <;> cases x1 <;> cases x2 <;> cases x3 <;> cases x4 <;> cases x5 <;> cases x6 <;> simp_all

/-- Every linear subspace of `F_2^k` has cardinality `2^d` for some `d ≤ k`. -/
private theorem subspace_size_pow2 : {k : Nat} → (S : Vec k → Bool) →
    S zeroVec = true →
    (∀ u v, S u = true → S v = true → S (xorVec u v) = true) →
    ∃ d : Nat, d ≤ k ∧ sumVecs (fun u => if S u then 1 else 0) = (2 : Int) ^ d
  | 0, S, h0, _ => by
    refine ⟨0, Nat.le_refl 0, ?_⟩
    simp only [sumVecs]
    have hz : (fun i : Fin 0 => Fin.elim0 i) = zeroVec := by funext i; exact Fin.elim0 i
    rw [hz, h0]; rfl
  | k + 1, S, h0, hcl => by
    let S0 : Vec k → Bool := fun v => S (consVec false v)
    let S1 : Vec k → Bool := fun v => S (consVec true v)
    have hS0_0 : S0 zeroVec = true := by
      dsimp only [S0]; rw [← zeroVec_cons]; exact h0
    have hS0_cl : ∀ u v, S0 u = true → S0 v = true → S0 (xorVec u v) = true := by
      intro u v hu hv
      have h := hcl (consVec false u) (consVec false v) hu hv
      rw [xorVec_cons, Bool.xor_false] at h; exact h
    obtain ⟨d, hdk, hd_eq⟩ := subspace_size_pow2 S0 hS0_0 hS0_cl
    by_cases hex : ∃ v0 : Vec k, S1 v0 = true
    · obtain ⟨v0, hv0⟩ := hex
      have hS1_eq : ∀ v : Vec k, S1 v = S0 (xorVec v v0) := by
        intro v
        cases h1 : S1 v
        · cases h2 : S0 (xorVec v v0)
          · rfl
          · have h := hcl (consVec false (xorVec v v0)) (consVec true v0) h2 hv0
            rw [xorVec_cons, Bool.false_xor, xorVec_assoc, xorVec_self, xorVec_zero_right] at h
            change S1 v = true at h; rw [h1] at h; cases h
        · have h := hcl (consVec true v) (consVec true v0) h1 hv0
          rw [xorVec_cons, Bool.xor_self] at h
          exact h.symm
      refine ⟨d + 1, Nat.succ_le_succ hdk, ?_⟩
      simp only [sumVecs]
      change sumVecs (fun v => if S0 v then 1 else 0) + sumVecs (fun v => if S1 v then 1 else 0) = _
      have hshift : sumVecs (fun v => if S1 v then (1 : Int) else 0) =
          sumVecs (fun v => if S0 v then (1 : Int) else 0) := by
        rw [sumVecs_congr (fun v => by rw [hS1_eq v])]
        exact sumVecs_xor_shift v0 (fun v => if S0 v then 1 else 0)
      rw [hshift, hd_eq, Int.pow_succ]; omega
    · refine ⟨d, Nat.le_succ_of_le hdk, ?_⟩
      simp only [sumVecs]
      change sumVecs (fun v => if S0 v then 1 else 0) + sumVecs (fun v => if S1 v then 1 else 0) = _
      have hS1_z : ∀ v : Vec k, (if S1 v then (1 : Int) else 0) = 0 := by
        intro v
        cases h : S1 v
        · rfl
        · exact False.elim (hex ⟨v, h⟩)
      rw [sumVecs_congr hS1_z, sumVecs_const, Int.mul_zero, Int.add_zero, hd_eq]

private theorem xor_sw (p q r s : Bool) : xor (xor p q) (xor r s) = xor (xor p r) (xor q s) := by
  cases p <;> cases q <;> cases r <;> cases s <;> rfl

private theorem xor_pair_eq (A B C D : Bool) (h : xor (xor A B) (xor C D) = false) :
    xor A B = xor C D := by
  cases A <;> cases B <;> cases C <;> cases D <;> simp_all

private theorem xor_group8 (A x3 x4 x5 x6 B : Bool) :
    xor (xor A (xor x3 x4)) (xor (xor x5 x6) B) =
    xor (xor A (xor x3 x5)) (xor (xor x4 x6) B) := by
  calc
    xor (xor A (xor x3 x4)) (xor (xor x5 x6) B)
        = xor (xor A B) (xor (xor x3 x4) (xor x5 x6)) := by
          rw [Bool.xor_comm (xor x5 x6) B, xor_sw A (xor x3 x4) B (xor x5 x6)]
    _ = xor (xor A B) (xor (xor x3 x5) (xor x4 x6)) := by
          rw [xor_sw x3 x4 x5 x6]
    _ = xor (xor A (xor x3 x5)) (xor (xor x4 x6) B) := by
          rw [xor_sw A B (xor x3 x5) (xor x4 x6), Bool.xor_comm B (xor x4 x6)]

/-- Coordinate-free autocorrelation of any quadratic Boolean function `q`. -/
private theorem walshBool_sq_quadratic {k : Nat} (q : Vec k → Bool) (hq : isQuadratic q) (x : Vec k) :
    walshBool q x * walshBool q x =
      (2 : Int) ^ k * sumVecs (fun u => if isRad q u then sign (xor (dot x u) (xor (q u) (q zeroVec))) else 0) := by
  have h1 : walshBool q x * walshBool q x =
      sumVecs (fun u => sign (dot x u) * sumVecs (fun a => sign (xor (q (xorVec a u)) (q a)))) := by
    unfold walshBool walsh
    have hmul : sumVecs (fun a => sign (q a) * sign (dot x a)) *
                sumVecs (fun b => sign (q b) * sign (dot x b)) =
        sumVecs (fun a => sumVecs (fun b => (sign (q a) * sign (dot x a)) * (sign (q b) * sign (dot x b)))) := by
      rw [← sumVecs_mul_right]
      apply sumVecs_congr; intro a
      rw [sumVecs_mul_left]
    rw [hmul]
    have hshift : ∀ a : Vec k,
        sumVecs (fun b => (sign (q a) * sign (dot x a)) * (sign (q b) * sign (dot x b))) =
        sumVecs (fun u => sign (dot x u) * sign (xor (q (xorVec a u)) (q a))) := by
      intro a
      rw [← sumVecs_xor_shift a]
      apply sumVecs_congr; intro u
      rw [xorVec_comm u a, dot_xor_right, sign_xor, sign_xor]
      have hsq := sign_sq (dot x a)
      have hcomm : (sign (q a) * sign (dot x a)) * (sign (q (xorVec a u)) * (sign (dot x a) * sign (dot x u))) =
          (sign (dot x a) * sign (dot x a)) * (sign (dot x u) * (sign (q (xorVec a u)) * sign (q a))) := by
        cases q a <;> cases dot x a <;> cases q (xorVec a u) <;> cases dot x u <;> rfl
      rw [hcomm, hsq, Int.one_mul]
    rw [sumVecs_congr hshift, sumVecs_swap]
    apply sumVecs_congr; intro u
    rw [sumVecs_mul_left]
  rw [h1, ← sumVecs_mul_left]
  apply sumVecs_congr; intro u
  by_cases hrad : isRad q u = true
  · simp only [hrad, ↓reduceIte]
    have hconst := (isRad_true_iff q u).mp hrad
    rw [sumVecs_congr (fun a => by rw [hconst a]), sumVecs_const,
        Int.mul_left_comm (sign (dot x u)) ((2 : Int) ^ k), ← sign_xor]
  · have hradf : isRad q u = false := by cases h : isRad q u <;> simp_all
    simp only [hradf, Bool.false_eq_true, ↓reduceIte, Int.mul_zero]
    have hex : ∃ a0 : Vec k, xor (q (xorVec a0 u)) (q a0) ≠ xor (q u) (q zeroVec) := by
      apply Classical.byContradiction; intro hall
      apply hrad; rw [isRad_true_iff]; intro a
      apply Classical.byContradiction; intro hne; exact hall ⟨a, hne⟩
    obtain ⟨a0, ha0⟩ := hex
    have hflip : ∀ a : Vec k,
        sign (xor (q (xorVec (xorVec a a0) u)) (q (xorVec a a0))) =
        -sign (xor (q (xorVec a u)) (q a)) := by
      intro a
      have hq3 := hq a a0 u
      have hne : xor (xor (q (xorVec a0 u)) (q a0)) (xor (q u) (q zeroVec)) = true := by
        cases h1 : xor (q (xorVec a0 u)) (q a0) <;> cases h2 : xor (q u) (q zeroVec) <;> simp_all
      rw [xor_group8] at hq3
      have heq := xor_pair_eq _ _ _ _ hq3
      rw [hne] at heq
      have hnot : xor (q (xorVec (xorVec a a0) u)) (q (xorVec a a0)) = !(xor (q (xorVec a u)) (q a)) := by
        generalize xor (q (xorVec (xorVec a a0) u)) (q (xorVec a a0)) = A at heq ⊢
        generalize xor (q (xorVec a u)) (q a) = B at heq ⊢
        cases A <;> cases B <;> simp_all
      rw [hnot, sign_not]
    have hsh := sumVecs_xor_shift a0 (fun a => sign (xor (q (xorVec a u)) (q a)))
    rw [sumVecs_congr hflip] at hsh
    have hneg : sumVecs (fun a => -sign (xor (q (xorVec a u)) (q a))) =
        -sumVecs (fun a => sign (xor (q (xorVec a u)) (q a))) := by
      have := sumVecs_mul_left (-1) (fun a => sign (xor (q (xorVec a u)) (q a)))
      simp only [Int.neg_mul, Int.one_mul] at this; exact this
    rw [hneg] at hsh
    have hz : sumVecs (fun a => sign (xor (q (xorVec a u)) (q a))) = 0 := by omega
    rw [hz, Int.mul_zero]

/-- Dichotomy for quadratic Walsh spectra: `W_q(x)^2 ∈ {0, 2^k * |Rad(q)|}`. -/
private theorem walshBool_sq_quadratic_dichotomy {k : Nat} (q : Vec k → Bool)
    (hq : isQuadratic q) (x : Vec k) :
    walshBool q x = 0 ∨ walshBool q x * walshBool q x = (2 : Int) ^ k * radSize q := by
  let h : Vec k → Bool := fun u => xor (dot x u) (xor (q u) (q zeroVec))
  by_cases hall : ∀ u : Vec k, isRad q u = true → h u = false
  · right
    rw [walshBool_sq_quadratic q hq x]
    congr 1
    unfold radSize
    apply sumVecs_congr; intro u
    cases hu : isRad q u
    · rfl
    · simp only [↓reduceIte]
      have hhu : xor (dot x u) (xor (q u) (q zeroVec)) = false := hall u hu
      rw [hhu]; rfl
  · left
    have hex : ∃ u0 : Vec k, isRad q u0 = true ∧ h u0 = true := by
      apply Classical.byContradiction; intro hno
      apply hall; intro u hu
      cases hhu : h u
      · rfl
      · exact False.elim (hno ⟨u, hu, hhu⟩)
    obtain ⟨u0, hu0, hhu0⟩ := hex
    have hlin : ∀ u : Vec k, isRad q u = true → h (xorVec u u0) = !(h u) := by
      intro u hu
      have hru0 := (isRad_true_iff q u0).mp hu0 u
      dsimp only [h] at hhu0 ⊢
      rw [dot_xor_right]
      generalize dot x u = d1; generalize dot x u0 = d2 at hhu0 ⊢
      generalize q (xorVec u u0) = q1 at hru0 ⊢
      generalize q u = q2 at hru0 ⊢
      generalize q u0 = q3 at hru0 hhu0 ⊢
      generalize q zeroVec = q0 at hru0 hhu0 ⊢
      cases d1 <;> cases d2 <;> cases q1 <;> cases q2 <;> cases q3 <;> cases q0 <;> simp_all
    have hrad_shift : ∀ u : Vec k, isRad q (xorVec u u0) = isRad q u := by
      intro u
      cases hu : isRad q u
      · cases hu' : isRad q (xorVec u u0)
        · rfl
        · have hback := isRad_xor (xorVec u u0) u0 hu' hu0
          rw [xorVec_assoc, xorVec_self, xorVec_zero_right] at hback
          rw [hu] at hback; cases hback
      · exact isRad_xor u u0 hu hu0
    have hsh := sumVecs_xor_shift u0 (fun u => if isRad q u then sign (h u) else 0)
    have hflip : ∀ u : Vec k,
        (if isRad q (xorVec u u0) then sign (h (xorVec u u0)) else 0) =
        -(if isRad q u then sign (h u) else 0) := by
      intro u
      rw [hrad_shift u]
      cases hu : isRad q u
      · simp
      · simp only [↓reduceIte, hlin u hu, sign_not]
    rw [sumVecs_congr hflip] at hsh
    have hneg : sumVecs (fun u => -(if isRad q u then sign (h u) else 0)) =
        -sumVecs (fun u => if isRad q u then sign (h u) else 0) := by
      have := sumVecs_mul_left (-1) (fun u => if isRad q u then sign (h u) else 0)
      simp only [Int.neg_mul, Int.one_mul] at this; exact this
    rw [hneg] at hsh
    have hsumz : sumVecs (fun u => if isRad q u then sign (h u) else 0) = 0 := by omega
    have hsq := walshBool_sq_quadratic q hq x
    rw [hsumz, Int.mul_zero] at hsq
    cases Int.mul_eq_zero.mp hsq with
    | inl h0 => exact h0
    | inr h0 => exact h0

/-- For a quadratic function `q` on `2m - 1` variables (`m ≥ 1`), its radical size is
    `2^(2m - 1 - 2r)` for some rank `r ≤ m - 1`, and every Walsh value has
    `W_q(x) ∈ {0, ± 2^(2m - 1 - r)}`. -/
private theorem quadratic_odd_dim_spectrum {m : Nat} (hm : 1 ≤ m)
    (q : Vec (2 * m - 1) → Bool) (hq : isQuadratic q) :
    ∃ r : Nat, r ≤ m - 1 ∧
      radSize q = (2 : Int) ^ (2 * m - 1 - 2 * r) ∧
      (∀ x, walshBool q x = 0 ∨
            walshBool q x = (2 : Int) ^ (2 * m - 1 - r) ∨
            walshBool q x = -(2 : Int) ^ (2 * m - 1 - r)) ∧
      sumVecs (fun x => if walshBool q x = 0 then (0 : Int) else (2 : Int) ^ (2 * m - 1 - r)) =
        (2 : Int) ^ (2 * m - 1 + r) := by
  obtain ⟨d, hdk, hd_eq⟩ := subspace_size_pow2 (isRad q) (isRad_zero q) (fun u v hu hv => isRad_xor u v hu hv)
  have hrad_eq : radSize q = (2 : Int) ^ d := hd_eq
  -- Show there exists some x with W_q(x) ≠ 0 (by Parseval).
  have hex_nz : ∃ x : Vec (2 * m - 1), walshBool q x ≠ 0 := by
    apply Classical.byContradiction; intro hall
    have hz : ∀ x, walshBool q x * walshBool q x = 0 := by
      intro x; have : walshBool q x = 0 := Classical.byContradiction (fun h => hall ⟨x, h⟩)
      rw [this]; rfl
    have hp := walshBool_parseval q
    rw [sumVecs_congr hz, sumVecs_const, Int.mul_zero] at hp
    have hpos := two_pow_pos (2 * (2 * m - 1))
    omega
  obtain ⟨x0, hx0⟩ := hex_nz
  have hsq0 : walshBool q x0 * walshBool q x0 = (2 : Int) ^ ((2 * m - 1) + d) := by
    cases walshBool_sq_quadratic_dichotomy q hq x0 with
    | inl hz => exact False.elim (hx0 hz)
    | inr hsq => rw [hsq, hrad_eq, ← int_pow_add]
  have heven : ((2 * m - 1) + d) % 2 = 0 := by
    by_cases hpar : ((2 * m - 1) + d) % 2 = 0
    · exact hpar
    · let s := ((2 * m - 1) + d) / 2
      have hodd : (2 * m - 1) + d = 2 * s + 1 := by omega
      rw [hodd] at hsq0
      exact False.elim (int_sq_ne_odd_two_pow (walshBool q x0) s hsq0)
  let r : Nat := ((2 * m - 1) - d) / 2
  have hr_le : r ≤ m - 1 := by omega
  have hd_val : d = 2 * m - 1 - 2 * r := by omega
  have hpow_half : (2 * m - 1) + d = (2 * m - 1 - r) + (2 * m - 1 - r) := by omega
  have hvals : ∀ x, walshBool q x = 0 ∨
      walshBool q x = (2 : Int) ^ (2 * m - 1 - r) ∨
      walshBool q x = -(2 : Int) ^ (2 * m - 1 - r) := by
    intro x
    cases walshBool_sq_quadratic_dichotomy q hq x with
    | inl hz => exact Or.inl hz
    | inr hsq =>
      rw [hrad_eq, ← int_pow_add, hpow_half, int_pow_add] at hsq
      cases int_sq_eq_iff hsq with
      | inl hp => exact Or.inr (Or.inl hp)
      | inr hn => exact Or.inr (Or.inr hn)
  -- Compute L1 sum via Parseval: M * ∑_{W ≠ 0} M = ∑ W^2 = 2^(4m - 2).
  let M : Int := (2 : Int) ^ (2 * m - 1 - r)
  have hM_pos : 0 < M := two_pow_pos (2 * m - 1 - r)
  have hmul : M * sumVecs (fun x => if walshBool q x = 0 then (0 : Int) else M) =
      (2 : Int) ^ (2 * (2 * m - 1)) := by
    rw [← sumVecs_mul_left, ← walshBool_parseval q]
    apply sumVecs_congr; intro x
    rcases hvals x with h0 | hp | hn
    · simp [h0]
    · have hne : walshBool q x ≠ 0 := by rw [hp]; exact Int.ne_of_gt hM_pos
      rw [if_neg hne, hp]
    · have hne : walshBool q x ≠ 0 := by rw [hn]; omega
      rw [if_neg hne, hn, Int.neg_mul, Int.mul_neg, Int.neg_neg]
  have hL1 : sumVecs (fun x => if walshBool q x = 0 then (0 : Int) else M) =
      (2 : Int) ^ (2 * m - 1 + r) := by
    have hpow : (2 : Int) ^ (2 * (2 * m - 1)) = M * (2 : Int) ^ (2 * m - 1 + r) := by
      dsimp only [M]; rw [← int_pow_add]; congr 1; omega
    rw [hpow] at hmul
    exact Int.eq_of_mul_eq_mul_left (Int.ne_of_gt hM_pos) hmul
  exact ⟨r, hr_le, by rw [hrad_eq, hd_val], hvals, hL1⟩

/-- If `Q : Vec (k + 1) → Bool` is quadratic, its two hyperplane slices `Q_0, Q_1`
    are quadratic and share the exact same radical. -/
private theorem slice_quad_same_rad {k : Nat} (Q : Vec (k + 1) → Bool) (hQ : isQuadratic Q) :
    isQuadratic (fun a' => Q (consVec false a')) ∧
    isQuadratic (fun a' => Q (consVec true a')) ∧
    ∀ u : Vec k, isRad (fun a' => Q (consVec false a')) u = isRad (fun a' => Q (consVec true a')) u := by
  have hQ0 : isQuadratic (fun a' => Q (consVec false a')) := by
    intro a b c
    have h := hQ (consVec false a) (consVec false b) (consVec false c)
    simpa only [xorVec_cons, Bool.xor_false, zeroVec_cons] using h
  have hdiff : ∀ a b : Vec k,
      xor (xor (Q (consVec true (xorVec a b))) (Q (consVec false (xorVec a b))))
          (xor (Q (consVec true a)) (Q (consVec false a))) =
      xor (xor (Q (consVec true b)) (Q (consVec false b)))
          (xor (Q (consVec true zeroVec)) (Q (consVec false zeroVec))) := by
    intro a b
    have h := hQ (consVec true zeroVec) (consVec false a) (consVec false b)
    simp only [xorVec_cons, Bool.xor_false, Bool.false_xor, xorVec_zero_left, zeroVec_cons] at h
    have hstep :
        xor (xor (xor (Q (consVec true (xorVec a b))) (Q (consVec false (xorVec a b))))
                 (xor (Q (consVec true a)) (Q (consVec false a))))
            (xor (xor (Q (consVec true b)) (Q (consVec false b)))
                 (xor (Q (consVec true zeroVec)) (Q (consVec false zeroVec)))) = false := by
      have hperm : ∀ t1 t2 t3 t4 t5 t6 t7 t8 : Bool,
          xor (xor (xor t1 t2) (xor t3 t4)) (xor (xor t5 t6) (xor t7 t8)) =
          xor (xor (xor t1 t3) (xor t5 t2)) (xor (xor t7 t4) (xor t6 t8)) := by
        intro t1 t2 t3 t4 t5 t6 t7 t8
        rw [xor_sw t1 t2 t3 t4, xor_sw t5 t6 t7 t8,
            xor_group8 (xor t1 t3) t2 t4 t5 t7 (xor t6 t8),
            Bool.xor_comm t2 t5, Bool.xor_comm t4 t7]
      rw [hperm]; exact h
    exact xor_pair_eq _ _ _ _ hstep
  have hQ1 : isQuadratic (fun a' => Q (consVec true a')) := by
    let D : Vec k → Bool := fun a' => xor (Q (consVec true a')) (Q (consVec false a'))
    have hD_lin : isQuadratic D := by
      intro x y z
      have d1 := hdiff (xorVec x y) z
      have d2 := hdiff x y
      have d3 := hdiff x z
      have d4 := hdiff y z
      change xor (D (xorVec (xorVec x y) z)) (D (xorVec x y)) = xor (D z) (D zeroVec) at d1
      change xor (D (xorVec x y)) (D x) = xor (D y) (D zeroVec) at d2
      change xor (D (xorVec x z)) (D x) = xor (D z) (D zeroVec) at d3
      change xor (D (xorVec y z)) (D y) = xor (D z) (D zeroVec) at d4
      rw [d1, xor_group8, d4, d3, Bool.xor_self]
    have heq : (fun a' => Q (consVec true a')) = (fun a' => xor (Q (consVec false a')) (D a')) := by
      funext a'; dsimp only [D]
      cases Q (consVec true a') <;> cases Q (consVec false a') <;> rfl
    rw [heq]
    exact isQuadratic_xor hQ0 hD_lin
  refine ⟨hQ0, hQ1, fun u => ?_⟩
  apply Bool.eq_iff_iff.mpr
  rw [isRad_true_iff, isRad_true_iff]
  have hiff : ∀ a : Vec k,
      xor (Q (consVec true (xorVec a u))) (Q (consVec true a)) =
        xor (Q (consVec true u)) (Q (consVec true zeroVec)) ↔
      xor (Q (consVec false (xorVec a u))) (Q (consVec false a)) =
        xor (Q (consVec false u)) (Q (consVec false zeroVec)) := by
    intro a
    have hd : xor (xor (Q (consVec true (xorVec a u))) (Q (consVec true a)))
                  (xor (Q (consVec false (xorVec a u))) (Q (consVec false a))) =
              xor (xor (Q (consVec true u)) (Q (consVec true zeroVec)))
                  (xor (Q (consVec false u)) (Q (consVec false zeroVec))) := by
      have h1 := hdiff a u
      rw [xor_sw (Q (consVec true (xorVec a u))) (Q (consVec false (xorVec a u))),
          xor_sw (Q (consVec true u)) (Q (consVec false u))] at h1
      exact h1
    have hcancel : ∀ A B C D : Bool, xor A B = xor C D → (A = C ↔ B = D) := by
      intro A B C D h; cases A <;> cases B <;> cases C <;> cases D <;> simp_all
    exact hcancel _ _ _ _ hd
  exact ⟨fun h a => (hiff a).mpr (h a), fun h a => (hiff a).mp (h a)⟩

/-! ## Section 5: Hyperplane Normalization #1 & `H_0` / `H_1` Energy Inequalities -/

private theorem two_mul_sq_eq (B : Int) : 2 * B * (2 * B) = 4 * (B * B) := by
  have h1 : 2 * B * (2 * B) = (2 * 2) * (B * B) := by
    rw [Int.mul_assoc, Int.mul_left_comm B 2 B, ← Int.mul_assoc]
  rw [h1]; rfl

private theorem bool_xor_solve (p q r : Bool) (h : xor p q = r) : p = xor r q := by
  cases p <;> cases q <;> cases r <;> simp_all

/-- If `F` is balanced on `2k + 2` variables (`k ≥ 4`) with `|W_F| ≤ 2^(k+1) + 4`,
    then `supportXor F ≠ 0` (otherwise `8 ∣ W_F` everywhere violates Parseval). -/
private theorem supportXor_ne_zero {k : Nat} (hk : 3 ≤ k)
    (F : Vec (2 * k + 2) → Bool) (hbal : isBalanced (2 * k + 2) F)
    (hcap : ∀ a, -((2 : Int) ^ (k + 1) + 4) ≤ walshBool F a ∧
                 walshBool F a ≤ (2 : Int) ^ (k + 1) + 4) :
    supportXor F ≠ zeroVec := by
  intro hv0
  let B : Int := (2 : Int) ^ k
  have hB_pos : 0 < B := two_pow_pos k
  have hB8 : (8 : Int) ∣ 2 * B := by
    have h2 : (2 : Int) ^ (k + 1) = 2 * B := by rw [Int.pow_succ, Int.mul_comm]
    rw [← h2]; exact two_pow_dvd_of_le (a := 3) (b := k + 1) (by omega)
  have hle2B : ∀ a : Vec (2 * k + 2), walshBool F a * walshBool F a ≤ 4 * (B * B) := by
    intro a
    have hmod := walshBool_mod8 (by omega) F hbal a
    rw [hv0, dot_zero_left] at hmod
    simp only [Bool.false_eq_true, ↓reduceIte] at hmod
    have hc := hcap a
    have h2B : (2 : Int) ^ (k + 1) = 2 * B := by rw [Int.pow_succ, Int.mul_comm]
    rw [h2B] at hc
    obtain ⟨q, hq⟩ := hB8
    have hlo : -(2 * B) ≤ walshBool F a := by omega
    have hhi : walshBool F a ≤ 2 * B := by omega
    have hsq := sq_le_of_abs_le hlo hhi
    rw [two_mul_sq_eq B] at hsq
    exact hsq
  have h0 : walshBool F zeroVec = 0 := walshBool_zero_of_balanced F hbal
  have hbound : sumVecs (fun a => walshBool F a * walshBool F a) ≤
      sumVecs (fun a : Vec (2 * k + 2) => if isZeroVec a then (0 : Int) else 4 * (B * B)) := by
    apply sumVecs_mono; intro a
    by_cases ha : isZeroVec a = true
    · simp only [ha, ↓reduceIte]
      have hz := (isZeroVec_true_iff a).mp ha
      rw [hz, h0]; decide
    · simp only [ha, ↓reduceIte]
      exact hle2B a
  have hrhs : sumVecs (fun a : Vec (2 * k + 2) => if isZeroVec a then (0 : Int) else 4 * (B * B)) =
      ((2 : Int) ^ (2 * k + 2) - 1) * (4 * (B * B)) := by
    have hpw : ∀ a : Vec (2 * k + 2),
        (if isZeroVec a then (0 : Int) else 4 * (B * B)) =
        4 * (B * B) - (if isZeroVec a then 4 * (B * B) else 0) := by
      intro a; cases isZeroVec a <;> simp
    rw [sumVecs_congr hpw, sumVecs_sub, sumVecs_const, sumVecs_delta_zero, Int.sub_mul, Int.one_mul]
  rw [walshBool_parseval, hrhs] at hbound
  have hN : (2 : Int) ^ (2 * k + 2) = 4 * (B * B) := by
    have : 2 * k + 2 = (k + k) + 2 := by omega
    rw [this, int_pow_add, int_pow_add, Int.mul_comm _ ((2 : Int) ^ 2)]
    rfl
  have hN2 : (2 : Int) ^ (2 * (2 * k + 2)) = (2 : Int) ^ (2 * k + 2) * (4 * (B * B)) := by
    have : 2 * (2 * k + 2) = (2 * k + 2) + (2 * k + 2) := by omega
    rw [this, int_pow_add, ← hN]
  rw [hN2] at hbound
  have hpos : 0 < 4 * (B * B) := by
    have := Int.mul_pos hB_pos hB_pos; omega
  rw [Int.sub_mul, Int.one_mul] at hbound
  omega

/-- Normalization #1: any balanced `F` on `2k + 2` variables (`k ≥ 4`) with `|W_F| ≤ 2B + 4`
    can be linearly transformed (preserving balance and the Walsh spectrum multiset) to `G`
    whose `supportXor` satisfies `a · supportXor G = a_0`. -/
private theorem normalize_supportXor {k : Nat} (hk : 3 ≤ k)
    (F : Vec (2 * k + 2) → Bool) (hbal : isBalanced (2 * k + 2) F)
    (hcap : ∀ a, -((2 : Int) ^ (k + 1) + 4) ≤ walshBool F a ∧
                 walshBool F a ≤ (2 : Int) ^ (k + 1) + 4) :
    ∃ G : Vec (2 * k + 2) → Bool,
      isBalanced (2 * k + 2) G ∧
      (∀ a, -((2 : Int) ^ (k + 1) + 4) ≤ walshBool G a ∧
            walshBool G a ≤ (2 : Int) ^ (k + 1) + 4) ∧
      (∀ (b : Bool) (a' : Vec (2 * k + 1)),
        dot (supportXor G) (consVec b a') = b) := by
  have hvne := supportXor_ne_zero hk F hbal hcap
  have hex : ∃ p : Fin (2 * k + 2), supportXor F p = true := by
    apply Classical.byContradiction; intro hno
    apply hvne; funext i
    cases hi : supportXor F i
    · rfl
    · exact False.elim (hno ⟨i, hi⟩)
  obtain ⟨p, hp⟩ := hex
  let s : Vec (2 * k + 2) := swap0 p (supportXor F)
  have hs0 : s ⟨0, Nat.zero_lt_succ _⟩ = true := by
    dsimp only [s]; unfold swap0; simp only [↓reduceIte]; exact hp
  let F1 : Vec (2 * k + 2) → Bool := fun x => F (swap0 p x)
  let G : Vec (2 * k + 2) → Bool := fun x => F1 (shearT s x)
  have hWG : ∀ a : Vec (2 * k + 2), walshBool G a = walshBool F (swap0 p (shear s a)) := by
    intro a
    unfold walshBool
    change walsh (fun x => sign (F1 (shearT s x))) a = walsh (fun x => sign (F x)) (swap0 p (shear s a))
    rw [walsh_shearT s hs0 (fun x => sign (F1 x)) a]
    exact walsh_swap0 p (fun x => sign (F x)) (shear s a)
  have hGbal : isBalanced (2 * k + 2) G := by
    unfold isBalanced hammingWeight at hbal ⊢
    have h1 := sumVecs_shearT s (fun y => if F1 y then (1 : Int) else 0)
    have h2 := sumVecs_swap0 p (fun y => if F y then (1 : Int) else 0)
    change 2 * sumVecs (fun x => if F1 (shearT s x) then (1 : Int) else 0) = _
    rw [h1]
    change 2 * sumVecs (fun x => if F (swap0 p x) then (1 : Int) else 0) = _
    rw [h2]; exact hbal
  have hGcap : ∀ a, -((2 : Int) ^ (k + 1) + 4) ≤ walshBool G a ∧
                    walshBool G a ≤ (2 : Int) ^ (k + 1) + 4 := by
    intro a; rw [hWG a]; exact hcap _
  refine ⟨G, hGbal, hGcap, fun b a' => ?_⟩
  have hmodG := walshBool_mod8 (by omega) G hGbal (consVec b a')
  have hmodF := walshBool_mod8 (by omega) F hbal (swap0 p (shear s (consVec b a')))
  rw [hWG] at hmodG
  have hdotF : dot (supportXor F) (swap0 p (shear s (consVec b a'))) = b := by
    rw [← swap0_dot p (supportXor F) (swap0 p (shear s (consVec b a'))), swap0_invol]
    rw [dot_comm]
    exact shear_dot_s s hs0 b a'
  rw [hdotF] at hmodF
  have heq : (if dot (supportXor G) (consVec b a') then (4 : Int) else 0) = (if b then 4 else 0) :=
    hmodG.symm.trans hmodF
  cases hb : b <;> rw [hb] at heq <;>
    cases hd : dot (supportXor G) (consVec _ a') <;> simp [hd] at heq ⊢

/-- Core structural relations for a normalized balanced function `F` (`dot (supportXor F) (b, a') = b`)
    on `2k + 2` variables (`k ≥ 4`). Extracts the integer `t ≥ 1` and proves both:
    - `H_0` defect bound: `8 * (B - 2) * wt(Q_0) ≤ B^2 * (4 * t - 1)`
    - `H_1` Plancherel bound: `L ≥ 2 * B^2 * (2 + t)` (plus pointwise nonnegative gap). -/
private theorem normalized_H0_H1_bounds {k : Nat} (hk : 3 ≤ k)
    (F : Vec (2 * k + 2) → Bool) (hbal : isBalanced (2 * k + 2) F)
    (hcap : ∀ a, -((2 : Int) ^ (k + 1) + 4) ≤ walshBool F a ∧
                 walshBool F a ≤ (2 : Int) ^ (k + 1) + 4)
    (hnorm : ∀ (b : Bool) (a' : Vec (2 * k + 1)), dot (supportXor F) (consVec b a') = b) :
    let B : Int := (2 : Int) ^ k
    let D : Vec (2 * k + 1) → Int := fun x' =>
      if F (consVec false x') == F (consVec true x') then 0 else sign (F (consVec false x'))
    let Q0 : Vec (2 * k + 1) → Bool := fun a' => quadMod2 F (consVec false a')
    let Q1 : Vec (2 * k + 1) → Bool := fun a' => quadMod2 F (consVec true a')
    let L : Int := sumVecs (fun a' => walshBool F (consVec true a') * sign (Q1 a'))
    ∃ t : Int,
      1 ≤ t ∧
      sumVecs (fun x' => D x' * D x') = B * B + 2 * t ∧
      8 * (B - 2) * hammingWeight Q0 ≤ B * B * (4 * t - 1) ∧
      2 * B * B * (2 + t) ≤ L ∧
      L = 2 * sumVecs (fun x' => D x' * walshBool Q1 x') ∧
      (L = 2 * B * B * (2 + t) →
        ∀ a' : Vec (2 * k + 1),
          walshBool F (consVec true a') * sign (Q1 a') = 2 * B + 4 ∨
          walshBool F (consVec true a') * sign (Q1 a') = -(2 * B - 4)) := by
  intro B D Q0 Q1 L
  let S : Vec (2 * k + 1) → Int := fun x' =>
    if F (consVec false x') == F (consVec true x') then sign (F (consVec false x')) else 0
  have hB_pos : 0 < B := two_pow_pos k
  have hB8 : 8 ≤ B := by
    have : (8 : Int) = (2 : Int) ^ 3 := rfl
    rw [this]; exact two_pow_le_of_le hk
  have hB_dvd8 : (8 : Int) ∣ B := by
    have : (8 : Int) = (2 : Int) ^ 3 := rfl
    rw [this]; exact two_pow_dvd_of_le (by omega)
  have hpow2k : (2 : Int) ^ (2 * k) = B * B := by
    have : 2 * k = k + k := by omega
    rw [this, int_pow_add]
  have hpow2k1 : (2 : Int) ^ (2 * k + 1) = 2 * (B * B) := by
    rw [Int.pow_succ, hpow2k, Int.mul_comm]
  have hpow2k2 : (2 : Int) ^ (2 * k + 2) = 4 * (B * B) := by
    rw [Int.pow_succ, hpow2k1]; omega
  -- Relate W_F(0, a') = 2 * W_S(a') and W_F(1, a') = 2 * W_D(a').
  have hW0 : ∀ a' : Vec (2 * k + 1), walshBool F (consVec false a') = 2 * walsh S a' := by
    intro a'
    unfold walshBool
    rw [walsh_cons]
    simp only [sign, Bool.false_eq_true, ↓reduceIte, Int.one_mul]
    unfold walsh
    rw [← sumVecs_add, ← sumVecs_mul_left]
    apply sumVecs_congr; intro x'
    dsimp only [S]
    cases F (consVec false x') <;> cases F (consVec true x') <;> cases dot a' x' <;> rfl
  have hW1 : ∀ a' : Vec (2 * k + 1), walshBool F (consVec true a') = 2 * walsh D a' := by
    intro a'
    unfold walshBool
    rw [walsh_cons]
    simp only [sign, ↓reduceIte, Int.neg_mul, Int.one_mul]
    unfold walsh
    have hadd : sumVecs (fun x' => sign (F (consVec false x')) * sign (dot a' x')) +
                -sumVecs (fun x' => sign (F (consVec true x')) * sign (dot a' x')) =
        sumVecs (fun x' => sign (F (consVec false x')) * sign (dot a' x') -
                           sign (F (consVec true x')) * sign (dot a' x')) := by
      rw [sumVecs_sub]; omega
    change sumVecs (fun x' => sign (F (consVec false x')) * sign (dot a' x')) +
           -sumVecs (fun x' => sign (F (consVec true x')) * sign (dot a' x')) = _
    rw [hadd, ← sumVecs_mul_left]
    apply sumVecs_congr; intro x'
    dsimp only [D]
    cases F (consVec false x') <;> cases F (consVec true x') <;> cases dot a' x' <;> rfl
  -- Show d_H = ∑ D^2 is even, so d_H = B^2 + 2t and s_H = ∑ S^2 = B^2 - 2t.
  let dH : Int := sumVecs (fun x' => D x' * D x')
  let sH : Int := sumVecs (fun x' => S x' * S x')
  have hSD_sum : sH + dH = 2 * (B * B) := by
    dsimp only [sH, dH]; rw [← sumVecs_add]
    have h1 : ∀ x' : Vec (2 * k + 1), S x' * S x' + D x' * D x' = 1 := by
      intro x'; dsimp only [S, D]
      cases F (consVec false x') <;> cases F (consVec true x') <;> rfl
    rw [sumVecs_congr h1, sumVecs_const, Int.mul_one, hpow2k1]
  have hdH_even : (2 : Int) ∣ dH := by
    have hpw : ∀ x' : Vec (2 * k + 1),
        D x' * D x' =
          (if F (consVec false x') then 1 else 0) + (if F (consVec true x') then 1 else 0) -
          2 * (if F (consVec false x') && F (consVec true x') then 1 else 0) := by
      intro x'; dsimp only [D]
      cases F (consVec false x') <;> cases F (consVec true x') <;> rfl
    have hFsplit : hammingWeight F =
        sumVecs (fun x' => if F (consVec false x') then (1 : Int) else 0) +
        sumVecs (fun x' => if F (consVec true x') then (1 : Int) else 0) := rfl
    have heq : dH = hammingWeight F - 2 * sumVecs (fun x' => if F (consVec false x') && F (consVec true x') then (1 : Int) else 0) := by
      dsimp only [dH]
      rw [sumVecs_congr hpw, sumVecs_sub, sumVecs_add, sumVecs_mul_left, hFsplit]
    unfold isBalanced at hbal
    rw [hpow2k2] at hbal
    exact ⟨B * B - sumVecs (fun x' => if F (consVec false x') && F (consVec true x') then (1 : Int) else 0), by omega⟩
  have hBsq_even : (2 : Int) ∣ B * B := by
    obtain ⟨b, hb⟩ := hB_dvd8
    refine ⟨4 * b * B, ?_⟩
    conv => lhs; arg 1; rw [hb]
    rw [show (8 * b : Int) = 2 * (4 * b) by omega, Int.mul_assoc]
  obtain ⟨qd, hqd⟩ := hdH_even
  obtain ⟨qb, hqb⟩ := hBsq_even
  let t : Int := qd - qb
  have hdH_eq : dH = B * B + 2 * t := by dsimp only [t]; omega
  have hsH_eq : sH = B * B - 2 * t := by omega
  -- Parseval on H_0 and H_1:
  have h42B : 4 * (2 * (B * B) * (B * B)) = 8 * (B * B) * (B * B) := by
    rw [← Int.mul_assoc 4 (2 * (B * B)), ← Int.mul_assoc 4 2 (B * B)]; rfl
  have h422t : 4 * (2 * (B * B) * (2 * t)) = 16 * (B * B) * t := by
    have h1 : 4 * (2 * (B * B) * (2 * t)) = (4 * 2 * 2) * (B * B) * t := by
      simp only [Int.mul_assoc, Int.mul_left_comm]
    rw [h1]; rfl
  have hE0 : sumVecs (fun a' => walshBool F (consVec false a') * walshBool F (consVec false a')) =
      8 * (B * B) * (B * B) - 16 * (B * B) * t := by
    have hsq : ∀ a' : Vec (2 * k + 1),
        walshBool F (consVec false a') * walshBool F (consVec false a') = 4 * (walsh S a' * walsh S a') := by
      intro a'; rw [hW0 a']; exact two_mul_sq_eq (walsh S a')
    rw [sumVecs_congr hsq, sumVecs_mul_left, walsh_parseval, hpow2k1]
    change 4 * (2 * (B * B) * sH) = _
    rw [hsH_eq, Int.mul_sub, Int.mul_sub, h42B, h422t]
  have hE1 : sumVecs (fun a' => walshBool F (consVec true a') * walshBool F (consVec true a')) =
      8 * (B * B) * (B * B) + 16 * (B * B) * t := by
    have hsq : ∀ a' : Vec (2 * k + 1),
        walshBool F (consVec true a') * walshBool F (consVec true a') = 4 * (walsh D a' * walsh D a') := by
      intro a'; rw [hW1 a']; exact two_mul_sq_eq (walsh D a')
    rw [sumVecs_congr hsq, sumVecs_mul_left, walsh_parseval, hpow2k1]
    change 4 * (2 * (B * B) * dH) = _
    rw [hdH_eq, Int.mul_add, Int.mul_add, h42B, h422t]
  -- H_0 defect bound:
  have h2B_pow : (2 : Int) ^ (k + 1) = 2 * B := by rw [Int.pow_succ, Int.mul_comm]
  have hQ0_zero : Q0 zeroVec = false := by
    dsimp only [Q0]; rw [← zeroVec_cons]; unfold quadMod2 suppDotCount
    have hz : sumVecs (fun x : Vec (2 * k + 2) => if F x && dot zeroVec x then (1 : Int) else 0) = 0 := by
      have : ∀ x, (if F x && dot zeroVec x then (1 : Int) else 0) = 0 := by
        intro x; rw [dot_zero_left, Bool.and_false]; rfl
      rw [sumVecs_congr this, sumVecs_const, Int.mul_zero]
    rw [hz]; rfl
  have hH0_pw : ∀ a' : Vec (2 * k + 1),
      walshBool F (consVec false a') * walshBool F (consVec false a') ≤
        4 * (B * B) - (if isZeroVec a' then 4 * (B * B) else 0) -
        (if Q0 a' then 32 * (B - 2) else 0) := by
    intro a'
    by_cases ha0 : isZeroVec a' = true
    · have hz := (isZeroVec_true_iff a').mp ha0
      subst hz
      simp only [ha0, hQ0_zero, ↓reduceIte, Bool.false_eq_true, Int.sub_zero]
      rw [← zeroVec_cons, walshBool_zero_of_balanced F hbal]; omega
    · simp only [ha0, ↓reduceIte, Int.sub_zero]
      have hmod16 := walshBool_mod16_quad (by omega) F hbal (consVec false a')
      rw [hnorm false a'] at hmod16
      simp only [Bool.false_eq_true, ↓reduceIte, Int.zero_add] at hmod16
      have hc := hcap (consVec false a')
      rw [h2B_pow] at hc
      obtain ⟨b8, hb8⟩ := hB_dvd8
      cases hq : Q0 a'
      · simp only [Bool.false_eq_true, ↓reduceIte, Int.sub_zero]
        dsimp only [Q0] at hq; rw [hq] at hmod16
        simp only [Bool.false_eq_true, ↓reduceIte] at hmod16
        have hlo : -(2 * B) ≤ walshBool F (consVec false a') := by omega
        have hhi : walshBool F (consVec false a') ≤ 2 * B := by omega
        have hsq := sq_le_of_abs_le hlo hhi
        rw [two_mul_sq_eq B] at hsq
        exact hsq
      · simp only [↓reduceIte]
        dsimp only [Q0] at hq; rw [hq] at hmod16
        simp only [↓reduceIte] at hmod16
        have hlo : -(2 * B - 8) ≤ walshBool F (consVec false a') := by omega
        have hhi : walshBool F (consVec false a') ≤ 2 * B - 8 := by omega
        have hsq := sq_le_of_abs_le hlo hhi
        have hexp : (2 * B - 8) * (2 * B - 8) = 4 * (B * B) - 32 * (B - 2) := by
          simp only [Int.sub_mul, Int.mul_sub]
          rw [two_mul_sq_eq B]
          have h16 : 2 * B * 8 = 16 * B := by rw [Int.mul_comm _ 8, ← Int.mul_assoc]; rfl
          have h16' : 8 * (2 * B) = 16 * B := by rw [← Int.mul_assoc]; rfl
          rw [h16, h16']; omega
        rw [hexp] at hsq
        have hif : (if false = true then 4 * (B * B) else 0) = 0 := rfl
        rw [hif, Int.sub_zero]
        exact hsq
  have hH0_sum := sumVecs_mono hH0_pw
  rw [hE0, sumVecs_sub, sumVecs_sub, sumVecs_const, sumVecs_delta_zero, hpow2k1] at hH0_sum
  have hwtQ0_sum : sumVecs (fun a' : Vec (2 * k + 1) => if Q0 a' then 32 * (B - 2) else 0) =
      32 * (B - 2) * hammingWeight Q0 := by
    unfold hammingWeight; rw [← sumVecs_mul_left]
    apply sumVecs_congr; intro a'; cases Q0 a' <;> simp
  rw [hwtQ0_sum] at hH0_sum
  have h8B4 : 2 * (B * B) * (4 * (B * B)) = 8 * (B * B) * (B * B) := by
    have h1 : 2 * (B * B) * (4 * (B * B)) = (2 * 4) * (B * B) * (B * B) := by
      simp only [Int.mul_assoc, Int.mul_left_comm]
    rw [h1]; rfl
  rw [h8B4] at hH0_sum
  have hH0_bound : 8 * (B - 2) * hammingWeight Q0 ≤ B * B * (4 * t - 1) := by
    have hmul : 4 * (8 * (B - 2) * hammingWeight Q0) ≤ 4 * (B * B * (4 * t - 1)) := by
      have h1 : 4 * (8 * (B - 2) * hammingWeight Q0) = 32 * (B - 2) * hammingWeight Q0 := by
        have : 4 * (8 * (B - 2) * hammingWeight Q0) = (4 * 8) * (B - 2) * hammingWeight Q0 := by
          simp only [Int.mul_assoc]
        rw [this]; rfl
      have h2 : 4 * (B * B * (4 * t - 1)) = 16 * (B * B) * t - 4 * (B * B) := by
        rw [Int.mul_sub, Int.mul_one, Int.mul_sub]
        have : 4 * (B * B * (4 * t)) = (4 * 4) * (B * B) * t := by
          simp only [Int.mul_assoc, Int.mul_left_comm]
        rw [this]; rfl
      omega
    omega
  have hwtQ0_nn : 0 ≤ hammingWeight Q0 := sumVecs_nonneg (fun a' => by cases Q0 a' <;> decide)
  have ht_ge1 : 1 ≤ t := by
    have hnn : 0 ≤ 8 * (B - 2) * hammingWeight Q0 :=
      Int.mul_nonneg (by omega) hwtQ0_nn
    have hBsq_pos : 0 < B * B := Int.mul_pos hB_pos hB_pos
    have h4t : 0 ≤ B * B * (4 * t - 1) := by omega
    apply Classical.byContradiction; intro hlt
    have hneg : 4 * t - 1 < 0 := by omega
    have : B * B * (4 * t - 1) < 0 := by
      have h1 := Int.mul_pos hBsq_pos (show 0 < -(4 * t - 1) by omega)
      rw [Int.mul_neg] at h1; omega
    omega
  -- H_1 Plancherel identity & lower bound:
  have hL_adj : L = 2 * sumVecs (fun x' => D x' * walshBool Q1 x') := by
    dsimp only [L]
    rw [sumVecs_congr (fun a' => by rw [hW1 a', Int.mul_assoc]), sumVecs_mul_left]
    congr 1
    exact walsh_adjoint D (fun a' => sign (Q1 a'))
  let gap : Vec (2 * k + 1) → Int := fun a' =>
    let w := walshBool F (consVec true a')
    let s := w * sign (Q1 a')
    (2 * B + 4 - s) * (2 * B - 4 + s)
  have hgap_eq : ∀ a' : Vec (2 * k + 1),
      gap a' = 8 * (walshBool F (consVec true a') * sign (Q1 a')) -
               (walshBool F (consVec true a') * walshBool F (consVec true a') - 4 * (B * B)) - 16 := by
    intro a'
    dsimp only [gap]
    let w := walshBool F (consVec true a')
    let s := w * sign (Q1 a')
    have hss : s * s = w * w := by
      dsimp only [s]
      have h1 : (w * sign (Q1 a')) * (w * sign (Q1 a')) = (w * w) * (sign (Q1 a') * sign (Q1 a')) := by
        simp only [Int.mul_assoc, Int.mul_left_comm]
      rw [h1, sign_sq, Int.mul_one]
    have h4 : 2 * B * (2 * B) = 4 * (B * B) := two_mul_sq_eq B
    change (2 * B + 4 - s) * (2 * B - 4 + s) = 8 * s - (w * w - 4 * (B * B)) - 16
    simp only [Int.add_mul, Int.sub_mul, Int.mul_add, Int.mul_sub, Int.mul_comm s (2 * B), Int.mul_comm s 4]
    omega
  have hgap_nn : ∀ a' : Vec (2 * k + 1), 0 ≤ gap a' := by
    intro a'
    dsimp only [gap]
    have hmod16 := walshBool_mod16_quad (by omega) F hbal (consVec true a')
    rw [hnorm true a'] at hmod16
    simp only [↓reduceIte] at hmod16
    have hc := hcap (consVec true a')
    rw [h2B_pow] at hc
    obtain ⟨b8, hb8⟩ := hB_dvd8
    cases hq : Q1 a'
    · dsimp only [Q1] at hq; rw [hq] at hmod16
      simp only [Bool.false_eq_true, ↓reduceIte, Int.add_zero] at hmod16
      simp only [sign, Bool.false_eq_true, ↓reduceIte, Int.mul_one]
      have hlo : -(2 * B - 4) ≤ walshBool F (consVec true a') := by omega
      have hhi : walshBool F (consVec true a') ≤ 2 * B + 4 := by omega
      exact Int.mul_nonneg (by omega) (by omega)
    · dsimp only [Q1] at hq; rw [hq] at hmod16
      simp only [↓reduceIte] at hmod16
      simp only [sign, ↓reduceIte, Int.mul_neg, Int.mul_one]
      have hlo : -(2 * B + 4) ≤ walshBool F (consVec true a') := by omega
      have hhi : walshBool F (consVec true a') ≤ 2 * B - 4 := by omega
      exact Int.mul_nonneg (by omega) (by omega)
  have hgap_sum : sumVecs gap = 8 * L - 16 * (B * B) * t - 32 * (B * B) := by
    rw [sumVecs_congr hgap_eq, sumVecs_sub, sumVecs_sub, sumVecs_mul_left,
        sumVecs_sub, sumVecs_const, sumVecs_const, hE1, hpow2k1]
    change 8 * L - (8 * (B * B) * (B * B) + 16 * (B * B) * t - 2 * (B * B) * (4 * (B * B))) -
           2 * (B * B) * 16 = _
    rw [h8B4]
    have h32 : 2 * (B * B) * 16 = 32 * (B * B) := by
      rw [Int.mul_comm (2 * (B * B)) 16, ← Int.mul_assoc 16 2]; rfl
    omega
  have h8mul : 8 * (2 * B * B * (2 + t)) = 16 * (B * B) * t + 32 * (B * B) := by
    have h1 : 2 * B * B = 2 * (B * B) := Int.mul_assoc 2 B B
    rw [h1, Int.mul_add, Int.mul_add]
    have hA : 8 * (2 * (B * B) * 2) = 32 * (B * B) := by
      rw [Int.mul_comm (2 * (B * B)) 2, ← Int.mul_assoc 2 2, ← Int.mul_assoc 8 (2 * 2)]; rfl
    have hB : 8 * (2 * (B * B) * t) = 16 * (B * B) * t := by
      rw [← Int.mul_assoc 8 (2 * (B * B)) t, ← Int.mul_assoc 8 2 (B * B)]; rfl
    rw [hA, hB]; omega
  have hgap_sum_nn : 0 ≤ sumVecs gap := sumVecs_nonneg hgap_nn
  have hL_ge : 2 * B * B * (2 + t) ≤ L := by omega
  have hL_eq : L = 2 * B * B * (2 + t) →
      ∀ a' : Vec (2 * k + 1),
        walshBool F (consVec true a') * sign (Q1 a') = 2 * B + 4 ∨
        walshBool F (consVec true a') * sign (Q1 a') = -(2 * B - 4) := by
    intro hEq a'
    have hgz : sumVecs gap = 0 := by omega
    have hga := sumVecs_eq_zero_of_nonneg hgap_nn hgz a'
    dsimp only [gap] at hga
    cases Int.mul_eq_zero.mp hga with
    | inl h1 => left; omega
    | inr h2 => right; omega
  exact ⟨t, ht_ge1, hdH_eq, hH0_bound, hL_ge, hL_adj, hL_eq⟩

/-! ## Section 6: Elimination of Non-Maximal Ranks `r ≤ k - 1` -/

private theorem rank_must_be_maximal {k : Nat} (hk : 3 ≤ k)
    (F : Vec (2 * k + 2) → Bool) (hbal : isBalanced (2 * k + 2) F)
    (hcap : ∀ a, -((2 : Int) ^ (k + 1) + 4) ≤ walshBool F a ∧
                 walshBool F a ≤ (2 : Int) ^ (k + 1) + 4)
    (hnorm : ∀ (b : Bool) (a' : Vec (2 * k + 1)), dot (supportXor F) (consVec b a') = b) :
    radSize (fun a' => quadMod2 F (consVec true a')) = 2 := by
  let B : Int := (2 : Int) ^ k
  let D : Vec (2 * k + 1) → Int := fun x' =>
    if F (consVec false x') == F (consVec true x') then 0 else sign (F (consVec false x'))
  let Q0 : Vec (2 * k + 1) → Bool := fun a' => quadMod2 F (consVec false a')
  let Q1 : Vec (2 * k + 1) → Bool := fun a' => quadMod2 F (consVec true a')
  let L : Int := sumVecs (fun a' => walshBool F (consVec true a') * sign (Q1 a'))
  have hB_pos : 0 < B := two_pow_pos k
  have hB8 : 8 ≤ B := by
    have : (8 : Int) = (2 : Int) ^ 3 := rfl
    rw [this]; exact two_pow_le_of_le hk
  have hBsq_pos : 0 < B * B := Int.mul_pos hB_pos hB_pos
  have hQ_quad := quadMod2_isQuadratic F
  obtain ⟨hQ0_quad, hQ1_quad, hrad_same⟩ := slice_quad_same_rad (quadMod2 F) hQ_quad
  obtain ⟨t, ht1, _, hH0_bound, hL_ge, hL_adj, _⟩ := normalized_H0_H1_bounds hk F hbal hcap hnorm
  -- Apply odd-dimension quadratic spectrum theorem to Q1 (on 2*(k+1) - 1 = 2*k + 1 variables).
  have hdim : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have hspec1 := quadratic_odd_dim_spectrum (m := k + 1) (by omega) Q1 hQ1_quad
  obtain ⟨r, hr_le, hrad1, hvals1, hL1⟩ := hspec1
  have hsub_dim : 2 * (k + 1) - 1 - r = 2 * k + 1 - r := by omega
  have hadd_dim : 2 * (k + 1) - 1 + r = 2 * k + 1 + r := by omega
  -- Show r = k (by eliminating r = 0 and 1 ≤ r ≤ k - 1).
  -- First, L ≤ 4 * B^2 * 2^r via hL_adj and |D x'| ≤ 1:
  have hL_adj' : L = 2 * sumVecs (fun x' => D x' * walshBool Q1 x') := hL_adj
  have hL_ge' : 2 * B * B * (2 + t) ≤ L := hL_ge
  have hH0_bound' : 8 * (B - 2) * hammingWeight Q0 ≤ B * B * (4 * t - 1) := hH0_bound
  have hL_ub : L ≤ 2 * (2 : Int) ^ (2 * k + 1 + r) := by
    rw [hL_adj']
    have hpw : ∀ x' : Vec (2 * k + 1),
        D x' * walshBool Q1 x' ≤ (if walshBool Q1 x' = 0 then (0 : Int) else (2 : Int) ^ (2 * k + 1 - r)) := by
      intro x'
      have hD_le : -1 ≤ D x' ∧ D x' ≤ 1 := by
        dsimp only [D]; cases F (consVec false x') <;> cases F (consVec true x') <;> decide
      have hM_pos : 0 < (2 : Int) ^ (2 * k + 1 - r) := two_pow_pos _
      have hvx := hvals1 x'
      rw [hsub_dim] at hvx
      rcases hvx with h0 | hp | hn
      · rw [h0]; simp
      · have hne : walshBool Q1 x' ≠ 0 := by rw [hp]; omega
        rw [if_neg hne, hp]
        have : D x' * (2 : Int) ^ (2 * k + 1 - r) ≤ 1 * (2 : Int) ^ (2 * k + 1 - r) :=
          Int.mul_le_mul_of_nonneg_right hD_le.2 (by omega)
        omega
      · have hne : walshBool Q1 x' ≠ 0 := by rw [hn]; omega
        rw [if_neg hne, hn]
        have : (-1) * (2 : Int) ^ (2 * k + 1 - r) ≤ D x' * (2 : Int) ^ (2 * k + 1 - r) :=
          Int.mul_le_mul_of_nonneg_right hD_le.1 (by omega)
        rw [Int.mul_neg]
        omega
    have hsum := sumVecs_mono hpw
    rw [hsub_dim, hadd_dim] at hL1
    have hle : sumVecs (fun x' : Vec (2 * k + 1) => D x' * walshBool Q1 x') ≤ (2 : Int) ^ (2 * k + 1 + r) :=
      hL1 ▸ hsum
    omega
  have hpow_ub : 2 * (2 : Int) ^ (2 * k + 1 + r) = 4 * (B * B) * (2 : Int) ^ r := by
    have : 2 * k + 1 + r = (k + k) + 1 + r := by omega
    rw [this, int_pow_add, int_pow_add, int_pow_add]
    have h21 : (2 : Int) ^ 1 = 2 := rfl
    rw [h21]
    have h1 : 2 * (B * B * 2 * (2 : Int) ^ r) = (2 * 2) * (B * B) * (2 : Int) ^ r := by
      rw [← Int.mul_assoc 2 (B * B * 2), Int.mul_comm (B * B) 2, ← Int.mul_assoc 2 2 (B * B)]
    exact h1
  rw [hpow_ub] at hL_ub
  have h2r_bound : 2 * B * B * (2 + t) ≤ 4 * (B * B) * (2 : Int) ^ r := by omega
  have ht_ub : 2 + t ≤ 2 * (2 : Int) ^ r := by
    have hmul : (B * B) * (2 * (2 + t)) ≤ (B * B) * (4 * (2 : Int) ^ r) := by
      have h1 : (B * B) * (2 * (2 + t)) = 2 * B * B * (2 + t) := by
        simp only [Int.mul_assoc, Int.mul_left_comm]
      have h2 : (B * B) * (4 * (2 : Int) ^ r) = 4 * (B * B) * (2 : Int) ^ r := by
        simp only [Int.mul_assoc, Int.mul_left_comm]
      omega
    have hle := Int.le_of_mul_le_mul_left hmul hBsq_pos
    omega
  by_cases hr0 : r = 0
  · subst hr0; simp at ht_ub; omega
  · by_cases hr_lt : r ≤ k - 1
    · -- Eliminate 1 ≤ r ≤ k - 1 via wt(Q_0) ≥ B^2 / 2.
      have hrad0 : radSize Q0 = (2 : Int) ^ (2 * k + 1 - 2 * r) := by
        have heq : radSize Q0 = radSize Q1 := by
          unfold radSize; apply sumVecs_congr; intro u; rw [hrad_same u]
        rw [heq, hrad1]; rfl
      -- From dichotomy on Q0 at x = 0: |W_{Q0}(0)| ≤ 2^(2k + 1 - r) ≤ B^2 (since r ≥ 1).
      have hW0_le : walshBool Q0 zeroVec ≤ B * B := by
        have hM_le : (2 : Int) ^ (2 * k + 1 - r) ≤ B * B := by
          have hpow : B * B = (2 : Int) ^ (2 * k) := by
            have : 2 * k = k + k := by omega
            rw [this, int_pow_add]
          rw [hpow]; exact two_pow_le_of_le (by omega)
        cases walshBool_sq_quadratic_dichotomy Q0 hQ0_quad zeroVec with
        | inl hz => rw [hz]; omega
        | inr hsq =>
          rw [hrad0, ← int_pow_add] at hsq
          have hexp : (2 * k + 1) + (2 * k + 1 - 2 * r) = (2 * k + 1 - r) + (2 * k + 1 - r) := by omega
          rw [hexp, int_pow_add] at hsq
          cases int_sq_eq_iff hsq with
          | inl hp => rw [hp]; exact hM_le
          | inr hn => rw [hn]; have := two_pow_pos (2 * k + 1 - r); omega
      have hwt_ge : B * B ≤ 2 * hammingWeight Q0 := by
        have h0 := walshBool_zero_eq_wt Q0
        have hpow : (2 : Int) ^ (2 * k + 1) = 2 * (B * B) := by
          have : 2 * k + 1 = (k + k) + 1 := by omega
          rw [this, Int.pow_succ, int_pow_add, Int.mul_comm]
        rw [hpow] at h0; omega
      have hH0' : 4 * (B - 2) * (B * B) ≤ B * B * (4 * t - 1) := by
        have hmul := Int.mul_le_mul_of_nonneg_left hwt_ge (show 0 ≤ 4 * (B - 2) by omega)
        have h1 : 4 * (B - 2) * (2 * hammingWeight Q0) = 8 * (B - 2) * hammingWeight Q0 := by
          have : 4 * (B - 2) * (2 * hammingWeight Q0) = (4 * 2) * (B - 2) * hammingWeight Q0 := by
            simp only [Int.mul_assoc, Int.mul_left_comm]
          exact this
        omega
      have ht_lb : 4 * (B - 2) ≤ 4 * t - 1 := by
        rw [Int.mul_comm (4 * (B - 2)) (B * B)] at hH0'
        exact Int.le_of_mul_le_mul_left hH0' hBsq_pos
      have h2r_le : 2 * (2 : Int) ^ r ≤ B := by
        have : 2 * (2 : Int) ^ r = (2 : Int) ^ (r + 1) := by rw [Int.pow_succ, Int.mul_comm]
        rw [this]; exact two_pow_le_of_le (by omega)
      omega
    · have hrk : r = k := by omega
      rw [hrad1, hrk]
      have : 2 * (k + 1) - 1 - 2 * k = 1 := by omega
      rw [this]; rfl

/-! ## Section 7: Maximal Rank `r = k`, Normalization #2, All `m ≥ 6`, and `n = 10` Closure -/

/-- Normalization #2: at `radSize Q_1 = 2`, linearly transform the last `2k + 1` coordinates
    (fixing coordinate `0`) so that `e_0 ∈ Rad(Q_0) = Rad(Q_1)`. -/
private theorem normalize_radical_e0 {k : Nat} (hk : 3 ≤ k)
    (F : Vec (2 * k + 2) → Bool) (hbal : isBalanced (2 * k + 2) F)
    (hcap : ∀ a, -((2 : Int) ^ (k + 1) + 4) ≤ walshBool F a ∧
                 walshBool F a ≤ (2 : Int) ^ (k + 1) + 4)
    (hnorm : ∀ (b : Bool) (a' : Vec (2 * k + 1)), dot (supportXor F) (consVec b a') = b) :
    ∃ G : Vec (2 * k + 2) → Bool,
      isBalanced (2 * k + 2) G ∧
      (∀ a, -((2 : Int) ^ (k + 1) + 4) ≤ walshBool G a ∧
            walshBool G a ≤ (2 : Int) ^ (k + 1) + 4) ∧
      (∀ (b : Bool) (a' : Vec (2 * k + 1)), dot (supportXor G) (consVec b a') = b) ∧
      radSize (fun a' => quadMod2 G (consVec true a')) = 2 ∧
      isRad (fun a' => quadMod2 G (consVec true a')) (consVec true zeroVec) = true := by
  let Q1 : Vec (2 * k + 1) → Bool := fun a' => quadMod2 F (consVec true a')
  have hrad2 : radSize Q1 = 2 := rank_must_be_maximal hk F hbal hcap hnorm
  -- Since radSize Q1 = 2 and zeroVec ∈ Rad(Q1), there exists u ≠ zeroVec in Rad(Q1).
  have hex_u : ∃ u : Vec (2 * k + 1), u ≠ zeroVec ∧ isRad Q1 u = true := by
    apply Classical.byContradiction; intro hno
    have hpw : ∀ u : Vec (2 * k + 1),
        (if isRad Q1 u then (1 : Int) else 0) = (if isZeroVec u then 1 else 0) := by
      intro u
      by_cases hu0 : isZeroVec u = true
      · have hz := (isZeroVec_true_iff u).mp hu0
        rw [hu0, hz, isRad_zero]
      · have hne : u ≠ zeroVec := fun h => hu0 ((isZeroVec_true_iff u).mpr h)
        cases hr : isRad Q1 u
        · simp [hu0]
        · exact False.elim (hno ⟨u, hne, hr⟩)
    unfold radSize at hrad2
    rw [sumVecs_congr hpw, sumVecs_delta_zero] at hrad2
    omega
  obtain ⟨u, hune, hurad⟩ := hex_u
  have hex_p : ∃ p : Fin (2 * k + 1), u p = true := by
    apply Classical.byContradiction; intro hno
    apply hune; funext i
    cases hi : u i
    · rfl
    · exact False.elim (hno ⟨i, hi⟩)
  obtain ⟨p, hp⟩ := hex_p
  let u1 : Vec (2 * k + 1) := swap0 p u
  have hu1_0 : u1 ⟨0, Nat.zero_lt_succ _⟩ = true := by
    dsimp only [u1]; unfold swap0; simp only [↓reduceIte]; exact hp
  let T : Vec (2 * k + 1) → Vec (2 * k + 1) := fun x' => swap0 p (shear u1 x')
  let Ts : Vec (2 * k + 1) → Vec (2 * k + 1) := fun a' => swap0 p (shearT u1 a')
  let G : Vec (2 * k + 2) → Bool := fun x =>
    F (consVec (x ⟨0, Nat.zero_lt_succ _⟩) (T (tailVec x)))
  have hWG : ∀ (b : Bool) (a' : Vec (2 * k + 1)),
      walshBool G (consVec b a') = walshBool F (consVec b (Ts a')) := by
    intro b a'
    unfold walshBool
    rw [walsh_cons, walsh_cons]
    have hslice : ∀ c : Bool,
        walsh (fun x' => sign (G (consVec c x'))) a' =
        walsh (fun x' => sign (F (consVec c x'))) (Ts a') := by
      intro c
      have h1 := walsh_shear u1 hu1_0 (fun y' => sign (F (consVec c (swap0 p y')))) a'
      have h2 := walsh_swap0 p (fun y' => sign (F (consVec c y'))) (shearT u1 a')
      exact h1.trans h2
    rw [hslice false, hslice true]
  have hGbal : isBalanced (2 * k + 2) G := by
    unfold isBalanced hammingWeight at hbal ⊢
    change 2 * (sumVecs (fun v => if G (consVec false v) then (1 : Int) else 0) +
                sumVecs (fun v => if G (consVec true v) then (1 : Int) else 0)) = _
    have h0 : sumVecs (fun v => if G (consVec false v) then (1 : Int) else 0) =
        sumVecs (fun v => if F (consVec false v) then (1 : Int) else 0) :=
      (sumVecs_shear u1 hu1_0 (fun y => if F (consVec false (swap0 p y)) then (1 : Int) else 0)).trans
        (sumVecs_swap0 p (fun y => if F (consVec false y) then (1 : Int) else 0))
    have h1 : sumVecs (fun v => if G (consVec true v) then (1 : Int) else 0) =
        sumVecs (fun v => if F (consVec true v) then (1 : Int) else 0) :=
      (sumVecs_shear u1 hu1_0 (fun y => if F (consVec true (swap0 p y)) then (1 : Int) else 0)).trans
        (sumVecs_swap0 p (fun y => if F (consVec true y) then (1 : Int) else 0))
    rw [h0, h1]; exact hbal
  have hGcap : ∀ a, -((2 : Int) ^ (k + 1) + 4) ≤ walshBool G a ∧
                    walshBool G a ≤ (2 : Int) ^ (k + 1) + 4 := by
    intro a; rw [← consVec_eta a, hWG]; exact hcap _
  have hGmod : ∀ (b : Bool) (a' : Vec (2 * k + 1)),
      dot (supportXor G) (consVec b a') = b ∧
      quadMod2 G (consVec b a') = quadMod2 F (consVec b (Ts a')) := by
    intro b a'
    have mG := walshBool_mod16_quad (by omega) G hGbal (consVec b a')
    have mF := walshBool_mod16_quad (by omega) F hbal (consVec b (Ts a'))
    rw [hWG b a'] at mG
    rw [hnorm b (Ts a')] at mF
    have heq := mG.symm.trans mF
    cases hb : b <;> rw [hb] at heq <;>
      cases hd : dot (supportXor G) (consVec _ a') <;>
      cases hqG : quadMod2 G (consVec _ a') <;>
      cases hqF : quadMod2 F (consVec _ (Ts a')) <;>
      simp [hd, hqG, hqF] at heq ⊢
  have hTs_xor : ∀ a1 a2 : Vec (2 * k + 1), Ts (xorVec a1 a2) = xorVec (Ts a1) (Ts a2) := by
    intro a1 a2; dsimp only [Ts]; rw [shearT_xor, swap0_xor]
  have hTs_zero : Ts zeroVec = zeroVec := by
    have := hTs_xor zeroVec zeroVec
    rw [xorVec_self, xorVec_self] at this
    exact this
  have hTs_e0 : Ts (consVec true zeroVec) = u := by
    dsimp only [Ts]; rw [shearT_e0 u1 hu1_0]; exact swap0_invol p u
  have hTs_surj : ∀ y : Vec (2 * k + 1), ∃ x : Vec (2 * k + 1), Ts x = y := by
    intro y; refine ⟨shearT u1 (swap0 p y), ?_⟩
    dsimp only [Ts]; rw [shearT_invol, swap0_invol]
  have hGnorm : ∀ (b : Bool) (a' : Vec (2 * k + 1)), dot (supportXor G) (consVec b a') = b :=
    fun b a' => (hGmod b a').1
  have hGrad2 : radSize (fun a' => quadMod2 G (consVec true a')) = 2 :=
    rank_must_be_maximal hk G hGbal hGcap hGnorm
  have hGe0_rad : isRad (fun a' => quadMod2 G (consVec true a')) (consVec true zeroVec) = true := by
    rw [isRad_true_iff]; intro a'
    rw [(hGmod true _).2, (hGmod true _).2, (hGmod true _).2, (hGmod true _).2,
        hTs_xor, hTs_e0, hTs_zero]
    exact (isRad_true_iff Q1 u).mp hurad (Ts a')
  exact ⟨G, hGbal, hGcap, hGnorm, hGrad2, hGe0_rad⟩

/-- Exclusion theorem for even `n = 2k + 2 ≥ 10` (`k ≥ 4`, i.e., `m = k + 1 ≥ 5`):
    No balanced Boolean function on `2k + 2` variables has `|W_F(a)| ≤ 2^(k+1) + 4` everywhere. -/
private theorem even_balanced_exclusion_aux {k : Nat} (hk : 3 ≤ k)
    (F0 : Vec (2 * k + 2) → Bool) (hbal0 : isBalanced (2 * k + 2) F0)
    (hcap0 : ∀ a, -((2 : Int) ^ (k + 1) + 4) ≤ walshBool F0 a ∧
                  walshBool F0 a ≤ (2 : Int) ^ (k + 1) + 4) : False := by
  obtain ⟨F1, hbal1, hcap1, hnorm1⟩ := normalize_supportXor hk F0 hbal0 hcap0
  obtain ⟨F, hbal, hcap, hnorm, hrad2, he0_rad⟩ := normalize_radical_e0 hk F1 hbal1 hcap1 hnorm1
  let B : Int := (2 : Int) ^ k
  let D : Vec (2 * k + 1) → Int := fun x' =>
    if F (consVec false x') == F (consVec true x') then 0 else sign (F (consVec false x'))
  let Q0 : Vec (2 * k + 1) → Bool := fun a' => quadMod2 F (consVec false a')
  let Q1 : Vec (2 * k + 1) → Bool := fun a' => quadMod2 F (consVec true a')
  let L : Int := sumVecs (fun a' => walshBool F (consVec true a') * sign (Q1 a'))
  have hB_pos : 0 < B := two_pow_pos k
  have hB8 : 8 ≤ B := by
    have : (8 : Int) = (2 : Int) ^ 3 := rfl
    rw [this]; exact two_pow_le_of_le hk
  have hBsq_pos : 0 < B * B := Int.mul_pos hB_pos hB_pos
  have hpow2k : (2 : Int) ^ (2 * k) = B * B := by
    have : 2 * k = k + k := by omega
    rw [this, int_pow_add]
  have hpow2k1 : (2 : Int) ^ (2 * k + 1) = 2 * (B * B) := by
    rw [Int.pow_succ, hpow2k, Int.mul_comm]
  have h2B_pow : (2 : Int) ^ (k + 1) = 2 * B := by rw [Int.pow_succ, Int.mul_comm]
  obtain ⟨t, ht1, hdH_eq, hH0_bound, hL_ge, hL_adj, hL_eq_char⟩ :=
    normalized_H0_H1_bounds hk F hbal hcap hnorm
  have hQ_quad := quadMod2_isQuadratic F
  obtain ⟨hQ0_quad, hQ1_quad, hrad_same⟩ := slice_quad_same_rad (quadMod2 F) hQ_quad
  have hrad0_eq : radSize Q0 = 2 := by
    have : radSize Q0 = radSize Q1 := by
      unfold radSize; apply sumVecs_congr; intro u; rw [hrad_same u]
    rw [this, hrad2]
  have hH0_bound' : 8 * (B - 2) * hammingWeight Q0 ≤ B * B * (4 * t - 1) := hH0_bound
  have hL_ge' : 2 * B * B * (2 + t) ≤ L := hL_ge
  have hL_adj' : L = 2 * sumVecs (fun x' => D x' * walshBool Q1 x') := hL_adj
  have hdH_eq' : sumVecs (fun x' => D x' * D x') = B * B + 2 * t := hdH_eq
  have hW0_dich : walshBool Q0 zeroVec = 0 ∨ walshBool Q0 zeroVec = 2 * B ∨ walshBool Q0 zeroVec = -(2 * B) := by
    cases walshBool_sq_quadratic_dichotomy Q0 hQ0_quad zeroVec with
    | inl hz => exact Or.inl hz
    | inr hsq =>
      rw [hrad0_eq, hpow2k1] at hsq
      have h4 : 2 * (B * B) * 2 = 2 * B * (2 * B) := by
        rw [two_mul_sq_eq B, Int.mul_comm (2 * (B * B)) 2, ← Int.mul_assoc]; rfl
      rw [h4] at hsq
      cases int_sq_eq_iff hsq with
      | inl hp => exact Or.inr (Or.inl hp)
      | inr hn => exact Or.inr (Or.inr hn)
  have hwtQ0_vals : hammingWeight Q0 = B * B ∨ hammingWeight Q0 = B * B - B ∨ hammingWeight Q0 = B * B + B := by
    have h0 := walshBool_zero_eq_wt Q0
    rw [hpow2k1] at h0
    rcases hW0_dich with hz | hp | hn
    · left; omega
    · right; left; omega
    · right; right; omega
  have hwtQ0_lb : B * B - B ≤ hammingWeight Q0 := by
    rcases hwtQ0_vals with h1 | h2 | h3 <;> omega
  have ht_lb : 2 * B - 5 ≤ t := by
    have h1 := Int.mul_le_mul_of_nonneg_left hwtQ0_lb (show 0 ≤ 8 * (B - 2) by omega)
    have h2 : 8 * (B - 2) * (B * B - B) ≤ B * B * (4 * t - 1) := by omega
    have hexp : 8 * (B - 2) * (B * B - B) = B * B * (8 * B - 24) + 16 * B := by
      simp only [Int.mul_sub, Int.sub_mul]
      have ha : 8 * B * (B * B) = B * B * (8 * B) := Int.mul_comm _ _
      have hb : 8 * 2 * (B * B) = 16 * (B * B) := rfl
      have hc : 8 * B * B = 8 * (B * B) := Int.mul_assoc _ _ _
      have hd : B * B * 24 = 24 * (B * B) := Int.mul_comm _ _
      have he : 8 * 2 * B = 16 * B := rfl
      rw [ha, hb, hc, hd, he]; omega
    rw [hexp] at h2
    have h3 : B * B * (8 * B - 24) < B * B * (4 * t - 1) := by omega
    have h4 : 8 * B - 24 < 4 * t - 1 := by
      apply Classical.byContradiction; intro hge
      have := Int.mul_le_mul_of_nonneg_left (show 4 * t - 1 ≤ 8 * B - 24 by omega) (by omega : 0 ≤ B * B)
      omega
    omega
  -- 2. Radical of Q1 is exactly {0, e_0}, so W_{Q1} is supported on one hyperplane x'_0 = eps.
  let e0 : Vec (2 * k + 1) := consVec true zeroVec
  have hrad_only : ∀ u : Vec (2 * k + 1), isRad Q1 u = true → u = zeroVec ∨ u = e0 := by
    intro u hur
    by_cases h0 : u = zeroVec
    · exact Or.inl h0
    · by_cases he : u = e0
      · exact Or.inr he
      · exfalso
        have h3 : sumVecs (fun v : Vec (2 * k + 1) =>
            (if isZeroVec v then (1 : Int) else 0) +
            (if isZeroVec (xorVec v e0) then 1 else 0) +
            (if isZeroVec (xorVec v u) then 1 else 0)) ≤ radSize Q1 := by
          unfold radSize
          apply sumVecs_mono; intro v
          by_cases hv0 : isZeroVec v = true
          · have hvz := (isZeroVec_true_iff v).mp hv0
            subst hvz
            have hne1 : isZeroVec (xorVec zeroVec e0) = false := by
              rw [xorVec_zero_left]; rfl
            have hne2 : isZeroVec (xorVec zeroVec u) = false := by
              rw [xorVec_zero_left]
              cases h : isZeroVec u
              · rfl
              · exact False.elim (h0 ((isZeroVec_true_iff u).mp h))
            simp [hv0, hne1, hne2, isRad_zero]
          · by_cases hve : isZeroVec (xorVec v e0) = true
            · have hv : v = e0 := by
                have := (isZeroVec_true_iff _).mp hve
                have h2 := congrArg (fun z => xorVec z e0) this
                simp only [xorVec_assoc, xorVec_self, xorVec_zero_right, xorVec_zero_left] at h2
                exact h2
              subst hv
              have hne2 : isZeroVec (xorVec e0 u) = false := by
                cases h : isZeroVec (xorVec e0 u)
                · rfl
                · have := (isZeroVec_true_iff _).mp h
                  have h2 := congrArg (fun z => xorVec e0 z) this
                  simp only [← xorVec_assoc, xorVec_self, xorVec_zero_left, xorVec_zero_right] at h2
                  exact False.elim (he h2)
              simp [hv0, hve, hne2, he0_rad]
            · by_cases hvu : isZeroVec (xorVec v u) = true
              · have hv : v = u := by
                  have := (isZeroVec_true_iff _).mp hvu
                  have h2 := congrArg (fun z => xorVec z u) this
                  simp only [xorVec_assoc, xorVec_self, xorVec_zero_right, xorVec_zero_left] at h2
                  exact h2
                subst hv
                simp [hv0, hve, hvu, hur]
              · simp [hv0, hve, hvu]; cases isRad Q1 v <;> decide
        rw [sumVecs_add, sumVecs_add, sumVecs_delta_zero,
            sumVecs_xor_shift e0 (fun v => if isZeroVec v then (1 : Int) else 0),
            sumVecs_delta_zero,
            sumVecs_xor_shift u (fun v => if isZeroVec v then (1 : Int) else 0),
            sumVecs_delta_zero, hrad2] at h3
        omega
  -- Exact formula for W_{Q1}(x')^2 = 2^(2k+1) * (1 + sign(x'_0 ⊕ eps)).
  let eps : Bool := xor (Q1 e0) (Q1 zeroVec)
  have hWQ1_sq : ∀ x' : Vec (2 * k + 1),
      walshBool Q1 x' * walshBool Q1 x' =
        2 * (B * B) * (1 + sign (xor (x' ⟨0, Nat.zero_lt_succ _⟩) eps)) := by
    intro x'
    rw [walshBool_sq_quadratic Q1 hQ1_quad x', hpow2k1]
    congr 1
    have hpw : ∀ u : Vec (2 * k + 1),
        (if isRad Q1 u then sign (xor (dot x' u) (xor (Q1 u) (Q1 zeroVec))) else 0) =
        (if isZeroVec u then (1 : Int) else 0) +
        (if isZeroVec (xorVec u e0) then sign (xor (x' ⟨0, Nat.zero_lt_succ _⟩) eps) else 0) := by
      intro u
      by_cases hu0 : isZeroVec u = true
      · have hz := (isZeroVec_true_iff u).mp hu0
        subst hz
        have hne : isZeroVec (xorVec zeroVec e0) = false := by rw [xorVec_zero_left]; rfl
        simp [hu0, hne, isRad_zero, dot_zero_right, sign]
      · by_cases hue : isZeroVec (xorVec u e0) = true
        · have hu : u = e0 := by
            have := (isZeroVec_true_iff _).mp hue
            have h2 := congrArg (fun z => xorVec z e0) this
            simp only [xorVec_assoc, xorVec_self, xorVec_zero_right, xorVec_zero_left] at h2
            exact h2
          subst hu
          have hdot : dot x' e0 = x' ⟨0, Nat.zero_lt_succ _⟩ := by
            conv => lhs; rw [← consVec_eta x']
            dsimp only [e0]; rw [dot_cons, dot_zero_right, Bool.and_true, Bool.xor_false]
          simp [hu0, hue, he0_rad, hdot, eps]
        · have hnotrad : isRad Q1 u = false := by
            cases hr : isRad Q1 u
            · rfl
            · cases hrad_only u hr with
              | inl hz => rw [hz] at hu0; exact False.elim (hu0 ((isZeroVec_true_iff zeroVec).mpr rfl))
              | inr he => rw [he, xorVec_self] at hue; exact False.elim (hue ((isZeroVec_true_iff zeroVec).mpr rfl))
          simp [hu0, hue, hnotrad]
    rw [sumVecs_congr hpw, sumVecs_add, sumVecs_delta_zero,
        sumVecs_xor_shift e0 (fun u => if isZeroVec u then sign (xor (x' ⟨0, Nat.zero_lt_succ _⟩) eps) else 0),
        sumVecs_delta_zero]
  have hWQ1_off : ∀ x'' : Vec (2 * k), walshBool Q1 (consVec (!eps) x'') = 0 := by
    intro x''
    have hsq := hWQ1_sq (consVec (!eps) x'')
    have hnot : xor (!eps) eps = true := by cases eps <;> rfl
    simp only [consVec_head, hnot, sign, ↓reduceIte] at hsq
    have hz : walshBool Q1 (consVec (!eps) x'') * walshBool Q1 (consVec (!eps) x'') = 0 := by omega
    cases Int.mul_eq_zero.mp hz with | inl h => exact h | inr h => exact h
  -- Bent slice b on Vec (2k): W_{Q1}(eps, x'') = 2 * B * sign(b x'').
  let b : Vec (2 * k) → Bool := fun x'' => decide (walshBool Q1 (consVec eps x'') < 0)
  have hWQ1_on : ∀ x'' : Vec (2 * k), walshBool Q1 (consVec eps x'') = 2 * B * sign (b x'') := by
    intro x''
    have hsq := hWQ1_sq (consVec eps x'')
    have hself : xor eps eps = false := by cases eps <;> rfl
    simp only [consVec_head, hself, sign, Bool.false_eq_true, ↓reduceIte] at hsq
    have h4 : 2 * (B * B) * (1 + 1) = 2 * B * (2 * B) := by
      rw [two_mul_sq_eq B, show (1 + 1 : Int) = 2 by rfl, Int.mul_comm (2 * (B * B)) 2, ← Int.mul_assoc]; rfl
    rw [h4] at hsq
    cases int_sq_eq_iff hsq with
    | inl hp =>
      have hbf : b x'' = false := by dsimp only [b]; rw [hp]; simp; omega
      rw [hp, hbf]; simp [sign]
    | inr hn =>
      have hbt : b x'' = true := by dsimp only [b]; rw [hn]; simp; omega
      rw [hn, hbt]; simp [sign]
  -- Walsh inversion on Q1 gives W_b(a'') = B * sign(Q1(0, a'')).
  let s : Vec (2 * k) → Int := fun a'' => sign (Q1 (consVec false a''))
  have hWb : ∀ a'' : Vec (2 * k), walshBool b a'' = B * s a'' := by
    intro a''
    have hinv' := walsh_inversion (fun x' => sign (Q1 x')) (consVec false a'')
    change walsh (walshBool Q1) (consVec false a'') = (2 : Int) ^ (2 * k + 1) * s a'' at hinv'
    rw [hpow2k1] at hinv'
    have hsum : walsh (walshBool Q1) (consVec false a'') = 2 * B * walshBool b a'' := by
      change sumVecs (fun x'' => walshBool Q1 (consVec false x'') * sign (dot (consVec false a'') (consVec false x''))) +
             sumVecs (fun x'' => walshBool Q1 (consVec true x'') * sign (dot (consVec false a'') (consVec true x''))) =
             2 * B * sumVecs (fun x'' => sign (b x'') * sign (dot a'' x''))
      have hdot0 : ∀ c x'', dot (consVec false a'') (consVec c x'') = dot a'' x'' := by
        intro c x''; rw [dot_cons, Bool.false_and, Bool.false_xor]
      have hs0 : sumVecs (fun x'' => walshBool Q1 (consVec false x'') * sign (dot (consVec false a'') (consVec false x''))) =
          sumVecs (fun x'' => walshBool Q1 (consVec false x'') * sign (dot a'' x'')) :=
        sumVecs_congr (fun x'' => by rw [hdot0 false x''])
      have hs1 : sumVecs (fun x'' => walshBool Q1 (consVec true x'') * sign (dot (consVec false a'') (consVec true x''))) =
          sumVecs (fun x'' => walshBool Q1 (consVec true x'') * sign (dot a'' x'')) :=
        sumVecs_congr (fun x'' => by rw [hdot0 true x''])
      rw [hs0, hs1]
      cases heps : eps
      · have hoff : ∀ x'', walshBool Q1 (consVec true x'') = 0 := by
          intro x''; have := hWQ1_off x''; rw [heps] at this; exact this
        have hon : ∀ x'', walshBool Q1 (consVec false x'') = 2 * B * sign (b x'') := by
          intro x''; have := hWQ1_on x''; rw [heps] at this; exact this
        have hpart1 : sumVecs (fun x'' => walshBool Q1 (consVec true x'') * sign (dot a'' x'')) = 0 := by
          rw [sumVecs_congr (fun x'' => by rw [hoff x'', Int.zero_mul]), sumVecs_const, Int.mul_zero]
        have hpart0 : sumVecs (fun x'' => walshBool Q1 (consVec false x'') * sign (dot a'' x'')) =
            2 * B * sumVecs (fun x'' => sign (b x'') * sign (dot a'' x'')) := by
          rw [sumVecs_congr (fun x'' => by rw [hon x'', Int.mul_assoc]), sumVecs_mul_left]
        rw [hpart0, hpart1, Int.add_zero]
      · have hoff : ∀ x'', walshBool Q1 (consVec false x'') = 0 := by
          intro x''; have := hWQ1_off x''; rw [heps] at this; exact this
        have hon : ∀ x'', walshBool Q1 (consVec true x'') = 2 * B * sign (b x'') := by
          intro x''; have := hWQ1_on x''; rw [heps] at this; exact this
        have hpart0 : sumVecs (fun x'' => walshBool Q1 (consVec false x'') * sign (dot a'' x'')) = 0 := by
          rw [sumVecs_congr (fun x'' => by rw [hoff x'', Int.zero_mul]), sumVecs_const, Int.mul_zero]
        have hpart1 : sumVecs (fun x'' => walshBool Q1 (consVec true x'') * sign (dot a'' x'')) =
            2 * B * sumVecs (fun x'' => sign (b x'') * sign (dot a'' x'')) := by
          rw [sumVecs_congr (fun x'' => by rw [hon x'', Int.mul_assoc]), sumVecs_mul_left]
        rw [hpart0, hpart1, Int.zero_add]
    rw [hsum] at hinv'
    have h2B_pos : 0 < 2 * B := by omega
    have h2 : 2 * B * walshBool b a'' = 2 * B * (B * s a'') := by
      rw [hinv']; simp only [Int.mul_assoc, Int.mul_left_comm]
    exact Int.eq_of_mul_eq_mul_left (Int.ne_of_gt h2B_pos) h2
  -- 3. Split D into D_star (on slice eps) and D_bar (on slice !eps), and decompose D_star = sign b + E_star.
  let Dstar : Vec (2 * k) → Int := fun x'' => D (consVec eps x'')
  let Dbar : Vec (2 * k) → Int := fun x'' => D (consVec (!eps) x'')
  let Estar : Vec (2 * k) → Int := fun x'' => Dstar x'' - sign (b x'')
  let m1 : Int := sumVecs (fun x'' => if Dstar x'' = 0 then (1 : Int) else 0)
  let m2 : Int := sumVecs (fun x'' => if Dstar x'' = -sign (b x'') then (1 : Int) else 0)
  let delta : Int := m1 + 2 * m2
  have hm1_nn : 0 ≤ m1 := sumVecs_nonneg (fun x'' => by by_cases h : Dstar x'' = 0 <;> simp [h])
  have hm2_nn : 0 ≤ m2 := sumVecs_nonneg (fun x'' => by by_cases h : Dstar x'' = -sign (b x'') <;> simp [h])
  -- Pointwise trichotomy on Dstar x'' ∈ {-1, 0, 1}:
  have hDstar_vals : ∀ x'' : Vec (2 * k),
      Dstar x'' = sign (b x'') ∨ Dstar x'' = 0 ∨ Dstar x'' = -sign (b x'') := by
    intro x''
    dsimp only [Dstar, D]
    cases F (consVec false (consVec eps x'')) <;>
      cases F (consVec true (consVec eps x'')) <;>
      cases b x'' <;> simp [sign]
  -- Exact sums for Dstar, Estar:
  have hDstar_sq : sumVecs (fun x'' => Dstar x'' * Dstar x'') = B * B - m1 := by
    have hpw : ∀ x'', Dstar x'' * Dstar x'' = 1 - (if Dstar x'' = 0 then 1 else 0) := by
      intro x''; rcases hDstar_vals x'' with h1 | h2 | h3
      · rw [h1, sign_sq]; cases b x'' <;> decide
      · rw [h2]; decide
      · rw [h3, Int.neg_mul, Int.mul_neg, Int.neg_neg, sign_sq]; cases b x'' <;> decide
    rw [sumVecs_congr hpw, sumVecs_sub, sumVecs_const, Int.mul_one, hpow2k]
  have hDbar_sq : sumVecs (fun x'' => Dbar x'' * Dbar x'') = 2 * t + m1 := by
    have hsplit_D : sumVecs (fun x' => D x' * D x') =
        sumVecs (fun x'' => Dstar x'' * Dstar x'') + sumVecs (fun x'' => Dbar x'' * Dbar x'') := by
      simp only [sumVecs]
      cases heps : eps
      · dsimp only [Dstar, Dbar]; rw [heps]; rfl
      · dsimp only [Dstar, Dbar]; rw [heps]; rw [Int.add_comm]; rfl
    omega
  have hEstar_lin : sumVecs (fun x'' => sign (b x'') * Estar x'') = -delta := by
    have hpw : ∀ x'', sign (b x'') * Estar x'' =
        -(if Dstar x'' = 0 then (1 : Int) else 0) - 2 * (if Dstar x'' = -sign (b x'') then (1 : Int) else 0) := by
      intro x''; dsimp only [Estar]
      rcases hDstar_vals x'' with h1 | h2 | h3
      · rw [h1]; cases b x'' <;> decide
      · rw [h2]; cases b x'' <;> decide
      · rw [h3]; cases b x'' <;> decide
    rw [sumVecs_congr hpw, sumVecs_sub, sumVecs_mul_left]
    have hneg : sumVecs (fun x'' => -(if Dstar x'' = 0 then (1 : Int) else 0)) = -m1 := by
      have := sumVecs_mul_left (-1) (fun x'' => if Dstar x'' = 0 then (1 : Int) else 0)
      simp only [Int.neg_mul, Int.one_mul] at this; exact this
    rw [hneg]; dsimp only [delta, m2]; omega
  have hEstar_sq : sumVecs (fun x'' => Estar x'' * Estar x'') = m1 + 4 * m2 := by
    have hpw : ∀ x'', Estar x'' * Estar x'' =
        (if Dstar x'' = 0 then (1 : Int) else 0) + 4 * (if Dstar x'' = -sign (b x'') then (1 : Int) else 0) := by
      intro x''; dsimp only [Estar]
      rcases hDstar_vals x'' with h1 | h2 | h3
      · rw [h1]; cases b x'' <;> decide
      · rw [h2]; cases b x'' <;> decide
      · rw [h3]; cases b x'' <;> decide
    rw [sumVecs_congr hpw, sumVecs_add, sumVecs_mul_left]
  -- Exact formula for L = 4 * B * (B^2 - delta).
  have hL_delta : L = 4 * B * (B * B - delta) := by
    rw [hL_adj']
    have hsum : sumVecs (fun x' => D x' * walshBool Q1 x') =
        sumVecs (fun x'' => Dstar x'' * (2 * B * sign (b x''))) := by
      simp only [sumVecs]
      cases heps : eps
      · have hoff : ∀ x'', walshBool Q1 (consVec true x'') = 0 := by
          intro x''; have := hWQ1_off x''; rw [heps] at this; exact this
        have hon : ∀ x'', walshBool Q1 (consVec false x'') = 2 * B * sign (b x'') := by
          intro x''; have := hWQ1_on x''; rw [heps] at this; exact this
        have hpart1 : sumVecs (fun x'' => D (consVec true x'') * walshBool Q1 (consVec true x'')) = 0 := by
          rw [sumVecs_congr (fun x'' => by rw [hoff x'', Int.mul_zero]), sumVecs_const, Int.mul_zero]
        rw [hpart1, Int.add_zero]
        apply sumVecs_congr; intro x''; dsimp only [Dstar]; rw [heps, hon x'']
      · have hoff : ∀ x'', walshBool Q1 (consVec false x'') = 0 := by
          intro x''; have := hWQ1_off x''; rw [heps] at this; exact this
        have hon : ∀ x'', walshBool Q1 (consVec true x'') = 2 * B * sign (b x'') := by
          intro x''; have := hWQ1_on x''; rw [heps] at this; exact this
        have hpart0 : sumVecs (fun x'' => D (consVec false x'') * walshBool Q1 (consVec false x'')) = 0 := by
          rw [sumVecs_congr (fun x'' => by rw [hoff x'', Int.mul_zero]), sumVecs_const, Int.mul_zero]
        rw [hpart0, Int.zero_add]
        apply sumVecs_congr; intro x''; dsimp only [Dstar]; rw [heps, hon x'']
    rw [hsum]
    have hfac : sumVecs (fun x'' => Dstar x'' * (2 * B * sign (b x''))) =
        2 * B * sumVecs (fun x'' => sign (b x'') * Dstar x'') := by
      rw [← sumVecs_mul_left]
      apply sumVecs_congr; intro x''
      rw [Int.mul_left_comm (Dstar x'') (2 * B) (sign (b x'')), Int.mul_comm (Dstar x'') (sign (b x''))]
    rw [hfac]
    have hinner : sumVecs (fun x'' => sign (b x'') * Dstar x'') = B * B - delta := by
      have hpw : ∀ x'', sign (b x'') * Dstar x'' = 1 + sign (b x'') * Estar x'' := by
        intro x''; dsimp only [Estar]; rw [Int.mul_sub, sign_sq]; omega
      rw [sumVecs_congr hpw, sumVecs_add, sumVecs_const, Int.mul_one, hpow2k, hEstar_lin]; omega
    rw [hinner, ← Int.mul_assoc, ← Int.mul_assoc]; rfl
  -- Hence 2 * delta ≤ 2 * B^2 - 2 * B - B * t.
  have hdelta_ub : 2 * delta ≤ 2 * (B * B) - 2 * B - B * t := by
    rw [hL_delta] at hL_ge'
    have hmul : 2 * B * (B * (2 + t)) ≤ 2 * B * (2 * (B * B - delta)) := by
      have h1 : 2 * B * (B * (2 + t)) = 2 * B * B * (2 + t) := by rw [← Int.mul_assoc (2 * B) B]
      have h2 : 2 * B * (2 * (B * B - delta)) = 4 * B * (B * B - delta) := by
        rw [← Int.mul_assoc (2 * B) 2, Int.mul_comm (2 * B) 2, ← Int.mul_assoc 2 2 B]; rfl
      omega
    have hle := Int.le_of_mul_le_mul_left hmul (by omega : 0 < 2 * B)
    rw [Int.mul_add] at hle
    omega
  -- 4. Pointwise closure: let u(a'') = s(a'') * W_{Estar}(a'') and z(a'') = s(a'') * W_{Dbar}(a'').
  let u : Vec (2 * k) → Int := fun a'' => s a'' * walsh Estar a''
  let z : Vec (2 * k) → Int := fun a'' => s a'' * walsh Dbar a''
  have hWF1_split : ∀ a'' : Vec (2 * k),
      walshBool F (consVec true (consVec false a'')) * s a'' = 2 * (B + u a'' + z a'') ∧
      walshBool F (consVec true (consVec true a'')) * sign eps * s a'' = 2 * (B + u a'' - z a'') := by
    intro a''
    have hWD_star : walsh Dstar a'' = B * s a'' + walsh Estar a'' := by
      unfold walsh
      have h1 : ∀ x'', Dstar x'' * sign (dot a'' x'') =
          sign (b x'') * sign (dot a'' x'') + Estar x'' * sign (dot a'' x'') := by
        intro x''; dsimp only [Estar]; rw [Int.sub_mul]; omega
      rw [sumVecs_congr h1, sumVecs_add]
      exact congrArg (· + _) (hWb a'')
    have hW1_eq : ∀ c : Bool,
        walshBool F (consVec true (consVec c a'')) =
          2 * (sign (c && eps) * walsh Dstar a'' + sign (c && !eps) * walsh Dbar a'') := by
      intro c
      have hW1 : walshBool F (consVec true (consVec c a'')) = 2 * walsh D (consVec c a'') := by
        unfold walshBool; rw [walsh_cons]
        simp only [sign, ↓reduceIte, Int.neg_mul, Int.one_mul]
        unfold walsh
        have hadd : sumVecs (fun x' => sign (F (consVec false x')) * sign (dot (consVec c a'') x')) +
                    -sumVecs (fun x' => sign (F (consVec true x')) * sign (dot (consVec c a'') x')) =
            sumVecs (fun x' => sign (F (consVec false x')) * sign (dot (consVec c a'') x') -
                               sign (F (consVec true x')) * sign (dot (consVec c a'') x')) := by
          rw [sumVecs_sub]; omega
        change sumVecs (fun x' => sign (F (consVec false x')) * sign (dot (consVec c a'') x')) +
               -sumVecs (fun x' => sign (F (consVec true x')) * sign (dot (consVec c a'') x')) = _
        rw [hadd, ← sumVecs_mul_left]
        apply sumVecs_congr; intro x'; dsimp only [D]
        cases F (consVec false x') <;> cases F (consVec true x') <;> cases dot (consVec c a'') x' <;> rfl
      rw [hW1, walsh_cons]
      congr 1
      cases heps : eps
      · dsimp only [Dstar, Dbar]; rw [heps]
        cases c <;> simp [sign]
      · dsimp only [Dstar, Dbar]; rw [heps]
        cases c <;> simp [sign, Int.add_comm]
    have hs_sq : s a'' * s a'' = 1 := sign_sq _
    constructor
    · rw [hW1_eq false]
      simp only [Bool.false_and, sign, Bool.false_eq_true, ↓reduceIte, Int.one_mul, hWD_star]
      dsimp only [u, z]
      simp only [Int.mul_add, Int.add_mul, Int.mul_assoc, Int.mul_comm (walsh Estar a'') (s a''),
                 Int.mul_comm (walsh Dbar a'') (s a'')]
      rw [hs_sq, Int.mul_one]
    · rw [hW1_eq true]
      simp only [Bool.true_and, hWD_star]
      have hse : sign eps * sign eps = 1 := sign_sq _
      have hsn : sign (!eps) * sign eps = -1 := by cases eps <;> rfl
      dsimp only [u, z]
      have hmul : 2 * (sign eps * (B * s a'' + walsh Estar a'') + sign (!eps) * walsh Dbar a'') * sign eps =
          2 * ((B * s a'' + walsh Estar a'') - walsh Dbar a'') := by
        cases eps <;> simp [sign] <;> omega
      rw [hmul]
      simp only [Int.sub_mul, Int.add_mul, Int.mul_sub, Int.mul_add, Int.mul_assoc,
                 Int.mul_comm (walsh Estar a'') (s a''), Int.mul_comm (walsh Dbar a'') (s a'')]
      rw [hs_sq, Int.mul_one]
  -- From |W_F(1, c, a'')| ≤ 2B + 4, deduce z^2 ≤ 4 - 4u + u^2.
  have hz_sq_le : ∀ a'' : Vec (2 * k), z a'' * z a'' ≤ 4 - 4 * u a'' + u a'' * u a'' := by
    intro a''
    obtain ⟨h0, h1⟩ := hWF1_split a''
    have hc0 := hcap (consVec true (consVec false a''))
    have hc1 := hcap (consVec true (consVec true a''))
    rw [h2B_pow] at hc0 hc1
    have hlo0 : -(B + 2) ≤ B + u a'' + z a'' ∧ B + u a'' + z a'' ≤ B + 2 := by
      have : -(2 * B + 4) ≤ walshBool F (consVec true (consVec false a'')) * s a'' ∧
             walshBool F (consVec true (consVec false a'')) * s a'' ≤ 2 * B + 4 := by
        dsimp only [s]; cases Q1 (consVec false a'') <;> simp [sign] <;> omega
      omega
    have hlo1 : -(B + 2) ≤ B + u a'' - z a'' ∧ B + u a'' - z a'' ≤ B + 2 := by
      have : -(2 * B + 4) ≤ walshBool F (consVec true (consVec true a'')) * sign eps * s a'' ∧
             walshBool F (consVec true (consVec true a'')) * sign eps * s a'' ≤ 2 * B + 4 := by
        dsimp only [s]; cases eps <;> cases Q1 (consVec false a'') <;> simp [sign] <;> omega
      omega
    have hz_le : -(2 - u a'') ≤ z a'' := by omega
    have hz_ge : z a'' ≤ 2 - u a'' := by omega
    have hsq := sq_le_of_abs_le hz_le hz_ge
    have hexp : (2 - u a'') * (2 - u a'') = 4 - 4 * u a'' + u a'' * u a'' := by
      simp only [Int.sub_mul, Int.mul_sub, Int.mul_comm (u a'') 2]; omega
    omega
  -- Sum over all B^2 masks a'' ∈ Vec (2k):
  have hsum_z2 : sumVecs (fun a'' => z a'' * z a'') = B * B * (2 * t + m1) := by
    have hpw : ∀ a'', z a'' * z a'' = walsh Dbar a'' * walsh Dbar a'' := by
      intro a''; dsimp only [z]
      have h1 : (s a'' * walsh Dbar a'') * (s a'' * walsh Dbar a'') =
          (s a'' * s a'') * (walsh Dbar a'' * walsh Dbar a'') := by
        simp only [Int.mul_assoc, Int.mul_left_comm]
      rw [h1, sign_sq, Int.one_mul]
    rw [sumVecs_congr hpw, walsh_parseval, hpow2k, hDbar_sq]
  have hsum_u : sumVecs u = -(B * delta) := by
    have hmul : B * sumVecs u = B * (-(B * delta)) := by
      rw [← sumVecs_mul_left]
      have hpw : ∀ a'', B * u a'' = walshBool b a'' * walsh Estar a'' := by
        intro a''; dsimp only [u]; rw [hWb a'', Int.mul_assoc]
      rw [sumVecs_congr hpw]
      unfold walshBool
      rw [walsh_plancherel, hpow2k, hEstar_lin, Int.mul_neg, Int.mul_neg, Int.mul_assoc]
    exact Int.eq_of_mul_eq_mul_left (Int.ne_of_gt hB_pos) hmul
  have hsum_u2 : sumVecs (fun a'' => u a'' * u a'') = B * B * (m1 + 4 * m2) := by
    have hpw : ∀ a'', u a'' * u a'' = walsh Estar a'' * walsh Estar a'' := by
      intro a''; dsimp only [u]
      have h1 : (s a'' * walsh Estar a'') * (s a'' * walsh Estar a'') =
          (s a'' * s a'') * (walsh Estar a'' * walsh Estar a'') := by
        simp only [Int.mul_assoc, Int.mul_left_comm]
      rw [h1, sign_sq, Int.one_mul]
    rw [sumVecs_congr hpw, walsh_parseval, hpow2k, hEstar_sq]
  -- Key inequality: 2 * B * t ≤ 4 * B + 4 * delta + 4 * B * m2.
  have hmaster : 2 * B * t ≤ 4 * B + 4 * delta + 4 * B * m2 := by
    have hsum := sumVecs_mono hz_sq_le
    rw [hsum_z2, sumVecs_add, sumVecs_sub, sumVecs_const, sumVecs_mul_left,
        hpow2k, hsum_u, hsum_u2] at hsum
    have hmul : B * (2 * B * t) ≤ B * (4 * B + 4 * delta + 4 * B * m2) := by
      simp only [Int.mul_add, Int.mul_neg] at hsum ⊢
      have h1 : B * B * (2 * t) = B * (2 * B * t) := by
        rw [Int.mul_assoc B B (2 * t), Int.mul_left_comm B 2 t, ← Int.mul_assoc 2 B t]
      have h2 : B * B * 4 = B * (4 * B) := by
        rw [Int.mul_assoc B B 4, Int.mul_comm B 4]
      have h3 : 4 * (B * delta) = B * (4 * delta) := Int.mul_left_comm 4 B delta
      have h4 : B * B * (4 * m2) = B * (4 * B * m2) := by
        rw [Int.mul_assoc B B (4 * m2), Int.mul_left_comm B 4 m2, ← Int.mul_assoc 4 B m2]
      omega
    exact Int.le_of_mul_le_mul_left hmul hB_pos
  -- Substitute 2 * m2 ≤ delta and 2 * delta ≤ 2 * B^2 - 2 * B - B * t to get (B + 4) * t ≤ 2 * B^2 + 2 * B.
  have ht_ub_all : (B + 4) * t ≤ 2 * (B * B) + 2 * B := by
    have h1 : 2 * B * t ≤ 4 * B + (B + 2) * (2 * delta) := by
      have h2m : 4 * B * m2 ≤ 2 * B * delta := by
        have hle := Int.mul_le_mul_of_nonneg_left (show 2 * m2 ≤ delta by dsimp only [delta]; omega) (show 0 ≤ 2 * B by omega)
        have hL : 2 * B * (2 * m2) = 4 * B * m2 := by
          rw [← Int.mul_assoc (2 * B) 2 m2, Int.mul_comm (2 * B) 2, ← Int.mul_assoc 2 2 B]; rfl
        omega
      have hexp : (B + 2) * (2 * delta) = 2 * B * delta + 4 * delta := by
        rw [Int.add_mul, ← Int.mul_assoc B 2 delta, Int.mul_comm B 2, ← Int.mul_assoc 2 2 delta]; rfl
      omega
    have h2 := Int.mul_le_mul_of_nonneg_left hdelta_ub (show 0 ≤ B + 2 by omega)
    have hexp : 4 * B + (B + 2) * (2 * (B * B) - 2 * B - B * t) =
        B * (2 * (B * B) + 2 * B) - B * (B + 2) * t := by
      simp only [Int.add_mul, Int.mul_add, Int.mul_sub, Int.sub_mul]
      have a1 : B * (2 * (B * B)) = 2 * (B * (B * B)) := Int.mul_left_comm B 2 (B * B)
      have a2 : 2 * (2 * (B * B)) = 4 * (B * B) := by rw [← Int.mul_assoc]; rfl
      have a3 : B * (2 * B) = 2 * (B * B) := Int.mul_left_comm B 2 B
      have a4 : 2 * (2 * B) = 4 * B := by rw [← Int.mul_assoc]; rfl
      have a5 : B * (B * t) = B * B * t := (Int.mul_assoc B B t).symm
      have a6 : 2 * (B * t) = B * 2 * t := by rw [← Int.mul_assoc 2 B t, Int.mul_comm 2 B]
      have a7 : B * (2 * (B * B)) = 2 * (B * (B * B)) := a1
      rw [a1, a2, a3, a4, a5, a6]; omega
    have h3 : B * ((B + 4) * t) ≤ B * (2 * (B * B) + 2 * B) := by
      have hL : B * ((B + 4) * t) = 2 * B * t + B * (B + 2) * t := by
        simp only [Int.add_mul, Int.mul_add]
        have b1 : B * (B * t) = B * B * t := (Int.mul_assoc B B t).symm
        have b2 : B * (4 * t) = 4 * (B * t) := Int.mul_left_comm B 4 t
        have b3 : 2 * B * t = 2 * (B * t) := Int.mul_assoc 2 B t
        have b4 : B * 2 * t = 2 * (B * t) := by rw [Int.mul_comm B 2, Int.mul_assoc]
        rw [b1, b2, b3, b4]; omega
      omega
    exact Int.le_of_mul_le_mul_left h3 hB_pos
  -- 5. Split: k ≥ 5 (all even n ≥ 12), k = 4 (n = 10), and k = 3 (n = 8).
  by_cases hk5 : 5 ≤ k
  · -- All even n ≥ 12 (B ≥ 32): (2B - 5)(B + 4) = 2B^2 + 3B - 20 > 2B^2 + 2B.
    have hB32 : 32 ≤ B := by
      have : (32 : Int) = (2 : Int) ^ 5 := rfl
      rw [this]; exact two_pow_le_of_le hk5
    have hlo := Int.mul_le_mul_of_nonneg_left ht_lb (show 0 ≤ B + 4 by omega)
    have hexp : (B + 4) * (2 * B - 5) = 2 * (B * B) + 3 * B - 20 := by
      simp only [Int.add_mul, Int.mul_sub, Int.sub_mul]
      have c1 : B * (2 * B) = 2 * (B * B) := Int.mul_left_comm B 2 B
      have c2 : B * 5 = 5 * B := Int.mul_comm B 5
      have c3 : 4 * (2 * B) = 8 * B := by rw [← Int.mul_assoc]; rfl
      rw [c1, c2, c3]; omega
    omega
  · by_cases hk4 : k = 4
    · -- Case k = 4 (n = 10, B = 16):
      subst hk4
      have hB16_eq : B = 16 := rfl
      have ht27 : t = 27 := by omega
      have hwtQ0_240 : hammingWeight Q0 = 240 := by
        rcases hwtQ0_vals with h1 | h2 | h3
        · rw [h1, hB16_eq, ht27] at hH0_bound; omega
        · rw [hB16_eq] at h2; omega
        · rw [h3, hB16_eq, ht27] at hH0_bound; omega
      have hQ0_inv : ∀ a'' : Vec 8, Q0 (consVec true a'') = Q0 (consVec false a'') := by
        have he0_Q0 : isRad Q0 e0 = true := by rw [hrad_same e0]; exact he0_rad
        have hrad_eq := (isRad_true_iff Q0 e0).mp he0_Q0
        have hQ0_e0_eq : Q0 e0 = Q0 zeroVec := by
          apply Classical.byContradiction; intro hne
          have hW0_z : walshBool Q0 zeroVec = 0 := by
            have hsq := walshBool_sq_quadratic Q0 hQ0_quad zeroVec
            have hpw : ∀ v : Vec 9,
                (if isRad Q0 v then sign (xor (dot zeroVec v) (xor (Q0 v) (Q0 zeroVec))) else 0) =
                (if isZeroVec v then (1 : Int) else 0) +
                (if isZeroVec (xorVec v e0) then -1 else 0) := by
              intro v
              by_cases hv0 : isZeroVec v = true
              · have hz := (isZeroVec_true_iff v).mp hv0; subst hz
                have hne1 : isZeroVec (xorVec zeroVec e0) = false := by rw [xorVec_zero_left]; rfl
                simp [hv0, hne1, isRad_zero, dot_zero_left, sign]
              · by_cases hve : isZeroVec (xorVec v e0) = true
                · have hv : v = e0 := by
                    have := (isZeroVec_true_iff _).mp hve
                    have h2 := congrArg (fun w => xorVec w e0) this
                    simp only [xorVec_assoc, xorVec_self, xorVec_zero_right, xorVec_zero_left] at h2
                    exact h2
                  subst hv
                  have hxt : xor (Q0 e0) (Q0 zeroVec) = true := by
                    have hne_bool : ∀ p q : Bool, p ≠ q → xor p q = true := by
                      intro p q h; cases p <;> cases q <;> first | rfl | exact False.elim (h rfl)
                    exact hne_bool _ _ hne
                  simp [hv0, hve, he0_Q0, dot_zero_left, hxt, sign]
                · have hnotrad : isRad Q0 v = false := by
                    rw [hrad_same v]
                    cases hr : isRad Q1 v
                    · rfl
                    · cases hrad_only v hr with
                      | inl hz => rw [hz] at hv0; exact False.elim (hv0 ((isZeroVec_true_iff zeroVec).mpr rfl))
                      | inr he => rw [he, xorVec_self] at hve; exact False.elim (hve ((isZeroVec_true_iff zeroVec).mpr rfl))
                  simp [hv0, hve, hnotrad]
            rw [sumVecs_congr hpw, sumVecs_add, sumVecs_delta_zero,
                sumVecs_xor_shift e0 (fun v => if isZeroVec v then (-1 : Int) else 0),
                sumVecs_delta_zero] at hsq
            have hz : walshBool Q0 zeroVec * walshBool Q0 zeroVec = 0 := by omega
            cases Int.mul_eq_zero.mp hz with | inl h => exact h | inr h => exact h
          have hw := walshBool_zero_eq_wt Q0
          rw [hW0_z, hwtQ0_240] at hw
          have : (2 : Int) ^ 9 = 512 := rfl
          omega
        intro a''
        have h := hrad_eq (consVec false a'')
        have hx : xorVec (consVec false a'') e0 = consVec true a'' := by
          dsimp only [e0]; rw [xorVec_cons, xorVec_zero_right]; rfl
        rw [hx, hQ0_e0_eq, Bool.xor_self] at h
        have hxeq : ∀ p q : Bool, xor p q = false → p = q := by
          intro p q h1; cases p <;> cases q <;> first | rfl | cases h1
        exact hxeq _ _ h
      let Sstar : Vec 8 → Int := fun x'' =>
        if F (consVec false (consVec eps x'')) == F (consVec true (consVec eps x'')) then
          sign (F (consVec false (consVec eps x'')))
        else 0
      have hm1_le2 : m1 ≤ 2 := by
        rw [hB16_eq, ht27] at hmaster hdelta_ub
        dsimp only [delta] at hmaster hdelta_ub
        omega
      have h4_dvd_WS : ∀ a'' : Vec 8, (4 : Int) ∣ walsh Sstar a'' := by
        intro a''
        have h0 := walshBool_mod16_quad (by omega) F hbal (consVec false (consVec false a''))
        have h1 := walshBool_mod16_quad (by omega) F hbal (consVec false (consVec true a''))
        rw [hnorm false (consVec false a'')] at h0
        rw [hnorm false (consVec true a'')] at h1
        simp only [Bool.false_eq_true, ↓reduceIte, Int.zero_add] at h0 h1
        have hqeq : quadMod2 F (consVec false (consVec true a'')) =
            quadMod2 F (consVec false (consVec false a'')) := hQ0_inv a''
        rw [hqeq] at h1
        have hsum16 : (16 : Int) ∣ (walshBool F (consVec false (consVec false a'')) +
                                    walshBool F (consVec false (consVec true a''))) := by
          cases quadMod2 F (consVec false (consVec false a'')) <;> simp at h0 h1 <;> omega
        have hdiff16 : (16 : Int) ∣ (walshBool F (consVec false (consVec false a'')) -
                                     walshBool F (consVec false (consVec true a''))) := by
          cases quadMod2 F (consVec false (consVec false a'')) <;> simp at h0 h1 <;> omega
        have hrel :
            walshBool F (consVec false (consVec false a'')) +
            sign eps * walshBool F (consVec false (consVec true a'')) = 4 * walsh Sstar a'' := by
          let w00 := walsh (fun x => sign (F (consVec false (consVec false x)))) a''
          let w01 := walsh (fun x => sign (F (consVec false (consVec true x)))) a''
          let w10 := walsh (fun x => sign (F (consVec true (consVec false x)))) a''
          let w11 := walsh (fun x => sign (F (consVec true (consVec true x)))) a''
          have hW00 : walshBool F (consVec false (consVec false a'')) = (w00 + w01) + (w10 + w11) := by
            unfold walshBool
            rw [walsh_cons, walsh_cons, walsh_cons]
            have hs0 : sign false = 1 := rfl
            rw [hs0, Int.one_mul, Int.one_mul, Int.one_mul]
          have hW01 : walshBool F (consVec false (consVec true a'')) = (w00 - w01) + (w10 - w11) := by
            unfold walshBool
            rw [walsh_cons, walsh_cons, walsh_cons]
            have hs0 : sign false = 1 := rfl
            have hs1 : sign true = -1 := rfl
            rw [hs0, hs1, Int.one_mul, Int.neg_mul, Int.one_mul]; omega
          rw [hW00, hW01]
          cases heps : eps
          · have hs0 : sign false = 1 := rfl
            rw [hs0, Int.one_mul]
            have hlin : (w00 + w01) + (w10 + w11) + ((w00 - w01) + (w10 - w11)) = 2 * (w00 + w10) := by omega
            rw [hlin]
            dsimp only [w00, w10]; unfold walsh
            rw [← sumVecs_add, ← sumVecs_mul_left, ← sumVecs_mul_left]
            apply sumVecs_congr; intro x''; dsimp only [Sstar]; rw [heps]
            cases F (consVec false (consVec false x'')) <;>
              cases F (consVec true (consVec false x'')) <;> cases dot a'' x'' <;> rfl
          · have hs1 : sign true = -1 := rfl
            rw [hs1, Int.neg_mul, Int.one_mul]
            have hlin : (w00 + w01) + (w10 + w11) + -((w00 - w01) + (w10 - w11)) = 2 * (w01 + w11) := by omega
            rw [hlin]
            dsimp only [w01, w11]; unfold walsh
            rw [← sumVecs_add, ← sumVecs_mul_left, ← sumVecs_mul_left]
            apply sumVecs_congr; intro x''; dsimp only [Sstar]; rw [heps]
            cases F (consVec false (consVec true x'')) <;>
              cases F (consVec true (consVec true x'')) <;> cases dot a'' x'' <;> rfl
        cases heps : eps
        · rw [heps] at hrel; simp only [sign, Bool.false_eq_true, ↓reduceIte, Int.one_mul] at hrel
          obtain ⟨q, hq⟩ := hsum16; exact ⟨q, by omega⟩
        · rw [heps] at hrel; simp only [sign, ↓reduceIte, Int.neg_mul, Int.one_mul] at hrel
          obtain ⟨q, hq⟩ := hdiff16; exact ⟨q, by omega⟩
      have hWS_zero : ∀ a'' : Vec 8, walsh Sstar a'' = 0 := by
        intro a''
        have hlo : -m1 ≤ walsh Sstar a'' := by
          unfold walsh
          have hneg : -m1 = sumVecs (fun x'' => -(if Dstar x'' = 0 then (1 : Int) else 0)) := by
            have := sumVecs_mul_left (-1) (fun x'' => if Dstar x'' = 0 then (1 : Int) else 0)
            simp only [Int.neg_mul, Int.one_mul] at this; exact this.symm
          rw [hneg]; apply sumVecs_mono; intro x''
          dsimp only [Sstar, Dstar, D]
          cases F (consVec false (consVec eps x'')) <;>
            cases F (consVec true (consVec eps x'')) <;> cases dot a'' x'' <;> decide
        have hhi : walsh Sstar a'' ≤ m1 := by
          unfold walsh; apply sumVecs_mono; intro x''
          dsimp only [Sstar, Dstar, D]
          cases F (consVec false (consVec eps x'')) <;>
            cases F (consVec true (consVec eps x'')) <;> cases dot a'' x'' <;> decide
        obtain ⟨q, hq⟩ := h4_dvd_WS a''
        omega
      have hm1_eq0 : m1 = 0 := by
        have hp := walsh_parseval Sstar
        have hz1 : ∀ a'' : Vec 8, walsh Sstar a'' * walsh Sstar a'' = 0 := fun a'' => by
          rw [hWS_zero a'']; rfl
        have hz : sumVecs (fun a'' : Vec 8 => walsh Sstar a'' * walsh Sstar a'') = 0 := by
          rw [sumVecs_congr hz1, sumVecs_const, Int.mul_zero]
        have hSsq : sumVecs (fun x'' : Vec 8 => Sstar x'' * Sstar x'') = m1 := by
          apply sumVecs_congr; intro x''; dsimp only [Sstar, Dstar, D]
          cases F (consVec false (consVec eps x'')) <;>
            cases F (consVec true (consVec eps x'')) <;> decide
        rw [hz, hSsq] at hp
        have : (2 : Int) ^ 8 = 256 := rfl
        omega
      have hm2_eq12 : m2 = 12 := by
        rw [hB16_eq, ht27] at hmaster hdelta_ub
        dsimp only [delta] at hmaster hdelta_ub
        rw [hm1_eq0] at hmaster hdelta_ub
        omega
      have hdelta_24 : delta = 24 := by dsimp only [delta]; omega
      have hL_exact : L = 2 * B * B * (2 + t) := by
        rw [hL_delta, hB16_eq, hdelta_24, ht27]; decide
      have hH1_exact := hL_eq_char hL_exact
      have hDstar_ne0 : ∀ x'' : Vec 8, Dstar x'' ≠ 0 := by
        have hnn : ∀ x'' : Vec 8, 0 ≤ (if Dstar x'' = 0 then (1 : Int) else 0) :=
          fun x'' => by by_cases h : Dstar x'' = 0 <;> simp [h]
        have hall := sumVecs_eq_zero_of_nonneg hnn hm1_eq0
        intro x'' h0
        have := hall x''
        rw [if_pos h0] at this; omega
      have h4_dvd_u : ∀ a'' : Vec 8, (4 : Int) ∣ u a'' := by
        intro a''
        have hE_eq : ∀ x'' : Vec 8,
            Estar x'' * sign (dot a'' x'') =
              2 * (if Dstar x'' = -sign (b x'') then -(sign (b x'') * sign (dot a'' x'')) else 0) := by
          intro x''; dsimp only [Estar]
          rcases hDstar_vals x'' with h1 | h2 | h3
          · have hne : Dstar x'' ≠ -sign (b x'') := by rw [h1]; cases b x'' <;> decide
            rw [if_neg hne, h1]; simp
          · exact False.elim (hDstar_ne0 x'' h2)
          · rw [if_pos h3, h3]; cases b x'' <;> cases dot a'' x'' <;> rfl
        have hpar : (2 : Int) ∣ sumVecs (fun x'' : Vec 8 =>
            if Dstar x'' = -sign (b x'') then -(sign (b x'') * sign (dot a'' x'')) else 0) := by
          let Wsum : Int := sumVecs (fun x'' : Vec 8 =>
            if Dstar x'' = -sign (b x'') then (if !(xor (b x'') (dot a'' x'')) then (-1 : Int) else 0) else 0)
          have hdiff : sumVecs (fun x'' : Vec 8 =>
              (if Dstar x'' = -sign (b x'') then -(sign (b x'') * sign (dot a'' x'')) else 0) -
              (if Dstar x'' = -sign (b x'') then (1 : Int) else 0)) = 2 * Wsum := by
            dsimp only [Wsum]
            rw [← sumVecs_mul_left]
            apply sumVecs_congr; intro x''
            by_cases h : Dstar x'' = -sign (b x'')
            · simp only [h, ↓reduceIte]
              cases b x'' <;> cases dot a'' x'' <;> decide
            · simp [h]
          rw [sumVecs_sub] at hdiff
          have hm2_sub : sumVecs (fun x'' : Vec 8 => if Dstar x'' = -sign (b x'') then (1 : Int) else 0) = 12 := hm2_eq12
          rw [hm2_sub] at hdiff
          refine ⟨6 + Wsum, ?_⟩
          rw [Int.mul_add]
          omega
        have hWE4 : (4 : Int) ∣ walsh Estar a'' := by
          unfold walsh
          rw [sumVecs_congr hE_eq, sumVecs_mul_left]
          obtain ⟨q, hq⟩ := hpar
          exact ⟨q, by omega⟩
        obtain ⟨q, hq⟩ := hWE4
        dsimp only [u]; rw [hq]
        exact ⟨s a'' * q, by rw [Int.mul_left_comm]⟩
      have hu_le24 : ∀ a'' : Vec 8, -24 ≤ u a'' ∧ u a'' ≤ 24 := by
        intro a''
        have hlo : -(2 * m2) ≤ walsh Estar a'' := by
          unfold walsh
          have h1 : -(2 * m2) = sumVecs (fun x'' => -2 * (if Dstar x'' = -sign (b x'') then (1 : Int) else 0)) := by
            rw [sumVecs_mul_left]; omega
          rw [h1]; apply sumVecs_mono; intro x''
          rcases hDstar_vals x'' with h1 | h2 | h3
          · dsimp only [Estar]; rw [h1]
            have hne : sign (b x'') ≠ -sign (b x'') := by cases b x'' <;> decide
            rw [if_neg hne]; simp
          · exact False.elim (hDstar_ne0 x'' h2)
          · dsimp only [Estar]; rw [if_pos h3, h3]
            cases b x'' <;> cases dot a'' x'' <;> decide
        have hhi : walsh Estar a'' ≤ 2 * m2 := by
          unfold walsh
          have h1 : 2 * m2 = sumVecs (fun x'' => 2 * (if Dstar x'' = -sign (b x'') then (1 : Int) else 0)) := by
            rw [sumVecs_mul_left]
          rw [h1]; apply sumVecs_mono; intro x''
          rcases hDstar_vals x'' with h1 | h2 | h3
          · dsimp only [Estar]; rw [h1]
            have hne : sign (b x'') ≠ -sign (b x'') := by cases b x'' <;> decide
            rw [if_neg hne]; simp
          · exact False.elim (hDstar_ne0 x'' h2)
          · dsimp only [Estar]; rw [if_pos h3, h3]
            cases b x'' <;> cases dot a'' x'' <;> decide
        dsimp only [u, s]
        cases Q1 (consVec false a'') <;> simp [sign] <;> omega
      have hu_sq_eq : ∀ a'' : Vec 8, u a'' * u a'' = -16 * u a'' := by
        intro a''
        obtain ⟨h0, h1⟩ := hWF1_split a''
        have he0 := hH1_exact (consVec false a'')
        have he1 := hH1_exact (consVec true a'')
        have hQ1_step : Q1 (consVec true a'') = xor eps (Q1 (consVec false a'')) := by
          have h := (isRad_true_iff Q1 e0).mp he0_rad (consVec false a'')
          have hx : xorVec (consVec false a'') e0 = consVec true a'' := by
            dsimp only [e0]; rw [xorVec_cons, xorVec_zero_right]; rfl
          rw [hx] at h
          exact bool_xor_solve _ _ _ h
        have hA : 16 + u a'' + z a'' = 18 ∨ 16 + u a'' + z a'' = -14 := by
          rw [hB16_eq] at h0
          change walshBool F (consVec true (consVec false a'')) * s a'' = 2 * 2 ^ 4 + 4 ∨
                 walshBool F (consVec true (consVec false a'')) * s a'' = -(2 * 2 ^ 4 - 4) at he0
          rcases he0 with he0a | he0b
          · left; omega
          · right; omega
        have hC : 16 + u a'' - z a'' = 18 ∨ 16 + u a'' - z a'' = -14 := by
          rw [hB16_eq] at h1
          have hs1 : sign (Q1 (consVec true a'')) = sign eps * s a'' := by
            rw [hQ1_step, sign_xor]
          change walshBool F (consVec true (consVec true a'')) * sign (Q1 (consVec true a'')) = 2 * 2 ^ 4 + 4 ∨
                 walshBool F (consVec true (consVec true a'')) * sign (Q1 (consVec true a'')) = -(2 * 2 ^ 4 - 4) at he1
          rw [hs1, ← Int.mul_assoc] at he1
          rcases he1 with he1a | he1b
          · left; omega
          · right; omega
        obtain ⟨q, hq⟩ := h4_dvd_u a''
        have hbd := hu_le24 a''
        have hu_or : u a'' = 0 ∨ u a'' = -16 := by
          rcases hA with hA1 | hA2 <;> rcases hC with hC1 | hC2 <;> omega
        rcases hu_or with hz | hm16
        · rw [hz]; decide
        · rw [hm16]
      have hcontra := sumVecs_congr hu_sq_eq
      rw [hsum_u2, sumVecs_mul_left, hsum_u, hB16_eq, hm1_eq0, hm2_eq12, hdelta_24] at hcontra
      omega
    · -- Case k = 3 (n = 8, B = 8):
      have hk3 : k = 3 := by omega
      subst hk3
      have hB8_eq : B = 8 := rfl
      have ht_range : t = 11 ∨ t = 12 := by
        rw [hB8_eq] at ht_lb ht_ub_all
        omega
      -- 5a. wt(Q0) ∈ {56, 64, 72}; wt(Q0) ≥ 64 ⟹ 48 * 64 ≤ 64 * (4t - 1) ⟹ t ≥ 13, impossible.
      --     Hence wt(Q0) = 56 ≠ 64 ⟹ Q0(1, a'') = Q0(0, a'') everywhere.
      have hwtQ0_56 : hammingWeight Q0 = 56 := by
        rcases hwtQ0_vals with h1 | h2 | h3
        · rw [h1, hB8_eq] at hH0_bound; rcases ht_range with ht | ht <;> rw [ht] at hH0_bound <;> omega
        · rw [hB8_eq] at h2; omega
        · rw [h3, hB8_eq] at hH0_bound; rcases ht_range with ht | ht <;> rw [ht] at hH0_bound <;> omega
      have hQ0_inv : ∀ a'' : Vec 6, Q0 (consVec true a'') = Q0 (consVec false a'') := by
        have he0_Q0 : isRad Q0 e0 = true := by rw [hrad_same e0]; exact he0_rad
        have hrad_eq := (isRad_true_iff Q0 e0).mp he0_Q0
        have hQ0_e0_eq : Q0 e0 = Q0 zeroVec := by
          apply Classical.byContradiction; intro hne
          have hW0_z : walshBool Q0 zeroVec = 0 := by
            have hsq := walshBool_sq_quadratic Q0 hQ0_quad zeroVec
            have hpw : ∀ v : Vec 7,
                (if isRad Q0 v then sign (xor (dot zeroVec v) (xor (Q0 v) (Q0 zeroVec))) else 0) =
                (if isZeroVec v then (1 : Int) else 0) +
                (if isZeroVec (xorVec v e0) then -1 else 0) := by
              intro v
              by_cases hv0 : isZeroVec v = true
              · have hz := (isZeroVec_true_iff v).mp hv0; subst hz
                have hne1 : isZeroVec (xorVec zeroVec e0) = false := by rw [xorVec_zero_left]; rfl
                simp [hv0, hne1, isRad_zero, dot_zero_left, sign]
              · by_cases hve : isZeroVec (xorVec v e0) = true
                · have hv : v = e0 := by
                    have := (isZeroVec_true_iff _).mp hve
                    have h2 := congrArg (fun w => xorVec w e0) this
                    simp only [xorVec_assoc, xorVec_self, xorVec_zero_right, xorVec_zero_left] at h2
                    exact h2
                  subst hv
                  have hxt : xor (Q0 e0) (Q0 zeroVec) = true := by
                    have hne_bool : ∀ p q : Bool, p ≠ q → xor p q = true := by
                      intro p q h; cases p <;> cases q <;> first | rfl | exact False.elim (h rfl)
                    exact hne_bool _ _ hne
                  simp [hv0, hve, he0_Q0, dot_zero_left, hxt, sign]
                · have hnotrad : isRad Q0 v = false := by
                    rw [hrad_same v]
                    cases hr : isRad Q1 v
                    · rfl
                    · cases hrad_only v hr with
                      | inl hz => rw [hz] at hv0; exact False.elim (hv0 ((isZeroVec_true_iff zeroVec).mpr rfl))
                      | inr he => rw [he, xorVec_self] at hve; exact False.elim (hve ((isZeroVec_true_iff zeroVec).mpr rfl))
                  simp [hv0, hve, hnotrad]
            rw [sumVecs_congr hpw, sumVecs_add, sumVecs_delta_zero,
                sumVecs_xor_shift e0 (fun v => if isZeroVec v then (-1 : Int) else 0),
                sumVecs_delta_zero] at hsq
            have hz : walshBool Q0 zeroVec * walshBool Q0 zeroVec = 0 := by omega
            cases Int.mul_eq_zero.mp hz with | inl h => exact h | inr h => exact h
          have hw := walshBool_zero_eq_wt Q0
          rw [hW0_z, hwtQ0_56] at hw
          have : (2 : Int) ^ 7 = 128 := rfl
          omega
        intro a''
        have h := hrad_eq (consVec false a'')
        have hx : xorVec (consVec false a'') e0 = consVec true a'' := by
          dsimp only [e0]; rw [xorVec_cons, xorVec_zero_right]; rfl
        rw [hx, hQ0_e0_eq, Bool.xor_self] at h
        have hxeq : ∀ p q : Bool, xor p q = false → p = q := by
          intro p q h1; cases p <;> cases q <;> first | rfl | cases h1
        exact hxeq _ _ h
      -- 5b. Hence 4 ∣ W_{Sstar}(a'') for all a'' : Vec 6, so m1 ≤ 2 ⟹ m1 = 0.
      let Sstar : Vec 6 → Int := fun x'' =>
        if F (consVec false (consVec eps x'')) == F (consVec true (consVec eps x'')) then
          sign (F (consVec false (consVec eps x'')))
        else 0
      have h4_dvd_WS : ∀ a'' : Vec 6, (4 : Int) ∣ walsh Sstar a'' := by
        intro a''
        have h0 := walshBool_mod16_quad (by omega) F hbal (consVec false (consVec false a''))
        have h1 := walshBool_mod16_quad (by omega) F hbal (consVec false (consVec true a''))
        rw [hnorm false (consVec false a'')] at h0
        rw [hnorm false (consVec true a'')] at h1
        simp only [Bool.false_eq_true, ↓reduceIte, Int.zero_add] at h0 h1
        have hqeq : quadMod2 F (consVec false (consVec true a'')) =
            quadMod2 F (consVec false (consVec false a'')) := hQ0_inv a''
        rw [hqeq] at h1
        have hsum16 : (16 : Int) ∣ (walshBool F (consVec false (consVec false a'')) +
                                    walshBool F (consVec false (consVec true a''))) := by
          cases quadMod2 F (consVec false (consVec false a'')) <;> simp at h0 h1 <;> omega
        have hdiff16 : (16 : Int) ∣ (walshBool F (consVec false (consVec false a'')) -
                                     walshBool F (consVec false (consVec true a''))) := by
          cases quadMod2 F (consVec false (consVec false a'')) <;> simp at h0 h1 <;> omega
        have hrel :
            walshBool F (consVec false (consVec false a'')) +
            sign eps * walshBool F (consVec false (consVec true a'')) = 4 * walsh Sstar a'' := by
          let w00 := walsh (fun x => sign (F (consVec false (consVec false x)))) a''
          let w01 := walsh (fun x => sign (F (consVec false (consVec true x)))) a''
          let w10 := walsh (fun x => sign (F (consVec true (consVec false x)))) a''
          let w11 := walsh (fun x => sign (F (consVec true (consVec true x)))) a''
          have hW00 : walshBool F (consVec false (consVec false a'')) = (w00 + w01) + (w10 + w11) := by
            unfold walshBool
            rw [walsh_cons, walsh_cons, walsh_cons]
            have hs0 : sign false = 1 := rfl
            rw [hs0, Int.one_mul, Int.one_mul, Int.one_mul]
          have hW01 : walshBool F (consVec false (consVec true a'')) = (w00 - w01) + (w10 - w11) := by
            unfold walshBool
            rw [walsh_cons, walsh_cons, walsh_cons]
            have hs0 : sign false = 1 := rfl
            have hs1 : sign true = -1 := rfl
            rw [hs0, hs1, Int.one_mul, Int.neg_mul, Int.one_mul]; omega
          rw [hW00, hW01]
          cases heps : eps
          · have hs0 : sign false = 1 := rfl
            rw [hs0, Int.one_mul]
            have hlin : (w00 + w01) + (w10 + w11) + ((w00 - w01) + (w10 - w11)) = 2 * (w00 + w10) := by omega
            rw [hlin]
            dsimp only [w00, w10]; unfold walsh
            rw [← sumVecs_add, ← sumVecs_mul_left, ← sumVecs_mul_left]
            apply sumVecs_congr; intro x''; dsimp only [Sstar]; rw [heps]
            cases F (consVec false (consVec false x'')) <;>
              cases F (consVec true (consVec false x'')) <;> cases dot a'' x'' <;> rfl
          · have hs1 : sign true = -1 := rfl
            rw [hs1, Int.neg_mul, Int.one_mul]
            have hlin : (w00 + w01) + (w10 + w11) + -((w00 - w01) + (w10 - w11)) = 2 * (w01 + w11) := by omega
            rw [hlin]
            dsimp only [w01, w11]; unfold walsh
            rw [← sumVecs_add, ← sumVecs_mul_left, ← sumVecs_mul_left]
            apply sumVecs_congr; intro x''; dsimp only [Sstar]; rw [heps]
            cases F (consVec false (consVec true x'')) <;>
              cases F (consVec true (consVec true x'')) <;> cases dot a'' x'' <;> rfl
        cases heps : eps
        · rw [heps] at hrel; simp only [sign, Bool.false_eq_true, ↓reduceIte, Int.one_mul] at hrel
          obtain ⟨q, hq⟩ := hsum16; exact ⟨q, by omega⟩
        · rw [heps] at hrel; simp only [sign, ↓reduceIte, Int.neg_mul, Int.one_mul] at hrel
          obtain ⟨q, hq⟩ := hdiff16; exact ⟨q, by omega⟩
      have hm1_le2_imp_0 : m1 ≤ 2 → m1 = 0 := by
        intro hm1_le2
        have hWS_zero : ∀ a'' : Vec 6, walsh Sstar a'' = 0 := by
          intro a''
          have hlo : -m1 ≤ walsh Sstar a'' := by
            unfold walsh
            have hneg : -m1 = sumVecs (fun x'' => -(if Dstar x'' = 0 then (1 : Int) else 0)) := by
              have := sumVecs_mul_left (-1) (fun x'' => if Dstar x'' = 0 then (1 : Int) else 0)
              simp only [Int.neg_mul, Int.one_mul] at this; exact this.symm
            rw [hneg]; apply sumVecs_mono; intro x''
            dsimp only [Sstar, Dstar, D]
            cases F (consVec false (consVec eps x'')) <;>
              cases F (consVec true (consVec eps x'')) <;> cases dot a'' x'' <;> decide
          have hhi : walsh Sstar a'' ≤ m1 := by
            unfold walsh; apply sumVecs_mono; intro x''
            dsimp only [Sstar, Dstar, D]
            cases F (consVec false (consVec eps x'')) <;>
              cases F (consVec true (consVec eps x'')) <;> cases dot a'' x'' <;> decide
          obtain ⟨q, hq⟩ := h4_dvd_WS a''
          omega
        have hp := walsh_parseval Sstar
        have hz1 : ∀ a'' : Vec 6, walsh Sstar a'' * walsh Sstar a'' = 0 := fun a'' => by
          rw [hWS_zero a'']; rfl
        have hz : sumVecs (fun a'' : Vec 6 => walsh Sstar a'' * walsh Sstar a'') = 0 := by
          rw [sumVecs_congr hz1, sumVecs_const, Int.mul_zero]
        have hSsq : sumVecs (fun x'' : Vec 6 => Sstar x'' * Sstar x'') = m1 := by
          apply sumVecs_congr; intro x''; dsimp only [Sstar, Dstar, D]
          cases F (consVec false (consVec eps x'')) <;>
            cases F (consVec true (consVec eps x'')) <;> decide
        rw [hz, hSsq] at hp
        have : (2 : Int) ^ 6 = 64 := rfl
        omega
      -- 5c. Exact mod-16 discretization on H_1: (u(a''), |z(a'')|) ∈ {(-10,4), (-6,0), (-6,8), (-2,4), (2,0)}.
      have hu_le_delta : ∀ a'' : Vec 6, -delta ≤ u a'' ∧ u a'' ≤ delta := by
        intro a''
        have hlo : -delta ≤ walsh Estar a'' := by
          unfold walsh
          have h1 : -delta = sumVecs (fun x'' =>
              -(if Dstar x'' = 0 then (1 : Int) else 0) -
              2 * (if Dstar x'' = -sign (b x'') then (1 : Int) else 0)) := by
            rw [sumVecs_sub, sumVecs_mul_left]
            have hneg : sumVecs (fun x'' => -(if Dstar x'' = 0 then (1 : Int) else 0)) = -m1 := by
              have := sumVecs_mul_left (-1) (fun x'' => if Dstar x'' = 0 then (1 : Int) else 0)
              simp only [Int.neg_mul, Int.one_mul] at this; exact this
            rw [hneg]; dsimp only [delta, m2]; omega
          rw [h1]; apply sumVecs_mono; intro x''
          dsimp only [Estar]
          rcases hDstar_vals x'' with h1 | h2 | h3
          · rw [h1]; cases b x'' <;> cases dot a'' x'' <;> decide
          · rw [h2]; cases b x'' <;> cases dot a'' x'' <;> decide
          · rw [h3]; cases b x'' <;> cases dot a'' x'' <;> decide
        have hhi : walsh Estar a'' ≤ delta := by
          unfold walsh
          have h1 : delta = sumVecs (fun x'' =>
              (if Dstar x'' = 0 then (1 : Int) else 0) +
              2 * (if Dstar x'' = -sign (b x'') then (1 : Int) else 0)) := by
            rw [sumVecs_add, sumVecs_mul_left]
          rw [h1]; apply sumVecs_mono; intro x''
          dsimp only [Estar]
          rcases hDstar_vals x'' with h1 | h2 | h3
          · rw [h1]; cases b x'' <;> cases dot a'' x'' <;> decide
          · rw [h2]; cases b x'' <;> cases dot a'' x'' <;> decide
          · rw [h3]; cases b x'' <;> cases dot a'' x'' <;> decide
        dsimp only [u, s]
        cases Q1 (consVec false a'') <;> simp [sign] <;> omega
      have hdelta_le12 : delta ≤ 12 := by
        rw [hB8_eq] at hdelta_ub
        rcases ht_range with ht | ht <;> rw [ht] at hdelta_ub <;> omega
      have hQ1_step : ∀ a'' : Vec 6, Q1 (consVec true a'') = xor eps (Q1 (consVec false a'')) := by
        intro a''
        have h := (isRad_true_iff Q1 e0).mp he0_rad (consVec false a'')
        have hx : xorVec (consVec false a'') e0 = consVec true a'' := by
          dsimp only [e0]; rw [xorVec_cons, xorVec_zero_right]; rfl
        rw [hx] at h
        exact bool_xor_solve _ _ _ h
      have huz_5pts : ∀ a'' : Vec 6,
          (u a'' = -10 ∧ (z a'' = 4 ∨ z a'' = -4)) ∨
          (u a'' = -6 ∧ z a'' = 0) ∨
          (u a'' = -6 ∧ (z a'' = 8 ∨ z a'' = -8)) ∨
          (u a'' = -2 ∧ (z a'' = 4 ∨ z a'' = -4)) ∨
          (u a'' = 2 ∧ z a'' = 0) := by
        intro a''
        obtain ⟨hsp0, hsp1⟩ := hWF1_split a''
        rw [hB8_eq] at hsp0 hsp1
        have hm0 := walshBool_mod16_quad (by omega) F hbal (consVec true (consVec false a''))
        have hm1 := walshBool_mod16_quad (by omega) F hbal (consVec true (consVec true a''))
        rw [hnorm true (consVec false a'')] at hm0
        rw [hnorm true (consVec true a'')] at hm1
        simp only [↓reduceIte] at hm0 hm1
        have hc0 := hcap (consVec true (consVec false a''))
        have hc1 := hcap (consVec true (consVec true a''))
        have h20 : (2 : Int) ^ (3 + 1) + 4 = 20 := rfl
        rw [h20] at hc0 hc1
        have hA : 8 + u a'' + z a'' = -6 ∨ 8 + u a'' + z a'' = 2 ∨ 8 + u a'' + z a'' = 10 := by
          have hq : Q1 (consVec false a'') = quadMod2 F (consVec true (consVec false a'')) := rfl
          dsimp only [s] at hsp0
          rw [hq] at hsp0
          cases hqb : quadMod2 F (consVec true (consVec false a'')) <;>
            rw [hqb] at hm0 hsp0 <;> simp [sign] at hm0 hsp0 <;> omega
        have hC : 8 + u a'' - z a'' = -6 ∨ 8 + u a'' - z a'' = 2 ∨ 8 + u a'' - z a'' = 10 := by
          have hs1 : sign (Q1 (consVec true a'')) = sign eps * s a'' := by
            rw [hQ1_step a'', sign_xor]
          have hsp1' : walshBool F (consVec true (consVec true a'')) * sign (Q1 (consVec true a'')) =
              2 * (8 + u a'' - z a'') := by
            rw [hs1, ← Int.mul_assoc]; exact hsp1
          have hq : Q1 (consVec true a'') = quadMod2 F (consVec true (consVec true a'')) := rfl
          rw [hq] at hsp1'
          cases hqb : quadMod2 F (consVec true (consVec true a'')) <;>
            rw [hqb] at hm1 hsp1' <;> simp [sign] at hm1 hsp1' <;> omega
        have hbd := hu_le_delta a''
        rcases hA with hA | hA | hA <;> rcases hC with hC | hC | hC <;> omega
      -- Helper: m1 = 0 and m2 = 4 implies 4 ∣ u zeroVec, contradicting u zeroVec % 4 = 2.
      have hno_m1_0_m2_4 : m1 = 0 → m2 = 4 → False := by
        intro hm1_0 hm2_4
        have hDstar_ne0 : ∀ x'' : Vec 6, Dstar x'' ≠ 0 := by
          have hnn : ∀ x'' : Vec 6, 0 ≤ (if Dstar x'' = 0 then (1 : Int) else 0) :=
            fun x'' => by by_cases h : Dstar x'' = 0 <;> simp [h]
          have hall := sumVecs_eq_zero_of_nonneg hnn hm1_0
          intro x'' h0
          have := hall x''
          rw [if_pos h0] at this; omega
        have hE_eq : ∀ x'' : Vec 6,
            Estar x'' * sign (dot zeroVec x'') =
              2 * (if Dstar x'' = -sign (b x'') then -(sign (b x'') * sign (dot zeroVec x'')) else 0) := by
          intro x''; dsimp only [Estar]
          rcases hDstar_vals x'' with h1 | h2 | h3
          · have hne : Dstar x'' ≠ -sign (b x'') := by rw [h1]; cases b x'' <;> decide
            rw [if_neg hne, h1]; simp
          · exact False.elim (hDstar_ne0 x'' h2)
          · rw [if_pos h3, h3]; cases b x'' <;> cases dot zeroVec x'' <;> rfl
        have hpar : (2 : Int) ∣ sumVecs (fun x'' : Vec 6 =>
            if Dstar x'' = -sign (b x'') then -(sign (b x'') * sign (dot zeroVec x'')) else 0) := by
          let Wsum : Int := sumVecs (fun x'' : Vec 6 =>
            if Dstar x'' = -sign (b x'') then (if !(xor (b x'') (dot zeroVec x'')) then (-1 : Int) else 0) else 0)
          have hdiff : sumVecs (fun x'' : Vec 6 =>
              (if Dstar x'' = -sign (b x'') then -(sign (b x'') * sign (dot zeroVec x'')) else 0) -
              (if Dstar x'' = -sign (b x'') then (1 : Int) else 0)) = 2 * Wsum := by
            dsimp only [Wsum]
            rw [← sumVecs_mul_left]
            apply sumVecs_congr; intro x''
            by_cases h : Dstar x'' = -sign (b x'')
            · simp only [h, ↓reduceIte]
              cases b x'' <;> cases dot zeroVec x'' <;> decide
            · simp [h]
          rw [sumVecs_sub] at hdiff
          have hm2_sub : sumVecs (fun x'' : Vec 6 => if Dstar x'' = -sign (b x'') then (1 : Int) else 0) = 4 := hm2_4
          rw [hm2_sub] at hdiff
          refine ⟨2 + Wsum, ?_⟩
          rw [Int.mul_add]; omega
        have hWE4 : (4 : Int) ∣ walsh Estar zeroVec := by
          unfold walsh
          rw [sumVecs_congr hE_eq, sumVecs_mul_left]
          obtain ⟨q, hq⟩ := hpar
          exact ⟨q, by omega⟩
        obtain ⟨q, hq⟩ := hWE4
        have h4u : (4 : Int) ∣ u zeroVec := by
          dsimp only [u]; rw [hq]; exact ⟨s zeroVec * q, by rw [Int.mul_left_comm]⟩
        obtain ⟨q', hq'⟩ := h4u
        have h5 := huz_5pts zeroVec
        omega
      -- 5d. Pointwise Farkas-type inequality: 3 * z^2 + 5 * u^2 + 44 * u ≤ 108 on all 5 allowed pairs.
      have hfarkas_pw : ∀ a'' : Vec 6,
          3 * (z a'' * z a'') + 5 * (u a'' * u a'') + 44 * u a'' ≤ 108 := by
        intro a''
        rcases huz_5pts a'' with ⟨hu, hz | hz⟩ | ⟨hu, hz⟩ | ⟨hu, hz | hz⟩ | ⟨hu, hz | hz⟩ | ⟨hu, hz⟩ <;>
          rw [hu, hz] <;> decide
      have hfarkas_sum : 12 * t + 5 * m1 + 18 * m2 ≤ 216 := by
        have hs := sumVecs_mono hfarkas_pw
        rw [sumVecs_add, sumVecs_add, sumVecs_mul_left, sumVecs_mul_left, sumVecs_mul_left,
            sumVecs_const, hsum_z2, hsum_u2, hsum_u, hB8_eq] at hs
        have h64 : (2 : Int) ^ 6 = 64 := rfl
        rw [h64] at hs
        dsimp only [delta] at hs
        omega
      -- 5e. Eliminate t = 12 and force (t, m1, m2) = (11, 6, 3) uniquely.
      have ht11 : t = 11 := by
        rcases ht_range with ht | ht
        · exact ht
        · exfalso
          rw [hB8_eq, ht] at hdelta_ub hmaster
          dsimp only [delta] at hdelta_ub hmaster
          exact hno_m1_0_m2_4 (by omega) (by omega)
      have hm12_unique : m1 = 6 ∧ m2 = 3 := by
        rw [hB8_eq, ht11] at hdelta_ub hmaster
        rw [ht11] at hfarkas_sum
        dsimp only [delta] at hdelta_ub hmaster
        have hm2_cases : m2 = 3 ∨ m2 = 4 := by omega
        rcases hm2_cases with hm2_3 | hm2_4
        · exact ⟨by omega, hm2_3⟩
        · exfalso
          have hm1_0 : m1 = 0 := hm1_le2_imp_0 (by omega)
          exact hno_m1_0_m2_4 hm1_0 hm2_4
      obtain ⟨hm1_6, hm2_3⟩ := hm12_unique
      have hdelta_12 : delta = 12 := by dsimp only [delta]; omega
      -- 5f. At (t = 11, m1 = 6, m2 = 3), both hz_sq_le and hfarkas_pw hold with equality everywhere.
      --     Hence u(a'') ∈ {-6, 2} for all a'' : Vec 6.
      have hz_sq_eq : ∀ a'' : Vec 6, z a'' * z a'' = 4 - 4 * u a'' + u a'' * u a'' := by
        have hnn : ∀ a'' : Vec 6, 0 ≤ (4 - 4 * u a'' + u a'' * u a'') - z a'' * z a'' :=
          fun a'' => by have := hz_sq_le a''; omega
        have hsz : sumVecs (fun a'' : Vec 6 => (4 - 4 * u a'' + u a'' * u a'') - z a'' * z a'') = 0 := by
          rw [sumVecs_sub, sumVecs_add, sumVecs_sub, sumVecs_const, sumVecs_mul_left,
              hsum_u, hsum_u2, hsum_z2, hB8_eq, ht11, hm1_6, hm2_3, hdelta_12]
          decide
        intro a''
        have := sumVecs_eq_zero_of_nonneg hnn hsz a''
        omega
      have hfarkas_eq : ∀ a'' : Vec 6,
          3 * (z a'' * z a'') + 5 * (u a'' * u a'') + 44 * u a'' = 108 := by
        have hnn : ∀ a'' : Vec 6, 0 ≤ 108 - (3 * (z a'' * z a'') + 5 * (u a'' * u a'') + 44 * u a'') :=
          fun a'' => by have := hfarkas_pw a''; omega
        have hsz : sumVecs (fun a'' : Vec 6 =>
            108 - (3 * (z a'' * z a'') + 5 * (u a'' * u a'') + 44 * u a'')) = 0 := by
          rw [sumVecs_sub, sumVecs_const, sumVecs_add, sumVecs_add,
              sumVecs_mul_left, sumVecs_mul_left, sumVecs_mul_left,
              hsum_z2, hsum_u2, hsum_u, hB8_eq, ht11, hm1_6, hm2_3, hdelta_12]
          decide
        intro a''
        have := sumVecs_eq_zero_of_nonneg hnn hsz a''
        omega
      have hu_two_vals : ∀ a'' : Vec 6, u a'' = -6 ∨ u a'' = 2 := by
        intro a''
        have he1 := hz_sq_eq a''
        have he2 := hfarkas_eq a''
        rcases huz_5pts a'' with ⟨hu, hz | hz⟩ | ⟨hu, hz⟩ | ⟨hu, hz | hz⟩ | ⟨hu, hz | hz⟩ | ⟨hu, hz⟩ <;>
          rw [hu, hz] at he1 he2 <;> omega
      -- 5g. Define Boolean g : Vec 6 → Bool with 4 * sign(g a'') = walsh Estar a'' + 2 * s a''.
      --     Walsh inversion gives walshBool g x'' = 16 * Estar x'' + 4 * sign(b x''),
      --     so |W_g| = 28 on exactly m2 = 3 points and |W_g| ≤ 12 on all other 61 points.
      let g : Vec 6 → Bool := fun a'' => decide (s a'' * (u a'' + 2) < 0)
      have hg_eq : ∀ a'' : Vec 6, 4 * sign (g a'') = walsh Estar a'' + 2 * s a'' := by
        intro a''
        have hsu : s a'' * (u a'' + 2) = walsh Estar a'' + 2 * s a'' := by
          dsimp only [u]
          rw [Int.mul_add, ← Int.mul_assoc, sign_sq, Int.one_mul, Int.mul_comm (s a'') 2]
        rw [← hsu]
        dsimp only [g]
        rcases hu_two_vals a'' with hu | hu <;> rw [hu] <;>
          dsimp only [s] <;> cases Q1 (consVec false a'') <;> decide
      have hws : ∀ x'' : Vec 6, walsh s x'' = 8 * sign (b x'') := by
        intro x''
        have hinv := walsh_inversion (fun y => sign (b y)) x''
        have h8 : walsh (walsh (fun y => sign (b y))) x'' = 8 * walsh s x'' := by
          unfold walsh
          rw [← sumVecs_mul_left]
          apply sumVecs_congr; intro a''
          have hb := hWb a''
          rw [hB8_eq] at hb
          change walshBool b a'' * sign (dot x'' a'') = 8 * (s a'' * sign (dot x'' a''))
          rw [hb, Int.mul_assoc]
        rw [h8] at hinv
        have h64 : (2 : Int) ^ 6 = 64 := rfl
        rw [h64] at hinv
        omega
      have hWg : ∀ x'' : Vec 6, walshBool g x'' = 16 * Estar x'' + 4 * sign (b x'') := by
        intro x''
        have h4 : 4 * walshBool g x'' = 64 * Estar x'' + 16 * sign (b x'') := by
          unfold walshBool walsh
          rw [← sumVecs_mul_left]
          have hpw : ∀ a'' : Vec 6,
              4 * (sign (g a'') * sign (dot x'' a'')) =
              walsh Estar a'' * sign (dot x'' a'') + 2 * (s a'' * sign (dot x'' a'')) := by
            intro a''
            rw [← Int.mul_assoc, hg_eq a'', Int.add_mul, Int.mul_assoc]
          rw [sumVecs_congr hpw, sumVecs_add, sumVecs_mul_left]
          change walsh (walsh Estar) x'' + 2 * walsh s x'' = _
          rw [walsh_inversion Estar x'', hws x'']
          have h64 : (2 : Int) ^ 6 = 64 := rfl
          rw [h64]; omega
        omega
      -- 5h. Extract the 3 distinct points x1, x2, x3 where Dstar x'' = -sign (b x''),
      --     take x4 = x1 ⊕ x2 ⊕ x3, and rule this out via the 4-coset bound (72 ≤ 64).
      let P : Vec 6 → Bool := fun x'' => decide (Dstar x'' = -sign (b x''))
      have hP_sum : sumVecs (fun x'' : Vec 6 => if P x'' then (1 : Int) else 0) = 3 := by
        have hpw : ∀ x'' : Vec 6,
            (if P x'' then (1 : Int) else 0) = (if Dstar x'' = -sign (b x'') then (1 : Int) else 0) := by
          intro x''; dsimp only [P]
          by_cases h : Dstar x'' = -sign (b x'') <;> simp [h]
        rw [sumVecs_congr hpw]; exact hm2_3
      -- Find x1 with P x1 = true
      have hex1 : ∃ x1 : Vec 6, P x1 = true := by
        apply Classical.byContradiction; intro hno
        have hz : sumVecs (fun x'' : Vec 6 => if P x'' then (1 : Int) else 0) = 0 := by
          have h0 : ∀ x'' : Vec 6, (if P x'' then (1 : Int) else 0) = 0 := by
            intro x''; cases hp : P x'' with
            | false => rfl
            | true => exact False.elim (hno ⟨x'', hp⟩)
          rw [sumVecs_congr h0, sumVecs_const, Int.mul_zero]
        omega
      obtain ⟨x1, hx1⟩ := hex1
      -- Find x2 ≠ x1 with P x2 = true
      have hex2 : ∃ x2 : Vec 6, x2 ≠ x1 ∧ P x2 = true := by
        apply Classical.byContradiction; intro hno
        have hle : sumVecs (fun x'' : Vec 6 => if P x'' then (1 : Int) else 0) ≤
            sumVecs (fun x'' : Vec 6 => if isZeroVec (xorVec x'' x1) then (1 : Int) else 0) := by
          apply sumVecs_mono; intro x''
          by_cases heq : x'' = x1
          · subst heq; rw [xorVec_self, (isZeroVec_true_iff zeroVec).mpr rfl]; cases P x'' <;> decide
          · cases hp : P x'' with
            | false => cases isZeroVec (xorVec x'' x1) <;> decide
            | true => exact False.elim (hno ⟨x'', heq, hp⟩)
        rw [sumVecs_xor_shift x1 (fun v => if isZeroVec v then (1 : Int) else 0),
            sumVecs_delta_zero, hP_sum] at hle
        omega
      obtain ⟨x2, hx21, hx2⟩ := hex2
      -- Find x3 distinct from x1, x2 with P x3 = true
      have hex3 : ∃ x3 : Vec 6, x3 ≠ x1 ∧ x3 ≠ x2 ∧ P x3 = true := by
        apply Classical.byContradiction; intro hno
        have hle : sumVecs (fun x'' : Vec 6 => if P x'' then (1 : Int) else 0) ≤
            sumVecs (fun x'' : Vec 6 =>
              (if isZeroVec (xorVec x'' x1) then (1 : Int) else 0) +
              (if isZeroVec (xorVec x'' x2) then (1 : Int) else 0)) := by
          apply sumVecs_mono; intro x''
          by_cases h1 : x'' = x1
          · subst h1; rw [xorVec_self, (isZeroVec_true_iff zeroVec).mpr rfl]
            cases P x'' <;> cases isZeroVec (xorVec x'' x2) <;> decide
          · by_cases h2 : x'' = x2
            · subst h2; rw [xorVec_self, (isZeroVec_true_iff zeroVec).mpr rfl]
              cases P x'' <;> cases isZeroVec (xorVec x'' x1) <;> decide
            · cases hp : P x'' with
              | false => cases isZeroVec (xorVec x'' x1) <;> cases isZeroVec (xorVec x'' x2) <;> decide
              | true => exact False.elim (hno ⟨x'', h1, h2, hp⟩)
        rw [sumVecs_add,
            sumVecs_xor_shift x1 (fun v => if isZeroVec v then (1 : Int) else 0),
            sumVecs_delta_zero,
            sumVecs_xor_shift x2 (fun v => if isZeroVec v then (1 : Int) else 0),
            sumVecs_delta_zero, hP_sum] at hle
        omega
      obtain ⟨x3, hx31, hx32, hx3⟩ := hex3
      -- Set x4 = x1 ⊕ x2 ⊕ x3; verify x4 is distinct from x1, x2, x3, hence P x4 = false.
      let x4 : Vec 6 := xorVec (xorVec x1 x2) x3
      have hx41 : x4 ≠ x1 := by
        intro heq
        have h1 := congrArg (fun v => xorVec x1 v) heq
        simp only [x4, ← xorVec_assoc, xorVec_self, xorVec_zero_left] at h1
        have h2 := congrArg (fun v => xorVec v x3) h1
        simp only [xorVec_assoc, xorVec_self, xorVec_zero_right, xorVec_zero_left] at h2
        exact hx32 h2.symm
      have hx42 : x4 ≠ x2 := by
        intro heq
        have h1 := congrArg (fun v => xorVec x2 v) heq
        dsimp only [x4] at h1
        have hcomm : xorVec x2 (xorVec (xorVec x1 x2) x3) = xorVec x1 x3 := by
          funext i; dsimp only [xorVec]; cases x1 i <;> cases x2 i <;> cases x3 i <;> rfl
        rw [hcomm, xorVec_self] at h1
        have h2 := congrArg (fun v => xorVec v x3) h1
        simp only [xorVec_assoc, xorVec_self, xorVec_zero_right, xorVec_zero_left] at h2
        exact hx31 h2.symm
      have hx43 : x4 ≠ x3 := by
        intro heq
        have h1 := congrArg (fun v => xorVec v x3) heq
        simp only [x4, xorVec_assoc, xorVec_self, xorVec_zero_right] at h1
        have h2 := congrArg (fun v => xorVec v x2) h1
        simp only [xorVec_assoc, xorVec_self, xorVec_zero_right, xorVec_zero_left] at h2
        exact hx21 h2.symm
      have hPx4 : P x4 = false := by
        cases hp4 : P x4
        · rfl
        · exfalso
          have hge : sumVecs (fun x'' : Vec 6 =>
              (if isZeroVec (xorVec x'' x1) then (1 : Int) else 0) +
              (if isZeroVec (xorVec x'' x2) then (1 : Int) else 0) +
              (if isZeroVec (xorVec x'' x3) then (1 : Int) else 0) +
              (if isZeroVec (xorVec x'' x4) then (1 : Int) else 0)) ≤
              sumVecs (fun x'' : Vec 6 => if P x'' then (1 : Int) else 0) := by
            apply sumVecs_mono; intro x''
            have hiff : ∀ y : Vec 6, isZeroVec (xorVec x'' y) = true ↔ x'' = y := by
              intro y; constructor
              · intro hz
                have h0 := (isZeroVec_true_iff _).mp hz
                have h2 := congrArg (fun v => xorVec v y) h0
                simp only [xorVec_assoc, xorVec_self, xorVec_zero_right, xorVec_zero_left] at h2
                exact h2
              · intro heq; rw [heq, xorVec_self]; exact (isZeroVec_true_iff zeroVec).mpr rfl
            by_cases h1 : isZeroVec (xorVec x'' x1) = true
            · have heq := (hiff x1).mp h1
              have n2 : isZeroVec (xorVec x'' x2) = false := by
                cases h : isZeroVec (xorVec x'' x2); · rfl
                · have h2 := (hiff x2).mp h; exact False.elim (hx21 (h2.symm.trans heq))
              have n3 : isZeroVec (xorVec x'' x3) = false := by
                cases h : isZeroVec (xorVec x'' x3); · rfl
                · have h3 := (hiff x3).mp h; exact False.elim (hx31 (h3.symm.trans heq))
              have n4 : isZeroVec (xorVec x'' x4) = false := by
                cases h : isZeroVec (xorVec x'' x4); · rfl
                · have h4 := (hiff x4).mp h; exact False.elim (hx41 (h4.symm.trans heq))
              have hpx : P x'' = true := by rw [heq]; exact hx1
              simp [h1, n2, n3, n4, hpx]
            · by_cases h2 : isZeroVec (xorVec x'' x2) = true
              · have heq := (hiff x2).mp h2
                have n3 : isZeroVec (xorVec x'' x3) = false := by
                  cases h : isZeroVec (xorVec x'' x3); · rfl
                  · have h3 := (hiff x3).mp h; exact False.elim (hx32 (h3.symm.trans heq))
                have n4 : isZeroVec (xorVec x'' x4) = false := by
                  cases h : isZeroVec (xorVec x'' x4); · rfl
                  · have h4 := (hiff x4).mp h; exact False.elim (hx42 (h4.symm.trans heq))
                have hpx : P x'' = true := by rw [heq]; exact hx2
                simp [h1, h2, n3, n4, hpx]
              · by_cases h3 : isZeroVec (xorVec x'' x3) = true
                · have heq := (hiff x3).mp h3
                  have n4 : isZeroVec (xorVec x'' x4) = false := by
                    cases h : isZeroVec (xorVec x'' x4); · rfl
                    · have h4 := (hiff x4).mp h; exact False.elim (hx43 (h4.symm.trans heq))
                  have hpx : P x'' = true := by rw [heq]; exact hx3
                  simp [h1, h2, h3, n4, hpx]
                · by_cases h4 : isZeroVec (xorVec x'' x4) = true
                  · have heq := (hiff x4).mp h4
                    have hpx : P x'' = true := by rw [heq]; exact hp4
                    simp [h1, h2, h3, h4, hpx]
                  · simp [h1, h2, h3, h4]; cases P x'' <;> decide
          rw [sumVecs_add, sumVecs_add, sumVecs_add,
              sumVecs_xor_shift x1 (fun v => if isZeroVec v then (1 : Int) else 0),
              sumVecs_xor_shift x2 (fun v => if isZeroVec v then (1 : Int) else 0),
              sumVecs_xor_shift x3 (fun v => if isZeroVec v then (1 : Int) else 0),
              sumVecs_xor_shift x4 (fun v => if isZeroVec v then (1 : Int) else 0),
              sumVecs_delta_zero, hP_sum] at hge
          omega
      -- Exact values of walshBool g at x1, x2, x3 (±28) and bound at x4 (|W| ≤ 12):
      have hWg_28 : ∀ y : Vec 6, P y = true → walshBool g y = 28 ∨ walshBool g y = -28 := by
        intro y hy
        have hD : Dstar y = -sign (b y) := by
          dsimp only [P] at hy; exact of_decide_eq_true hy
        have hW := hWg y
        dsimp only [Estar] at hW
        rw [hD] at hW
        cases b y <;> simp [sign] at hW <;> omega
      have hW1_28 := hWg_28 x1 hx1
      have hW2_28 := hWg_28 x2 hx2
      have hW3_28 := hWg_28 x3 hx3
      have hW4_12 : -12 ≤ walshBool g x4 ∧ walshBool g x4 ≤ 12 := by
        have hDne : Dstar x4 ≠ -sign (b x4) := by
          intro heq
          have : P x4 = true := by dsimp only [P]; exact decide_eq_true heq
          rw [hPx4] at this; cases this
        have hW := hWg x4
        dsimp only [Estar] at hW
        rcases hDstar_vals x4 with h1 | h2 | h3
        · rw [h1] at hW; cases b x4 <;> simp [sign] at hW <;> omega
        · rw [h2] at hW; cases b x4 <;> simp [sign] at hW <;> omega
        · exact False.elim (hDne h3)
      -- 4-coset bound: for all c1 c2 : Bool,
      --   |W_g(x1) + sign(c1)*W_g(x2) + sign(c2)*W_g(x3) + sign(c1)*sign(c2)*W_g(x4)| ≤ 64.
      let α : Vec 6 := xorVec x1 x2
      let β : Vec 6 := xorVec x1 x3
      have hα_ne : α ≠ zeroVec := by
        intro hz
        have h1 := congrArg (fun v => xorVec v x2) hz
        simp only [α, xorVec_assoc, xorVec_self, xorVec_zero_right, xorVec_zero_left] at h1
        exact hx21 h1.symm
      have hβ_ne : β ≠ zeroVec := by
        intro hz
        have h1 := congrArg (fun v => xorVec v x3) hz
        simp only [β, xorVec_assoc, xorVec_self, xorVec_zero_right, xorVec_zero_left] at h1
        exact hx31 h1.symm
      have hαβ_ne : xorVec α β ≠ zeroVec := by
        intro hz
        have heq : xorVec α β = xorVec x2 x3 := by
          dsimp only [α, β]
          rw [xorVec_comm x1 x2, xorVec_assoc, ← xorVec_assoc x1 x1 x3, xorVec_self, xorVec_zero_left]
        rw [heq] at hz
        have h1 := congrArg (fun v => xorVec v x3) hz
        simp only [xorVec_assoc, xorVec_self, xorVec_zero_right, xorVec_zero_left] at h1
        exact hx32 h1.symm
      have h4coset : ∀ c1 c2 : Bool,
          -64 ≤ walshBool g x1 + sign c1 * walshBool g x2 +
                sign c2 * walshBool g x3 + sign c1 * sign c2 * walshBool g x4 ∧
          walshBool g x1 + sign c1 * walshBool g x2 +
          sign c2 * walshBool g x3 + sign c1 * sign c2 * walshBool g x4 ≤ 64 := by
        intro c1 c2
        let ind : Vec 6 → Int := fun a =>
          (1 + sign c1 * sign (dot α a)) * (1 + sign c2 * sign (dot β a))
        have hind_nn : ∀ a : Vec 6, 0 ≤ ind a := by
          intro a; dsimp only [ind]
          cases c1 <;> cases c2 <;> cases dot α a <;> cases dot β a <;> decide
        have hind_sum : sumVecs ind = 64 := by
          have hexp : ∀ a : Vec 6,
              ind a = 1 + sign c1 * sign (dot α a) + sign c2 * sign (dot β a) +
                      (sign c1 * sign c2) * sign (dot (xorVec α β) a) := by
            intro a; dsimp only [ind]
            have hdab : dot (xorVec α β) a = xor (dot α a) (dot β a) := dot_xor_left α β a
            rw [hdab, sign_xor]
            cases c1 <;> cases c2 <;> cases dot α a <;> cases dot β a <;> rfl
          rw [sumVecs_congr hexp, sumVecs_add, sumVecs_add, sumVecs_add,
              sumVecs_const, sumVecs_mul_left, sumVecs_mul_left, sumVecs_mul_left]
          have h0α : sumVecs (fun a => sign (dot α a)) = 0 := by
            have := walsh_const_one_ne_zero α hα_ne
            unfold walsh at this
            rw [sumVecs_congr (fun a => Int.one_mul _)] at this; exact this
          have h0β : sumVecs (fun a => sign (dot β a)) = 0 := by
            have := walsh_const_one_ne_zero β hβ_ne
            unfold walsh at this
            rw [sumVecs_congr (fun a => Int.one_mul _)] at this; exact this
          have h0αβ : sumVecs (fun a => sign (dot (xorVec α β) a)) = 0 := by
            have := walsh_const_one_ne_zero (xorVec α β) hαβ_ne
            unfold walsh at this
            rw [sumVecs_congr (fun a => Int.one_mul _)] at this; exact this
          rw [h0α, h0β, h0αβ, Int.mul_zero, Int.mul_zero, Int.mul_zero,
              Int.add_zero, Int.add_zero, Int.add_zero]; rfl
        have hcomb : sumVecs (fun a : Vec 6 => sign (g a) * sign (dot x1 a) * ind a) =
            walshBool g x1 + sign c1 * walshBool g x2 +
            sign c2 * walshBool g x3 + sign c1 * sign c2 * walshBool g x4 := by
          have hx2_eq : xorVec x1 α = x2 := by
            dsimp only [α]; rw [← xorVec_assoc, xorVec_self, xorVec_zero_left]
          have hx3_eq : xorVec x1 β = x3 := by
            dsimp only [β]; rw [← xorVec_assoc, xorVec_self, xorVec_zero_left]
          have hx4_eq : xorVec x1 (xorVec α β) = x4 := by
            funext i; dsimp only [x4, α, β, xorVec]; cases x1 i <;> cases x2 i <;> cases x3 i <;> rfl
          have hexp : ∀ a : Vec 6,
              sign (g a) * sign (dot x1 a) * ind a =
                sign (g a) * sign (dot x1 a) +
                sign c1 * (sign (g a) * sign (dot x2 a)) +
                sign c2 * (sign (g a) * sign (dot x3 a)) +
                (sign c1 * sign c2) * (sign (g a) * sign (dot x4 a)) := by
            intro a; dsimp only [ind]
            have d2 : dot x2 a = xor (dot x1 a) (dot α a) := by
              rw [← hx2_eq, dot_xor_left]
            have d3 : dot x3 a = xor (dot x1 a) (dot β a) := by
              rw [← hx3_eq, dot_xor_left]
            have d4 : dot x4 a = xor (dot x1 a) (xor (dot α a) (dot β a)) := by
              rw [← hx4_eq, dot_xor_left, dot_xor_left]
            rw [d2, d3, d4]
            cases g a <;> cases c1 <;> cases c2 <;>
              cases dot x1 a <;> cases dot α a <;> cases dot β a <;> decide
          rw [sumVecs_congr hexp, sumVecs_add, sumVecs_add, sumVecs_add,
              sumVecs_mul_left, sumVecs_mul_left, sumVecs_mul_left]
          rfl
        have hlo : -sumVecs ind ≤ sumVecs (fun a : Vec 6 => sign (g a) * sign (dot x1 a) * ind a) := by
          have hneg : -sumVecs ind = sumVecs (fun a : Vec 6 => -(ind a)) := by
            have := sumVecs_mul_left (-1) ind
            simp only [Int.neg_mul, Int.one_mul] at this; exact this.symm
          rw [hneg]; apply sumVecs_mono; intro a
          have hnn := hind_nn a
          cases g a <;> cases dot x1 a <;> simp [sign] <;> omega
        have hhi : sumVecs (fun a : Vec 6 => sign (g a) * sign (dot x1 a) * ind a) ≤ sumVecs ind := by
          apply sumVecs_mono; intro a
          have hnn := hind_nn a
          cases g a <;> cases dot x1 a <;> simp [sign] <;> omega
        rw [hind_sum, hcomb] at hlo hhi
        exact ⟨hlo, hhi⟩
      have hff := h4coset false false
      have hft := h4coset false true
      have htf := h4coset true false
      have htt := h4coset true true
      simp only [sign, Bool.false_eq_true, ↓reduceIte, Int.one_mul, Int.neg_mul] at hff hft htf htt
      rcases hW1_28 with h1 | h1 <;> rcases hW2_28 with h2 | h2 <;> rcases hW3_28 with h3 | h3 <;> omega

/-! ## Section 8: Main Theorems (All Even `n ≥ 8`, and `n = 8, 10`) -/

/-- **Balanced nonlinearity exclusion for even `n = 2m ≥ 8` (`m ≥ 4`):**
    No balanced Boolean function on `2m` variables (`m ≥ 4`) has nonlinearity
    `≥ 2^(2m - 1) - 2^(m - 1) - 2` (equivalently `|W_F(a)| ≤ 2^m + 4` everywhere). -/
theorem even_balanced_no_nl_ge_from8 (m : Nat) (hm : 4 ≤ m)
    (F : Vec (2 * m) → Bool) (hbal : isBalanced (2 * m) F) :
    ¬ hasNonlinearityAtLeast (2 * m) F ((2 : Int) ^ (2 * m - 1) - (2 : Int) ^ (m - 1) - 2) := by
  intro hnl
  cases m with
  | zero => omega
  | succ k =>
    have hk : 3 ≤ k := by omega
    have hcap : ∀ a : Vec (2 * (k + 1)),
        -((2 : Int) ^ (k + 1) + 4) ≤ walshBool F a ∧
        walshBool F a ≤ (2 : Int) ^ (k + 1) + 4 := by
      apply abs_walshBool_le_of_nl F ((2 : Int) ^ (2 * (k + 1) - 1) - (2 : Int) ^ (k + 1 - 1) - 2)
        ((2 : Int) ^ (k + 1) + 4) hnl
      have h1 : (2 : Int) ^ (2 * (k + 1)) = 2 * (2 : Int) ^ (2 * (k + 1) - 1) := by
        have he : 2 * (k + 1) = (2 * (k + 1) - 1) + 1 := by omega
        conv => lhs; rw [he, Int.pow_succ, Int.mul_comm]
      have h2 : (2 : Int) ^ (k + 1) = 2 * (2 : Int) ^ (k + 1 - 1) := by
        have he : k + 1 = (k + 1 - 1) + 1 := by omega
        conv => lhs; rw [he, Int.pow_succ, Int.mul_comm]
      omega
    exact even_balanced_exclusion_aux hk F hbal hcap

/-- **Upper bound on balanced nonlinearity for even `n = 2m ≥ 8` (`m ≥ 4`):**
    Every balanced Boolean function on `2m` variables (`m ≥ 4`) satisfies
    `nl(F) ≤ 2^(2m - 1) - 2^(m - 1) - 4` (i.e. cannot achieve `≥ 2^(2m - 1) - 2^(m - 1) - 3`). -/
theorem even_balanced_nl_le_from8 (m : Nat) (hm : 4 ≤ m)
    (F : Vec (2 * m) → Bool) (hbal : isBalanced (2 * m) F) :
    ¬ hasNonlinearityAtLeast (2 * m) F ((2 : Int) ^ (2 * m - 1) - (2 : Int) ^ (m - 1) - 3) := by
  intro hnl
  have hd_even : hasNonlinearityAtLeast (2 * m) F ((2 : Int) ^ (2 * m - 1) - (2 : Int) ^ (m - 1) - 2) := by
    intro a c
    have hge := hnl a c
    have hW_even : (2 : Int) ∣ walshBool F a := by
      have h0 := walshBool_eq_dist_false F a
      have hpow : (2 : Int) ∣ (2 : Int) ^ (2 * m) := two_pow_dvd_of_le (a := 1) (b := 2 * m) (by omega)
      obtain ⟨q, hq⟩ := hpow
      exact ⟨q - hammingDist F (affine a false), by omega⟩
    have hdist_even : (2 : Int) ∣ hammingDist F (affine a c) := by
      have hpow4 : (4 : Int) ∣ (2 : Int) ^ (2 * m) := two_pow_dvd_of_le (a := 2) (b := 2 * m) (by omega)
      have h4W : (4 : Int) ∣ walshBool F a := by
        have hmod8 := walshBool_mod8 (by omega) F hbal a
        cases dot (supportXor F) a <;> simp at hmod8 <;> omega
      obtain ⟨q1, hq1⟩ := hpow4
      obtain ⟨q2, hq2⟩ := h4W
      cases c
      · have h0 := walshBool_eq_dist_false F a; exact ⟨q1 - q2, by omega⟩
      · have h1 := walshBool_eq_dist_true F a; exact ⟨q1 + q2, by omega⟩
    have hpar_target : (2 : Int) ∣ ((2 : Int) ^ (2 * m - 1) - (2 : Int) ^ (m - 1) - 2) := by
      have hp1 : (2 : Int) ∣ (2 : Int) ^ (2 * m - 1) := two_pow_dvd_of_le (a := 1) (b := 2 * m - 1) (by omega)
      have hp2 : (2 : Int) ∣ (2 : Int) ^ (m - 1) := two_pow_dvd_of_le (a := 1) (b := m - 1) (by omega)
      obtain ⟨q1, hq1⟩ := hp1
      obtain ⟨q2, hq2⟩ := hp2
      exact ⟨q1 - q2 - 1, by omega⟩
    obtain ⟨qd, hqd⟩ := hdist_even
    obtain ⟨qt, hqt⟩ := hpar_target
    omega
  exact even_balanced_no_nl_ge_from8 m hm F hbal hd_even

/-- **The case `n = 8`** (first proved by Yuan et al., IACR ePrint 2026/1687, and Lou–Xu–Wang):
    No balanced 8-variable Boolean function has nonlinearity `≥ 118`. -/
theorem balanced_8_no_118 (F : Vec 8 → Bool) (hbal : isBalanced 8 F) :
    ¬ hasNonlinearityAtLeast 8 F 118 :=
  even_balanced_no_nl_ge_from8 4 (by decide) F hbal

/-- **Concrete Corollary (`n = 8`):** Every balanced 8-variable Boolean function has `nl(F) ≤ 116`. -/
theorem balanced_8_nl_le_116 (F : Vec 8 → Bool) (hbal : isBalanced 8 F) :
    ¬ hasNonlinearityAtLeast 8 F 117 :=
  even_balanced_nl_le_from8 4 (by decide) F hbal

/-- **The case `n = 10`** (first proved by Xu–Wang, IACR ePrint 2026/2797):
    No balanced 10-variable Boolean function has nonlinearity `≥ 494`. -/
theorem balanced_10_no_494 (F : Vec 10 → Bool) (hbal : isBalanced 10 F) :
    ¬ hasNonlinearityAtLeast 10 F 494 :=
  even_balanced_no_nl_ge_from8 5 (by decide) F hbal

/-- **Concrete Corollary (`n = 10`):** Every balanced 10-variable Boolean function has `nl(F) ≤ 492`. -/
theorem balanced_10_nl_le_492 (F : Vec 10 → Bool) (hbal : isBalanced 10 F) :
    ¬ hasNonlinearityAtLeast 10 F 493 :=
  even_balanced_nl_le_from8 5 (by decide) F hbal

/-! ## Section 9: Vectorial Balanced S-Box & Permutation Nonlinearity Bounds (`n = 2m ≥ 8`) -/

/-- A vectorial `(n, r)`-Boolean function (S-box) is balanced if every nonzero component `v · F` is balanced. -/
def isBalancedSBox (n r : Nat) (F : Vec n → Vec r) : Prop :=
  ∀ v : Vec r, v ≠ zeroVec → isBalanced n (fun x => dot v (F x))

/-- A vectorial `(n, r)`-S-box has nonlinearity `≥ d` if every nonzero component has nonlinearity `≥ d`. -/
def hasVectorialNonlinearityAtLeast (n r : Nat) (F : Vec n → Vec r) (d : Int) : Prop :=
  ∀ v : Vec r, v ≠ zeroVec → hasNonlinearityAtLeast n (fun x => dot v (F x)) d

/-- Bijective invariance of `sumVecs` (zero-Mathlib proof via Kronecker delta + sum swap). -/
private theorem sumVecs_bij {n : Nat} (F G : Vec n → Vec n)
    (hGF : ∀ x, G (F x) = x) (hFG : ∀ y, F (G y) = y) (h : Vec n → Int) :
    sumVecs (fun x => h (F x)) = sumVecs h := by
  have h1 : ∀ x : Vec n,
      h (F x) = sumVecs (fun y => if isZeroVec (xorVec (F x) y) then h y else 0) := by
    intro x
    have hpw : ∀ y : Vec n,
        (if isZeroVec (xorVec (F x) y) then h y else 0) =
        (if isZeroVec (xorVec y (F x)) then h (F x) else 0) := by
      intro y
      rw [xorVec_comm (F x) y]
      by_cases hz : isZeroVec (xorVec y (F x)) = true
      · have h0 := (isZeroVec_true_iff _).mp hz
        have h2 := congrArg (fun v => xorVec v (F x)) h0
        simp only [xorVec_assoc, xorVec_self, xorVec_zero_right, xorVec_zero_left] at h2
        rw [hz, h2]
      · simp [hz]
    rw [sumVecs_congr hpw,
        sumVecs_xor_shift (F x) (fun v => if isZeroVec v then h (F x) else 0),
        sumVecs_delta_zero]
  rw [sumVecs_congr h1, sumVecs_swap]
  apply sumVecs_congr; intro y
  have hpw2 : ∀ x : Vec n,
      (if isZeroVec (xorVec (F x) y) then h y else 0) =
      (if isZeroVec (xorVec x (G y)) then h y else 0) := by
    intro x
    have hiff : isZeroVec (xorVec (F x) y) = true ↔ isZeroVec (xorVec x (G y)) = true := by
      constructor
      · intro hz
        have h0 := (isZeroVec_true_iff _).mp hz
        have h2 := congrArg (fun v => xorVec v y) h0
        simp only [xorVec_assoc, xorVec_self, xorVec_zero_right, xorVec_zero_left] at h2
        have hx : x = G y := by rw [← hGF x, h2]
        rw [hx, xorVec_self]; exact (isZeroVec_true_iff zeroVec).mpr rfl
      · intro hz
        have h0 := (isZeroVec_true_iff _).mp hz
        have h2 := congrArg (fun v => xorVec v (G y)) h0
        simp only [xorVec_assoc, xorVec_self, xorVec_zero_right, xorVec_zero_left] at h2
        have hfx : F x = y := by rw [h2, hFG y]
        rw [hfx, xorVec_self]; exact (isZeroVec_true_iff zeroVec).mpr rfl
    cases ha : isZeroVec (xorVec (F x) y) <;> cases hb : isZeroVec (xorVec x (G y))
    · rfl
    · exact False.elim (by have := hiff.mpr hb; rw [ha] at this; cases this)
    · exact False.elim (by have := hiff.mp ha; rw [hb] at this; cases this)
    · rfl
  rw [sumVecs_congr hpw2,
      sumVecs_xor_shift (G y) (fun v => if isZeroVec v then h y else 0),
      sumVecs_delta_zero]

/-- Every bijective `n`-bit permutation `F : Vec n → Vec n` is a balanced `(n, n)`-S-box. -/
theorem permutation_is_balanced_sbox {n : Nat} (F G : Vec n → Vec n)
    (hGF : ∀ x, G (F x) = x) (hFG : ∀ y, F (G y) = y) :
    isBalancedSBox n n F := by
  intro v hv
  unfold isBalanced hammingWeight
  rw [sumVecs_bij F G hGF hFG (fun y => if dot v y then (1 : Int) else 0)]
  have h0 := walsh_const_one_ne_zero v hv
  unfold walsh at h0
  have h1 : ∀ y : Vec n, (1 : Int) * sign (dot v y) = 1 - 2 * (if dot v y then (1 : Int) else 0) := by
    intro y; cases dot v y <;> decide
  rw [sumVecs_congr h1, sumVecs_sub, sumVecs_const, sumVecs_mul_left, Int.mul_one] at h0
  omega

/-- **Vectorial S-box nonlinearity bound (`n = 2m ≥ 8`, `r ≥ 1`):**
    Every balanced `(2m, r)`-S-box (`m ≥ 4`, `r ≥ 1`) satisfies `nl(F) ≤ 2^(2m - 1) - 2^(m - 1) - 4`. -/
theorem sbox_even_nl_le_from8 (m r : Nat) (hm : 4 ≤ m) (hr : 1 ≤ r)
    (F : Vec (2 * m) → Vec r) (hbal : isBalancedSBox (2 * m) r F) :
    ¬ hasVectorialNonlinearityAtLeast (2 * m) r F ((2 : Int) ^ (2 * m - 1) - (2 : Int) ^ (m - 1) - 3) := by
  intro hnl
  cases r with
  | zero => omega
  | succ r' =>
    let v0 : Vec (r' + 1) := consVec true zeroVec
    have hv0 : v0 ≠ zeroVec := by
      intro heq
      have h := congrFun heq ⟨0, Nat.zero_lt_succ r'⟩
      dsimp only [v0, consVec, zeroVec] at h
      cases h
    exact even_balanced_nl_le_from8 m hm (fun x => dot v0 (F x)) (hbal v0 hv0) (hnl v0 hv0)

/-- **Even-bit permutation nonlinearity bound (`n = 2m ≥ 8`):**
    Every bijective `2m`-bit permutation (`m ≥ 4`) satisfies `nl(F) ≤ 2^(2m - 1) - 2^(m - 1) - 4`. -/
theorem permutation_even_nl_le_from8 (m : Nat) (hm : 4 ≤ m)
    (F G : Vec (2 * m) → Vec (2 * m))
    (hGF : ∀ x, G (F x) = x) (hFG : ∀ y, F (G y) = y) :
    ¬ hasVectorialNonlinearityAtLeast (2 * m) (2 * m) F ((2 : Int) ^ (2 * m - 1) - (2 : Int) ^ (m - 1) - 3) :=
  sbox_even_nl_le_from8 m (2 * m) hm (by omega) F (permutation_is_balanced_sbox F G hGF hFG)

/-- **8-Bit S-Box / Permutation Bound:** Every balanced `(8, r)`-S-box (`r ≥ 1`) has `nl(F) ≤ 116`. -/
theorem sbox_8bit_nl_le_116 (r : Nat) (hr : 1 ≤ r)
    (F : Vec 8 → Vec r) (hbal : isBalancedSBox 8 r F) :
    ¬ hasVectorialNonlinearityAtLeast 8 r F 117 :=
  sbox_even_nl_le_from8 4 r (by decide) hr F hbal

/-- **8-Bit Bijective Permutation Bound:** Every 8-bit permutation has `nl(F) ≤ 116`. -/
theorem permutation_8bit_nl_le_116 (F G : Vec 8 → Vec 8)
    (hGF : ∀ x, G (F x) = x) (hFG : ∀ y, F (G y) = y) :
    ¬ hasVectorialNonlinearityAtLeast 8 8 F 117 :=
  permutation_even_nl_le_from8 4 (by decide) F G hGF hFG

/-- **10-Bit S-Box Bound:** Every balanced `(10, r)`-S-box (`r ≥ 1`) has `nl(F) ≤ 492`. -/
theorem sbox_10bit_nl_le_492 (r : Nat) (hr : 1 ≤ r)
    (F : Vec 10 → Vec r) (hbal : isBalancedSBox 10 r F) :
    ¬ hasVectorialNonlinearityAtLeast 10 r F 493 :=
  sbox_even_nl_le_from8 5 r (by decide) hr F hbal

/-- **10-Bit Bijective Permutation Bound:** Every 10-bit permutation has `nl(F) ≤ 492`. -/
theorem permutation_10bit_nl_le_492 (F G : Vec 10 → Vec 10)
    (hGF : ∀ x, G (F x) = x) (hFG : ∀ y, F (G y) = y) :
    ¬ hasVectorialNonlinearityAtLeast 10 10 F 493 :=
  permutation_even_nl_le_from8 5 (by decide) F G hGF hFG

/-! ## Section 10: Sarkar–Maitra (2000) Divisibility & `t`-Resilient Nonlinearity Bounds -/

/-- Hamming weight of a bit-vector `a ∈ F_2^n`. -/
def vecWeight : {n : Nat} → Vec n → Nat
  | 0, _ => 0
  | _ + 1, v => (if v ⟨0, Nat.zero_lt_succ _⟩ then 1 else 0) + vecWeight (tailVec v)

/-- A Boolean function `F : F_2^n → F_2` is `t`-resilient if `W_F(a) = 0` for all `wt(a) ≤ t`. -/
def isResilient (n t : Nat) (F : Vec n → Bool) : Prop :=
  ∀ a : Vec n, vecWeight a ≤ t → walshBool F a = 0

private def updateVec {n : Nat} (v : Vec n) (q : Fin n) (b : Bool) : Vec n :=
  fun i => if i = q then b else v i

private theorem vecWeight_updateVec : {n : Nat} → (v : Vec n) → (q : Fin n) → (b : Bool) →
    vecWeight (updateVec v q b) + (if v q then 1 else 0) = vecWeight v + (if b then 1 else 0)
  | 0, _, q, _ => Fin.elim0 q
  | n + 1, v, q, b => by
    cases hq : q.val with
    | zero =>
      have hq0 : q = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext hq
      have hhead : updateVec v q b ⟨0, Nat.zero_lt_succ n⟩ = b := by
        unfold updateVec; rw [hq0, if_pos rfl]
      have htail : tailVec (updateVec v q b) = tailVec v := by
        funext i; unfold tailVec updateVec
        have hne : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n + 1)) ≠ q := by
          intro h; have := congrArg Fin.val h; simp [hq] at this
        rw [if_neg hne]
      dsimp only [vecWeight]
      rw [hhead, htail, hq0]; omega
    | succ q' =>
      let qf : Fin n := ⟨q', by omega⟩
      have hhead : updateVec v q b ⟨0, Nat.zero_lt_succ n⟩ = v ⟨0, Nat.zero_lt_succ n⟩ := by
        unfold updateVec
        have hne : (⟨0, Nat.zero_lt_succ n⟩ : Fin (n + 1)) ≠ q := by
          intro h; have := congrArg Fin.val h; simp [hq] at this
        rw [if_neg hne]
      have htail : tailVec (updateVec v q b) = updateVec (tailVec v) qf b := by
        funext i; unfold tailVec updateVec
        by_cases h : i = qf
        · have heq : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n + 1)) = q := by
            apply Fin.ext; simp [h, qf, hq]
          rw [if_pos heq, if_pos h]
        · have hne : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n + 1)) ≠ q := by
            intro heq; apply h; apply Fin.ext
            have := congrArg Fin.val heq; simp [qf, hq] at this ⊢; exact this
          rw [if_neg hne, if_neg h]
      have hvq : tailVec v qf = v q := by
        unfold tailVec; congr 1; apply Fin.ext; simp [qf, hq]
      dsimp only [vecWeight]
      rw [hhead, htail]
      have ih := vecWeight_updateVec (tailVec v) qf b
      rw [hvq] at ih
      omega

private theorem vecWeight_swap0 {n : Nat} (p : Fin (n + 1)) (a : Vec (n + 1)) :
    vecWeight (swap0 p a) = vecWeight a := by
  cases hp : p.val with
  | zero =>
    have hp0 : p = ⟨0, Nat.zero_lt_succ n⟩ := Fin.ext hp
    have heq : swap0 p a = a := by
      funext i; unfold swap0; rw [hp0]
      by_cases h : i = ⟨0, Nat.zero_lt_succ n⟩
      · rw [if_pos h, h]
      · rw [if_neg h, if_neg h]
    rw [heq]
  | succ q' =>
    let qf : Fin n := ⟨q', by omega⟩
    have hhead : swap0 p a ⟨0, Nat.zero_lt_succ n⟩ = a p := by
      unfold swap0; rw [if_pos rfl]
    have htail : tailVec (swap0 p a) =
        updateVec (tailVec a) qf (a ⟨0, Nat.zero_lt_succ n⟩) := by
      funext i; unfold tailVec swap0 updateVec
      have hne0 : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n + 1)) ≠ ⟨0, Nat.zero_lt_succ n⟩ := by
        intro h; have := congrArg Fin.val h; simp at this
      rw [if_neg hne0]
      by_cases h : i = qf
      · have heq : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n + 1)) = p := by
          apply Fin.ext; simp [h, qf, hp]
        rw [if_pos heq, if_pos h]
      · have hne : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (n + 1)) ≠ p := by
          intro heq; apply h; apply Fin.ext
          have := congrArg Fin.val heq; simp [qf, hp] at this ⊢; exact this
        rw [if_neg hne, if_neg h]
    have hap : tailVec a qf = a p := by
      unfold tailVec; congr 1; apply Fin.ext; simp [qf, hp]
    dsimp only [vecWeight]
    rw [hhead, htail]
    have hu := vecWeight_updateVec (tailVec a) qf (a ⟨0, Nat.zero_lt_succ n⟩)
    rw [hap] at hu
    omega

private theorem vecWeight_zero_iff : {n : Nat} → (a : Vec n) → (vecWeight a = 0 ↔ a = zeroVec)
  | 0, _ => ⟨fun _ => funext (fun i => Fin.elim0 i), fun _ => rfl⟩
  | n + 1, a => by
    constructor
    · intro h
      dsimp only [vecWeight] at h
      have h0 : a ⟨0, Nat.zero_lt_succ n⟩ = false := by
        cases hv : a ⟨0, Nat.zero_lt_succ n⟩
        · rfl
        · rw [hv] at h; simp at h
      have ht : tailVec a = zeroVec := (vecWeight_zero_iff (tailVec a)).mp (by
        rw [h0] at h; simp at h; exact h)
      rw [← consVec_eta a, h0, ht, zeroVec_cons]
    · intro h; subst h; dsimp only [vecWeight]
      rw [show tailVec (zeroVec : Vec (n + 1)) = zeroVec from rfl]
      have := (vecWeight_zero_iff (zeroVec : Vec n)).mpr rfl
      simp [zeroVec, this]

private theorem two_dvd_walshBool_of_pos {n : Nat} (hn : 1 ≤ n) (F : Vec n → Bool) (a : Vec n) :
    (2 : Int) ∣ walshBool F a := by
  have h0 := walshBool_eq_dist_false F a
  have hpow : (2 : Int) ∣ (2 : Int) ^ n := two_pow_dvd_of_le (a := 1) (b := n) hn
  obtain ⟨q, hq⟩ := hpow
  exact ⟨q - hammingDist F (affine a false), by omega⟩

/-- **Sarkar–Maitra (2000) Divisibility Theorem:**
    For every `t`-resilient Boolean function `F : F_2^n → F_2` with `t + 2 ≤ n`,
    every Walsh coefficient satisfies `2^(t + 2) ∣ W_F(a)`. -/
theorem sarkar_maitra_divisibility :
    ∀ (t : Nat) {n : Nat}, t + 2 ≤ n →
      ∀ (F : Vec n → Bool), isResilient n t F →
        ∀ a : Vec n, (2 : Int) ^ (t + 2) ∣ walshBool F a := by
  intro t
  induction t with
  | zero =>
    intro n hn F hres
    have hbyW : ∀ w : Nat, ∀ a : Vec n, vecWeight a = w → (2 : Int) ^ 2 ∣ walshBool F a := by
      intro w
      induction w with
      | zero =>
        intro a ha
        have h0 : walshBool F a = 0 := hres a (by omega)
        rw [h0]; exact ⟨0, (Int.mul_zero _).symm⟩
      | succ w' ihw =>
        intro a ha
        cases n with
        | zero => omega
        | succ m =>
          have hne : a ≠ zeroVec := by
            intro hz; have := (vecWeight_zero_iff a).mpr hz; omega
          have hex : ∃ p : Fin (m + 1), a p = true := by
            apply Classical.byContradiction; intro hno; apply hne; funext i
            cases hi : a i with
            | false => rfl
            | true => exact False.elim (hno ⟨i, hi⟩)
          obtain ⟨p, hp⟩ := hex
          let G : Vec (m + 1) → Bool := fun x => F (swap0 p x)
          let b : Vec (m + 1) := swap0 p a
          have hWG : ∀ c : Vec (m + 1), walshBool G c = walshBool F (swap0 p c) := fun c =>
            walsh_swap0 p (fun x => sign (F x)) c
          have hGres : isResilient (m + 1) 0 G := by
            intro c hc; rw [hWG c]; exact hres (swap0 p c) (by rw [vecWeight_swap0]; exact hc)
          have hWFa : walshBool F a = walshBool G b := by
            rw [hWG b]; dsimp only [b]; rw [swap0_invol]
          have hb0 : b ⟨0, Nat.zero_lt_succ m⟩ = true := by
            dsimp only [b]; unfold swap0; simp [hp]
          let b' : Vec m := tailVec b
          have hb_eq : b = consVec true b' := by rw [← consVec_eta b, hb0]
          have hwb' : vecWeight (consVec false b') = w' := by
            have hwb : vecWeight b = w' + 1 := by dsimp only [b]; rw [vecWeight_swap0]; exact ha
            rw [hb_eq] at hwb
            dsimp only [vecWeight] at hwb ⊢
            rw [consVec_head, tailVec_cons] at hwb ⊢
            simp at hwb ⊢; omega
          have hprev : (2 : Int) ^ 2 ∣ walshBool G (consVec false b') := by
            have := ihw (swap0 p (consVec false b')) (by rw [vecWeight_swap0]; exact hwb')
            rw [hWG (consVec false b')]; exact this
          let G1 : Vec m → Bool := fun x' => G (consVec true x')
          have hrel : walshBool G (consVec true b') =
              walshBool G (consVec false b') - 2 * walshBool G1 b' := by
            unfold walshBool
            rw [walsh_cons, walsh_cons]
            have hs0 : sign false = 1 := rfl
            have hs1 : sign true = -1 := rfl
            rw [hs0, hs1, Int.one_mul, Int.neg_mul, Int.one_mul]
            change _ = _ - 2 * walsh (fun x' => sign (G (consVec true x'))) b'
            omega
          have h2G1 : (2 : Int) ∣ walshBool G1 b' := two_dvd_walshBool_of_pos (by omega) G1 b'
          rw [hWFa, hb_eq, hrel]
          obtain ⟨q1, hq1⟩ := hprev
          obtain ⟨q2, hq2⟩ := h2G1
          exact ⟨q1 - q2, by have : (2 : Int) ^ 2 = 4 := rfl; rw [this] at hq1 ⊢; omega⟩
    intro a; exact hbyW (vecWeight a) a rfl
  | succ t' iht =>
    intro n hn F hres
    have hbyW : ∀ w : Nat, ∀ a : Vec n, vecWeight a = w → (2 : Int) ^ (t' + 1 + 2) ∣ walshBool F a := by
      intro w
      induction w with
      | zero =>
        intro a ha
        have h0 : walshBool F a = 0 := hres a (by omega)
        rw [h0]; exact ⟨0, (Int.mul_zero _).symm⟩
      | succ w' ihw =>
        intro a ha
        cases n with
        | zero => omega
        | succ m =>
          have hne : a ≠ zeroVec := by
            intro hz; have := (vecWeight_zero_iff a).mpr hz; omega
          have hex : ∃ p : Fin (m + 1), a p = true := by
            apply Classical.byContradiction; intro hno; apply hne; funext i
            cases hi : a i with
            | false => rfl
            | true => exact False.elim (hno ⟨i, hi⟩)
          obtain ⟨p, hp⟩ := hex
          let G : Vec (m + 1) → Bool := fun x => F (swap0 p x)
          let b : Vec (m + 1) := swap0 p a
          have hWG : ∀ c : Vec (m + 1), walshBool G c = walshBool F (swap0 p c) := fun c =>
            walsh_swap0 p (fun x => sign (F x)) c
          have hGres : isResilient (m + 1) (t' + 1) G := by
            intro c hc; rw [hWG c]; exact hres (swap0 p c) (by rw [vecWeight_swap0]; exact hc)
          have hWFa : walshBool F a = walshBool G b := by
            rw [hWG b]; dsimp only [b]; rw [swap0_invol]
          have hb0 : b ⟨0, Nat.zero_lt_succ m⟩ = true := by
            dsimp only [b]; unfold swap0; simp [hp]
          let b' : Vec m := tailVec b
          have hb_eq : b = consVec true b' := by rw [← consVec_eta b, hb0]
          have hwb' : vecWeight (consVec false b') = w' := by
            have hwb : vecWeight b = w' + 1 := by dsimp only [b]; rw [vecWeight_swap0]; exact ha
            rw [hb_eq] at hwb
            dsimp only [vecWeight] at hwb ⊢
            rw [consVec_head, tailVec_cons] at hwb ⊢
            simp at hwb ⊢; omega
          have hprev : (2 : Int) ^ (t' + 1 + 2) ∣ walshBool G (consVec false b') := by
            have := ihw (swap0 p (consVec false b')) (by rw [vecWeight_swap0]; exact hwb')
            rw [hWG (consVec false b')]; exact this
          let G1 : Vec m → Bool := fun x' => G (consVec true x')
          have hG1_res : isResilient m t' G1 := by
            intro c' hc'
            have hw0 : vecWeight (consVec false c') ≤ t' + 1 := by
              dsimp only [vecWeight]; rw [consVec_head, tailVec_cons]; simp; omega
            have hw1 : vecWeight (consVec true c') ≤ t' + 1 := by
              dsimp only [vecWeight]; rw [consVec_head, tailVec_cons]; simp; omega
            have h0 := hGres (consVec false c') hw0
            have h1 := hGres (consVec true c') hw1
            have hdiff : walshBool G (consVec false c') - walshBool G (consVec true c') =
                2 * walshBool G1 c' := by
              unfold walshBool
              rw [walsh_cons, walsh_cons]
              have hs0 : sign false = 1 := rfl
              have hs1 : sign true = -1 := rfl
              rw [hs0, hs1, Int.one_mul, Int.neg_mul, Int.one_mul]
              change _ = 2 * walsh (fun x' => sign (G (consVec true x'))) c'
              omega
            omega
          have hG1_dvd : (2 : Int) ^ (t' + 2) ∣ walshBool G1 b' :=
            iht (by omega) G1 hG1_res b'
          have hrel : walshBool G (consVec true b') =
              walshBool G (consVec false b') - 2 * walshBool G1 b' := by
            unfold walshBool
            rw [walsh_cons, walsh_cons]
            have hs0 : sign false = 1 := rfl
            have hs1 : sign true = -1 := rfl
            rw [hs0, hs1, Int.one_mul, Int.neg_mul, Int.one_mul]
            change _ = _ - 2 * walsh (fun x' => sign (G (consVec true x'))) b'
            omega
          rw [hWFa, hb_eq, hrel]
          obtain ⟨q1, hq1⟩ := hprev
          obtain ⟨q2, hq2⟩ := hG1_dvd
          have hpow_step : (2 : Int) ^ (t' + 1 + 2) = 2 * (2 : Int) ^ (t' + 2) := by
            have he : t' + 1 + 2 = (t' + 2) + 1 := by omega
            rw [he, Int.pow_succ, Int.mul_comm]
          refine ⟨q1 - q2, ?_⟩
          rw [hq1, hq2, Int.mul_sub, ← Int.mul_assoc 2, ← hpow_step]
    intro a; exact hbyW (vecWeight a) a rfl

/-- **Even-Dimension `t`-Resilient Nonlinearity Bound (`t + 2 ≤ m`):**
    Every `t`-resilient Boolean function on `2m` variables (`t + 2 ≤ m`) satisfies
    `nl(F) ≤ 2^(2m - 1) - 2^(m - 1) - 2^(t + 1)` (i.e. cannot reach `+ 1` above this). -/
theorem t_resilient_even_nl_le (m t : Nat) (ht : t + 2 ≤ m)
    (F : Vec (2 * m) → Bool) (hres : isResilient (2 * m) t F) :
    ¬ hasNonlinearityAtLeast (2 * m) F
        ((2 : Int) ^ (2 * m - 1) - (2 : Int) ^ (m - 1) - (2 : Int) ^ (t + 1) + 1) := by
  intro hnl
  let D : Int := (2 : Int) ^ (t + 2)
  let M : Int := (2 : Int) ^ m
  have hD_pos : 0 < D := two_pow_pos (t + 2)
  have hM_pos : 0 < M := two_pow_pos m
  have hD_dvd_M : D ∣ M := two_pow_dvd_of_le ht
  have hD_dvd_W : ∀ a : Vec (2 * m), D ∣ walshBool F a :=
    sarkar_maitra_divisibility t (by omega) F hres
  have hcap : ∀ a : Vec (2 * m), -(M + D - 2) ≤ walshBool F a ∧ walshBool F a ≤ M + D - 2 := by
    apply abs_walshBool_le_of_nl F
      ((2 : Int) ^ (2 * m - 1) - (2 : Int) ^ (m - 1) - (2 : Int) ^ (t + 1) + 1)
      (M + D - 2) hnl
    have h1 : (2 : Int) ^ (2 * m) = 2 * (2 : Int) ^ (2 * m - 1) := by
      have he : 2 * m = (2 * m - 1) + 1 := by omega
      conv => lhs; rw [he, Int.pow_succ, Int.mul_comm]
    have h2 : M = 2 * (2 : Int) ^ (m - 1) := by
      have he : m = (m - 1) + 1 := by omega
      dsimp only [M]; conv => lhs; rw [he, Int.pow_succ, Int.mul_comm]
    have h3 : D = 2 * (2 : Int) ^ (t + 1) := by
      dsimp only [D]; rw [Int.pow_succ, Int.mul_comm]
    omega
  have hW_le_M : ∀ a : Vec (2 * m), walshBool F a * walshBool F a ≤ M * M := by
    intro a
    obtain ⟨qw, hqw⟩ := hD_dvd_W a
    obtain ⟨qm, hqm⟩ := hD_dvd_M
    have hc := hcap a
    have hq_lo : -qm ≤ qw := by
      apply Classical.byContradiction; intro hlt
      have h1 : qw ≤ -qm - 1 := by omega
      have h2 := Int.mul_le_mul_of_nonneg_left h1 (by omega : 0 ≤ D)
      rw [← hqw, Int.mul_sub, Int.mul_neg, ← hqm, Int.mul_one] at h2
      omega
    have hq_hi : qw ≤ qm := by
      apply Classical.byContradiction; intro hlt
      have h1 : qm + 1 ≤ qw := by omega
      have h2 := Int.mul_le_mul_of_nonneg_left h1 (by omega : 0 ≤ D)
      rw [← hqw, Int.mul_add, ← hqm, Int.mul_one] at h2
      omega
    have hlo : -M ≤ walshBool F a := by
      have := Int.mul_le_mul_of_nonneg_left hq_lo (by omega : 0 ≤ D)
      rw [Int.mul_neg, ← hqm, ← hqw] at this; exact this
    have hhi : walshBool F a ≤ M := by
      have := Int.mul_le_mul_of_nonneg_left hq_hi (by omega : 0 ≤ D)
      rw [← hqm, ← hqw] at this; exact this
    exact sq_le_of_abs_le hlo hhi
  have hW0 : walshBool F zeroVec = 0 := hres zeroVec (by
    rw [(vecWeight_zero_iff zeroVec).mpr rfl]; omega)
  have hsum : sumVecs (fun a : Vec (2 * m) => walshBool F a * walshBool F a) ≤
      sumVecs (fun a : Vec (2 * m) => if isZeroVec a then (0 : Int) else M * M) := by
    apply sumVecs_mono; intro a
    by_cases ha : isZeroVec a = true
    · simp only [ha, ↓reduceIte]
      rw [(isZeroVec_true_iff a).mp ha, hW0]; decide
    · simp only [ha, ↓reduceIte]; exact hW_le_M a
  have hrhs : sumVecs (fun a : Vec (2 * m) => if isZeroVec a then (0 : Int) else M * M) =
      ((2 : Int) ^ (2 * m) - 1) * (M * M) := by
    have hpw : ∀ a : Vec (2 * m),
        (if isZeroVec a then (0 : Int) else M * M) = M * M - (if isZeroVec a then M * M else 0) := by
      intro a; cases isZeroVec a <;> simp
    rw [sumVecs_congr hpw, sumVecs_sub, sumVecs_const, sumVecs_delta_zero, Int.sub_mul, Int.one_mul]
  rw [walshBool_parseval, hrhs] at hsum
  have hM2 : M * M = (2 : Int) ^ (2 * m) := by
    have : 2 * m = m + m := by omega
    rw [this, int_pow_add]
  have hN2 : (2 : Int) ^ (2 * (2 * m)) = (2 : Int) ^ (2 * m) * (M * M) := by
    have : 2 * (2 * m) = 2 * m + 2 * m := by omega
    rw [this, int_pow_add, ← hM2]
  rw [hN2, Int.sub_mul, Int.one_mul] at hsum
  have hM2_pos : 0 < M * M := Int.mul_pos hM_pos hM_pos
  omega

/-- **Sarkar–Maitra–Tarannikov high-order resiliency bound (any `n`, even or odd, `t + 2 ≤ n`):**
    Every `t`-resilient Boolean function on `n ≥ t + 2` variables satisfies
    `nl(F) ≤ 2^(n - 1) - 2^(t + 1)`. -/
theorem t_resilient_high_order_nl_le (n t : Nat) (ht : t + 2 ≤ n)
    (F : Vec n → Bool) (hres : isResilient n t F) :
    ¬ hasNonlinearityAtLeast n F ((2 : Int) ^ (n - 1) - (2 : Int) ^ (t + 1) + 1) := by
  intro hnl
  let D : Int := (2 : Int) ^ (t + 2)
  have hD_pos : 0 < D := two_pow_pos (t + 2)
  have hD_dvd_W : ∀ a : Vec n, D ∣ walshBool F a :=
    sarkar_maitra_divisibility t ht F hres
  have hcap : ∀ a : Vec n, -(D - 2) ≤ walshBool F a ∧ walshBool F a ≤ D - 2 := by
    apply abs_walshBool_le_of_nl F ((2 : Int) ^ (n - 1) - (2 : Int) ^ (t + 1) + 1) (D - 2) hnl
    have h1 : (2 : Int) ^ n = 2 * (2 : Int) ^ (n - 1) := by
      have he : n = (n - 1) + 1 := by omega
      conv => lhs; rw [he, Int.pow_succ, Int.mul_comm]
    have h2 : D = 2 * (2 : Int) ^ (t + 1) := by
      dsimp only [D]; rw [Int.pow_succ, Int.mul_comm]
    omega
  have hW_zero : ∀ a : Vec n, walshBool F a = 0 := by
    intro a
    obtain ⟨q, hq⟩ := hD_dvd_W a
    have hc := hcap a
    have hq0 : q = 0 := by
      apply Classical.byContradiction; intro hne
      by_cases hpos : 0 < q
      · have := Int.mul_le_mul_of_nonneg_left (show 1 ≤ q by omega) (by omega : 0 ≤ D)
        rw [Int.mul_one, ← hq] at this; omega
      · have := Int.mul_le_mul_of_nonneg_left (show q ≤ -1 by omega) (by omega : 0 ≤ D)
        rw [Int.mul_neg, Int.mul_one, ← hq] at this; omega
    rw [hq, hq0, Int.mul_zero]
  have hp := walshBool_parseval F
  have hz : sumVecs (fun a : Vec n => walshBool F a * walshBool F a) = 0 := by
    have h0 : ∀ a : Vec n, walshBool F a * walshBool F a = 0 := fun a => by rw [hW_zero a]; rfl
    rw [sumVecs_congr h0, sumVecs_const, Int.mul_zero]
  rw [hz] at hp
  have hpos : 0 < (2 : Int) ^ (2 * n) := two_pow_pos (2 * n)
  omega

end EvenBalanced8Bound

#print axioms EvenBalanced8Bound.even_balanced_no_nl_ge_from8
#print axioms EvenBalanced8Bound.even_balanced_nl_le_from8
#print axioms EvenBalanced8Bound.balanced_8_no_118
#print axioms EvenBalanced8Bound.balanced_8_nl_le_116
#print axioms EvenBalanced8Bound.balanced_10_no_494
#print axioms EvenBalanced8Bound.balanced_10_nl_le_492
#print axioms EvenBalanced8Bound.sbox_even_nl_le_from8
#print axioms EvenBalanced8Bound.permutation_even_nl_le_from8
#print axioms EvenBalanced8Bound.sbox_8bit_nl_le_116
#print axioms EvenBalanced8Bound.permutation_8bit_nl_le_116
#print axioms EvenBalanced8Bound.sbox_10bit_nl_le_492
#print axioms EvenBalanced8Bound.permutation_10bit_nl_le_492
#print axioms EvenBalanced8Bound.sarkar_maitra_divisibility
#print axioms EvenBalanced8Bound.t_resilient_even_nl_le
#print axioms EvenBalanced8Bound.t_resilient_high_order_nl_le
