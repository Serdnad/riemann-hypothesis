module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Pi
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

section

open Matrix

namespace GlobalTheory.CompanionTheory.HeckeMult

variable {R : Type} [CommRing R]

def CongOne {n : ℕ} (I : Ideal R) (A : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, A i j - (1 : Matrix (Fin n) (Fin n) R) i j ∈ I

def bordered {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (c r : Fin n → R) (d : R) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) R := fun i j =>
  Fin.lastCases (motive := fun _ => R)
    (Fin.lastCases (motive := fun _ => R) d r j)
    (fun i' => Fin.lastCases (motive := fun _ => R) (c i') (M i') j) i

section bordered
variable {n : ℕ} (M : Matrix (Fin n) (Fin n) R) (c r : Fin n → R) (d : R)

@[simp] theorem bordered_cc (i j : Fin n) :
    bordered M c r d i.castSucc j.castSucc = M i j := by simp [bordered]
@[simp] theorem bordered_cl (i : Fin n) :
    bordered M c r d i.castSucc (Fin.last n) = c i := by simp [bordered]
@[simp] theorem bordered_lc (j : Fin n) :
    bordered M c r d (Fin.last n) j.castSucc = r j := by simp [bordered]
@[simp] theorem bordered_ll :
    bordered M c r d (Fin.last n) (Fin.last n) = d := by simp [bordered]
end bordered

theorem one_cc {n : ℕ} (i j : Fin n) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc j.castSucc
      = (1 : Matrix (Fin n) (Fin n) R) i j := by
  simp [Matrix.one_apply]

theorem one_cl {n : ℕ} (i : Fin n) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i.castSucc (Fin.last n) = 0 :=
  Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne

theorem one_lc {n : ℕ} (i : Fin n) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (Fin.last n) i.castSucc = 0 :=
  Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne'

theorem CongOne.bordered {n : ℕ} {I : Ideal R} {M : Matrix (Fin n) (Fin n) R}
    {c r : Fin n → R} {d : R} (hM : CongOne I M) (hc : ∀ i, c i ∈ I) (hr : ∀ i, r i ∈ I)
    (hd : d - 1 ∈ I) : CongOne I (bordered M c r d) := by
  intro i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simpa using hd
    | cast j => simpa [one_lc] using hr j
  | cast i =>
    induction j using Fin.lastCases with
    | last => simpa [one_cl] using hc i
    | cast j => simpa [one_cc] using hM i j

theorem exists_upper_lower (I : Ideal R) (hI : ∀ s : R, s - 1 ∈ I → IsUnit s) (n : ℕ) :
    ∀ A : Matrix (Fin n) (Fin n) R, CongOne I A →
      ∃ U L : Matrix (Fin n) (Fin n) R, CongOne I U ∧ CongOne I L ∧
        (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → L i j = 0) ∧ A = U * L := by
  induction n with
  | zero =>
    intro A _
    exact ⟨1, 1, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      by ext i; exact i.elim0⟩
  | succ n ih =>
    intro A hA
    have hs1 : A (Fin.last n) (Fin.last n) - 1 ∈ I := by
      simpa using hA (Fin.last n) (Fin.last n)
    obtain ⟨t, hst⟩ := (hI _ hs1).exists_right_inv
    have hq : ∀ i : Fin n, A i.castSucc (Fin.last n) ∈ I := fun i => by
      simpa [one_cl] using hA i.castSucc (Fin.last n)
    have hr : ∀ j : Fin n, A (Fin.last n) j.castSucc ∈ I := fun j => by
      simpa [one_lc] using hA (Fin.last n) j.castSucc
    let P : Matrix (Fin n) (Fin n) R := fun i j =>
      A i.castSucc j.castSucc - A i.castSucc (Fin.last n) * t * A (Fin.last n) j.castSucc
    have hP : CongOne I P := by
      intro i j
      have h1 := hA i.castSucc j.castSucc
      rw [one_cc] at h1
      have h2 : A i.castSucc (Fin.last n) * t * A (Fin.last n) j.castSucc ∈ I :=
        I.mul_mem_left _ (hr j)
      have : P i j - (1 : Matrix (Fin n) (Fin n) R) i j
          = (A i.castSucc j.castSucc - (1 : Matrix (Fin n) (Fin n) R) i j)
            - A i.castSucc (Fin.last n) * t * A (Fin.last n) j.castSucc := by
        simp only [P]; ring
      rw [this]
      exact I.sub_mem h1 h2
    obtain ⟨U', L', hU', hL', hUt, hLt, hUL⟩ := ih P hP
    refine ⟨bordered U' (fun i => A i.castSucc (Fin.last n) * t) 0 1,
      bordered L' 0 (fun j => A (Fin.last n) j.castSucc) (A (Fin.last n) (Fin.last n)),
      hU'.bordered (fun i => I.mul_mem_right _ (hq i)) (fun _ => I.zero_mem) (by simp),
      hL'.bordered (fun _ => I.zero_mem) hr hs1, ?_, ?_, ?_⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => simp
      | cast i =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (not_lt.mpr (Fin.castSucc_lt_last i).le)
        | cast j => simpa using hUt i j (by simpa using hij)
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => exact absurd hij (lt_irrefl _)
        | cast j => exact absurd hij (not_lt.mpr (Fin.castSucc_lt_last j).le)
      | cast i =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j => simpa using hLt i j (by simpa using hij)
    · ext i j
      rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => simp
        | cast j => simp
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp only [bordered_cc, bordered_cl, bordered_ll, Pi.zero_apply, mul_zero,
            Finset.sum_const_zero, zero_add]
          rw [mul_assoc, mul_comm t, hst, mul_one]
        | cast j =>
          simp only [bordered_cc, bordered_cl, bordered_lc]
          have h := congrFun (congrFun hUL i) j
          rw [Matrix.mul_apply] at h
          rw [← h]
          simp only [P]; ring

section conj
variable {K : Type} [Field K] [Algebra R K]

theorem conj_upper {n : ℕ} {I : Ideal R} (ϖ : R) (hϖ : algebraMap R K ϖ ≠ 0) (a : Fin n → ℤ)
    (ha : Antitone a) (U : Matrix (Fin n) (Fin n) R) (hU : CongOne I U)
    (hUt : ∀ i j, j < i → U i j = 0) :
    ∃ V : Matrix (Fin n) (Fin n) R, CongOne I V ∧
      Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (a i)) * U.map (algebraMap R K)
        = V.map (algebraMap R K) * Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (a i)) := by
  refine ⟨Matrix.of fun i j => U i j * ϖ ^ (a i - a j).toNat, ?_, ?_⟩
  · intro i j
    rw [Matrix.of_apply]
    rcases lt_trichotomy i j with h | h | h
    · rw [Matrix.one_apply_ne h.ne, sub_zero]
      have := hU i j
      rw [Matrix.one_apply_ne h.ne, sub_zero] at this
      exact I.mul_mem_right _ this
    · subst h
      simpa using hU i i
    · rw [Matrix.one_apply_ne h.ne', sub_zero, hUt i j h, zero_mul]
      exact I.zero_mem
  · ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, map_pow]
    rcases lt_or_ge j i with h | h
    · simp [hUt i j h]
    · have hnn : 0 ≤ a i - a j := sub_nonneg.mpr (ha h)
      have : (algebraMap R K ϖ) ^ (a i) = (algebraMap R K ϖ) ^ (a i - a j).toNat * (algebraMap R K ϖ) ^ (a j) := by
        rw [← zpow_natCast, Int.toNat_of_nonneg hnn, ← zpow_add₀ hϖ]
        congr 1; ring
      rw [this]; ring

theorem conj_lower {n : ℕ} {I : Ideal R} (ϖ : R) (hϖ : algebraMap R K ϖ ≠ 0) (b : Fin n → ℤ)
    (hb : Antitone b) (L : Matrix (Fin n) (Fin n) R) (hL : CongOne I L)
    (hLt : ∀ i j, i < j → L i j = 0) :
    ∃ V : Matrix (Fin n) (Fin n) R, CongOne I V ∧
      L.map (algebraMap R K) * Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (b i))
        = Matrix.diagonal (fun i => (algebraMap R K ϖ) ^ (b i)) * V.map (algebraMap R K) := by
  refine ⟨Matrix.of fun i j => L i j * ϖ ^ (b j - b i).toNat, ?_, ?_⟩
  · intro i j
    rw [Matrix.of_apply]
    rcases lt_trichotomy i j with h | h | h
    · rw [Matrix.one_apply_ne h.ne, sub_zero, hLt i j h, zero_mul]
      exact I.zero_mem
    · subst h
      simpa using hL i i
    · rw [Matrix.one_apply_ne h.ne', sub_zero]
      have := hL i j
      rw [Matrix.one_apply_ne h.ne', sub_zero] at this
      exact I.mul_mem_right _ this
  · ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    simp only [Matrix.map_apply, Matrix.of_apply, map_mul, map_pow]
    rcases lt_or_ge i j with h | h
    · simp [hLt i j h]
    · have hnn : 0 ≤ b j - b i := sub_nonneg.mpr (hb h)
      have : (algebraMap R K ϖ) ^ (b j) = (algebraMap R K ϖ) ^ (b j - b i).toNat * (algebraMap R K ϖ) ^ (b i) := by
        rw [← zpow_natCast, Int.toNat_of_nonneg hnn, ← zpow_add₀ hϖ]
        congr 1; ring
      rw [this]; ring

end conj

end GlobalTheory.CompanionTheory.HeckeMult
end

section

namespace GlobalTheory.CompanionTheory.StrictCone

theorem exists_char_of_mul_on_cone {G : Type*} [AddCommGroup G] (S : Set G)
    (hS : ∀ x ∈ S, ∀ y ∈ S, x + y ∈ S) (f : G → ℂ)
    (hf : ∀ x ∈ S, ∀ y ∈ S, f (x + y) = f x * f y) (s₀ : G) (hs₀ : s₀ ∈ S) (hne : f s₀ ≠ 0)
    (arch : ∀ g : G, ∃ k : ℕ, 0 < k ∧ k • s₀ + g ∈ S) :
    ∃ φ : G → ℂˣ, (∀ g h, φ (g + h) = φ g * φ h) ∧ ∀ s ∈ S, f s = (φ s : ℂ) := by
  have hmem : ∀ k : ℕ, k • s₀ + s₀ ∈ S ∧ f (k • s₀ + s₀) ≠ 0 := by
    intro k
    induction k with
    | zero => simpa using ⟨hs₀, hne⟩
    | succ n ih =>
      have h1 : (n + 1) • s₀ + s₀ = (n • s₀ + s₀) + s₀ := by rw [succ_nsmul]
      rw [h1]
      refine ⟨hS _ ih.1 _ hs₀, ?_⟩
      rw [hf _ ih.1 _ hs₀]
      exact mul_ne_zero ih.2 hne
  have hmem' : ∀ k : ℕ, 0 < k → k • s₀ ∈ S ∧ f (k • s₀) ≠ 0 := by
    intro k hk
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    rw [succ_nsmul]
    exact hmem n
  have hnz : ∀ z ∈ S, f z ≠ 0 := by
    intro z hz h0
    obtain ⟨k, hk, hw⟩ := arch (-z)
    have h2 : k • s₀ = z + (k • s₀ + -z) := by abel
    have h3 := (hmem' k hk).2
    rw [h2, hf _ hz _ hw, h0, zero_mul] at h3
    exact h3 rfl
  have wd : ∀ c₁ ∈ S, ∀ c₂ ∈ S, ∀ d₁ ∈ S, ∀ d₂ ∈ S, c₁ - c₂ = d₁ - d₂ →
      f c₁ / f c₂ = f d₁ / f d₂ := by
    intro c₁ h₁ c₂ h₂ d₁ h₃ d₂ h₄ h
    have e : c₁ + d₂ = d₁ + c₂ := by
      have : c₁ + d₂ - (d₁ + c₂) = (c₁ - c₂) - (d₁ - d₂) := by abel
      rw [← sub_eq_zero, this, h, sub_self]
    have e' := congrArg f e
    rw [hf _ h₁ _ h₄, hf _ h₃ _ h₂] at e'
    rw [div_eq_div_iff (hnz _ h₂) (hnz _ h₄)]
    exact e'
  choose k hk hd using arch
  have hc : ∀ g, k g • s₀ ∈ S := fun g => (hmem' _ (hk g)).1
  let φ : G → ℂˣ := fun g =>
    Units.mk0 (f (k g • s₀ + g) / f (k g • s₀)) (div_ne_zero (hnz _ (hd g)) (hnz _ (hc g)))
  refine ⟨φ, ?_, ?_⟩
  · intro g h
    apply Units.ext
    simp only [φ, Units.val_mul, Units.val_mk0]
    have := wd _ (hd (g + h)) _ (hc (g + h)) _ (hS _ (hd g) _ (hd h)) _ (hS _ (hc g) _ (hc h))
      (by abel)
    rw [this, hf _ (hd g) _ (hd h), hf _ (hc g) _ (hc h), mul_div_mul_comm]
  · intro s hs
    simp only [φ, Units.val_mk0]
    rw [hf _ (hc s) _ hs, mul_div_cancel_left₀ _ (hnz _ (hc s))]

theorem char_eq_prod {n : ℕ} (φ : (Fin n → ℤ) → ℂˣ) (h : ∀ g g', φ (g + g') = φ g * φ g') (x : Fin n → ℤ) :
    φ x = ∏ i, φ (Pi.single i 1) ^ x i := by
  let F : (Fin n → ℤ) →+ Additive ℂˣ :=
    AddMonoidHom.mk' (fun g => Additive.ofMul (φ g)) (fun g g' => by rw [h]; rfl)
  have hx : x = ∑ i, x i • (Pi.single i (1 : ℤ) : Fin n → ℤ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have h2 : F x = ∑ i, x i • F (Pi.single i 1) := by
    conv_lhs => rw [hx]

    rw [map_sum]
    simp only [map_zsmul]
  have h3 := congrArg Additive.toMul h2
  simpa [F, toMul_sum] using h3

theorem zpow_sum_units (Q : ℂˣ) {n : ℕ} (e : Fin n → ℤ) : Q ^ (∑ i, e i) = ∏ i, Q ^ e i := by
  classical
  refine Finset.induction_on (Finset.univ : Finset (Fin n)) (by simp) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem char_split {n : ℕ} (c : Fin n → ℤ) (Q : ℂˣ) (φ : (Fin n → ℤ) → ℂˣ)
    (h : ∀ g g', φ (g + g') = φ g * φ g') :
    ∃ ξ : Fin n → ℂˣ, ∀ x, φ x = Q ^ (∑ i, c i * x i) * ∏ i, ξ i ^ x i := by
  refine ⟨fun i => φ (Pi.single i 1) * Q ^ (-c i), fun x => ?_⟩
  rw [char_eq_prod φ h x, zpow_sum_units, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [mul_zpow, ← zpow_mul, mul_left_comm, ← zpow_add]
  simp

def IsStrict {n : ℕ} (x : Fin n → ℤ) : Prop := ∀ i j, i < j → x j + 1 ≤ x i

theorem IsStrict.add {n : ℕ} {x y : Fin n → ℤ} (hx : IsStrict x) (hy : IsStrict y) :
    IsStrict (x + y) := by
  intro i j hij
  have := hx i j hij
  have := hy i j hij
  simp only [Pi.add_apply]
  omega

theorem IsStrict.arch {n : ℕ} {s : Fin n → ℤ} (hs : IsStrict s) (g : Fin n → ℤ) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → IsStrict (k • s + g) := by
  refine ⟨1 + ∑ i, ∑ j, (g i - g j).natAbs, fun k hk i j hij => ?_⟩
  have h1 : (g j - g i).natAbs ≤ ∑ i, ∑ j, (g i - g j).natAbs :=
    (Finset.single_le_sum (f := fun j' => (g j' - g i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      (by
        rw [Finset.sum_comm]
        exact Finset.single_le_sum (f := fun i' => ∑ j', (g j' - g i').natAbs)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have h2 : s j + 1 ≤ s i := hs i j hij
  have h3 : (k : ℤ) * (s j + 1) ≤ (k : ℤ) * s i :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : (g j - g i) ≤ ((g j - g i).natAbs : ℤ) := by omega
  generalize (∑ i, ∑ j, (g i - g j).natAbs) = T at hk h1
  have h5 : (1 : ℤ) + T ≤ k := by exact_mod_cast hk
  have h6 : ((g j - g i).natAbs : ℤ) ≤ T := by exact_mod_cast h1
  rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, nsmul_eq_mul, nsmul_eq_mul]
  nlinarith

theorem mul_on_cone_eq_delta_char : ∀ (a b : ℕ) (q : ℂ), q ≠ 0 → ∀ χ : (Fin a → ℤ) → (Fin b → ℤ) → ℂ, (∀ x x' y y', (∀ i j, i < j → x j + 1 ≤ x i) → (∀ i j, i < j → x' j + 1 ≤ x' i) → (∀ i j, i < j → y j + 1 ≤ y i) → (∀ i j, i < j → y' j + 1 ≤ y' i) → χ (x + x') (y + y') = χ x y * χ x' y') → (∃ x y, (∀ i j, i < j → x j + 1 ≤ x i) ∧ (∀ i j, i < j → y j + 1 ≤ y i) ∧ χ x y ≠ 0) → ∃ (ξa : Fin a → ℂˣ) (ξb : Fin b → ℂˣ), ∀ x y, (∀ i j, i < j → x j + 1 ≤ x i) → (∀ i j, i < j → y j + 1 ≤ y i) → χ x y = q ^ (∑ i : Fin a, ((a : ℤ) - 1 - 2 * (i : ℕ)) * x i) * (∏ i, ((ξa i ^ x i : ℂˣ) : ℂ)) * (q ^ (∑ i : Fin b, ((b : ℤ) - 1 - 2 * (i : ℕ)) * y i) * ∏ i, ((ξb i ^ y i : ℂˣ) : ℂ)) := by
  intro a b q hq χ hχ ⟨x₀, y₀, hx₀, hy₀, hne⟩
  let S : Set ((Fin a → ℤ) × (Fin b → ℤ)) := {z | IsStrict z.1 ∧ IsStrict z.2}
  obtain ⟨φ, hφ, hfφ⟩ := exists_char_of_mul_on_cone S
    (fun x hx y hy => ⟨hx.1.add hy.1, hx.2.add hy.2⟩) (fun z => χ z.1 z.2)
    (fun x hx y hy => hχ _ _ _ _ hx.1 hy.1 hx.2 hy.2) (x₀, y₀) ⟨hx₀, hy₀⟩ hne
    (fun g => by
      obtain ⟨K₁, h₁⟩ := IsStrict.arch (s := x₀) hx₀ g.1
      obtain ⟨K₂, h₂⟩ := IsStrict.arch (s := y₀) hy₀ g.2
      refine ⟨K₁ + K₂ + 1, by omega, ?_, ?_⟩
      · exact h₁ _ (by omega)
      · exact h₂ _ (by omega))
  let Q : ℂˣ := Units.mk0 q hq
  obtain ⟨ξa, ha⟩ := char_split (fun i : Fin a => (a : ℤ) - 1 - 2 * (i : ℕ)) Q
    (fun x => φ (x, 0)) (fun g g' => by rw [← hφ]; simp)
  obtain ⟨ξb, hb⟩ := char_split (fun i : Fin b => (b : ℤ) - 1 - 2 * (i : ℕ)) Q
    (fun y => φ (0, y)) (fun g g' => by rw [← hφ]; simp)
  refine ⟨ξa, ξb, fun x y hx hy => ?_⟩
  have h1 : χ x y = (φ (x, y) : ℂ) := hfφ (x, y) ⟨hx, hy⟩
  have h2 : φ (x, y) = φ (x, 0) * φ (0, y) := by rw [← hφ]; simp
  rw [h1, h2, ha x, hb y]
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mk0, Q, Units.coe_prod]

end GlobalTheory.CompanionTheory.StrictCone
end

section

namespace GlobalTheory.CompanionTheory.Tempered

theorem weighted_antitone_eq_zero_of_tails_nonneg :
    ∀ (h : ℕ) (d e : Fin h → ℝ), (∀ i, 0 < d i) → Antitone e → ∑ i, d i * e i = 0 →
      (∀ j : Fin h, 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => j ≤ i), d i * e i) →
      ∀ i, e i = 0 := by
  intro h d e hd he hsum htail
  have hnn : ∀ i, 0 ≤ e i := by
    intro i
    by_contra hneg
    rw [not_le] at hneg
    have hlt : ∑ k ∈ Finset.univ.filter (fun k => i ≤ k), d k * e k < 0 := by
      apply Finset.sum_neg
      · intro k hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
        exact mul_neg_of_pos_of_neg (hd k) (lt_of_le_of_lt (he hk) hneg)
      · exact ⟨i, by simp⟩
    linarith [htail i]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg fun k _ => mul_nonneg (hd k).le (hnn k)).1 hsum
  intro i
  rcases mul_eq_zero.1 (hz i (Finset.mem_univ i)) with h1 | h1
  · exact absurd h1 (hd i).ne'
  · exact h1

end GlobalTheory.CompanionTheory.Tempered
end

section

namespace GlobalTheory.CompanionTheory.FinReversal

theorem prod_filter_le_rev {M : Type*} [CommMonoid M] (h : ℕ) (f : Fin h → M) (j : Fin h) :
    ∏ a ∈ Finset.univ.filter (fun a => a ≤ j), f (Fin.rev a)
      = ∏ i ∈ Finset.univ.filter (fun i => Fin.rev j ≤ i), f i := by
  refine Finset.prod_nbij' Fin.rev Fin.rev ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact Fin.rev_le_rev.mpr ha
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [← Fin.rev_le_rev, Fin.rev_rev]
    exact ha
  · intro a _
    exact Fin.rev_rev a
  · intro a _
    exact Fin.rev_rev a
  · intro a _
    rfl

end GlobalTheory.CompanionTheory.FinReversal
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free

def hypOne {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    Matrix (Fin (M + 2)) (Fin (M + 2)) K :=
  Matrix.of (Fin.cons (Fin.cons 0 (Fin.cons 1 fun _ => 0))
    (Fin.cons (Fin.cons 1 (Fin.cons 0 fun _ => 0)) fun i => Fin.cons 0 (Fin.cons 0 (A i))))

section Entries

variable {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K)

theorem hypOne_zero_zero : hypOne A 0 0 = 0 := rfl
theorem hypOne_zero_one : hypOne A 0 1 = 1 := rfl
theorem hypOne_one_zero : hypOne A 1 0 = 1 := rfl
theorem hypOne_one_one : hypOne A 1 1 = 0 := rfl
theorem hypOne_zero_rest (j : Fin M) : hypOne A 0 j.succ.succ = 0 := rfl
theorem hypOne_one_rest (j : Fin M) : hypOne A 1 j.succ.succ = 0 := rfl
theorem hypOne_rest_zero (i : Fin M) : hypOne A i.succ.succ 0 = 0 := rfl
theorem hypOne_rest_one (i : Fin M) : hypOne A i.succ.succ 1 = 0 := rfl
theorem hypOne_rest_rest (i j : Fin M) : hypOne A i.succ.succ j.succ.succ = A i j := rfl

end Entries

end GlobalTheory.CompanionTheory.WeilSiegel.Free
end
end
