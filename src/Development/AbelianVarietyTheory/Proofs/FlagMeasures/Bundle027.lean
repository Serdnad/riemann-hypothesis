module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle017
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle018
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle021
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle019
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryHermFrameUnipotent
public import Formalism.RealPlaceAnalysis.Bundle001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle001
public import Mathlib.Analysis.Matrix.Spectrum
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle020
public import Formalism.RealPlaceAnalysis.Bundle002
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.ContMDiffMap
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

@[expose] public section

section

open GlobalTheory.GramCount
open scoped Classical

theorem _root_.GlobalTheory.T.ncard_primitive_tuples_gram_mod_nilpotent : ∀ {A B : Type} [CommRing A] [Finite A] [CommRing B] (c : A →+* A) (c' : B →+* B), (∀ u, c (c u) = u) → ∀ (p : A), IsNilpotent p → ∀ (φ : A →+* B), Function.Surjective φ → (∀ u, φ (c u) = c' (φ u)) → (∀ u, φ u = 0 ↔ p ∣ u) → ∀ (m n : ℕ) (G : Matrix (Fin m) (Fin m) A), Set.ncard {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} = Nat.card {u : A // p ∣ u} ^ (n * m) * Set.ncard (sols c' n (G.map φ)) := by
  first | exact @GlobalTheory.GramCount.ncard_gram_mod_eq_card_ker_pow_mul | exact GlobalTheory.GramCount.ncard_gram_mod_eq_card_ker_pow_mul | (intros; apply GlobalTheory.GramCount.ncard_gram_mod_eq_card_ker_pow_mul <;> assumption)
end

section

open GlobalTheory.GramCount
open scoped Classical

theorem _root_.GlobalTheory.T.ncard_dependent_vectors_affine_gram_le : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (k n : ℕ), 2 * k ≤ n → ∀ (x : Fin k → Fin n → B), Prim c x → ∀ (g : Fin k → B), Set.ncard {y : Fin n → B | (∀ i, ip c y (x i) = g i) ∧ ∃ a : B, a ≠ 0 ∧ ∃ s : Fin k → B, a • y = ∑ i, s i • x i} ≤ 2 * q ^ n := by
  first | exact @GlobalTheory.GramCount.ncard_dependent_le | exact GlobalTheory.GramCount.ncard_dependent_le | (intros; apply GlobalTheory.GramCount.ncard_dependent_le <;> assumption)
end

section

open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

variable {A : Type} [CommRing A]

def henselHerm (c : A →+* A) (m : ℕ) (q : A) : AddSubgroup (Matrix (Fin m) (Fin m) A) where
  carrier := {H | (∀ a b, c (H b a) = H a b) ∧ ∀ a b, q ∣ H a b}
  zero_mem' := ⟨fun a b => by simp, fun a b => by simp⟩
  add_mem' := fun {H K} hH hK =>
    ⟨fun a b => by simp [Matrix.add_apply, hH.1, hK.1],
      fun a b => by simpa [Matrix.add_apply] using dvd_add (hH.2 a b) (hK.2 a b)⟩
  neg_mem' := fun {H} hH =>
    ⟨fun a b => by simp [Matrix.neg_apply, hH.1],
      fun a b => by simpa [Matrix.neg_apply] using hH.2 a b⟩

def henselGram (c : A →+* A) {m n : ℕ} (x : Fin m → Fin n → A) : Matrix (Fin m) (Fin m) A :=
  Matrix.of fun a b => ip c (x b) (x a)

def henselDiff (c : A →+* A) {m n : ℕ} (q : A) (x : Fin m → Fin n → A) :
    (Fin m → Fin n → A) →+ Matrix (Fin m) (Fin m) A where
  toFun w := Matrix.of fun a b => q * (ip c (w b) (x a) + ip c (x b) (w a))
  map_zero' := by
    ext a b
    simp [ip_zero_left, ip_zero_right]
  map_add' w w' := by
    ext a b
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, ip_add_left, ip_add_right]
    ring

theorem hensel_step [Finite A] (c : A →+* A) (hc : ∀ u, c (c u) = u) {ω : A}
    (hω : IsUnit (ω - c ω)) {p : A} (hp : c p = p) (hn : IsNilpotent p) (m n : ℕ)
    (G : Matrix (Fin m) (Fin m) A) (i : ℕ) :
    Set.ncard {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m (p ^ (i + 1))} *
      Nat.card (henselHerm c m (p ^ (i + 2))) =
    Set.ncard {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m (p ^ (i + 2))} *
      Nat.card (henselHerm c m (p ^ (i + 1))) := by
  obtain ⟨θ, -, hθ, -, -⟩ := exists_trace_one c hc hω
  have hq : c (p ^ (i + 1)) = p ^ (i + 1) := by rw [map_pow, hp]
  refine GlobalTheory.henselStep_count (DistribSMul.toAddMonoidHom (Fin m → Fin n → A) (p ^ (i + 1)))
    (henselGram c) _ _ _ G ?_ ?_ ?_
  · intro H hH
    exact ⟨hH.1, fun a b => (pow_dvd_pow p (by omega)).trans (hH.2 a b)⟩
  · rintro x ⟨y, hy⟩ w
    refine prim_of_sub_mem c hc (Ideal.span {p}) ?_ _ y fun a b => ?_
    · intro u hu
      obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton.1 hu
      exact IsNilpotent.isUnit_one_add ((Commute.all _ _).isNilpotent_mul_right hn)
    · rw [Ideal.mem_span_singleton]
      refine ⟨p ^ i * ip c (w a) (y b), ?_⟩
      simp only [Pi.add_apply, DistribSMul.toAddMonoidHom_apply, Pi.smul_apply, ip_add_left,
        ip_smul_left, hy]
      ring
  · rintro x ⟨y, hy⟩
    refine ⟨henselDiff c (p ^ (i + 1)) x, fun w => ⟨fun a b => ?_, fun a b => ?_⟩, ?_, fun w => ⟨fun a b => ?_, fun a b => ?_⟩⟩
    · simp only [henselDiff, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply, map_mul,
        map_add, hq, cj_ip c hc]
      ring
    · exact Dvd.intro _ rfl
    · intro H hH
      choose u hu using hH.2
      have hy' : ∀ a b, ip c (y b) (x a) = if a = b then 1 else 0 := by
        intro a b
        rw [← cj_ip c hc, hy]
        split_ifs <;> simp
      refine ⟨fun b => ∑ e, (θ * u e b) • y e, ?_⟩
      have : henselDiff c (p ^ (i + 1)) x (fun b => ∑ e, (θ * u e b) • y e) = H := by
        ext a b
        have h1 : p ^ (i + 1) * c (u b a) = H a b := by
          rw [← hH.1 a b, hu b a, map_mul, hq]
        simp only [henselDiff, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply,
          ip_sum_left, ip_sum_right, ip_smul_left, ip_smul_right, hy, hy', mul_ite, mul_one,
          mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul]
        linear_combination (c θ) * h1 - θ * hu a b + H a b * hθ
      rw [this, sub_self]
      exact zero_mem _
    · simp only [henselDiff, henselGram, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply,
        Matrix.sub_apply, map_mul, map_sub, map_add, hq, cj_ip c hc]
      ring
    · refine ⟨p ^ i * ip c (w b) (w a), ?_⟩
      simp only [henselDiff, henselGram, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.of_apply,
        Matrix.sub_apply, Pi.add_apply, DistribSMul.toAddMonoidHom_apply, Pi.smul_apply,
        ip_add_left, ip_add_right, ip_smul_left, ip_smul_right, hq]
      ring

theorem hensel_iter [Finite A] (c : A →+* A) (hc : ∀ u, c (c u) = u) {ω : A}
    (hω : IsUnit (ω - c ω)) {p : A} (hp : c p = p) (hn : IsNilpotent p) (m n : ℕ)
    (G : Matrix (Fin m) (Fin m) A) (k : ℕ) :
    Set.ncard {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m (p ^ (0 + 1))} *
      Nat.card (henselHerm c m (p ^ (k + 1))) =
    Set.ncard {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m (p ^ (k + 1))} *
      Nat.card (henselHerm c m (p ^ (0 + 1))) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := hensel_step c hc hω hp hn m n G k
    have hpos : 0 < Nat.card (henselHerm c m (p ^ (k + 1))) := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [show k + 1 + 1 = k + 2 from rfl]
    rw [mul_right_comm, ih, mul_right_comm, h, mul_right_comm]

theorem hensel_count : ∀ {A : Type} [CommRing A] [Finite A] (c : A →+* A), (∀ u, c (c u) = u) → ∀ (ω : A), IsUnit (ω - c ω) → ∀ (p : A), c p = p → IsNilpotent p → ∀ (m n : ℕ) (G : Matrix (Fin m) (Fin m) A), (∀ a b, c (G b a) = G a b) → Set.ncard (sols c n G) * Nat.card {H : Matrix (Fin m) (Fin m) A // (∀ a b, c (H b a) = H a b) ∧ ∀ a b, p ∣ H a b} = Set.ncard {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} := by
  intro A _ _ c hc ω hω p hp hn m n G hG
  obtain ⟨k, hk⟩ := id hn
  have h := hensel_iter c hc hω hp hn m n G k
  have hk' : p ^ (k + 1) = 0 := by rw [pow_succ, hk, zero_mul]
  have hbot : henselHerm c m (p ^ (k + 1)) = ⊥ := by
    rw [hk', eq_bot_iff]
    intro H hH
    rw [AddSubgroup.mem_bot]
    ext a b
    simpa using hH.2 a b
  rw [hbot, zero_add, pow_one, AddSubgroup.card_bot, mul_one] at h
  have e1 : {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ henselHerm c m p} =
      {x : Fin m → Fin n → A | Prim c x ∧ ∀ a b, p ∣ ip c (x b) (x a) - G a b} := by
    ext x
    refine and_congr_right fun _ => ⟨fun h => h.2, fun h => ⟨fun a b => ?_, h⟩⟩
    simp only [henselGram, Matrix.sub_apply, Matrix.of_apply, map_sub, cj_ip c hc, hG]
  have e2 : {x : Fin m → Fin n → A | x ∈ {x | Prim c x} ∧
        henselGram c x - G ∈ (⊥ : AddSubgroup (Matrix (Fin m) (Fin m) A))} = sols c n G := by
    ext x
    refine and_congr_right fun _ => ?_
    rw [AddSubgroup.mem_bot, sub_eq_zero, ← Matrix.ext_iff]
    rfl
  rw [e1, e2] at h
  exact h.symm

end GlobalTheory.GramCount
end

section

open GlobalTheory.GramCount
open scoped Classical

theorem _root_.GlobalTheory.T.isPrimitiveTuple_of_linearIndependent_finite_ring : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (χ : AddChar B ℂ), χ.IsPrimitive → ∀ (k n : ℕ) (x : Fin k → Fin n → B), (∀ s : Fin k → B, ∑ a, s a • x a = 0 → s = 0) → Prim c x := by
  first | exact @GlobalTheory.GramCount.prim_of_indep_of_isPrimitive | exact GlobalTheory.GramCount.prim_of_indep_of_isPrimitive | (intros; apply GlobalTheory.GramCount.prim_of_indep_of_isPrimitive <;> assumption)
end

section

open GlobalTheory.GramCount
open scoped Classical

theorem _root_.GlobalTheory.T.norm_gauss_sum_hermitian_form_linear_le : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (q : ℕ), 2 ≤ q → Fintype.card B = q ^ 2 → ∀ (χ : AddChar B ℂ), χ.IsPrimitive → (∀ u, χ (c u) = χ u) → ∀ (n : ℕ) (a : B), IsUnit (a + c a) → ∀ (v : Fin n → B), ‖∑ y : Fin n → B, χ (a * ip c y y + ip c y v)‖ ≤ (q : ℝ) ^ n := by
  first | exact @GlobalTheory.GramCount.norm_gauss_sum_ip_le | exact GlobalTheory.GramCount.norm_gauss_sum_ip_le | (intros; apply GlobalTheory.GramCount.norm_gauss_sum_ip_le <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.dualVectors_normalForm_mem_secondFlag : ∀ {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {r j : ℕ} (hj : j ≤ r) (e e' s : Fin r → V),
    (Matrix.of fun a b : Fin j => H.B (e (Fin.castLE hj a)) (e' (Fin.castLE hj b))).det ≠ 0 →
    (∀ a b, H.B (e' a) (e' b) = 0) →
    (∀ a b : Fin r, j ≤ a.val → b.val < j → H.B (e a) (e' b) = 0) →
    (∀ a b : Fin r, j ≤ b.val → H.B (e a) (s b) = if a = b then 1 else 0) →
    (∀ a b : Fin r, a.val < j → j ≤ b.val → H.B (e' a) (s b) = 0) →
    (∀ a b : Fin r, j ≤ a.val → j ≤ b.val → H.B (s a) (s b) = 0) →
    ∃ f : Fin r → V, (∀ a, j ≤ a.val → f a = s a) ∧
      (∀ a, a.val < j → f a ∈ Submodule.span K (e' '' {b | b.val < j})) ∧
      (∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) ∧ (∀ a b, H.B (f a) (f b) = 0) ∧
      (∀ a, a.val < j → e' a ∈ Submodule.span K (f '' {b | b.val < j})) := by
  first | exact @GlobalTheory.dual_vectors_in_second_flag | exact GlobalTheory.dual_vectors_in_second_flag | (intros; apply GlobalTheory.dual_vectors_in_second_flag <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_isometry_hermFrame_unipotent : ∀ {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) {r : ℕ} (e f e' f' : Fin r → V) (z z' : V),
    (∀ a b, H.B (e a) (e b) = 0) → (∀ a b, H.B (f a) (f b) = 0) →
    (∀ a b, H.B (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, H.B (e a) z = 0) → (∀ a, H.B (f a) z = 0) → H.B z z ≠ 0 →
    (∀ a b, H.B (e' a) (e' b) = 0) → (∀ a b, H.B (f' a) (f' b) = 0) →
    (∀ a b, H.B (e' a) (f' b) = if a = b then 1 else 0) →
    (∀ a, H.B (e' a) z' = 0) → (∀ a, H.B (f' a) z' = 0) →
    (∀ a, e' a - e a ∈ Submodule.span K (e '' {b | b < a})) →
    z' - z ∈ Submodule.span K (Set.range e) →
    ∃ m : V ≃ₗ[K] V, (∀ x y, H.B (m x) (m y) = H.B x y) ∧ (∀ a, m (e' a) = e a) ∧ (∀ a, m (f' a) = f a) ∧
      m z' = z ∧ (∀ a, m (e a) - e a ∈ Submodule.span K (e '' {b | b < a})) ∧
      (∀ y, (∀ a, H.B (e a) y = 0) → m y - y ∈ Submodule.span K (Set.range e)) ∧
      (∀ a, m.symm (e a) - e a ∈ Submodule.span K (e '' {b | b < a})) ∧
      (∀ y, (∀ a, H.B (e a) y = 0) → m.symm y - y ∈ Submodule.span K (Set.range e)) := by
  first | exact @GlobalTheory.RatIsoFrame.exists_isometry_frame_unipotent | exact GlobalTheory.RatIsoFrame.exists_isometry_frame_unipotent | (intros; apply GlobalTheory.RatIsoFrame.exists_isometry_frame_unipotent <;> assumption)
end

section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

namespace GlobalTheory

theorem rpow_three_halves_sq_eq_cube {x : ℝ} (hx : 0 ≤ x) : (x ^ ((3 : ℝ) / 2)) ^ 2 = x ^ 3 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

theorem rhoN_norm_le_and_casimir_arith :
    (∀ (n : ℕ) (ε : Fin n → Bool), Real.sqrt (nsq (rhoN ε)) ≤ 0.58 * (n : ℝ) ^ ((3 : ℝ) / 2)) ∧
    ∀ (L a n : ℝ), 0 ≤ L → 0 ≤ a → 0 ≤ n →
      2 * (L + a) ^ 2 - L ^ 2 + n ^ 3 / 12 ≤ (L + 2 * a + 0.3 * n ^ ((3 : ℝ) / 2)) ^ 2 := by
  refine ⟨fun n ε => ?_, fun L a n hL ha hn => ?_⟩
  · have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hs := rpow_three_halves_sq_eq_cube hn
    have hp : 0 ≤ (n : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hn _
    have h1 : nsq (rhoN ε) ≤ (n : ℝ) * ((n : ℝ) / 2) ^ 2 := by
      have : ∑ a : Fin n, (rhoN ε a) ^ 2 ≤ ∑ _a : Fin n, ((n : ℝ) / 2) ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        obtain ⟨h1, h2⟩ := rho_rhoN_bound ε a
        exact sq_le_sq' h1 h2
      simpa [nsq, dot, sq] using this
    refine Real.sqrt_le_iff.mpr ⟨by positivity, h1.trans ?_⟩
    rw [mul_pow, hs]
    have : (0 : ℝ) ≤ (n : ℝ) ^ 3 := by positivity
    nlinarith
  · have hs := rpow_three_halves_sq_eq_cube hn
    have hp : 0 ≤ n ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hn _
    generalize n ^ ((3 : ℝ) / 2) = s at hs hp
    rw [← hs]
    nlinarith [mul_nonneg hL hp, mul_nonneg ha hp, sq_nonneg a, sq_nonneg s]

end GlobalTheory
end

section

open Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants

theorem _root_.GlobalTheory.T.abs_sum_eigenvalues_noncompactPart_le : ∀ (n : ℕ) (ε : Fin n → Bool) (Y : Matrix (Fin n) (Fin n) ℂ) (hY : Y.IsHermitian), inP ε Y → ∀ J : Finset (Fin n), |∑ j ∈ J, hY.eigenvalues j| ≤ Real.sqrt (2 * ((min (univ.filter fun a => ε a = true).card (univ.filter fun a => ε a = false).card : ℕ) : ℝ)) * Real.sqrt (hs Y) := by
  first | exact @GlobalTheory.EigenPartialSum.abs_sum_eigenvalues_le | exact GlobalTheory.EigenPartialSum.abs_sum_eigenvalues_le | (intros; apply GlobalTheory.EigenPartialSum.abs_sum_eigenvalues_le <;> assumption)
end

section

open Formalism.REAL
open scoped ContDiff Manifold Topology

namespace GlobalTheory


open scoped ContDiff Manifold Topology in
theorem _root_.GlobalTheory.exists_contDiff_extension_of_isClosed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {S : Set E} (hS : IsClosed S) (f : E → ℂ)
    (hf : ∀ x ∈ S, ∃ (U : Set E) (F : E → ℂ), IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
      ∀ y ∈ U, y ∈ S → f y = F y) :
    ∃ F : E → ℂ, ContDiff ℝ ∞ F ∧ ∀ y ∈ S, F y = f y := by
  classical
  let t : E → Set ℂ := fun y => if y ∈ S then {f y} else Set.univ
  have ht : ∀ y, Convex ℝ (t y) := by
    intro y
    by_cases hy : y ∈ S
    · simp only [t, if_pos hy]; exact convex_singleton _
    · simp only [t, if_neg hy]; exact convex_univ
  have hloc : ∀ x : E, ∃ U ∈ 𝓝 x, ∃ g : E → ℂ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) g U ∧ ∀ y ∈ U, g y ∈ t y := by
    intro x
    by_cases hx : x ∈ S
    · obtain ⟨U, F, hU, hxU, hF, hfF⟩ := hf x hx
      refine ⟨U, hU.mem_nhds hxU, F, hF.contMDiffOn, fun y hy => ?_⟩
      by_cases hyS : y ∈ S
      · simp only [t, if_pos hyS, Set.mem_singleton_iff]; exact (hfF y hy hyS).symm
      · simp only [t, if_neg hyS, Set.mem_univ]
    · refine ⟨Sᶜ, hS.isOpen_compl.mem_nhds hx, fun _ => 0, contMDiffOn_const, fun y hy => ?_⟩
      simp only [t, if_neg (show y ∉ S from hy), Set.mem_univ]
  obtain ⟨g, hg⟩ := exists_contMDiffMap_forall_mem_convex_of_local 𝓘(ℝ, E) (n := ⊤) ht hloc
  refine ⟨g, g.contMDiff.contDiff, fun y hy => ?_⟩
  have hgy := hg y
  simpa only [t, if_pos hy, Set.mem_singleton_iff] using hgy


open scoped ContDiff Manifold Topology in
theorem _root_.GlobalTheory.smoothOnG_exists_contDiff_extension :
    ∀ (n : ℕ) (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → ℂ), _root_.Formalism.REAL.SmoothOnG ε f →
      ∃ F : (Fin n → Fin n → ℂ) → ℂ, ContDiff ℝ ∞ F ∧
        ∀ g : Matrix (Fin n) (Fin n) ℂ, _root_.Formalism.REAL.inUJ ε g → F (fun i j => g i j) = f g := by
  intro n ε f hf
  let S : Set (Fin n → Fin n → ℂ) := {x | _root_.Formalism.REAL.inUJ ε (Matrix.of x)}
  have hS : IsClosed S := by
    have h0 : Continuous (fun x : Fin n → Fin n → ℂ => Matrix.of x) := continuous_id
    have hc : Continuous
        (fun x : Fin n → Fin n → ℂ => Matrix.conjTranspose (Matrix.of x) * _root_.Formalism.REAL.Jm ε * Matrix.of x) :=
      (h0.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul h0
    exact isClosed_eq hc continuous_const
  obtain ⟨F, hF, hFS⟩ := _root_.GlobalTheory.exists_contDiff_extension_of_isClosed hS
    (fun x => f (Matrix.of x)) (by
      intro x hx
      unfold _root_.Formalism.REAL.SmoothOnG at hf
      obtain ⟨U, G, hU, hxU, hG, hfG⟩ := hf (Matrix.of x) hx
      let U' : Set (Fin n → Fin n → ℂ) := U
      let G' : (Fin n → Fin n → ℂ) → ℂ := G
      have hU' : IsOpen U' := hU
      have hG' : ContDiffOn ℝ ∞ G' U' := hG
      exact ⟨U', G', hU', hxU, hG', fun y hy hyS => hfG (Matrix.of y) hy hyS⟩)
  exact ⟨F, hF, fun g hg => hFS (fun i j => g i j) hg⟩

end GlobalTheory
end

section

open Finset Matrix

noncomputable section

namespace GlobalTheory.Dec.GelfSepProof


open PowerSeries Matrix in
theorem _root_.GlobalTheory.Dec.GelfSepProof.gen {n : ℕ} (l : Fin n → ℂ) :
    ((1 : PowerSeries ℂ) -
        PowerSeries.X * PowerSeries.mk fun (k : ℕ) ↦ ∑ a : Fin n, ∑ b : Fin n, (_root_.Formalism.REAL.Amat l ^ k) a b) *
      ∏ a : Fin n, ((1 : PowerSeries ℂ) - (PowerSeries.C : ℂ → PowerSeries ℂ) (l a) * PowerSeries.X) =
    ∏ a : Fin n,
      ((1 : PowerSeries ℂ) -
        ((PowerSeries.C : ℂ → PowerSeries ℂ) (l a) + (1 : PowerSeries ℂ)) * PowerSeries.X) := by
  have hA : ∀ a b, _root_.Formalism.REAL.Amat l a b = if a = b then l a else if a < b then -1 else 0 := by
    intro a b
    unfold _root_.Formalism.REAL.Amat
    rfl
  set A := _root_.Formalism.REAL.Amat l with hAdef
  let Y : Matrix (Fin n) (Fin n) (PowerSeries ℂ) := A.map (PowerSeries.C : ℂ → PowerSeries ℂ)
  let B : Matrix (Fin n) (Fin n) (PowerSeries ℂ) :=
    Matrix.of fun a b => PowerSeries.mk fun k => (A ^ k) a b
  have hB : (1 - (X : PowerSeries ℂ) • Y) * B = 1 := by
    rw [sub_mul, one_mul, smul_mul_assoc]
    ext a b k
    rcases k with _ | k
    · simp [B, Matrix.one_apply]

    · simp [B, Y, Matrix.mul_apply, Matrix.one_apply, pow_succ', PowerSeries.coeff_succ_X_mul,
        map_sum]
      split_ifs <;> simp
  let c : Matrix (Fin n) (Fin 1) (PowerSeries ℂ) := replicateCol (Fin 1) 1
  let R : Matrix (Fin 1) (Fin n) (PowerSeries ℂ) := replicateRow (Fin 1) 1
  let J : Matrix (Fin n) (Fin n) (PowerSeries ℂ) := Matrix.of fun _ _ => 1
  let U : Matrix (Fin n) (Fin 1) (PowerSeries ℂ) := -((X : PowerSeries ℂ) • (B * c))
  have hcR : c * R = J := by
    ext a b
    simp [c, R, J, Matrix.mul_apply]
  have hBc : (1 - (X : PowerSeries ℂ) • Y) * (B * c) = c := by
    rw [← Matrix.mul_assoc, hB, Matrix.one_mul]
  have hfactor : (1 - (X : PowerSeries ℂ) • Y) * (1 + U * R) =
      1 - (X : PowerSeries ℂ) • Y - (X : PowerSeries ℂ) • J := by
    have hU : (1 - (X : PowerSeries ℂ) • Y) * U = -((X : PowerSeries ℂ) • c) := by
      show (1 - (X : PowerSeries ℂ) • Y) * -((X : PowerSeries ℂ) • (B * c)) = _
      rw [Matrix.mul_neg, Matrix.mul_smul, hBc]
    rw [mul_add, mul_one, ← Matrix.mul_assoc, hU, Matrix.neg_mul, Matrix.smul_mul, hcR]
    abel
  have hdet1 : (1 - (X : PowerSeries ℂ) • Y).det = ∏ a : Fin n, (1 - C (l a) * X) := by
    rw [Matrix.det_of_isUpperTriangular]
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp [Y, hA, mul_comm]
    · intro a b hab
      have hba : b < a := hab
      simp [Y, hA, hba.ne', not_lt_of_gt hba, Matrix.one_apply_ne hba.ne']
  have hdet2 : (1 - (X : PowerSeries ℂ) • Y - (X : PowerSeries ℂ) • J).det =
      ∏ a : Fin n, (1 - (C (l a) + 1) * X) := by
    rw [Matrix.det_of_isLowerTriangular]
    · refine Finset.prod_congr rfl fun a _ => ?_
      simp [Y, J, hA]
      ring
    · intro a b hab
      have hab' : a < b := hab
      simp [Y, J, hA, hab'.ne, hab', Matrix.one_apply_ne hab'.ne]
  have hdet3 : (1 + U * R).det =
      1 - X * PowerSeries.mk fun k => ∑ a : Fin n, ∑ b : Fin n, (A ^ k) a b := by
    rw [Matrix.det_one_add_mul_comm, Matrix.det_unique]
    simp [U, R, B, c, Matrix.mul_apply, Finset.mul_sum, sub_eq_add_neg]
    simp only [← Finset.mul_sum]
    congr 1
    ext k

    simp [PowerSeries.coeff_mk, map_sum]
  rw [← hdet2, ← hfactor, Matrix.det_mul, hdet1, hdet3, mul_comm]



end GlobalTheory.Dec.GelfSepProof

namespace GlobalTheory.Dec

end GlobalTheory.Dec
end
end

section

open MeasureTheory NumberField Finset

theorem _root_.GlobalTheory.T.sum_absNorm_rpow_neg_le_dedekindZeta_bound : ∀ (K : Type) [Field K] [NumberField K] (s : ℝ), 1 < s → ∀ (S : Finset (Ideal (𝓞 K))), (∀ I ∈ S, I ≠ ⊥) → ∑ I ∈ S, (Ideal.absNorm I : ℝ) ^ (-s) ≤ (s / (s - 1)) ^ Module.finrank ℚ K := by
  first | exact @GlobalTheory.IdealZetaSum.sum_absNorm_rpow_neg_le | exact GlobalTheory.IdealZetaSum.sum_absNorm_rpow_neg_le | (intros; apply GlobalTheory.IdealZetaSum.sum_absNorm_rpow_neg_le <;> assumption)
end
