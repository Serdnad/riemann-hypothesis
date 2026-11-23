module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle198
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.MeasureTheory.Constructions.Pi
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle199
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle201
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle202
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle184
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FormalDegreeBessel.StatementWR
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle162
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle167
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle163
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Max

@[expose] public section

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCov

theorem existsUnique_mul_mem_box_of_layers : ∀ (M I A B D : Type) [Monoid M] [Fintype I] [AddCommGroup A] [AddCommGroup B] [AddCommGroup D] (ht : I → ℕ) (C : (I → A) × B × D → M) (Γ : Set M) (Λ₁ F₁ : I → Set A) (Λ₂ F₂ : Set B) (Λ₃ F₃ : Set D), Function.Injective C → C 0 = 1 → (∀ p q, ∃ w, C p * C q = C w ∧ (∀ i, (∀ l, ht l < ht i → p.1 l = 0) → w.1 i = p.1 i + q.1 i) ∧ (p.1 = 0 → w.2.1 = p.2.1 + q.2.1) ∧ (p.1 = 0 → p.2.1 = 0 → w.2.2 = p.2.2 + q.2.2)) → Γ ⊆ Set.range C → (1 : M) ∈ Γ → (∀ a ∈ Γ, ∀ b ∈ Γ, a * b ∈ Γ) → (∀ a ∈ Γ, ∃ b ∈ Γ, b * a = 1) → (∀ p, C p ∈ Γ → ∀ i, p.1 i ∈ Λ₁ i) → (∀ p, C p ∈ Γ → p.1 = 0 → p.2.1 ∈ Λ₂) → (∀ p, C p ∈ Γ → p.1 = 0 → p.2.1 = 0 → p.2.2 ∈ Λ₃) → (∀ i, ∀ a ∈ Λ₁ i, ∃ p, C p ∈ Γ ∧ p.1 = Pi.single i a) → (∀ b ∈ Λ₂, ∃ p, C p ∈ Γ ∧ p.1 = 0 ∧ p.2.1 = b) → (∀ d ∈ Λ₃, C (0, 0, d) ∈ Γ) → (∀ i a, ∃! b, b ∈ Λ₁ i ∧ b + a ∈ F₁ i) → (∀ a, ∃! b, b ∈ Λ₂ ∧ b + a ∈ F₂) → (∀ a, ∃! b, b ∈ Λ₃ ∧ b + a ∈ F₃) → ∀ q, ∃! m, m ∈ Γ ∧ m * C q ∈ C '' (Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃) := by
  intro M I A B D _ _ _ _ _ ht C Γ Λ₁ F₁ Λ₂ F₂ Λ₃ F₃ hC hC0 hmul hΓC h1 hmulΓ hinv h1Λ h2Λ h3Λ
    h1s h2s h3s hF₁ hF₂ hF₃ q
  classical

  have h0Γ : C 0 ∈ Γ := hC0 ▸ h1
  have z1 : ∀ i, (0 : A) ∈ Λ₁ i := fun i => h1Λ 0 h0Γ i
  have z2 : (0 : B) ∈ Λ₂ := h2Λ 0 h0Γ rfl
  have z3 : (0 : D) ∈ Λ₃ := h3Λ 0 h0Γ rfl rfl

  have layer1 : ∀ s : Finset I, ∀ q, ∃ m ∈ Γ, ∃ w, m * C q = C w ∧ ∀ i ∈ s, w.1 i ∈ F₁ i := by
    intro s
    induction s using Finset.induction_on_max_value ht with
    | empty => exact fun q => ⟨1, h1, q, one_mul _, by simp⟩
    | insert a s has hmax ih =>
      intro q
      obtain ⟨m, hm, w, hmw, hw⟩ := ih q
      obtain ⟨b, ⟨hbΛ, hbF⟩, -⟩ := hF₁ a (w.1 a)
      obtain ⟨p, hpΓ, hp1⟩ := h1s a b hbΛ
      obtain ⟨w', hw'eq, hw'1, -, -⟩ := hmul p w
      refine ⟨C p * m, hmulΓ _ hpΓ _ hm, w', by rw [mul_assoc, hmw, hw'eq], ?_⟩
      have key : ∀ i, ht i ≤ ht a → w'.1 i = p.1 i + w.1 i := fun i hi =>
        hw'1 i (fun l hl => by
          rw [hp1]; exact Pi.single_eq_of_ne (ne_of_apply_ne ht (by omega)) _)
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · rw [key i le_rfl, hp1, Pi.single_eq_same]; exact hbF
      · have hia : i ≠ a := fun h => has (h ▸ hi)
        rw [key i (hmax i hi), hp1, Pi.single_eq_of_ne hia, zero_add]; exact hw i hi

  have hex : ∃ m ∈ Γ, ∃ u, m * C q = C u ∧ u ∈ Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃ := by
    obtain ⟨m, hm, w, hmw, hw⟩ := layer1 Finset.univ q
    obtain ⟨b, ⟨hbΛ, hbF⟩, -⟩ := hF₂ w.2.1
    obtain ⟨p, hpΓ, hp1, hp2⟩ := h2s b hbΛ
    obtain ⟨w', hw'eq, hw'1, hw'2, -⟩ := hmul p w
    obtain ⟨d, ⟨hdΛ, hdF⟩, -⟩ := hF₃ w'.2.2
    obtain ⟨w'', hw''eq, hw''1, hw''2, hw''3⟩ := hmul (0, 0, d) w'
    refine ⟨C (0, 0, d) * (C p * m), hmulΓ _ (h3s d hdΛ) _ (hmulΓ _ hpΓ _ hm), w'',
      by rw [mul_assoc, mul_assoc, hmw, hw'eq, hw''eq], ?_⟩
    have e1 : ∀ i, w'.1 i = w.1 i := fun i => by
      rw [hw'1 i (fun l _ => by rw [hp1]; rfl), hp1]; exact zero_add _
    have e1' : ∀ i, w''.1 i = w'.1 i := fun i => by
      rw [hw''1 i (fun l _ => rfl)]; exact zero_add _
    have e2 : w''.2.1 = w'.2.1 := by rw [hw''2 rfl]; exact zero_add _
    refine Set.mk_mem_prod ?_ (Set.mk_mem_prod ?_ ?_)
    · exact Set.mem_univ_pi.2 fun i => by
        rw [e1', e1]; exact hw i (Finset.mem_univ i)
    · rw [e2, hw'2 hp1, hp2]; exact hbF
    · rw [hw''3 rfl rfl]; exact hdF

  have rigid : ∀ g ∈ Γ, ∀ u u', u ∈ Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃ →
      u' ∈ Set.pi Set.univ F₁ ×ˢ F₂ ×ˢ F₃ → g * C u = C u' → g = 1 := by
    intro g hg u u' hu hu' hgu
    obtain ⟨p, rfl⟩ := hΓC hg
    obtain ⟨w, hweq, hw1, hw2, hw3⟩ := hmul p u
    have hwu : w = u' := hC (hweq.symm.trans hgu)
    rw [hwu] at hw1 hw2 hw3
    simp only [Set.mem_prod, Set.mem_univ_pi] at hu hu'

    have key : ∀ n, ∀ i, ht i = n → p.1 i = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | _ n ih =>
        intro i hi
        have e := hw1 i (fun l hl => ih (ht l) (hi ▸ hl) l rfl)
        exact (hF₁ i (u.1 i)).unique ⟨h1Λ p hg i, e ▸ hu'.1 i⟩ ⟨z1 i, (zero_add (u.1 i)).symm ▸ hu.1 i⟩
    have hp1 : p.1 = 0 := funext fun i => key _ i rfl
    have hp2 : p.2.1 = 0 :=
      (hF₂ u.2.1).unique ⟨h2Λ p hg hp1, hw2 hp1 ▸ hu'.2.1⟩ ⟨z2, (zero_add u.2.1).symm ▸ hu.2.1⟩
    have hp3 : p.2.2 = 0 :=
      (hF₃ u.2.2).unique ⟨h3Λ p hg hp1 hp2, hw3 hp1 hp2 ▸ hu'.2.2⟩
        ⟨z3, (zero_add u.2.2).symm ▸ hu.2.2⟩
    have hp : p = 0 := Prod.ext hp1 (Prod.ext hp2 hp3)
    rw [hp, hC0]

  obtain ⟨m, hmΓ, u, hmu, hu⟩ := hex
  refine ⟨m, ⟨hmΓ, u, hu, hmu.symm⟩, ?_⟩
  rintro m' ⟨hm'Γ, u', hu', hm'u⟩
  obtain ⟨n, hnΓ, hnm⟩ := hinv m hmΓ
  have hg : m' * n = 1 := by
    refine rigid (m' * n) (hmulΓ _ hm'Γ _ hnΓ) u u' hu hu' ?_
    rw [← hmu, hm'u, ← mul_assoc, mul_assoc m', hnm, mul_one]
  calc m' = m' * (n * m) := by rw [hnm, mul_one]
    _ = m' * n * m := (mul_assoc _ _ _).symm
    _ = m := by rw [hg, one_mul]

end GlobalTheory.DegVol.RefCov
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.MeanDual

theorem _root_.GlobalTheory.T.det_matrix_sandwich_linear_map : ∀ (ι : Type) [Fintype ι] (j : ℕ) (A B : ι → Matrix (Fin j) (Fin j) ℂ) (L : (ι → Fin j → Fin j → ℂ) →ₗ[ℝ] (ι → Fin j → Fin j → ℂ)), (∀ h w, Matrix.of (L h w) = A w * Matrix.of (h w) * B w) → LinearMap.det L = ∏ w, (‖(A w).det‖ ^ 2 * ‖(B w).det‖ ^ 2) ^ j := by
  first | exact @GlobalTheory.MatMulDet.det_real_mul_mul | exact GlobalTheory.MatMulDet.det_real_mul_mul | (intros; apply GlobalTheory.MatMulDet.det_real_mul_mul <;> assumption)
end

section

open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.RefCov

theorem prod_pow_bounds : ∀ (v : ℝ) (f k r m a b : ℕ) (x : ℝ≥0∞), 1 ≤ v → m ≤ r → a ≤ r ^ 2 → b ≤ r ^ 2 → ENNReal.ofReal ((8 * v) ^ (-(f : ℝ))) ^ m ≤ x → x ≤ ENNReal.ofReal ((8 * v) ^ (f : ℝ)) ^ m → ENNReal.ofReal (v ^ (k * m * f) / (8 * v) ^ (2 * (r + 1) ^ 2 * f)) ≤ ENNReal.ofReal (v ^ f) ^ a * (ENNReal.ofReal ((v ^ f) ^ (k + 1)) ^ m * (ENNReal.ofReal (v ^ f) ^ b * x)) ∧ ENNReal.ofReal (v ^ f) ^ a * (ENNReal.ofReal ((v ^ f) ^ (k + 1)) ^ m * (ENNReal.ofReal (v ^ f) ^ b * x)) ≤ ENNReal.ofReal (v ^ (k * m * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f)) := by
  intro v f k r m a b x hv hm ha hb hlo hhi
  have hv0 : 0 < v := by linarith
  have hw1 : 1 ≤ 8 * v := by linarith
  have hw0 : 0 < 8 * v := by linarith
  have hvw : v ≤ 8 * v := by linarith
  have hvf : 0 ≤ v ^ f := by positivity
  have key : ∀ y : ℝ, 0 ≤ y →
      ENNReal.ofReal (v ^ f) ^ a * (ENNReal.ofReal ((v ^ f) ^ (k + 1)) ^ m *
        (ENNReal.ofReal (v ^ f) ^ b * ENNReal.ofReal y ^ m)) =
      ENNReal.ofReal (v ^ (k * m * f) * (v ^ (f * (a + m + b)) * y ^ m)) := by
    intro y hy
    rw [← ENNReal.ofReal_pow hvf, ← ENNReal.ofReal_pow hvf, ← ENNReal.ofReal_pow hy,
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  rw [Real.rpow_neg hw0.le, Real.rpow_natCast] at hlo
  rw [Real.rpow_natCast] at hhi
  constructor
  · refine le_trans ?_ (mul_le_mul_right (mul_le_mul_right (mul_le_mul_right hlo _) _) _)
    rw [key _ (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : 1 ≤ v ^ (f * (a + m + b)) := one_le_pow₀ hv
    have h2 : ((8 * v) ^ (2 * (r + 1) ^ 2 * f))⁻¹ ≤ ((8 * v) ^ f)⁻¹ ^ m := by
      rw [inv_pow, ← pow_mul]
      apply inv_anti₀ (by positivity)
      apply pow_le_pow_right₀ hw1
      rw [mul_comm f m]
      apply Nat.mul_le_mul_right
      nlinarith
    exact h2.trans (le_mul_of_one_le_left (by positivity) h1)
  · refine le_trans (mul_le_mul_right (mul_le_mul_right (mul_le_mul_right hhi _) _) _) ?_
    rw [key _ (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have h1 : v ^ (f * (a + m + b)) ≤ (8 * v) ^ (f * (a + m + b)) :=
      pow_le_pow_left₀ hv0.le hvw _
    calc v ^ (f * (a + m + b)) * ((8 * v) ^ f) ^ m
        ≤ (8 * v) ^ (f * (a + m + b)) * ((8 * v) ^ f) ^ m :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (8 * v) ^ ((a + m + b + m) * f) := by ring
      _ ≤ (8 * v) ^ (2 * (r + 1) ^ 2 * f) := by
          apply pow_le_pow_right₀ hw1
          apply Nat.mul_le_mul_right
          nlinarith

end GlobalTheory.DegVol.RefCov
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.exists_unitary_leading_term_of_skew_layer : ∀ (R K : Type) [CommRing R] [Field K] [StarRing K] [Algebra R K] (n m : ℕ) (J : Matrix (Fin n) (Fin n) K) (A : ℕ → Submodule R (Matrix (Fin n) (Fin n) K)) (w : R), Jᴴ = J → J.det ≠ 0 → algebraMap R K w + star (algebraMap R K w) = 1 → (∀ c, A (c + 1) ≤ A c) → A m = ⊥ → (∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1)) → (∀ c, ∀ X ∈ A c, J⁻¹ * Xᴴ * J ∈ A c) → ∀ c, ∀ X ∈ A c, J⁻¹ * Xᴴ * J = -X → ∃ Y ∈ A (c + 1), (1 + X + Y)ᴴ * J * (1 + X + Y) = J := by
  first | exact @GlobalTheory.RadCov.exists_unitary_of_skew_layer | exact GlobalTheory.RadCov.exists_unitary_of_skew_layer | (intros; apply GlobalTheory.RadCov.exists_unitary_of_skew_layer <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

theorem _root_.GlobalTheory.T.lintegral_pi_prod_mul_fintype_product : ∀ (ι : Type) [Fintype ι] (X : ι → Type) [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SigmaFinite ν] (f : ∀ i, X i → ENNReal) (g : Y → ENNReal), (∀ i, Measurable (f i)) → Measurable g → ∫⁻ p, (∏ i, f i (p.1 i)) * g p.2 ∂((Measure.pi μ).prod ν) = (∏ i, ∫⁻ y, f i y ∂(μ i)) * ∫⁻ y, g y ∂ν := by
  first | exact @GlobalTheory.StabUnfold.lintegral_pi_prod_mul | exact GlobalTheory.StabUnfold.lintegral_pi_prod_mul | (intros; apply GlobalTheory.StabUnfold.lintegral_pi_prod_mul <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.right_invariant_eq_smul_left_invariant_probability : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (K : Set G) (μ ν : Measure G) [SFinite μ] [SFinite ν], μ Kᶜ = 0 → ν Kᶜ = 0 → μ Set.univ = 1 → (∀ k ∈ K, μ.map (fun g => k * g) = μ) → (∀ k ∈ K, ν.map (fun g => g * k) = ν) → ν = ν Set.univ • μ := by
  first | exact @GlobalTheory.IwConst.right_inv_eq_smul_left_inv | exact GlobalTheory.IwConst.right_inv_eq_smul_left_inv | (intros; apply GlobalTheory.IwConst.right_inv_eq_smul_left_inv <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

theorem _root_.GlobalTheory.T.iwasawa_lintegral_unfold_compact_levi : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (M L : Set G) (μN μM μK νL : Measure G) [SFinite μN] [SFinite μM] [SFinite μK] [SFinite νL] (δ φ ψ : G → ENNReal), Measurable δ → Measurable φ → Measurable ψ → μM Mᶜ = 0 → νL Lᶜ = 0 → (∀ l ∈ L, μM.map (fun g => g * l) = μM) → (∀ l ∈ L, μK.map (fun g => l * g) = μK) → (∀ l ∈ L, ∀ m ∈ M, δ (m * l) = δ m) → νL Set.univ * ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ψ k ∂μK ∂μM ∂μN = ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, φ (u * m * k) * ∫⁻ l, ψ (l * k) ∂νL ∂μK ∂μM ∂μN := by
  first | exact @GlobalTheory.IwConst.iwasawa_unfold_lintegral | exact GlobalTheory.IwConst.iwasawa_unfold_lintegral | (intros; apply GlobalTheory.IwConst.iwasawa_unfold_lintegral <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

theorem _root_.GlobalTheory.T.lintegral_Ioi_comp_const_div_change_of_var : ∀ (κ : ℝ), 0 < κ → ∀ w : ℝ → ENNReal, Measurable w → ∫⁻ t in Set.Ioi (0 : ℝ), w (κ / t) * ENNReal.ofReal t / ENNReal.ofReal t = ENNReal.ofReal κ * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  first | exact @GlobalTheory.lintegral_Ioi_comp_const_div_mul_div | exact GlobalTheory.lintegral_Ioi_comp_const_div_mul_div | (intros; apply GlobalTheory.lintegral_Ioi_comp_const_div_mul_div <;> assumption)
end
