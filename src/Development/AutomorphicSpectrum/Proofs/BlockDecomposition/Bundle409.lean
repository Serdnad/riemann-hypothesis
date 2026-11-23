module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle392
public import GroundTheory.AutomorphicForms.HilbertSchmidt
public import Mathlib.MeasureTheory.Function.L2Space
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle398
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumAdmissibility
import Formalism.LocalToGlobal.IndefiniteReal.Bundle009
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle397
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels

@[expose] public section

section

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA

private theorem avg_conj_coef_ge_lemma {Γ : Type} [Group Γ] [TopologicalSpace Γ] {B : Type}
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] {ρ : Γ → (B →L[ℂ] B)} (hρ : IsU ρ)
    (g : Γ) (x y : B) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(ρ g : B →ₗ[ℂ] B), hρ.norm g⟩ : B →ₗᵢ[ℂ] B).inner_map_map x y

private theorem avg_conj_coef_ge_lemma_2 {Γ : Type} [Group Γ] [TopologicalSpace Γ] {B : Type}
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] {ρ : Γ → (B →L[ℂ] B)} (hρ : IsU ρ)
    (g h : Γ) (x : B) : ρ g (ρ h x) = ρ (g * h) x := by
  rw [hρ.mul]; rfl

private theorem avg_conj_coef_ge_lemma_3 {Γ : Type} [Group Γ] [TopologicalSpace Γ] {B : Type}
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] {ρ : Γ → (B →L[ℂ] B)} (hρ : IsU ρ)
    (g : Γ) (x y : B) : ⟪ρ g x, y⟫_ℂ = ⟪x, ρ g⁻¹ y⟫_ℂ := by
  have e : y = ρ g (ρ g⁻¹ y) := by
    rw [avg_conj_coef_ge_lemma_2 hρ, mul_inv_cancel, hρ.one]; rfl
  conv_lhs => rw [e]
  exact avg_conj_coef_ge_lemma hρ g x _

theorem avg_conj_coef_ge : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ) (hσ : IsU σ) (hρ : IsU ρ), IsFd ν σ d →
    ∀ w₀ : A, ‖w₀‖ = 1 → ∀ (hc : Integrable (fun g => star ⟪w₀, σ g w₀⟫_ℂ) ν) (i : A →L[ℂ] B), IsIsoMap σ ρ i → ∀ z : B,
    ‖⟪z, i w₀⟫_ℂ‖ ^ 2 / d ≤ (⟪z, coefOp ν ρ hρ (fun g => star ⟪w₀, σ g w₀⟫_ℂ) hc z⟫_ℂ).re := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hFd w₀ hw₀ hc i hi z
  obtain ⟨hd, hFd'⟩ := hFd
  have hmap : ∀ g x, i (σ g x) = ρ g (i x) := hi.1
  have hiso : ∀ x, ‖i x‖ = ‖x‖ := hi.2
  set f : Γ → ℂ := fun g => star ⟪w₀, σ g w₀⟫_ℂ with hf
  set T := coefOp ν ρ hρ f hc with hT
  have hw1 : ⟪w₀, w₀⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw₀]; simp
  set a := ContinuousLinearMap.adjoint i z with ha
  have hA : ⟪i w₀, T z⟫_ℂ = ⟪i w₀, z⟫_ℂ / (d : ℂ) := by
    rw [hT, inner_coefOp]
    have hpt : ∀ g, f g * ⟪i w₀, ρ g z⟫_ℂ = ⟪w₀, σ g a⟫_ℂ * star ⟪w₀, σ g w₀⟫_ℂ := by
      intro g
      have e1 : ⟪i w₀, ρ g z⟫_ℂ = ⟪w₀, σ g a⟫_ℂ := by
        calc ⟪i w₀, ρ g z⟫_ℂ = ⟪ρ g⁻¹ (i w₀), z⟫_ℂ := by
              rw [avg_conj_coef_ge_lemma_3 hρ, inv_inv]
          _ = ⟪i (σ g⁻¹ w₀), z⟫_ℂ := by rw [hmap]
          _ = ⟪σ g⁻¹ w₀, a⟫_ℂ := by rw [ha, ContinuousLinearMap.adjoint_inner_right]
          _ = ⟪w₀, σ g a⟫_ℂ := by rw [avg_conj_coef_ge_lemma_3 hσ, inv_inv]
      rw [e1, hf, mul_comm]
    simp_rw [hpt]
    rw [(hFd' a w₀ w₀ w₀).2, hw1, mul_one, ha, ContinuousLinearMap.adjoint_inner_right]
  have hB1 : ∀ g, ⟪ρ g z, T z⟫_ℂ = ∫ k, f (g * k) * ⟪z, ρ k z⟫_ℂ ∂ν := by
    intro g
    rw [hT, inner_coefOp]
    have e : ∀ h, f h * ⟪ρ g z, ρ h z⟫_ℂ = f (g * (g⁻¹ * h)) * ⟪z, ρ (g⁻¹ * h) z⟫_ℂ := by
      intro h
      rw [mul_inv_cancel_left, avg_conj_coef_ge_lemma_3 hρ, avg_conj_coef_ge_lemma_2 hρ]
    simp_rw [e]
    exact integral_mul_left_eq_self (fun k => f (g * k) * ⟪z, ρ k z⟫_ℂ) g⁻¹
  set φ : Γ → ℂ := fun k => ⟪z, ρ k z⟫_ℂ with hφ
  have hfc : Continuous f := (continuous_const.inner (hσ.cont w₀)).star
  have hφc : Continuous φ := continuous_const.inner (hρ.cont z)
  have hφb : ∀ k, ‖φ k‖ ≤ ‖z‖ ^ 2 := by
    intro k
    calc ‖φ k‖ ≤ ‖z‖ * ‖ρ k z‖ := norm_inner_le_norm _ _
      _ = ‖z‖ ^ 2 := by rw [hρ.norm, sq]
  have hcs : Integrable (fun g => star (f g)) ν :=
    hc.mono (hfc.star.aestronglyMeasurable) (ae_of_all _ fun g => by rw [norm_star])
  have hG : Integrable (fun p : Γ × Γ => f p.1 * star (f (p.1 * p.2))) (ν.prod ν) := by
    have h0 : Integrable (fun p : Γ × Γ => f p.1 * star (f p.2)) (ν.prod ν) := hc.mul_prod hcs
    exact (measurePreserving_prod_mul ν ν).integrable_comp_of_integrable h0
  have hF : Integrable (Function.uncurry fun g k => f g * (star (f (g * k)) * star (φ k))) (ν.prod ν) := by
    refine Integrable.mono' (hG.norm.mul_const (‖z‖ ^ 2)) ?_ (ae_of_all _ fun p => ?_)
    · exact (show Continuous (fun p : Γ × Γ => f p.1 * (star (f (p.1 * p.2)) * star (φ p.2))) from
        (hfc.comp continuous_fst).mul (((hfc.comp (continuous_fst.mul continuous_snd)).star).mul
          ((hφc.comp continuous_snd).star))).aestronglyMeasurable
    · show ‖f p.1 * (star (f (p.1 * p.2)) * star (φ p.2))‖ ≤ ‖f p.1 * star (f (p.1 * p.2))‖ * ‖z‖ ^ 2
      simp only [norm_mul, norm_star]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hφb _) (norm_nonneg _)) (norm_nonneg _)
  have hinner : ∀ k, ∫ g, f g * star (f (g * k)) ∂ν = star (f k) / (d : ℂ) := by
    intro k
    have e : ∀ g, f g * star (f (g * k)) = ⟪w₀, σ g (σ k w₀)⟫_ℂ * star ⟪w₀, σ g w₀⟫_ℂ := by
      intro g
      simp only [hf, star_star]
      rw [← avg_conj_coef_ge_lemma_2 hσ]
      ring
    simp_rw [e]
    rw [(hFd' (σ k w₀) w₀ w₀ w₀).2, hw1, mul_one]
    simp only [hf, star_star]
  have hB2 : ⟪T z, T z⟫_ℂ = star ⟪z, T z⟫_ℂ / (d : ℂ) := by
    have s1 : ⟪T z, T z⟫_ℂ = ∫ g, f g * ⟪T z, ρ g z⟫_ℂ ∂ν := inner_coefOp ν ρ hρ f hc (T z) z
    have s2 : ∀ g, f g * ⟪T z, ρ g z⟫_ℂ = ∫ k, f g * (star (f (g * k)) * star (φ k)) ∂ν := by
      intro g
      rw [← inner_conj_symm, hB1 g, ← integral_conj, ← integral_const_mul]
      simp only [map_mul, starRingEnd_apply, hφ]
    have s3 : ∀ k, ∫ g, f g * (star (f (g * k)) * star (φ k)) ∂ν = star (f k) / (d : ℂ) * star (φ k) := by
      intro k
      simp_rw [← mul_assoc]
      rw [integral_mul_const, hinner k]
    have s4 : ⟪z, T z⟫_ℂ = ∫ k, f k * φ k ∂ν := inner_coefOp ν ρ hρ f hc z z
    have s5 : ∀ k, star (f k) / (d : ℂ) * star (φ k) = (starRingEnd ℂ) (f k * φ k) / (d : ℂ) := by
      intro k
      rw [map_mul, starRingEnd_apply, starRingEnd_apply]
      ring
    rw [s1]
    simp_rw [s2]
    rw [integral_integral_swap hF]
    simp_rw [s3, s5]
    rw [integral_div, integral_conj, ← s4, starRingEnd_apply]
  have hTn : ⟪T z, T z⟫_ℂ = ((‖T z‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hX : star ⟪z, T z⟫_ℂ = ((d * ‖T z‖ ^ 2 : ℝ) : ℂ) := by
    have h := hB2.symm.trans hTn
    rw [div_eq_iff hdC] at h
    rw [h]
    push_cast
    ring
  have hre : (⟪z, T z⟫_ℂ).re = d * ‖T z‖ ^ 2 := by
    have h := congrArg Complex.re hX
    rw [Complex.ofReal_re] at h
    rw [← h]
    exact (Complex.conj_re _).symm
  have hle : ‖⟪z, i w₀⟫_ℂ‖ ≤ d * ‖T z‖ := by
    have h1' : ‖⟪i w₀, T z⟫_ℂ‖ ≤ ‖T z‖ := by
      calc ‖⟪i w₀, T z⟫_ℂ‖ ≤ ‖i w₀‖ * ‖T z‖ := norm_inner_le_norm _ _
        _ = ‖T z‖ := by rw [hiso, hw₀, one_mul]
    have h2' : ‖⟪z, i w₀⟫_ℂ‖ = d * ‖⟪i w₀, T z⟫_ℂ‖ := by
      rw [hA, norm_div, norm_inner_symm, Complex.norm_real, Real.norm_of_nonneg hd.le]
      field_simp
    rw [h2']
    exact mul_le_mul_of_nonneg_left h1' hd.le
  rw [hre, div_le_iff₀ hd]
  have hsq : ‖⟪z, i w₀⟫_ℂ‖ ^ 2 ≤ (d * ‖T z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  nlinarith [hsq]

end GlobalTheory.CompanionTheory.RgHeA
end
end

section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RgHeA.CoefHS

section SlopeTestRemainingChoices

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  {ν : Measure Γ} {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B]

theorem memLp_coef {σ : Γ → (A →L[ℂ] A)} (hσ : IsU σ) {d : ℝ} (hd : IsFd ν σ d) (w v : A) :
    MemLp (fun g => ⟪w, σ g v⟫_ℂ) 2 ν := by
  have hm : AEStronglyMeasurable (fun g => ⟪w, σ g v⟫_ℂ) ν :=
    (continuous_const.inner (hσ.cont v)).aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
  refine ((hd.2 v w v w).1.norm).congr (.of_forall fun g => ?_)
  simp only [norm_mul, norm_star, sq]

theorem memLp_diag {ρ : Γ → (B →L[ℂ] B)} (hρ : IsU ρ) (v : B)
    (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν) : MemLp (fun g => ⟪v, ρ g v⟫_ℂ) 2 ν := by
  have hc : Continuous fun g => ⟪v, ρ g v⟫_ℂ := continuous_const.inner (hρ.cont v)
  refine (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 ?_
  refine (hm.norm.mul_const (‖v‖ * ‖v‖)).mono' (hc.norm.pow 2).aestronglyMeasurable (.of_forall fun g => ?_)
  have h1 : ‖⟪v, ρ g v⟫_ℂ‖ ≤ ‖v‖ * ‖v‖ := (norm_inner_le_norm _ _).trans (by rw [hρ.norm])
  rw [Real.norm_of_nonneg (by positivity), norm_star, sq]
  exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

theorem inner_toLp {f g : Γ → ℂ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ⟪hf.toLp f, hg.toLp g⟫_ℂ = ∫ x, star (f x) * g x ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [RCLike.inner_apply, mul_comm]

theorem orthonormal_coef {σ : Γ → (A →L[ℂ] A)} (hσ : IsU σ) {d : ℝ} (hd : IsFd ν σ d) {ι : Type*} {e : ι → A}
    (he : Orthonormal ℂ e) :
    Orthonormal ℂ fun p : ι × ι => ((√d : ℝ) : ℂ) • (memLp_coef hσ hd (e p.1) (e p.2)).toLp _ := by
  classical
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.1.ne'
  have hs : conj ((√d : ℝ) : ℂ) * ((√d : ℝ) : ℂ) = d := by
    rw [Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt hd.1.le]
  rw [orthonormal_iff_ite]
  rintro ⟨k, l⟩ ⟨k', l'⟩
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, hs, inner_toLp]
  have h := (hd.2 (e l') (e k') (e l) (e k)).2
  have h2 : ∫ x, star ⟪e k, σ x (e l)⟫_ℂ * ⟪e k', σ x (e l')⟫_ℂ ∂ν =
      ⟪e l, e l'⟫_ℂ * ⟪e k', e k⟫_ℂ / (d : ℂ) := by
    rw [← h]
    exact integral_congr_ae (.of_forall fun x => mul_comm _ _)
  simp only []
  rw [h2, orthonormal_iff_ite.1 he l l', orthonormal_iff_ite.1 he k' k]
  by_cases h1 : k = k' <;> by_cases h3 : l = l' <;> simp [h1, h3, hd0, eq_comm]

end SlopeTestRemainingChoices

theorem isHilbertSchmidt_coefOp : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ) (hσ : IsU σ), IsU ρ → IsFd ν σ d →
    ∀ (v : B) (hm : Integrable (fun g => star ⟪v, ρ g v⟫_ℂ) ν),
    GroundTheory.Automorphic.IsHilbertSchmidt (coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm) := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hd v hm
  set T := coefOp ν σ hσ (fun g => star ⟪v, ρ g v⟫_ℂ) hm with hT
  let e := GroundTheory.Automorphic.stdHilbertBasis ℂ A
  have hX := memLp_diag hρ v hm
  have hon := orthonormal_coef hσ hd e.orthonormal
  have hsum := Orthonormal.inner_products_summable (hX.toLp _) hon
  have hsd : √d ^ 2 = d := Real.sq_sqrt hd.1.le
  have key : ∀ p : _ × _, ‖⟪e p.1, T (e p.2)⟫_ℂ‖ ^ 2 =
      d⁻¹ * ‖⟪((√d : ℝ) : ℂ) • (memLp_coef hσ hd (e p.1) (e p.2)).toLp _, hX.toLp _⟫_ℂ‖ ^ 2 := by
    intro p
    have h1 : ⟪e p.1, T (e p.2)⟫_ℂ = ⟪hX.toLp _, (memLp_coef hσ hd (e p.1) (e p.2)).toLp _⟫_ℂ := by
      rw [hT, inner_coefOp, inner_toLp]
    rw [h1, inner_smul_left, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      mul_pow, hsd, norm_inner_symm, ← mul_assoc, inv_mul_cancel₀ hd.1.ne', one_mul]
  have hs2 : Summable fun p : _ × _ => ‖⟪e p.1, T (e p.2)⟫_ℂ‖ ^ 2 := by
    simp_rw [key]
    exact hsum.mul_left _
  rw [GroundTheory.Automorphic.isHilbertSchmidt_iff e]
  have h3 : ∑' l, ‖T (e l)‖ₑ ^ 2 = ∑' p : _ × _, ENNReal.ofReal (‖⟪e p.1, T (e p.2)⟫_ℂ‖ ^ 2) := by
    simp_rw [GroundTheory.Automorphic.enorm_sq_eq_tsum e (T _)]
    rw [ENNReal.tsum_comm, ← ENNReal.tsum_prod]
    refine tsum_congr fun p => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [h3]
  exact hs2.tsum_ofReal_lt_top

end GlobalTheory.CompanionTheory.RgHeA.CoefHS

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.WeilM Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory GlobalTheory.CompanionTheory.ThetaCoord
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ContDiff

namespace GlobalTheory.CompanionTheory.ThetaCoord.Cont

variable {F : Type} [Field F] [NumberField F] {κ : Type}

def ratA (ξ : κ → F) : κ → AF F := fun i => algebraMap F (AF F) (ξ i)

theorem continuous_finOf : Continuous (finOf : (κ → AF F) → κ → FiniteAdeleRing (𝓞 F) F) :=
  continuous_pi fun i => continuous_snd.comp (continuous_apply i)

private theorem continuous_infiniteAdeleRing_ringEquiv_mixedSpace :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  first
  | exact (InfiniteAdeleRing.homeomorph_mixedSpace F).continuous
  | (rw [show (InfiniteAdeleRing.ringEquiv_mixedSpace F : InfiniteAdeleRing F → mixedEmbedding.mixedSpace F) =
        fun x => (fun v : {w : InfinitePlace F // w.IsReal} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v.1),
          fun v : {w : InfinitePlace F // w.IsComplex} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v.1)) from rfl]
     exact Continuous.prodMk
      (continuous_pi fun v => (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp (continuous_apply _))
      (continuous_pi fun v => (InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp (continuous_apply _)))

theorem continuous_infOf : Continuous (infOf : (κ → AF F) → κ → mixedEmbedding.mixedSpace F) := by
  exact continuous_pi fun i => continuous_infiniteAdeleRing_ringEquiv_mixedSpace.comp (continuous_fst.comp (continuous_apply i))

theorem indicator_mem_SB_of_isClopen {X : Type} [TopologicalSpace X] {V : Set X} (hV : IsClopen V) (hc : IsCompact V) :
    V.indicator (fun _ => (1 : ℂ)) ∈ SB X := by
  refine ⟨fun s => ?_, ?_⟩
  · have h := Set.indicator_const_preimage V s (1 : ℂ)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h <;> rw [h]
    · exact isOpen_univ
    · exact hV.isOpen
    · exact hV.isClosed.isOpen_compl
    · exact isOpen_empty
  · exact HasCompactSupport.intro' hc hV.isClosed fun x hx => by simp [hx]

private theorem totallyDisconnectedSpace_finiteAdeleRing :
    TotallyDisconnectedSpace (FiniteAdeleRing (𝓞 F) F) := by
  let f : FiniteAdeleRing (𝓞 F) F → ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F := fun x v => x v
  have hf : Continuous f := by
    first
    | exact RestrictedProduct.continuous_coe
    | fun_prop
  have hi : Function.Injective f := by
    first
    | exact RestrictedProduct.coe_injective
    | exact fun x y h => Subtype.ext h
  refine ⟨fun s _ hs => ?_⟩
  have h1 : (f '' s).Subsingleton := (hs.image f hf.continuousOn).subsingleton
  exact fun x hx y hy => hi (h1 (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy))


open GroundTheory.Global in
theorem exists_clopen_superset [Fintype κ] {S : Set (κ → FiniteAdeleRing (𝓞 F) F)} (hS : IsCompact S) :
    ∃ V, IsClopen V ∧ IsCompact V ∧ S ⊆ V := by
  classical
  haveI := totallyDisconnectedSpace_finiteAdeleRing (F := F)
  have hB : TopologicalSpace.IsTopologicalBasis {s : Set (κ → FiniteAdeleRing (𝓞 F) F) | IsClopen s} :=
    loc_compact_Haus_tot_disc_of_zero_dim
  have hx : ∀ x ∈ S, ∃ C : Set (κ → FiniteAdeleRing (𝓞 F) F), IsClopen C ∧ IsCompact C ∧ x ∈ C := by
    intro x _
    obtain ⟨K, hK, hKx⟩ := exists_compact_mem_nhds x
    obtain ⟨C, hCc, hxC, hCK⟩ := hB.mem_nhds_iff.1 hKx
    exact ⟨C, hCc, hK.of_isClosed_subset hCc.isClosed hCK, hxC⟩
  choose! C hCc hCk hxC using hx
  obtain ⟨t, htS, ht, hcov⟩ := hS.elim_finite_subcover_image (fun x hx => (hCc x hx).isOpen)
    (fun x hx => Set.mem_biUnion hx (hxC x hx))
  refine ⟨⋃ x ∈ t, C x, ⟨ht.isClosed_biUnion fun x hx => (hCc x (htS hx)).isClosed,
    isOpen_biUnion fun x hx => (hCc x (htS hx)).isOpen⟩, ht.isCompact_biUnion fun x hx => hCk x (htS hx), hcov⟩

theorem infOf_ratA_add [Fintype κ] (ξ : κ → F) (a : κ → AF F) :
    infOf (ratA ξ + a) = (fun i => mixedEmbedding F (ξ i) : κ → mixedEmbedding.mixedSpace F) + infOf a := by
  funext i
  show InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (InfiniteAdeleRing F) (ξ i) + (a i).1) =
    mixedEmbedding F (ξ i) + InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1
  rw [map_add (f := _), InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F]

theorem finOf_ratA_add (ξ : κ → F) (a : κ → AF F) :
    finOf (ratA ξ + a) = (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + finOf a := rfl


open scoped Classical in
theorem pure_bound [Fintype κ] (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F))
    {K : Set (κ → AF F)} (hK : IsCompact K) :
    ∃ u : (κ → F) → ℝ, Summable u ∧ ∀ ξ, ∀ a ∈ K, ‖pureA F f g (ratA ξ + a)‖ ≤ u ξ := by
  obtain ⟨hgl, hgc⟩ := hg
  obtain ⟨M, hM⟩ := hgl.continuous.bounded_above_of_compact_support hgc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨R0, hR0⟩ := (hK.image continuous_infOf).isBounded.exists_norm_le
  have hD : IsCompact ((fun q : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F) => q.1 - q.2) ''
      (tsupport g ×ˢ (finOf '' K))) :=
    (hgc.isCompact.prod (hK.image continuous_finOf)).image continuous_sub
  obtain ⟨V, hVc, hVk, hDV⟩ := exists_clopen_superset hD
  obtain ⟨k, hk⟩ := GlobalTheory.CompanionTheory.ThetaAdm.summable_weight F (indicator_mem_SB_of_isClopen hVc hVk)
  have hC : ∀ z, (1 + ‖z‖) ^ k * ‖f z‖ ≤
      2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := fun z => by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl f z
    simpa [norm_iteratedFDeriv_zero] using this
  obtain ⟨C, hCdef⟩ : ∃ C, C = 2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f := ⟨_, rfl⟩
  rw [← hCdef] at hC
  have hC0 : 0 ≤ C := (mul_nonneg (by positivity) (norm_nonneg _)).trans (hC 0)
  obtain ⟨R, hR, hRdef⟩ : ∃ R : ℝ, 0 ≤ R ∧ R = max R0 0 := ⟨_, le_max_right _ _, rfl⟩
  refine ⟨fun ξ => (M * (C * (1 + R) ^ k)) *
    (‖V.indicator (fun _ => (1 : ℂ)) (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))‖ *
      ((1 + ‖(fun i => mixedEmbedding F (ξ i) : κ → mixedEmbedding.mixedSpace F)‖) ^ k)⁻¹), hk.mul_left _, ?_⟩
  intro ξ a ha
  beta_reduce
  have hpure : pureA F f g (ratA ξ + a) =
      f ((fun i => mixedEmbedding F (ξ i) : κ → mixedEmbedding.mixedSpace F) + infOf a) *
        g ((fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) + finOf a) := by
    show f (infOf (ratA ξ + a)) * g (finOf (ratA ξ + a)) = _
    rw [infOf_ratA_add, finOf_ratA_add]
  rw [hpure, norm_mul]
  generalize hp : (fun i => mixedEmbedding F (ξ i) : κ → mixedEmbedding.mixedSpace F) = p
  generalize hy : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) = y
  have hRa : ‖infOf a‖ ≤ R := hRdef ▸ (hR0 _ ⟨a, ha, rfl⟩).trans (le_max_left _ _)
  have hf1 : ‖f (p + infOf a)‖ ≤ C * (1 + R) ^ k * ((1 + ‖p‖) ^ k)⁻¹ := by
    have h0 : ‖p‖ ≤ ‖p + infOf a‖ + ‖infOf a‖ := by
      simpa using norm_sub_le (p + infOf a) (infOf a)
    have h1 : 1 + ‖p‖ ≤ (1 + ‖p + infOf a‖) * (1 + R) := by
      nlinarith [norm_nonneg (p + infOf a), norm_nonneg (infOf a)]
    have hpos : 0 < 1 + ‖p‖ := by positivity
    have h2 : (1 + ‖p‖) ^ k ≤ (1 + ‖p + infOf a‖) ^ k * (1 + R) ^ k := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hpos.le h1 k
    have h3 := hC (p + infOf a)
    rw [le_mul_inv_iff₀ (by positivity)]
    calc ‖f (p + infOf a)‖ * (1 + ‖p‖) ^ k
        ≤ ‖f (p + infOf a)‖ * ((1 + ‖p + infOf a‖) ^ k * (1 + R) ^ k) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = ((1 + ‖p + infOf a‖) ^ k * ‖f (p + infOf a)‖) * (1 + R) ^ k := by ring
      _ ≤ C * (1 + R) ^ k := mul_le_mul_of_nonneg_right h3 (by positivity)
  have hg1 : ‖g (y + finOf a)‖ ≤ M * ‖V.indicator (fun _ => (1 : ℂ)) y‖ := by
    by_cases hyV : y ∈ V
    · rw [Set.indicator_of_mem hyV, norm_one, mul_one]
      exact hM _
    · have hz : g (y + finOf a) = 0 := by
        by_contra hne
        apply hyV
        apply hDV
        exact ⟨(y + finOf a, finOf a), ⟨subset_tsupport g hne, ⟨a, ha, rfl⟩⟩, by simp⟩
      rw [hz, norm_zero]
      exact mul_nonneg hM0 (norm_nonneg _)
  calc ‖f (p + infOf a)‖ * ‖g (y + finOf a)‖
      ≤ (C * (1 + R) ^ k * ((1 + ‖p‖) ^ k)⁻¹) * (M * ‖V.indicator (fun _ => (1 : ℂ)) y‖) :=
        mul_le_mul hf1 hg1 (norm_nonneg _) (by positivity)
    _ = M * (C * (1 + R) ^ k) * (‖V.indicator (fun _ => (1 : ℂ)) y‖ * ((1 + ‖p‖) ^ k)⁻¹) := by ring


open scoped Classical in
theorem schA_bound [Fintype κ] {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    Continuous Φ ∧ ∀ K : Set (κ → AF F), IsCompact K →
      ∃ u : (κ → F) → ℝ, Summable u ∧ ∀ ξ, ∀ a ∈ K, ‖Φ (ratA ξ + a)‖ ≤ u ξ := by
  refine Submodule.span_induction (p := fun Φ _ => Continuous Φ ∧ ∀ K : Set (κ → AF F), IsCompact K →
      ∃ u : (κ → F) → ℝ, Summable u ∧ ∀ ξ, ∀ a ∈ K, ‖Φ (ratA ξ + a)‖ ≤ u ξ) ?_ ?_ ?_ ?_ hΦ
  · rintro x ⟨f, g, hg, rfl⟩
    refine ⟨?_, fun K hK => pure_bound f hg hK⟩
    show Continuous fun x => f (infOf x) * g (finOf x)
    exact (f.continuous.comp continuous_infOf).mul (hg.1.continuous.comp continuous_finOf)
  · refine ⟨continuous_const, fun K _ => ⟨0, summable_zero, fun ξ a _ => by simp⟩⟩
  · rintro x y _ _ ⟨hxc, hxb⟩ ⟨hyc, hyb⟩
    refine ⟨hxc.add hyc, fun K hK => ?_⟩
    obtain ⟨u, hu, hub⟩ := hxb K hK
    obtain ⟨v, hv, hvb⟩ := hyb K hK
    exact ⟨u + v, hu.add hv, fun ξ a ha => (norm_add_le _ _).trans (add_le_add (hub ξ a ha) (hvb ξ a ha))⟩
  · rintro c x _ ⟨hxc, hxb⟩
    refine ⟨hxc.const_smul c, fun K hK => ?_⟩
    obtain ⟨u, hu, hub⟩ := hxb K hK
    refine ⟨fun ξ => ‖c‖ * u ξ, hu.mul_left _, fun ξ a ha => ?_⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hub ξ a ha) (norm_nonneg _)

end GlobalTheory.CompanionTheory.ThetaCoord.Cont

end
end

section

open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct

theorem _root_.GlobalTheory.T.unitary_borel_splitting : PositivityTheory.SphericalProduct.BorelSplitU := by
  first | exact @GlobalTheory.CompanionTheory.BorelSplit.borelSplitU | exact GlobalTheory.CompanionTheory.BorelSplit.borelSplitU | (intros; apply GlobalTheory.CompanionTheory.BorelSplit.borelSplitU <;> assumption)
end
