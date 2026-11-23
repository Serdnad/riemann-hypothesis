module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle692
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.GenSpace
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle088
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle120
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle153
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle133
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle187
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle538
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle313
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle539
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle449
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle036
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle107
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle119
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle474
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondLeviFamily
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle464
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle540
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
import Mathlib.Topology.Sheaves.Init
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.IsSliceMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle286
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.L2DecayOfCountEscape
public import Mathlib.Algebra.Order.Chebyshev
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.ProdGPn
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr

@[expose] public section

section

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.exists_invariant_projection : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ L : Subgroup (GL (Fin N) (Af E)), IsCompact (L : Set (GL (Fin N) (Af E))) → ∀ x ∈ V, ∃ x' ∈ V, (∀ u ∈ L, finRep E N u x' = x') ∧ ∀ y : Sm E N, y ∈ squareIntegrableSmoothSubmoduleGL μ → (∀ u ∈ L, finRep E N u y = y) → ⟪l2Map μ x, l2Map μ y⟫_ℂ = ⟪l2Map μ x', l2Map μ y⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscAvg.exists_avg | exact GlobalTheory.CompanionTheory.FinDiscAvg.exists_avg | (intros; apply GlobalTheory.CompanionTheory.FinDiscAvg.exists_avg <;> assumption)
end

section

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.integral_eq_l2_inner : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ → ∀ x y : Sm E N, x ∈ squareIntegrableSmoothSubmoduleGL μ → y ∈ squareIntegrableSmoothSubmoduleGL μ → ∫ g in F, x.1 g * (starRingEnd ℂ) (y.1 g) ∂μ = ⟪l2Map μ y, l2Map μ x⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscOrth.setIntegral_mul_conj_eq_inner | exact GlobalTheory.CompanionTheory.FinDiscOrth.setIntegral_mul_conj_eq_inner | (intros; apply GlobalTheory.CompanionTheory.FinDiscOrth.setIntegral_mul_conj_eq_inner <;> assumption)
end

section

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.lie_skew_adjoint_l2' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : Lie E N) (x y : Sm E N), Continuous x.1 → Continuous y.1 → Continuous (lie E N X x).1 → Continuous (lie E N X y).1 → x ∈ squareIntegrableSmoothSubmoduleGL μ → y ∈ squareIntegrableSmoothSubmoduleGL μ → lie E N X x ∈ squareIntegrableSmoothSubmoduleGL μ → lie E N X y ∈ squareIntegrableSmoothSubmoduleGL μ → ⟪l2Map μ x, l2Map μ (lie E N X y)⟫_ℂ = -⟪l2Map μ (lie E N X x), l2Map μ y⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscOrth.lie_skew_l2Map | exact GlobalTheory.CompanionTheory.FinDiscOrth.lie_skew_l2Map | (intros; apply GlobalTheory.CompanionTheory.FinDiscOrth.lie_skew_l2Map <;> assumption)
end

section

open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

theorem _root_.GlobalTheory.T.right_translate_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (g : GA E N) (x y : Sm E N), x ∈ squareIntegrableSmoothSubmoduleGL μ → y ∈ squareIntegrableSmoothSubmoduleGL μ → rt E N g x ∈ squareIntegrableSmoothSubmoduleGL μ ∧ ⟪l2Map μ (rt E N g x), l2Map μ (rt E N g y)⟫_ℂ = ⟪l2Map μ x, l2Map μ y⟫_ℂ := by
  first | exact @GlobalTheory.CompanionTheory.FinDiscOrth.rt_mem_l2Sub_and_inner_eq | exact GlobalTheory.CompanionTheory.FinDiscOrth.rt_mem_l2Sub_and_inner_eq | (intros; apply GlobalTheory.CompanionTheory.FinDiscOrth.rt_mem_l2Sub_and_inner_eq <;> assumption)
end

section

open scoped ENNReal NNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

namespace GlobalTheory.CompanionTheory.Conc.BesselPt

theorem sq_tsum_le {ι : Type*} (t : ι → ℝ≥0) (k : ℕ) (h : (Function.support t).encard ≤ k) :
    (∑' i, (t i : ℝ≥0∞)) ^ 2 ≤ k * ∑' i, (t i : ℝ≥0∞) ^ 2 := by
  have hfin : (Function.support t).Finite := Set.finite_of_encard_le_coe h
  set S := hfin.toFinset with hS
  have hcard : S.card ≤ k := by
    have : (S.card : ℕ∞) ≤ k := by
      rw [← Set.encard_coe_eq_coe_finsetCard, hS, hfin.coe_toFinset]; exact h
    exact_mod_cast this
  have hz : ∀ i, i ∉ S → t i = 0 := fun i hi => by simpa [hS] using hi
  have e1 : ∑' i, (t i : ℝ≥0∞) = ∑ i ∈ S, (t i : ℝ≥0∞) :=
    tsum_eq_sum (fun i hi => by simp [hz i hi])
  have e2 : ∑' i, (t i : ℝ≥0∞) ^ 2 = ∑ i ∈ S, (t i : ℝ≥0∞) ^ 2 :=
    tsum_eq_sum (fun i hi => by simp [hz i hi])
  rw [e1, e2]
  have h3 : (∑ i ∈ S, t i) ^ 2 ≤ k * ∑ i ∈ S, t i ^ 2 := by
    have h4 : ((∑ i ∈ S, (t i : ℝ)) ^ 2) ≤ S.card * ∑ i ∈ S, (t i : ℝ) ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h5 : (∑ i ∈ S, t i) ^ 2 ≤ S.card * ∑ i ∈ S, t i ^ 2 := by exact_mod_cast h4
    exact h5.trans (by gcongr)
  exact_mod_cast h3

theorem sq_lintegral_mul_le {X : Type*} [MeasurableSpace X] (ν : Measure X) {f g : X → ℝ≥0∞}
    (hf : AEMeasurable f ν) (hg : AEMeasurable g ν) :
    (∫⁻ a, f a * g a ∂ν) ^ 2 ≤ (∫⁻ a, f a ^ 2 ∂ν) * ∫⁻ a, g a ^ 2 ∂ν := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two hf hg
  simp only [Pi.mul_apply, ENNReal.rpow_ofNat] at h
  refine (pow_le_pow_left' h 2).trans (le_of_eq ?_)
  rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ _), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul]
  norm_num

theorem encard_support_le {G : Type*} [Group G] [TopologicalSpace G] (Γ : Subgroup G) (α : G → ℂ) (x w : G)
    (k : ℕ)
    (hk : {γ : G | γ ∈ Γ ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k) :
    (Function.support fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊).encard ≤ k := by
  rcases (Function.support fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊).eq_empty_or_nonempty with h0 | ⟨γ₀, h₀⟩
  · simp [h0]
  refine le_trans ?_ hk
  have hinj : Set.InjOn (fun γ : Γ => (γ : G) * (γ₀ : G)⁻¹)
      (Function.support fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊) := by
    intro a _ b _ hab
    exact Subtype.ext (mul_right_cancel hab)
  rw [← hinj.encard_image]
  refine Set.encard_le_encard ?_
  rintro _ ⟨γ, hγ, rfl⟩
  have mem : ∀ c : Γ, c ∈ (Function.support fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊) →
      x⁻¹ * ((c : G) * w) ∈ tsupport α := fun c hc => by
    apply subset_tsupport
    simpa [Function.mem_support] using hc
  refine ⟨Γ.mul_mem γ.2 (Γ.inv_mem γ₀.2), _, mem γ hγ, _, mem γ₀ h₀, ?_⟩
  group

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

theorem sq_lintegral_le (μ : Measure G) [μ.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ] {F : Set G}
    (hF : IsFundamentalDomain Γ F μ) {α ψ : G → ℂ} (hα : Continuous α) (hψ : Continuous ψ)
    (hinv : ∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) (hn : (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1) (x : G) (k : ℕ)
    (hk : {γ : G | γ ∈ Γ ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k) :
    (∫⁻ y, ‖α y‖ₑ * ‖ψ (x * y)‖ₑ ∂μ) ^ 2 ≤ k * ∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ := by
  set a : G → ℝ≥0∞ := fun w => ‖α (x⁻¹ * w)‖ₑ with ha
  have ham : Measurable a := (hα.comp (continuous_const.mul continuous_id)).enorm.measurable
  have hψm : Measurable fun w => ‖ψ w‖ₑ := hψ.enorm.measurable
  have htr : ∀ γ : Γ, Measurable fun w => a ((γ : G) * w) :=
    fun γ => ham.comp (measurable_const_mul _)
  have e1 : ∫⁻ y, ‖α y‖ₑ * ‖ψ (x * y)‖ₑ ∂μ = ∫⁻ w in F, (∑' γ : Γ, a ((γ : G) * w)) * ‖ψ w‖ₑ ∂μ := by
    have h1 := lintegral_mul_left_eq_self (μ := μ) (fun w => a w * ‖ψ w‖ₑ) x
    simp only [ha, inv_mul_cancel_left] at h1
    rw [h1, hF.lintegral_eq_tsum'', ← lintegral_tsum]
    · refine lintegral_congr fun w => ?_
      rw [← ENNReal.tsum_mul_right]
      refine tsum_congr fun γ => ?_
      rw [Subgroup.smul_def, smul_eq_mul, hinv _ γ.2]
    · intro γ
      simp only [Subgroup.smul_def, smul_eq_mul, hinv _ γ.2]
      exact ((htr γ).mul hψm).aemeasurable
  have e2 : ∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ = ∫⁻ w in F, ∑' γ : Γ, a ((γ : G) * w) ^ 2 ∂μ := by
    have h1 := lintegral_mul_left_eq_self (μ := μ) (fun w => a w ^ 2) x
    simp only [ha, inv_mul_cancel_left] at h1
    rw [h1, hF.lintegral_eq_tsum'', ← lintegral_tsum]
    · rfl
    · intro γ
      exact ((htr γ).pow_const 2).aemeasurable
  have hK : Measurable fun w => ∑' γ : Γ, a ((γ : G) * w) := Measurable.tsum htr
  rw [e1, e2, ← lintegral_const_mul' _ _ (ENNReal.natCast_ne_top k)]
  refine (sq_lintegral_mul_le _ hK.aemeasurable hψm.aemeasurable).trans ?_
  rw [hn, mul_one]
  refine lintegral_mono fun w => ?_
  have := sq_tsum_le (fun γ : Γ => ‖α (x⁻¹ * ((γ : G) * w))‖₊) k (encard_support_le Γ α x w k hk)
  simpa [ha, enorm_eq_nnnorm] using this

theorem pointwise (μ : Measure G) [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (Γ : Subgroup G) [Countable Γ]
    {α : G → ℂ} {δ : ℝ} {F : Set G} (hα : Continuous α) (hc : HasCompactSupport α) (hδ : 0 < δ)
    (hF : IsFundamentalDomain Γ F μ) : ∃ C₀ : ℝ, ∀ ψ : G → ℂ, Continuous ψ → (∀ γ ∈ Γ, ∀ g, ψ (γ * g) = ψ g) →
      (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) → (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 →
      ∀ (x : G) (k : ℕ), {γ : G | γ ∈ Γ ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k →
        ‖ψ x‖ ^ 2 ≤ C₀ * k := by
  refine ⟨(δ ^ 2)⁻¹ * (∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ).toReal, ?_⟩
  rintro ψ hψ hinv ⟨s, hs, hrep⟩ hn x k hk
  have hA : (∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ) ≠ ⊤ := by
    have hc2 : HasCompactSupport ((fun z : ℂ => ‖z‖ ^ 2) ∘ α) :=
      HasCompactSupport.comp_left (g := fun z : ℂ => ‖z‖ ^ 2) hc (by simp)
    have hi : Integrable ((fun z : ℂ => ‖z‖ ^ 2) ∘ α) μ :=
      Continuous.integrable_of_hasCompactSupport ((continuous_norm.pow 2).comp hα) hc2
    have := hi.2.ne
    simpa [HasFiniteIntegral, enorm_pow] using this
  have h1 : ‖s‖ₑ * ‖ψ x‖ₑ ≤ ∫⁻ y, ‖α y‖ₑ * ‖ψ (x * y)‖ₑ ∂μ := by
    rw [← enorm_mul, ← hrep x]
    exact (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (by simp only [enorm_mul]))
  have h3 : (‖s‖ₑ * ‖ψ x‖ₑ) ^ 2 ≤ k * ∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ :=
    (pow_le_pow_left' h1 2).trans (sq_lintegral_le μ _ hF hα hψ hinv hn x k hk)
  have h4 : (‖s‖ * ‖ψ x‖) ^ 2 ≤ k * (∫⁻ y, ‖α y‖ₑ ^ 2 ∂μ).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) hA) h3
    simpa [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm] using this
  have hδ2 : 0 < δ ^ 2 := by positivity
  have h5 : δ ^ 2 * ‖ψ x‖ ^ 2 ≤ (‖s‖ * ‖ψ x‖) ^ 2 := by
    rw [mul_pow]
    gcongr
  have h6 := h5.trans h4
  rw [mul_assoc, inv_mul_eq_div, le_div_iff₀ hδ2]
  nlinarith [h6]

end GlobalTheory.CompanionTheory.Conc.BesselPt


open GlobalTheory.CompanionTheory.Conc.BesselPt in
theorem GlobalTheory.CompanionTheory.Conc.besselPt : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] (α : GA E N → ℂ) (δ : ℝ) (F : Set (GA E N)), Continuous α → HasCompactSupport α → 0 < δ →
  IsFundamentalDomain (latticeGL E N) F μ → ∃ C₀ : ℝ, ∀ ψ : GA E N → ℂ, Continuous ψ → (∀ γ ∈ latticeGL E N, ∀ g, ψ (γ * g) = ψ g) →
  (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ (x * y) ∂μ = s * ψ x) → (∫⁻ x in F, ‖ψ x‖ₑ ^ 2 ∂μ) = 1 →
  ∀ (x : GA E N) (k : ℕ), {γ : GA E N | γ ∈ latticeGL E N ∧ ∃ a ∈ tsupport α, ∃ b ∈ tsupport α, γ = x * a * b⁻¹ * x⁻¹}.encard ≤ k →
    ‖ψ x‖ ^ 2 ≤ C₀ * k := by
  intro E _ _ _ N _ _ μ _ α δ F hα hc hδ hF
  haveI : Countable (latticeGL E N) := GlobalTheory.DiscreteUnit.countable_latticeGL
  exact pointwise μ (latticeGL E N) hα hc hδ hF
end

section

open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDisc

theorem exists_isFundamentalDomain_of_isSqInt :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
      (μ : Measure (GA E N)) [μ.IsHaarMeasure] (φ : GA E N → ℂ), IsSqInt φ →
      ∃ F : Set (GA E N), IsFundamentalDomain (latticeGL E N) F μ := by
  intro E _ _ _ N _ _ μ _ φ _
  obtain ⟨F, -, hF⟩ := GlobalTheory.CompanionTheory.LatticeFD.exists_measurable_isFundamentalDomain E N
  exact ⟨F, hF μ⟩

end GlobalTheory.CompanionTheory.FinDisc

end
end

section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

theorem _root_.GlobalTheory.T.split_centre_translate_preserves_cusp_space : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))), J ⊆ Zalg E a → ∀ φ : Sm E a, φ ∈ genSpace L ρ J → IsCuspidal φ.1 → ∀ t : ℝ, rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ ∈ genSpace L ρ J ∧ IsCuspidal (rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ).1 := by
  first | exact @GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem | exact GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem | (intros; apply GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SmGL.Bernstein

theorem prod₂_detRep_isIrreducible :
    (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      JacquetOfInducedFiltration k) →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ →
      IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) →
      (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible := by
  intro hJ k _ _ _ _ a b χ₁ χ₂ s₁ s₂ u₁ u₂ hne
  haveI := GlobalTheory.CompanionTheory.DegPrinSeries.nontrivial_subrepresentation k a b χ₁ χ₂ s₁ s₂
  show IsSimpleOrder (Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b)))
    ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)))
  refine ⟨fun W => ?_⟩
  obtain ⟨W', hc⟩ := GlobalTheory.T.admissible_unitary_semisimple _ (GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset k (a + b))
    (GlobalTheory.CompanionTheory.DegenSeries.isAdmissible_degenerate k a b χ₁ χ₂ s₁ s₂)
    (GlobalTheory.CompanionTheory.DegenerateSeries.isUnitarisable_degenerateSeries k a b χ₁ χ₂ s₁ s₂ u₁ u₂) W
  by_contra h
  push_neg at h
  have hW' : W' ≠ ⊥ := by
    rintro rfl
    exact h.2 (eq_top_of_isCompl_bot hc)
  exact GlobalTheory.T.induced_two_characters_not_scalar k a b χ₁ χ₂ W W' hc h.1 hW'
    (GlobalTheory.T.jacquet_induced_two_characters k a b χ₁ χ₂ (hJ k) s₁ s₂ u₁ u₂ hne)

end GlobalTheory.CompanionTheory.SmGL.Bernstein
end

section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

theorem _root_.GlobalTheory.T.smooth_parabolic_induction_product : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {r t N : ℕ} (h : r + t = N) (π₁ : Representation ℂ (GL (Fin r) k) V) (π₂ : Representation ℂ (GL (Fin t) k) W), IsSmooth π₁ → IsSmooth π₂ → IsSmooth (sQ h π₁ π₂) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.isSmooth_sQ | exact GlobalTheory.CompanionTheory.BZRes.isSmooth_sQ | (intros; apply GlobalTheory.CompanionTheory.BZRes.isSmooth_sQ <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory


theorem _root_.GlobalTheory.T.closure_dim_iff_arithmetic_variety : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (d : ℕ), CharZero ((MP ℤ m n).residueField x) → (topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (d : ℕ) ↔ Geo.IsArithVar (ptIdeal x) d) := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.DimClosure.dim_closure_iff_isArithVar | exact GlobalTheory.CompanionTheory.MPDict.DimClosure.dim_closure_iff_isArithVar | (intros; apply GlobalTheory.CompanionTheory.MPDict.DimClosure.dim_closure_iff_isArithVar <;> assumption)
end
end

section

namespace GlobalTheory.CompanionTheory.CapClsA

open GlobalTheory.CompanionTheory.PairMult

theorem capOne_newton : CapOne := by
  intro n V _ _ E χ hE hg Y
  refine LinearMap.ext fun v => ?_
  have h := GlobalTheory.CapelliNewton.capelli_of_gelfand V n E χ hE
    (fun k x => by rw [etr_eq_gelA]; exact hg (k + 1) x) Y v
  simpa [Formalism.QuantumDeterminants.capP] using h

theorem dualCap_newton : DualCap := by
  intro n V _ _ E χ hE hg Y
  obtain ⟨hF, hq⟩ := GlobalTheory.CapelliNegT.glRel_negT_and_qdet (Module.End ℂ V) n E hE
  have h := capOne_newton n V (PositivityTheory.RgBcC.RealD.barF E) (fun a => -χ a) hF hg (-Y)
  have hq' := hq (-Y + ((n : ℂ) - 1) / 2)
  have harg : (n : ℂ) - 1 - (-Y + ((n : ℂ) - 1) / 2) = Y + ((n : ℂ) - 1) / 2 := by ring
  rw [harg] at hq'
  have hne : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
    rw [← mul_pow]; simp
  have h2 : ((-1 : ℂ) ^ n) • Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) =
      ((-1 : ℂ) ^ n * Formalism.QuantumDeterminants.capP χ Y) • (1 : Module.End ℂ V) := by
    rw [← hq', ← capelliPoly_neg]
    exact h
  calc Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2)
      = ((-1 : ℂ) ^ n) • (((-1 : ℂ) ^ n) • Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2)) := by
        rw [smul_smul, hne, one_smul]
    _ = Formalism.QuantumDeterminants.capP χ Y • (1 : Module.End ℂ V) := by
        rw [h2, smul_smul, ← mul_assoc, hne, one_mul]

theorem capCls_of_actUU : PositivityTheory.RgBcC.RealD.ActUU → PositivityTheory.RgBcC.RealD.CapCls := fun hAct =>
  GlobalTheory.CompanionTheory.CapClsProof.capCls_of hAct capOne_newton dualCap_newton

end GlobalTheory.CompanionTheory.CapClsA
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

theorem _root_.GlobalTheory.T.irregular_projection_image_null : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D),
    volume (GlobalTheory.CompanionTheory.MixZ.ArchEq.projCoord i Ψ '' {y | y ∈ c.e.source ∧
      (∃ z, GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z ∧ Ψ (segre z) 0 ≠ 0) ∧ ¬ GlobalTheory.CompanionTheory.MixZ.ArchEq.IsRegAt i Ψ c y}) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.volume_image_crit | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.volume_image_crit | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.volume_image_crit <;> assumption)
end
