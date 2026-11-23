module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle148
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle187
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle147
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle287
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle257
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle269
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle131
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle289
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOrbitalIntegralEqInvDegSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle290
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualUnipotentGroupActsUnitriangularOnto
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle291
public import Formalism.HermitianLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsShortVectorUnimodularHermitianLatticeRankT
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.SmoothRepsType

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalPlaceBasis

theorem exists_level_bump (B : RowsAut) (hg : 1 ≤ B.g) :
    ∃ χ : B.I.Gf → ℂ, Continuous χ ∧ HasCompactSupport χ ∧ (∀ k, χ k ≠ 0 → k ∈ B.I.Kg B.g) ∧
      ∫ k, χ k ∂B.μf = 1 := by
  obtain ⟨hT, -, -, hKc, -, -, hK⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨ho, ⟨K, hKe⟩, -⟩ := hK B.g hg
  have hcl : IsClosed (B.I.Kg B.g) := by
    rw [← hKe] at ho ⊢
    exact K.isClosed_of_isOpen ho
  have hc : IsCompact (B.I.Kg B.g) := hKc.of_isClosed_subset hcl fun x hx => hx.1
  have hne : (B.I.Kg B.g).Nonempty := by
    rw [← hKe]; exact ⟨1, K.one_mem⟩
  have hpos : 0 < B.μf.real (B.I.Kg B.g) :=
    ENNReal.toReal_pos (ho.measure_pos B.μf hne).ne' hc.measure_lt_top.ne
  refine ⟨(B.I.Kg B.g).indicator fun _ => (((B.μf.real (B.I.Kg B.g))⁻¹ : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · exact IsClopen.continuous_indicator ⟨hcl, ho⟩ continuous_const
  · exact HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _
  · intro k hk
    exact Set.mem_of_indicator_ne_zero hk
  · rw [integral_indicator_const _ ho.measurableSet, Complex.real_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hpos.ne', Complex.ofReal_one]

theorem integrable_of_prod (B : RowsAut) (hσ : IsURep B.σs) (a : B.I.Ginf → ℂ) (χ : B.I.Gf → ℂ)
    (h1 : ∫ k, χ k ∂B.μf = 1) (hc : Continuous fun y : B.I.GA => a y.1 * χ y.2)
    (hs : HasCompactSupport fun y : B.I.GA => a y.1 * χ y.2) (w : B.Hs) :
    Integrable (fun g => a g • B.σs g w) (muInf B.I) := by
  obtain ⟨k, hk⟩ : ∃ k, χ k ≠ 0 := by
    by_contra h
    push Not at h
    simp [h] at h1
  have hac : Continuous a := by
    have h2 : Continuous fun g : B.I.Ginf => a g * χ k :=
      hc.comp (f := fun g : B.I.Ginf => ((g, k) : B.I.GA)) (Continuous.prodMk_left k)
    have h3 := h2.mul_const (χ k)⁻¹
    simpa [mul_assoc, mul_inv_cancel₀ hk] using h3
  have has : HasCompactSupport a := by
    refine HasCompactSupport.intro (hs.isCompact.image continuous_fst) fun g hg => ?_
    by_contra h0
    exact hg ⟨(g, k), subset_tsupport _ (mul_ne_zero h0 hk), rfl⟩
  have : IsFiniteMeasureOnCompacts (muInf B.I) := by unfold muInf; infer_instance
  exact (hac.smul (hσ.2.2.2 w)).integrable_of_hasCompactSupport has.smul_right

theorem conv_avg (B : RowsAut) (T : B.Hs →L[ℂ] B.I.L2 B.μf B.fund)
    (hT : T ∈ B.I.HomS B.σs B.μf B.fund B.R) (hk : ∀ u, ∀ k ∈ B.I.Kg B.g, B.R (1, k) (T u) = T u)
    (a : B.I.Ginf → ℂ) (χ : B.I.Gf → ℂ) (hχ : ∀ k, χ k ≠ 0 → k ∈ B.I.Kg B.g) (h1 : ∫ k, χ k ∂B.μf = 1)
    (w : B.Hs) (hint : Integrable (fun g => a g • B.σs g w) (muInf B.I)) :
    ∫ y, (a y.1 * χ y.2) • B.R y (T w) ∂(B.I.muA B.μf) = T (∫ g, a g • B.σs g w ∂(muInf B.I)) := by
  have : SigmaFinite (muInf B.I) := by unfold muInf; infer_instance
  obtain ⟨-, hmul, -⟩ := GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  have hpt : ∀ y : B.I.GA, (a y.1 * χ y.2) • B.R y (T w) = χ y.2 • T (a y.1 • B.σs y.1 w) := by
    rintro ⟨g, k⟩
    by_cases h0 : χ k = 0
    · simp [h0]
    · have e1 : B.R (g, k) (T w) = T (B.σs g w) := by
        have : ((g, k) : B.I.GA) = (g, 1) * (1, k) := by simp
        rw [this, hmul, ContinuousLinearMap.mul_apply, hk w k (hχ k h0)]
        exact (congrArg (fun S : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => S w) (hT g)).symm
      simp only [e1, map_smul, smul_smul, mul_comm]
  simp_rw [hpt]
  change ∫ y : B.I.Ginf × B.I.Gf, χ y.2 • T (a y.1 • B.σs y.1 w) ∂((muInf B.I).prod B.μf) = _
  rw [← integral_prod_swap]
  have := integral_prod_smul (μ := B.μf) (ν := muInf B.I) χ (fun g => T (a g • B.σs g w))
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [this, h1, one_smul, T.integral_comp_comm hint]

theorem repsExist : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d →
    (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v))
      (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.g →
    ∀ T ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ u, ∀ k ∈ B.I.Kg B.g, B.R (1, k) (T u) = T u) →
      ∃ Fr, IsReps B T Fr := by
  intro B d hd h1 hg T hT hk
  classical
  obtain ⟨χ, hχc, hχs, hχK, hχ1⟩ := exists_level_bump B hg
  obtain ⟨huniq, -, htr, -⟩ := GlobalTheory.ContRepUniq.contRep_unique_linear B
  have hσ : IsURep B.σs := (GlobalTheory.Dec.tensorRep B d hd).1
  let Fr : B.Hs → B.I.GA → ℂ := fun u => if h : ∃ f, IsContRep B (T u) f then h.choose else 0
  have hFr : ∀ u f, IsContRep B (T u) f → Fr u = f := by
    intro u f hf
    have h : ∃ f, IsContRep B (T u) f := ⟨f, hf⟩
    have : Fr u = h.choose := dif_pos h
    rw [this]
    exact huniq _ _ _ h.choose_spec hf
  refine ⟨Fr, fun P u hu => ?_⟩
  obtain ⟨A, hA, hAs, hfix⟩ := GlobalTheory.T.exists_smooth_average_lowest_KType B d hd h1 P u hu
  let ψ : B.I.GA → ℂ := fun y => A (fun v i j => uMat (y.1 v) i j) * χ y.2
  have hder := fun E => GlobalTheory.T.hasDerivAt_convolution_archimedeanUnitaryLieAlgebra B A χ ψ E hA hAs hχc hχs (fun _ => rfl)
  have hψ : ∫ y, ψ y • B.R y (T (B.tens B.w)) ∂(B.I.muA B.μf) = T u := by
    rw [hfix]
    exact conv_avg B T hT hk (fun g => A (fun v i j => uMat (g v) i j)) χ hχK hχ1 _
      (integrable_of_prod B hσ (fun g => A (fun v i j => uMat (g v) i j)) χ hχ1 (hder 0).1 (hder 0).2.1 _)
  have hrep := GlobalTheory.ConvContRep.conv_isContRep B ψ (T (B.tens B.w)) (hder 0).1 (hder 0).2.1
  rw [hψ] at hrep
  have hFu := hFr u _ hrep
  have hrep' : IsContRep B (T u) (Fr u) := by rw [hFu]; exact hrep
  refine ⟨hrep', fun k hkK y => ?_, fun E y => ?_⟩
  · have := htr _ _ (1, k) hrep'
    rw [hk u k hkK] at this
    exact congrFun (huniq _ _ _ this hrep') y
  · obtain ⟨-, -, ψ', hc', hs', hd'⟩ := hder E
    obtain ⟨hd1, hd2⟩ := hd' (T (B.tens B.w))
    rw [hψ] at hd1
    obtain ⟨A', -, -, hA'⟩ := GlobalTheory.AverageDeriv.hasDerivAt_orbit_average B A E (B.tens B.w) hσ hA hAs
    rw [← hfix] at hA'
    have hdiff : HasDerivAt (orbit B E u) (dAct B E u) 0 := hA'.differentiableAt.hasDerivAt
    have hd3 : HasDerivAt (fun t : ℝ => T (orbit B E u t)) (T (dAct B E u)) 0 :=
      (T.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hdiff
    have hfun : (fun t : ℝ => T (orbit B E u t)) =
        fun t : ℝ => B.R ((fun v => expU (t • E v)), 1) (T u) := by
      funext t
      exact congrArg (fun S : B.Hs →L[ℂ] B.I.L2 B.μf B.fund => S u) (hT _)
    rw [hfun] at hd3
    have heq := hd3.unique hd1
    have hrep2 := GlobalTheory.ConvContRep.conv_isContRep B ψ' (T (B.tens B.w)) hc' hs'
    rw [← heq] at hrep2
    rw [hFr _ _ hrep2, hFu]
    exact hd2 y

end GlobalTheory.SmoothRepsType
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

theorem _root_.GlobalTheory.T.exists_continuousRepresentative_bounded_evaluation : ∀ (B : RowsAut) (d : InfinitePlace B.I.F → ℝ), IsDSData B d → (∀ v, Formalism.MainNotions.S.IsKTypeOf (B.I.ε v) (B.σ v) (Formalism.QuantumDeterminants.lowK (B.I.ε v) (B.lam v)) (Formalism.MainNotions.S.lowKSub (B.I.ε v) (B.lam v) (B.σ v))) → 1 ≤ B.I.n → 1 ≤ B.g → ∃ C : ℝ, ∀ A ∈ B.I.HomS B.σs B.μf B.fund B.R, (∀ k ∈ B.I.Kg B.g, B.R (1, k) (A (B.tens B.w)) = A (B.tens B.w)) → ∃ f : B.I.GA → ℂ, IsContRep B (A (B.tens B.w)) f ∧ ∀ x, ‖f x‖ ≤ C * (tau1 B.I x)⁻¹ ^ (2 * B.I.n ^ 2 * B.I.f) * ‖A (B.tens B.w)‖ := by
  first | exact @GlobalTheory.EvalBound.exists_contRep_bound_of_isKTypeOf | exact GlobalTheory.EvalBound.exists_contRep_bound_of_isKTypeOf | (intros; apply GlobalTheory.EvalBound.exists_contRep_bound_of_isKTypeOf <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselOrbitalIntegral_eq_inv_deg_smul : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [CompleteSpace Wq] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) (z' : Fin (2 * r + k + 1) → ℂ) (c' : Fin r → ℂ) (π' : Mat k r → (Wq →L[ℂ] Wq)) (μS' : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → Side z' π' μS' → ∀ w₀ ∈ DD σ w, ∀ w₀' ∈ DD σ w, ∀ (ξ : Wp) (ξ' : Wq), ∀ γ ∈ Greg k r z z', Integrable (fun p : Mt k r × Mt k r => coef σ w₀' w₀ (Matrix.of (act2 γ p)) • rk1 (PiS (psiGen k r z c) π (Matrix.of p.1)⁻¹ ξ) (PiS (psiGen k r z' c') π' (Matrix.of p.2)⁻¹ ξ')) (μS.prod μS') ∧ Integrable (fun x : Mt k r => rk1 ((Afun (psiGen k r z c) π μS σ w w₀ ξ) (Matrix.of x)) ((Afun (psiGen k r z' c') π' μS' σ w w₀' ξ') (γ⁻¹ * Matrix.of x))) μG ∧ OO μG (Afun (psiGen k r z c) π μS σ w w₀ ξ) (Afun (psiGen k r z' c') π' μS' σ w w₀' ξ') γ = (d : ℂ)⁻¹ • Iint (psiGen k r z c) (psiGen k r z' c') π π' μS μS' σ w₀' w₀ ξ ξ' γ := by
  first | exact @GlobalTheory.SgInf.OO_eq_inv_deg_smul_Iint | exact GlobalTheory.SgInf.OO_eq_inv_deg_smul_Iint | (intros; apply GlobalTheory.SgInf.OO_eq_inv_deg_smul_Iint <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselFunctional_equivariant_unipotent_character : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, IsSPsiEquiv z (psiGen k r z c) π (Afun (psiGen k r z c) π μS σ u v ξ) := by
  first | exact @GlobalTheory.SgInf.Afun_isSPsiEquiv | exact GlobalTheory.SgInf.Afun_isSPsiEquiv | (intros; apply GlobalTheory.SgInf.Afun_isSPsiEquiv <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.integrable_matrixCoefficient_quotientMeasure : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ u ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, Integrable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) ν := by
  first | exact @GlobalTheory.SgInf.integrable_Afun_quotMeas | exact GlobalTheory.SgInf.integrable_Afun_quotMeas | (intros; apply GlobalTheory.SgInf.integrable_Afun_quotMeas <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselFolner_overlap_average_tendsto_form : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ Om : ℕ → Set (Mt k r), IsFolner (Sset k r z) μS Om → ∀ y ∈ DD σ w, ∀ ξ : Wp, Filter.Tendsto (fun j => (∫ p, ((μS {s | s ∈ Om j ∧ lmulM (Matrix.of p) s ∈ Om j}).toReal : ℂ) * (coef σ y y (Matrix.of p) * ⟪ξ, PiS (psiGen k r z c) π (Matrix.of p)⁻¹ ξ⟫_ℂ) ∂μS) / ((μS (Om j)).toReal : ℂ)) Filter.atTop (nhds ⟪ξ, be (psiGen k r z c) π μS σ y y ξ⟫_ℂ) := by
  first | exact @GlobalTheory.SgInf.FolnerLimit.folner_limit | exact GlobalTheory.SgInf.FolnerLimit.folner_limit | (intros; apply GlobalTheory.SgInf.FolnerLimit.folner_limit <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.bessel_inner_integral_eq_form : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ W : Mat k r → Wp, IsSPsiEquiv z (psiGen k r z c) π W → ∀ y ∈ GG k r, ∀ x : Mt k r, Matrix.of x ∈ GG k r → ∫ s, star (coef σ w w (y⁻¹ * (Matrix.of s * Matrix.of x))) • W (Matrix.of s * Matrix.of x) ∂μS = be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of x) w) (W (Matrix.of x)) := by
  first | exact @GlobalTheory.SgInf.inner_integral_eq_be | exact GlobalTheory.SgInf.inner_integral_eq_be | (intros; apply GlobalTheory.SgInf.inner_integral_eq_be <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.besselSubgroupIntegral_eq_inner_besselForm : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∫ t, ⟪v, σ (Matrix.of t)⁻¹ v⟫_ℂ * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μS = ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ := by
  first | exact @GlobalTheory.SgInf.SInt.sint_eq_inner_be | exact GlobalTheory.SgInf.SInt.sint_eq_inner_be | (intros; apply GlobalTheory.SgInf.SInt.sint_eq_inner_be <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.inner_besselFunctional_eq_integral_subgroup : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ x : Mt k r, Matrix.of x ∈ GG k r → ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ = ∫ s, coef σ u v (Matrix.of (lmulM (Matrix.of s) x)) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of (lmulM (Matrix.of s) x)), ξ⟫_ℂ ∂μS := by
  first | exact @GlobalTheory.SgInf.afun_inner_eq_integral | exact GlobalTheory.SgInf.afun_inner_eq_integral | (intros; apply GlobalTheory.SgInf.afun_inner_eq_integral <;> assumption)
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.matrixCoeff_mul_inner_besselFunctional_eq_integral : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ y : Mt k r, Matrix.of y ∈ GG k r → coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ = ∫ t, coef σ u v (Matrix.of y) * star (coef σ u₁ v (Matrix.of t * Matrix.of y)) * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μS := by
  first | exact @GlobalTheory.SgInf.coef_mul_inner_Afun_eq_integral | exact GlobalTheory.SgInf.coef_mul_inner_Afun_eq_integral | (intros; apply GlobalTheory.SgInf.coef_mul_inner_Afun_eq_integral <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ToC

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
  {H : HermSp M V} {r k : ℕ}

def swapEs (Fr : LocNG.FrameD H r) (es₂ : Fin r → V) (h1 : ∀ i j, H.h (es₂ i) (es₂ j) = 0)
    (h2 : ∀ i j : Fin r, H.h (Fr.f i.castSucc) (es₂ j) = if i = j then 1 else 0)
    (h3 : ∀ i, H.h (es₂ i) (Fr.f (Fin.last r)) = 0) : LocNG.FrameD H r :=
  ⟨Fr.f, es₂, Fr.T, Fr.h_iso, Fr.h_zz, h1, h2, h3⟩

lemma mem_img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) (x : V) :
    x ∈ LocNG.img g Λ ↔ ∃ y ∈ Λ, g y = x := by
  simp [LocNG.img, Submodule.mem_map]

lemma img_mul (g k : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) :
    LocNG.img (g * k) Λ = LocNG.img g (LocNG.img k Λ) := by
  ext x
  simp only [mem_img]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨k y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

lemma h_sum_left (H : HermSp M V) {ι : Type} (s : Finset ι) (c : ι → E) (v : ι → V) (y : V) :
    H.h (∑ i ∈ s, c i • v i) y = ∑ i ∈ s, c i * H.h (v i) y := by
  induction s using Finset.induction_on with
  | empty => simp [H.h_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]

lemma pair_eq (hM : M.OK) (Fr : LocNG.FrameD H r) (es₂ : Fin r → V) (h1 : ∀ i j, H.h (es₂ i) (es₂ j) = 0)
    (h2 : ∀ i j : Fin r, H.h (Fr.f i.castSucc) (es₂ j) = if i = j then 1 else 0)
    (h3 : ∀ i, H.h (es₂ i) (Fr.f (Fin.last r)) = 0) (hT : Fr.T ≠ 0) {n : V ≃ₗ[E] V} (hn : n ∈ Fr.N)
    (b : Fin (r + 1)) (a : Fin r) : H.h (n (Fr.f b)) (es₂ a) = H.h (n (Fr.f b)) (Fr.es a) := by
  obtain ⟨A, -, hA⟩ := (GlobalTheory.LocOver.UnipOnto.unipotent_onto M hM H r Fr hT).2.1 n hn
  have hb : ∀ c, H.h (Fr.f c) (es₂ a) = H.h (Fr.f c) (Fr.es a) := by
    intro c
    induction c using Fin.lastCases with
    | last =>
      have e1 : H.h (Fr.f (Fin.last r)) (es₂ a) = M.L.cj (H.h (es₂ a) (Fr.f (Fin.last r))) := H.h_herm _ _
      have e2 : H.h (Fr.f (Fin.last r)) (Fr.es a) = M.L.cj (H.h (Fr.es a) (Fr.f (Fin.last r))) := H.h_herm _ _
      rw [e1, e2, h3, Fr.h_sz]
    | cast i => rw [h2, Fr.h_es]
  rw [show n (Fr.f b) = _ from hA b, h_sum_left, h_sum_left]
  exact Finset.sum_congr rfl fun c _ => by rw [hb c]

lemma pulled (S : Frames M.L r k) (e : V ≃ₗ[E] S.V) (he : ∀ x y, S.h (e x) (e y) = H.h x y)
    (f : Fin (r + 1) → V) (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (hg : ∀ a, g a = e (f a))
    (hdual : ∀ a j, hf M.L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (hiso : ∀ i j, hf M.L S.Hm (gs i) (gs j) = 0) :
    (∀ i j, H.h (e.symm (gs i)) (e.symm (gs j)) = 0) ∧
    (∀ i j : Fin r, H.h (f i.castSucc) (e.symm (gs j)) = if i = j then 1 else 0) ∧
    (∀ i, H.h (e.symm (gs i)) (f (Fin.last r)) = 0) := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i => ?_⟩
  · rw [← he, e.apply_symm_apply, e.apply_symm_apply]; exact hiso i j
  · rw [← he, e.apply_symm_apply, ← hg]
    change hf M.L S.Hm _ _ = _
    rw [hdual]; simp [Fin.castSucc_inj]
  · rw [H.h_herm, ← he, e.apply_symm_apply, ← hg]
    change M.L.cj (hf M.L S.Hm _ _) = _
    rw [hdual]
    have : Fin.last r ≠ i.castSucc := (Fin.castSucc_lt_last i).ne'
    simp [this]

variable {P : LocNG.FPair H r} {S : Frames M.L r k}

def pair₂ (c : WCoord P S) : LocNG.FPair H r :=
  ⟨swapEs P.A (fun a => c.e.symm (S.es a))
      (pulled S c.e c.h_eq P.A.f S.f S.es c.f_eq S.dual S.iso).1
      (pulled S c.e c.h_eq P.A.f S.f S.es c.f_eq S.dual S.iso).2.1
      (pulled S c.e c.h_eq P.A.f S.f S.es c.f_eq S.dual S.iso).2.2,
    swapEs P.B (fun a => c.e.symm (S.es' a))
      (pulled S c.e c.h_eq P.B.f S.f' S.es' c.f'_eq S.dual' S.iso').1
      (pulled S c.e c.h_eq P.B.f S.f' S.es' c.f'_eq S.dual' S.iso').2.1
      (pulled S c.e c.h_eq P.B.f S.f' S.es' c.f'_eq S.dual' S.iso').2.2⟩

def coord₂ (c : WCoord P S) : Coord (pair₂ c) S :=
  ⟨c.e, c.h_eq, c.f_eq, c.f'_eq, fun a => (c.e.apply_symm_apply _).symm,
    fun a => (c.e.apply_symm_apply _).symm, c.T_eq, c.T'_eq, c.gg_none, c.gg_some⟩

def datEq (c : WCoord P S) : LocNG.Datum P ≃ LocNG.Datum (pair₂ c) where
  toFun d := ⟨d.L, d.L', d.hL, d.hL', d.io, d.io_L⟩
  invFun d := ⟨d.L, d.L', d.hL, d.hL', d.io, d.io_L⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem std_swap : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ) (Fr : LocNG.FrameD H r) (es₂ : Fin r → V) (h1 : ∀ i j, H.h (es₂ i) (es₂ j) = 0) (h2 : ∀ i j : Fin r, H.h (Fr.f i.castSucc) (es₂ j) = if i = j then 1 else 0) (h3 : ∀ i, H.h (es₂ i) (Fr.f (Fin.last r)) = 0), Fr.T ≠ 0 → ∀ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L → ∃ m ∈ Fr.N, (∀ b, m (Fr.f b) = Fr.f b) ∧ (⟨Fr.f, es₂, Fr.T, Fr.h_iso, Fr.h_zz, h1, h2, h3⟩ : LocNG.FrameD H r).LamStd L = LocNG.img m (Fr.LamStd L) :=
  GlobalTheory.T.standardLattice_dualVectors_change_unipotent

lemma inv_fix {m : V ≃ₗ[E] V} {x : V} (hx : m x = x) : m⁻¹ x = x := by
  conv_lhs => rw [← hx]
  show (m⁻¹ * m) x = x
  rw [inv_mul_cancel]; rfl

lemma side_iff (hM : M.OK) (Fr : LocNG.FrameD H r) (es₂ : Fin r → V) (h1 : ∀ i j, H.h (es₂ i) (es₂ j) = 0)
    (h2 : ∀ i j : Fin r, H.h (Fr.f i.castSucc) (es₂ j) = if i = j then 1 else 0)
    (h3 : ∀ i, H.h (es₂ i) (Fr.f (Fin.last r)) = 0) (hT : Fr.T ≠ 0)
    (L : Submodule M.L.O (H.Wb Fr.f)) (hL : Fr.IsInner L) (f : Fin (r + 1) → V) (Λ : Submodule M.L.O V) :
    (∃ n ∈ Fr.N, f = (fun b => n (Fr.f b)) ∧ Λ = LocNG.img n (Fr.LamStd L)) ↔
      ∃ n ∈ (swapEs Fr es₂ h1 h2 h3).N, f = (fun b => n ((swapEs Fr es₂ h1 h2 h3).f b)) ∧
        Λ = LocNG.img n ((swapEs Fr es₂ h1 h2 h3).LamStd L) := by
  obtain ⟨m, hm, hmf, hmΛ⟩ := std_swap M hM H r Fr es₂ h1 h2 h3 hT L hL
  have e : (swapEs Fr es₂ h1 h2 h3).LamStd L = LocNG.img m (Fr.LamStd L) := hmΛ
  rw [e]
  constructor
  · rintro ⟨n, hn, hf, hΛ⟩
    refine ⟨n * m⁻¹, Fr.N.mul_mem hn (Fr.N.inv_mem hm), ?_, ?_⟩
    · rw [hf]; funext b; show n (Fr.f b) = n (m⁻¹ (Fr.f b)); rw [inv_fix (hmf b)]
    · rw [← img_mul, mul_assoc, inv_mul_cancel, mul_one]; exact hΛ
  · rintro ⟨n, hn, hf, hΛ⟩
    refine ⟨n * m, Fr.N.mul_mem hn hm, ?_, ?_⟩
    · rw [hf]; funext b; show n (Fr.f b) = n (m (Fr.f b)); rw [hmf b]
    · rw [img_mul]; exact hΛ

end

theorem changed_duals : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), ∀ (S : Frames M.L r k) (c : WCoord P S), ∃ (P₂ : LocNG.FPair H r) (c₂ : Coord P₂ S) (φ : LocNG.Datum P ≃ LocNG.Datum P₂), c₂.e = c.e ∧ P₂.St = P.St ∧ P₂.K0 = P.K0 ∧ P₂.UW0 = P.UW0 ∧ P₂.Hp = P.Hp ∧ (P₂.PrimeTo ↔ P.PrimeTo) ∧ (∀ d, c₂.dat (φ d) = c.dat d) ∧ (∀ d t, LocNG.IsTermOver P d t ↔ LocNG.IsTermOver P₂ (φ d) t) ∧ (∀ d t, LocNG.IsTermOver P d t → LocNG.om P₂ t = LocNG.om P t) ∧ ∀ g d d', LocNG.Datum.Moves g d d' ↔ LocNG.Datum.Moves g (φ d) (φ d') := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P S c
  have hTA : P.A.T ≠ 0 := by rw [← c.T_eq]; exact S.T.ne_zero
  have hTB : P.B.T ≠ 0 := by rw [← c.T'_eq]; exact S.T'.ne_zero
  have pA := pulled S c.e c.h_eq P.A.f S.f S.es c.f_eq S.dual S.iso
  have pB := pulled S c.e c.h_eq P.B.f S.f' S.es' c.f'_eq S.dual' S.iso'
  have kA : ∀ n ∈ P.A.N, ∀ b a, H.h (n ((pair₂ c).A.f b)) ((pair₂ c).A.es a) = H.h (n (P.A.f b)) (P.A.es a) :=
    fun n hn b a => pair_eq hM P.A _ pA.1 pA.2.1 pA.2.2 hTA hn b a
  have kB : ∀ n ∈ P.B.N, ∀ b a, H.h (n ((pair₂ c).B.f b)) ((pair₂ c).B.es a) = H.h (n (P.B.f b)) (P.B.es a) :=
    fun n hn b a => pair_eq hM P.B _ pB.1 pB.2.1 pB.2.2 hTB hn b a
  refine ⟨pair₂ c, coord₂ c, datEq c, rfl, rfl, ?_, rfl, rfl, Iff.rfl, fun d => rfl, ?_, ?_, fun g d d' => Iff.rfl⟩
  · unfold LocNG.FPair.K0
    congr 1
    ext s
    constructor
    · rintro ⟨hs, h⟩
      have hs' := Subgroup.mem_inf.mp hs
      refine ⟨hs, fun a b => ?_⟩
      rw [← kA s hs'.1 b a, ← kB s hs'.2 b a]
      exact h a b
    · rintro ⟨hs, h⟩
      have hs' := Subgroup.mem_inf.mp hs
      refine ⟨hs, fun a b => ?_⟩
      rw [kA s hs'.1 b a, kB s hs'.2 b a]
      exact h a b
  · intro d t
    exact and_congr Iff.rfl (and_congr Iff.rfl
      (and_congr (side_iff hM P.A _ pA.1 pA.2.1 pA.2.2 hTA d.L d.hL t.f t.abelian₂)
        (and_congr (side_iff hM P.B _ pB.1 pB.2.1 pB.2.2 hTB d.L' d.hL' t.f' t.abelian₂) Iff.rfl)))
  · rintro d t ⟨-, -, ⟨n, hn, hf, -⟩, ⟨n', hn', hf', -⟩, -⟩
    have e1 : (pair₂ c).A.coefSum t.f = P.A.coefSum t.f := by
      unfold LocNG.FrameD.coefSum; rw [hf]
      exact Finset.sum_congr rfl fun a _ => kA n hn a.succ a
    have e2 : (pair₂ c).B.coefSum t.f' = P.B.coefSum t.f' := by
      unfold LocNG.FrameD.coefSum; rw [hf']
      exact Finset.sum_congr rfl fun a _ => kB n' hn' a.succ a
    unfold LocNG.om LocNG.FrameD.psiOf
    rw [e1, e2]

end GlobalTheory.HL.ToC
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.exists_short_vector_unimodular_hermitian_lattice_rank_two : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (J : Matrix (Fin 2) (Fin 2) E), Jᴴ = J → (∀ (φ : E →+* ℂ) (y : Fin 2 → E), y ≠ 0 → 0 < (φ (star y ⬝ᵥ (J *ᵥ y))).re) → ∀ Λ : Submodule (𝓞 E) (Fin 2 → E), Submodule.IsLattice E Λ → (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) → ∃ u ∈ Λ, u ≠ 0 ∧ ∀ φ : E →+* ℂ, (φ (star u ⬝ᵥ (J *ᵥ u))).re ≤ 2 * Formalism.HermitianLatticesTheory.vInv E := by
  first | exact @GlobalTheory.ShortVec.exists_short_vector | exact GlobalTheory.ShortVec.exists_short_vector | (intros; apply GlobalTheory.ShortVec.exists_short_vector <;> assumption)
end
