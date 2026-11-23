module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle063
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle096
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle097
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle052
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle058
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle094
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
public import Formalism.HermitianCurvature.FrameExists2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieListProducts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle004
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle062
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormSqUnitNormalizationLe
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle034
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle037
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDerivedActionFiniteDimUnitaryRep
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle010
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle020
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
import Formalism.HermitianCurvature.Bundle001

@[expose] public section

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselFirstLeft

theorem sigmaFinite_of_haar {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (h : B.IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun {K} hK => h.finite_compact K hK⟩
  infer_instance

theorem left_integral {k r : ℕ} (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (hk : 1 ≤ k) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) (hl : IsBeL R z π μW μN l)
    {Y x : R.H} (hY : Y ∈ R.sm) (hx : x ∈ R.TK) :
    Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2) *
        ⟪x, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹) Y⟫_ℂ) • π (Matrix.of p.1)) (μW.prod μN) ∧
    ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2) *
        ⟪x, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹) Y⟫_ℂ) • π (Matrix.of p.1) ∂(μW.prod μN) =
      (innerSL ℂ (l x)).smulRight (l Y) := by
  obtain ⟨-, -, -, -, hinv, hae⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r z μW μN hk hz hT
    (((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r μW).2.2 z hz hT hk).2 hW) ((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r μN).2.1.2 hN)
  obtain ⟨-, -, hψ, -, hU, -⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r z Formalism.QuantumDeterminants.cStd hz
  obtain ⟨hint, hbe⟩ := hl.2 Y hY x hx
  set φ := (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => ((Matrix.of p.2)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) with hφ
  have heq : (fun p => beInt z Formalism.QuantumDeterminants.cStd π R.σ Y x (φ p)) =ᵐ[μW.prod μN]
      (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2) *
        ⟪x, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹) Y⟫_ℂ) • π (Matrix.of p.1)) := by
    filter_upwards [hae] with p hp
    have h1 : ((Matrix.of p.1 : Mx k r)⁻¹)⁻¹ = Matrix.of p.1 :=
      Matrix.nonsing_inv_nonsing_inv _ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit (hU _ hp.1 _ hp.1).2.2)
    have h2 := (hψ _ hp.2).2
    change (⟪x, R.σ ((Matrix.of p.1 : Mx k r)⁻¹ * (Matrix.of p.2 : Mx k r)⁻¹) Y⟫_ℂ *
      star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2 : Mx k r)⁻¹)) • π ((Matrix.of p.1 : Mx k r)⁻¹)⁻¹ = _
    rw [h1, h2, star_star, mul_comm]
  refine ⟨((hinv.integrable_comp hint.aestronglyMeasurable).2 hint).congr heq, ?_⟩
  rw [← integral_congr_ae heq, ← hbe, be]
  have := integral_map hinv.aemeasurable (f := beInt z Formalism.QuantumDeterminants.cStd π R.σ Y x)
    (by rw [hinv.map_eq]; exact hint.aestronglyMeasurable)
  rw [hinv.map_eq] at this
  exact this.symm

theorem bessel_integrate_left : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (l : R.H → Wp) (l' : R.H → Wq), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → ∀ γ ∈ JF.Om k r D.z D.z', ∃ A : R.H → Wq → Wq → Wp, (∀ y a c (t : ℂ), A y (t • a) c = star t • A y a c) ∧ ∀ x ∈ R.TK, ∀ y ∈ R.TK, ∀ (X : Wq →L[ℂ] Wp) (c : Wq), B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ c = A y (ContinuousLinearMap.adjoint X (l x)) c := by
  intro hyp k r ε mu h R Wp _ _ _ _ Wq _ _ _ _ D l l' hDS hgap hok hl hl' γ hγ
  refine ⟨fun y a c => ∫ q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
    (star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd (Matrix.of q.2)) * ⟪a, D.π' (Matrix.of q.1)⁻¹ c⟫_ℂ) •
      l (R.σ (γ * Matrix.of q.2 * Matrix.of q.1) y) ∂(D.μW'.prod D.μN), ?_, ?_⟩
  · intro y a c t
    rw [← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [inner_smul_left, smul_smul]
    congr 1
    rw [starRingEnd_apply]; ring
  intro x hx y hy X c
  haveI := sigmaFinite_of_haar D.haarW
  haveI := sigmaFinite_of_haar D.haarW'
  haveI := sigmaFinite_of_haar D.haarN
  obtain ⟨hmul, -, -, hsm, hTK, -⟩ := GlobalTheory.rep_basic_of_isDS hyp.1.2.2.1 k r ε mu R hDS
  have hcoef : IsCoef R l l' (fun g => ⟪x, R.σ g y⟫_ℂ • X) ⟪l x, X (l' y)⟫_ℂ :=
    ⟨1, fun _ => x, fun _ => y, fun _ => X, fun _ => ⟨hx, hy⟩, fun g _ => by simp, by simp⟩
  have hcc := (GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap hyp k r ε mu h R Wp Wq l l' _ _ hDS hgap hok hcoef).2 0
  have hint := (Formalism.FourierDecayAlt.P.bessel_integral_converges k r Wp Wq D _ _ (GlobalTheory.T.decayThresholds_of_spectralGapCondition k r h hok).1 hcc).1 γ hγ
  have hJ : B.JF D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ =
      ∫ p, JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ p ∂D.μSS := rfl
  rw [hJ, ContinuousLinearMap.integral_apply hint]
  have hint' : Integrable (fun p => JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ p c)
      ((D.μW.prod D.μN).prod (D.μW'.prod D.μN)) :=
    (ContinuousLinearMap.apply ℂ Wp c).integrable_comp hint
  rw [B.RealPlaceData.μSS, integral_prod_symm _ hint']
  have hae := (GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z D.μW D.μN D.k_pos D.z_mem D.T_pos
    (((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μW).2.2 _ D.z_mem D.T_pos D.k_pos).2 D.haarW)
    ((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μN).2.1.2 D.haarN)).2.2.2.2.2
  have hae' := (GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z' D.μW' D.μN D.k_pos D.z'_mem D.T'_pos
    (((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μW').2.2 _ D.z'_mem D.T'_pos D.k_pos).2 D.haarW')
    ((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r D.μN).2.1.2 D.haarN)).2.2.2.2.2
  obtain ⟨-, -, -, -, hU, hNG⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z Formalism.QuantumDeterminants.cStd D.z_mem
  obtain ⟨-, -, -, -, hU', -⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z' Formalism.QuantumDeterminants.cStd D.z'_mem
  refine integral_congr_ae ?_
  filter_upwards [hae'] with q hq
  have hg : γ * Matrix.of q.2 * Matrix.of q.1 ∈ GG k r :=
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul hγ.1 (hNG _ hq.2)) (hU' _ hq.1 _ hq.1).2.2
  obtain ⟨hI, hE⟩ := left_integral R D.z D.π D.μW D.μN l D.k_pos D.z_mem D.T_pos D.haarW D.haarN hl
    (hsm _ hg y (hTK y hy)) hx
  have hE' := congrArg (fun T : Wp →L[ℂ] Wp =>
    star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd (Matrix.of q.2)) • T (X (D.π' (Matrix.of q.1)⁻¹ c))) hE
  simp only [ContinuousLinearMap.integral_apply hI] at hE'
  rw [← integral_smul] at hE'
  rw [ContinuousLinearMap.adjoint_inner_left, ← smul_smul]
  refine Eq.trans (integral_congr_ae ?_) hE'
  filter_upwards [hae] with p hp
  have hs : (Matrix.of p.1 : Mx k r)⁻¹ * (Matrix.of p.2 : Mx k r)⁻¹ ∈ GG k r :=
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv (hU _ hp.1 _ hp.1).2.2) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv (hNG _ hp.2))
  rw [← hmul _ hs _ hg]
  simp only [JF.integrand, JF.xiP, B.rho, B.sgs, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    map_smul, smul_smul, Matrix.mul_assoc]
  congr 1
  ring

end GlobalTheory.BesselFirstLeft
end
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

noncomputable section

namespace GlobalTheory.TensorDualDifferential

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def hermLin {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] ℂ where
  toFun M := herm H (M *ᵥ v) w
  map_add' M N := by simp [herm, Matrix.add_mulVec, Matrix.mulVec_add]
  map_smul' c M := by simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul]

theorem herm_exp_hasDeriv {n : ℕ} (H X : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    HasDerivAt (fun t : ℝ => herm H (NormedSpace.exp ((t : ℂ) • X) *ᵥ v) w) (herm H (X *ᵥ v) w) 0 := by
  have h : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) X 0 :=
    hasDerivAt_iff_tendsto_slope.2 (Formalism.REAL.tendsto_slope_exp_smul X)
  exact (((LinearMap.toContinuousLinearMap (hermLin H v w)).restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt
    (0 : ℝ) h

theorem herm_skew {n : ℕ} {H X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * H + H * X = 0) (v w : Fin n → ℂ) :
    herm H v (X *ᵥ w) = -herm H (X *ᵥ v) w := by
  have h : Xᴴ * H = -(H * X) := eq_neg_of_add_eq_zero_left hX
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h,
    Matrix.neg_mulVec, dotProduct_neg]

theorem dOp_tensor {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (V →L[ℂ] V)} {B : Fin k → (Fin (2 * r + k + 1) → ℂ)}
    {πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V)))}
    (hπ : IsRepW k r z π) (hπt : IsRepW k r z πt) (hB : IsFrameOf k r [z] B)
    (h : ∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, star (herm (Hpk k r) (h *ᵥ B d) (B c)) • π h (y d))
    {X : Mx k r} (hX : InLieW k r z X) (y : PiLp 2 (fun _ : Fin k => V)) (c : Fin k) :
    dOp πt X y c = dOp π X (y c) - ∑ d, hermLin (Hpk k r) (B c) (B d) X • y d := by
  have h1 := dOp_hasDeriv hπt.1 hπt.2 hX
  have h2 := dOp_hasDeriv hπ.1 hπ.2 hX
  have h3 : HasDerivAt (fun t : ℝ => πt (NormedSpace.exp ((t : ℂ) • X)) y c) (dOp πt X y c) 0 :=
    (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin k => V) c).comp
      (ContinuousLinearMap.apply ℂ _ y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h4 : ∀ d, HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) (y d)) (dOp π X (y d)) 0 :=
    fun d => ((ContinuousLinearMap.apply ℂ V (y d)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h5 := HasDerivAt.fun_sum (u := Finset.univ) fun d _ =>
    (herm_exp_hasDeriv (Hpk k r) X (B d) (B c)).star.fun_smul (h4 d)
  have h6 : (fun t : ℝ => πt (NormedSpace.exp ((t : ℂ) • X)) y c) = fun t : ℝ =>
      ∑ d, star (herm (Hpk k r) (NormedSpace.exp ((t : ℂ) • X) *ᵥ B d) (B c)) •
        π (NormedSpace.exp ((t : ℂ) • X)) (y d) := funext fun t => h _ (exp_uw hX t) y c
  rw [h6] at h3
  rw [h3.unique h5, Finset.sum_add_distrib]
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec, hπ.1.1, hB.2.1,
    Qx2.herm_star, herm_skew hX.1.1]
  simp [hermLin, sub_eq_add_neg]

theorem EB_tensor : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V)))), inWb k r z → 0 < Tz k r z → IsRepW k r z π → IsRepW k r z πt → IsFrameOf k r [z] B → (∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, star (herm (Hpk k r) (h *ᵥ B d) (B c)) • π h (y d)) → ∀ a b y c, EB πt B a b y c = EB π B a b (y c) - if c = b then y a else 0 := by
  intro V _ _ _ k r z π B πt _ _ hπ hπt hB h a b y c
  have hl := frame_lie hB a b
  have e1 := dOp_tensor hπ hπt hB h hl.1 y c
  have e2 := dOp_tensor hπ hπt hB h hl.2 y c
  have e3 : ∑ d, hermLin (Hpk k r) (B c) (B d) (hpart1 (Hpk k r) (unitB (Hpk k r) B a b)) • y d +
      Complex.I • ∑ d, hermLin (Hpk k r) (B c) (B d) (hpart2 (Hpk k r) (unitB (Hpk k r) B a b)) • y d =
      if c = b then y a else 0 := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    have e4 : ∀ d, hermLin (Hpk k r) (B c) (B d) (hpart1 (Hpk k r) (unitB (Hpk k r) B a b)) • y d +
        Complex.I • hermLin (Hpk k r) (B c) (B d) (hpart2 (Hpk k r) (unitB (Hpk k r) B a b)) • y d =
        if a = d then (if c = b then y d else 0) else 0 := by
      intro d
      rw [smul_smul, ← add_smul, ← smul_eq_mul Complex.I, ← map_smul, ← map_add (f := _), LieListProducts.hsum]
      have e5 : hermLin (Hpk k r) (B c) (B d) (unitB (Hpk k r) B a b) =
          herm (Hpk k r) (B c) (B b) * herm (Hpk k r) (B a) (B d) := by
        show herm (Hpk k r) (unitB (Hpk k r) B a b *ᵥ B c) (B d) = _
        rw [Qx8.unitB_mulVec]
        simp [herm, Matrix.mulVec_smul]
      rw [e5, hB.2.1, hB.2.1]
      split_ifs <;> simp
    simp [e4]
  have e6 : EB πt B a b y c = dOp πt (hpart1 (Hpk k r) (unitB (Hpk k r) B a b)) y c +
      Complex.I • dOp πt (hpart2 (Hpk k r) (unitB (Hpk k r) B a b)) y c := rfl
  have e7 : EB π B a b (y c) = dOp π (hpart1 (Hpk k r) (unitB (Hpk k r) B a b)) (y c) +
      Complex.I • dOp π (hpart2 (Hpk k r) (unitB (Hpk k r) B a b)) (y c) := rfl
  rw [e6, e7, e1, e2, ← e3, smul_sub]
  abel

end GlobalTheory.TensorDualDifferential
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem familyDerivativeExpansion_smul (P : M.Par) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b C₃ : ℝ) (a₁ : ℕ) (t : ℂ)
    (h : Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p f b C₃ a₁) :
    Formalism.FourierDecayAlt.P.CutBP.FamilyDerivativeExpansion p (fun g => t • f g) b C₃ a₁ := by
  obtain ⟨Par, inst, fam, lam, n₁, ninf, c0, q0, Gam, hf, hGam, h1, h2, h3, h4, hstep, hrange, hGb,
    hnorm, hmeas⟩ := h
  refine ⟨Par, inst, fun μ g => t • fam μ g, lam, n₁, ninf, c0, q0, Gam, ?_, hGam, h1, h2, h3, h4, ?_,
    hrange, hGb, ?_, ?_⟩
  · subst hf; rfl
  · intro μ hμ
    obtain ⟨a, hE, hS, hsupp⟩ := hstep μ hμ
    refine ⟨a, ?_, hS, hsupp⟩
    funext c
    have hc := congrFun hE c
    simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply] at hc ⊢
    rw [Formalism.FourierDecayAlt.P.CutBP.V_csmul p (fam μ) t, smul_comm, hc, Finset.smul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Formalism.FourierDecayAlt.P.CutBP.V_csmul p (fam (μ + ν)) t, smul_comm]
  · intro μ
    rw [Formalism.FourierDecayAlt.P.CutBP.norm_sq_const_smul p (fam μ) t, Formalism.FourierDecayAlt.P.CutBP.norm_sq_const_smul p f t]
    gcongr
    exact hnorm μ
  · intro μ
    have e : (fun c : Fin (P.r + 1) → ℂ =>
        ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fun g => t • fam μ g) (P.r + 1) [] (TBB.bigPt P.r c))) =
        fun c => ENNReal.ofReal (‖t‖ ^ 2) *
          ENNReal.ofReal (TBB.Ew p (fun _ => 1) (fam μ) (P.r + 1) [] (TBB.bigPt P.r c)) := by
      funext c
      rw [Formalism.FourierDecayAlt.P.CutBP.Ew_csmul p (fam μ) t, ENNReal.ofReal_mul (sq_nonneg _)]
    rw [e]
    exact (hmeas μ).const_mul _

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons

namespace GlobalTheory.HalfGen

theorem factors_of_ncard_places (E : Type) [Field E] [NumberField E] (g : ℕ) (hg : g.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((g : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E) :
    (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).card = Module.finrank ℚ E ∧
      (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(g : 𝓞 E)})).Nodup := by
  classical
  set I : Ideal (𝓞 E) := Ideal.span {(g : 𝓞 E)} with hI
  set s := UniqueFactorizationMonoid.normalizedFactors I with hs
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hg.ne_zero
  have hprod : s.prod = I := Ideal.prod_normalizedFactors_eq_self hI0
  have hprime : ∀ P ∈ s, Prime P := fun P hP =>
    UniqueFactorizationMonoid.prime_of_normalized_factor P hP
  have hN : Ideal.absNorm I = g ^ Module.finrank ℚ E := by
    rw [hI, Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  have hle : ∀ a ∈ s.map Ideal.absNorm, g ≤ a := by
    intro a ha
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp ha
    have hdvd : Ideal.absNorm P ∣ g ^ Module.finrank ℚ E := by
      rw [← hN, ← hprod]
      exact map_dvd _ (Multiset.dvd_prod hP)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hg).mp hdvd
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, Ideal.absNorm_eq_one_iff] at hk
      exact (hprime P hP).ne_one (by rw [hk, Ideal.one_eq_top])
    rw [hk]
    exact Nat.le_self_pow hk0 g
  have h1 : s.card ≤ Module.finrank ℚ E := by
    have := Multiset.pow_card_le_prod hle
    rw [← map_multiset_prod, hprod, hN, Multiset.card_map] at this
    exact (Nat.pow_le_pow_iff_right hg.one_lt).1 this
  have h2 : Module.finrank ℚ E ≤ s.toFinset.card := by
    rw [← h, ← Set.ncard_coe_finset]
    refine Set.ncard_le_ncard_of_injOn (fun v => v.asIdeal) (fun v hv => ?_)
      (fun v _ w _ e => HeightOneSpectrum.ext e) (Finset.finite_toSet _)
    rw [Finset.mem_coe, Multiset.mem_toFinset, hs, Ideal.mem_normalizedFactors_iff hI0]
    exact ⟨v.isPrime, (Ideal.span_singleton_le_iff_mem _).2 hv⟩
  have h3 := Multiset.toFinset_card_le s
  exact ⟨by omega, Multiset.toFinset_card_eq_card_iff_nodup.1 (by omega)⟩

theorem barE_piG {D : D7} (EX : ErrX D) (i : Fin 2) : barE D (EX.piG i) = piBarO EX i := by
  apply IsFractionRing.injective (𝓞 D.host.E) D.host.E
  exact barE_eq_conj D _

theorem half_principal_and_split : ∀ (D : D7) (T : Core D), LawsM T → ∀ EX : ErrX D,
 letI := T.Q.H.starRing
 (∃ α : 𝓞 D.host.E, α * star α = ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∧ T.Q.l.Mb = Ideal.span {star α}) ∧ (∀ i, star (EX.piG i) = piBarO EX i ∧ piBarO EX i * star (piBarO EX i) = ((D.host.g i : ℕ) : 𝓞 D.host.E)) ∧ ((∀ i, T.Q.l.Mb ≤ Ideal.span {piBarO EX i}) → T.Q.l.Mb = Ideal.span {piBarO EX 0 * piBarO EX 1}) ∧ ∀ (L : SizeData₂ D), ParameterChoice' D L → ∀ i, (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)})).card = Module.finrank ℚ D.host.E ∧ (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {((D.host.g i : ℕ) : 𝓞 D.host.E)})).Nodup := by
  intro D T h EX
  have hb : ∀ i, T.Q.H.bar (EX.piG i) = piBarO EX i := fun i => by rw [bar_core, barE_piG]
  have hbb : ∀ a, T.Q.H.bar (T.Q.H.bar a) = a := fun a => by rw [bar_core, bar_core, barE_barE]
  have hn : ∀ i, piBarO EX i * T.Q.H.bar (piBarO EX i) = ((D.host.g i : ℕ) : 𝓞 D.host.E) := fun i => by
    rw [← hb, hbb, mul_comm, hb]
    exact RPfVal.piG_mul_bar EX i
  have hM : T.Q.l.Mb = Ideal.span {piOf T EX 0 * piOf T EX 1} := by
    rw [← Ideal.span_singleton_mul_span_singleton, span_piOf T h, span_piOf T h, Mb_eq T h]
  have hp : ∀ i, piOf T EX i * T.Q.H.bar (piOf T EX i) = ((D.host.g i : ℕ) : 𝓞 D.host.E) := fun i => by
    rw [bar_core]; exact piOf_mul_barE T EX i
  have hpp : (piOf T EX 0 * piOf T EX 1) * T.Q.H.bar (piOf T EX 0 * piOf T EX 1) =
      ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
    rw [map_mul, ← hp 0, ← hp 1]; ring
  refine ⟨⟨T.Q.H.bar (piOf T EX 0 * piOf T EX 1), ?_, ?_⟩, fun i => ⟨hb i, hn i⟩, fun ho => ?_, fun _ _ i => ?_⟩
  · show T.Q.H.bar _ * T.Q.H.bar (T.Q.H.bar _) = _
    rw [hbb, mul_comm, hpp, level_M T h, Nat.cast_mul]
  · show _ = Ideal.span {T.Q.H.bar (T.Q.H.bar _)}
    rw [hbb, hM]
  · have hcg : IsCoprime ((D.host.g 0 : ℕ) : 𝓞 D.host.E) ((D.host.g 1 : ℕ) : 𝓞 D.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime 0) (D.host.g_prime 1)).2 D.host.g_ne)
    rw [← hn 0, ← hn 1] at hcg
    have hc : IsCoprime (piBarO EX 0) (piBarO EX 1) := hcg.of_mul_left_left.of_mul_right_left
    have hd : ∀ i, piBarO EX i ∣ piOf T EX 0 * piOf T EX 1 := fun i =>
      Ideal.mem_span_singleton.1 (ho i (hM ▸ Ideal.mem_span_singleton_self _))
    obtain ⟨c, hcc⟩ := hc.mul_dvd (hd 0) (hd 1)
    have hg : ((D.host.g 0 : ℕ) : 𝓞 D.host.E) * ((D.host.g 1 : ℕ) : 𝓞 D.host.E) ≠ 0 :=
      mul_ne_zero (Nat.cast_ne_zero.2 (D.host.g_prime 0).ne_zero) (Nat.cast_ne_zero.2 (D.host.g_prime 1).ne_zero)
    have hu : c * T.Q.H.bar c = 1 := by
      apply mul_left_cancel₀ hg
      rw [_root_.mul_one]
      conv_rhs => rw [← hpp, hcc, map_mul, map_mul]
      rw [← hn 0, ← hn 1]
      ring
    rw [hM, hcc]
    exact Ideal.span_singleton_mul_right_unit (IsUnit.of_mul_eq_one _ hu) _
  · exact factors_of_ncard_places D.host.E (D.host.g i) (D.host.g_prime i) (D.nd.g_split i)

end GlobalTheory.HalfGen
end

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Proof.ModelAtPrimeToLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

variable (Xo : Moduli Dw l) (c : Coeff l)

end General

section Instance

variable {D : D7} {T : Top D}

theorem one_le_rank (h : LawsP T) {j : ℕ} (hj : InR D j) : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  obtain ⟨h1, h2⟩ := hj
  rw [hp, hq]
  have h3 := D.R.m_add_three_le_k
  simp only [Ranks.sigW]
  omega

end Instance

section Full

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

end Full

end GlobalTheory.Proof.ModelAtPrimeToLevel
end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.exists_derivedAction_finiteDimUnitaryRep : ∀ (k : ℕ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (π : Matrix (Fin k) (Fin k) ℂ → (W →L[ℂ] W)), PI.UpqRep.IsURepOn (PI.UpqRep.UJset (PI.UpqRep.allPos k)) π → ∃ E : Fin k → Fin k → Module.End ℂ W, Formalism.REAL.GlRel E ∧ Formalism.REAL.IsUnitary (PI.UpqRep.allPos k) E ∧ ∀ Z : Matrix (Fin k) (Fin k) ℂ, Zᴴ = -Z → ∀ v, HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • Z)) v) (∑ a, ∑ b, Z a b • E a b v) 0 := by
  first | exact @GlobalTheory.UnitaryDerived.exists_derived_action | exact GlobalTheory.UnitaryDerived.exists_derived_action | (intros; apply GlobalTheory.UnitaryDerived.exists_derived_action <;> assumption)
end
