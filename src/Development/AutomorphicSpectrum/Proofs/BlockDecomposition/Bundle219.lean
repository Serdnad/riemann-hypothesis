module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Instances.Matrix
public import GroundTheory.AutomorphicForms.InductionParabolic
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle091
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle207
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Mathlib.Analysis.SpecialFunctions.Exponential
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import GroundTheory.AutomorphicForms.FiniteBruhat
public import GroundTheory.AutomorphicForms.GeometricLemmaJacquetCell
public import GroundTheory.AutomorphicForms.GeometricLemmaNormal
import Mathlib.GroupTheory.DoubleCoset
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.InstAddCommGroup
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
import Development.AbelianVarietyTheory.Definitions.Divisors.CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Pullback1MemHodgeFiltration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle026
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.PairAdj

section General

variable {Γ V : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [T2Space Γ]
  [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  (μ : Measure Γ) [μ.IsMulRightInvariant] [μ.IsInvInvariant] [IsFiniteMeasureOnCompacts μ] [SFinite μ]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]


omit [IsTopologicalGroup Γ] [T2Space Γ] [SecondCountableTopology Γ] [BorelSpace Γ] [Group Γ] [TopologicalSpace Γ] in
theorem inner_integral_left {μ : Measure Γ} {A : Γ → V} (hA : Integrable A μ) (c : V) :
    ⟪∫ y, A y ∂μ, c⟫_ℂ = ∫ y, ⟪A y, c⟫_ℂ ∂μ := by
  rw [← inner_conj_symm, ← integral_inner hA c, ← integral_conj]
  simp only [inner_conj_symm]

theorem pair_general (K : Γ → V →L[ℂ] V) (F H : Γ → V) (hK : Continuous K) (hF : Continuous F)
    (hH : Continuous H) (cK : HasCompactSupport K) (cF : HasCompactSupport F) (cH : HasCompactSupport H) :
    ∫ x, ⟪∫ y, ContinuousLinearMap.adjoint (K y⁻¹) (F (x * y)) ∂μ, H x⟫_ℂ ∂μ
      = ∫ x, ⟪F x, ∫ y, K y (H (x * y)) ∂μ⟫_ℂ ∂μ := by
  have hadj : Continuous fun y : Γ => ContinuousLinearMap.adjoint (K y⁻¹) :=
    (ContinuousLinearMap.adjoint (𝕜 := ℂ) (E := V) (F := V)).continuous.comp (hK.comp continuous_inv)

  have i1 : ∀ x, Integrable (fun y => ContinuousLinearMap.adjoint (K y⁻¹) (F (x * y))) μ := by
    intro x
    refine Continuous.integrable_of_hasCompactSupport
      (hadj.clm_apply (hF.comp (continuous_const.mul continuous_id))) ?_
    have c1 : HasCompactSupport fun y => F (x * y) := cF.comp_homeomorph (Homeomorph.mulLeft x)
    refine c1.mono (fun y hy => ?_)
    simp only [Function.mem_support, ne_eq] at hy ⊢
    intro h0
    exact hy (by rw [h0, map_zero])
  have i2 : ∀ x, Integrable (fun y => K y (H (x * y))) μ := by
    intro x
    refine Continuous.integrable_of_hasCompactSupport
      (hK.clm_apply (hH.comp (continuous_const.mul continuous_id))) ?_
    refine cK.mono (fun y hy => ?_)
    simp only [Function.mem_support, ne_eq] at hy ⊢
    intro h0
    exact hy (by rw [h0]; simp)

  have jA : Integrable (Function.uncurry fun x y : Γ => ⟪F (x * y⁻¹), K y (H x)⟫_ℂ) (μ.prod μ) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · have c1 : Continuous fun p : Γ × Γ => F (p.1 * p.2⁻¹) :=
        hF.comp (continuous_fst.mul continuous_snd.inv)
      have c2 : Continuous fun p : Γ × Γ => K p.2 (H p.1) :=
        (hK.comp continuous_snd).clm_apply (hH.comp continuous_fst)
      exact c1.inner c2
    · refine HasCompactSupport.intro (cH.isCompact.prod cK.isCompact) (fun p hp => ?_)
      have : H p.1 = 0 ∨ K p.2 = 0 := by
        by_contra hc
        push_neg at hc
        exact hp ⟨subset_tsupport _ hc.1, subset_tsupport _ hc.2⟩
      rcases this with h0 | h0 <;> simp [Function.uncurry, h0]
  have jB : Integrable (Function.uncurry fun x y : Γ => ⟪F x, K y (H (x * y))⟫_ℂ) (μ.prod μ) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · have c2 : Continuous fun p : Γ × Γ => K p.2 (H (p.1 * p.2)) :=
        (hK.comp continuous_snd).clm_apply (hH.comp (continuous_fst.mul continuous_snd))
      exact (hF.comp continuous_fst).inner c2
    · refine HasCompactSupport.intro (cF.isCompact.prod cK.isCompact) (fun p hp => ?_)
      have : F p.1 = 0 ∨ K p.2 = 0 := by
        by_contra hc
        push_neg at hc
        exact hp ⟨subset_tsupport _ hc.1, subset_tsupport _ hc.2⟩
      rcases this with h0 | h0 <;> simp [Function.uncurry, h0]
  calc ∫ x, ⟪∫ y, ContinuousLinearMap.adjoint (K y⁻¹) (F (x * y)) ∂μ, H x⟫_ℂ ∂μ
      = ∫ x, ∫ y, ⟪F (x * y⁻¹), K y (H x)⟫_ℂ ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only
        rw [inner_integral_left (i1 x) (H x),
          ← integral_inv_eq_self (fun y => ⟪F (x * y⁻¹), K y (H x)⟫_ℂ) μ]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only [inv_inv]
        exact ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = ∫ y, ∫ x, ⟪F (x * y⁻¹), K y (H x)⟫_ℂ ∂μ ∂μ := integral_integral_swap jA
    _ = ∫ y, ∫ x, ⟪F x, K y (H (x * y))⟫_ℂ ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [← integral_mul_right_eq_self (fun x => ⟪F (x * y⁻¹), K y (H x)⟫_ℂ) y]
        simp only [mul_inv_cancel_right]
    _ = ∫ x, ∫ y, ⟪F x, K y (H (x * y))⟫_ℂ ∂μ ∂μ := (integral_integral_swap jB).symm
    _ = ∫ x, ⟪F x, ∫ y, K y (H (x * y)) ∂μ⟫_ℂ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        exact integral_inner (i2 x) (F x)

end General

variable {n : ℕ}

instance instSC : SecondCountableTopology (G n) := by
  haveI : SecondCountableTopology (Mat n) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Mat n)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Mat n)).symm.secondCountableTopology
  exact (Units.isEmbedding_embedProduct (M := Mat n)).secondCountableTopology

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n := by
  change y.val.det ≠ 0
  exact (Matrix.isUnits_det_units y).ne_zero

theorem pairAdj : LgFacts → Unimod → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (f h : Mat n → E.V), KReg k → ContinuousOn f (GLs n) → ContinuousOn h (GLs n) → Cpt f → Cpt h → (haveI := FiniteDimensional.complete ℂ E.V; ∫ x : G n, ⟪act μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) f x.val, h x.val⟫_ℂ ∂μ = ∫ x : G n, ⟪f x.val, act μ E k h x.val⟫_ℂ ∂μ) := by
  intro hL hU n _ _ μ _ E k f h hk hf hh cf ch
  haveI := FiniteDimensional.complete ℂ E.V
  haveI : μ.IsMulRightInvariant := (hU n μ).1
  haveI : μ.IsInvInvariant := (hU n μ).2
  have hc : ∀ R, IsCompact {y : G n | lg y.val ≤ R} := (hL n).2.2.2.2.1
  haveI : SigmaFinite μ := ⟨⟨⟨fun m : ℕ => {y : G n | lg y.val ≤ m}, fun _ => trivial,
    fun m => (hc m).measure_lt_top,
    Set.eq_univ_of_forall fun y => Set.mem_iUnion.2 (exists_nat_ge (lg y.val))⟩⟩⟩
  have cont : ∀ {W : Type} [TopologicalSpace W] {φ : Mat n → W}, ContinuousOn φ (GLs n) →
      Continuous fun y : G n => φ y.val := fun hφ =>
    hφ.comp_continuous Units.continuous_val val_mem_GLs
  have supp : ∀ {W : Type} [TopologicalSpace W] [Zero W] {φ : Mat n → W},
      (∃ R, ∀ y ∈ GLs n, R < lg y → φ y = 0) → HasCompactSupport fun y : G n => φ y.val := by
    rintro W _ _ φ ⟨R, hR⟩
    exact HasCompactSupport.intro (hc R) fun y hy => hR _ (val_mem_GLs y) (not_le.1 hy)
  have key := pair_general μ (fun y : G n => k y.val) (fun x => f x.val) (fun x => h x.val)
    (cont hk.1) (cont hf) (cont hh) (supp hk.2) (supp cf) (supp ch)
  simp only [Matrix.coe_units_inv, Units.val_mul] at key
  exact key

end GlobalTheory.CompanionTheory.WaveMult.PairAdj
end
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

namespace GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve

section RingNorm

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem continuous_exp_smul {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp (t • Y)) :=
  continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y t).continuousAt

theorem hasDerivAt_exp_smul_zero {n : ℕ} (Y : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Y)) Y 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h

end RingNorm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem exp_smul_mem_unitaryGroup {n : ℕ} (Y : Mat n) (hY : Yᴴ = -Y) (t : ℝ) :
    NormedSpace.exp (t • Y) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have hc : (t • Y)ᴴ = -(t • Y) := by
    rw [conjTranspose_smul, hY]; simp
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, hc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Y)).neg_right]
  simp

theorem exists_unitary_curve : ∀ {n : ℕ} (Y : Mat n), Yᴴ = -Y →
    ∃ c : ℝ → Matrix.unitaryGroup (Fin n) ℂ, Continuous c ∧ c 0 = 1 ∧
      (∀ s t, c (s + t) = c s * c t) ∧ HasDerivAt (fun t => (c t).1) Y 0 := by
  intro n Y hY
  refine ⟨fun t => ⟨NormedSpace.exp (t • Y), exp_smul_mem_unitaryGroup Y hY t⟩,
    (continuous_exp_smul Y).subtype_mk _, ?_, ?_, ?_⟩
  · apply Subtype.ext
    simp
  · intro s t
    apply Subtype.ext
    show NormedSpace.exp ((s + t) • Y) = NormedSpace.exp (s • Y) * NormedSpace.exp (t • Y)
    rw [add_smul]
    exact Matrix.exp_add_of_commute _ _
      (((Commute.refl Y).smul_left s).smul_right t)
  · exact hasDerivAt_exp_smul_zero Y

end GlobalTheory.CompanionTheory.WaveSpd.UnitaryCurve
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

namespace GlobalTheory.CompanionTheory.JacquetEquiv

theorem nonempty_jacquetRep_equiv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (γ : Fin n → ℕ) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (π : Representation ℂ (GL (Fin n) F) V) (π' : Representation ℂ (GL (Fin n) F) V'), π.Equiv π' → Nonempty ((jacquetRep F n γ π).Equiv (jacquetRep F n γ π')) := by
  intro F _ _ _ _ n γ V V' _ _ _ _ π π' φ
  let e : V ≃ₗ[ℂ] V' := φ.toLinearEquiv
  have he : ∀ g, (e : V →ₗ[ℂ] V') ∘ₗ π g = π' g ∘ₗ (e : V →ₗ[ℂ] V') := by
    intro g
    rw [Representation.Equiv.toLinearEquiv_toLinearMap]
    exact φ.toIntertwiningMap.isIntertwining' g
  have he' := LinearEquiv.isIntertwining_symm_isIntertwining he
  let f : Representation.IntertwiningMap (MonoidHom.comp π (unipotentRadical F n γ).subtype) (MonoidHom.comp π' (unipotentRadical F n γ).subtype) :=
    ⟨(e : V →ₗ[ℂ] V'), fun x => he x⟩
  let g : Representation.IntertwiningMap (MonoidHom.comp π' (unipotentRadical F n γ).subtype) (MonoidHom.comp π (unipotentRadical F n γ).subtype) :=
    ⟨(e.symm : V' →ₗ[ℂ] V), fun x => he' x⟩
  let M := Representation.Coinvariants.map _ _ f
  let M' := Representation.Coinvariants.map _ _ g
  have hMM' : M ∘ₗ M' = LinearMap.id := by
    apply Representation.Coinvariants.hom_ext
    ext v
    simp only [LinearMap.comp_apply, LinearMap.id_apply, M, M', Representation.Coinvariants.map_mk]
    congr 1
    exact e.apply_symm_apply v
  have hM'M : M' ∘ₗ M = LinearMap.id := by
    apply Representation.Coinvariants.hom_ext
    ext v
    simp only [LinearMap.comp_apply, LinearMap.id_apply, M, M', Representation.Coinvariants.map_mk]
    congr 1
    exact e.symm_apply_apply v
  let E := LinearEquiv.ofLinearMap (re₁₂ := RingHomInvPair.ids) (re₂₁ := RingHomInvPair.ids) M M' hMM' hM'M
  refine ⟨Representation.Equiv.mk E ?_⟩
  intro m
  apply Representation.Coinvariants.hom_ext
  ext u
  have hc : f ((π (m : GL (Fin n) F)) u) = (π' (m : GL (Fin n) F)) (f u) := LinearMap.congr_fun (he m) u
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, E, LinearEquiv.coe_ofLinearMap, jacquetRep,
    GroundTheory.Automorphic.Parabolic.twist_apply, map_smul, GroundTheory.Automorphic.Parabolic.jacquetAction,
    MonoidHom.coe_mk, OneHom.coe_mk, GroundTheory.Automorphic.coinvariantsTranslate_mk, M,
    Representation.Coinvariants.map_mk]
  rw [hc]

end GlobalTheory.CompanionTheory.JacquetEquiv
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

namespace GlobalTheory.CompanionTheory.Conductor

theorem mem_chartRingQ_of_mem_chartRingZ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {x : Ω}
    (hx : x ∈ chartRingZ y c) : x ∈ chartRingQ y c := by
  unfold chartRingZ at hx
  unfold chartRingQ
  induction hx using Algebra.adjoin_induction with
  | mem z hz => exact Algebra.subset_adjoin hz
  | algebraMap r =>
    rw [eq_intCast (algebraMap ℤ Ω) r]
    exact intCast_mem _ r
  | add u v _ _ hu hv => exact add_mem hu hv
  | mul u v _ _ hu hv => exact mul_mem hu hv

theorem exists_conductor_section :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
      (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
      ∃ (e : K → ℕ) (c : Ω), c ≠ 0 ∧ ∀ (a : K → ℤ) (τ : ℕ),
        ∀ s ∈ Submodule.span ℚ (chartLatNm y a τ : Set Ω),
          c * s ∈ chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1 := by
  classical
  intro K _ ι _ Ω _ _ y D _ hbir
  let C := {c : ∀ k, ι k // ∀ k, y ⟨k, c k⟩ ≠ 0}
  choose δ F hF hF0 hcond using fun c : C => Conductor.exists_chart_conductor y hbir c.1 c.2
  refine ⟨∑ c : C, δ c, ∏ c : C, aeval y (F c), Finset.prod_ne_zero_iff.mpr fun c _ => hF0 c,
    fun a τ s hs => ?_⟩
  have key : ∀ s ∈ chartLatNm y a τ, (∏ c : C, aeval y (F c)) * s ∈
      chartLatQ y ((τ : ℤ) • a + fun k => (((∑ c : C, δ c) k : ℕ) : ℤ)) 1 := by
    intro s hs c' hc'
    let c : C := ⟨c', hc'⟩
    have hx := hs c' hc'
    have hm : ∏ k, y ⟨k, c' k⟩ ^ (-(((1 : ℕ) : ℤ) *
          (((τ : ℤ) • a + fun k => (((∑ c : C, δ c) k : ℕ) : ℤ)) k))) =
        (∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k))) * Conductor.invMon y c' (∑ c : C, δ c) := by
      rw [← Conductor.prod_zpow_eq_invMon, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_add₀ (hc' k)]
      congr 1
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_one, one_mul]
      ring
    apply mem_chartRingQ_of_mem_chartRingZ
    rw [hm, ← Conductor.invMon_sum y c' Finset.univ δ]
    have hsplit : (∏ b : C, aeval y (F b)) * s * ((∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k))) *
          ∏ b : C, Conductor.invMon y c' (δ b)) =
        (∏ b ∈ Finset.univ.erase c, aeval y (F b) * Conductor.invMon y c' (δ b)) *
          (aeval y (F c) * Conductor.invMon y c' (δ c) *
            (s * ∏ k, y ⟨k, c' k⟩ ^ (-((τ : ℤ) * a k)))) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun b => aeval y (F b)) (Finset.mem_univ c),
        ← Finset.mul_prod_erase Finset.univ (fun b => Conductor.invMon y c' (δ b)) (Finset.mem_univ c),
        Finset.prod_mul_distrib]
      ring
    rw [hsplit]
    exact mul_mem (prod_mem fun b _ => Conductor.form_mul_invMon_mem y c' (hF b)) (hcond c _ hx)
  induction hs using Submodule.span_induction with
  | mem x hx => exact key x hx
  | zero => simpa using Submodule.zero_mem _
  | add u v _ _ hu hv => rw [mul_add]; exact Submodule.add_mem _ hu hv
  | smul r u _ hu => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hu

end GlobalTheory.CompanionTheory.Conductor
end

section

open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

theorem _root_.GlobalTheory.T.adic_complete_tensor_finite : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (l : ℕ), Irreducible (l : W) → ∀ (A : Type) [CommRing A] [Algebra W A] [IsAdicComplete (Ideal.span {(l : A)}) A] (L : Type 1) [AddCommGroup L] [Module W L] [Module.Finite W L], IsAdicComplete (Ideal.span {(l : A)}) (A ⊗[W] L) := by
  first | exact @GlobalTheory.CompanionTheory.TensorCompleteFinite.isAdicComplete_tensor_finite | exact GlobalTheory.CompanionTheory.TensorCompleteFinite.isAdicComplete_tensor_finite | (intros; apply GlobalTheory.CompanionTheory.TensorCompleteFinite.isAdicComplete_tensor_finite <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_scheme_base_change_exists : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (A : Over (Sp R)) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ (A' : Over (Sp R')) (_ : GrpObj A') (φ : A'.left ⟶ A.left), IsAbelianScheme A' ∧
      SmoothOfRelativeDimension g A'.hom ∧ IsPullback φ A'.hom A.hom (spMap (algebraMap R R')) := by
  first | exact @GlobalTheory.CompanionTheory.Axis.exists_abelianScheme_baseChange_ringHom | exact GlobalTheory.CompanionTheory.Axis.exists_abelianScheme_baseChange_ringHom | (intros; apply GlobalTheory.CompanionTheory.Axis.exists_abelianScheme_baseChange_ringHom <;> assumption)
end
