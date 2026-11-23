module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle311
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle014
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle010
import Formalism.SharpRestriction.CuspSpanNormBounds.ThresholdCubicInequalitySignPattern
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle011
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle371
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.WittIndexEqZeroIff
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (resL resR)

noncomputable section

namespace GlobalTheory.Core.Rk.DeltaTheta

variable {D : D7}

def fstH (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun := resL A B
  map_zero' := rfl
  map_add' _ _ := rfl

def sndH (A B : HSp D) : WO (dblSp A) B →+ WO A B where
  toFun x := -resR A B x
  map_zero' := neg_zero
  map_add' x y := neg_add (resR A B x) (resR A B y)

theorem continuous_fstH (A B : HSp D) : Continuous (fstH A B) :=
  continuous_matrix fun i _ => continuous_id.matrix_elem i _

theorem continuous_sndH (A B : HSp D) : Continuous (sndH A B) := by
  obtain ⟨i1, -⟩ := GlobalTheory.MixModel.lattice_Mx D B.rank A.rank
  have h : Continuous (resR A B) := continuous_matrix fun i _ => continuous_id.matrix_elem i _
  exact h.neg

theorem map_fstH {R : Type} [CommRing R] (φ : AE D →+* R) (A B : HSp D) {u : WO (dblSp A) B} (h : u.map φ = 0) :
    (fstH A B u).map φ = 0 :=
  Matrix.ext fun i j => congrFun (congrFun h i) (finSumFinEquiv (Sum.inl j))

theorem map_sndH {R : Type} [CommRing R] (φ : AE D →+* R) (A B : HSp D) {u : WO (dblSp A) B} (h : u.map φ = 0) :
    (sndH A B u).map φ = 0 :=
  Matrix.ext fun i j => by
    have e : φ (u i (finSumFinEquiv (Sum.inr j))) = 0 := congrFun (congrFun h i) (finSumFinEquiv (Sum.inr j))
    change φ (-(u i (finSumFinEquiv (Sum.inr j)))) = 0
    rw [map_neg, e, neg_zero]

theorem hO_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    hO (dblSp A) B x y = hO A B (fstH A B x) (fstH A B y) - hO A B (sndH A B x) (sndH A B y) := by
  have hi : (dblSp A).gram⁻¹ = blkMat finSumFinEquiv A.gram⁻¹ (-A.gram⁻¹) := Matrix.inv_eq_left_inv (by
    rw [gram_hdbl, dblGram, blkMat_mul, neg_mul_neg, Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det A), blkMat_one])
  simp only [hO, hi, ← finSumFinEquiv.sum_comp, Fintype.sum_sum_type, fstH, sndH, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    resR, Matrix.of_apply,
    blkMat, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply, map_zero,
    map_neg, zero_mul, Finset.sum_const_zero, add_zero, zero_add, neg_mul, mul_neg, neg_neg,
    Finset.sum_neg_distrib, sub_eq_add_neg]
  rfl

theorem symplOH_dbl (A B : HSp D) (x y : WO (dblSp A) B) :
    symplOH (dblSp A) B x y =
      symplOH A B (fstH A B x) (fstH A B y) - symplOH A B (sndH A B x) (sndH A B y) := by
  simp only [GlobalTheory.MixModel.symplOH_eq, hO_dbl, map_sub]

theorem conj_char {G : Type} [AddCommGroup G] (ψ : AddChar G ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : G) :
    conj (ψ x) = ψ (-x) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (h x)]

theorem isThetaFunO_delta {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ x, ‖ψ x‖ = 1) {A B : HSp D} {f₁ f₂ : WO A B → ℂ}
    (h₁ : IsThetaFunO ψ A B f₁) (h₂ : IsThetaFunO ψ A B f₂) : IsThetaFunO ψ (dblSp A) B (delta A B f₁ f₂) := by
  have hd : delta A B f₁ f₂ = fun w => f₁ (fstH A B w) * conj (f₂ (sndH A B w)) := rfl
  rw [hd]
  refine ⟨fun γ w => ?_, ?_, ?_, fun k L hL h0 w => ?_⟩
  · have e₁ : fstH A B (ratW B (dblSp A) γ) =
        ratW B A (Matrix.of fun i j => γ i (finSumFinEquiv (Sum.inl j))) := rfl
    have e₂ : sndH A B (ratW B (dblSp A) γ) =
        ratW B A (Matrix.of fun i j => -γ i (finSumFinEquiv (Sum.inr j))) :=
      Matrix.ext fun i j => (map_neg (incA D) _).symm
    rw [map_add (f := _), map_add (f := _), symplOH_dbl, e₁, e₂, h₁.quasi, h₂.quasi, map_mul, conj_char ψ hn, neg_neg, neg_sub,
      sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  · obtain ⟨U₁, hU₁, k₁⟩ := h₁.level
    obtain ⟨U₂, hU₂, k₂⟩ := h₂.level
    refine ⟨U₁.comap (fstH A B) ⊓ U₂.comap (sndH A B),
      (hU₁.preimage (continuous_fstH A B)).inter (hU₂.preimage (continuous_sndH A B)), fun u hu h0 => ?_⟩
    funext w
    have e₁ := congrFun (k₁ _ hu.1 (map_fstH _ _ _ h0)) (fstH A B w)
    have e₂ := congrFun (k₂ _ hu.2 (map_sndH _ _ _ h0)) (sndH A B w)
    simp only [heisO] at e₁ e₂ ⊢
    rw [← e₁, ← e₂, symplOH_dbl, sub_eq_add_neg, AddChar.map_add_eq_mul, map_add (f := _), map_add (f := _), map_mul, conj_char ψ hn]
    ring
  · exact (h₁.cont.comp (continuous_fstH A B)).mul
      (Complex.continuous_conj.comp (h₂.cont.comp (continuous_sndH A B)))
  · simp only [map_add (f := _)]
    exact (h₁.smooth k ((fstH A B).comp L) ((continuous_fstH A B).comp hL) (fun t => map_fstH _ _ _ (h0 t)) _).mul
      (Complex.conjCLE.contDiff.comp (h₂.smooth k ((sndH A B).comp L) ((continuous_sndH A B).comp hL)
        (fun t => map_sndH _ _ _ (h0 t)) _))

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D), IsStdChar D ψ (-1) → ∀ f₁ f₂, IsThetaFunO ψ A B f₁ → IsThetaFunO ψ A B f₂ → IsThetaFunO ψ (dblSp A) B (delta A B f₁ f₂) :=
  fun _ _ _ _ hψ _ _ h₁ h₂ => isThetaFunO_delta hψ.1.2.1 h₁ h₂

end GlobalTheory.Core.Rk.DeltaTheta

end
end

section

noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.CuspConj

theorem isKFinite_conj {G : Type} [Group G] {K : Subgroup G} {Φ : G → ℂ} (h : GlobalTheory.Doubling.IsKFinite K Φ) :
    GlobalTheory.Doubling.IsKFinite K fun g => conj (Φ g) := by
  unfold GlobalTheory.Doubling.IsKFinite GlobalTheory.Doubling.kSpan at *
  refine GlobalTheory.Mem.AutConj.finiteDimensional_span_star h ?_
  rintro f ⟨k, hk, rfl⟩
  refine ⟨k, hk, ?_⟩
  funext g
  show star (conj (Φ (g * k))) = Φ (g * k)
  rw [starRingEnd_apply, star_star]

theorem conj_comp_mem_A0 : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A), IsInfFam θ →
    ∀ u ∈ GlobalTheory.Cusp.A0 θ A cA, (fun g => conj (u g)) ∈ GlobalTheory.Cusp.A0 θ A cA := by
  intro D θ A cA hθ u hu
  have hu' : u ∈ autForms θ A (Kinf θ A cA) ⊓ cuspCont A := hu
  show (fun g => conj (u g)) ∈ autForms θ A (Kinf θ A cA) ⊓ cuspCont A
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hu'
  obtain ⟨hs, hk⟩ := mem_autForms.1 h1
  refine Submodule.mem_inf.2 ⟨mem_autForms.2 ⟨?_, isKFinite_conj hk⟩, conj_mem_cuspCont h2⟩
  exact GlobalTheory.Mem.AutConj.isAutFunSm_star D θ hθ A u hs

end GlobalTheory.Core.Rk.CuspConj

end
end

section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem genericTerms_points_agree_groupSums_corankOne : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ), (∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ ↔ PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ) ∧ (∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ ↔ HasPt Y u u (Y.tO u u).genSet γ) ∧ (∀ c γ ν, PN.grp (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν = grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν) ∧ ((∀ t ∈ (Y.tO u u).genSet, J2of Y u u νL (ptPN t) = 0 → (Y.tO u u).vec t = 0) → PN.AmpInput (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng)) := by
  intro D X Y u νL νB ng
  have hs : (genT (scT (Y.tO u u))).ngSet = (Y.tO u u).genSet := genT_ngSet _
  have hs' : (genT (Y.tO u u)).ngSet = (Y.tO u u).genSet := genT_ngSet _
  have hA : ∀ γ, PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ ↔ HasPt Y u u (Y.tO u u).genSet γ := by
    intro γ
    constructor
    · rintro ⟨c, ν, t, ht, hv, -, hp, -⟩
      rw [hs] at ht
      exact ⟨t, ht, hv, hp⟩
    · rintro ⟨t, ht, hv, hp⟩
      exact ⟨cls1 Y u t, nmlOf Y u u t, t, hs ▸ ht, hv, rfl, hp, rfl⟩
  have hB : ∀ γ, PN.IsPt (genT (Y.tO u u)) (NOfG Y u νL νB ng) γ ↔ HasPt Y u u (Y.tO u u).genSet γ := by
    intro γ
    constructor
    · rintro ⟨c, ν, t, ht, hv, -, hp, -⟩
      rw [hs'] at ht
      exact ⟨t, ht, hv, hp⟩
    · rintro ⟨t, ht, hv, hp⟩
      exact ⟨clsG Y u t, nmlOf Y u u t, t, hs' ▸ ht, hv, rfl, hp, rfl⟩
  have hG : ∀ c γ ν, PN.grp (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) c γ ν =
      grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν := by
    intro c γ ν
    unfold PN.grp grpF
    rw [hs]
    rfl
  refine ⟨fun γ => (hA γ).trans (hB γ).symm, hA, hG, ?_⟩
  intro h
  have hJ : ∀ γ, 0 ≤ J2of Y u u νL γ := fun γ => J2of_nonneg Y u u νL γ
  have hV : ∀ c γ ν, J2of Y u u νL γ = 0 → grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν = 0 := by
    intro c γ ν h0
    unfold grpF
    have hz : ∀ t, ((Y.tO u u).genSet ∩ {t | cls1 Y u t = c ∧ ptPN t = γ ∧ nmlOf Y u u t = ν}).indicator
        (Y.tO u u).vec t = 0 := by
      intro t
      by_cases ht : t ∈ (Y.tO u u).genSet ∩ {t | cls1 Y u t = c ∧ ptPN t = γ ∧ nmlOf Y u u t = ν}
      · rw [Set.indicator_apply, if_pos ht]
        exact h t ht.1 (by rw [ht.2.2.1]; exact h0)
      · rw [Set.indicator_apply, if_neg ht]
    simp only [hz, tsum_zero]
  refine ⟨fun c γ ν => ?_, hJ, fun c γ ν => ?_⟩
  · show 0 ≤ a2F Y u u (Y.tO u u).genSet (cls1 Y u) νL c γ ν
    unfold a2F
    exact div_nonneg (by positivity) (hJ γ)
  · rw [hG]
    show ‖grpF Y u u (Y.tO u u).genSet (cls1 Y u) c γ ν‖ ^ 2 ≤
      a2F Y u u (Y.tO u u).genSet (cls1 Y u) νL c γ ν * J2of Y u u νL γ
    unfold a2F
    by_cases h0 : J2of Y u u νL γ = 0
    · rw [hV c γ ν h0]; simp
    · rw [div_mul_cancel₀ _ h0]

end GlobalTheory.Core.One
end

section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.One

theorem stepClass1_of (h : CorankOneIsEquivalenceOnRow) : StepClass1 := by
  intro D X Y u hc νL νB ng
  obtain ⟨hR, hS, hT⟩ := h D X Y u u hc
  have hsub : ∀ t ∈ (Y.tO u u).genSet, t ∈ (Y.tO u u).nzSet := fun t ht => ht.1
  intro t ht t' ht'
  rw [genT_ngSet] at ht ht'
  change t ∈ (Y.tO u u).genSet at ht
  change t' ∈ (Y.tO u u).genSet at ht'
  have es : (genT (scT (Y.tO u u))).s0 t t' = 1 ↔ (Y.tO u u).s0 t t' = 1 := by
    simp only [genT, scT, and_true]
    by_cases hc : (Y.tO u u).s0 t t' = 1
    · simp [hc]
    · simp [hc]
  show ((scT (Y.tO u u)).rowOf t = (scT (Y.tO u u)).rowOf t' ∧ (genT (scT (Y.tO u u))).s0 t t' = 1) ↔
    cls1 Y u t = cls1 Y u t'
  rw [es]
  change ((Y.tO u u).rowOf t = (Y.tO u u).rowOf t' ∧ (Y.tO u u).s0 t t' = 1) ↔ cls1 Y u t = cls1 Y u t'
  constructor
  · rintro ⟨hr, h1⟩
    have b1 := hS t (hsub t ht) t' (hsub t' ht') hr h1
    ext x
    simp only [cls1, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hx, hrx, hx1⟩
      exact ⟨hx, hrx.trans hr, hT t' (hsub t' ht') t (hsub t ht) x (hsub x hx) hr.symm hrx.symm b1 hx1⟩
    · rintro ⟨hx, hrx, hx1⟩
      exact ⟨hx, hrx.trans hr.symm, hT t (hsub t ht) t' (hsub t' ht') x (hsub x hx) hr hrx.symm h1 hx1⟩
  · intro hc
    have hm : t' ∈ cls1 Y u t' := ⟨ht', rfl, hR t' (hsub t' ht')⟩
    rw [← hc] at hm
    exact ⟨hm.2.1.symm, hm.2.2⟩

end GlobalTheory.Core.One
end

section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One

namespace GlobalTheory.Core.One

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem ampQ_not_eq_ampG {Cl Nu : Type} (L : PN.LocalNG Cl Nu) : ampQ Not L = ampG L := by
  funext d
  unfold ampQ ampG
  rw [Finset.sum_eq_single_of_mem ∅ (by simp) (fun A hA h => absurd (by simp at hA; exact hA.2) h)]
  simp

private theorem hasPt_of_isPt {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word)
    (νL νB : X.B.I.Ginf → Measure X.B.I.Ginf) (ng : PN.Pts D.host.E D.R.rS → ℝ) (γ : PN.Pts D.host.E D.R.rS)
    (h : PN.IsPt (genT (scT (Y.tO u u))) (NOf1 Y u νL νB ng) γ) : HasPt Y u u (Y.tO u u).genSet γ := by
  obtain ⟨c, n, t, ht, hv, -, hp, -⟩ := h
  rw [genT_ngSet] at ht
  exact ⟨t, ht, hv, hp⟩

theorem stepFam1_of : (∀ D : D7, 4 * D.R.rS + 7 ≤ D.R.k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets D.R.k D.R.rS 9) → Formalism.L2.SG.FamDefs.HTie → FamGen1 → FamilyWeightSumUnfoldingIdentity → WeightsFam → FamilyGroupSumFactorsWeightAmplitude → ExistFam → StepFam1 := by
  intro hG6 hH hF hG5 hW hG4 hE Cg cb Cw cT CT C0
  obtain ⟨CSt, hCSt, a4, b4, h4⟩ := hG4 Cg cb Cw cT CT C0
  obtain ⟨aH, bH, hH2⟩ := hH Cg cb Cw cT CT C0
  obtain ⟨a5, b5, h5⟩ := hG5 Cg cb Cw cT CT C0
  obtain ⟨aW, bW, hW2⟩ := hW Cg cb Cw cT CT C0
  obtain ⟨aE, bE, hE2⟩ := hE Cg cb Cw cT CT C0
  refine ⟨9, CSt, hCSt, max a4 (max aH (max a5 (max aW aE))), max b4 (max bH (max b5 (max bW bE))),
    fun C' Cl e1 e2 D large₂ X Y u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν => ?_⟩
  simp only [max_le_iff] at e1 e2
  obtain ⟨e1a, e1b, e1c, e1d, e1e⟩ := e1
  obtain ⟨e2a, e2b, e2c, e2d, e2e⟩ := e2
  have hQ := hF D X Y u hc.2.2
  obtain ⟨s, hs1, hs0, hsb, htie⟩ :=
    h4 C' Cl e1a e2a D large₂ X Y u u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν
  refine ⟨s, hs1, hs0, hsb, fun γ hγ S => ?_⟩
  have hP := hasPt_of_isPt Y u _ _ _ γ hγ
  obtain ⟨Fm, hFT, hRel, hTerm, hDs, hrw⟩ := hE2 C' Cl e1e e2e D large₂ X Y u u hc _ _ _ _ hQ γ hP
  have hG5Fm := Formalism.L2.SG.FamDefs.orbitFamilyIdentity_at_volume hFT (h5 C' Cl e1c e2c D large₂ X Y u u hc _ _ _ _ hQ γ hP Fm hFT)
  obtain ⟨hWpos, hWle⟩ := hW2 C' Cl e1d e2d D large₂ X Y u u hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk
    _ _ _ _ hQ γ hP Fm hFT hRel hTerm hG5Fm
  refine ⟨Fm, Formalism.L2.SG.FamDefs.famOKS_of (NOf1 Y u (sc s ν) ν (fun _ => 0)) γ S _ (fun L => ampG L) Fm hFT
    hRel hTerm hDs hrw (hG6 D (Formalism.L2.SG.FamDefs.four_rank_add_seven_le_k hc)) hG5Fm
    (hH2 C' Cl e1b e2b D large₂ X Y u u hc _ _ _ γ Fm hFT) hWpos hWle (fun x _ => ?_)⟩
  have h := htie _ _ _ _ hQ γ hP Fm hFT x.1 x.2
  rw [ampQ_not_eq_ampG] at h
  exact h

end GlobalTheory.Core.One
end
end

section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.Pf.MainEqCut Formalism.L2.SG.Pf.MainEqSteps Formalism.L2.SG.Pf.MainEqAna Formalism.L2.SG.Pf.MainEqLoc Formalism.L2.SG.Pf.MainEqFam GlobalTheory.SnFam GlobalTheory.Core.One
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Diag

theorem mR_eq_m (D : D7) : Formalism.L2.SG.RowsConc.mR D = (D.R.m : ℝ) := by
  have h : 2 * D.R.rS + 2 = D.R.m := by
    obtain ⟨j, hj⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Formalism.BasicNotions.Ranks.rS
    omega
  unfold Formalism.L2.SG.RowsConc.mR
  rw [h]

theorem log_b_eq (D : D7) (large₂ : SizeData₂ D) : Real.log large₂.sc.b = large₂.sc.L := by
  unfold Formalism.BasicNotions.Scale.b
  exact Real.log_exp _

theorem gamB_eq_gamL (D : D7) (large₂ : SizeData₂ D) (C : ℝ) : gamB D large₂ C = gamL D large₂.sc.L C := by
  unfold gamB gamL
  rw [mR_eq_m, log_b_eq]

theorem epsNG_le_gamL (D : D7) (large₂ : SizeData₂ D) (C : ℝ) : epsNG D large₂ C ≤ gamL D large₂.sc.L C := by
  unfold epsNG
  have h1 : ((2 : ℝ) ^ (D.R.k - 2 * D.R.rS - 5))⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have h2 : Real.exp (C * Formalism.L2.SG.RowsConc.mR D ^ 5 * D.R.f * Real.log large₂.sc.b) = gamL D large₂.sc.L C := by
    unfold gamL
    rw [mR_eq_m, log_b_eq]
  rw [h2]
  exact mul_le_of_le_one_left (Real.exp_pos _).le h1

theorem oneOn_singleton_of_rows :
    (RowGen1P → ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} true) ∧ (GlobalTheory.NGRow.RowNGP → ∀ c : ℝ, GlobalTheory.Core.Diag.OneOn {c} false) := by
  constructor
  · intro hG c Cg cb Cu cT CT hcb hcT
    obtain ⟨CB, hCB, C'₀, Cl₀, H⟩ := hG Cg cb Cu cT CT c hcb hcT
    refine ⟨CB, hCB, max (max C'₀ Cl₀) 3, ?_⟩
    intro C0 hC0 C' Cl h1 h2 D large₂ X Y u hT hH hC ha
    rw [Set.mem_singleton_iff] at hC0
    subst hC0
    have a1 : C'₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
    have b1 : Cl₀ ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h2
    have b3 : (2 : ℝ) < Cl := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) h2)
    have hs : Formalism.MainNotions.S.Cnt.Stand D u u := Formalism.MainNotions.Stand_of D large₂ C' Cl Cg cb Cu cT CT C0 hH.2.1 hH.1 b3 u u
    have r := H C' Cl a1 b1 D large₂ X Y u hT hH hs hC ha
    unfold GeneratorBoundAt at r
    rw [gamB_eq_gamL] at r
    rw [if_pos rfl]
    exact r
  · intro hN c Cg cb Cu cT CT hcb hcT
    obtain ⟨C4, hC4, C'₀, Cl₀, H⟩ := hN Cg cb Cu cT CT c hcb hcT
    refine ⟨C4, hC4, max (max C'₀ Cl₀) 3, ?_⟩
    intro C0 hC0 C' Cl h1 h2 D large₂ X Y u hT hH hC ha
    rw [Set.mem_singleton_iff] at hC0
    subst hC0
    have a1 : C'₀ ≤ C' := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) h1
    have b1 : Cl₀ ≤ Cl := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) h2
    have b3 : (2 : ℝ) < Cl := lt_of_lt_of_le (by norm_num) (le_trans (le_max_right _ _) h2)
    have hs : Formalism.MainNotions.S.Cnt.Stand D u u := Formalism.MainNotions.Stand_of D large₂ C' Cl Cg cb Cu cT CT C0 hH.2.1 hH.1 b3 u u
    have r : (Y.tO u u).pairSum ((Y.tO u u).one (Y.tO u u).ngSet) ≤ epsNG D large₂ C4 * ddC X Y u u :=
      H C' Cl a1 b1 D large₂ X Y u u hT hH hs hC ha
    rw [if_neg Bool.false_ne_true]
    exact r.trans (mul_le_mul_of_nonneg_right (epsNG_le_gamL D large₂ C4) (Formalism.L2.SG.RowsConc.dd_nonneg hC u u))

end GlobalTheory.Core.Diag
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem chainPar_inj_at (D : D7) (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (h : chainPar c B k w = chainPar c B' k w) : B w = B' w := by
  induction k with
  | zero => simpa [chainPar] using h
  | succ k ih =>
    apply ih
    rw [chainPar_succ, chainPar_succ] at h
    simp only [stepPar] at h
    have h2 := add_right_cancel h
    exact Multiset.map_injective (mul_right_injective _) h2

theorem chainPar_inj : ∀ (D : D7) (c : Com D) (k : ℕ) (B B' : GlobalTheory.LFun.Fam D.host.E) (w : HeightOneSpectrum (𝓞 D.host.E)),
    chainPar c B k w = chainPar c B' k w → B w = B' w :=
  chainPar_inj_at

end GlobalTheory.ChainOnto
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finDim_of_levFacts : GlobalTheory.Published.HarishChandraFinite → ∀ D : D7, LevFacts D → FinDim D := by
  intro hP D hL c hc j hj s hs
  have h1 := (hL c hc j hj s hs).1
  have : FiniteDimensional ℂ (Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L)) :=
    GlobalTheory.MultFinite.hcFinite hP hc.inf h1
  exact Module.Finite.map _ _

end GlobalTheory.ChainOnto

end
end
