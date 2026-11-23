module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHLIso
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle003
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle030
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianZZEqNeg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IsClosedSLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle029
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MulVecMapMem
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle045
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle032
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ProductExactness
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle044
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SecMeasLocHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle028
import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.BH.Sw

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.MainNotions.BridgeCSB Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem lieE_G : Formalism.MainNotions.S.lieE (UH (Hpk k r)) = (uH k r).map RL := by
  have h : Formalism.MainNotions.S.lieOf (UH (Hpk k r)) = ((uH k r : Submodule ℝ (Mat k r)) : Set (Mat k r)) := BH.lieG k r
  unfold Formalism.MainNotions.S.lieE
  rw [h]
  change Submodule.span ℝ (⇑(RL (k := k) (r := r)) '' ↑(uH k r)) = _
  rw [Submodule.span_image, Submodule.span_eq]

theorem lieG' : LieG := fun k r => lieE_G

theorem mulVec_bvec (X : Mat k r) (j i : Fin (2 * r + k + 1)) : (X *ᵥ bvec j) i = X i j := by
  simp [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one]

theorem mid_or (j : Fin (2 * r + k + 1)) (h : ¬ Mid k r j) :
    (∃ a : Fin r, j = eI k r a) ∨ (∃ a : Fin r, j = esI k r a) := by
  simp only [Mid, not_and_or, not_le] at h
  rcases h with h | h
  · exact Or.inl ⟨⟨j, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨2 * r + k - j, by omega⟩, Fin.ext ?_⟩
    have hj := j.isLt
    show (j : ℕ) = 2 * r + k - (2 * r + k - j)
    omega

private theorem mul_hpk_apply_lemma (A : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (A * Hpk k r) i j = A i (tau k r j) * sgn k r j := by
  rw [Matrix.mul_apply]
  simp_rw [Formalism.QuantumDeterminants.WeylGroupFacts.hpk_row]
  rw [Finset.sum_eq_single (tau k r j)]
  · rw [tau_tau, if_pos rfl, sgn_tau]
  · intro m _ hm
    rw [if_neg (fun h => hm (by rw [h, tau_tau])), mul_zero]
  · simp

private theorem adjH_apply_lemma_2 (X : Mat k r) (i j : Fin (2 * r + k + 1)) :
    (Hpk k r * Xᴴ * Hpk k r) i j = sgn k r i * star (X (tau k r j) (tau k r i)) * sgn k r j := by
  rw [mul_hpk_apply_lemma, Formalism.QuantumDeterminants.WeylGroupFacts.hpk_mul_apply, Matrix.conjTranspose_apply]

theorem lieWb_set : Formalism.MainNotions.S.lieOf (Formalism.FourierDecayAlt.B2.UWb k r) = (uWb k r : Set (Mat k r)) := by
  rw [BH.lieWb k r]
  ext X
  change _ ↔ (adjH X + X = 0 ∧ ∀ i j, ¬(Mid k r i ∧ Mid k r j) → X i j = 0)
  rw [adjH_def]
  constructor
  · rintro ⟨hX, hc⟩
    have hcol : ∀ i j, ¬ Mid k r j → X i j = 0 := by
      intro i j hj
      rcases mid_or j hj with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · rw [← mulVec_bvec X (eI k r a) i, (hc a).1]; rfl
      · rw [← mulVec_bvec X (esI k r a) i, (hc a).2]; rfl
    refine ⟨hX, fun i j hij => ?_⟩
    rcases not_and_or.1 hij with hi | hj
    · have h := congrFun (congrFun hX i) j
      simp only [Matrix.add_apply, Matrix.zero_apply] at h
      rw [adjH_apply_lemma_2] at h
      have htau : ¬ Mid k r (tau k r i) := by
        have := tau_out i (by simp only [Mid, not_and_or, not_le] at hi; exact hi)
        simp only [Mid, not_and_or, not_le]; exact this
      rw [hcol _ _ htau, star_zero, mul_zero, zero_mul, zero_add] at h
      exact h
    · exact hcol i j hj
  · rintro ⟨hX, hz⟩
    refine ⟨hX, fun a => ⟨?_, ?_⟩⟩
    · funext i
      rw [mulVec_bvec]
      apply hz
      intro h
      have h1 : r ≤ (a : ℕ) := h.2.1
      have := a.isLt
      omega
    · funext i
      rw [mulVec_bvec]
      apply hz
      intro h
      have h2 : 2 * r + k - (a : ℕ) ≤ r + k := h.2.2
      have := a.isLt
      omega

theorem lieWb' : LieWb := by
  intro k r
  refine ⟨fun Z hZ => ?_, ?_⟩
  · have h : Z ∈ Formalism.MainNotions.S.lieOf (Formalism.FourierDecayAlt.B2.UWb k r) := by rw [lieWb_set]; exact hZ
    simpa using h 1
  · unfold Formalism.MainNotions.S.lieE
    rw [lieWb_set]
    have : (fun X => (WithLp.equiv 2 _).symm (Formalism.MainNotions.S.realifyFun X)) '' (uWb k r : Set (Mat k r)) =
        (RL : Mat k r → _) '' (uWb k r : Set (Mat k r)) := rfl
    rw [this, Submodule.span_image, Submodule.span_eq]

def prodEquiv {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (p : Submodule R M) (q : Submodule R N) : ↥(p.prod q) ≃ₗ[R] ↥p × ↥q where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  map_add' x y := rfl
  map_smul' c x := rfl
  left_inv x := rfl
  right_inv y := rfl

theorem finrank_prodS {R M N : Type*} [Field R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (p : Submodule R M) (q : Submodule R N) [FiniteDimensional R p] [FiniteDimensional R q] :
    Module.finrank R ↥(p.prod q) = Module.finrank R p + Module.finrank R q := by
  rw [(prodEquiv p q).finrank_eq, Module.finrank_prod]

private theorem eq_zero_of_RL_lemma_3 (M : Mat k r) (h : ‖RL (k := k) (r := r) M‖ ^ 2 = 0) : M = 0 := by
  rw [RL_sq] at h
  ext i j
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg ‖M i j‖))).1 h i (Finset.mem_univ _)
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg ‖M i j‖)).1 h1 j (Finset.mem_univ _)
  simpa using h2

theorem lm_inj {v : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r} (hv : v ∈ Vs k r) (h : Lm k r v = 0) : v = 0 := by
  have hn := lm_norm hv
  rw [h, map_zero, norm_zero] at hn
  have h1 := sq_nonneg ‖RL (k := k) (r := r) v.1‖
  have h2 : 0 ≤ ∑ a : Fin r, ‖v.2.1 a‖ ^ 2 := Finset.sum_nonneg (fun a _ => sq_nonneg _)
  have h3 := sq_nonneg ‖RL (k := k) (r := r) v.2.2.1‖
  have h4 := sq_nonneg ‖RL (k := k) (r := r) v.2.2.2‖
  have e1 : ‖RL (k := k) (r := r) v.1‖ ^ 2 = 0 := by nlinarith
  have e2 : ∑ a : Fin r, ‖v.2.1 a‖ ^ 2 = 0 := by nlinarith
  have e3 : ‖RL (k := k) (r := r) v.2.2.1‖ ^ 2 = 0 := by nlinarith
  have e4 : ‖RL (k := k) (r := r) v.2.2.2‖ ^ 2 = 0 := by nlinarith
  have hx : v.2.1 = 0 := by
    funext a
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => sq_nonneg ‖v.2.1 a‖)).1 e2 a (Finset.mem_univ _)
    simpa using this
  exact Prod.ext (eq_zero_of_RL_lemma_3 _ e1)
    (Prod.ext hx (Prod.ext (eq_zero_of_RL_lemma_3 _ e3) (eq_zero_of_RL_lemma_3 _ e4)))

def lmEquiv (k r : ℕ) : ↥(Vs k r) ≃ₗ[ℝ] ↥(uH k r) :=
  LinearEquiv.ofBijective ((Lm k r).toLinearMap.restrict fun v hv => lm_mem hv)
    ⟨fun a b hab => by
      have h : Lm k r (a.1 - b.1) = 0 := by
        have := congrArg Subtype.val hab
        simp only [LinearMap.restrict_apply] at this
        rw [map_sub]; exact sub_eq_zero.2 this
      exact Subtype.ext (sub_eq_zero.1 (lm_inj ((Vs k r).sub_mem a.2 b.2) h)),
     fun y => by
      obtain ⟨v, hv, hvy⟩ := lm_surj y.2
      exact ⟨⟨v, hv⟩, Subtype.ext hvy⟩⟩

theorem dimG : Formalism.L2.SG.Pf.BH.DimG := by
  intro k r
  have eG : Module.finrank ℝ ↥(Formalism.MainNotions.S.lieE (UH (Hpk k r))) = Module.finrank ℝ ↥(uH k r) := by
    rw [lieE_G]; exact ((Submodule.equivMapOfInjective _ RL_injective (uH k r)).finrank_eq).symm
  have eN : Module.finrank ℝ ↥(Formalism.MainNotions.S.lieE (Nset k r)) = Module.finrank ℝ ↥(lieNS k r) := by
    rw [lieE_N]; exact ((Submodule.equivMapOfInjective _ RL_injective (lieNS k r)).finrank_eq).symm
  have eW : Module.finrank ℝ ↥(Formalism.MainNotions.S.lieE (Formalism.FourierDecayAlt.B2.UWb k r)) = Module.finrank ℝ ↥(uWb k r) := by
    rw [(lieWb' k r).2]; exact ((Submodule.equivMapOfInjective _ RL_injective (uWb k r)).finrank_eq).symm
  rw [eG, eN, eW, ← (lmEquiv k r).finrank_eq]
  unfold Vs
  rw [finrank_prodS, finrank_prodS, finrank_prodS, finrank_top, Module.finrank_pi_fintype]
  simp only [Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

end Formalism.L2.SG.Pf.BH.Sw
end
end

section

noncomputable section

open MeasureTheory Topology NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.RealObj.InfCut.ProductExactness

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sf_smul {β : Type*} [MeasurableSpace β] (μ : Measure β) [SigmaFinite μ] (c : ℝ≥0∞) (hc : c ≠ ∞) :
    SigmaFinite (c • μ) := by
  rw [← ENNReal.coe_toNNReal hc, ← ENNReal.smul_def]
  infer_instance

theorem ProdExact_holds : Formalism.L2.SG.Pf.NcReal.ProdExact := by
  classical
  intro D X u u' μN μN' μH μH' C hσN hσN' hσH hσH' hC hN hN' hH hH' hDis
  haveI : ∀ v, SigmaFinite (μN v) := hσN
  haveI : ∀ v, SigmaFinite (μN' v) := hσN'
  haveI : ∀ v, SigmaFinite (μH v) := hσH
  haveI : ∀ v, SigmaFinite (μH' v) := hσH'
  have hU : UnimodLoc := JL.rightInvS_of JL.setCorr_holds (JL.haarCorr_of JL.setCorr_holds)
  have hep : ∀ v a b, hJ (X.B.I.ε v) (eV X v a) (pV X v b) = if a = b then 1 else 0 := fun v a b =>
    (hJ_X X v _ _).trans (by rw [X.ef]; simp)
  have hpp : ∀ v a b, hJ (X.B.I.ε v) (pV X v a) (pV X v b) = 0 := fun v a b =>
    (hJ_X X v _ _).trans (by rw [X.ff]; simp)
  have hzp : ∀ w v b, hJ (X.B.I.ε v) (zV X w v) (pV X v b) = 0 := fun w v b => by
    have h0 : hJ (X.B.I.ε v) (pV X v b) (zV X w v) = 0 :=
      (hJ_X X v _ _).trans (by rw [(X.zu_orth w b).2]; simp)
    rw [hJ_cj, h0, map_zero]
  have hSH : ∀ w v, IsHaarS (SLoc (X.B.I.ε v) (eV X v) (zV X w v)) (muSv X w v) := fun w v =>
    NilradicalHermitianFrames.NH.NHLoc_holds _ _ _ _ _ _ _ _ _ _ (frameLoc_X X w u v) (hep v) (hpp v) (hzp w v) _ _
      (muNv_haar X w v) (muHv_haar X w v)

  have fN : ∀ (w : D.what₂.Word) (μ : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) [∀ v, SigmaFinite (μ v)],
      X.muN w = Measure.pi μ → ∀ v, ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ μ v = κ • muNv X w v := by
    intro w μ _ hw v
    obtain ⟨_, h0, hc, hi⟩ := X.muN_haar w
    rw [← NinfG_coe, hw] at hc hi
    rw [hw] at h0
    rw [NinfG, Subgroup.coe_pi] at hc
    exact PiM.factor_uniq μ (NGv X w) (fun v => NilradicalHermitianFrames.NH.NG_closed _ _ _) (muNv X w)
      (fun v => (muNv_haar X w v).1.2.2.1) (fun v => (muNv_haar X w v).1.2.2.2) (fun v => (muNv_haar X w v).1.2.1)
      h0 hc (fun g hg => hi g ((Subgroup.mem_pi _).2 fun v _ => hg v)) v
  have fH : ∀ (w : D.what₂.Word) (μ : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) [∀ v, SigmaFinite (μ v)],
      X.muH w = Measure.pi μ → ∀ v, ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ∞ ∧ μ v = κ • muHv X w v := by
    intro w μ _ hw v
    obtain ⟨_, h0, hc, hi⟩ := X.muH_haar w
    rw [← HinfG_coe, hw] at hc hi
    rw [hw] at h0
    rw [HinfG, Subgroup.coe_pi] at hc
    exact PiM.factor_uniq μ (HGv X w) (fun v => NilradicalHermitianFrames.NH.HG_closed _ _ _ _) (muHv X w)
      (fun v => (muHv_haar X w v).1.2.2.1) (fun v => (muHv_haar X w v).1.2.2.2) (fun v => (muHv_haar X w v).1.2.1)
      h0 hc (fun g hg => hi g ((Subgroup.mem_pi _).2 fun v _ => hg v)) v
  choose κN hκN0 hκNT hκN using fN u μN hN
  choose κN' hκN'0 hκN'T hκN' using fN u' μN' hN'
  choose κH hκH0 hκHT hκH using fH u μH hH
  choose κH' hκH'0 hκH'T hκH' using fH u' μH' hH'
  have hSL : ∀ v, Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v) = (κN v * κH v) • muSv X u v := fun v => by
    haveI : SigmaFinite (muHv X u v) := inferInstance
    unfold Formalism.L2.SG.Pf.NcReal.muSL muSv
    rw [hκN v, hκH v, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul]
    all_goals exact measurable_mul.aemeasurable
  have hSL' : ∀ v, Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v) = (κN' v * κH' v) • muSv X u' v := fun v => by
    unfold Formalism.L2.SG.Pf.NcReal.muSL muSv
    rw [hκN' v, hκH' v, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, Measure.map_smul]
    all_goals exact measurable_mul.aemeasurable
  haveI : ∀ w v, SigmaFinite (muSv X w v) := fun w v => (hSH w v).1.1
  haveI hσS : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v)) := fun v => by
    rw [hSL v]; exact sf_smul _ _ (ENNReal.mul_ne_top (hκNT v) (hκHT v))
  haveI hσS' : ∀ v, SigmaFinite (Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v)) := fun v => by
    rw [hSL' v]; exact sf_smul _ _ (ENNReal.mul_ne_top (hκN'T v) (hκH'T v))

  have hmS : ∀ (w : D.what₂.Word) (ρN ρH : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) [∀ v, SigmaFinite (ρN v)]
      [∀ v, SigmaFinite (ρH v)] [∀ v, SigmaFinite (Formalism.L2.SG.Pf.NcReal.muSL (ρH v) (ρN v))],
      X.muN w = Measure.pi ρN → X.muH w = Measure.pi ρH →
      muS X w = Measure.pi fun v => Formalism.L2.SG.Pf.NcReal.muSL (ρH v) (ρN v) := by
    intro w ρN ρH _ _ hσ h1 h2
    unfold muS
    rw [h1, h2]
    have mp := measurePreserving_piProd ρN ρH
    rw [← mp.map_eq, Measure.map_map (measurable_mul : Measurable fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2)
      mp.measurable]
    haveI : ∀ v, SigmaFinite (((ρN v).prod (ρH v)).map
        (fun q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v) => q.1 * q.2)) := hσ
    exact Measure.pi_map_pi (f := fun v (q : Formalism.REAL.UJ (X.B.I.ε v) × Formalism.REAL.UJ (X.B.I.ε v)) => q.1 * q.2)
      (fun v => measurable_mul.aemeasurable)
  have hmu := hmS u μN μH hN hH
  have hmu' := hmS u' μN' μH' hN' hH'

  have hsec := fun v => SecMeasLoc_holds _ _ _ _ _ _ _ _ _ 1 (frameLoc_X X u u' v) one_pos
  choose hs hsm hss using hsec
  have hloc : ∀ v, Formalism.REAL.muG (X.B.I.ε v) =
      ((nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v)).prod ((Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v)).prod
        (Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v)))).map (phiLoc (X.B.I.ε v) (hs v)) := fun v =>
    muG_eq_map _ _ _ _ _ _ _ (hsm v) _ (hDis v (hs v) (hss v))
  intro φ hφ
  have hpf := prod_formula (fun v => Formalism.REAL.muG (X.B.I.ε v)) (fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v))
    (fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v)) (fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v)) hs hsm hloc φ hφ
  change ∫⁻ x, φ x ∂(Measure.pi fun v => Formalism.REAL.muG (X.B.I.ε v)) = _
  rw [hpf]
  have hwm : ∀ v, Measurable fun c : Fin (D.R.rS + 1) → ℂ => ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') c) :=
    fun v => ENNReal.measurable_ofReal.comp (measurable_const.mul (wtLoc_cont D.R.k (Tw u) (Tw u')).measurable)
  have hν : Measure.pi (fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v)) =
      ((dcInf X).restrict (Good X u u')).withDensity
        (fun c => ∏ v, ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') (c v))) := by
    unfold nuLoc
    haveI : SigmaFinite (dcLoc (r := D.R.rS)) := by unfold dcLoc; infer_instance
    rw [PiM.pi_withDensity _ _ hwm (fun v x => ENNReal.ofReal_ne_top), ← Measure.restrict_pi_pi, good_eq]
    rfl
  set H : (Cinf X) → X.B.I.Ginf := fun c v => hs v (c v) with hHd
  have hHm : Measurable H := Measurable.of_eval fun v => (hsm v).comp (measurable_pi_apply v)
  set μP := Measure.pi fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH v) (μN v) with hμP
  set μP' := Measure.pi fun v => Formalism.L2.SG.Pf.NcReal.muSL (μH' v) (μN' v) with hμP'
  set Fc : Cinf X → ℝ≥0∞ := fun c => ∫⁻ s, ∫⁻ s', φ (s * H c * s'⁻¹) ∂μP' ∂μP with hFc
  have hFm : Measurable Fc := by
    have h1 : Measurable fun q : (Cinf X × X.B.I.Ginf) × X.B.I.Ginf => φ (q.1.2 * H q.1.1 * q.2⁻¹) :=
      hφ.comp (((measurable_snd.comp measurable_fst).mul (hHm.comp (measurable_fst.comp measurable_fst))).mul
        measurable_snd.inv)
    exact h1.lintegral_prod_right'.lintegral_prod_right'
  rw [show (∫⁻ c, ∫⁻ s, ∫⁻ s', φ (s * (fun v => hs v (c v)) * s'⁻¹) ∂μP' ∂μP
      ∂Measure.pi fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v)) = ∫⁻ c, Fc c
      ∂Measure.pi fun v => nuLoc (r := D.R.rS) D.R.k (Tw u) (Tw u') (C v) from rfl,
    hν, lintegral_withDensity_eq_lintegral_mul _
      (f := fun c : Cinf X => ∏ v, ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') (c v)))
      (Finset.measurable_prod _ fun v _ => (hwm v).comp (measurable_pi_apply v)) hFm]
  have hGm : MeasurableSet (Good X u u') := by
    rw [good_eq]; exact MeasurableSet.univ_pi fun v => measurableSet_goodLoc _ _
  refine setLIntegral_congr_fun hGm fun c hc => ?_
  simp only [Pi.mul_apply]
  have hcv : ∀ v, c v ∈ GoodLoc (r := D.R.rS) (Tw u) (Tw u') := fun v => by
    rw [good_eq, Set.mem_univ_pi] at hc; exact hc v
  have hW : ∏ v, ENNReal.ofReal (C v * wtLoc D.R.k (Tw u) (Tw u') (c v)) =
      ENNReal.ofReal ((∏ v, C v) * wt X u u' c) := by
    rw [← ENNReal.ofReal_prod_of_nonneg fun v _ => mul_nonneg (hC v).le (wtLoc_nonneg _ _ _ (hcv v)),
      Finset.prod_mul_distrib]
    rfl
  have hex := StepReal_holds D X u u' 1 one_pos c hc
  have hh : HasDiag X u u' 1 c (hOf X u u' 1 c) := by
    unfold hOf; rw [dite_eq_left hex]; exact hex.choose_spec
  have hdc := fun v => Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.DiagDCLoc_holds _ _ _ _ _ _ _ _ _ 1 (frameLoc_X X u u' v) (c v)
    (hcv v) (hs v (c v)) (hOf X u u' 1 c v) (hss v (c v) (hcv v)) (hh v)
  choose t ht t' ht' htt using hdc
  have hofe : hOf X u u' 1 c = t * H c * t'⁻¹ := funext fun v => htt v
  have hrt : μP.map (fun x => x * t) = μP :=
    PiM.pi_map_mul_right _ t fun v => by
      rw [hSL v, Measure.map_smul,
        hU _ _ _ _ _ _ _ _ _ (frameLoc_X X u u' v) _ (hSH u v) (t v) (ht v)]
      exact (measurable_id.mul measurable_const).aemeasurable
  have hrt' : μP'.map (fun x => x * t') = μP' :=
    PiM.pi_map_mul_right _ t' fun v => by
      rw [hSL' v, Measure.map_smul,
        hU _ _ _ _ _ _ _ _ _ (frameLoc_X X u' u v) _ (hSH u' v) (t' v) (ht' v)]
      exact (measurable_id.mul measurable_const).aemeasurable
  have hsw : ∫⁻ s, ∫⁻ s', φ (s * hOf X u u' 1 c * s'⁻¹) ∂μP' ∂μP = Fc c := by
    rw [hofe]; exact dc_switch _ _ φ hφ (H c) t t' hrt hrt'
  rw [hW, hmu, hmu', hsw]

end Formalism.L2.SG.RealObj.InfCut.ProductExactness
end
end
