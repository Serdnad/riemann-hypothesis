module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle229
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle211
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBPts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle223
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle212
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle232
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.PhiMulVec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXPbSuppHyp
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle200
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle230
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle024
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddGen
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle231
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle019
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ScalarCommuteTransposedRMatrixEntry
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKap
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LevelPointCoordinates

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.PBQ

theorem side1Pos_of (hC : CutOffStep) (hE : CutOffExists) (h0 : CutHB.Side0Pos) (hW : PartialBesselProperness.PbWords)
    (hPr : PBQ.ProperDomP) : CutHB.Side1Pos := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hj1 hF hw hγ hΩ t ht e
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  obtain ⟨Fc, hFc, hag⟩ := hE Wp Wq P p F j hj w h hh hF hw t ht e
  rw [hC Wp Wq P p F j hj w h hh γ hF hw hγ hΩ t ht e Fc hFc hag]
  rw [h0 Wp Wq P p Fc j hj [] h hh γ hj1 hFc ⟨fun a => a.elim0, fun a => a.elim0⟩ hγ hΩ (fun a => a.elim0) t ht0]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  show ellH h v (CutHB.phf p Fc j hj [] h hh.2 γ v (fun a => a.elim0) t) = ellH h v _
  congr 1
  have hpt := CutHB.pts Wp Wq P p j hj h hh γ hγ hΩ v
  have hyD := hpt.2 t ht0
  have hyG := x0_GV hj hpt.1 ht0 hγ

  obtain ⟨R, hR⟩ := hF.2.1
  set Cs : Set (B.Mat P.k P.r) := {g | B.gN g ≤ R} with hCs
  have hCc : IsCompact Cs := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le P.k P.r R
  have e' : j + (P.r - j) = P.r := by omega
  have hz : p.T.base.z = D.castV e' (liftVec P.k j (P.r - j) (p.T.bs j).z) := (p.T.z_lev j (by omega)).symm
  have hPW := hW P.k j (P.r - j) P.r Wp Wq (p.T.bs j) p.T.base e' hz (j + 1) hj F Cs (fun g hg _ => hF.1 g hg) hCc
    (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne))
    (domP P.k P.r j p.T.base.z p.T.base.z') (isOpen_domP _ _ _ _ _)
    (fun g hg => hg.1 ⟨j + 1, by omega⟩ (show j ≤ j + 1 by omega) (show j + 1 ≤ P.r by omega))
    (hPr Wp Wq P p j (by omega) Cs hCc) w e _ hyD hyG
  show pbT p j (by omega) Fc (x0 P.k P.r j hj (zxH h j hh.2 v) t γ) =
    D.uwG P.k P.r p.T.base.z p.T.base.z' (pbT p j (by omega) F) (j + 1) hj w e (x0 P.k P.r j hj (zxH h j hh.2 v) t γ)
  unfold pbT
  rw [hPW]
  have hDv : Dmin P.k P.r p.T.base.z p.T.base.z' (x0 P.k P.r j hj (zxH h j hh.2 v) t γ) ⟨j + 1, by omega⟩ = aVal h t := by
    rw [(CutHL.leading_minors_at_base_point P.k P.r j hj p.T.base.z p.T.base.z' (zxH h j hh.2 v) t γ hpt.1 ht0 hγ).2, zxH_det h j hh v]
    rfl
  exact pbT_agree P p j hj (aVal h t) Fc _ (fun g _ hg => hag g hg) _ hyG hDv

end Formalism.FourierDecayAlt.P.LevelPointCoordinates
end
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

theorem kap_Dw_emb (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    PI.UnitaryGroupMassFormula.GsFr.Dw k r * B2.embWb k r μ = B2.embWb k r μ * PI.UnitaryGroupMassFormula.GsFr.Dw k r := by
  ext i j
  simp only [PI.UnitaryGroupMassFormula.GsFr.Dw, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hi : TwoByOneBlock.mid k r i <;> by_cases hj : TwoByOneBlock.mid k r j
  · have hi' : (r ≤ i.val ∧ i.val ≤ r + k) := hi
    have hj' : (r ≤ j.val ∧ j.val ≤ r + k) := hj
    simp [hi', hj']
  · have hi' : (r ≤ i.val ∧ i.val ≤ r + k) := hi
    have hj' : ¬(r ≤ j.val ∧ j.val ≤ r + k) := hj
    have hij : i ≠ j := fun h => hj (h ▸ hi)
    rw [TwoByOneBlock.emb_out_col μ i j hj]
    simp [hi', hj', hij]
  · have hi' : ¬(r ≤ i.val ∧ i.val ≤ r + k) := hi
    have hj' : (r ≤ j.val ∧ j.val ≤ r + k) := hj
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [TwoByOneBlock.emb_out_row μ i j hi]
    simp [hi', hj', hij]
  · have hi' : ¬(r ≤ i.val ∧ i.val ≤ r + k) := hi
    have hj' : ¬(r ≤ j.val ∧ j.val ≤ r + k) := hj
    simp [hi', hj']

theorem wbP_mulVec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h : B.Mat k r}
    (hh : h ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    SSn.wbP k r (h *ᵥ v) = h *ᵥ SSn.wbP k r v := by
  obtain ⟨η, -, -, rfl⟩ := (TwoByOneBlock.UWset_iff hz h).1 hh
  have e : ∀ w, SSn.wbP k r w = PI.UnitaryGroupMassFormula.GsFr.Dw k r *ᵥ w := fun w => by
    rw [PI.UnitaryGroupMassFormula.GsFr.Dw_mulVec]; rfl
  rw [e, e, Matrix.mulVec_mulVec, kap_Dw_emb, ← Matrix.mulVec_mulVec]

theorem kap_prWv_mulVec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h : B.Mat k r}
    (hh : h ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    SSn.prWv k r z (h *ᵥ v) = h *ᵥ SSn.prWv k r z v := by
  have hz' : h *ᵥ z = z := hh.2.2
  have hherm : herm (Hpk k r) (h *ᵥ SSn.wbP k r v) z = herm (Hpk k r) (SSn.wbP k r v) z := by
    conv_lhs => rw [← hz']
    exact Formalism.FourierDecayAlt.P.Qx2.herm_uh hh.1 _ _
  unfold SSn.prWv
  rw [wbP_mulVec hz hh, Matrix.mulVec_add, Matrix.mulVec_smul, hz', hherm]

theorem kap_nrmW_mulVec {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h : B.Mat k r}
    (hh : h ∈ UWset k r z) (a : Fin (2 * r + k + 1) → ℂ) :
    PRho.nrmW k r z (h *ᵥ a) = PRho.nrmW k r z a := by
  unfold PRho.nrmW
  rw [kap_prWv_mulVec hz hh, Formalism.FourierDecayAlt.P.Qx2.herm_uh hh.1]

theorem kap_mulVec_contDiff {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a : Fin n → ℂ => M *ᵥ a) := by
  have h := ((LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)).contDiff
    (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).restrict_scalars ℝ
  convert h using 1
  funext a
  rfl

theorem kap_herm_contDiff {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun u : Fin n → ℂ => herm H u u) := by
  have hconj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (starRingEnd ℂ) := Complex.conjCLE.contDiff
  have e : (fun u : Fin n → ℂ => herm H u u) = fun u => ∑ i, starRingEnd ℂ (u i) * (H *ᵥ u) i := by
    funext u; simp [herm, dotProduct, Complex.star_def]
  rw [e]
  refine ContDiff.sum fun i _ => ?_
  exact (hconj.comp (contDiff_apply ℝ (fun _ => ℂ) i)).mul ((contDiff_apply ℝ (fun _ => ℂ) i).comp (kap_mulVec_contDiff H))

theorem kap_nrmW_contDiff (z : Fin (2 * r + k + 1) → ℂ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun a => PRho.nrmW k r z a) := by
  have e : (fun a => PRho.nrmW k r z a) =
      fun a => (herm (Hpk k r) (PI.UnitaryGroupMassFormula.GsFr.Pm k r z *ᵥ a) (PI.UnitaryGroupMassFormula.GsFr.Pm k r z *ᵥ a)).re := by
    funext a; unfold PRho.nrmW; rw [PI.UnitaryGroupMassFormula.GsFr.Pm_mulVec]; rfl
  rw [e]
  exact Complex.reCLM.contDiff.comp ((kap_herm_contDiff (Hpk k r)).comp (kap_mulVec_contDiff _))

theorem weighted_norm_facts_hold : NrmWFacts := fun k r z hz _ =>
  ⟨kap_nrmW_contDiff z, fun _ hh a => kap_nrmW_mulVec hz hh a⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

section

open Matrix MeasureTheory Filter Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutEXPbSupp

theorem hpk_zero (k : ℕ) : Hpk k 0 = diagonal (dS (2 * 0 + k)) := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, diagonal_apply, dS, Fin.ext_iff, Fin.val_last]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem tz_sum (k : ℕ) (z : Fin (2 * 0 + k + 1) → ℂ) :
    ∑ i : Fin (2 * 0 + k), ‖z i.castSucc‖ ^ 2 = ‖z (Fin.last _)‖ ^ 2 - Tz k 0 z := by
  have e : ∀ w : ℂ, (starRingEnd ℂ w * w).re = ‖w‖ ^ 2 := by
    intro w
    rw [Complex.conj_mul']
    norm_cast
  unfold Tz herm
  rw [hpk_zero]
  simp only [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_castSucc, Pi.star_apply, Complex.star_def]
  have h1 : ∀ i : Fin (2 * 0 + k), dS (2 * 0 + k) i.castSucc = 1 := fun i => by
    unfold dS
    rw [if_neg (Fin.castSucc_lt_last i).ne]
  have h2 : dS (2 * 0 + k) (Fin.last (2 * 0 + k)) = -1 := by
    unfold dS
    rw [if_pos rfl]
  simp only [h1, h2, one_mul, neg_one_mul, mul_neg, Complex.add_re, Complex.neg_re, Complex.re_sum, e]
  ring

theorem gf_eq_GGl (k ρ : ℕ) (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (g : B.Mat k ρ) :
    Gf k ρ z z' g = Q.GGl k ρ z z' g := by
  subst hρ
  unfold Gf Q.GGl Dmin
  rw [Matrix.det_fin_zero, Matrix.det_fin_one]
  simp only [Complex.normSq_one, mul_one]
  rfl

theorem mu_bound (k ρ : ℕ) (hρ : ρ = 0) (z z' : Fin (2 * ρ + k + 1) → ℂ) (hT : 0 < Tz k ρ z) (hT' : 0 < Tz k ρ z')
    (μ : B.Mat k ρ) (hμ : μ ∈ Q.Glev k ρ (Fin.last ρ)) (i j : Fin (2 * ρ + k + 1)) :
    ‖μ i j‖ * (Tz k ρ z * Tz k ρ z') ≤ 4 * ‖z ⟨2 * ρ + k, by omega⟩‖ * ‖z' ⟨2 * ρ + k, by omega⟩‖ *
      ‖Q.zetaL k ρ z z' (Fin.last ρ) μ‖ := by
  subst hρ
  have hU : μᴴ * diagonal (dS (2 * 0 + k)) * μ = diagonal (dS (2 * 0 + k)) := by
    have h := hμ.1
    rw [hpk_zero] at h
    exact h
  have hζ : Q.zetaL k 0 z z' (Fin.last 0) μ = star z ⬝ᵥ (diagonal (dS (2 * 0 + k)) *ᵥ (μ *ᵥ z')) := by
    unfold Q.zetaL herm
    rw [hpk_zero]
    simp [fvec]
  rw [hζ]
  exact entry_bound μ hU z z' _ _ hT hT' (tz_sum k z) (tz_sum k z') i j

end Formalism.FourierDecayAlt.P.CutEXPbSupp

namespace Formalism.FourierDecayAlt.P

open CutEX CutEXPbSupp

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem pullback_support : CutEX.PbSupp := by
  intro Wp Wq _ _ _ _ _ _ P p G hG
  obtain ⟨⟨_, ⟨R, hR⟩, ⟨ε, hε, hεG⟩⟩, K0, hK0c, h0K0, hK0⟩ := hG

  obtain ⟨δ, hδ, hδK⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ w ∈ K0, δ ≤ ‖w‖ := by
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hK0c.isClosed.isOpen_compl 0 h0K0
    refine ⟨δ, hδ, fun w hw => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hball (by simpa [Metric.mem_ball, dist_zero_right] using hlt) hw

  obtain ⟨M1, hM1⟩ := hK0c.isBounded.exists_norm_le
  set M0 : ℝ := max M1 1 with hM0
  have hM0pos : 0 < M0 := lt_of_lt_of_le one_pos (le_max_right _ _)

  set SR : Set (B.Mat P.k P.r) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R
    with hSRdef
  have hSR : IsCompact SR := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  obtain ⟨Cg, hCg⟩ := hSR.exists_bound_of_continuousOn
    (f := fun g : B.Mat P.k P.r => Gf P.k P.r p.T.base.z p.T.base.z' g)
    (Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf p.T.base.z p.T.base.z').continuous.continuousOn

  set zr := (p.T.bs P.r).z with hzr
  set zr' := (p.T.bs P.r).z' with hzr'
  have hT : 0 < Tz P.k (P.r - P.r) zr := (p.T.bs P.r).T_pos
  have hT' : 0 < Tz P.k (P.r - P.r) zr' := (p.T.bs P.r).T'_pos
  set TT : ℝ := Tz P.k (P.r - P.r) zr * Tz P.k (P.r - P.r) zr' with hTT
  have hTTpos : 0 < TT := mul_pos hT hT'
  set Zb : ℝ := Real.sqrt (Cg / δ ^ 2 + TT) with hZb
  set Bμ : ℝ := 4 * ‖zr ⟨2 * (P.r - P.r) + P.k, by omega⟩‖ * ‖zr' ⟨2 * (P.r - P.r) + P.k, by omega⟩‖ * Zb / TT
    with hBμ
  set c : ℝ := ε / M0 ^ 2 with hc
  have hcpos : 0 < c := div_pos hε (by positivity)
  set Bset : Set (Mt P.k (P.r - P.r)) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) Bμ with hBset
  set Aset : Set (Fin P.r → Fin P.r → ℂ) :=
    Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R with hAset
  have hA : IsCompact Aset := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hB : IsCompact Bset := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine ⟨(Aset ×ˢ Bset) ∩ ((fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.1).det) ⁻¹' K0) ∩
      ((fun q : (Fin P.r → Fin P.r → ℂ) × Mt P.k (P.r - P.r) => (Matrix.of q.2 : B.Mat P.k (P.r - P.r))) ⁻¹'
        Q.Glev P.k (P.r - P.r) (Fin.last _)) ∩
      {q | c ≤ Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2)}, ?_, ?_, ?_⟩
  · refine (((hA.prod hB).inter_right ?_).inter_right ?_).inter_right ?_
    · exact hK0c.isClosed.preimage (Continuous.matrix_det continuous_fst)
    · exact (Formalism.FourierDecayAlt.P.JCTx5.glev_closed _ _ _).preimage continuous_snd
    · exact isClosed_le continuous_const ((Formalism.FourierDecayAlt.P.Qx8.GGl_cont _ _ _ _).comp continuous_snd)
  · rintro q ⟨⟨⟨_, hq1⟩, _⟩, hq3⟩
    refine ⟨fun h0 => h0K0 ?_, lt_of_lt_of_le hcpos hq3⟩
    have : (Matrix.of q.1).det ∈ K0 := hq1
    rwa [h0] at this
  · intro q hdet hμ hpb
    obtain ⟨g, hg, hGg, u, hu, hb, hD, hGf⟩ := CutEXPbSupp.orbit_point p G (Matrix.of q.1) (Matrix.of q.2) hdet hμ hpb
    have hgR : B.gN g ≤ R := hR g hg hGg
    have hDK : (Matrix.of q.1).det ∈ K0 := hD ▸ hK0 g hg hGg
    have hdetδ : δ ≤ ‖(Matrix.of q.1).det‖ := hδK _ hDK
    have hdetM : ‖(Matrix.of q.1).det‖ ≤ M0 := (hM1 _ hDK).trans (le_max_left _ _)
    have hGε : ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g := hεG g hg hGg
    have hgSR : g ∈ SR := by
      rw [hSRdef]
      exact fun a _ b _ => by
        rw [Metric.mem_closedBall, dist_zero_right]; exact (CutEXPbSupp.norm_entry_le_gN g a b).trans hgR
    have hGC : Gf P.k P.r p.T.base.z p.T.base.z' g ≤ Cg := (le_abs_self _).trans (hCg g hgSR)
    set Gr := Gf P.k (P.r - P.r) zr zr' (Matrix.of q.2) with hGr
    have hns : Complex.normSq (Matrix.of q.1).det = ‖(Matrix.of q.1).det‖ ^ 2 := Complex.normSq_eq_norm_sq _
    have hGr_pos : 0 < Gr := by
      by_contra hle
      push Not at hle
      have : Gf P.k P.r p.T.base.z p.T.base.z' g ≤ 0 := by
        rw [hGf]; exact mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hle
      linarith
    have hGGl : Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2) = Gr :=
      (CutEXPbSupp.gf_eq_GGl P.k (P.r - P.r) (Nat.sub_self _) zr zr' _).symm
    have hδ2 : δ ^ 2 ≤ Complex.normSq (Matrix.of q.1).det := by
      rw [hns]; exact pow_le_pow_left₀ hδ.le hdetδ 2
    have hM2 : Complex.normSq (Matrix.of q.1).det ≤ M0 ^ 2 := by
      rw [hns]; exact pow_le_pow_left₀ (norm_nonneg _) hdetM 2
    have hGr_up : Gr ≤ Cg / δ ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      calc Gr * δ ^ 2 ≤ Gr * Complex.normSq (Matrix.of q.1).det := mul_le_mul_of_nonneg_left hδ2 hGr_pos.le
        _ = Gf P.k P.r p.T.base.z p.T.base.z' g := by rw [hGf, mul_comm]
        _ ≤ Cg := hGC
    have hGr_lo : c ≤ Gr := by
      rw [hc, div_le_iff₀ (by positivity)]
      calc ε ≤ Gf P.k P.r p.T.base.z p.T.base.z' g := hGε
        _ = Complex.normSq (Matrix.of q.1).det * Gr := hGf
        _ ≤ M0 ^ 2 * Gr := mul_le_mul_of_nonneg_right hM2 hGr_pos.le
        _ = Gr * M0 ^ 2 := mul_comm _ _
    have hζ : ‖Q.zetaL P.k (P.r - P.r) zr zr' (Fin.last _) (Matrix.of q.2)‖ ≤ Zb := by
      rw [Complex.norm_def, hZb]
      refine Real.sqrt_le_sqrt ?_
      have e : Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2) =
          Complex.normSq (Q.zetaL P.k (P.r - P.r) zr zr' (Fin.last _) (Matrix.of q.2)) - TT := rfl
      linarith
    refine ⟨u, hu, ⟨⟨⟨?_, ?_⟩, hμ⟩, ?_⟩⟩
    · refine ⟨?_, ?_⟩
      · simp only [hAset, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
        exact fun a b => (hb a b).trans hgR
      · simp only [hBset, Set.mem_univ_pi, Metric.mem_closedBall, dist_zero_right]
        intro a b
        have hm := CutEXPbSupp.mu_bound P.k (P.r - P.r) (Nat.sub_self _) zr zr' hT hT' (Matrix.of q.2) hμ a b
        rw [hBμ, le_div_iff₀ hTTpos]
        refine hm.trans ?_
        exact mul_le_mul_of_nonneg_left hζ (by positivity)
    · show (Matrix.of (Matrix.of.symm (Matrix.of q.1 * u))).det ∈ K0
      rw [Equiv.apply_symm_apply, Matrix.det_mul, Formalism.DoubleCosetMeasures.isUpUni_det ℂ hu, mul_one]
      exact hDK
    · show c ≤ Q.GGl P.k (P.r - P.r) zr zr' (Matrix.of q.2)
      rw [hGGl]; exact hGr_lo

end Formalism.FourierDecayAlt.P
end
end

section

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn

theorem sSnRealiser_of (hCh : ChainBd) (hG : SSnGeom) (hR : SSnRep) : SSnRealiser :=
  sSnAssemble_of (JA.datumCompose_of (JA.datumBd_of_chain hCh)) hG hR

theorem jABddSSnQQ_of_leaves (hCh : ChainBd) (hG : SSnGeom) (hR : SSnRep) : JABddSSnQQ :=
  jABddSSnQQ_of real_to_bounded_holds (sSnRealiser_of hCh hG hR)

theorem jABddSSnStarQQ_of_leaves (hCh : ChainBd) (hG : SSnGeom) (hR : SSnRep) : JABddSSnStarQQ :=
  jABddSSnStarQQ_of real_to_bounded_holds (sSnRealiser_of hCh hG hR)

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn
end

section

open Matrix Formalism.FourierDecayAlt.Wd

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

namespace IbTInvPf

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem plus_inv (σ : Site A) (hW : YangianSpanCharacter.T.WeylRel σ.p σ.c σ.ci) (Y : K) (hY : star Y = Y) :
    (!![0, -star σ.ci; star σ.c, algebraMap K A (Y + 1) + star σ.p] : M2 A) * (Ts σ Y)ᴴ = 1 := by
  have hs := congrArg star hW.2.2
  simp only [star_mul, star_add] at hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ts, YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · rw [← star_mul, hW.1, star_one]
  · rw [← algebraMap_star_comm, hY, mul_add, add_mul, add_mul, one_mul, hs, Algebra.commutes]
    abel
  · rw [← star_mul, hW.2.1, star_one]

theorem minus_inv (σ : Site A) (hW : YangianSpanCharacter.T.WeylRel σ.p σ.c σ.ci) (Y : K) :
    (!![0, -σ.ci; σ.c, algebraMap K A (Y - 1) + σ.p] : M2 A) * ((Ts σ Y).map star)ᴴ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Ts, YangianSpanCharacter.T.Tm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
  · exact hW.2.1
  · rw [mul_add, add_mul, sub_mul, one_mul, hW.2.2, Algebra.commutes]
    abel
  · exact hW.1

theorem lift_zero_one : (lift0 (1 : M2 A) : M2 (SlopeTestRemainingChoices S A)) = 1 := by
  unfold lift0
  ext i j
  rw [Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp [io]

theorem ivlet_mul_star (σ : Site A) (hW : YangianSpanCharacter.T.WeylRel σ.p σ.c σ.ci) (l : Letter K S)
    (hl : star l.pt = l.pt) : ivlet σ l * star (vlet σ l) = 1 := by
  unfold ivlet vlet
  rw [Formalism.FourierDecayAlt.P.Wd1.ins_star _ _ (Formalism.FourierDecayAlt.P.Wd7.freeOf2_lift _ _),
    ← Formalism.FourierDecayAlt.P.Wd1.ins_mul _ _ _ (Formalism.FourierDecayAlt.P.Wd7.freeOf2_lift _ _), Formalism.FourierDecayAlt.P.Wd7.liftMatrix_conjTranspose,
    ← Formalism.FourierDecayAlt.P.Wd7.lift_reduction_mul]
  cases hpl : l.plus
  · simp only [Bool.false_eq_true, ite_false]
    rw [minus_inv σ hW l.pt, lift_zero_one, Formalism.FourierDecayAlt.P.Wd1.ins_one]
  · simp only [ite_true]
    rw [plus_inv σ hW l.pt hl, lift_zero_one, Formalism.FourierDecayAlt.P.Wd1.ins_one]

theorem ibT_mul_star (σ : Site A) (hσ : IsSite σ) :
    ∀ w : List (Letter K S), (∀ l ∈ w, star l.pt = l.pt) → ibT σ w * star (bT σ w) = 1
  | [], _ => by simp [ibT, bT]
  | l :: w, h => by
    have hw := ibT_mul_star σ hσ w (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    rw [ibT, bT, star_mul, mul_assoc, ← mul_assoc (ibT σ w), hw, one_mul,
      ivlet_mul_star σ hσ.1 l (h l (by simp))]

end IbTInvPf

theorem boundary_torus_invariance : IbTInv := by
  intro K A S _ _ _ _ _ _ _ _ σ w hσ hw
  exact IbTInvPf.ibT_mul_star σ hσ w hw

end Formalism.FourierDecayAlt.P.CutSE
end
end
