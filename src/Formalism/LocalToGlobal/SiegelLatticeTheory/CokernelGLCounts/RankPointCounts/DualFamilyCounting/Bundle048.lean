module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InvMulOfUnitri
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibLatB
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle041
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle046
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle039
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationInvarianceEverySetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.MulVecMapMem
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle038
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeLemma3
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPfA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.FinEnum
import Mathlib.Data.NNRat.Floor
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
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NOfibAlg

@[expose] public section

section

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

theorem nofibLat_of_rest (hL : DictLat) (hE : DictEx) (hF : FibQ) (hO : FibOnto) : NOfibLat := by
  have hR : NOratC := by first | exact @noratC_holds | exact @noratC_proved | exact @noratC | exact @nOratC_holds | exact @noratC_of | exact @NOratC_holds
  have hG : DictGram := by first | exact @dictGram_holds | exact @dictGram_proved | exact @dictGram | exact @DictGram_holds | exact @dictGram_of
  have hP : DictPlace := by first | exact @dictionary_place_holds | exact @dictPlace_holds | exact @dictPlace_proved | exact @dictPlace | exact @DictPlace_holds | exact @dictPlace_of
  exact @nofibLat_of hR hG hL hE hP hF hO

theorem nofib_of_rest (hL : DictLat) (hE : DictEx) (hF : FibQ) (hO : FibOnto) : NOfib := @Formalism.L2.SG.Pf.NcReal.JX.nofib_of (@nofibLat_of_rest hL hE hF hO)

theorem nOfib_of_dict_fib (hB : DictLatB) (hF : FibQ) (hO : FibOnto) : NOfib := by
  have hLF : DictLatF := by first | exact @dictLatF_proof | exact @dictLatF_holds | exact @dictLatF_proved | exact @dictLatF | exact @DictLatF_holds | exact @dictLatF_of
  have hL : DictLat := @dictLat_of hLF hB
  have hE : DictEx := @Ex.dictEx_holds
  exact @nofib_of_rest hL hE hF hO

theorem nofib_of_fib (hF : FibQ) (hO : FibOnto) : NOfib := by
  have hB : DictLatB := by first | exact @dictLatB_proof | exact @dictLatB_holds | exact @dictLatB_proved | exact @dictLatB | exact @DictLatB_holds | exact @dictLatB_of
  exact @nOfib_of_dict_fib hB hF hO

theorem nofib_of_fibQ (hF : FibQ) : NOfib := by
  have hO : FibOnto := by first | exact @fibOnto_proof | exact @fibOnto_holds | exact @fibOnto_proved | exact @fibOnto | exact @FibOnto_holds | exact @fibOnto_of
  exact @nofib_of_fib hF hO

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

theorem embQ (hF : IsFrameJ ε e f wf z0) :
    MeasurableEmbedding (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) :=
  cM_measEmb (ε := ε) (A := Qi ε e f wf z0) (B := Qm e f wf z0) (A' := Qm e f wf z0) (B' := Qi ε e f wf z0)
    (Qm_mul_Qi hF) (Qm_mul_Qi hF)

theorem Qm_e (a : Fin r) : Qm e f wf z0 *ᵥ bvec (eI k r a) = e a := by rw [Qm_mulVec_bvec, colQ_eI]

theorem Qm_f (a : Fin r) : Qm e f wf z0 *ᵥ bvec (esI k r a) = f a := by rw [Qm_mulVec_bvec, colQ_esI]

theorem conj_fix (hF : IsFrameJ ε e f wf z0) {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {v : Fin (2 * r + k + 1) → ℂ} (hv : s *ᵥ v = v) :
    (Qm e f wf z0 * s * Qi ε e f wf z0) *ᵥ (Qm e f wf z0 *ᵥ v) = Qm e f wf z0 *ᵥ v := by
  rw [Matrix.mulVec_mulVec]
  have e1 : Qm e f wf z0 * s * Qi ε e f wf z0 * Qm e f wf z0 = Qm e f wf z0 * s := by
    rw [Matrix.mul_assoc (Qm e f wf z0 * s), Qi_mul_Qm hF, Matrix.mul_one]
  rw [e1, ← Matrix.mulVec_mulVec, hv]

theorem measW_of (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} {μH : Measure (Formalism.REAL.UJ ε)}
    (hH : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB)) μH) :
    Formalism.MainNotions.S.IsHaarOn (UWset k r zB) (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) := by
  have emb := embQ hF
  obtain ⟨hsf, hne, hcon, hinv⟩ := hH
  haveI := hsf
  refine ⟨emb.sigmaFinite_map, (Measure.map_ne_zero_iff emb.measurable.aemeasurable).mpr hne, ?_, ?_⟩
  · rw [emb.map_apply]
    refine measure_mono_null (fun g hg => ?_) hcon
    intro hgH
    apply hg
    exact conj_mem_UWset hF rfl (uMat_mem g) (fun a => (hgH.1 a).1) (fun a => (hgH.1 a).2) hgH.2
  · intro s hs
    have ht := conjQ_UJ hF hs.1
    set t := toUJ (Qm e f wf z0 * s * Qi ε e f wf z0) ht
    have htH : t ∈ Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB) := by
      show (∀ a, uMat t *ᵥ e a = e a ∧ uMat t *ᵥ f a = f a) ∧ uMat t *ᵥ (Qm e f wf z0 *ᵥ zB) = Qm e f wf z0 *ᵥ zB
      rw [uMat_toUJ]
      refine ⟨fun a => ⟨?_, ?_⟩, conj_fix hF hs.2.2⟩
      · rw [← Qm_e (e := e) (f := f) (wf := wf) (z0 := z0) a]; exact conj_fix hF (hs.2.1 a).1
      · rw [← Qm_f (e := e) (f := f) (wf := wf) (z0 := z0) a]; exact conj_fix hF (hs.2.1 a).2
    rw [Measure.map_map (measurable_lmulM s) emb.measurable]
    have hfun : lmulM s ∘ cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) =
        cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) ∘ (fun g : Formalism.REAL.UJ ε => t * g) := by
      funext g
      simp only [Function.comp, lmulM_cM]
      unfold cM
      rw [uMat_mul, uMat_toUJ]
      simp only [← Matrix.mul_assoc, Qi_mul_Qm hF, Matrix.one_mul]
      try rfl
    rw [hfun, ← Measure.map_map emb.measurable (measurable_const_mul t), hinv t htH]

theorem measN_of (hF : IsFrameJ ε e f wf z0) (κ : ℝ) :
    (ENNReal.ofReal κ • refN ε e f wf z0).map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) =
      Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ) := by
  have emb := embQ hF
  rw [Measure.map_smul _ emb.measurable.aemeasurable, refN, emb.map_comap, Jac.haarLie_eq_smul (Nset k r) (ENNReal.ofReal κ)]
  congr 1
  refine Measure.restrict_eq_self_of_ae_mem ?_
  have hc : (Formalism.MainNotions.S.haarLie (Nset k r) 1) {x | Matrix.of x ∉ Nset k r} = 0 := Jac.nilradical_measure_is_haar.2.2.1
  refine ae_iff.2 (measure_mono_null (fun x hx => ?_) hc)
  simp only [Set.mem_setOf_eq] at hx ⊢
  intro hxN
  apply hx
  have hU := conjQ_UJ hF hxN.1
  refine ⟨toUJ _ hU, ?_⟩
  show Qi ε e f wf z0 * uMat (toUJ _ hU) * Qm e f wf z0 = x
  rw [uMat_toUJ, Qi_Qm_conj hF]
  rfl

theorem haarN_of (κ : ℝ) (hκ : 0 < κ) : Formalism.MainNotions.S.IsHaarOn (Nset k r) (Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ)) :=
  Formalism.MainNotions.BridgeCSB.haarLieN k r _ (ENNReal.ofReal_pos.2 hκ).ne' ENNReal.ofReal_ne_top

theorem psi_mul (hF : IsFrameJ ε e f wf z0) (n h : Formalism.REAL.UJ ε) :
    cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) (n * h) =
      Jac.mm (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) n) (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) h) :=
  (cM_comp_mul hF (Qm e f wf z0) n h).symm

theorem measS_of (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r zB)
    (hT : 0 < Tz k r zB) {μH : Measure (Formalism.REAL.UJ ε)} (hH : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB)) μH)
    (κ : ℝ) (hκ : 0 < κ) :
    (muSL μH (ENNReal.ofReal κ • refN ε e f wf z0)).map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) =
      Formalism.MainNotions.S.muS (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)))
        (Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ)) := by
  have emb := embQ hF
  have hW := measW_of hF hH
  have hN := haarN_of (k := k) (r := r) κ hκ
  set Ψ := cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) with hΨ
  set μW := μH.map Ψ with hμW
  set μN := Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ) with hμN
  set μN' := ENNReal.ofReal κ • refN ε e f wf z0 with hμN'
  haveI : SigmaFinite μH := hH.1
  haveI : SigmaFinite μW := hW.1
  haveI : SigmaFinite μN := hN.1
  have hNmap : μN'.map Ψ = μN := measN_of hF κ
  have hWB : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 k r _ hN
  apply Measure.ext_of_lintegral
  intro g hg
  have hgm : Measurable fun p : Mt k r × Mt k r => g (Jac.mm p.1 p.2) := hg.comp Jac.measurable_mt_mul
  rw [Jac.lintegral_muS μW μN hg, lintegral_map hg emb.measurable]
  have hmul : Measurable fun p : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε => p.1 * p.2 := measurable_mul
  have hgΨ : Measurable fun a : Formalism.REAL.UJ ε => g (Ψ a) := hg.comp emb.measurable
  rw [show muSL μH μN' = (μN'.prod μH).map (fun p => p.1 * p.2) from rfl,
    lintegral_map hgΨ hmul,
    lintegral_prod (fun p : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε => g (Ψ (p.1 * p.2))) (hgΨ.comp hmul).aemeasurable]
  have hpm : ∀ n h : Formalism.REAL.UJ ε, Ψ (n * h) = Jac.mm (Ψ n) (Ψ h) := psi_mul hF
  simp only [hpm]
  have step1 : ∀ n : Formalism.REAL.UJ ε, ∫⁻ h, g (Jac.mm (Ψ n) (Ψ h)) ∂μH = ∫⁻ y, g (Jac.mm (Ψ n) y) ∂μW := by
    intro n
    rw [hμW, emb.lintegral_map]
  simp_rw [step1]
  rw [← emb.lintegral_map (μ := μN') (f := fun x => ∫⁻ y, g (Jac.mm x y) ∂μW), hNmap]
  rw [lintegral_lintegral_swap (f := fun x y => g (Jac.mm x y)) hgm.aemeasurable]

  have hconc : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r zB := by
    have h0 : μW {x | Matrix.of x ∉ UWset k r zB} = 0 := hW.2.2.1
    exact ae_iff.2 h0
  refine lintegral_congr_ae ?_
  filter_upwards [hconc] with h hh
  have hd : IsUnit (Matrix.of h).det := JL.RI.det_unit_of_UH hh.1
  have hhi : (Matrix.of h)⁻¹ ∈ UWset k r zB := JL.RI.inv_mem_UW hh
  have hc : μN.map (conjM (k := k) (r := r) (Matrix.of h)⁻¹) = μN :=
    Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r zB μN hz hT hWB _ hhi
  conv_rhs => rw [← hc]
  have hmh : Measurable fun n : Mt k r => g (Jac.mm h n) := hgm.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_map hmh (Jac.meas_conjM _)]
  refine lintegral_congr fun x => ?_
  congr 1
  show Jac.mm x h = Jac.mm h (conjM (Matrix.of h)⁻¹ x)
  funext i j
  show (Matrix.of x * Matrix.of h) i j = (Matrix.of h * ((Matrix.of h)⁻¹ * Matrix.of x * ((Matrix.of h)⁻¹)⁻¹)) i j
  rw [Matrix.nonsing_inv_nonsing_inv _ hd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
    Matrix.one_mul]

theorem haarW_B (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r zB) (hT : 0 < Tz k r zB)
    {μH : Measure (Formalism.REAL.UJ ε)} (hH : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB)) μH)
    (hfin : μH Set.univ ≠ ⊤) :
    Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r zB) (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) := by
  have emb := embQ hF
  have hW := measW_of hF hH
  obtain ⟨μ0, h0⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r zB hz hT
  have hνfin : ∀ K, (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) K < ⊤ := fun K =>
    lt_of_le_of_lt (measure_mono (Set.subset_univ K)) (by rw [emb.map_apply, Set.preimage_univ]; exact hfin.lt_top)
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r (UWset k r zB) μ0 _ (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r zB) h0
    hW.2.2.1 hW.2.2.2 (fun K _ => hνfin K)
  exact ⟨hW.2.2.1, hW.2.2.2, fun a ha => by rw [hc, Measure.map_smul _ (JL.RI.meas_rmul a).aemeasurable, h0.right a ha], fun K _ => hνfin K, hW.2.1⟩

theorem rightX_of (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r zB)
    (hT : 0 < Tz k r zB) {μH : Measure (Formalism.REAL.UJ ε)}
    (hH : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB)) μH) (hfin : μH Set.univ ≠ ⊤)
    (κ : ℝ) (hκ : 0 < κ) (s : Formalism.REAL.UJ ε) (hs : s ∈ SLoc ε e (Qm e f wf z0 *ᵥ zB)) :
    (muSL μH (ENNReal.ofReal κ • refN ε e f wf z0)).map (fun x => x * s) =
      muSL μH (ENNReal.ofReal κ • refN ε e f wf z0) := by
  have emb := embQ hF
  set Ψ := cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) with hΨ
  set μS := muSL μH (ENNReal.ofReal κ • refN ε e f wf z0) with hμS
  have hN := haarN_of (k := k) (r := r) κ hκ
  have hWB := haarW_B hF hz hT hH hfin
  have hNB : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) (Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ)) :=
    Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 k r _ hN
  have hQinv : (Qm e f wf z0)⁻¹ = Qi ε e f wf z0 := Matrix.inv_eq_left_inv (Qi_mul_Qm hF)
  have hdet : IsUnit (Qm e f wf z0).det := Matrix.isUnit_det_of_left_inverse (Qi_mul_Qm hF)
  set sM : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Qi ε e f wf z0 * uMat s * Qm e f wf z0 with hsM
  have hSs : sM ∈ Sset k r zB := by
    have := (JL.setCorr_holds r k ε e (Qm e f wf z0 *ᵥ zB) zB (Qm e f wf z0) (gramQ hF) hdet
      (fun a => Qm_e (f := f) (wf := wf) (z0 := z0) a) hz rfl hT s).1 hs
    rw [hQinv] at this
    exact this
  have hmeas : Measurable fun x : Formalism.REAL.UJ ε => x * s := measurable_mul_const s
  have hfun : Ψ ∘ (fun x => x * s) = Formalism.FourierDecayAlt.B.rmulF sM ∘ Ψ := by
    funext x
    show (Qi ε e f wf z0 * uMat (x * s) * Qm e f wf z0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
      (Qi ε e f wf z0 * uMat x * Qm e f wf z0) * (Qi ε e f wf z0 * uMat s * Qm e f wf z0)
    rw [uMat_mul]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (Qi ε e f wf z0 * uMat x) (Qm e f wf z0) (Qi ε e f wf z0), Qm_mul_Qi hF, Matrix.mul_one]
  have key : (μS.map (fun x => x * s)).map Ψ = μS.map Ψ := by
    rw [Measure.map_map emb.measurable hmeas, hfun,
      ← Measure.map_map (JL.RI.meas_rmul (k := k) (r := r) _) emb.measurable, hμS, measS_of hF hz hT hH κ hκ]
    exact JL.RI.muS_right hz hT hWB hNB _ hSs
  rw [← emb.comap_map (μS.map (fun x => x * s)), key, emb.comap_map]

end Formalism.L2.SG.Pf.NcReal.JX
end
end

section

noncomputable section

open MeasureTheory Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.EC

open Formalism.QuantumDeterminants WlocSk.NB
open Formalism.MainNotions.BridgeCSB (Fil lieN dg)

variable {k r : ℕ}

theorem mp_toC : MeasurePreserving (toC (k := k) (r := r)) volume volume := by
  have h1 := volume_measurePreserving_sumPiEquivProdPi (fun _ : J k r => ℝ)
  have h2 := volume_measurePreserving_sumPiEquivProdPi (fun _ : CI k r ⊕ CI k r => ℝ)
  have h3 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (CI k r)).symm
  have h4 : MeasurePreserving (fun (w : CI k r → ℝ × ℝ) (i : CI k r) =>
      Complex.measurableEquivRealProd.symm (w i)) volume volume :=
    volume_preserving_pi (fun _ => Complex.volume_preserving_equiv_real_prod.symm)
  have h5 := ((h4.comp h3).comp h2).prod (MeasurePreserving.id (volume : Measure (Fin r → ℝ)))
  have h6 := h5.comp h1
  convert h6 using 1
  all_goals first | rfl | (funext y; rfl)

def fromC (t : (CI k r → ℂ) × (Fin r → ℝ)) : J k r → ℝ
  | Sum.inl (Sum.inl c) => (t.1 c).re
  | Sum.inl (Sum.inr c) => (t.1 c).im
  | Sum.inr a => t.2 a

theorem toC_fromC (t : (CI k r → ℂ) × (Fin r → ℝ)) : toC (fromC t) = t := by
  rfl

theorem continuous_fromC : Continuous (fromC (k := k) (r := r)) := by
  refine continuous_pi fun j => ?_
  rcases j with (c | c) | a
  · exact Complex.continuous_re.comp ((continuous_apply c).comp continuous_fst)
  · exact Complex.continuous_im.comp ((continuous_apply c).comp continuous_fst)
  · exact (continuous_apply a).comp continuous_snd

section Cont

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem continuous_expLJ : Continuous fun y : J k r → ℝ => (NormedSpace.exp (LJ y) : Mx k r) :=
  NormedSpace.exp_continuous.comp continuous_LJ

end Cont

def sJ (y : J k r → ℝ) : J k r → ℝ := fromC (psiC (NormedSpace.exp (LJ y)), psiR (NormedSpace.exp (LJ y)))

theorem continuous_sJ : Continuous (sJ (k := k) (r := r)) :=
  continuous_fromC.comp ((continuous_psiC.comp continuous_expLJ).prodMk (continuous_psiR.comp continuous_expLJ))

theorem entry_of_fil {D E : Mx k r} {p : ℕ} (h : Fil (p + 1) (D - E)) {i j : Fin (2 * r + k + 1)}
    (hij : dg k r j ≤ dg k r i + p) : D i j = E i j := by
  have h1 := h i j (by omega)
  rw [Matrix.sub_apply, sub_eq_zero] at h1
  exact h1

theorem mof_sub {g g' : Mx k r} (hg : g ∈ Nset k r) (hg' : g' ∈ Nset k r) (a b : Fin r)
    (hG : Fil (2 * r - a.val - b.val) (g - g')) :
    mof g a b - mof g' a b = g (eI k r a) (esI k r b) - g' (eI k r a) (esI k r b) := by
  have h1 := ((Formalism.MainNotions.BridgeCSB.mem_N_iff g).1 hg).2
  have h1' := ((Formalism.MainNotions.BridgeCSB.mem_N_iff g').1 hg').2
  have key : ∀ c : Fin r, star (g (esI k r c) (esI k r a)) * g (eI k r c) (esI k r b) -
      star (g' (esI k r c) (esI k r a)) * g' (eI k r c) (esI k r b) =
      if c = a then g (eI k r a) (esI k r b) - g' (eI k r a) (esI k r b) else 0 := by
    intro c
    have ha := a.isLt; have hb := b.isLt; have hc := c.isLt
    rcases lt_trichotomy c a with h | rfl | h
    · have hca : c.val < a.val := h
      have e1 := h1 (esI k r c) (esI k r a) (by rw [dg_esI, dg_esI]; omega)
      have e2 := h1' (esI k r c) (esI k r a) (by rw [dg_esI, dg_esI]; omega)
      rw [Matrix.sub_apply, Matrix.one_apply, if_neg (fun e => (ne_of_lt h) (esI_inj.1 e)), sub_zero] at e1 e2
      rw [e1, e2, if_neg (ne_of_lt h)]; simp
    · have e1 := h1 (esI k r c) (esI k r c) (by rw [dg_esI]; omega)
      have e2 := h1' (esI k r c) (esI k r c) (by rw [dg_esI]; omega)
      rw [Matrix.sub_apply, Matrix.one_apply, if_pos rfl, sub_eq_zero] at e1 e2
      rw [e1, e2, if_pos rfl]; simp
    · have hac : a.val < c.val := h
      have e1 := hG (esI k r c) (esI k r a) (by rw [dg_esI, dg_esI]; omega)
      have e2 := hG (eI k r c) (esI k r b) (by rw [dg_esI, dg_eI]; omega)
      rw [Matrix.sub_apply, sub_eq_zero] at e1 e2
      rw [e1, e2, if_neg (ne_of_gt h), sub_self]
  simp only [mof, Matrix.mul_apply, conjTranspose_apply, bF, bC]
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun c _ => key c)]
  simp

theorem psiC_sub (t t' : (CI k r → ℂ) × (Fin r → ℝ)) (c : CI k r)
    (hG : Fil (hC c) (NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')))
    (hE : Fil (hC c + 1) ((NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')) - (Lm t - Lm t'))) :
    psiC (NormedSpace.exp (Lm t)) c - psiC (NormedSpace.exp (Lm t')) c = t.1 c - t'.1 c := by
  have hg := Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem t)
  have hg' := Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem t')
  have ent : ∀ i j, dg k r j ≤ dg k r i + hC c →
      (NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')) i j = (Lm t - Lm t') i j :=
    fun i j h => entry_of_fil hE h
  rcases c with ⟨⟨a, b⟩, h⟩ | ⟨a, j⟩ | ⟨⟨a, b⟩, h⟩
  · have hab : a.val < b.val := h
    have := ent (eI k r a) (eI k r b) (by rw [dg_eI, dg_eI]; simp only [hC]; omega)
    simp only [Matrix.sub_apply, Lm_ee, chart_matrix_upper _ h] at this
    exact this
  · have := ent (eI k r a) (wI k r j) (by rw [dg_eI, dg_wI]; simp only [hC]; omega)
    simp only [Matrix.sub_apply, Lm_ew] at this
    exact this
  · have hab' : a.val < b.val := h
    have hb := b.isLt
    have eh : hC (Sum.inr (Sum.inr ⟨(a, b), h⟩) : CI k r) = 2 * r - a.val - b.val := rfl
    have hab := mof_sub hg hg' a b (by rw [← eh]; exact hG)
    have hba := mof_sub hg hg' b a (by
      have : 2 * r - b.val - a.val = 2 * r - a.val - b.val := by omega
      rw [this, ← eh]; exact hG)
    have e1 := ent (eI k r a) (esI k r b) (by rw [dg_eI, dg_esI, eh]; omega)
    have e2 := ent (eI k r b) (esI k r a) (by rw [dg_eI, dg_esI, eh]; omega)
    simp only [Matrix.sub_apply, Lm_es] at e1 e2
    have hba' := congrArg star hba
    have e2' := congrArg star e2
    simp only [star_sub] at hba' e2'
    have sk := cK_skew t.1 t.2 a b
    have sk' := cK_skew t'.1 t'.2 a b
    have hx : ∀ x : CI k r → ℂ, ∀ s, cK x s a b = x (Sum.inr (Sum.inr ⟨(a, b), h⟩)) := by
      intro x s; unfold cK; rw [dite_eq_left h]
    show kof _ a b - kof _ a b = _
    rw [← hx t.1 t.2, ← hx t'.1 t'.2]
    simp only [kof]
    linear_combination (1 / 2 : ℂ) * hab + (1 / 2 : ℂ) * e1 - (1 / 2 : ℂ) * hba' - (1 / 2 : ℂ) * e2' -
      (1 / 2 : ℂ) * sk + (1 / 2 : ℂ) * sk'

theorem psiR_sub (t t' : (CI k r → ℂ) × (Fin r → ℝ)) (a : Fin r)
    (hG : Fil (2 * r - 2 * a.val) (NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')))
    (hE : Fil (2 * r - 2 * a.val + 1) ((NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')) - (Lm t - Lm t'))) :
    psiR (NormedSpace.exp (Lm t)) a - psiR (NormedSpace.exp (Lm t')) a = t.2 a - t'.2 a := by
  have hg := Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem t)
  have hg' := Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem t')
  have ha := a.isLt
  have hm := mof_sub hg hg' a a (by
    have : 2 * r - a.val - a.val = 2 * r - 2 * a.val := by omega
    rw [this]; exact hG)
  have e1 := entry_of_fil hE (i := eI k r a) (j := esI k r a) (by rw [dg_eI, dg_esI]; omega)
  simp only [Matrix.sub_apply, Lm_es] at e1
  have hk : ∀ (x : CI k r → ℂ) (s : Fin r → ℝ), cK x s a a = (s a : ℂ) * Complex.I := by
    intro x s; unfold cK; rw [dite_eq_right (lt_irrefl a), dite_eq_right (lt_irrefl a)]
  rw [hk, hk] at e1
  have := congrArg Complex.im (hm.trans e1)
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero] at this
  simp only [psiR]
  linarith

theorem sJ_shear (i : J k r) (y y' : J k r → ℝ) (h : ∀ j, ht j < ht i → y j = y' j) :
    sJ y i - y i = sJ y' i - y' i := by
  have hF := Lm_fil_sub h
  have hE := Formalism.MainNotions.BridgeCSB.Fil.exp_sub_exp (chart_filtration_one (toC y)) (chart_filtration_one (toC y')) hF
  have hG : Fil (ht i) (NormedSpace.exp (Lm (toC y)) - NormedSpace.exp (Lm (toC y'))) := by
    have := (hE.mono (Nat.le_succ _)).add hF
    rwa [sub_add_cancel] at this
  rcases i with (c | c) | a
  · have := congrArg Complex.re (psiC_sub (toC y) (toC y') c hG hE)
    simp only [Complex.sub_re] at this
    show (psiC (NormedSpace.exp (Lm (toC y))) c).re - ((toC y).1 c).re =
      (psiC (NormedSpace.exp (Lm (toC y'))) c).re - ((toC y').1 c).re
    linarith
  · have := congrArg Complex.im (psiC_sub (toC y) (toC y') c hG hE)
    simp only [Complex.sub_im] at this
    show (psiC (NormedSpace.exp (Lm (toC y))) c).im - ((toC y).1 c).im =
      (psiC (NormedSpace.exp (Lm (toC y'))) c).im - ((toC y').1 c).im
    linarith
  · have := psiR_sub (toC y) (toC y') a hG hE
    show psiR (NormedSpace.exp (Lm (toC y))) a - (toC y).2 a =
      psiR (NormedSpace.exp (Lm (toC y'))) a - (toC y').2 a
    linarith

theorem shear_change_holds : ShearStep := by
  intro k r
  refine ⟨fun y => (psiC (NormedSpace.exp (LJ y)), psiR (NormedSpace.exp (LJ y))), ?_, ?_⟩
  · have hS := Formalism.MainNotions.BridgeCSB.shearMP (J k r) ht sJ continuous_sJ.measurable
      (fun i y y' h => sJ_shear i y y' h)
    have := mp_toC.comp hS
    convert this using 1
    funext y
    exact (toC_fromC _).symm
  · intro y
    exact nilpotent_chart_left_inverse (Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem (toC y)))

end Formalism.L2.SG.Pf.NcReal.JX.EC
end
end
