module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle225
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle191
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBPts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle108
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle233
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle192
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SlicesFiniteRegularityBuilt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle036
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle212
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle113
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSE2
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle217
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSELeibnizCls
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEOuterLeib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEPairAtDeriv
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEWaveJc
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle231
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle026
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle235
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle234
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DecayPairEstimate
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExpansionSiteZeroInduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsNormBoundThreeFamilies
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle050
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle236
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle232
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle200
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle051
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle198
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle189
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle188
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle163
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermPartsCompactSupport
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle096
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.LeftFubiniLemmas

theorem side0Pos_of (hW : PartialBesselProperness.PbWords) (hPr : ProperLeftVariablesDomain) (hPts : CutHB.Pts) : CutHB.Side0Pos := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hj1 hF hw hγ hΩ e τ hτ
  have hPt := hPts Wp Wq P p j hj h hh γ hγ hΩ
  obtain ⟨hab, rfl⟩ := hh
  have hjr : D.ptSize h ≤ P.r := by omega
  have e0 : D.ptSize h + (P.r - D.ptSize h) = P.r := by omega
  have hd : ∀ q, D.ptDiag h q ≠ 0 := fun q => Formalism.FourierDecayAlt.P.JCTx6.Link2.ptScal_ne h hab q q.2
  have hT := p.hT
  obtain ⟨R, hR⟩ := hF.2.1

  have hOm : LevelPointCoordinates.mLev P (D.ptSize h) hj τ γ ∈
      JF.Om P.k (P.r - D.ptSize h) (p.T.bs (D.ptSize h)).z (p.T.bs (D.ptSize h)).z' := by
    have h2 := Formalism.FourierDecayAlt.P.PBH.om_cast (by omega : P.r - (D.ptSize h + 1) + 1 = P.r - D.ptSize h) _ _ _
      (Formalism.FourierDecayAlt.P.PBH.mcOm P.k (P.r - (D.ptSize h + 1)) (p.T.bs (D.ptSize h + 1)).z (p.T.bs (D.ptSize h + 1)).z'
        (p.T.bs (D.ptSize h + 1)).z_mem (p.T.bs (D.ptSize h + 1)).z'_mem τ hτ γ hγ hΩ)
    rw [Formalism.FourierDecayAlt.P.PBH.asm_castM_castM, Formalism.FourierDecayAlt.P.PBH.asm_castV_castV, Formalism.FourierDecayAlt.P.PBH.asm_castV_castV] at h2
    rw [Formalism.FourierDecayAlt.P.PBH.levTower_bs_z_eq_castV_liftVec p.T _ hj, Formalism.FourierDecayAlt.P.PBH.levTower_bs_z'_eq_castV_liftVec p.T _ hj]
    exact h2
  have hHc : ContinuousOn (D.uwG P.k P.r p.T.base.z p.T.base.z' F (D.ptSize h) hjr w e)
      {x | x ∈ B.GV P.k P.r ∧ Dmin P.k P.r p.T.base.z p.T.base.z' x ⟨D.ptSize h, by omega⟩ ≠ 0} :=
    Formalism.FourierDecayAlt.P.PBG.contOn_of_loc (S := Formalism.FourierDecayAlt.P.PBG.Sd p.T.base.z p.T.base.z' (D.ptSize h) hjr)
      (fun x hx hxG => Formalism.FourierDecayAlt.P.PBG.uwG_mem (E := Wq →L[ℂ] Wp) p.T.base.z p.T.base.z' (D.ptSize h) hjr hF.1 w e
        x hx hxG)
  have hR' := Formalism.FourierDecayAlt.P.PBG.uwG_supp p.T.base.z p.T.base.z' F R hR (D.ptSize h) hjr w e
  have key := jfSliceIntN e0 hj1 (D.ptPerm h) (D.ptDiag h) hd (p.T.bs (D.ptSize h)) p.T.base
    (p.T.z_lev _ hjr) (p.T.z'_lev _ hjr) (p.T.π'_lev _ hjr) (hT _ hjr).2.1
    (Formalism.FourierDecayAlt.P.PBM.tower_haarW' p.T hT _ hjr e0) (hT _ hjr).2.2 (hT 0 (Nat.zero_le _)).2.2
    (LevelPointCoordinates.mLev P (D.ptSize h) hj τ γ) hOm _ hHc R hR'
  have hs := slice_eq p.T.base.z p.T.base.z' (D.uwG P.k P.r p.T.base.z p.T.base.z' F (D.ptSize h) hjr w e) h hjr
    rfl e0
  show B.JF (p.T.bs (D.ptSize h)) (D.castF _ (D.sliceAt P.k P.r p.T.base.z p.T.base.z'
    (D.uwG P.k P.r p.T.base.z p.T.base.z' F (D.ptSize h) hjr w e) h)) (LevelPointCoordinates.mLev P (D.ptSize h) hj τ γ) = _
  rw [hs, key]
  congr 1
  funext v
  have hZ : IsUnit (lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h)).det := by
    rw [Matrix.det_mul]
    exact (lh_unit _ v).mul (Ne.isUnit (Formalism.FourierDecayAlt.P.Ux10.det_hMat_ne _ _ hd))
  have hz : PBQ.zxH h (D.ptSize h) rfl v = lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h) := by
    simp only [PBQ.zxH, finCongr_refl, Matrix.reindex_refl_refl]
  have hpt : D.castM e0 (U.mMap P.k (D.ptSize h) (P.r - D.ptSize h)
      (lhOf (D.ptPerm h) v * U.hMat (D.ptPerm h) (D.ptDiag h)) (LevelPointCoordinates.mLev P (D.ptSize h) hj τ γ)) =
      LevelPointCoordinates.x0 P.k P.r (D.ptSize h) hj (PBQ.zxH h (D.ptSize h) rfl v) τ γ := by
    rw [hz]
    exact pt_eq hj _ hZ τ hτ γ e0 _
  rw [hpt]
  have hy := (hPt v).2 τ hτ
  have hyG : LevelPointCoordinates.x0 P.k P.r (D.ptSize h) hj (PBQ.zxH h (D.ptSize h) rfl v) τ γ ∈ B.GV P.k P.r :=
    LevelPointCoordinates.x0_GV hj (hPt v).1 hτ hγ
  have hpw := hW P.k (D.ptSize h) (P.r - D.ptSize h) P.r Wp Wq (p.T.bs (D.ptSize h)) p.T.base e0
    (p.T.z_lev _ hjr).symm (D.ptSize h) hjr F {g | B.gN g ≤ R} (fun g hg _ => hF.1 g hg)
    (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le _ _ R) (fun g hg hgC => by
      by_contra hne
      exact hgC (hR g hg hne))
    (PBQ.domP P.k P.r (D.ptSize h) p.T.base.z p.T.base.z') (PBQ.isOpen_domP _ _ _ _ _)
    (fun g hg => hg.1 ⟨D.ptSize h, by omega⟩ le_rfl hjr)
    (hPr Wp Wq P p (D.ptSize h) hjr _ (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le _ _ R)) w e _ hy hyG
  unfold PBQ.ellH CutHB.phf
  rw [_root_.smul_apply, ContinuousLinearMap.id_apply, ← hpw]
  rfl

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

theorem side0Pos_of'' (hPr : ProperLeftVariablesDomain) : CutHB.Side0Pos :=
  side0Pos_of Formalism.FourierDecayAlt.P.letters_pass_partial_bessel hPr CutHB.pts

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas
end
end

section

open MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

theorem clsE_sliceGood_ofC (hJ : JSliceGenC) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (h1 : 1 ≤ l0) (h2 : l0 ≤ P.k)
    (hz : D.z = z) (hz' : D.z' = z') (hπ : D.π = π) (hπ' : D.π' = π') (l : Fin P.r) (hl : l.val = 0)
    (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r) (Φ : RadSp P.k P.r z z' π π')
    (hΦ : Φ ∈ ClsE S P z z' π π' X L st l0 D l) : SliceGood X μ l c Φ := by
  have hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hD.2.1
  have hle : ClsE S P z z' π π' X L st l0 D l ≤ sgSub (X := X) (μ := μ) (l := l) (c := c) hμ := by
    refine opClos_le X l ?_ ?_
    · refine le_trans (base0_le_waveJc (S := S) P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' l hl) ?_
      refine Submodule.span_le.mpr ?_
      intro Ψ hΨ
      exact hJ Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc Ψ hΨ
    · intro j Ψ hΨ
      have h' : SliceGood X μ l c Ψ := hΨ
      exact sliceGood_op (h := h') (j := j)
  exact hle hΦ

theorem leibnizCls_ofC (hO : OuterLeib) (hJ : JSliceGenC) : LeibnizCls := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl u v hu hv c hc t ht
  have hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hD.2.1
  have hsu : ∀ b, SliceGood X μ l c (u b) := fun b =>
    clsE_sliceGood_ofC hJ S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc (u b) (hu b)
  have hsv : ∀ b, SliceGood X μ l c (v b) := fun b =>
    clsE_sliceGood_ofC hJ S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc (v b) (hv b)
  exact wirt_of_hasFDerivAt (hO P.k P.r z z' Wp Wq π π' X μ hμ l S u v c hc hsu hsv t ht)

theorem densSmoothCls_ofC (hO : OuterLeib) (hJ : JSliceGenC) : DensSmoothCls := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl u v hu hv c hc
  have hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hD.2.1
  haveI : SFinite μ := Formalism.FourierDecayAlt.P5.sfinite_of_isHaarOn _ μ hμ
  have hsu : ∀ b, SliceGood X μ l c (u b) := fun b =>
    clsE_sliceGood_ofC hJ S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc (u b) (hu b)
  have hsv : ∀ b, SliceGood X μ l c (v b) := fun b =>
    clsE_sliceGood_ofC hJ S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' l hl c hc (v b) (hv b)
  refine ⟨fun n => ?_, fun t ht b => ⟨levelSquareIntegrable_succ_update_of_sliceGood X μ l c (hsu b) ht, levelSquareIntegrable_succ_update_of_sliceGood X μ l c (hsv b) ht⟩⟩
  exact (contDiffOn_inverse_norm_sq n).mul (form_contDiffOn hO X μ hμ l S c hc n u v hsu hsv)

theorem leibnizCls_of_jSliceC (hJ : JSliceGenC) : LeibnizCls :=
  leibnizCls_ofC (outerLeib_of pairing_derivative_formula) hJ

theorem densSmoothCls_of_jSliceC (hJ : JSliceGenC) : DensSmoothCls :=
  densSmoothCls_ofC (outerLeib_of pairing_derivative_formula) hJ

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC
  Formalism.FourierDecayAlt.P5.HerD

theorem wave_outgoing_orbital : WaveOutJ := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hdat hl0 hle hz hz' hπ hπ' l hl u v hu hv c hc s Wv hW
  have hμ : B.IsHaarOn (Glev P.k P.r (Fin.last P.r)) μ := hdat.2.1
  haveI := sfinite_of_isHaarOn _ μ hμ

  have hl2u := fun b => wave_operator_le_l2_subspace P z z' π π' μ hμ D hz hz' hπ hπ' l (hu b)
  have hl2v := fun b => wave_operator_le_l2_subspace P z z' π π' μ hμ D hz hz' hπ hπ' l (hv b)
  have hW1 : ∀ c' : Fin P.r → ℂ, ‖fsv s (c' l)‖ = 1 := fun c' => HerC.norm_fsv s (c' l)
  have hl' : l.castSucc = 0 := by
    ext
    simp [hl]
  have keyu : ∀ b, LevelSquareIntegrable μ l.castSucc (u b) c := by
    intro b
    rw [hl']
    exact (hl2u b).2 c
  have keyv : ∀ b, LevelSquareIntegrable μ l.castSucc (v b) c := by
    intro b
    rw [hl']
    exact (hl2v b).2 c

  have keyW : ∀ b, LevelSquareIntegrable μ l.castSucc (Wv (u b)) c := by
    intro b
    have h := keyu b
    unfold LevelSquareIntegrable at h ⊢
    simp only [waveOut_pairAt_self μ hW hW1]
    exact h
  have hd := dens_int μ hμ l (fun b => Wv (u b)) v (fun b => mul_lc hW _ (hl2u b).1)
    (fun b => (hl2v b).1) c keyW keyv
  rw [← hd.2]
  simp_rw [waveOut_dens μ l s hW u v c]

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.FourierDecayAlt.P5.HerD

theorem expansion_l2_of_open_estimates (hO : OneLetterDens) (hS : DensSmoothCls) (h2 : DecayPair2) (h3 : DecayPair3)
    (h4 : DecayPair4) : LevelDensitySquareIntegrable :=
  expansion_L2_of_decay_pairs word_expansion (step_density_expansion_of_mirror boundary_torus_invariance (expansion_site_zero_induction hS hO boundary_torus_closure))
    decay_pair_estimate h2 h3 h4

theorem stepExp0_of_open (hO : OneLetterDens) (hS : DensSmoothCls) (h2 : DecayPair2) (h3 : DecayPair3)
    (h4 : DecayPair4) : StepExp0 :=
  step_density_of_square (expansion_l2_of_open_estimates hO hS h2 h3 h4)

end Formalism.FourierDecayAlt.P.CutSE
end
end

section

namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt NumberField

def WaveLocBC : Prop :=
  P5.ThmPActualCpt → StandardPairingDecay.PStdC → KB.DegWave → KB.SizeStdCpt → KB.VIsoCpt → FormPosCpt →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∃ X : ℕ → Fin S.f → ℝ, JC.HidaCurvatureBarriers S X ∧
      ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.WaveLoc (setC S p F) v fun i => X i v

def WaveLocBPCpt : Prop :=
  P5.ThmPActualCpt → StandardPairingDecay.PStdC →
  ∀ (Cb Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    28 * Real.exp 1 ≤ Cc → KB.IsLeadingFormSetting Cb Cc S p f χ A₀ →
    ∃ X : ℕ → Fin S.f → ℝ, JC.HidaCurvatureBarriers S X ∧
      ∀ F : ∀ v : Fin S.f, ℝ → B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
        (∀ v ε, 0 < ε → KB.CptCoef (p v).T.base (F v ε)) → ∀ v, KB.WaveLoc (setC S p F) v fun i => X i v

end Formalism.FourierDecayAlt.P.PBL


open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBL in
theorem Formalism.FourierDecayAlt.P.wave_local_compact_support_route : Formalism.FourierDecayAlt.P.PBL.WaveLocBC := by
  intro hA hPSC hDW hSS hVI hFP Cb Cc E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hCc hB
  refine ⟨fun i v => Xw S i v, thr_wave hCc hB, fun F hF v => ?_⟩
  intro i hi1 hir a ha haK
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have hir' : j + 1 ≤ S.G.r + 1 := hir
  have hj : j ≤ S.G.r := by omega
  have haK' : a.length + C.Kst ≤ S.Ntop := haK
  have ha' : D.AdmAt S v a := ha
  have haN : a.length ≤ S.Ntop := by omega
  have hB' := hB
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGo, hGr, -⟩ := hB'
  have hCI := Formalism.FourierDecayAlt.P.PBCut.cutInside_of_built hB
  obtain ⟨grid, hinj, hl1, hnodes, hlp, hlm⟩ := nodes_level hB v a ha' C.Kst haK' j hj
  have hwa : KB.CutWord (D.parOf S v) (S.l + 1) a :=
    (Formalism.FourierDecayAlt.P.new_letters_admissible E Wp Wq S hGo hGr hCI v a C.Kst 0 ha' haK' (by omega)).1
  refine ⟨PBD.pushU grid (fun ys => KB.plusW ys a), PBD.pushTh grid (fun ys => KB.plusW ys a),
    PBD.pushU grid (fun ys => KB.minusW ys a), PBD.pushTh grid (fun ys => KB.minusW ys a), hlp, hlm,
    fun ε hε l Y hY => ⟨?_, Complex.I ^ C.Kst, by simp, ?_⟩⟩
  · have hY' : ∀ h ∈ Y, D.ptSize h = j := fun h hh => by have := hY h hh; omega
    have h0 := block0C hA hPSC hVI hFP hB F hF v ε hε j hj a hwa l Y hY'
    rw [Nat.add_sub_cancel]
    exact h0
  · have hY' : ∀ h ∈ Y, D.ptSize h = j := fun h hh => by have := hY h hh; omega
    have hK := blockK_waveC hA hPSC hDW hSS hVI hFP hB F hF v ε hε j hj a ha' haN hwa C.Kst grid hinj hnodes
      (Xw S (j + 1) v) (xw_nonneg hB _ v) (xw_K hB v j C.Kst grid hl1) l Y hY'
    refine blockPSD_congr (fun p' _ q' _ => ?_) (fun _ _ _ _ => rfl) (fun p' _ q' _ => ?_) hK
    · show ((Xw S (j + 1) v ^ C.Kst : ℝ) : ℂ) * ∑ n, (F7.thGrid grid n : ℂ) *
          KB.gN (setC S p F) v ε j (KB.plusW (List.ofFn fun b => grid b (n b)) a) p' q' =
        ((Xw S (j + 1) v ^ C.Kst : ℝ) : ℂ) * KB.mix (setC S p F) v ε (j + 1 - 1)
          (PBD.pushU grid fun ys => KB.plusW ys a) (PBD.pushTh grid fun ys => KB.plusW ys a) p' q'
      rw [Nat.add_sub_cancel, mix_push]
    · show ((Xw S (j + 1) v ^ C.Kst : ℝ) : ℂ) * ∑ n, (F7.thGrid grid n : ℂ) *
          KB.gN (setC S p F) v ε j (KB.minusW (List.ofFn fun b => grid b (n b)) a) p' q' =
        ((Xw S (j + 1) v ^ C.Kst : ℝ) : ℂ) * KB.mix (setC S p F) v ε (j + 1 - 1)
          (PBD.pushU grid fun ys => KB.minusW ys a) (PBD.pushTh grid fun ys => KB.minusW ys a) p' q'
      rw [Nat.add_sub_cancel, mix_push]

theorem Formalism.FourierDecayAlt.P.wave_local_positive_compact_support : Formalism.FourierDecayAlt.P.PBL.WaveLocBPCpt := fun hA hPSC =>
  Formalism.FourierDecayAlt.P.wave_local_compact_support_route hA hPSC Formalism.FourierDecayAlt.P.degree_of_plane_wave Formalism.FourierDecayAlt.P.size_standard_compact
    Formalism.FourierDecayAlt.P.vector_isomorphism_compact_support Formalism.FourierDecayAlt.P.module_form_pos_compact_support
end

section

namespace Formalism.FourierDecayAlt.P.GermRateSplit

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.PBK Formalism.FourierDecayAlt.P.GermRealisation Formalism.FourierDecayAlt.P.GermFibreKernels Finset Filter Topology MeasureTheory NumberField
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)]

def GermRateLow (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Prop :=
  ∀ ε, 0 < ε → ∀ b s, 1 ≤ b → 2 ≤ s → b + s ≤ S.G.r + 1 → ∀ a, D.AdmAt S v a →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Vec : C.LPt → H),
    (∀ P Q, KB.gN S v ε (b + s - 1) a P Q = ⟪Vec P, Vec Q⟫_ℂ) →
    ∃ (ε' : ℂ) (φ : ℂ → ℂ), ‖ε'‖ = 1 ∧ (∀ z, ‖φ z‖ = 1) ∧ ContinuousOn φ {0}ᶜ ∧
      ∀ h : C.LPt, D.ptSize h = b - 1 → ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
        ‖utOf s (vOf (KB.dlB S (b + s - 1) 1) Vec) h x D -
          mainD s (betaL S) ε' (fun z => φ z • btOf s (KB.dlB S b s) Vec h z) x D‖ ≤ C * ‖x‖⁻¹

def GermRateTop (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Prop :=
  ∀ ε, 0 < ε → ∀ b s, 1 ≤ b → 2 ≤ s → b + s = S.G.r + 2 → ∀ a, D.AdmAt S v a →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (Vec : C.LPt → H),
    (∀ P Q, KB.gN S v ε (b + s - 1) a P Q = ⟪Vec P, Vec Q⟫_ℂ) →
    ∃ (ε' : ℂ) (φ : ℂ → ℂ), ‖ε'‖ = 1 ∧ (∀ z, ‖φ z‖ = 1) ∧ ContinuousOn φ {0}ᶜ ∧
      ∀ h : C.LPt, D.ptSize h = b - 1 → ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → ∃ C : ℝ, ∀ x : ℂ, x ≠ 0 → ∀ D ∈ K,
        ‖utOf s (vOf (KB.dlB S (b + s - 1) 1) Vec) h x D -
          mainD s (betaL S) ε' (fun z => φ z • btOf s (KB.dlB S b s) Vec h z) x D‖ ≤ C * ‖x‖⁻¹

theorem germRate_of (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (hL : GermRateLow S v) (hT : GermRateTop S v) :
    GermRate S v := by
  intro ε hε b s hb hs hbs
  rcases Nat.lt_or_ge (b + s) (S.G.r + 2) with h | h
  · exact hL ε hε b s hb hs (by omega)
  · exact hT ε hε b s hb hs (by omega)

end loc

def GermRateLowB : Prop :=
  P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ → ∀ n v, GermRateLow (PBL.setC S p (PBASM.cutSeq S p f χ n)) v

def GermRateTopB : Prop :=
  P5.ThmPActualCpt → ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (p : ∀ v, KB.Pl (D.parOf S v) (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ) (A₀ : ℝ),
    KB.IsLeadingFormSetting Cb Cc S p f χ A₀ → ∀ n v, GermRateTop (PBL.setC S p (PBASM.cutSeq S p f χ n)) v

theorem germRateB_of (hL : GermRateLowB) (hT : GermRateTopB) : GermRateB := by
  intro hA Cb
  obtain ⟨c1, h1⟩ := hL hA Cb
  obtain ⟨c2, h2⟩ := hT hA Cb
  refine ⟨max c1 c2, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S p f χ A₀ hB n v
  exact germRate_of _ v (h1 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place (le_max_left _ _) hB) n v)
    (h2 E Wp Wq S p f χ A₀ (PBJoint.built_setting_to_model_place (le_max_right _ _) hB) n v)

end

end Formalism.FourierDecayAlt.P.GermRateSplit

theorem Formalism.FourierDecayAlt.P.germ_rate_bound_of_split :
    Formalism.FourierDecayAlt.P.GermRateSplit.GermRateLowB → Formalism.FourierDecayAlt.P.GermRateSplit.GermRateTopB → Formalism.FourierDecayAlt.P.GermFibreKernels.GermRateB :=
  Formalism.FourierDecayAlt.P.GermRateSplit.germRateB_of
end
