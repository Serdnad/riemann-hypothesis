module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle185
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle177
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle184
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle065
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChiLIntegrable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IntegrableUnipotentNormRpowNeg
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceContOn
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CornerBZero
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AestronglyMeasurableGermIntegrand
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpNormPiLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightCosetActionMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.GrpMA

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def LvlA : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    (k r : ℕ) (hr : 1 ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (D' : Set (Q.Mx k r)) (Y : ℂ),
    inWb k r z → inWb k r z' → Q.IsDom k r z z' (TemperedBoundGL3.lr hr).castSucc D' →
    ∀ J₀ ∈ Q.FFl k r z z' π π' (TemperedBoundGL3.lr hr).castSucc D', ∀ c ∈ OmX r, ∀ g ∈ Q.Glev k r (Fin.last r),
      g ∈ Qx6.Dc1 (TemperedBoundGL3.lr hr) D' c →
      NLv k r z z' (TemperedBoundGL3.lr hr).castSucc (Q.uC k r (Fin.last r) Y - 1) J₀
          (Q.w1 k r (TemperedBoundGL3.lr hr) (c (TemperedBoundGL3.lr hr)) * g) =
        -((Q.uC k r (Fin.last r) Y - 1 - ((Q.mdim k r (Fin.last r) - 1 : ℕ) : ℂ)) •
              Q.tL k r z z' (Fin.last r) Y 0 1 (fun x => J₀ (Q.w1 k r (TemperedBoundGL3.lr hr) (c (TemperedBoundGL3.lr hr)) * x)) g -
            pbOp (TemperedBoundGL3.lr hr) (fun c' => Q.tL k r z z' (Fin.last r) Y 0 1
              (fun x => J₀ (Q.w1 k r (TemperedBoundGL3.lr hr) (c' (TemperedBoundGL3.lr hr)) * x)) g) c) -
          (star (c (TemperedBoundGL3.lr hr)))⁻¹ •
            Q.tL k r z z' (Fin.last r) Y 1 1 (fun x => J₀ (Q.w1 k r (TemperedBoundGL3.lr hr) (c (TemperedBoundGL3.lr hr)) * x)) g

section ops

variable {k r : ℕ} {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

theorem nlv_smulC (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1)) (u : ℂ) :
    Formalism.FourierDecayAlt.P5.SmulC (E := X) (NLv k r z z' l u) := by
  intro α f
  funext x
  simp only [NLv, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [Formalism.FourierDecayAlt.P5.qminorOp_smulC (fun a b => Formalism.FourierDecayAlt.P5.eabH_smulC _ a b) _ _ u α f, Pi.smul_apply, smul_comm]

theorem nlv_left {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 1))
    (u : ℂ) (i : Fin (r + 1)) {c : Fin r → ℂ} (hc : c ∈ OmX r) (f : Q.Mx k r → X) :
    NLv k r z z' l u (fun x => f (Q.wCell k r i c * x)) = fun x => NLv k r z z' l u f (Q.wCell k r i c * x) := by
  funext x
  simp only [NLv]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
  rw [TemperedBoundGL3.hermitian_invariant_cell_action i hc hz x]
  congr 1
  exact congrFun (Formalism.FourierDecayAlt.P.quantum_minor_left_hermitian X _ _ (Hpk k r) f _ _ u _) x

end ops

theorem jDRvStepA_of_lvlA (h : LvlA) : JDRvStepA := by
  intro Wp Wq _ _ _ _ k r hr z z' π π' D Y hz hz' hD J hJ c hc g hg hcg
  obtain ⟨hJ₀, hD'⟩ := TemperedBoundGL3.br1 hz hz' hD hJ hc (TemperedBoundGL3.lr hr)
  have hcg' : Q.wCell k r (TemperedBoundGL3.lr hr).succ c * g ∈ D := by rw [TemperedBoundGL3.lr_succ]; exact hcg
  have hgD' := TemperedBoundGL3.cell_preimage_mem_domain (TemperedBoundGL3.lr hr) hcg'
  have hL := h Wp Wq k r hr z z' π π' _ Y hz hz' hD' _ hJ₀ c hc g hg hgD'

  set l : Fin r := TemperedBoundGL3.lr hr with hl
  set J₀ := Q.resG k r l.castSucc J c with hJ₀def
  set W : (Fin r → ℂ) → ℂ := fun c' => ((‖c' l‖ ^ (Mdim k r l - 1) : ℝ) : ℂ) with hW
  set A' : (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun c' =>
    Q.tL k r z z' (Fin.last r) Y 0 1 (fun x => J₀ (Q.w1 k r l (c' l) * x)) g with hA'
  set T22 := Q.tL k r z z' (Fin.last r) Y 1 1 (fun x => J₀ (Q.w1 k r l (c l) * x)) g with hT22

  have hb := TemperedBoundGL3.br2 l (NLv k r z z' l.castSucc (Q.uC k r (Fin.last r) Y - 1)) (nlv_smulC z z' _ _) c
    (nlv_left hz z' _ _ l.castSucc hc) J g
  rw [TemperedBoundGL3.lr_succ] at hb
  have eL : FNv k r z z' Y J ⟨r - 1, by omega⟩ c g =
      W c • NLv k r z z' l.castSucc (Q.uC k r (Fin.last r) Y - 1) J₀ (Q.w1 k r l (c l) * g) := by
    show Q.resG k r (Fin.last r) (NLv k r z z' l.castSucc (Q.uC k r (Fin.last r) Y - 1) J) c g = _
    rw [hb]

  have eR : ∀ c' ∈ OmX r, (∀ a : Fin r, a.val < l.val → c' a = c a) →
      Q.resG k r (Fin.last r) J c' = fun x => W c' • J₀ (Q.w1 k r l (c' l) * x) := by
    intro c' hc' hcc
    rw [← TemperedBoundGL3.lr_succ hr, Qx6.resG_succ]
    funext x
    show W c' • Q.resG k r l.castSucc J c' (Q.w1 k r l (c' l) * x) = _
    rw [Qx6.ind_resG l.castSucc J c' hc' c hc (fun a ha => hcc a ha)]
  have eRc := eR c hc (fun _ _ => rfl)

  have hTop := mirror_residue_top_holds Wp Wq k r z z' π π' D Y hz hz' hD J hJ
  set f₂ : (Fin r → ℂ) → (Wq →L[ℂ] Wp) := fun c' =>
    Q.tL k r z z' (Fin.last r) Y 0 1 (Q.resG k r (Fin.last r) J c') g with hf₂
  have hgerm : (fun c' => FNv k r z z' Y J (Fin.last r) c' g) =ᶠ[𝓝 c] fun c' => -f₂ c' := by
    filter_upwards [Qx6.near_pt (Qx6.open_Dcell hD.1 (Fin.last r)) hc hcg] with c' hc'
    rw [hTop c' hc'.1 g hg hc'.2]
    rfl
  have hfam := (Formalism.FourierDecayAlt.P.restriction_good_family Wp Wq k r z z' π π' D hz hz' hD J hJ (Fin.last r)).1
  have hf₂d : DifferentiableAt ℝ f₂ c :=
    Formalism.FourierDecayAlt.P.Qx3.fam_differentiableAt (Formalism.FourierDecayAlt.P.Qx3.pres_tL z z' Y 0 1 _ hfam) (x := (c, g)) ⟨hc, hcg⟩ hg
  have hrr := Formalism.FourierDecayAlt.P.Qx3.pres_tL (i := l.succ) (U₀ := Qx6.UU (Qx6.Dc1 l (Qx6.Dcell D l.castSucc c))) z z' Y 0 1 _
    (Qx6.sf_rr Formalism.FourierDecayAlt.P.weyl_level_element_properties l hJ₀.1)
  rw [TemperedBoundGL3.lr_succ] at hrr
  have hA'd : DifferentiableAt ℝ A' c :=
    Formalism.FourierDecayAlt.P.Qx3.fam_differentiableAt hrr (x := (c, g)) ⟨hc, hgD'⟩ hg
  have hWd : DifferentiableAt ℝ W c := Qx6.diff_gamma l _ hc
  have hf₃d : DifferentiableAt ℝ (fun c' => W c' • A' c') c := hWd.smul hA'd
  have hline : ∀ᶠ s in 𝓝 (c l), (fun c' => -f₂ c') (Function.update c l s) =
      (-1 : ℂ) • (fun c' => W c' • A' c') (Function.update c l s) := by
    filter_upwards [isOpen_ne.mem_nhds (hc l)] with s hs
    have hu : Function.update c l s ∈ OmX r := Qx6.update_mem_Om hc l hs
    have hcc : ∀ a : Fin r, a.val < l.val → Function.update c l s a = c a := fun a ha =>
      Function.update_of_ne (fun e => by rw [e] at ha; exact lt_irrefl _ ha) _ _
    show -(Q.tL k r z z' (Fin.last r) Y 0 1 (Q.resG k r (Fin.last r) J (Function.update c l s)) g) = _
    rw [eR _ hu hcc, show (fun x => W (Function.update c l s) • J₀ (Q.w1 k r l (Function.update c l s l) * x)) =
      W (Function.update c l s) • (fun x => J₀ (Q.w1 k r l (Function.update c l s l) * x)) from rfl,
      Formalism.FourierDecayAlt.P5.tL_smulC z z' (Fin.last r) Y 0 1 (W (Function.update c l s))
      (fun x => J₀ (Q.w1 k r l (Function.update c l s l) * x)), neg_one_smul]
    rfl
  have hp1 : pbOp l (fun c' => FNv k r z z' Y J (Fin.last r) c' g) c = pbOp l (fun c' => -f₂ c') c :=
    Qx6.opL_germ l 3 hgerm
  have hp2 : pbOp l (fun c' => -f₂ c') c = (-1 : ℂ) • pbOp l (fun c' => W c' • A' c') c :=
    Qx6.opL_dir l 3 (-1) hf₂d.neg hf₃d hline
  have hp3 : pbOp l (fun c' => W c' • A' c') c = W c • pbOp l A' c + ((((Mdim k r l - 1 : ℕ) : ℂ) / 2) * W c) • A' c := by
    rw [Qx6.pbOp_smul l hc hWd hA'd, Qx6.pbOp_gamma l hc]

  have eF : FNv k r z z' Y J (Fin.last r) c g = -(W c • A' c) := by
    rw [hTop c hc g hg hcg]
    show -(Q.tL k r z z' (Fin.last r) Y 0 1 (Q.resG k r (Fin.last r) J c) g) = _
    rw [eRc, show (fun x => W c • J₀ (Q.w1 k r l (c l) * x)) = W c • (fun x => J₀ (Q.w1 k r l (c l) * x)) from rfl,
      Formalism.FourierDecayAlt.P5.tL_smulC z z' (Fin.last r) Y 0 1 (W c) (fun x => J₀ (Q.w1 k r l (c l) * x))]
    rfl
  have e11 : Q.QL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J) c g = W c • T22 := by
    show Q.tL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J c) g = _
    rw [eRc, show (fun x => W c • J₀ (Q.w1 k r l (c l) * x)) = W c • (fun x => J₀ (Q.w1 k r l (c l) * x)) from rfl,
      Formalism.FourierDecayAlt.P5.tL_smulC z z' (Fin.last r) Y 1 1 (W c) (fun x => J₀ (Q.w1 k r l (c l) * x))]
    rfl

  have hmd : ((Q.mdim k r (Fin.last r) - 1 : ℕ) : ℂ) = (Q.mdim k r (Fin.last r) : ℂ) - 1 := by
    have : 1 ≤ Q.mdim k r (Fin.last r) := by simp [Q.mdim]
    push_cast [Nat.cast_sub this]
    ring
  have hMd : ((Mdim k r l - 1 : ℕ) : ℂ) = (Q.mdim k r (Fin.last r) : ℂ) + 1 := by
    rw [Qx6.stp_Mdim, TemperedBoundGL3.lr_succ]
  have hU : Q.uC k r (Fin.last r) Y - 1 - ((Q.mdim k r (Fin.last r) - 1 : ℕ) : ℂ) =
      Y - ((Mdim k r l - 1 : ℕ) : ℂ) / 2 := by
    rw [hmd, hMd]
    unfold Q.uC
    ring

  rw [eL, hL, hU]
  show _ = Y • FNv k r z z' Y J (Fin.last r) c g - pbOp l (fun c' => FNv k r z z' Y J (Fin.last r) c' g) c -
    (star (c l))⁻¹ • Q.QL k r z z' (Fin.last r) Y 1 1 (Q.resG k r (Fin.last r) J) c g
  rw [hp1, hp2, hp3, eF, e11]
  module

end

end Formalism.FourierDecayAlt.P.CutMP.GrpMA
end

section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section outer

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]



theorem outer_int (S : B.RealPlaceData k r Wp Wq) (hN : S.μN = D.muN k r) (hW1 : S.μW Set.univ = 1)
    (hW1' : S.μW' Set.univ = 1) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0)) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (hFc : ContinuousOn F (B.GV k r)) (M : ℝ) (Bs : Set (U.Xi k r 0 0 σ)) (hBs : MeasurableSet Bs)
    (hBsf : U.muXi k r 0 0 σ Bs < ⊤)
    (hdom : ∀ (ξ : U.Xi k r 0 0 σ) (γ : B.Mat k 0), γ ∈ B.GV k 0 →
      ‖F (U.gaXi k 0 σ d ξ (fun a => a.elim0) γ)‖ ≤ Bs.indicator (fun _ => M) ξ) :
    Integrable (fun p => theta0 S.z σ.symm p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p) S.μSS ∧
      ∫ p, theta0 S.z σ.symm p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p ∂S.μSS =
        ∫ x, conjL S x.1 x.2 (U.PhiFun (s := 0) k 0 σ d S.z S.z' F (fun a => a.elim0)
          ((midB r 0 (Matrix.of x.1))⁻¹ * γ0 * midB r 0 (Matrix.of x.2))) ∂(S.μW.prod S.μW') := by
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hsW : SigmaFinite S.μW := Dx2.OrbJ.sigmaF S.haarW
  have hsW' : SigmaFinite S.μW' := Dx2.OrbJ.sigmaF S.haarW'
  have hfW : IsFiniteMeasure S.μW := ⟨by rw [hW1]; exact ENNReal.one_lt_top⟩
  have hfW' : IsFiniteMeasure S.μW' := ⟨by rw [hW1']; exact ENNReal.one_lt_top⟩
  set γ := U.mMap k r 0 (U.hMat σ d) γ0 with hγ
  have hγG : γ ∈ B.GV k r := by
    have := (Formalism.FourierDecayAlt.P.slice_membership k r 0).1 (U.hMat σ d) γ0 (hMat_det_ne σ d hd) hγ0
    exact this
  set f : B.SS k r → (Wq →L[ℂ] Wp) := fun p => theta0 S.z σ.symm p • D.orbIntegrand S γ F p with hf
  have hfm : AEStronglyMeasurable f S.μSS :=
    (theta0_meas S.z σ.symm).aestronglyMeasurable.smul (Dx3.integrand_aesm S hγG hFc)

  have hSS := muSS_eq S hN
  set P := (S.μW.prod (QN k r)).prod (S.μW'.prod (QN k r)) with hP
  have hfm' : AEStronglyMeasurable f (P.map (TN k r)) := by rw [← hSS]; exact hfm
  have hTm : AEMeasurable (TN k r) P := TN_meas.aemeasurable
  set P2 := (S.μW.prod S.μW').prod ((QN k r).prod (QN k r)) with hP2
  have hsw := Dx2.SL.measurePreserving_prod_middle_swap S.μW (QN k r) S.μW' (QN k r)
  set G2 : (Mt k r × Mt k r) × ((U.RC k r 0 × (G.UT r → ℂ)) × (U.RC k r 0 × (G.UT r → ℂ))) → (Wq →L[ℂ] Wp) :=
    fun x => f (TN k r ((x.1.1, x.2.1), (x.1.2, x.2.2))) with hG2
  have hG2e : G2 = (f ∘ TN k r) ∘ (Dx2.SL.swap4 (α := Mt k r) (β := U.RC k r 0 × (G.UT r → ℂ)) (γ := Mt k r)
      (δ := U.RC k r 0 × (G.UT r → ℂ))).symm := by
    funext x; rfl
  have hfTm : AEStronglyMeasurable (f ∘ TN k r) P := hfm'.comp_aemeasurable hTm
  have hG2m : AEStronglyMeasurable G2 P2 := by
    rw [hG2e]
    exact hfTm.comp_measurePreserving (hsw.symm _)

  have hae : ∀ᵐ x ∂(S.μW.prod S.μW'), Matrix.of x.1 ∈ UWset k r S.z ∧ Matrix.of x.2 ∈ UWset k r S.z' := by
    have b1 := (Measure.quasiMeasurePreserving_fst (μ := S.μW) (ν := S.μW')).ae (Dx2.OrbJ.ae_mem S.haarW)
    have b2 := (Measure.quasiMeasurePreserving_snd (μ := S.μW) (ν := S.μW')).ae (Dx2.OrbJ.ae_mem S.haarW')
    filter_upwards [b1, b2] with x h1 h2 using ⟨h1, h2⟩
  have hin := fun x : Mt k r × Mt k r => fun hx : Matrix.of x.1 ∈ UWset k r S.z ∧ Matrix.of x.2 ∈ UWset k r S.z' =>
    inner_int S z0 z0' hz hz' σ d hd γ0 hγ0 hrel F hFc M Bs hBs hBsf hdom x.1 x.2 hx.1 hx.2
  have hG2i : Integrable G2 P2 := by
    rw [integrable_prod_iff hG2m]
    refine ⟨?_, ?_⟩
    · filter_upwards [hae] with x hx using (hin x hx).1
    · refine Integrable.of_bound hG2m.norm.integral_prod_right' (M * (U.muXi k r 0 0 σ Bs).toReal) ?_
      filter_upwards [hae] with x hx
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hin x hx).2.2

  have hfTi : Integrable (f ∘ TN k r) P := by
    have := (hsw.symm _).integrable_comp_emb (MeasurableEquiv.measurableEmbedding _) (g := f ∘ TN k r)
    rw [← this, ← hG2e]; exact hG2i
  refine ⟨?_, ?_⟩
  · rw [hSS]; exact (integrable_map_measure hfm' hTm).2 hfTi
  · rw [hSS, integral_map hTm hfm']
    have e := (hsw.symm _).integral_comp' (f ∘ TN k r)
    change ∫ x, (f ∘ TN k r) x ∂P = _
    rw [← e]
    change ∫ x, G2 x ∂P2 = _
    rw [hP2, integral_prod G2 hG2i]
    refine integral_congr_ae ?_
    filter_upwards [hae] with x hx using (hin x hx).2.1

theorem orbJ_mMap (S : B.RealPlaceData k r Wp Wq) (hN : S.μN = D.muN k r) (hW1 : S.μW Set.univ = 1)
    (hW1' : S.μW' Set.univ = 1) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ)
    (hz : S.z = liftVec k r 0 z0) (hz' : S.z' = liftVec k r 0 z0')
    (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ a, d a ≠ 0) (γ0 : B.Mat k 0) (hγ0 : γ0 ∈ B.GV k 0)
    (hrel : C6.IsRelevant S (U.mMap k r 0 (U.hMat σ d) γ0))
    (w : Equiv.Perm (Fin (r + 1))) (dd : Fin (r + 1) → ℂ) (hdd : ∀ a, dd a ≠ 0)
    (hZw : Zhat k r S.z S.z' (U.mMap k r 0 (U.hMat σ d) γ0) = C2.monoP w dd)
    (hw : ∀ a : Fin r, w.symm a.castSucc = (σ a).castSucc)
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) (hFc : ContinuousOn F (B.GV k r)) (hr : 1 ≤ r) (R : ℝ)
    (hFs : ∀ g ∈ B.GV k r, F g ≠ 0 → B.gN g ≤ R) :
    D.orbJ S (U.mMap k r 0 (U.hMat σ d) γ0) (D.muR S (U.mMap k r 0 (U.hMat σ d) γ0) w) F =
      ∫ x, conjL S x.1 x.2 (U.PhiFun (s := 0) k 0 σ d S.z S.z' F (fun a => a.elim0)
        ((midB r 0 (Matrix.of x.1))⁻¹ * γ0 * midB r 0 (Matrix.of x.2))) ∂(S.μW.prod S.μW') := by
  obtain ⟨M, Bs, hBs, hBsf, hdom⟩ := slice_dom k r hr σ d hd F hFc R hFs
  obtain ⟨hint, heq⟩ := outer_int S hN hW1 hW1' z0 z0' hz hz' σ d hd γ0 hγ0 hrel F hFc M Bs hBs hBsf hdom
  have hγG : U.mMap k r 0 (U.hMat σ d) γ0 ∈ B.GV k r :=
    (Formalism.FourierDecayAlt.P.slice_membership k r 0).1 (U.hMat σ d) γ0 (hMat_det_ne σ d hd) hγ0
  have hw' : ∀ a : Fin r, w.symm a.castSucc = (σ.symm.symm a).castSucc := by simpa using hw
  have hnc := theta0_normCut S hγG hdd hZw σ.symm hw'
  have hex : ∃ θ, D.IsNormCut S (U.mMap k r 0 (U.hMat σ d) γ0) (D.muR S (U.mMap k r 0 (U.hMat σ d) γ0) w) θ ∧
      Integrable (fun p => θ p • D.orbIntegrand S (U.mMap k r 0 (U.hMat σ d) γ0) F p) S.μSS :=
    ⟨_, hnc, hint⟩
  unfold D.orbJ
  rw [dite_eq_left hex, Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq S _ _ hrel
    (Formalism.FourierDecayAlt.P.radial_measure_is_haar k r Wp Wq S _ w dd hγG hdd hZw) F hex.choose _ hex.choose_spec.1 hnc
    hex.choose_spec.2 hint, heq]

end outer

end Formalism.FourierDecayAlt.P.PBM
end
end

section

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBQ

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

theorem emb_mu_uni {k p ρ : ℕ} (ν : B.Mat k ρ) (V : Matrix (Fin p) (Fin p) ℂ) (a : Matrix (Fin p) (Fin (2 * ρ + k + 1)) ℂ)
    (b : Matrix (Fin p) (Fin p) ℂ) (c : Matrix (Fin (2 * ρ + k + 1)) (Fin p) ℂ) :
    U.embG k p ρ ν * U.muP k p ρ V * U.blk3 1 a b 0 1 c 0 0 1 =
      U.blk3 V (V * a) (V * b) 0 ν (ν * c) 0 0 (G.wMat p * Vᴴ⁻¹ * G.wMat p) := by
  unfold U.embG U.muP
  rw [Ux3.block3_mul, Ux3.block3_mul]
  congr 1 <;> simp

theorem upper_inj {p : ℕ} {u u' : G.UT p → ℂ} (h : G.upper u = G.upper u') : u = u' := by
  funext p
  have h1 := congrFun (congrFun h p.1.1) p.1.2
  simp only [G.upper, G.strictUpper, Matrix.add_apply, Matrix.of_apply, Matrix.one_apply_ne (ne_of_lt p.2),
    zero_add, dif_pos p.2] at h1
  exact h1

theorem kr_eq_integral_krI_psiR {k p ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (Bj : B.RealPlaceData k ρ Wp Wq) (B0 : B.RealPlaceData k (p + ρ) Wp Wq)
    (hW' : Bj.μW' Set.univ = 1) (hW0' : B0.μW' = Bj.μW'.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl))
    (hNj : Bj.μN = D.muN k ρ) (hN0 : B0.μN = D.muN k (p + ρ))
    (H : B.Mat k (p + ρ) → (Wq →L[ℂ] Wp)) (y₀ : B.Mat k (p + ρ)) :
    PBG.Kr B0 H y₀ = ∫ s, LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR s) ∂(LeftFubiniLemmas.muR (p := p) Bj) := by
  classical
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarW'
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Bj.haarN
  have := Formalism.FourierDecayAlt.P.Dx2.SplitF.sf_RC (k := k) p ρ

  set S : Set (LeftFubiniLemmas.XR k p ρ) := {s | LeftFubiniLemmas.GoodR Bj s} with hSdef
  have hSc : IsClosed S :=
    IsClosed.and ((Formalism.FourierDecayAlt.P.B6.isClosed_UWset k ρ Bj.z').preimage (continuous_fst.comp continuous_fst))
      ((Formalism.FourierDecayAlt.P.B6.isClosed_Nset k ρ).preimage (continuous_snd.comp continuous_fst))
  have hBS : BorelSpace (LeftFubiniLemmas.XR k p ρ) := by
    have : BorelSpace ((G.UT p → ℂ) × (Fin p → ℝ)) := Prod.borelSpace
    have : BorelSpace (U.RC k p ρ) := Prod.borelSpace
    have : BorelSpace (U.RC k p ρ × (G.UT p → ℂ)) := Prod.borelSpace
    have : BorelSpace (Mt k ρ × Mt k ρ) := Prod.borelSpace
    exact Prod.borelSpace
  have hSm : MeasurableSet S := hSc.measurableSet

  have hmp : MeasurePreserving (LeftFubiniLemmas.PsiR (k := k) (p := p) (ρ := ρ)) (LeftFubiniLemmas.muR Bj) (B0.μW'.prod B0.μN) := by
    have h := LeftFubiniLemmas.right_measure_preserving k p ρ Bj.z' Bj.μW' B0.μW' Bj.haarW' hW' hW0'
    unfold LeftFubiniLemmas.muR
    rw [hN0, hNj]
    exact h

  have hinj : Set.InjOn (LeftFubiniLemmas.PsiR (k := k) (p := p) (ρ := ρ)) S := by
    intro s hs s' hs' he
    have he1 := congrArg Prod.fst he
    have he2 := congrArg Prod.snd he
    have h11 : s.1.1 = s'.1.1 := by
      have := congrArg (Formalism.FourierDecayAlt.P.PBM.midMt p ρ rfl) he1
      simpa only [LeftFubiniLemmas.PsiR, Formalism.FourierDecayAlt.P.PBM.midMt_levMt] using this
    have hN : LeftFubiniLemmas.NR s = LeftFubiniLemmas.NR s' := Matrix.of.symm.injective he2
    obtain ⟨a, b, c, hRn⟩ : ∃ a b c, U.Rn k p ρ (LeftFubiniLemmas.rcAct (Matrix.of s.1.1) s.2.1) = U.blk3 1 a b 0 1 c 0 0 1 :=
      ⟨_, _, _, Formalism.FourierDecayAlt.P.Ux3.rn_eq _⟩
    obtain ⟨a', b', c', hRn'⟩ : ∃ a b c, U.Rn k p ρ (LeftFubiniLemmas.rcAct (Matrix.of s'.1.1) s'.2.1) = U.blk3 1 a b 0 1 c 0 0 1 :=
      ⟨_, _, _, Formalism.FourierDecayAlt.P.Ux3.rn_eq _⟩
    unfold LeftFubiniLemmas.NR at hN
    rw [hRn, hRn', emb_mu_uni, emb_mu_uni, Formalism.FourierDecayAlt.P.Ux3.block3_eq_iff] at hN
    obtain ⟨hU, hUa, hUb, -, hν, hνc, -, -, -⟩ := hN
    have hUu : IsUnit (G.upper s.2.2).det := by rw [Formalism.FourierDecayAlt.P.Ux3.det_upper]; exact isUnit_one
    have hνu : IsUnit (Matrix.of s.1.2 : B.Mat k ρ).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hs.2.1
    have hu : s.2.2 = s'.2.2 := upper_inj hU
    rw [← hU] at hUa hUb
    rw [← hν] at hνc
    have ha : a = a' := by
      have := congrArg (fun M => (G.upper s.2.2)⁻¹ * M) hUa
      simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUu, Matrix.one_mul] using this
    have hb : b = b' := by
      have := congrArg (fun M => (G.upper s.2.2)⁻¹ * M) hUb
      simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hUu, Matrix.one_mul] using this
    have hc : c = c' := by
      have := congrArg (fun M => (Matrix.of s.1.2 : B.Mat k ρ)⁻¹ * M) hνc
      simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hνu, Matrix.one_mul] using this
    have hR : LeftFubiniLemmas.rcAct (Matrix.of s.1.1) s.2.1 = LeftFubiniLemmas.rcAct (Matrix.of s'.1.1) s'.2.1 :=
      (Formalism.FourierDecayAlt.P.radical_parametrisation k p ρ).1 (by rw [hRn, hRn', ha, hb, hc])
    rw [← h11] at hR
    have hhu : IsUnit (Matrix.of s.1.1 : B.Mat k ρ).det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hs.1.1
    have h21 : s.2.1 = s'.2.1 := by
      have e1 := congrArg Prod.fst hR
      have e2 := congrArg Prod.snd hR
      simp only [LeftFubiniLemmas.rcAct] at e1 e2
      have e1' : (Matrix.of s.1.1 : B.Mat k ρ) * Matrix.of s.2.1.1 = Matrix.of s.1.1 * Matrix.of s'.2.1.1 := by
        ext v w; exact congrFun (congrFun e1 v) w
      have e3 := congrArg (fun M => (Matrix.of s.1.1 : B.Mat k ρ)⁻¹ * M) e1'
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hhu, Matrix.one_mul] at e3
      exact Prod.ext (by ext v w; exact congrFun (congrFun e3 v) w) e2
    have h12 : s.1.2 = s'.1.2 := by
      ext v w; exact congrFun (congrFun hν v) w
    exact Prod.ext (Prod.ext h11 h12) (Prod.ext h21 hu)
  have hres : (LeftFubiniLemmas.muR (p := p) Bj).restrict S = LeftFubiniLemmas.muR Bj :=
    Measure.restrict_eq_self_of_ae_mem (LeftFubiniLemmas.ae_goodR Bj)
  have hcont : Continuous (LeftFubiniLemmas.PsiR (k := k) (p := p) (ρ := ρ)) := by
    unfold LeftFubiniLemmas.PsiR
    exact ((Formalism.FourierDecayAlt.P.PBM.levMt_cont p ρ rfl).comp (continuous_fst.comp continuous_fst)).prodMk LeftFubiniLemmas.NR_cont
  have hPol : PolishSpace (LeftFubiniLemmas.XR k p ρ) := {}
  have : BorelSpace (Mt k (p + ρ) × Mt k (p + ρ)) := Prod.borelSpace
  have hemb : MeasurableEmbedding (fun s : S => LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ)) :=
    ContinuousOn.measurableEmbedding hSm hcont.continuousOn hinj
  rw [LeftFubiniLemmas.kr_eq_int]
  calc ∫ q, LeftFubiniLemmas.KrI B0 H y₀ q ∂(B0.μW'.prod B0.μN)
      = ∫ q, LeftFubiniLemmas.KrI B0 H y₀ q ∂((LeftFubiniLemmas.muR (p := p) Bj).map LeftFubiniLemmas.PsiR) := by rw [hmp.map_eq]
    _ = ∫ q, LeftFubiniLemmas.KrI B0 H y₀ q ∂((Measure.comap Subtype.val (LeftFubiniLemmas.muR (p := p) Bj)).map
          (fun s : S => LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ))) := by
        rw [show (fun s : S => LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ)) = LeftFubiniLemmas.PsiR ∘ Subtype.val from rfl,
          ← Measure.map_map hcont.measurable measurable_subtype_coe, map_comap_subtype_coe hSm, hres]
    _ = ∫ s : S, LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR (s : LeftFubiniLemmas.XR k p ρ)) ∂(Measure.comap Subtype.val (LeftFubiniLemmas.muR (p := p) Bj)) :=
        hemb.integral_map _
    _ = ∫ s, LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR s) ∂((Measure.comap Subtype.val (LeftFubiniLemmas.muR (p := p) Bj)).map
          (Subtype.val : S → LeftFubiniLemmas.XR k p ρ)) :=
        ((MeasurableEmbedding.subtype_coe hSm).integral_map (fun s => LeftFubiniLemmas.KrI B0 H y₀ (LeftFubiniLemmas.PsiR s))).symm
    _ = _ := by rw [map_comap_subtype_coe hSm, hres]

end Formalism.FourierDecayAlt.P.PBQ
end
end
