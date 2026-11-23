module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinVt
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle042
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeNC
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle018
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalModelPeriodLattices
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.KppLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowsGoodRed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.TermTieOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsAdd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTRph
import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle037
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle043
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.CarPinVt

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.Pf.Built Formalism.L2.SG.LocWSOf
  Formalism.L2.SG.Pf.CarrierT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem exists_nonneg_ptG_lptOf_eq_mul (v : InfinitePlace X.B.I.F) (κ : ℂ) (hκ : star κ = -κ) (TT : ℝ)
    (w : Point D.host.E (D.R.rS + 1)) :
    ∃ c : ℝ, 0 ≤ c ∧ Formalism.FourierDecayAlt.D.ptG TT D.R.rS (Bridge.lptOf ((X.B.I.φ v).comp X.ιE.symm.toRingHom) κ D.R.rS 0 w.1) =
      c * (‖RealObj.Dl (RealObj.ZhatO (ptC X v w)) (D.R.rS + 1)‖ ^ 2 -
        TT * ‖RealObj.Dl (RealObj.ZhatO (ptC X v w)) D.R.rS‖ ^ 2) := by
  set σ : D.host.E →+* ℂ := (X.B.I.φ v).comp X.ιE.symm.toRingHom
  set Y := RealObj.ZhatO (ptC X v w)
  have hY : ptC X v w = Matrix.diagonal (fun _ => 1) * Y * Matrix.diagonal (Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS) := by
    rw [← Formalism.L2.SG.Pf.CarrierTop.zhatO_eq_mul, Formalism.L2.SG.Pf.CarrierTop.zhatO_invol]
  have hM : Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1) =
      Matrix.diagonal (fun a : Fin (D.R.rS + 1) => Bridge.Af κ D.R.rS a * 1) * Y *
        Matrix.diagonal (fun b : Fin (D.R.rS + 1) => Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS b * Bridge.Bf κ D.R.rS b) := by
    rw [Bridge.ptMatN_lptOf σ κ D.R.rS hκ w]
    show Matrix.diagonal _ * ptC X v w * Matrix.diagonal _ = _
    rw [hY]
    ext a b
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    ring
  have hdet1 : (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1)).det =
      RealObj.Dl (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1)) (D.R.rS + 1) :=
    (Bridge.dl_top' _).symm
  have hdet2 : (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) D.R.rS).det =
      RealObj.Dl (Formalism.FourierDecayAlt.D.ptMatN (Bridge.lptOf σ κ D.R.rS 0 w.1) (D.R.rS + 1)) D.R.rS := by
    unfold RealObj.Dl; rw [dite_eq_left (Nat.le_succ _)]; rfl
  have hGd := Bridge.G_diag D.R.rS Y (fun a : Fin (D.R.rS + 1) => Bridge.Af κ D.R.rS a * 1)
    (fun b : Fin (D.R.rS + 1) => Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS b * Bridge.Bf κ D.R.rS b) TT
    (by simp [Bridge.Af, Bridge.Bf, Formalism.L2.SG.Pf.CarrierTop.sgnV])
  refine ⟨(‖∏ i : Fin D.R.rS, Bridge.Af κ D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i) * 1‖ *
    ‖∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.sgnV D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i) *
      Bridge.Bf κ D.R.rS (Fin.castLE (Nat.le_succ D.R.rS) i)‖) ^ 2, sq_nonneg _, ?_⟩
  unfold Formalism.FourierDecayAlt.D.ptG
  rw [hdet1, hdet2, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hM, hGd]

variable {θ : ℝ} (C : Choice X θ)

theorem rZero_carrierInT (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (fc : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS → (X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u (tauE X e j)))
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (hPRE : PtRepExists X u u' sc i0 i0') :
    RZero X (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)) u u'
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).T
      (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).fc ν' m₀ := by
  intro p w hp hng

  obtain ⟨v, hv0⟩ : ∃ v, ‖RealObj.Dl (RealObj.ZhatO (ptC X v w)) (D.R.rS + 1)‖ ^ 2 -
      Tw (D := D) u * Tw (D := D) u' * ‖RealObj.Dl (RealObj.ZhatO (ptC X v w)) D.R.rS‖ ^ 2 ≤ 0 := by
    by_cases hrep : ∃ γ, IsPtRep X u u' w γ
    · have h1 : ¬ ∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v := fun h => hng ⟨hrep, h⟩
      push_neg at h1
      obtain ⟨v, hv1⟩ := h1
      refine ⟨v, ?_⟩
      have hrepw : IsPtRep X u u' w (gamW X u u' w) := by
        unfold gamW; rw [dite_eq_left hrep]; exact hrep.choose_spec
      have hZ1 : ZX X u u' 1 (gamW X u u' w) v = RealObj.ZhatO (ptC X v w) := by
        rw [← hrepw v, Formalism.L2.SG.Pf.CarrierTop.zhatO_invol]
      change Gv (Tw (D := D) u) (Tw (D := D) u') (ZX X u u' D.host.rdE (gamW X u u' w) v) ≤ 0 at hv1
      unfold Gv at hv1
      have hcl : Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.last D.R.rS) = 1 := by
        simp [Formalism.L2.SG.Pf.CarrierTop.cS]
      have hGd := Bridge.G_diag D.R.rS (ZX X u u' 1 (gamW X u u' w) v)
        (Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE) (Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE)
        (Tw (D := D) u * Tw (D := D) u') (by rw [hcl]; simp)
      rw [Formalism.L2.SG.Pf.CarrierTop.zx_sc, hGd, hZ1] at hv1
      by_contra hpos
      push_neg at hpos
      have hrd := Formalism.MainNotions.LocalModelPeriodLattices.rdE_pos D
      have hne : (∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.castLE (Nat.le_succ D.R.rS) i)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => by
          simp [Formalism.L2.SG.Pf.CarrierTop.cS, hrd.ne']
      have hc : 0 < (‖∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.castLE (Nat.le_succ D.R.rS) i)‖ *
          ‖∏ i : Fin D.R.rS, Formalism.L2.SG.Pf.CarrierTop.cS D.R.rS D.host.rdE (Fin.castLE (Nat.le_succ D.R.rS) i)‖) ^ 2 :=
        pow_pos (mul_pos (norm_pos_iff.mpr hne) (norm_pos_iff.mpr hne)) 2
      have := mul_pos hc hpos
      linarith
    · by_contra hall
      push_neg at hall
      obtain ⟨γ, hγ, -⟩ := hPRE w (fun v => by have := hall v; unfold Gv; exact this)
      exact hrep ⟨γ, hγ⟩
  refine ⟨(tauE X e).symm v, Or.inr ?_⟩
  set j := (tauE X e).symm v with hj
  set σ : D.host.E →+* ℂ := (X.B.I.φ v).comp X.ιE.symm.toRingHom with hσ
  set gg : ℕ := D.host.g 0 * D.host.g 1 with hggdef
  set κ : ℂ := -Complex.I * (((gg : ℝ) / (2 * Real.pi) : ℝ) : ℂ) with hκ
  have hκstar : star κ = -κ := by
    rw [hκ, star_mul', star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal]; ring

  have hpt := hp
  unfold ptOfL Formalism.L2.SG.DataInst.ptOfList at hpt
  split_ifs at hpt with hPtL
  have hw1 : w.1 = (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.swap := by
    rw [← Option.some_inj.mp hpt]; rfl
  have hfst : (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.fst = p.map Prod.fst :=
    Formalism.L2.SG.DataInst.sign_list_fst D.R.rS 1 p
  have hblk : ∀ b ∈ p, 1 ≤ b.1 := by
    intro b hb
    have : b.1 ∈ (Formalism.L2.SG.DataInst.signPt D.R.rS p).map Prod.fst := by
      rw [hfst]; exact List.mem_map_of_mem hb
    obtain ⟨b', hb', hbb⟩ := List.mem_map.mp this
    rw [← hbb]; exact (hPtL.2 b' hb').1
  have hsum : 0 + (p.map Prod.fst).sum ≤ D.R.rS + 1 := by rw [← hfst, hPtL.1]; omega
  have hlt := Bridge.lptOf_toStd σ D.R.rS (gg : ℝ) p 0 hblk hsum
  have hemb : (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).σ j = σ := by
    show embE X e j = σ
    unfold embE
    rw [hj, Equiv.apply_symm_apply]
  have hstd : Formalism.FourierDecayAlt.D.toStd D.R.rS (gg : ℝ) 1
      (Formalism.FourierDecayAlt.C.loc ((sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).σ j) p) =
      Bridge.lptOf σ κ D.R.rS 0 w.1 := by
    rw [hemb, hw1]; exact hlt.symm
  obtain ⟨cc, hcc, hG⟩ := exists_nonneg_ptG_lptOf_eq_mul X v κ hκstar (((D.mem u).A.T : ℝ) * ((D.mem u').A.T : ℝ)) w
  unfold Formalism.FourierDecayAlt.JC.vecPlace Formalism.FourierDecayAlt.D.vecV
  rw [dite_eq_right]
  · simp [Formalism.FourierDecayAlt.B.hsVec]
    exact Or.inr rfl
  · rintro ⟨-, hpos⟩
    have hT := (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).hT j
    have hT1 : Formalism.QuantumDeterminants.Tz (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).G.k
        (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).G.r
        ((carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).T j).base.z = ((D.mem u).A.T : ℝ) :=
      hT.1
    have hT2 : Formalism.QuantumDeterminants.Tz (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).G.k
        (sOf (carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀)).G.r
        ((carrierInT X C u u' e he hv CA de de' l grid grid1 fc c ν' m₀ Θ TP A₀).T j).base.z' = ((D.mem u').A.T : ℝ) :=
      hT.2
    have hpos' : 0 < Formalism.FourierDecayAlt.D.ptG (((D.mem u).A.T : ℝ) * ((D.mem u').A.T : ℝ)) D.R.rS
        (Bridge.lptOf σ κ D.R.rS 0 w.1) := by
      convert hpos using 2
      all_goals first | rfl | exact (congrArg₂ (· * ·) hT1 hT2).symm | exact hstd.symm
    rw [hG] at hpos'
    have hpos := hpos'
    unfold Tw at hv0
    have := mul_nonpos_of_nonneg_of_nonpos hcc hv0
    linarith

end Formalism.L2.SG.Pf.Carrier.CarPinVt
end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppLoc

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.Pf.AllRowsRedKerA Formalism.L2.SG.Pf.KppRedW Formalism.L2.SG.Pf.KppFrameW Formalism.L2.SG.Pf.KppIdx

theorem ne_val {r : ℕ} {i j : Fin r} (h : i.1 ≠ j.1) : i ≠ j := fun e => h (congrArg Fin.val e)

theorem rv_inj {n : ℕ} {a b : Fin n} : rv a = rv b ↔ a = b :=
  ⟨fun h => by rw [← rv_rv a, h, rv_rv], fun h => h ▸ rfl⟩

theorem gram_of {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {u v : VA I} {P Q : Prop} [Decidable P] [Decidable Q]
    (h : hhat I u v - (if P then 1 else 0) ∈ Wq I w) (hPQ : P ↔ Q) :
    hhat I u v - (if Q then 1 else 0) ∈ Wq I w := by
  have e : (if P then (1 : I.E ⊗[I.F] Af I.F) else 0) = if Q then 1 else 0 := by
    by_cases hp : P
    · rw [if_pos hp, if_pos (hPQ.1 hp)]
    · rw [if_neg hp, if_neg (fun hq => hp (hPQ.2 hq))]
  rwa [e] at h

theorem gram_ne {I : AutInst} {w : HeightOneSpectrum (𝓞 I.E)} {u v : VA I} {Q : Prop} [Decidable Q]
    (h : hhat I u v ∈ Wq I w) (hQ : ¬ Q) : hhat I u v - (if Q then 1 else 0) ∈ Wq I w := by
  rwa [if_neg hQ, sub_zero]

variable {D : D7} (X : HidaSetting D)

theorem sg_hA (u v : VA X.B.I) : sg X.B.I (hA X.B.I u v) = hhat X.B.I v u := hhat_conj X.B.I u v

theorem fr_wt (i : Fin D.R.k) : fr X true (wI (hrD D) i) = X.bw i := by rw [fr_w]; rfl
theorem fr_wf (i : Fin D.R.k) : fr X false (wI (hrD D) i) = X.bwd (rv i) := by rw [fr_w]; rfl
theorem frd_wt (i : Fin D.R.k) : frd X true (wI (hrD D) i) = X.bwd i := by rw [frd_w]; rfl
theorem frd_wf (i : Fin D.R.k) : frd X false (wI (hrD D) i) = X.bw (rv i) := by rw [frd_w]; rfl

variable {w : HeightOneSpectrum (𝓞 X.B.I.E)}

theorem wq (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (h : ZMod' X.B.I X.B.g c) : c ∈ Wq X.B.I w := zmod_Wq hg h

theorem wqs (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal) {c : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}
    (h : ZMod' X.B.I X.B.g c) : sg X.B.I c ∈ Wq X.B.I w := zmod_Wq hg (zmod_sg h)

theorem xI_inj {a b : Fin D.R.rS} : xI (hrD D) a = xI (hrD D) b ↔ a = b :=
  ⟨fun h => Fin.ext (by have := congrArg Fin.val h; simpa [xI, wI, yI] using this), fun h => h ▸ rfl⟩
theorem wI_inj {a b : Fin D.R.k} : wI (hrD D) a = wI (hrD D) b ↔ a = b :=
  ⟨fun h => Fin.ext (by have := congrArg Fin.val h; simpa [xI, wI, yI] using this), fun h => h ▸ rfl⟩
theorem yI_inj {a b : Fin D.R.rS} : yI (hrD D) a = yI (hrD D) b ↔ a = b :=
  ⟨fun h => Fin.ext (by have := congrArg Fin.val h; simpa [xI, wI, yI] using this), fun h => h ▸ rfl⟩

theorem gram (ob : Bool) (hg : ((X.B.g : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal)
    (hew : X.ew - (if ob then 1 else 0) ∈ Wq X.B.I w) (hsew : sg X.B.I X.ew - (if ob then 0 else 1) ∈ Wq X.B.I w) :
    GramW w (fr X ob) (frd X ob) := by
  intro i j
  have sg_ite : ∀ (P : Prop) [Decidable P],
      sg X.B.I (if P then (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) else 0) = if P then 1 else 0 := by
    intro P _; split_ifs <;> simp
  rcases kind_cases (hrD D) i with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl | ⟨a, rfl⟩ <;>
  rcases kind_cases (hrD D) j with ⟨b, rfl⟩ | ⟨b, rfl⟩ | rfl | ⟨b, rfl⟩
  ·
    rw [dual_frame_isotropic, frame_isotropic]
    have h := wqs X hg ((X.gramIntegral b a).2.2)
    rw [map_sub, sg_hA, sg_ite] at h
    exact gram_of h (by rw [xI_inj]; exact eq_comm)
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    · rw [dual_frame_isotropic, fr_wf]; exact wq X hg ((X.weightVectorsIntegral (rv b)).2.2 a).2.2.2
    · rw [dual_frame_isotropic, fr_wt]; exact wq X hg ((X.weightVectorsIntegral b).2.2 a).2.1
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rw [dual_frame_isotropic, frame_anisotropic]; exact wq X hg (X.formsAtZero.2 a).2
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rw [dual_frame_isotropic, fr_y]; exact wq X hg (X.gramIntegral a (rv b)).2.1
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    · rw [frd_wf, frame_isotropic]; have := wqs X hg ((X.weightVectorsIntegral (rv a)).2.2 b).1; rwa [sg_hA] at this
    · rw [frd_wt, frame_isotropic]; have := wqs X hg ((X.weightVectorsIntegral a).2.2 b).2.2.1; rwa [sg_hA] at this
  ·
    cases ob
    · rw [frd_wf, fr_wf]
      simp only [Bool.false_eq_true, if_false] at hsew
      have h := wqs X hg (X.bw_dual (rv b) (rv a))
      rw [map_sub, sg_hA] at h
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl] at h ⊢
        have := add_mem h hsew
        convert this using 1; ring
      · rw [if_neg (fun h' => hab (rv_inj.1 h'.symm)), map_zero, sub_zero] at h
        exact gram_ne h (fun h' => hab (wI_inj.1 h'))
    · rw [frd_wt, fr_wt]
      simp only [if_true] at hew
      have h := wq X hg (X.bw_dual a b)
      by_cases hab : a = b
      · subst hab
        rw [if_pos rfl] at h ⊢
        change hhat X.B.I (X.bwd a) (X.bw a) - X.ew ∈ _ at h
        have := add_mem h hew
        convert this using 1; ring
      · rw [if_neg hab, sub_zero] at h
        exact gram_ne h (fun h' => hab (wI_inj.1 h'))
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    · rw [frd_wf, frame_anisotropic]; have := wqs X hg (X.weightVectorsIntegral (rv a)).1; rwa [sg_hA] at this
    · rw [frd_wt, frame_anisotropic]; have := wqs X hg (X.weightVectorsIntegral a).2.1; rwa [sg_hA] at this
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    · rw [frd_wf, fr_y]; have := wqs X hg ((X.weightVectorsIntegral (rv a)).2.2 (rv b)).2.1; rwa [sg_hA] at this
    · rw [frd_wt, fr_y]; have := wqs X hg ((X.weightVectorsIntegral a).2.2 (rv b)).2.2.2; rwa [sg_hA] at this
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rw [dual_frame_anisotropic, frame_isotropic, hhat_neg_left]
    refine neg_mem ?_
    have := wqs X hg (X.formsAtZero.2 b).1; rwa [sg_hA] at this
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    · rw [dual_frame_anisotropic, fr_wf, hhat_neg_left]; exact neg_mem (wq X hg (X.weightVectorsIntegral (rv b)).2.1)
    · rw [dual_frame_anisotropic, fr_wt, hhat_neg_left]; exact neg_mem (wq X hg (X.weightVectorsIntegral b).1)
  ·
    rw [dual_frame_anisotropic, frame_anisotropic, hhat_neg_left, if_pos rfl]
    have := neg_mem (wq X hg X.formsAtZero.1)
    convert this using 1
    show -hhat X.B.I X.z0 X.z0 - 1 = -(hA X.B.I X.z0 X.z0 + 1)
    rw [show hA X.B.I X.z0 X.z0 = hhat X.B.I X.z0 X.z0 from rfl]; ring
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rw [dual_frame_anisotropic, fr_y, hhat_neg_left]
    refine neg_mem ?_
    have := wqs X hg (X.formsAtZero.2 (rv b)).2; rwa [sg_hA] at this
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rw [frd_y, frame_isotropic]; exact wq X hg (X.gramIntegral (rv a) b).1
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    cases ob
    · rw [frd_y, fr_wf]; exact wq X hg ((X.weightVectorsIntegral (rv b)).2.2 (rv a)).2.2.1
    · rw [frd_y, fr_wt]; exact wq X hg ((X.weightVectorsIntegral b).2.2 (rv a)).1
  ·
    refine gram_ne ?_ (ne_val (by simp [xI, wI, yI, zI] <;> omega))
    rw [frd_y, frame_anisotropic]; exact wq X hg (X.formsAtZero.2 (rv a)).1
  ·
    rw [frd_y, fr_y]
    exact gram_of (wq X hg (X.gramIntegral (rv a) (rv b)).2.2) (by rw [rv_inj, yI_inj])

end Formalism.L2.SG.Pf.KppLoc
end
end

section

noncomputable section

open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.AllRowsDcount

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.HidaSetting Formalism.L2.SG.AllRowsOf Formalism.L2.SG.Pf.AllRowsAdd

variable {D : D7} (X : HidaSetting D)

theorem reT_rph (S : Set (Tup2 D)) : (ReT X S).comp X.Rph = X.Rph.comp (ReT X S) := by
  refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun x => ?_
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_inner_left,
    X.Rph_spec, X.Rph_spec]
  congr 1
  funext g
  rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
    reT_comm]

theorem HH_eq_VT (t : Tup2 D) :
    Formalism.L2.SG.RowsDef.HH X.B.I X.B.μf X.B.fund (ReT X {t}) X.Rph = Formalism.L2.SG.Pf.RowsGoodRed.VT X t := by
  have hPE : (ReT X {t}).comp X.B.Re = ReT X {t} := by
    rw [← reT_univ' X, reT_inter, Set.inter_univ]
  have hEP : X.B.Re.comp (ReT X {t}) = ReT X {t} := by
    rw [← reT_univ' X, reT_inter, Set.univ_inter]
  have hPP : (ReT X {t}).comp (ReT X {t}) = ReT X {t} := by
    rw [reT_inter, Set.inter_self]
  have hR := reT_rph X {t}
  apply le_antisymm
  · rintro v ⟨y, rfl⟩
    refine ⟨⟨ReT X {t} y, ?_⟩, ?_⟩
    · show X.B.Re (X.Rph (ReT X {t} y)) = ReT X {t} (X.Rph y)
      have := congrArg (fun L => L y) hR
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [← this]
      have := congrArg (fun L => L (X.Rph y)) hEP
      simpa only [ContinuousLinearMap.comp_apply] using this
    · show ReT X {t} (ReT X {t} (X.Rph y)) - ReT X {t} (X.Rph y) = 0
      have := congrArg (fun L => L (X.Rph y)) hPP
      simp only [ContinuousLinearMap.comp_apply] at this
      rw [this, sub_self]
  · rintro v ⟨⟨y, hy⟩, hv⟩
    have hv' : ReT X {t} v = v := by
      have : ReT X {t} v - v = 0 := hv
      exact sub_eq_zero.1 this
    refine ⟨y, ?_⟩
    show ReT X {t} (X.Rph y) = v
    have hy' : X.B.Re (X.Rph y) = v := hy
    rw [← hv', ← hy']
    have := congrArg (fun L => L (X.Rph y)) hPE
    simp only [ContinuousLinearMap.comp_apply] at this
    exact this.symm

theorem dcountEq_holds (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D) : Formalism.L2.SG.Pf.RowsGoodRed.DcountEq X := by
  intro t _ _
  have hint := Formalism.L2.SG.Pf.RowDictPf.hint_of_gap X hG
  have hB := Formalism.L2.SG.Closed.RowsBij_holds X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec (eT X {t})
    (ReT X {t}) (reT_spec X (etInt_holds X) {t}) X.B.H X.B.σ X.dv X.B.w (fun v => (X.ds v).2.2.1)
    (fun v => (X.ds v).2.2.2.1) (Formalism.L2.SG.EvalTRph.isFdeg_dv X) (fun v => (X.low v).1) hint X.Rph X.Rph_spec
    X.B.Hs X.B.σs X.B.tens X.B.tens_spec
  delta dimX
  rw [← Formalism.L2.SG.RowsDef.finrank_HH_eq_Dcount hB.1 hB.2, HH_eq_VT]

end Formalism.L2.SG.Pf.AllRowsDcount
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X}

theorem ooIntAll_of (hWD : Formalism.L2.SG.WuDecay.WuDecay X) (w w' : D.what₂.Word) :
    OOIntAll X w w' (X.Fu w) (X.Fu w') (Y.what₂ w) (Y.what₂ w') :=
  Formalism.L2.SG.Closed.OOIntAllC_outright D X Y w w'
    (Formalism.L2.SG.Closed.FoldOKC_outright D X Y w (Formalism.L2.SG.Closed.level_subgroup_properties X) hWD)
    (Formalism.L2.SG.Closed.FoldOKC_outright D X Y w' (Formalism.L2.SG.Closed.level_subgroup_properties X) hWD)
    (Formalism.L2.SG.Pf.fundExistsC_holds D X Y w w')

variable {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (_root_.Formalism.L2.SG.PackageTie2.sOf hF))

theorem pvalForm_holds (hWD : Formalism.L2.SG.WuDecay.WuDecay X) : ∃ A : AmpDat X, PvalForm W hI A :=
  pvalForm_exists_oi W hI (ooIntAll_of hWD) (Formalism.L2.SG.Pf.FibreEq.FibreCountEq_holds hF)

end Formalism.L2.SG.Pf.KernelOfEmbedding
end
end
