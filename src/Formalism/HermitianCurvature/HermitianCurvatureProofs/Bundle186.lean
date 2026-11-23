module

public import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
public import Formalism.HermitianCurvature.Bundle004
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.BFCell
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle083
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftMemMatrixAlgebra
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVnice
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVrad
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle122
public import Formalism.HermitianCurvature.StatementD
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSetting
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle173
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

@[expose] public section

section

open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBFV

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

section Pic

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem JF_mul_inv (Bs : B.RealPlaceData k r Wp Wq) (m : B.Mat k r → ℂ)
    (hm : ∀ p : B.SS k r, Bs.inSS p → ∀ g, m (B.sgs p g) = m g) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (h : B.Mat k r) : B.JF Bs (fun g => m g • F g) h = m h • B.JF Bs F h := by
  show ∫ p, JF.xiP Bs p • B.rho Bs p (fun g => m g • F g) h ∂Bs.μSS = m h • ∫ p, JF.xiP Bs p • B.rho Bs p F h ∂Bs.μSS
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [Formalism.FourierDecayAlt.P.B5.ae_inSS Bs] with p hp
  simp only [B.rho, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hm p hp h]
  exact smul_comm _ _ _

theorem JF_uInv (Bs : B.RealPlaceData k r Wp Wq) (ε : ℝ) (s : ℂ) {h : B.Mat k r} (hh : h ∈ JF.Om k r Bs.z Bs.z') :
    ∀ (w : List C.Letter) (x : Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)), (∀ e, JC.NiceCoef Bs ε (x e)) →
      ∀ e, B.JF Bs (KB.uInv s w x e) h = KB.uInv s w (fun e => B.JF Bs (x e) h) e
  | [], x, _, e => rfl
  | l :: w, x, hx, e => by
    rw [uInv_cons, uInv_cons]
    by_cases h0 : e 0 = 0
    · rw [if_pos h0, if_pos h0]
      exact JF_uInv Bs ε s hh w _ (fun e' => hx _) _
    · rw [if_neg h0, if_neg h0]
      generalize (if l.1 = true then s else (starRingEnd ℂ) s) = c
      have h1 := uInv_nice Bs ε s w (fun e' => x (Fin.cons 1 e')) (fun e' => hx _) (fun a => e a.succ)
      have h2 := uInv_nice Bs ε s w (fun e' => x (Fin.cons 0 e')) (fun e' => hx _) (fun a => e a.succ)
      have e1 := JCx2.bc_JF_add h1 (JCx2.mn_nice_smul c h2) hh
      simp only [Pi.add_def, Pi.smul_apply]
      rw [e1, JCx2.bc_JF_smul, JF_uInv Bs ε s hh w _ (fun e' => hx _),
        JF_uInv Bs ε s hh w _ (fun e' => hx _)]

end Pic

section Minor

variable {k r : ℕ}

theorem first_minor_cell_eq_coord {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') (hr : 0 < r)
    (c : Fin r → ℂ) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r)) (h1 : 1 < r + 2) :
    Dmin k r z z' (wCell k r (Fin.last r) c * g) ⟨1, h1⟩ = c ⟨0, hr⟩ := by
  obtain ⟨μ, _, rfl⟩ := (Formalism.FourierDecayAlt.P.TwoByOneBlock.UWb_iff g).1 (Rad.glev_last_uwb hg)
  have e : wCell k r (Fin.last r) c * B2.embWb k r μ = bigCell k r c μ := by
    rw [Rad.wCell_last_eq, ← (Formalism.FourierDecayAlt.P.bruhat_big_cell_factorization k r c μ).1]
  rw [e]
  have hmin := (big_cell_minors_holds k r z z' c μ hz hz').1 ⟨1, by omega⟩
  have hl : (⟨(⟨1, by omega⟩ : Fin (r + 1)).val, by omega⟩ : Fin (r + 2)) = ⟨1, h1⟩ := Fin.ext rfl
  rw [hl] at hmin
  rw [hmin]
  have hs : (Finset.univ.filter fun a : Fin r => a.val < (⟨1, by omega⟩ : Fin (r + 1)).val) = {⟨0, hr⟩} := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro ha; exact Fin.ext (by simp at ha; omega)
    · rintro rfl; simp
  rw [Finset.prod_filter, ← Finset.prod_filter, hs, Finset.prod_singleton]

theorem first_minor_top_eq_zeta {z z' : Fin (2 * r + k + 1) → ℂ} (hr : r = 0) (c : Fin r → ℂ) (g : Mx k r) (h1 : 1 < r + 2) :
    Dmin k r z z' (wCell k r (Fin.last r) c * g) ⟨1, h1⟩ = P5.zeta k r z z' g := by
  subst hr
  have hw : wCell k 0 (Fin.last 0) c = 1 := Formalism.FourierDecayAlt.P.Qx6.wCell_zero c
  rw [hw, one_mul, dmin_one]
  simp [P5.zeta, zetaL, fvec]

end Minor

section Rad

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem radPic_wave (Bs : B.RealPlaceData k r Wp Wq) (ε : ℝ) (s : ℂ) (w : List C.Letter)
    (x : Ix (Fin w.length) → B.Mat k r → (Wq →L[ℂ] Wp)) (hx : ∀ e, JC.NiceCoef Bs ε (x e))
    (Φ : Ix (Fin w.length) → RadSp k r Bs.z Bs.z' Bs.π Bs.π')
    (hΦ : ∀ e, ∀ y ∈ DomR k r Bs.z Bs.z',
      (Φ e : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = resG k r (Fin.last r) (B.JF Bs (x e)) y.1 y.2)
    (m : (Fin r → ℂ) → Mx k r → ℂ) (h1 : 1 < r + 2)
    (hm : ∀ y ∈ DomR k r Bs.z Bs.z', m y.1 y.2 = fsv s (Dmin k r Bs.z Bs.z' (wCell k r (Fin.last r) y.1 * y.2) ⟨1, h1⟩))
    (Wv Wv' : Module.End ℂ (RadSp k r Bs.z Bs.z' Bs.π Bs.π')) (hW : multiplicationOperator Wv m) :
    ∀ e, ∀ y ∈ DomR k r Bs.z Bs.z', (act (Vw (mkP Wv Wv') s (D.positionted w)) Φ e : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 =
      resG k r (Fin.last r) (B.JF Bs (KB.waveG Bs s w x e)) y.1 y.2 := by
  intro e y hy
  have hGV : wCell k r (Fin.last r) y.1 * y.2 ∈ B.GV k r := by
    rw [Rad.wCell_last_eq]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (big_cell_mem_holds _ _ _ 1 hy.1 (by simp)) hy.2.1.1
  have hh : wCell k r (Fin.last r) y.1 * y.2 ∈ JF.Om k r Bs.z Bs.z' :=
    ⟨hGV, Rad.wCell_mem_omPlus Bs.z_mem Bs.z'_mem hy.1 hy.2.1 hy.2.2⟩
  set h := wCell k r (Fin.last r) y.1 * y.2 with hhdef
  rw [Vw, act_mul, act_io]
  change (Wv (act (UUiw s (D.positionted w)) Φ e) : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 = _
  rw [hW, act_UUiw]
  let ev : RadSp k r Bs.z Bs.z' Bs.π Bs.π' →ₗ[ℂ] (Wq →L[ℂ] Wp) :=
    { toFun := fun Ψ => (Ψ : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hev : ((KB.uInv s w Φ e : RadSp k r Bs.z Bs.z' Bs.π Bs.π') : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2 =
      KB.uInv s w (fun e => (Φ e : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2) e := uInv_map ev s w Φ e
  rw [hev]
  have hfun : (fun e => (Φ e : Fn k r (Wq →L[ℂ] Wp)) y.1 y.2) = fun e => resG k r (Fin.last r) (B.JF Bs (x e)) y.1 y.2 :=
    funext fun e => hΦ e y hy
  rw [hfun]
  simp only [resG]
  set gau : ℂ := ((∏ a : Fin r, (if a.val < (Fin.last r).val then ‖y.1 a‖ ^ (Mdim k r a - 1) else 1) : ℝ) : ℂ)
    with hgau
  have hsm := uInv_map ((gau • LinearMap.id : (Wq →L[ℂ] Wp) →ₗ[ℂ] (Wq →L[ℂ] Wp))) s w (fun e => B.JF Bs (x e) h) e
  simp only [LinearMap.smul_apply, LinearMap.id_apply] at hsm
  rw [← hsm]
  unfold KB.waveG
  rw [JF_mul_inv Bs (fun g => P5.fsv s (Dmin k r Bs.z Bs.z' g ⟨1, h1⟩))
    (fun p hp g => by rw [Formalism.FourierDecayAlt.P.BigCellZetaMinors.dmin_sgs Bs hp g]),
    JF_uInv Bs ε s hh w x hx e, hm y hy, smul_comm]

end Rad

end Formalism.FourierDecayAlt.P.PBFV
end
end

section

namespace Formalism.FourierDecayAlt.P.CutBP.PolTop

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem orbital_integrand_linear {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (a b : ℂ) (p : B.SS k r) :
    D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g) p =
      a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p := by

  unfold D.orbIntegrand B.rho
  ext x
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    map_add, map_smul, smul_add]
  rw [smul_comm (B.xiTau Bs (1, 1) p) a, smul_comm (B.xiTau Bs (1, 1) p) b]

theorem orbJ_linear_of_decay : ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (γ : B.Mat k r)
    (w : Equiv.Perm (Fin (r + 1))) (d : Fin (r + 1) → ℂ) (A : ℝ),
    γ ∈ B.GV k r → (∀ a, d a ≠ 0) → Zhat k r Bs.z Bs.z' γ = C2.monoP w d →
    0 < Gf k r Bs.z Bs.z' γ → C6.IsRelevant Bs γ →
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF →
      AEStronglyMeasurable (D.orbIntegrand Bs γ H₁) Bs.μSS →
      AEStronglyMeasurable (D.orbIntegrand Bs γ H₂) Bs.μSS →
      (∀ p, Bs.inSS p → ‖H₁ (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)) →
      (∀ p, Bs.inSS p → ‖H₂ (B.sgs p γ)‖ ≤ cF * B.gN (B.sgs p γ) ^ (-A)) → ∀ a b : ℂ,
      D.orbJ Bs γ (D.muR Bs γ w) (fun g => a • H₁ g + b • H₂ g) =
        a • D.orbJ Bs γ (D.muR Bs γ w) H₁ + b • D.orbJ Bs γ (D.muR Bs γ w) H₂ := by
  obtain ⟨c₃, hc₃⟩ := Formalism.FourierDecayAlt.P.PBE.orbJ_dom
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ Bs γ w d A hγ hd hZ hpos hrel hA H₁ H₂ cF hcF hm₁ hm₂ hb₁ hb₂ a b
  obtain ⟨θ, maj, hθ, hmaj, hdom⟩ := hc₃ k r Wp Wq Bs γ w d A hγ hd hZ hpos hA
  have hG : Formalism.FourierDecayAlt.P.Dx2.Rad.Good Bs γ w d := ⟨Formalism.FourierDecayAlt.P.Dx2.Rad.exists_rho Bs hγ hpos hd hZ,
    Formalism.FourierDecayAlt.P.Dx2.Rad.u_inj Bs hγ hpos hd hZ, fun ρ hρ => Formalism.FourierDecayAlt.P.Dx2.Rad.u_lstg Bs hγ hpos hd hZ hρ⟩
  have hR := Formalism.FourierDecayAlt.P.Dx2.Rad.haar_good Bs hγ hd hG
  have hInt : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), 0 ≤ c →
      AEStronglyMeasurable (D.orbIntegrand Bs γ G) Bs.μSS →
      (∀ p, Bs.inSS p → ‖G (B.sgs p γ)‖ ≤ c * B.gN (B.sgs p γ) ^ (-A)) →
      Integrable (fun p => θ p • D.orbIntegrand Bs γ G p) Bs.μSS := fun G c hc hGm hGb =>
    Integrable.mono' (hmaj.const_mul c) (hθ.1.aestronglyMeasurable.smul hGm) (hdom G c hc hGb)
  have hEq : ∀ (G : B.Mat k r → (Wq →L[ℂ] Wp)) (c : ℝ), 0 ≤ c →
      AEStronglyMeasurable (D.orbIntegrand Bs γ G) Bs.μSS →
      (∀ p, Bs.inSS p → ‖G (B.sgs p γ)‖ ≤ c * B.gN (B.sgs p γ) ^ (-A)) →
      D.orbJ Bs γ (D.muR Bs γ w) G = ∫ p, θ p • D.orbIntegrand Bs γ G p ∂Bs.μSS := by
    intro G c hc hGm hGb
    have hex : ∃ θ', D.IsNormCut Bs γ (D.muR Bs γ w) θ' ∧
        Integrable (fun p => θ' p • D.orbIntegrand Bs γ G p) Bs.μSS := ⟨θ, hθ, hInt G c hc hGm hGb⟩
    unfold D.orbJ
    rw [dif_pos hex]
    exact Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq Bs γ (D.muR Bs γ w) hrel hR G _ θ hex.choose_spec.1 hθ
      hex.choose_spec.2 (hInt G c hc hGm hGb)
  have hlin : D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g) =
      fun p => a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p :=
    funext fun p => orbital_integrand_linear Bs γ H₁ H₂ a b p
  have hm : AEStronglyMeasurable (D.orbIntegrand Bs γ (fun g => a • H₁ g + b • H₂ g)) Bs.μSS := by
    rw [hlin]
    exact (hm₁.const_smul a).add (hm₂.const_smul b)
  have hc' : 0 ≤ (‖a‖ + ‖b‖) * cF := mul_nonneg (by positivity) hcF
  have hb : ∀ p, Bs.inSS p → ‖a • H₁ (B.sgs p γ) + b • H₂ (B.sgs p γ)‖ ≤
      (‖a‖ + ‖b‖) * cF * B.gN (B.sgs p γ) ^ (-A) := by
    intro p hp
    have h1 := hb₁ p hp
    have h2 := hb₂ p hp
    calc ‖a • H₁ (B.sgs p γ) + b • H₂ (B.sgs p γ)‖ ≤ ‖a‖ * ‖H₁ (B.sgs p γ)‖ + ‖b‖ * ‖H₂ (B.sgs p γ)‖ := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_smul, norm_smul]
      _ ≤ ‖a‖ * (cF * B.gN (B.sgs p γ) ^ (-A)) + ‖b‖ * (cF * B.gN (B.sgs p γ) ^ (-A)) :=
          add_le_add (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
      _ = (‖a‖ + ‖b‖) * cF * B.gN (B.sgs p γ) ^ (-A) := by ring
  have i₁ := hInt H₁ cF hcF hm₁ hb₁
  have i₂ := hInt H₂ cF hcF hm₂ hb₂
  rw [hEq _ _ hc' hm hb, hEq H₁ cF hcF hm₁ hb₁, hEq H₂ cF hcF hm₂ hb₂, hlin]
  have e : (fun p => θ p • (a • D.orbIntegrand Bs γ H₁ p + b • D.orbIntegrand Bs γ H₂ p)) =
      fun p => a • (θ p • D.orbIntegrand Bs γ H₁ p) + b • (θ p • D.orbIntegrand Bs γ H₂ p) := by
    funext p
    rw [smul_add, smul_comm (θ p) a, smul_comm (θ p) b]
  have j₁ : Integrable (fun p => a • (θ p • D.orbIntegrand Bs γ H₁ p)) Bs.μSS := i₁.smul a
  have j₂ : Integrable (fun p => b • (θ p • D.orbIntegrand Bs γ H₂ p)) Bs.μSS := i₂.smul b
  rw [e, integral_add j₁ j₂, integral_smul, integral_smul]

theorem vector_valued_orbital_linear : ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (q : C.LPt) (A : ℝ),
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    ∀ (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)) (cF : ℝ), 0 ≤ cF →
      ContinuousOn H₁ (B.GPos Bs) → ContinuousOn H₂ (B.GPos Bs) →
      (∀ g ∈ B.GPos Bs, ‖H₁ g‖ ≤ cF * B.gN g ^ (-A)) → (∀ g ∈ B.GPos Bs, ‖H₂ g‖ ≤ cF * B.gN g ^ (-A)) →
      ∀ a b : ℂ, D.vecV Bs ν' m₀ (fun g => a • H₁ g + b • H₂ g) q =
        a • D.vecV Bs ν' m₀ H₁ q + b • D.vecV Bs ν' m₀ H₂ q := by
  obtain ⟨c₃, hc₃⟩ := orbJ_linear_of_decay
  refine ⟨c₃, ?_⟩
  intro k r Wp Wq _ _ _ _ Bs ν' m₀ q A hA H₁ H₂ cF hcF hc₁ hc₂ hb₁ hb₂ a b
  unfold D.vecV
  by_cases h : D.IsLocPt q (r + 1) ∧ 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r q
  · simp only [dif_pos h]
    by_cases h' : ∃ γ ∈ B.GV k r, Zhat k r Bs.z Bs.z' γ = D.ptMatN q (r + 1) ∧ D.IsDFrame Bs ν' m₀ γ
    · simp only [dif_pos h']
      have hγ := h'.choose_spec.1
      have hZ := h'.choose_spec.2.1
      have hGq := Formalism.FourierDecayAlt.P.ptG_spec k r Bs.z Bs.z' q h'.choose h.1 hZ
      have hpos : 0 < Gf k r Bs.z Bs.z' h'.choose := hGq ▸ h.2
      obtain ⟨hmono, hd⟩ := Formalism.FourierDecayAlt.P.Dx2.VV.ptMatN_monoP' q (r + 1) h.1.2 h.1.1
      have hrel := Formalism.FourierDecayAlt.P.relevant_points_holds k r Wp Wq Bs q h'.choose h.1 hγ hZ
      have horb : ∀ p, Bs.inSS p → B.sgs p h'.choose ∈ B.GPos Bs := fun p hp =>
        ⟨Formalism.FourierDecayAlt.P.B7.sgs_mem Bs hp hγ, by rw [Formalism.FourierDecayAlt.P.JCx1.needs.gf_sgs Bs hp]; exact hpos⟩
      exact hc₃ k r Wp Wq Bs h'.choose _ _ A hγ hd (hZ.trans hmono) hpos hrel hA H₁ H₂ cF hcF
        (Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb hc₁) (Formalism.FourierDecayAlt.P.PBE.integrand_aesm' Bs horb hc₂)
        (fun p hp => hb₁ _ (horb p hp)) (fun p hp => hb₂ _ (horb p hp)) a b
    · simp only [dif_neg h']
      simp
  · simp only [dif_neg h]
    simp

end

end Formalism.FourierDecayAlt.P.CutBP.PolTop

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace


end

end Formalism.FourierDecayAlt.P.CutBP
end

section

namespace Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity

open MeasureTheory
open scoped ContDiff

def EllRegBridge : Prop := ZetaZeros.D.EllReg.Internal → EllRegW

section bridge

variable {d : ℕ}

noncomputable abbrev brT (d : ℕ) : ZetaZeros.D.EllReg.E d ≃L[ℝ] (Fin d → ℝ) := EuclideanSpace.equiv (Fin d) ℝ

lemma brT_ev (j : Fin d) : brT d (ZetaZeros.D.EllReg.ev j) = Pi.single j 1 := by
  unfold ZetaZeros.D.EllReg.ev
  rfl

lemma dw_comp_brT (w : List (Fin d)) (f : (Fin d → ℝ) → ℂ) :
    ZetaZeros.D.EllReg.dw w (f ∘ brT d) = pdc w f ∘ brT d := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    funext x
    show fderiv ℝ (ZetaZeros.D.EllReg.dw w (f ∘ brT d)) x (ZetaZeros.D.EllReg.ev j) =
      fderiv ℝ (pdc w f) (brT d x) (Pi.single j 1)
    rw [ih, (brT d).comp_right_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, brT_ev]

noncomputable def brSys {ι : Type} (P : ι → SOp d) : ZetaZeros.D.EllReg.Sys d ι where
  ord i := (P i).ord
  a i n w := if h : n < (P i).ord + 1 then (P i).a ⟨n, h⟩ w ∘ brT d else 0

lemma brSys_tr {ι : Type} (P : ι → SOp d) (i : ι) (φ : (Fin d → ℝ) → ℂ) (x : ZetaZeros.D.EllReg.E d) :
    (brSys P).tr i (φ ∘ brT d) x = (P i).tr φ (brT d x) := by
  unfold ZetaZeros.D.EllReg.Sys.tr ZetaZeros.D.EllReg.trOp SOp.tr
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun w _ => ?_
  congr 1
  have e : (fun y => (brSys P).a i k w y * (φ ∘ brT d) y) =
      (fun y' => (P i).a k w y' * φ y') ∘ brT d := by
    funext y
    simp only [brSys, Function.comp_apply]
    rw [dif_pos (show (k : ℕ) < (P i).ord + 1 from k.isLt)]
    rfl
  rw [e, dw_comp_brT]
  rfl

lemma brSys_symb {ι : Type} (P : ι → SOp d) (i : ι) (x ξ : ZetaZeros.D.EllReg.E d) :
    (brSys P).symb i x ξ = (P i).symb (brT d x) (brT d ξ) := by
  unfold ZetaZeros.D.EllReg.Sys.symb SOp.symb
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [brSys, dif_pos (Nat.lt_succ_self _)]
  rw [mul_comm]
  rfl

end bridge

theorem elliptic_regularity_transfer_holds : EllRegBridge := by
  intro hI d ι _ P U u hU ha hu hweak hsymb
  have hHyp : ZetaZeros.D.EllReg.Hyp (brSys P) (brT d ⁻¹' U) (u ∘ brT d) := by
    refine ⟨hU.preimage (brT d).continuous, ?_, ?_, hu.comp (brT d).continuous.continuousOn (fun x hx => hx), ?_⟩
    · intro i n w
      simp only [brSys]
      split_ifs with h
      · exact (ha i ⟨n, h⟩ w).comp_continuousLinearMap ((brT d : ZetaZeros.D.EllReg.E d →L[ℝ] (Fin d → ℝ)))
      · exact contDiffOn_const
    · intro x hx ξ hξ
      have hξ' : brT d ξ ≠ 0 := fun h => hξ ((brT d).injective (h.trans (map_zero (brT d)).symm))
      obtain ⟨i, hi⟩ := hsymb (brT d x) hx (brT d ξ) hξ'
      exact ⟨i, by rw [brSys_symb]; exact hi⟩
    · intro i φ hφ hφc hφU
      have hψ : ContDiff ℝ ∞ (φ ∘ (brT d).symm) := hφ.comp (brT d).symm.contDiff
      have hψc : HasCompactSupport (φ ∘ (brT d).symm) := hφc.comp_homeomorph (brT d).symm.toHomeomorph
      have hψU : tsupport (φ ∘ (brT d).symm) ⊆ U := by
        intro y hy
        have hy' : y ∈ tsupport (φ ∘ (brT d).symm.toHomeomorph) := hy
        rw [tsupport_comp_eq_preimage φ (brT d).symm.toHomeomorph] at hy'
        have h1 := hφU hy'
        have h2 : brT d ((brT d).symm y) ∈ U := h1
        rwa [ContinuousLinearEquiv.apply_symm_apply] at h2
      have hφeq : φ = (φ ∘ (brT d).symm) ∘ brT d := by
        funext x
        simp
      have h1 := hweak i (φ ∘ (brT d).symm) hψ hψc hψU
      rw [hφeq]
      simp_rw [brSys_tr]
      rw [← h1]
      exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
        (fun y => u y * (P i).tr (φ ∘ (brT d).symm) y)
  have key := hI d ι (brSys P) (brT d ⁻¹' U) (u ∘ brT d) hHyp
  have h2 := key.comp_continuousLinearMap (((brT d).symm : (Fin d → ℝ) →L[ℝ] ZetaZeros.D.EllReg.E d))
  have e1 : (u ∘ brT d) ∘ (((brT d).symm : (Fin d → ℝ) →L[ℝ] ZetaZeros.D.EllReg.E d)) = u := by
    funext x
    show u (brT d ((brT d).symm x)) = u x
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have e2 : (((brT d).symm : (Fin d → ℝ) →L[ℝ] ZetaZeros.D.EllReg.E d)) ⁻¹' (brT d ⁻¹' U) = U := by
    ext x
    show brT d ((brT d).symm x) ∈ U ↔ x ∈ U
    rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [e1, e2] at h2
  exact h2

end Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity
end
