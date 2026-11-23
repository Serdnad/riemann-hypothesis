module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle062
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle056
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle055
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle063
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle139
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle125
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle029
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelCoordinatesCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle143
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle145
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellMulVecBasis
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RightSingleRule.PatEntryZero
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaFiniteOfHaar
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle144
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvTr

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem dZb_sub {f g : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℝ f w) (hg : DifferentiableAt ℝ g w) :
    NF.dZb (fun x => f x - g x) w = NF.dZb f w - NF.dZb g w := by
  simp only [NF.dZb]
  rw [show (fun x => f x - g x) = f - g from rfl, (hf.hasFDerivAt.sub hg.hasFDerivAt).fderiv]
  simp only [ContinuousLinearMap.sub_apply]
  ring

theorem dzQ_one (P : M.Par) (hTT : 0 ≤ P.TT) : dzQ P (1 : MA.SmQ P.r P.TT) = 0 := by
  have hev : (MA.DQ P).ev M.vz 1 = 0 := by
    apply Subtype.ext
    funext q
    show MA.coordE M.vz q.1 * MA.wirt M.vz (MA.ext ((1 : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ)) q.1 = 0
    have hloc : MA.ext (1 : MA.Qp P.r P.TT → ℂ) =ᶠ[nhds q.1] fun _ => (1 : ℂ) := by
      filter_upwards [(MA.Qset_open P.r P.TT).mem_nhds q.2] with x hx
      simp [MA.ext, hx]
    simp [MA.wirt, hloc.fderiv_eq]
  simp only [dzQ, MA.DAlg.dzP, MA.DAlg.mkP]
  show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vz)) ((MA.DQ P).ev M.vz 1) = 0
  rw [hev, map_zero]

theorem dzbQ_one (P : M.Par) (hTT : 0 ≤ P.TT) : dzbQ P (1 : MA.SmQ P.r P.TT) = 0 := by
  have hev : (MA.DQ P).ev M.vzb 1 = 0 := by
    apply Subtype.ext
    funext q
    show MA.coordE M.vzb q.1 * MA.wirt M.vzb (MA.ext ((1 : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ)) q.1 = 0
    have hloc : MA.ext (1 : MA.Qp P.r P.TT → ℂ) =ᶠ[nhds q.1] fun _ => (1 : ℂ) := by
      filter_upwards [(MA.Qset_open P.r P.TT).mem_nhds q.2] with x hx
      simp [MA.ext, hx]
    simp [MA.wirt, hloc.fderiv_eq]
  simp only [dzbQ, MA.DAlg.dzbP, MA.DAlg.mkP]
  show (MA.DQ P).mulOp ((MA.DQ P).inv ((MA.DQ P).x M.vzb)) ((MA.DQ P).ev M.vzb 1) = 0
  rw [hev, map_zero]

theorem actA_ggiA (P : M.Par) (g : M.Ty P → MA.SmQ P.r P.TT) (ρ : M.Ty P) :
    MA.actA P (MA.ggiA P (MA.DQ P)) g ρ = mulQ P ((MA.DQ P).ggiP P.TT) (g ρ) := by
  simp only [MA.actA, MA.ggiA, MA.sc, mulQ, Matrix.scalar_apply]
  refine (Finset.sum_eq_single ρ ?_ ?_).trans ?_
  · intro b _ hb
    simp [Matrix.diagonal, Ne.symm hb]
    rfl
  · intro h
    exact absurd (Finset.mem_univ ρ) h
  · simp [Matrix.diagonal]
    rfl

theorem curvTr_core
    (hmod : ∀ (P : M.Par) (ρ : M.Ty P) (ζ : ℂ), ζ ∈ Ann P →
      NF.dZb (modA P ρ) ζ = -(((M.aC P ρ * P.TT : ℝ) : ℂ)) / ((Complex.normSq ζ : ℂ) - (P.TT : ℂ)) ^ 2) :
    GTCCurvTr := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e he hK A B hAB hC hBA hcurv ρ ζ hζ
  have hTT : 0 ≤ P.TT := tt_nonneg_of_hyp hyp
  have hev : ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT),
      ((trR P Bs e Φ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q :=
    fun Φ σ q => SSTr.trR_apply P Bs hyp.1 hyp.2.1 e he Φ σ q
  have tsub : ∀ (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT),
      ((trR P Bs e (Φ - Ψ) σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        ((trR P Bs e Φ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q -
          ((trR P Bs e Ψ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q := by
    intro Φ Ψ σ q
    rw [hev, hev, hev, Submodule.coe_sub, sub_eq_add_neg, ← neg_one_smul ℂ (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)),
      VLem.rawR_add, VLem.rawR_smul]
    simp [sub_eq_add_neg]
  have tsmul : ∀ (c : ℂ) (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT),
      ((trR P Bs e (c • Φ) σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
        c * ((trR P Bs e Φ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q := by
    intro c Φ σ q
    rw [hev, hev, Submodule.coe_smul, VLem.rawR_smul]
    rfl
  obtain ⟨Φ₀, hΦ₀, -⟩ := SSTr.exists_tr P Bs hyp.1 hyp.2.1 e he (fun _ => (1 : MA.SmQ P.r P.TT))
  have hAs := (hAB ρ).1
  have hBs := (hAB ρ).2
  have hΨ : trR P Bs e ((d.κ (dTy P ρ)).1 Φ₀) ρ = 1 := by
    rw [hK, actA_kap, hΦ₀]
    simp [dTy]
  have hN : trR P Bs e (d.L.nab.1 ((d.κ (dTy P ρ)).1 Φ₀)) ρ = fnZ P (A ρ) := by
    rw [(hC _ ρ).1, hΨ, dzQ_one P hTT, zero_add, mul_one]
  have hS : trR P Bs e (d.L.nabs.1 ((d.κ (dTy P ρ)).1 Φ₀)) ρ = fnZ P (B ρ) := by
    rw [(hC _ ρ).2, hΨ, dzbQ_one P hTT, neg_zero, zero_add, mul_one]
  have hSN : trR P Bs e (d.L.nabs.1 (d.L.nab.1 ((d.κ (dTy P ρ)).1 Φ₀))) ρ =
      -dzbQ P (fnZ P (A ρ)) + fnZ P (B ρ) * fnZ P (A ρ) := by
    rw [(hC _ ρ).2, hN]
  have hNS : trR P Bs e (d.L.nab.1 (d.L.nabs.1 ((d.κ (dTy P ρ)).1 Φ₀))) ρ =
      dzQ P (fnZ P (B ρ)) + fnZ P (A ρ) * fnZ P (B ρ) := by
    rw [(hC _ ρ).1, hS]
  have hG : ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      trR P Bs e (d.L.GGi.1 Φ) ρ = mulQ P ((MA.DQ P).ggiP P.TT) (trR P Bs e Φ ρ) := by
    intro Φ
    rw [((GT.gauge_function_holds Wp Wq P Bs X d hyp e) Φ).2.2.2.2.2, actA_ggiA]
  have hc' : d.L.nabs.1 (d.L.nab.1 ((d.κ (dTy P ρ)).1 Φ₀)) - d.L.nab.1 (d.L.nabs.1 ((d.κ (dTy P ρ)).1 Φ₀)) =
      ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) • d.L.GGi.1 (d.L.GGi.1 ((d.κ (dTy P ρ)).1 Φ₀)) :=
    congrArg (fun x : Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') => x.1 Φ₀) (hcurv ρ)
  have hζQ : (((fun _ => (1 : ℂ)), ζ) : MA.E P.r) ∈ MA.Qset P.r P.TT := ⟨fun _ => one_ne_zero, hζ⟩
  have key := congrArg (fun Φ => ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) ⟨_, hζQ⟩) hc'
  rw [tsub, tsmul, hSN, hNS, hG, hG, hΨ] at key
  simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_neg, Pi.add_apply, Pi.mul_apply, Pi.neg_apply,
    mulQ_ggiP, Subalgebra.coe_one, Pi.one_apply, dzbQ_apply P hTT, dzQ_apply P hTT,
    fnZ_val P hAs, fnZ_val P hBs] at key
  have hz1 := wirt_fnZ_zb P hAs ⟨_, hζQ⟩
  have hz2 := wirtinger_derivative_fibre_function P hBs ⟨_, hζQ⟩
  dsimp only at hz1 hz2
  rw [hz1, hz2] at key
  have hAd : DifferentiableAt ℝ (A ρ) ζ := (hAs.contDiffAt ((ann_open P).mem_nhds hζ)).differentiableAt (by simp)
  have hmd : DifferentiableAt ℝ (modA P ρ) ζ :=
    ((modA_smooth P ρ hTT).contDiffAt ((ann_open P).mem_nhds hζ)).differentiableAt (by simp)
  have hBeq : B ρ =ᶠ[nhds ζ] fun w => star (A ρ w) := by
    filter_upwards [(ann_open P).mem_nhds hζ] with w hw
    exact hBA ρ w hw
  have hdZB : NF.dZ (B ρ) ζ = star (NF.dZb (A ρ) ζ) := by
    rw [Formalism.FourierDecayAlt.P5.HerB.dZ_eq, hBeq.fderiv_eq, ← Formalism.FourierDecayAlt.P5.HerB.dZ_eq]
    exact Formalism.FourierDecayAlt.P5.HerB.dZ_conj hAd
  change -NF.dZb (A ρ) ζ + B ρ ζ * A ρ ζ - (NF.dZ (B ρ) ζ + A ρ ζ * B ρ ζ) =
    ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) * (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ *
      (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ * 1)) at key
  rw [hdZB] at key
  have h2 : -NF.dZb (A ρ) ζ + B ρ ζ * A ρ ζ - (star (NF.dZb (A ρ) ζ) + A ρ ζ * B ρ ζ) =
      -(NF.dZb (A ρ) ζ + star (NF.dZb (A ρ) ζ)) := by ring
  have h4 : ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) * (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ *
      (((Complex.normSq ζ : ℂ) - (P.TT : ℂ))⁻¹ * 1)) =
      ((2 * M.aC P ρ * P.TT * ((Complex.normSq ζ - P.TT)⁻¹ * (Complex.normSq ζ - P.TT)⁻¹) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h2, h4] at key
  have h3 := congrArg Complex.re key
  rw [Complex.neg_re, Complex.add_re, Complex.star_def, Complex.conj_re, Complex.ofReal_re] at h3
  have hx : 0 < Complex.normSq ζ - P.TT := sub_pos.mpr hζ
  rw [dZb_sub hmd hAd, Complex.sub_re, re_dZb_modA P ρ hζ]
  have hw : (NF.dZb (A ρ) ζ).re = -(M.aC P ρ * P.TT) * ((Complex.normSq ζ - P.TT)⁻¹ * (Complex.normSq ζ - P.TT)⁻¹) := by
    linarith
  rw [hw]
  field_simp
  ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.CurvTr

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem curvature_trace_holds : GTCCurvTr := CurvTr.curvTr_core (fun P ρ ζ hζ => dZb_modA P ρ hζ)

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ

noncomputable section

theorem quadratic_transfer_identity : GQBridge := by
  intro Wp Wq _ _ _ _ _ _ P Bs hk X d hA e he hg Y a b Φ
  have hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' := hA.1
  have hz := hpl.2.1
  have hz' := hpl.2.2.1
  have hΦ : (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := Φ.2
  have hF : Gauge.FamR P Bs (fun _ => Qx8.Dp P.k P.r Bs.z Bs.z') (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) := by
    refine ⟨Qx5.isOpen_OpR P.k P.r Bs.z Bs.z', fun c _ => Qx8.Dp_dom P.k P.r Bs.z Bs.z', fun q => ?_, ?_, ?_⟩
    · exact (Gauge.GC.GT.sec_pt P Bs hpl q).1.2.2
    · exact NFx1.TC.radSp_fam hΦ
    · intro c hc
      exact Qx8.slice_FF hz hz' hΦ hc
  have h := hg (fun _ => Qx8.Dp P.k P.r Bs.z Bs.z') (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) hF Y a b
  funext ρ
  show MA.toSm P (Gauge.rawR P Bs.μsec e ((X.t (Y : ℂ) a b Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
      Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) =
    MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ')) ρ
  refine Eq.trans ?_ (h ρ)
  congr 1
  funext q
  unfold Gauge.rawR
  rw [X.t_apply (Y : ℂ) a b Φ _ (Gauge.GC.GT.sec_pt P Bs hpl q).1]
  rfl

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.GQ
end

section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.HeadLetterLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.Qx5

theorem nL_glev0 {k r j : ℕ} (hj : j + 1 ≤ r) (a : Fin j → ℂ) : LevelPointCoordinates.nL k r j hj a ∈ Q.Glev k r 0 :=
  ⟨SingleEntryHermitianProducts.nL_uh j hj a, fun b hb => absurd hb (by simp)⟩

theorem derivative_keeps_character {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r j : ℕ} (hj : j + 1 ≤ r)
    (z : Fin (2 * r + k + 1) → ℂ) {Dm : Set (Q.Mx k r)} (hD : IsOpen Dm)
    (hDm : ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ, LevelPointCoordinates.nL k r j hj a * g ∈ Dm)
    (p q : Fin (2 * r + k + 1)) (w : VS k r 0 Dm E)
    (hw : ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ a : Fin j → ℂ,
      (w : Q.Mx k r → E) (LevelPointCoordinates.nL k r j hj a * g) = psi k r z cStd (LevelPointCoordinates.nL k r j hj a) • (w : Q.Mx k r → E) g)
    (g : Q.Mx k r) (hg : g ∈ Q.Glev k r 0 ∩ Dm) (a : Fin j → ℂ) :
    ((PBG.E0 hD p q w : VS k r 0 Dm E) : Q.Mx k r → E) (LevelPointCoordinates.nL k r j hj a * g) =
      psi k r z cStd (LevelPointCoordinates.nL k r j hj a) • ((PBG.E0 hD p q w : VS k r 0 Dm E) : Q.Mx k r → E) g := by
  have hng : LevelPointCoordinates.nL k r j hj a * g ∈ Q.Glev k r 0 ∩ Dm :=
    ⟨Qx3.glev_mul (nL_glev0 hj a) hg.1, hDm g hg a⟩
  set c := psi k r z cStd (LevelPointCoordinates.nL k r j hj a) with hc
  have hG := Qx2.good_eh (E := E) (k := k) (r := r) (i := 0) hD (PBG.c0 p) (PBG.c0 q)
  simp only [PBG.position_level_zero_coord] at hG
  unfold PBG.E0
  rw [ev_E hD _ _ w hng, ev_E hD _ _ w hg, PBG.position_level_zero_coord, PBG.position_level_zero_coord]
  rw [← WeylCellAction.eH_left (LevelPointCoordinates.nL k r j hj a) p q (w : Q.Mx k r → E) g]
  rw [hG.loc (fun x => (w : Q.Mx k r → E) (LevelPointCoordinates.nL k r j hj a * x)) (fun x => (fun _ => (0 : E)) x + c • (w : Q.Mx k r → E) x)
    (fun x hx => by simp only [zero_add]; exact hw x hx a) g hg]
  rw [hG.lin (fun _ => (0 : E)) (w : Q.Mx k r → E) c Qx2.smooth_zero w.2.1 g hg]
  have h0 : Q.EH k r p q (fun _ : Q.Mx k r => (0 : E)) g = 0 := by
    simp [Q.EH, EabH, RdV]
  rw [h0, zero_add]

theorem _root_.Formalism.FourierDecayAlt.P.adjoin_lower_unipotent : LevelPointCoordinates.AdjoinNL := by
  intro E _ _ k r j hj z Dm hD hDm x hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨⟨p, q⟩, rfl⟩ := hy
    intro v hv g hg a
    exact derivative_keeps_character hj z hD hDm p q v hv g hg a
  | algebraMap c =>
    intro v hv g hg a
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hv g hg a, smul_comm]
  | add y1 y2 _ _ h1 h2 =>
    intro v hv g hg a
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [h1 v hv g hg a, h2 v hv g hg a, smul_add]
  | mul y1 y2 _ _ h1 h2 =>
    intro v hv
    exact h1 _ (h2 v hv)

end Formalism.FourierDecayAlt.P.HeadLetterLemmas
end
end

section

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.HeadLetterLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBG

variable {k r : ℕ}


open Formalism.FourierDecayAlt.Q.QRR in
theorem rdV_of_eq {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (z' : Fin (2 * r + k + 1) → ℂ)
    (hz : inWb k r z') (Φ : Q.Mx k r → E) (g : Q.Mx k r)
    (hΦ : ∀ n ∈ QuantumDeterminants.Nset k r, Φ (g * n) = psi k r z' cStd n • Φ g)
    (l : Fin r) (X : Q.Mx k r) (hX : Pat k r l X) (hS : dag k r X = -X) :
    RdV X Φ g = (ell k r z' X - star (ell k r z' X)) • Φ g := by
  unfold RdV
  have hfun : (fun t : ℝ => Φ (g * NormedSpace.exp ((t : ℂ) • X))) =
      fun t : ℝ => psi k r z' cStd (NormedSpace.exp ((t : ℂ) • X)) • Φ g := by
    funext t
    apply hΦ
    apply (exp_mem_nlev (pat_smul _ hX) _).1
    rw [dag_smul, hS, Complex.star_def, Complex.conj_ofReal, smul_neg]
  rw [hfun]
  exact ((hasDerivAt_psi z' hz X).smul_const (Φ g)).deriv

theorem _root_.Formalism.FourierDecayAlt.P.rule_of_eq : LevelPointCoordinates.RuleOfEq := by
  intro E _ _ k r z' Φ g hz hΦ p q hpq
  obtain ⟨l, hl⟩ := exists_pat p q hpq
  have hr : 1 ≤ r := by have := l.isLt; omega
  set Z : B.Mat k r := Matrix.single p q (1 : ℂ) with hZ
  have h1 := rdV_of_eq z' hz Φ g hΦ l _ (Formalism.FourierDecayAlt.Q.QRR.pat_hpart1 hl) (Formalism.FourierDecayAlt.Q.QRR.skew_hpart1 Z)
  have h2 := rdV_of_eq z' hz Φ g hΦ l _ (Formalism.FourierDecayAlt.Q.QRR.pat_hpart2 hl) (Formalism.FourierDecayAlt.Q.QRR.skew_hpart2 Z)
  set Λ : B.Mat k r → ℂ := fun X => ∑ a, ∑ b, X a b * C3.dpsiP k r z' a b with hΛ
  have hΛ1 : ell k r z' (hpart1 (Hpk k r) Z) - star (ell k r z' (hpart1 (Hpk k r) Z)) = Λ (hpart1 (Hpk k r) Z) := by
    rw [← dEll_eq_ell _ _ hr]
    exact (Formalism.FourierDecayAlt.P.dpsi_is_derivation k r z' _ hr hz (Formalism.FourierDecayAlt.P.PBG.hermitian_part_one_mem_lie Z)
      (pat_inNp (Formalism.FourierDecayAlt.Q.QRR.pat_hpart1 hl))).symm
  have hΛ2 : ell k r z' (hpart2 (Hpk k r) Z) - star (ell k r z' (hpart2 (Hpk k r) Z)) = Λ (hpart2 (Hpk k r) Z) := by
    rw [← dEll_eq_ell _ _ hr]
    exact (Formalism.FourierDecayAlt.P.dpsi_is_derivation k r z' _ hr hz (Formalism.FourierDecayAlt.P.PBG.hermitian_part_two_mem_lie Z)
      (pat_inNp (Formalism.FourierDecayAlt.Q.QRR.pat_hpart2 hl))).symm
  have hsum : hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z = Z := by
    unfold hpart1 hpart2
    rw [smul_smul]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
    rw [this, ← smul_add]
    rw [show Z - (Hpk k r)⁻¹ * Zᴴ * Hpk k r + (Z + (Hpk k r)⁻¹ * Zᴴ * Hpk k r) = (2 : ℂ) • Z by
      rw [two_smul]; abel]
    rw [smul_smul]; norm_num
  have hΛZ : Λ (hpart1 (Hpk k r) Z) + Complex.I * Λ (hpart2 (Hpk k r) Z) = C3.dpsiP k r z' p q := by
    have hlin : Λ (hpart1 (Hpk k r) Z) + Complex.I * Λ (hpart2 (Hpk k r) Z) =
        Λ (hpart1 (Hpk k r) Z + Complex.I • hpart2 (Hpk k r) Z) := by
      simp only [hΛ, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum, mul_assoc]
    rw [hlin, hsum]
    simp only [hΛ, hZ, Matrix.single_apply]
    rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
    · intro a _ ha; apply Finset.sum_eq_zero; intro b _; simp [Ne.symm ha]
    · simp
  show EabH (Hpk k r) p q Φ g = _
  unfold EabH
  rw [h1, h2, hΛ1, hΛ2, smul_smul, ← add_smul, hΛZ]

end Formalism.FourierDecayAlt.P.HeadLetterLemmas
end
end

section

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem hpk_inv' (k r : ℕ) : (Hpk k r)⁻¹ = Hpk k r :=
  Matrix.inv_eq_left_inv (Formalism.QuantumDeterminants.WeylGroupFacts.hpk_sq (k := k) (r := r))

theorem sandwich_apply {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (u v p q : Fin N) :
    (H * Matrix.single u v (1 : ℂ) * H) p q = H p u * H v q := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul]

theorem hpk_col_eI (k r : ℕ) (b : Fin r) (p : Fin (2 * r + k + 1)) :
    Hpk k r p (eI k r b) = if p.val + b.val = 2 * r + k then 1 else 0 := by
  have := b.isLt
  unfold Hpk eI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_row_eI (k r : ℕ) (a : Fin r) (q : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) q = if a.val + q.val = 2 * r + k then 1 else 0 := by
  have := a.isLt
  unfold Hpk eI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_col_esI (k r : ℕ) (b : Fin r) (p : Fin (2 * r + k + 1)) :
    Hpk k r p (esI k r b) = if p.val = b.val then 1 else 0 := by
  have := b.isLt
  unfold Hpk esI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpk_row_esI (k r : ℕ) (a : Fin r) (q : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) q = if q.val = a.val then 1 else 0 := by
  have := a.isLt
  unfold Hpk esI
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega

theorem hpartLevi : HpartLevi := by
  intro k r j hj a b
  have ha := a.isLt
  have hb := b.isLt
  have hcI : (starRingEnd ℂ) (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat, mul_neg, div_neg]
  have hc2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [map_div₀, map_one, map_ofNat]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext p q <;>
    simp only [hpart1, hpart2, hpk_inv', Matrix.conjTranspose_single, star_one, Matrix.smul_apply,
      Matrix.sub_apply, Matrix.add_apply, sandwich_apply, hpk_col_eI, hpk_row_eI, hpk_col_esI, hpk_row_esI] <;>
    simp only [levi, Matrix.of_apply, Matrix.single_apply, eI, esI, Fin.ext_iff, Fin.val_castLE, smul_eq_mul,
      Matrix.smul_apply] <;>
    split_ifs <;> first | (exfalso; omega) | skip
  all_goals first
    | (exfalso; omega)
    | (simp; done)
    | (simp [Complex.conj_I]; done)
    | (simp [Complex.conj_I]; ring; done)
    | (simp only [mul_one, mul_zero, sub_zero, zero_sub, add_zero, zero_add, map_neg, hcI, hc2, neg_neg,
        neg_mul] <;> ring)

end Formalism.FourierDecayAlt.P.WirtingerOperators.LeviExponential
end
end
