module

public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.BqOriginSt
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle013
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle025
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSEqJetMap
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle014
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffAddFirstSecond
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.IsUnitCoeffZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj

variable {D : D7}


open Classical in
def clOf {j : ℕ} (wL : WeightFamilies.Wt D j) {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) : ℝ :=
  if ((D.host.QS : ℕ) : 𝓞 K) ∈ la.asIdeal then (padicValNat (ringChar (𝓞 K ⧸ la.asIdeal)) D.host.QS : ℝ) * (c2 D wL : ℝ)
  else if ((D.host.q : ℕ) : 𝓞 K) ∈ la.asIdeal ∨ ((D.host.d : ℕ) : 𝓞 K) ∈ la.asIdeal then (cHalf wL : ℝ)
  else 0

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory



theorem bqOrigin : BqOriginSt := by
  unfold BqOriginSt
  intro E _ _ _ H Dw l Xo c _ hstar S _ _ _ y C a wLa hLa wLb hLb Z r z J hJ

  have hA : ∀ e : 𝓞 E, (1 : overAt y.x S ⟶ Xo.univ.t.G) ≫ Xo.univ.t.act.act e = 1 := by
    intro e
    haveI := Xo.univ.t.act.hom e
    first
      | (simp; done)
      | (show (toUnit _ ≫ η[Xo.univ.t.G]) ≫ _ = toUnit _ ≫ η[Xo.univ.t.G]
         rw [Category.assoc, IsMonHom.one_hom])

  have hF : lift (1 : overAt y.x S ⟶ Xo.univ.t.G) 1 ≫ faceMap Xo.univ.t.G 2 = lift 1 (lift 1 1) := by
    first
      | (rw [show faceMap Xo.univ.t.G 2 = lift (x2 Xo.univ.t.G 0)
              (lift (x2 Xo.univ.t.G 1) (pzero Xo.univ.t.G (G2 Xo.univ.t.G))) from rfl,
            comp_lift, comp_lift,
            show x2 Xo.univ.t.G 0 = fst _ _ from rfl, show x2 Xo.univ.t.G 1 = snd _ _ from rfl,
            lift_fst, lift_snd,
            show pzero Xo.univ.t.G (G2 Xo.univ.t.G) = (1 : G2 Xo.univ.t.G ⟶ Xo.univ.t.G) from rfl,
            ExpGD.comp_one'])
      | (simp [faceMap, x2, pzero]; done)

  have hR : val C.wP (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J =
      val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J := by
    rw [← val_corr hJ C.prim.2 (r ≫ (toUnit (overAt y.x S)).left), val_pull hJ, Category.assoc]
    all_goals first | rfl | exact hJ
  have hP : ∀ e : 𝓞 E, val C.wP ((r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) ≫
      (Xo.univ.t.act.act e).left) z J = val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J := by
    intro e
    rw [Category.assoc, ← Over.comp_left, hA, hR]

  have hC : ∀ e₁ e₂ e₃ : 𝓞 E, val Xo.univ.t.cub.t ((r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) ≫
      (lift (Xo.univ.t.act.act e₁) (lift (Xo.univ.t.act.act e₂) (Xo.univ.t.act.act e₃))).left) z J = 1 := by
    intro e₁ e₂ e₃
    have hm : (1 : overAt y.x S ⟶ Xo.univ.t.G) ≫
        lift (Xo.univ.t.act.act e₁) (lift (Xo.univ.t.act.act e₂) (Xo.univ.t.act.act e₃)) =
        lift (1 : overAt y.x S ⟶ Xo.univ.t.G) 1 ≫ faceMap Xo.univ.t.G 2 := by
      rw [hF, comp_lift, comp_lift, hA, hA, hA]
    rw [Category.assoc, ← Over.comp_left, hm, Over.comp_left, ← Category.assoc]
    refine (val_pull hJ _ _ _).symm.trans ((val_corr hJ (Xo.univ.t.cub.face 2) _).trans ?_)
    first | exact val_one _ | exact val_one hJ _ | (simp [val_one, hJ]; done)

  have hLa0 : val wLa ((r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) ≫
      (lift (Xo.univ.t.act.act 1) (Xo.univ.t.act.act (a * H.w0))).left) z J = 1 := by
    rw [Category.assoc, ← Over.comp_left, comp_lift, hA, hA]
    exact ExpGD.wL_zero C a wLa hLa r z J hJ
  have hLb0 : val wLb ((r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) ≫
      (lift (Xo.univ.t.act.act a) (Xo.univ.t.act.act H.w0)).left) z J = 1 := by
    rw [Category.assoc, ← Over.comp_left, comp_lift, hA, hA]
    exact ExpGD.wL_zero C (H.bar a) wLb hLb r z J hJ

  have hCB : val (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act 1) (lift (Xo.univ.t.act.act (a * H.bar a))
              (Xo.univ.t.act.act ((1 + a * H.bar a) * H.w0)))).left)
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
              (Xo.univ.t.act.act 1))).left) (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
              (Xo.univ.t.act.act (a * H.bar a)))).left)))
      (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J = 1 := by
    refine (val_mul hJ _ _ _).trans ?_
    rw [show val (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act 1) (lift (Xo.univ.t.act.act (a * H.bar a))
              (Xo.univ.t.act.act ((1 + a * H.bar a) * H.w0)))).left) (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J = 1 from
      (val_pull hJ _ _ _).trans (hC _ _ _)]
    refine (congrArg _ (val_mul hJ _ _ _)).trans ?_
    rw [show val (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
              (Xo.univ.t.act.act 1))).left) (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J = 1 from
      (val_pull hJ _ _ _).trans (hC _ _ _),
      show val (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
              (Xo.univ.t.act.act (a * H.bar a)))).left) (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J = 1 from
      (val_pull hJ _ _ _).trans (hC _ _ _)]
    simp

  change val (LB.mulGen Xo.univ.t.PP.L _ _ _ _
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (Xo.univ.t.act.act (1 + a * H.bar a)).left)
          (LB.mulGen Xo.univ.t.PP.L _ _ _ _
            (LB.invGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (Xo.univ.t.act.act a).left))
            (LB.invGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (Xo.univ.t.act.act a).left))))
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.invGen Xo.univ.t.PP.L _ _ C.wP)
          (LB.invGen Xo.univ.t.PP.L _ _
            (LB.pullGen Xo.univ.t.PP.L _ _ C.wP (Xo.univ.t.act.act (a * H.bar a)).left))))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
            (lift (Xo.univ.t.act.act 1) (lift (Xo.univ.t.act.act (a * H.bar a))
              (Xo.univ.t.act.act ((1 + a * H.bar a) * H.w0)))).left)
          (LB.mulGen Xo.univ.t.PP.L _ _ _ _
            (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
              (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
                (Xo.univ.t.act.act 1))).left)
            (LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t
              (lift (Xo.univ.t.act.act H.w0) (lift (Xo.univ.t.act.act (a * H.bar a * H.w0))
                (Xo.univ.t.act.act (a * H.bar a)))).left)))
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _
          (LB.pullGen Xo.univ.t.PP.L _ _ wLa (lift (Xo.univ.t.act.act 1) (Xo.univ.t.act.act (a * H.w0))).left)
          (LB.invGen Xo.univ.t.PP.L _ _
            (LB.pullGen Xo.univ.t.PP.L _ _ wLb (lift (Xo.univ.t.act.act a) (Xo.univ.t.act.act H.w0)).left)))))
    (r ≫ (1 : overAt y.x S ⟶ Xo.univ.t.G).left) z J *
      val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J ^ (3 : ℤ) = 1
  simp only [val_mul hJ, val_inv, val_pull hJ, hP, hR, hC, hLa0, hLb0, hJ]
  rw [hCB]
  clear hA hF hR hP hC hLa0 hLb0 hstar hLa hLb hCB
  generalize val Xo.univ.t.PP.rig (r ≫ (toUnit (overAt y.x S)).left) z J = R
  group

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGO
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGU Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGF Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGG

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}

def ptm (C : ChartAt Xo c y) {n : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : ℕ) :
    jO y (dL Dw) m 1 ⟶ jO y C.d m n :=
  homAt y.x (jetSubstPS (m := m) (fun p : Fin n × Fin C.d => P p.1 p.2))

theorem ptm_congr (C : ChartAt Xo c y) {n : ℕ} {P P' : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S}
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (hP' : ∀ i j, MvPowerSeries.constantCoeff (P' i j) = 0)
    (m : ℕ) (h : ∀ i j, psJet m (P i j) = psJet m (P' i j)) : ptm C P m = ptm C P' m := by
  unfold ptm
  refine congrArg (homAt y.x) (GermD.jet_hom_ext fun q => ?_)
  exact (ExpGF.jetSubstPS_X m (fun p : Fin n × Fin C.d => P p.1 p.2) (fun p => hP p.1 p.2) q).trans
    ((h q.1 q.2).trans (ExpGF.jetSubstPS_X m (fun p : Fin n × Fin C.d => P' p.1 p.2) (fun p => hP' p.1 p.2) q).symm)

theorem coe_actP (u : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) :
    ((actP (Dw := Dw) (S := S) c u q : MvPolynomial _ S) : MvPowerSeries (Fin 1 × Fin (dL Dw)) S) =
      actPS (Dw := Dw) (S := S) c u q := by
  simp only [actP, actPS, MvPolynomial.coe_mul, MvPolynomial.coe_C, MvPolynomial.coe_X]
  rw [← MvPowerSeries.smul_eq_C_mul, algebraMap_smul]

theorem cc_actP (u : 𝓞 E) (q : Fin 1 × Fin (dL Dw)) :
    MvPolynomial.constantCoeff (actP (Dw := Dw) (S := S) c u q) = 0 := by
  simp [actP]

theorem jetSubstP_actP (m : ℕ) (u : 𝓞 E) :
    jetSubstP m (actP (Dw := Dw) (S := S) c u) = jetSubstPS (m := m) (actPS (Dw := Dw) (S := S) c u) := by
  rw [ExpGF.jetSubstP_eq_jetSubstPS m _ (fun q => cc_actP u q)]
  congr 1
  funext q
  exact coe_actP u q

theorem sA_ptm (C : ChartAt Xo c y) {n : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (m : ℕ) (u : 𝓞 E) :
    homAt y.x (jetSubstP m (actP (Dw := Dw) (S := S) c u)) ≫ ptm C P m =
      ptm C (fun i j => MvPowerSeries.subst (actPS (Dw := Dw) (S := S) c u) (P i j)) m := by
  unfold ptm
  rw [GermD.homAt_comp, jetSubstP_actP,
    ExpGF.jetSubstPS_comp m (fun p : Fin n × Fin C.d => P p.1 p.2) (actPS (Dw := Dw) (S := S) c u)
      (fun p => hP p.1 p.2) (const_actPS c u)]

theorem ptm_copy (C : ChartAt Xo c y) {n : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (m : ℕ) (i : Fin n) :
    ptm C P m ≫ homAt y.x (jetCopy C.d m i) = ptm C ![P i] m := by
  have hs : MvPowerSeries.HasSubst (fun p : Fin n × Fin C.d => P p.1 p.2) := by
    first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => hP p.1 p.2)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_zero (fun p => hP p.1 p.2)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun q => by rw [(fun p => hP p.1 p.2) q]; exact IsNilpotent.zero)
  unfold ptm
  rw [GermD.homAt_comp, ExpGF.jetCopy_eq_PS,
    ExpGF.jetSubstPS_comp m (fun p : Fin 1 × Fin C.d => (MvPowerSeries.X (i, p.2) : MvPowerSeries (Fin n × Fin C.d) S))
      (fun p : Fin n × Fin C.d => P p.1 p.2) (fun p => MvPowerSeries.constantCoeff_X _) (fun p => hP p.1 p.2)]
  refine congrArg (homAt y.x) (congrArg (jetSubstPS (m := m)) ?_)
  funext p
  obtain ⟨a, j⟩ := p
  fin_cases a
  simp [MvPowerSeries.subst_X hs]

theorem ptm_subst (C : ChartAt Xo c y) {n n' : ℕ} (P : Fin n → Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hP : ∀ i j, MvPowerSeries.constantCoeff (P i j) = 0) (m : ℕ)
    (σ : Fin n' × Fin C.d → MvPolynomial (Fin n × Fin C.d) S) (hσ : ∀ k, MvPolynomial.constantCoeff (σ k) = 0) :
    ptm C P m ≫ homAt y.x (jetSubstP m σ) =
      ptm C (fun i j => MvPowerSeries.subst (fun p : Fin n × Fin C.d => P p.1 p.2)
        ((σ (i, j) : MvPolynomial _ S) : MvPowerSeries (Fin n × Fin C.d) S)) m := by
  unfold ptm
  rw [GermD.homAt_comp, ExpGF.jetSubstP_eq_jetSubstPS m σ hσ,
    ExpGF.jetSubstPS_comp m (fun k => ((σ k : MvPolynomial _ S) : MvPowerSeries (Fin n × Fin C.d) S))
      (fun p : Fin n × Fin C.d => P p.1 p.2) (fun k => by
        have h0 : AddMonoidAlgebra.coeff (σ k) 0 = 0 := hσ k
        rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe, h0]) (fun p => hP p.1 p.2)]

theorem jφ_eq (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S) (m : ℕ) :
    homAt y.x (jφ φ m) = ptm C ![φ] m := by
  have e : (fun p : Fin 1 × Fin C.d => φ p.2) = (fun p : Fin 1 × Fin C.d => (![φ] : Fin 1 → _) p.1 p.2) := by
    funext p
    obtain ⟨a, j⟩ := p
    fin_cases a
    rfl
  unfold ptm jφ
  rw [e]

theorem exp_chart_action_point (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (hx : IsExpChart y (xExp y C φ)) (m : ℕ) (u : 𝓞 E) :
    xExp y C φ m ≫ Xo.univ.t.act.act u = ptm C ![φa c φ u] m ≫ C.x m := by
  have hP : ∀ i j, MvPowerSeries.constantCoeff ((![φ] : Fin 1 → _) i j) = 0 := by
    intro i j
    fin_cases i
    exact hφ j
  have e : (fun i j => MvPowerSeries.subst (actPS (Dw := Dw) (S := S) c u) ((![φ] : Fin 1 → _) i j)) =
      ![φa c φ u] := by
    funext i j
    fin_cases i
    rfl
  rw [hx.act m u, xExp, ← Category.assoc, jφ_eq, sA_ptm C _ hP m u, e]

theorem ptm_jpt (C : ChartAt Xo c y) (φ : Fin C.d → MvPowerSeries (Fin 1 × Fin (dL Dw)) S)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (hx : IsExpChart y (xExp y C φ)) (m : ℕ) {n : ℕ}
    (us : Fin n → 𝓞 E) (i : Fin n) :
    ptm C (fun k => φa c φ (us k)) m ≫ jpt y C.d C.x m i = xExp y C φ m ≫ Xo.univ.t.act.act (us i) := by
  have hP : ∀ k j, MvPowerSeries.constantCoeff (φa c φ (us k) j) = 0 := fun k j => const_φa c φ hφ (us k) j
  rw [jpt, ← Category.assoc, ptm_copy C _ hP m i, exp_chart_action_point C φ hφ hx m (us i)]

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGH
end
end

section

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open AlgebraicGeometry CategoryTheory Limits NumberField MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
  Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix
open ReciprocityTheory.ChartRestriction.G.TB (dLin)

def FrRatioSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra ℚ S] (y : FrPt Xo c S) (C : ChartAt Xo c y) (m : ℕ),
    ∃ U : (Jet S (Fin 2 × Fin C.d) m)ˣ,
      LB.Gen.Corr Xo.univ.t.PP.L _ _ _ _
        (LB.pullGen Xo.univ.t.PP.L _ _ (C.e (m + 1))
          (homAt y.x (jetTrunc : Jet S (Fin 2 × Fin C.d) (m + 1) →ₐ[S] Jet S (Fin 2 × Fin C.d) m)).left)
        (scaleGen (Xo := Xo) _ _ (unitΓ U) (C.e m)) ∧
      jetSubstP m (fun p : Fin 2 × Fin C.d =>
          (![fun j => psIn C.d m (![0, 1] : Fin 2 → Fin 3) (C.B.G.F j), fun j => X ((2 : Fin 3), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) =
        jetSubstP m (fun p : Fin 2 × Fin C.d => (![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) *
        jetSubstP m (fun p : Fin 2 × Fin C.d => (![fun j => X ((1 : Fin 3), j), fun j => X ((2 : Fin 3), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 3 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) ∧
      jetSubstP m (fun p : Fin 2 × Fin C.d => (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] :
          Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) = U ∧
      ∀ a : 𝓞 E, jetSubstP m (fun p : Fin 2 × Fin C.d =>
          (![fun j => psIn C.d m ![0] (C.B.A.act a j), fun j => X ((1 : Fin 2), j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m) =
        jetSubstP m (fun p : Fin 2 × Fin C.d =>
          (![fun j => X ((0 : Fin 2), j), fun j => psIn C.d m ![1] (C.B.A.act (H.bar a) j)] :
            Fin 2 → Fin C.d → MvPolynomial (Fin 2 × Fin C.d) S) p.1 p.2) (U : Jet S (Fin 2 × Fin C.d) m)

def ccOf {S : Type} [CommRing S] {d : ℕ} (cm : ℕ → Fin d → Fin d → S) : ℕ → Fin d → Fin d → S
  | 0 => 0
  | m + 1 => ccOf cm m - cm m

theorem frTruncFix_of (hA : FrRatioSt) : FrTruncFixSt := by
  intro E _ _ _ H Dw l Xo c _ hstar S _ _ _ y C
  choose U hCorr h1 hs hb using fun m => hA E H Dw l Xo c hstar S y C m
  have hact : ∀ (a : 𝓞 E) (i : Fin C.d), MvPowerSeries.constantCoeff (C.B.A.act a i) = 0 :=
    fun a i => C.B.A.const a i
  choose cm hcs hcb hcU using fun m =>
    CIndFrExp3.fixExp (G := C.B.G) (act := C.B.A.act) (hact := hact) (bar := H.bar) (m := m)
      (U := U m) (h1 := h1 m) (hs := hs m) (hb := hb m)
  have hsym : ∀ m i j, ccOf cm m i j = ccOf cm m j i := by
    intro m
    induction m with
    | zero => intro i j; rfl
    | succ m ih =>
      intro i j
      show ccOf cm m i j - cm m i j = ccOf cm m j i - cm m j i
      rw [ih i j, hcs m i j]
  have hbal : ∀ m (a : 𝓞 E), Matrix.transpose (dLin (C.B.A.act a)) * Matrix.of (ccOf cm m) =
      Matrix.of (ccOf cm m) * dLin (C.B.A.act (H.bar a)) := by
    intro m
    induction m with
    | zero => intro a; simp only [ccOf, Matrix.of_zero, mul_zero, zero_mul]
    | succ m ih =>
      intro a
      simp only [ccOf]
      rw [← Matrix.of_sub_of, mul_sub, sub_mul, ih a, hcb m a]
  have hdiff : ∀ m, ccOf cm m - ccOf cm (m + 1) = cm m := fun m =>
    show ccOf cm m - (ccOf cm m - cm m) = cm m from sub_sub_cancel _ _
  obtain ⟨e', hfr, hrig, htr, hu⟩ := CIndFrFix2c.fixTw (C := C) (cc := ccOf cm) (h0 := rfl)
    (hsym := hsym) (hbal := hbal)
    (hstep := fun m => ⟨U m, by rw [hdiff m]; exact hcU m, hCorr m⟩)
  exact ⟨e', hfr, hrig, ccOf cm, htr, rfl, hsym, hbal, hu⟩

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
