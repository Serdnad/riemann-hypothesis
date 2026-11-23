module

public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle002
public import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
public import Formalism.LocalToGlobal.IndefiniteReal.PartsOrth
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle004
public import Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsWithPassage
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Formalism.LocalToGlobal.IndefiniteReal.Bundle005
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle006
public import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartFamily
public import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle011
public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.Bundle001
public import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RatThOfLiftTest
public import Formalism.LocalToGlobal.IndefiniteReal.IsThPKernelSigBase
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.IndefR.Heis

section Law

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

@[ext] structure HeisG (B : M →ₗ[R] M →ₗ[R] R) where

  w : M

  t : R

namespace HeisG

variable {B : M →ₗ[R] M →ₗ[R] R} [Invertible (2 : R)]

end HeisG

end Law

section Rat

variable {E : Type*} [Field E] [NumberField E] (c : E →+* E)

structure HermSp where

  n : ℕ

  J : Matrix (Fin n) (Fin n) E
  herm : J.transpose = J.map c
  nondeg : J.det ≠ 0

variable {c}

def hf (V : HermSp c) (v u : Fin V.n → E) : E := ∑ i, ∑ j, v i * V.J i j * c (u j)

end Rat

section Ad

variable {𝔸 WA : Type*} [CommRing 𝔸] [AddCommGroup WA] [Module 𝔸 WA]

variable [Invertible (2 : 𝔸)] (ψ : AddChar 𝔸 ℂ) (B : WA →ₗ[𝔸] WA →ₗ[𝔸] 𝔸)

end Ad

section D7

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def Hth (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) : Submodule ℂ (WA V W → ℂ) where
  carrier := {f | IsThetaFun ψ V W f}
  zero_mem' := by
    refine ⟨fun γ w => by simp, ⟨⊤, isOpen_univ, fun u _ _ => ?_⟩, continuous_const, fun k L _ _ w => contDiff_const⟩
    funext w; simp [Heisenberg₂]
  add_mem' := by
    intro f g hf hg
    obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨U', hU', hUg⟩ := hg.level
    refine ⟨fun γ w => ?_, ⟨U ⊓ U', ?_, fun u hu h0 => ?_⟩, hf.cont.add hg.cont, fun k L hL hL0 w => ?_⟩
    · simp only [Pi.add_apply, hf.quasi γ w, hg.quasi γ w, mul_add]
    · rw [AddSubgroup.coe_inf]; exact hU.inter hU'
    · funext w
      have e1 := congrFun (hUf u hu.1 h0) w
      have e2 := congrFun (hUg u hu.2 h0) w
      simp only [Heisenberg₂, Pi.add_apply] at e1 e2 ⊢
      rw [mul_add, e1, e2]
    · exact (hf.smooth k L hL hL0 w).add (hg.smooth k L hL hL0 w)
  smul_mem' := by
    intro a f hf
    obtain ⟨U, hU, hUf⟩ := hf.level
    refine ⟨fun γ w => ?_, ⟨U, hU, fun u hu h0 => ?_⟩, continuous_const.mul hf.cont, fun k L hL hL0 w => ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, hf.quasi γ w]; ring
    · funext w
      have e1 := congrFun (hUf u hu h0) w
      simp only [Heisenberg₂, Pi.smul_apply, smul_eq_mul] at e1 ⊢
      rw [mul_left_comm, e1]
    · exact contDiff_const.mul (hf.smooth k L hL hL0 w)

def FinCovol (V W : HSp D) : Prop :=
  (∃ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL V W) 𝓕 μ) ∧
    ∀ (μ : Measure (WA V W)) (𝓕 : Set (WA V W)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V W) 𝓕 μ → μ 𝓕 < ⊤

end D7

end Formalism.IndefR.Heis

end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]

section Concrete

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

def crdOf (A : FamIn K G Pl0 T m) (P0 : Subgroup G) (ψ0 : P0 →* Kˣ) (P1 : Subgroup G) (ψ1 : P1 →* Kˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (Sp : ∀ Zs : DefSub A.fam.amb, SPer (Dc Zs))
    (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) : Crd A.fam.amb (faceOf A P0 ψ0 P1 ψ1 Dc Sp Zsc) where
  toR Zs b t := match b with
    | false => (A.fam.R t).toF (A.fam.lvl P0 ψ0) (Zs.Z t)
    | true => (A.fam.R t).toF (A.fam.lvl P1 ψ1) (Zs.Z t)
  toL Zs b j t := match b with
    | false => (A.fam.L j t).toF (A.fam.lvlA P0 ψ0) (Zs.Zl j t)
    | true => (A.fam.L j t).toF (A.fam.lvlA P1 ψ1) (Zs.Zl j t)

end Concrete

end Formalism.IndefR.Cx
end
end

section

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}

section CoreR3

variable {A3 : FamIn3 K G Pl0 I0 Ty T m} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ} {P1 : Subgroup G} {ψ1 : P1 →* Kˣ}
  {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)} {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)}
  {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {X : CxData A3.fam3.amb3} {s : ℕ}
  {C0 : ∀ j : Fin m, ((A3.liftI j A3.A.fam.μ0).OpIx → K) → Prop}
  {eV : ∀ t, (Fin ((faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Df1.nV t) → K) →ₗ[K] A3.fam3.amb3.FR t}
  {sEE : X.EE →ₗ⋆[ℂ] (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH} {C CH : ℝ}
  {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)}
  {gE : Representation ℂ G X.EE} {gW : ∀ j, Representation ℂ G (X.W j)} {cf : ConvFace A3.fam3.base3}

theorem ComplexDataConditionsBaseLevel.stable (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) : X.zs.Stable :=
  CxData.cutStable X hC.kFormR hC.kFormL
    (Formalism.IndefR.CxPass.definite_kernel_stable hC.kFormR hC.gEquiv hC.thetaR)
    (Formalism.IndefR.CxPass.lift_kernel_stable hC.kFormL hC.gEquivL hC.thetaL)
    (definite_adjoint_closed hC.ok hC.heckeR hC.kFormR hC.jIsoR) (lift_adjoint_closed hC.ok hC.heckeL hC.kFormL hC.jIsoL)

theorem ComplexDataConditionsBaseLevel.wf (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) :
    ∀ b, (lv (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) b).WF := fun b => match b with
  | false => A3.side_well_formed hC.ok P0 ψ0 X.zs hC.stable hC.inBlock hC.sep
  | true => A3.side_well_formed hC.ok P1 ψ1 X.zs hC.stable hC.inBlock hC.sep

theorem ComplexDataConditionsBaseLevel.ratZ (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) : X.RatZ :=
  Formalism.IndefR.Rat.ratZOfTests X (cvOf3 A3 P0 ψ0 P1 ψ1) hC.kFormR hC.kFormL hC.jIsoR hC.jIsoL hC.rowTest hC.liftTest

theorem ComplexDataConditionsBaseLevel.levs (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (b : Bool) :
    X.RatLev (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) b ∧ X.DnLev (cvOf3 A3 P0 ψ0 P1 ψ1) b ∧
      X.UpLev (cvOf3 A3 P0 ψ0 P1 ψ1) b :=
  ⟨Formalism.IndefR.CxPass.rationality_at_level_of_equivariance hC.ok hC.kFormR hC.jIsoR hC.ratZ hC.gUnit hC.gEquiv b,
    Formalism.IndefR.CxPass.descent_of_types hC.ok hC.kFormR hC.jIsoR hC.ratZ hC.gUnit hC.gEquiv hC.h2P hC.lev0 hC.lev1 b,
    Formalism.IndefR.CxPass.upper_level_of_types hC.ok hC.kFormR hC.jIsoR hC.gUnit hC.gEquiv hC.lev0 hC.lev1 b⟩

theorem ComplexDataConditionsBaseLevel.what₂ (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (b : Bool) :
    X.H2 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b ∧ X.H4 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b :=
  cutRows (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) b (hC.wf b) hC.h4pos
    (definite_isometry_of_norms hC.ok hC.jIsoR hC.npTie b) (definite_coordinates_in_subspaces X b) (definite_coordinates_in_good_part X b) (hC.levs b).1 (hC.levs b).2.1 (hC.levs b).2.2
    (hC.thmBop b) (hC.partsE b)

theorem ComplexDataConditionsBaseLevel.ratMu (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (b : Bool) :
    X.RATmu (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b :=
  Formalism.IndefR.Rat.ratMuOfRowTest X (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b hC.rowTest (hC.what₂ b).1

theorem ComplexDataConditionsBaseLevel.partsOrth (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (b : Bool) :
    X.PartsOrth b (fc := faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) := by
  cases b
  · exact fun v _ p q hpq x hx y hy =>
      majAt_eq_zero_of_mem_Qp_of_ne A3 X hC.ok (hC.heckeR A3.A.fam.μ0) hC.stable P0 ψ0 v p q hpq x hx y hy
  · exact fun v _ p q hpq x hx y hy =>
      majAt_eq_zero_of_mem_Qp_of_ne A3 X hC.ok (hC.heckeR A3.A.fam.μ0) hC.stable P1 ψ1 v p q hpq x hx y hy

theorem ComplexDataConditionsBaseLevel.rowHyp (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) (b : Bool) :
    X.RowHyp (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) b :=
  ⟨hC.wf b, hC.h4pos, (hC.what₂ b).1, hC.ratMu b,
    definite_equivariance_of_primitive P0 ψ0 P1 ψ1 Dc Sp Zsc hC.kFormR hC.stable hC.ok hC.thetaR b, (hC.what₂ b).2, hC.partsOrth b⟩

theorem ComplexDataConditionsBaseLevel.lifts0 (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) :
    X.H5 (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false ∧ X.ThmA (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false :=
  CxData.cutLifts X (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) false (hC.wf false) hC.h4pos hC.kForm
    (lift_isometry_of_norms hC.ok hC.jIsoL hC.npTie false) (lift_coordinates_in_subspaces X false) (lift_coordinates_in_good_part_family X false)
    (Formalism.IndefR.CxPass.lift_rationality_of_equivariance hC.ok hC.kFormL hC.jIsoL hC.ratZ hC.gUnitL hC.gEquivL false)
    (Formalism.IndefR.CxPass.lift_descent_at_lower_type hC.ok hC.kFormL hC.jIsoL hC.ratZ hC.gUnitL hC.gEquivL hC.lower_level_lift_type)
    (Formalism.IndefR.CxPass.upper_level_lift_at_lower_type hC.ok hC.kFormL hC.jIsoL hC.gUnitL hC.gEquivL hC.lower_level_lift_type)
    hC.thmAop hC.partsW

theorem ComplexDataConditionsBaseLevel.ratTh (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) :
    X.RATth (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false :=
  Formalism.IndefR.Rat.ratThOfLiftTest X (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false hC.base_lift_test hC.lifts0.1 hC.kForm hC.ewNorm
    (hC.h4pos.2.2 false)

theorem ComplexDataConditionsBaseLevel.liftHyp0 (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) :
    X.LiftHyp (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false :=
  ⟨hC.lifts0.1, hC.ratTh, hC.kForm, hC.ewNorm, hC.lifts0.2, hC.galD,
    lift_equivariance_of_primitive P0 ψ0 P1 ψ1 Dc Sp Zsc hC.kFormL hC.stable hC.ok hC.thetaL false, hC.mLat⟩

theorem ComplexDataConditionsBaseLevel.types0 (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) :
    (lv (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) false).Types :=
  types_of_lift_eigenvalues A3 X hC.ok hC.sep hC.stable P0 ψ0 hC.eig0 hC.typ0

theorem ComplexDataConditionsBaseLevel.proviso0 (hC : ComplexDataConditionsBaseLevel A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 hE hW gE gW) :
    (lv (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs) false).Proviso :=
  proviso_of_lift_eigenvalues A3 X hC.ok (fun j => hC.heckeL j A3.A.fam.μ0) P0 ψ0 hC.eig0

theorem PrimitiveStatementsBaseLiftsOnly.cols (hC : PrimitiveStatementsBaseLiftsOnly A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 eV sEE C CH hE hW gE gW cf) :
    ∃ ζ : (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Dc.Mem → A3.fam3.base3.Tup → K,
      (X.colOf (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).PairingFactorsThroughPeriods ∧
      (X.colOf (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).L1e :=
  X.exists_zeta_pairing_factors_through_periods (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) eV sEE (hC.wf true) hC.h4pos (hC.what₂ true).1
    (hC.ratMu true) hC.jIsoR (hC.levs true).1 (hC.levs true).2.1 (hC.levs true).2.2 (definite_coordinates_in_good_part X true) hC.evTie hC.seeIso
    hC.miStar

def zetaEps (X : CxData A3.fam3.amb3) (cr : Crd A3.fam3.amb3 (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc))
    (sEE : X.EE →ₗ⋆[ℂ] (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Sp.HH) :
    (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X.zs).Dc.Mem → A3.fam3.base3.Tup → K :=
  Classical.epsilon fun ζ => (X.colOf cr (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).PairingFactorsThroughPeriods ∧
    (X.colOf cr (X.colDef (fun u t => (ζ u t)⁻¹) sEE)).L1e

def basePackageFullHecke (hC : PrimitiveStatementsWithPassage A3 P0 ψ0 P1 ψ1 Dc Sp Zsc X s C0 eV sEE C CH hE hW gE gW cf) :
    IndefPkgR A3.fam3.amb3 (faceOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) cf C CH :=
  X.cxPkgR (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) cf (X.colDef (fun u t => (zetaEps X (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) sEE u t)⁻¹) sEE) C CH
    hC.stable hC.inBlock (hC.rowHyp false) hC.liftHyp0 hC.pos hC.proviso0 hC.types0 hC.h0
    (CxData.cutDims X (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) false (hC.wf false) hC.h4pos hC.kForm hC.ewNorm hC.types0
      (hC.what₂ false).1 (hC.ratMu false) (hC.rowHyp false).h3 hC.lifts0.1 hC.ratTh hC.liftHyp0.h3W (hC.partsE false)
      hC.partsW hC.dimParts)
    hC.l3 hC.on (hC.rowHyp true) hC.l6 (Classical.epsilon_spec hC.cols).1 (Classical.epsilon_spec hC.cols).2
    (CxData.cutTuples2 X (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) C CH hC.h0 hC.w1) hC.passage hC.fun0 hC.conv
    (X.heckeB_of (hC.what₂ false).1 hC.kForm hC.ewNorm hC.h4pos hC.heckeRB.some
      hC.heckeWB.some).some
    (X.heckeC_of (hC.what₂ true).1 hC.heckeRC.some).some

end CoreR3

end Formalism.IndefR.Cx
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.FrobeniusOrbits

namespace Formalism.IndefR.Conj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem emb_mul' (g g' : D.R.GG) (x : D.host.E) :
    D.host.emb (g * g') x = D.host.emb g (D.host.sigmaOf g' x) := by
  simp only [Host.emb, Host.sigmaOf, map_mul, RingHom.comp_apply]
  rfl

theorem conj_comp_emb (g : D.R.GG) :
    (starRingEnd ℂ).comp (D.host.emb g) = D.host.emb (g * D.R.cc) := by
  ext x
  rw [RingHom.comp_apply, emb_mul', ← D.host.conjE_apply (D.host.emb g)]
  rfl

theorem cc_mul_cc : D.R.cc * D.R.cc = 1 := by
  simp [Formalism.HC.Frame.cc, c0, Prod.ext_iff]

theorem ArchLab.emb_eq (A : ArchLab D) (τ : D.what₂.Tau) :
    A.emb τ = D.host.emb ((D.eTau (A.perm τ)).1 * (if A.side then 1 else D.R.cc)) := by
  rcases A with ⟨p, s⟩
  cases s
  · simp [ArchLab.emb, tauE, conj_comp_emb]
  · simp [ArchLab.emb, tauE]

theorem emb_injective : Function.Injective (D.host.emb) := (factEmb D.R D.host).1.1

theorem snd_side (b : Bool) : ((if b then 1 else D.R.cc : D.R.GG)).1.2 = if b then 1 else -1 := by
  cases b <;> rfl

theorem labExists : LabExists D := by
  intro σ
  obtain ⟨γ, hγ⟩ := (factEmb D.R D.host).1.2 (σ.comp D.embE)
  have hlab : ∀ τ, labE σ τ = D.host.emb (γ * (D.eTau τ).1) := by
    intro τ
    ext x
    rw [emb_mul', hγ]
    rfl
  by_cases hγP : γ ∈ D.R.Psi
  · let f : D.what₂.Tau → D.what₂.Tau := fun τ => D.eTau.symm ⟨γ * (D.eTau τ).1, mul_mem hγP (D.eTau τ).2⟩
    have hf : Function.Injective f := by
      intro a b hab
      have e1 := congrArg (fun x => (D.eTau x).1) hab
      simp only [f, Equiv.apply_symm_apply] at e1
      exact D.eTau.injective (Subtype.ext (mul_left_cancel e1))
    refine ⟨⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), true⟩, fun τ => ?_⟩
    rw [hlab τ]
    simp [ArchLab.emb, tauE, f]
  · have hnot : ∀ τ, γ * (D.eTau τ).1 ∉ D.R.Psi := by
      intro τ hm
      apply hγP
      have h1 : (γ * (D.eTau τ).1).1.2 = 1 := hm
      have h2 : (D.eTau τ).1.1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau τ).2
      show γ.1.2 = 1
      simpa [Prod.fst_mul, Prod.snd_mul, h2] using h1
    have hmem : ∀ τ, γ * (D.eTau τ).1 * D.R.cc ∈ D.R.Psi := by
      intro τ
      have h1 := hnot τ
      rw [Formalism.HC.Frame.mem_Psi_iff] at h1 ⊢
      show (γ * (D.eTau τ).1).1.2 * (-1) = 1
      rcases Int.units_eq_one_or (γ * (D.eTau τ).1).1.2 with h | h
      · exact absurd h h1
      · rw [h]; rfl
    let f : D.what₂.Tau → D.what₂.Tau := fun τ => D.eTau.symm ⟨γ * (D.eTau τ).1 * D.R.cc, hmem τ⟩
    have hf : Function.Injective f := by
      intro a b hab
      have e1 := congrArg (fun x => (D.eTau x).1) hab
      simp only [f, Equiv.apply_symm_apply] at e1
      exact D.eTau.injective (Subtype.ext (mul_left_cancel (mul_right_cancel e1)))
    refine ⟨⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), false⟩, fun τ => ?_⟩
    rw [hlab τ, ArchLab.emb_eq]
    simp only [Equiv.ofBijective_apply, f, Equiv.apply_symm_apply, Bool.false_eq_true, if_false]
    rw [mul_assoc (γ * (D.eTau τ).1), cc_mul_cc, mul_one]

end Formalism.IndefR.Conj

end
end
