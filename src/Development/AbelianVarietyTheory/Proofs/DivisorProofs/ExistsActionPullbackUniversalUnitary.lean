module


import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullEndo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.PullAction

section
open MonObj

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem exists_lift_end (h : IsGrpPullback G' G f φ) (u : G ⟶ G) [IsMonHom u] :
    ∃ v : G' ⟶ G', IsMonHom v ∧ v.left ≫ φ = φ ≫ u.left := by
  apply _root_.GlobalTheory.Ex.Arch.exists_pull_endo <;> assumption

end

theorem exists_action_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (W : Scheme.{0}) (w : W ⟶ Xo.XF c) (G₀ : Over W) [GrpObj G₀] (β₀ : G₀.left ⟶ Xo.univ.t.G.left), IsGrpPullback G₀ Xo.univ.t.G (w ≫ pullback.fst _ _) β₀ → ∃ f₀ : 𝓞 E → (G₀ ⟶ G₀), (∀ a, IsMonHom (f₀ a) ∧ (f₀ a).left ≫ β₀ = β₀ ≫ (Xo.univ.t.act.act a).left) ∧ ∀ (T : Scheme.{0}) (x : T ⟶ W) (tT : SAB H T) (mm : SABMap tT Xo.univ.t ((x ≫ w) ≫ pullback.fst _ _)), ∃ γ : tT.G.left ⟶ G₀.left, IsGrpPullback tT.G G₀ x γ ∧ γ ≫ β₀ = mm.φ ∧ LBIso tT.PP.L ((Xo.univ.t.PP.L.pull β₀).pull γ) ∧ ∀ a, (tT.act.act a).left ≫ γ = γ ≫ (f₀ a).left := by
  intro E _ _ _ H Dw l Xo c W w G₀ _ β₀ hβ
  have key : ∀ a : 𝓞 E, ∃ v : G₀ ⟶ G₀, IsMonHom v ∧ v.left ≫ β₀ = β₀ ≫ (Xo.univ.t.act.act a).left := fun a =>
    haveI := Xo.univ.t.act.hom a
    exists_lift_end hβ _
  choose f₀ hf₀ using key
  refine ⟨f₀, hf₀, fun T x tT mm => ?_⟩
  have hp := hβ.1
  let γ : tT.G.left ⟶ G₀.left := hp.lift mm.φ (tT.G.hom ≫ x)
    (mm.cart.1.w.trans (by simp only [Category.assoc]))
  have hγ : γ ≫ β₀ = mm.φ := hp.lift_fst _ _ _
  have hw : γ ≫ G₀.hom = tT.G.hom ≫ x := hp.lift_snd _ _ _
  have hL : LBIso tT.PP.L (Xo.univ.t.PP.L.pull mm.φ) := mm.lin.imp fun _ h => h.1
  have hU := Xo.univ.t.PP.isLB
  refine ⟨γ, hβ.cancel (by rw [hγ, ← Category.assoc]; exact mm.cart) hw, hγ,
    LBIso.trans tT.PP.isLB (pull_isLB hU _) (pull_isLB (pull_isLB hU _) _) hL
      (GlobalTheory.GenSpread.lbIso_pull_pull hU γ hγ.symm), fun a => ?_⟩
  apply hp.hom_ext
  · rw [Category.assoc, hγ, mm.act, Category.assoc γ, (hf₀ a).2, ← Category.assoc γ, hγ]
  · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]

end GlobalTheory.PullAction
