module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle003
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.Bundle005
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.CeLiftSqToBase
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ZarhinTrick.PullPowAddInv
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
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual

attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)

namespace PositivityTheory.PrwZar

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Ar.GR

def QuasiInverseR : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (A B : Over (Spec (CommRingCat.of R))) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (l : A ⟶ B),
      ∀ g : ℕ, IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom →
      SmoothOfRelativeDimension g B.hom → IsDual A B P → IsDual B A (swap P) → Zarhin.IsPolarisation A B P l →
        ∃ (m : ℕ) (mu : B ⟶ A), 1 ≤ m ∧ IsMonHom mu ∧ l ≫ mu = 𝟙 A ^ m ∧ mu ≫ l = 𝟙 B ^ m

def PolFibreIsogAny : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (P : LB (A ⊗ B).left) (l : A ⟶ B),
      ∀ g : ℕ, IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom →
      SmoothOfRelativeDimension g B.hom → IsDual A B P → IsDual B A (swap P) → Zarhin.IsPolarisation A B P l →
      ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ Sp R),
        IsFinite ((Over.pullback s).map l).left ∧ Flat ((Over.pullback s).map l).left ∧
          Surjective ((Over.pullback s).map l).left

def KilledAny : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C], v.Integers R →
    ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (F : Type) [CommRing F] [Algebra R F]
      (h : sp (R₀ := R) F ⟶ G), IsFinFlatSub G F h →
      ∃ n : ℕ, 0 < n ∧ ∀ (S : Type) [CommRing S] [Algebra R S] (φ : F →ₐ[R] S), (spMap φ ≫ h) ^ n = 1

end PositivityTheory.PrwZar
end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase toBase)

attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.PrwZar

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]

theorem two_cls_eMap (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    (m : ℕ) (hm : 1 ≤ m) (h₁ : l ≫ mu = 𝟙 A ^ m) (h₂ : mu ≫ l = 𝟙 B ^ m)
    (hα : α.transpose * α = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (hα' : α * α.transpose = ((4 * m ^ 2 - 1 : ℕ) : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ))
    (h₁' : ((zb mu α s P L).pull ((Over.pullback s).map (eMap mu α m)).left).IsLB)
    (h₂' : (lPart mu s L).IsLB) :
    2 • cls _ h₁' = 2 • cls _ h₂' :=
  Z2.two_cls_eMap hA hB hD hD' l mu α s L hL e m hm h₁ h₂ hα hα' h₁' h₂'

theorem two_cls_pow (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB (A ⊗ B).left} (hD : IsDual A B P)
    (hD' : IsDual B A (swap P)) (l : A ⟶ B) [IsMonHom l] (mu : B ⟶ A) [IsMonHom mu] (α : Matrix (Fin 4) (Fin 4) ℤ)
    (s : Sp Ω ⟶ S) (L : LB ((Over.pullback s).obj A).left) (hL : L.IsLB)
    (e : LBIso ((ev P (fst A A) (snd A A ≫ l)).pull (sqToBase A s)) (abelian₂ ((Over.pullback s).obj A) L))
    (n : ℕ) (h' : ((zb mu α s P L).pull ((𝟙 ((Over.pullback s).obj (G4 (A ⊗ B)))) ^ n).left).IsLB) :
    2 • cls _ h' = (2 * n ^ 2) • cls _ (isLB_zb mu α s hD.isLB hL) :=
  Z2.two_cls_pow hA hB hD hD' l mu α s L hL e n h'

end PositivityTheory.PrwZar
end
end
