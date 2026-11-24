module

import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIntegralFramedPointBaseChangeCdvrTransitiv
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FinExtIn
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFramedPointBaseChangeAlgHom
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointBaseChangeLaws
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GeneratesOfNonzeroOnSpecialFibre
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

noncomputable section

namespace GlobalTheory.IntFrBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_restrict (T T' : CDVR) (iT : T.Fr →+* T'.Fr) (e : ℕ)
    (h : ∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a) :
    ∃ φ : T.V →+* T'.V, ∀ a, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a) := by
  first | exact _root_.GlobalTheory.PlaceInt.Ext.exists_restrict | exact @_root_.GlobalTheory.PlaceInt.Ext.exists_restrict | apply _root_.GlobalTheory.PlaceInt.Ext.exists_restrict <;> assumption

theorem exists_intFr_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), PullbackSections.IntFrBCSt Xo c := by
  intro E _ _ _ H Dw l Xo c T T' io y iT e _ hv
  have hv' : ∀ a : T.Fr, vV T'.V (iT a) = (e : ℤ) * vV T.V a := fun a => by
    by_cases h : a = 0
    · subst h
      simp [vV]
    · exact hv a h
  let _ := io.toAlgebra
  let _ := (iT.comp io).toAlgebra
  obtain ⟨φ, hφ⟩ := exists_restrict T T' iT e hv'
  have inj : Function.Injective φ := fun a b h => IsFractionRing.injective T.V T.Fr
    (iT.injective ((hφ a).symm.trans ((congrArg _ h).trans (hφ b))))
  let ψ : T.Fr →ₐ[c.F] T'.Fr := ⟨iT, fun _ => rfl⟩
  obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.abelianSchemeLaws_all.1 E H Dw l Xo c _ _ ψ y.1
  obtain ⟨p, ρ, y₀, h₀⟩ := y.2.1
  exact ⟨⟨z, ⟨p, ψ.comp ρ, y₀, GlobalTheory.FramedBaseChange.trans ρ ψ h₀ hz⟩,
    GlobalTheory.IntegralPull.integral_baseChange T T' io (iT.comp io) φ inj ψ (fun a => (hφ a).symm) y.1 z hz y.2.2⟩,
    ψ, rfl, hz⟩

end GlobalTheory.IntFrBaseChange
