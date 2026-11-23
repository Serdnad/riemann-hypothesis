module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ChainBetweenPairs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3

namespace UpperTheory.V.Cu

def GoodAt {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (K' L : IntermediateField ℚ Ω) [NumberField L]
    (ρ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* GL (Fin 2) (Qbar l)) : Prop :=
  ∀ p : ℕ, p.Prime → (∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → _root_.ReciprocityTheory.Gal.Dec (F := ℚ) A ≤ K'.fixingSubgroup) ∨
    (p ≠ l ∧ ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → ∀ s ∈ Ine (F := L) A, resQ L s ∈ K'.fixingSubgroup ∧ ρ (resQ L s) = 1)

def GoodOf4 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (D : Raw Ω c) (T₀ T : Tower D), D.Good → T₀.Le T →
    ∀ (K' : IntermediateField ℚ Ω), (∀ p ∈ D.S, ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → _root_.ReciprocityTheory.Gal.Dec (F := ℚ) A ≤ K'.fixingSubgroup) →
    (∀ g : _root_.Formalism.ConjugateSelfDual.G T₀.F Ω, resQ T₀.F g ∉ K'.fixingSubgroup → T₀.rb wAl g = -1) →
    ∀ (w : ℕ) (θ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* (Qbar l)ˣ), w.Prime → T₀.Splits w → (∀ A, Raw.Away {w} A → Ine (F := ℚ) A ≤ θ.ker) →
    ∀ (k : ℕ) (g0 : _root_.Formalism.ConjugateSelfDual.G ℚ Ω) (ρ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* GL (Fin 2) (Qbar l)) (c₁ : Coef l) (h : c.O ≤ c₁.O) (ρ₁ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* M2 c₁.O)
      (x : ValuationSubring Ω → c₁.O), Mod4 D T₀.pr θ k g0 ρ h ρ₁ x → GoodAt K' T.L ρ

def PolOf4 : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (K' : IntermediateField ℚ Ω) [NumberField K'], Module.finrank ℚ K' = 2 → IsTotallyComplex K' →
    ∀ ρ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous ρ → IsAutR ι ρ →
    ∀ (g0 : _root_.Formalism.ConjugateSelfDual.G ℚ Ω) (m : ℕ) (c₁ : Coef l) (κ : _root_.Formalism.ConjugateSelfDual.G K' Ω →* (Qbar l)ˣ) (τ : _root_.Formalism.ConjugateSelfDual.G ℚ Ω →* M2 c₁.O) s, TauDat ι K' g0 m c₁ τ s κ →
    Af.Sol.Pol ι (Af.tw (ρ.comp (resQ K')) κ)

end UpperTheory.V.Cu

end
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Cu.RankFourChainReduction

open UpperTheory.V.Ws.Chn

theorem inA_of {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [Field k] {Φ : Fr O Γ} {a : O →+* k}
    {P P' : PD Φ.ι Γ k} (h : Φ.IsRes a P) (hq : Supp qQ P.r) (e : P.SameAl P') (h' : InA P') : InA P := by
  have r10 : ∀ g, P.r g 1 0 = 0 := fun g => (e.1 g).trans (h'.1 g 1 0 (by decide) (by decide))
  refine ⟨fun g i j hij hw => ?_, fun v => (e.2 v).symm ▸ h'.2 v⟩
  have : wt i j ∉ qQ ∨ i = 1 ∧ j = 0 ∨ i = 3 ∧ j = 2 := by revert hw; revert i j; decide
  rcases this with h1 | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hq g i j hij h1
  · exact r10 g
  · exact al_zero h (qM hq) (r10 g)

end UpperTheory.V.Cu.RankFourChainReduction

end
