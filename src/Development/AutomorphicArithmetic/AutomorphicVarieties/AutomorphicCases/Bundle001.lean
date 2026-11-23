module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.DecompSigmaOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.IsAutQ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle014
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

@[expose] public section

section

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.Aut

def IsQi (K : Type) [Field K] [NumberField K] : Prop := Module.finrank ℚ K = 2 ∧ ∃ i : K, i * i = -1

structure BPrime (K : Type) [Field K] [NumberField K] [IsCMField K] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : G ℚ Ω → Matrix (Fin 3) (Fin 3) (Qbar l)) : Prop where
  opens : ∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → U ≤ (eta4 Ω).ker → MatIrr U a
  cyc : MatIrr ((eta4 Ω).ker ⊓ (cycZ ℚ Ω l).ker) a
  aut : Af.AutOn K ι (-1) a

end UpperTheory.V.Aut

end
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.Top

namespace UpperTheory.V.Aut

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

structure OfChar (D : Raw Ω c) (e : ℕ) {N : ℕ} [NeZero N] (ψ : DirichletCharacter c.O N) (n' p₁ m₀ : ℕ) : Prop where
  e_eq : D.e = e
  psi : D.ψ = Chr.dirG ℚ Ω ψ
  S_eq : D.S = (2 * l * N * p₁).primeFactors
  xi : ∃ (_ : NeZero p₁) (ξ' : DirichletCharacter c.O (2 ^ n')) (ξ₀ : DirichletCharacter c.O p₁), ξ'.IsPrimitive ∧ ξ' (-1) = -1 ∧
    orderOf ξ₀ = m₀ ∧ D.ξ = Chr.dirG ℚ Ω ξ₀ * Chr.dirG ℚ Ω ξ'

def OfCase (D : Raw Ω c) (h : Host) (e : ℕ) (ψ : DirichletCharacter c.O h.N) : Prop :=
  (h.CaseII l e ψ ∧ OfChar D e ψ (h.nII l ψ) 1 1) ∨ (h.CaseIII l e ψ ∧ OfChar D e ψ (h.nIII l ψ) (pOne h.chi) (orderOf ψ))

def IsAut4 (ι : PadicAlgCl l ≃+* ℂ) (r : G ℚ Ω →* M4 (PadicAlgCl l)) : Prop := Af.IsAutQ ι r.toHomUnits

def Sp4In : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (h : Host) (t : ℕ), h.Big t →
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ), l ≠ 2 → 0 < e → e < t → ∀ ψ ∈ h.X c e, ∀ D : Raw Ω c, D.Good → OfCase D h e ψ →
      D.Fin0 ∧ D.NoEnd ∧ ∃ ι : PadicAlgCl l ≃+* ℂ, D.AllIrr (IsAut4 ι)

end UpperTheory.V.Aut

end
end

section

noncomputable section

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.U3

namespace UpperTheory.V.Aut

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {K : Type} [Field K] [NumberField K] [Algebra K Ω]
  {l : ℕ} [Fact l.Prime] {c : Coef l} {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N} (D : Dat Ω K c e ψ)

set_option synthInstance.maxHeartbeats 200000 in
def FinA (g₁ : G ℚ Ω) : Prop :=
  ∀ (U : D.ULoc) (S : D.Ring U g₁), Module.Finite c.O (weightZeroSubalgebra c.O S.r.hom)

set_option synthInstance.maxHeartbeats 200000 in
def AutB [IsCMField K] (ι : Qbar l ≃+* ℂ) (g₁ : G ℚ Ω) : Prop :=
  ∀ (U : D.ULoc) (S : D.Ring U g₁) (ξ : entAlg c.O S.r.hom →ₐ[c.O] PadicAlgCl l)
    (r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)) (hr : HasMult D.η r), IsPush ξ S.r.hom r → TypeI D.η r → D.IsAutI ι r hr

set_option synthInstance.maxHeartbeats 200000 in
def LemW (ι : Qbar l ≃+* ℂ) (g₁ : G ℚ Ω) : Prop :=
  ∀ (U : D.ULoc) (S : D.Ring U g₁) (ξ : entAlg c.O S.r.hom →ₐ[c.O] PadicAlgCl l)
    (r : G ℚ Ω →* GG (m := 3) (R := PadicAlgCl l)), IsPush ξ S.r.hom r → TypeII D.η r → (∀ g ∈ D.η.ker, (r g).mat 1 1 = 1) →
    ∀ W : G ℚ Ω →* GL (Fin 2) (PadicAlgCl l), D.IsExt r W → D.IsModular ι W

def AutomorphyUnramifiedCoefficients : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra K Ω]
    (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (D : Dat Ω K c e ψ),
    eO l c.O = 1 → ∀ ι : Qbar l ≃+* ℂ, ∃ g₁ : G ℚ Ω, D.Marked g₁ ∧ FinA D g₁ ∧ AutB D ι g₁ ∧ LemW D ι g₁

end UpperTheory.V.Aut

end
end
