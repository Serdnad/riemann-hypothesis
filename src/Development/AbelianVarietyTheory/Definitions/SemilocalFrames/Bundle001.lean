module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Algebra.AffineMonoid.Basic
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob

variable {E : Type} [Field E] [NumberField E]

def dInv (E : Type) [Field E] [NumberField E] (j : ℕ) : FractionalIdeal (𝓞 E)⁰ E :=
  ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)⁻¹) ^ j

def SelfDual (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  Λ.FG ∧ ∀ v, v ∈ Λ ↔ ∀ w ∈ Λ, form σ J v w ∈ (algebraMap (𝓞 E) E).range

def frameLat {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {v | ∃ (b : Fin (r + 1)) (a : E), a ∈ dInv E (r - (b : ℕ)) ∧ v = a • fun i => P i b}

def PrimIn {n : ℕ} (M Λ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  M ≤ Λ ∧ ∀ v ∈ Λ, v ∈ Submodule.span E (M : Set (Fin n → E)) → v ∈ M

def pairLat {n r : ℕ} (g : ℕ) (P P' : Matrix (Fin n) (Fin (r + 1)) E) :
    Submodule (𝓞 E) (Fin n → E) :=
  frameLat P ⊔ frameLat (((g : E)⁻¹) • (P' - P))

def latMap {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) := Λ.map (γ.mulVecLin.restrictScalars (𝓞 E))

abbrev Tri (E : Type) [Field E] [NumberField E] (n r : ℕ) : Type :=
  Submodule (𝓞 E) (Fin n → E) × Matrix (Fin n) (Fin (r + 1)) E × Matrix (Fin n) (Fin (r + 1)) E

def GenConf (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (T T' : E) (g : ℕ)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Set (Tri E n r) :=
  {x | SelfDual σ J x.1 ∧ (x.2.1, x.2.2) ∈ XZ σ J T T' Z ∧ PrimIn (pairLat g x.2.1 x.2.2) x.1}

def FrameLats (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Set (Submodule (𝓞 E) (Fin n → E)) :=
  {Λ | SelfDual σ J Λ ∧ PrimIn (frameLat P) Λ}

end GlobalTheory.SgGlob
end
end

section

noncomputable section
open ValuativeRel IsDedekindDomain NumberField ComplexConjugate Formalism.MainNotions.S.Loc
open scoped Classical

namespace GlobalTheory.SgGlob

structure ModFam (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sig : E →ₐ[F] E) (g₁ g₂ : ℕ) where
  rank : Module.finrank F E = 2
  g₁_prime : g₁.Prime
  g₂_prime : g₂.Prime
  g_ne : g₁ ≠ g₂
  A : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p
  M : ∀ p, Model (A p).Fp (A p).Ep
  ok : ∀ p, (M p).OK
  de : ∀ p, (A p).Fp
  de_ne : ∀ p, de p ≠ 0
  de_gen : ∀ p (x : (A p).Fp), (haveI := (A p).ellPrime;
    ∀ y ∈ 𝒪[(A p).Fp], ‖Algebra.trace ℚ_[resChar p] (A p).Fp (x * y)‖ ≤ 1) ↔ de p * x ∈ 𝒪[(A p).Fp]
  cj_eq : ∀ p, (M p).L.cj = (A p).cj
  fractionFieldToGenericStalk_algebraMap_eq : ∀ p y, (M p).L.psi0 y = (A p).psiE (-(algebraMap (A p).Fp (A p).Ep (de p)⁻¹ * y))
  typed : ∀ p, (M p).split.isSome ↔ (resChar p = g₁ ∨ resChar p = g₂)
  split_eq : ∀ p (G : SplitG (M p).L), (M p).split = some G →
    (G.q : (A p).Fp) = (resChar p : (A p).Fp) ∧ ∃ S, (A p).split = some S ∧ S.e = G.e

section Inhabitant

end Inhabitant

section Local
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]


end Local

namespace ModFam
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {g₁ g₂ : ℕ} (X : ModFam F E sig g₁ g₂)


def nu (r a s : ℕ) : ℤ := 2 * (r : ℤ) + 1 - 2 * a - s


end ModFam

def lead {K : Type} [CommRing K] {n : ℕ} (Z : Matrix (Fin n) (Fin n) K) (l : ℕ) (hl : l ≤ n) : K :=
  (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det

def GZ {F E : Type} [Field F] [Field E] [Algebra F E] (sig : E →ₐ[F] E) {r : ℕ} (T T' : F)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : E :=
  Z.det * sig Z.det - algebraMap F E (T * T') * (lead Z r (Nat.le_succ r) * sig (lead Z r (Nat.le_succ r)))

def psiInf {E : Type} [Field E] [NumberField E] (x : E) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ E x : ℚ) : ℂ))

end GlobalTheory.SgGlob
end
end
