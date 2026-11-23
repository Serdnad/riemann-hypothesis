module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Data.EReal.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.LinearAlgebra.BilinearMap
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E] [Module Ω E]

def LocFree (R : Subalgebra o Ω) (r : ℕ) (L : AddSubgroup E) : Prop :=
  (∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) ∧
  ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ R) ∧ (∀ l, c l ∈ R) ∧ ∑ l, c l * f l = 1 ∧
    ∀ l, ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, f l ^ n • e ∈ L) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q

def spanOver (R : Subalgebra o Ω) (S : Set E) : AddSubgroup E :=
  AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ S, v = a • e}

def GenDual (R : Subalgebra o Ω) (L : AddSubgroup E) {M : ℕ} (φ : Fin M → Module.Dual Ω E) : Prop :=
  (∀ l, ∀ v ∈ L, φ l v ∈ R) ∧
  ∀ ψ : Module.Dual Ω E, (∀ v ∈ L, ψ v ∈ R) → ∃ u : Fin M → Ω, (∀ l, u l ∈ R) ∧ ψ = ∑ l, u l • φ l

noncomputable def flagMinor {N M : ℕ} (φ : Fin M → Module.Dual Ω E) (w : Fin N → E) (i : ℕ) (hi : i ≤ N)
    (I : Fin i → Fin M) : Ω :=
  Matrix.det (Matrix.of fun a b : Fin i => φ (I a) (w (Fin.castLE hi b)))

end GlobalTheory.CompanionTheory.Ar.Num
end

section

namespace GlobalTheory.CompanionTheory.Ar.Crv

def lmuNum {T : Type} [Fintype T] (j q : ℕ) (μ w l : T → ℕ → ℝ) : ℝ :=
  -∑ τ, ((∑ i ∈ Finset.range j, μ τ (i + 1) * (w τ (i + 1) - w τ i)) +
    ∑ m ∈ Finset.range q, μ τ (j + m + 1) * (l τ (q - m - 1) - l τ (q - m)))

def GapCond {T : Type} [Fintype T] (p j q : ℕ) (μ : T → ℕ → ℝ) : Prop :=
  (∀ τ i, 1 ≤ i → i < j + q → μ τ (i + 1) ≤ μ τ i) ∧
    ∃ M g : ℝ, (∀ τ i, 1 ≤ i → i ≤ j + q → |μ τ i| ≤ M) ∧ (∀ τ, g ≤ μ τ j - μ τ (j + 1)) ∧
      4 * (Fintype.card T : ℝ) * M ≤ ((p : ℝ) - 2) * g

end GlobalTheory.CompanionTheory.Ar.Crv
end

section

namespace GlobalTheory.CompanionTheory.Ar.BT

variable {R : Type} [CommRing R] {T H : Type} [CommGroup T] [CommGroup H]

def prodSpan (A : Subalgebra R (T → R)) : Submodule R (T × T → R) :=
  Submodule.span R {g | ∃ a ∈ A, ∃ b ∈ A, g = fun z => a z.1 * b z.2}

structure IsHopfOrder (A : Subalgebra R (T → R)) : Prop where

  finite : Module.Finite R A

  projective : Module.Projective R A

  full : ∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A

  comul : ∀ f ∈ A, (fun z : T × T => f (z.1 * z.2)) ∈ prodSpan A

  inv : ∀ f ∈ A, (fun x => f x⁻¹) ∈ A

def indOrder (ι : H →* T) (A : Subalgebra R (H → R)) : Subalgebra R (T → R) where
  carrier := {f | ∀ t, (fun h => f (t * ι h)) ∈ A}
  mul_mem' hf hg t := A.mul_mem (hf t) (hg t)
  add_mem' hf hg t := A.add_mem (hf t) (hg t)
  algebraMap_mem' r _ := A.algebraMap_mem r

def extOrder {R' : Type} [CommRing R'] (φ : R →+* R') (A : Subalgebra R (T → R)) : Subalgebra R' (T → R') :=
  Algebra.adjoin R' {g | ∃ f ∈ A, g = fun t => φ (f t)}

def evalAt (A : Subalgebra R (T → R)) (t : T) : A →ₐ[R] R :=
  (Pi.evalAlgHom R (fun _ : T => R) t).comp A.val

def augIdeal (A : Subalgebra R (T → R)) : Ideal A := RingHom.ker (evalAt A 1)

abbrev omega (A : Subalgebra R (T → R)) : Type := (augIdeal A).Cotangent


open scoped Classical in
open Classical in
noncomputable def dlogChar (A : Subalgebra R (T → R)) (χ : T →* Rˣ) : omega A :=
  if h : (fun t => ((χ t : Rˣ) : R)) ∈ A then
    (augIdeal A).toCotangent ⟨⟨_, h⟩ - 1, by simp [augIdeal, evalAt, RingHom.mem_ker]⟩
  else 0

namespace OrderApi


omit [CommGroup T] in
theorem mul_mem_prodSpan {A : Subalgebra R (T → R)} {a b : T → R} (ha : a ∈ A) (hb : b ∈ A) :
    (fun z : T × T => a z.1 * b z.2) ∈ prodSpan A :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩

theorem mem_indOrder (ι : H →* T) (A : Subalgebra R (H → R)) (f : T → R) :
    f ∈ indOrder ι A ↔ ∀ t, (fun h => f (t * ι h)) ∈ A := Iff.rfl


omit [CommGroup T] in
theorem comp_mem_extOrder {R' : Type} [CommRing R'] (φ : R →+* R') {A : Subalgebra R (T → R)} {f : T → R}
    (hf : f ∈ A) : (fun t => φ (f t)) ∈ extOrder φ A :=
  Algebra.subset_adjoin ⟨f, hf, rfl⟩

theorem mem_augIdeal (A : Subalgebra R (T → R)) (f : A) : f ∈ augIdeal A ↔ (f : T → R) 1 = 0 := Iff.rfl

theorem dlogChar_of_mem (A : Subalgebra R (T → R)) (χ : T →* Rˣ) (h : (fun t => ((χ t : Rˣ) : R)) ∈ A) :
    dlogChar A χ =
      (augIdeal A).toCotangent ⟨⟨_, h⟩ - 1, by simp [augIdeal, evalAt, RingHom.mem_ker]⟩ := by
  rw [dlogChar, dite_eq_left h]

end OrderApi

namespace OrderEx

end OrderEx

end GlobalTheory.CompanionTheory.Ar.BT
end

section

namespace GlobalTheory.CompanionTheory.Ar.Ref

open NumberField IsDedekindDomain

noncomputable section

variable {K : Type} [Field K] [NumberField K]

def vl (la : HeightOneSpectrum (𝓞 K)) (x : K) : ℤ := -WithZero.log (la.valuation K x)

structure PtSys (K : Type) [Field K] [NumberField K] (R : Type) [CommRing R] [Algebra K R] where

  Pt : HeightOneSpectrum (𝓞 K) → Type

  val : ∀ {la}, Pt la → R → EReal
  val_zero : ∀ {la} (y : Pt la), val y 0 = ⊤
  val_ne_bot : ∀ {la} (y : Pt la) f, val y f ≠ ⊥
  val_add : ∀ {la} (y : Pt la) f g, min (val y f) (val y g) ≤ val y (f + g)
  val_smul : ∀ {la} (y : Pt la) (a : K) f, a ≠ 0 → val y (a • f) = (((vl la a : ℤ) : ℝ) : EReal) + val y f
  val_mul : ∀ {la} (y : Pt la) f g, val y (f * g) = val y f + val y g

namespace PtSys

variable {R : Type} [CommRing R] [Algebra K R] (S : PtSys K R)

end PtSys

end

end GlobalTheory.CompanionTheory.Ar.Ref
end

section

namespace GlobalTheory.CompanionTheory.Ar

structure ProIso (O : Type) [CommRing O] {L L' : Type} [AddCommGroup L] [Module O L] [AddCommGroup L']
    [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L') where

  a : ℕ → (L →ₗ[O] L')
  inj : ∀ n, 0 < n → ∀ x, (∃ y, a n x = n • y) ↔ ∃ y, x = n • y
  surj : ∀ n, 0 < n → ∀ y, ∃ x e, y = a n x + n • e
  isom : ∀ n : ℕ, 0 < n → ∀ x y, (n : ℤ) ∣ B' (a n x) (a n y) - B x y
  compat : ∀ n m, 0 < n → 0 < m → ∀ x, ∃ e, a (n * m) x = a n x + n • e

structure ProIsoAt (p : ℕ) (O : Type) [CommRing O] {L L' : Type} [AddCommGroup L] [Module O L]
    [AddCommGroup L'] [Module O L'] (B : LinearMap.BilinForm ℤ L) (B' : LinearMap.BilinForm ℤ L') where

  a : ℕ → (L →ₗ[O] L')
  inj : ∀ k x, (∃ y, a k x = p ^ k • y) ↔ ∃ y, x = p ^ k • y
  surj : ∀ k y, ∃ x e, y = a k x + p ^ k • e
  isom : ∀ k x y, ((p : ℤ) ^ k) ∣ B' (a k x) (a k y) - B x y
  compat : ∀ k x, ∃ e, a (k + 1) x = a k x + p ^ k • e

variable {O : Type} [CommRing O] {L L' L'' : Type} [AddCommGroup L] [Module O L] [AddCommGroup L']
  [Module O L'] [AddCommGroup L''] [Module O L''] {B : LinearMap.BilinForm ℤ L}
  {B' : LinearMap.BilinForm ℤ L'} {B'' : LinearMap.BilinForm ℤ L''}

def ProIso.IsInv (f : ProIso O B B') (g : ProIso O B' B) : Prop :=
  (∀ n, 0 < n → ∀ x, ∃ e, g.a n (f.a n x) = x + n • e) ∧ ∀ n, 0 < n → ∀ y, ∃ e, f.a n (g.a n y) = y + n • e

end GlobalTheory.CompanionTheory.Ar
end
