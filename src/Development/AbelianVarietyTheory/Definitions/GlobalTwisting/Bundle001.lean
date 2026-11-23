module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section
end

section

noncomputable section

namespace GlobalTheory.OrdLoc

variable {G : Type} [Group G] [TopologicalSpace G] (E : Type) [NontriviallyNormedField E]

variable {E}

def Z1 (γ : G →* Eˣ) : Submodule E (G → E) where
  carrier := {c | Continuous c ∧ ∀ g h, c (g * h) = c g + (γ g : E) * c h}
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨ha.add hb, fun g h => by simp only [Pi.add_apply, ha', hb']; ring⟩
  zero_mem' := ⟨continuous_const, fun g h => by simp⟩
  smul_mem' := by
    rintro t a ⟨ha, ha'⟩
    exact ⟨continuous_const.mul ha, fun g h => by simp only [Pi.smul_apply, smul_eq_mul, ha']; ring⟩

end OrdLoc
end GlobalTheory
end
end

section

noncomputable section

open CategoryTheory

namespace GlobalTheory.HomStab

variable {k G : Type} [CommRing k] [Group G]

def permRep (X : Type) [MulAction G X] (A : Rep k G) : Representation k G (X →₀ A.V) where
  toFun g := Finsupp.lmapDomain A.V k (g • ·) ∘ₗ Finsupp.mapRange.linearMap (A.ρ g)
  map_one' := by ext x a; simp
  map_mul' g h := by ext x a; simp [mul_smul]

@[simp] theorem permRep_single {X : Type} [MulAction G X] (A : Rep k G) (g : G) (x : X) (a : A.V) :
    permRep X A g (Finsupp.single x a) = Finsupp.single (g • x) (A.ρ g a) := by
  simp [permRep]

abbrev permT (X : Type) [MulAction G X] (A : Rep k G) : Rep k G := Rep.of (permRep X A)


variable (k G) in
abbrev perm (X : Type) [MulAction G X] : Rep k G := permT X (Rep.trivial k G k)

def permCoef (X : Type) [MulAction G X] {A B : Rep k G} (f : A ⟶ B) : permT X A ⟶ permT X B :=
  Rep.ofHom ⟨Finsupp.mapRange.linearMap f.hom.toLinearMap, fun g => by
    ext x a; simp [Rep.hom_comm_apply f]⟩

def permMap {X Y : Type} [MulAction G X] [MulAction G Y] (f : X → Y) (hf : ∀ (g : G) x, f (g • x) = g • f x)
    (A : Rep k G) : permT X A ⟶ permT Y A :=
  Rep.ofHom ⟨Finsupp.lmapDomain A.V k f, fun g => by ext x a; simp [hf]⟩

def ptMap {H X : Type} [Group H] [MulAction G X] (φ : H →* G) (x : X) (hx : ∀ h, φ h • x = x) (A : Rep k G) :
    Rep.res φ A ⟶ Rep.res φ (permT X A) :=
  Rep.ofHom ⟨Finsupp.lsingle x, fun h => LinearMap.ext fun a => by
    change Finsupp.single x (A.ρ (φ h) a) = permRep X A (φ h) (Finsupp.single x a)
    rw [permRep_single, hx]⟩


variable (k) in
def ptH {H X : Type} [Group H] [MulAction G X] (φ : H →* G) (x : X) (hx : ∀ h, φ h • x = x) (n : ℕ) :
    groupHomology (Rep.trivial k H k) n ⟶ groupHomology (perm (k := k) (G := G) X) n :=
  groupHomology.map (A := Rep.trivial k H k) φ (ptMap φ x hx (Rep.trivial k G k)) n

abbrev hMap {A B : Rep k G} (f : A ⟶ B) (n : ℕ) : groupHomology A n ⟶ groupHomology B n :=
  groupHomology.map (MonoidHom.id G) f n

end GlobalTheory.HomStab

end
end

section

noncomputable section

open scoped Matrix

namespace GlobalTheory.SeqCx

def bd (V : Type) : (List V →₀ ℤ) →ₗ[ℤ] (List V →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun l : List V =>
    ∑ i ∈ Finset.range l.length, (-1 : ℤ) ^ i • Finsupp.single (l.eraseIdx i) (1 : ℤ)

def chains {V : Type} (F : Set (List V)) (p : ℕ) : Submodule ℤ (List V →₀ ℤ) :=
  Finsupp.supported ℤ ℤ {l | l ∈ F ∧ l.length = p}

def ExactAt {V : Type} (F : Set (List V)) (p : ℕ) : Prop :=
  ∀ c ∈ chains F p, bd V c = 0 → ∃ b ∈ chains F (p + 1), bd V b = c

def SubClosed {V : Type} (F : Set (List V)) : Prop := ∀ l ∈ F, ∀ l' : List V, l'.Sublist l → l' ∈ F

def linkIn {V : Type} (F : Set (List V)) (S : Set V) (τ : List V) : Set (List V) :=
  {w | (∀ x ∈ w, x ∈ S) ∧ τ ++ w ∈ F}

def uniSeq (R : Type) [CommRing R] (n : ℕ) : Set (List (Fin n → R)) :=
  {l | ∃ f : Fin l.length → Fin n → R, ∀ i j : Fin l.length, f i ⬝ᵥ l.get j = if i = j then 1 else 0}

def splitSeq (R : Type) [CommRing R] (n : ℕ) : Set (List ((Fin n → R) × (Fin n → R))) :=
  {l | ∀ i j : Fin l.length, (l.get i).2 ⬝ᵥ (l.get j).1 = if i = j then 1 else 0}

end GlobalTheory.SeqCx

end
end
