module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

section Orbits

variable (O : Type) [CommRing O] {A : Type} [CommRing A] [Algebra O A]

def mulLat (t : A) (L : Submodule O A) : Submodule O A := L.map (LinearMap.mulLeft O t)

def stabLat (L : Submodule O A) : Subgroup Aˣ where
  carrier := {t | ∀ y, y ∈ L ↔ (t : A) * y ∈ L}
  one_mem' := by intro y; simp
  mul_mem' := by
    intro a b ha hb y
    rw [hb y, ha ((b : A) * y), Units.val_mul, mul_assoc]
  inv_mem' := by
    intro a ha y
    have := ha (((a⁻¹ : Aˣ) : A) * y)
    rw [← mul_assoc, Units.mul_inv, one_mul] at this
    exact this.symm

def intUnits (A : Type) [CommRing A] [Algebra O A] : Subgroup Aˣ where
  carrier := {t | IsIntegral O (t : A) ∧ IsIntegral O ((t⁻¹ : Aˣ) : A)}
  one_mem' := by simpa using isIntegral_one
  mul_mem' := by
    intro a b ha hb
    refine ⟨by simpa using ha.1.mul hb.1, ?_⟩
    rw [mul_inv_rev, Units.val_mul]
    exact hb.2.mul ha.2
  inv_mem' := by
    intro a ha
    exact ⟨ha.2, by simpa using ha.1⟩

def Orb (G : Subgroup Aˣ) (X : Set (Submodule O A)) : Type :=
  Quot fun L M : X => ∃ t ∈ G, (M : Submodule O A) = mulLat O (t : A) (L : Submodule O A)

def orbSum (G : Subgroup Aˣ) (X : Set (Submodule O A)) (w : Submodule O A → ℚ) : ℚ :=
  ∑ᶠ o : Orb O G X, w (Quot.out o).1 *
    (((stabLat O (Quot.out o).1 ⊓ G).relIndex (intUnits O A ⊓ G) : ℕ) : ℚ)

def IsLat (E : Type) [Field E] [Algebra E A] (L : Submodule O A) : Prop :=
  L.FG ∧ Submodule.span E (L : Set A) = ⊤

def countGL (E : Type) [Field E] [Algebra E A] (g : A) : ℚ :=
  orbSum O ⊤ {L | IsLat O E L ∧ ∀ y ∈ L, g * y ∈ L} fun _ => 1

end Orbits

def val (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {E : Type} [Field E]
    [Algebra O E] [IsFractionRing O E] (x : E) : ℤ :=
  -WithZero.log ((IsDiscreteValuationRing.maximalIdeal O).valuation E x)

structure UQ : Type 1 where
  O : Type
  E : Type
  [cO : CommRing O]
  [dO : IsDomain O]
  [dvr : IsDiscreteValuationRing O]
  [cpl : IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [fin : Finite (IsLocalRing.ResidueField O)]
  [fE : Field E]
  [aOE : Algebra O E]
  [frac : IsFractionRing O E]
  [c0 : CharZero E]
  c : E ≃+* E
  c_c : ∀ x, c (c x) = x
  c_int : ∀ x : O, ∃ y : O, c (algebraMap O E x) = algebraMap O E y
  c_res : ∃ x y : O, c (algebraMap O E x) = algebraMap O E y ∧ x - y ∉ IsLocalRing.maximalIdeal O
  q : ℕ
  card_res : Nat.card (IsLocalRing.ResidueField O) = q ^ 2

attribute [instance] UQ.cO UQ.dO UQ.dvr UQ.cpl UQ.fin UQ.fE UQ.aOE UQ.frac UQ.c0

def UQ.Odd (K : UQ) : Prop := IsUnit (2 : K.O)

def UQ.eta (K : UQ) (x : K.E) : ℚ := (-1 : ℚ) ^ val K.O x

structure InvAlg (K : UQ) : Type 1 where
  A : Type
  [cA : CommRing A]
  [aE : Algebra K.E A]
  [aO : Algebra K.O A]
  [tow : IsScalarTower K.O K.E A]
  [fd : Module.Finite K.E A]
  σ : A ≃+* A
  σ_σ : ∀ y, σ (σ y) = y
  σ_alg : ∀ e : K.E, σ (algebraMap K.E A e) = algebraMap K.E A (K.c e)
  g : A

attribute [instance] InvAlg.cA InvAlg.aE InvAlg.aO InvAlg.tow InvAlg.fd

namespace InvAlg

variable {K : UQ} (B : InvAlg K)

def P : K.E[X] := (LinearMap.mulLeft K.E B.g).charpoly

def prod (B₁ B₂ : InvAlg K) : InvAlg K where
  A := B₁.A × B₂.A
  σ := RingEquiv.prodCongr B₁.σ B₂.σ
  σ_σ := fun y => Prod.ext (B₁.σ_σ y.1) (B₂.σ_σ y.2)
  σ_alg := fun e => Prod.ext (B₁.σ_alg e) (B₂.σ_alg e)
  g := (B₁.g, B₂.g)

def herm (x y z : B.A) : K.E := Algebra.trace K.E B.A (x * y * B.σ z)

def X (x : B.A) : Set (Submodule K.O B.A) :=
  {L | IsLat K.O K.E L ∧ (∀ y ∈ L, B.g * y ∈ L) ∧
    ∀ y, y ∈ L ↔ ∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range}

def T : Subgroup B.Aˣ where
  carrier := {t | (t : B.A) * B.σ (t : B.A) = 1}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at ha hb ⊢
    calc (a : B.A) * b * (B.σ a * B.σ b) = ((a : B.A) * B.σ a) * ((b : B.A) * B.σ b) := by ring
      _ = 1 := by rw [ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h1 : B.σ (a : B.A) * B.σ ((a⁻¹ : B.Aˣ) : B.A) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    calc ((a⁻¹ : B.Aˣ) : B.A) * B.σ ((a⁻¹ : B.Aˣ) : B.A)
        = ((a⁻¹ : B.Aˣ) : B.A) * B.σ ((a⁻¹ : B.Aˣ) : B.A) * ((a : B.A) * B.σ a) := by rw [ha, mul_one]
      _ = (((a⁻¹ : B.Aˣ) : B.A) * a) * (B.σ (a : B.A) * B.σ ((a⁻¹ : B.Aˣ) : B.A)) := by ring
      _ = 1 := by rw [h1, Units.inv_mul, one_mul]

def N (x : B.A) : ℚ := orbSum K.O B.T (B.X x) fun _ => 1

def gramDet (x : B.A) : K.E :=
  (Matrix.of fun i j => B.herm x (Module.finBasis K.E B.A i) (Module.finBasis K.E B.A j)).det

def Cl : Type :=
  Quot fun x y : {x : B.Aˣ // B.σ (x : B.A) = x} => ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A))

def Cl.rep {B : InvAlg K} (k : B.Cl) : B.A := ((Quot.out k).1 : B.Aˣ)

def stSum : ℚ := ∑ᶠ k : B.Cl, B.N k.rep

def kapSum (B₁ B₂ : InvAlg K) : ℚ :=
  ∑ᶠ k : (B₁.prod B₂).Cl, K.eta (B₁.gramDet (Cl.rep k).1) * (B₁.prod B₂).N k.rep

def Identity (B₁ B₂ : InvAlg K) : Prop :=
  (-(K.q : ℚ)) ^ (-val K.O (resultant B₁.P B₂.P)) * kapSum B₁ B₂ = B₁.stSum * B₂.stSum

end InvAlg

def UnitLemmaGroup : Prop :=
  ∀ (K : UQ), K.Odd → ∀ B₁ B₂ : InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 →
    (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂

def UnitLemmaLie : Prop :=
  ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g →
    (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂

end GlobalTheory.UnitLemma
end
end

section

noncomputable section

open PowerSeries

namespace GlobalTheory.NB

structure Fr (l : ℕ) (O : Type) [CommRing O] where
  prime : l.Prime
  odd : l ≠ 2
  l_nonunit : ¬ IsUnit (l : O)

  root : ∃ x : O, Associated (x ^ (l - 1)) (l : O)
  e : ℕ
  s : ℕ
  es : e * s = l - 1
  ϖ : Fin e → O
  ϖ_val : ∀ τ, Associated (ϖ τ ^ e) (l : O)
  ϖ_sub : ∀ τ τ', τ ≠ τ' → Associated (ϖ τ - ϖ τ') (ϖ τ)
  E : O⟦X⟧
  E_def : E = ∏ τ, (X - C (ϖ τ))
  φ : O⟦X⟧ →ₐ[O] O⟦X⟧
  γ : O⟦X⟧ →ₐ[O] O⟦X⟧
  comm : ∀ a, φ (γ a) = γ (φ a)
  u : (O⟦X⟧)ˣ
  φ_X : φ X = (u : O⟦X⟧) * X * E ^ s
  κ : (O⟦X⟧)ˣ
  γ_X : γ X = X * (1 + (κ : O⟦X⟧) * E)
  χ : Oˣ
  χ_gen : Associated ((χ : O) - 1) (l : O)
  χ_zero : constantCoeff (1 + (κ : O⟦X⟧) * E) = (χ : O) ^ s

  lev : Fin e → (O⟦X⟧ ≃ₐ[O] O⟦X⟧)
  lev_X : ∀ τ, lev τ X = X + C (ϖ τ)

  χ_lev : ∀ τ, ∃ w : O⟦X⟧, γ (X - C (ϖ τ)) = (X - C (ϖ τ)) * w ∧ constantCoeff (lev τ w) = (χ : O)

  lvl_red : ∀ (k : ℕ) (a : O⟦X⟧), (φ ^ k) E ∣ a ^ 2 → (φ ^ k) E ∣ a

  lvl_triv : ∀ (k : ℕ) (a : O⟦X⟧), (φ ^ k) E ∣ (γ ^ (l ^ k)) a - a

  lvl_inv : e = 1 → ∀ (k : ℕ) (a : O⟦X⟧), (φ ^ k) E ∣ γ a - a → ∃ c : O, (φ ^ k) E ∣ a - C c

  EE : Type
  [eeRing : CommRing EE]
  [eeAlgA : Algebra O⟦X⟧ EE]
  [eeAlgO : Algebra O EE]
  [eeTow : IsScalarTower O O⟦X⟧ EE]
  EE_inj : Function.Injective (algebraMap O⟦X⟧ EE)
  EE_X : IsUnit (algebraMap O⟦X⟧ EE X)
  EE_complete : IsAdicComplete (Ideal.span {(l : EE)}) EE
  EE_dense : ∀ (x : EE) (k : ℕ), ∃ (a : O⟦X⟧) (m : ℕ),
    (l : EE) ^ k ∣ x * algebraMap O⟦X⟧ EE (X ^ m) - algebraMap O⟦X⟧ EE a
  EE_sat : ∀ (a : O⟦X⟧) (k : ℕ), (l : EE) ^ k ∣ algebraMap O⟦X⟧ EE a → (l : O⟦X⟧) ^ k ∣ a
  φE : EE →ₐ[O] EE
  φE_ext : ∀ a, φE (algebraMap O⟦X⟧ EE a) = algebraMap O⟦X⟧ EE (φ a)
  γE : EE →ₐ[O] EE
  γE_ext : ∀ a, γE (algebraMap O⟦X⟧ EE a) = algebraMap O⟦X⟧ EE (γ a)

  coeffRing : ∃ (_ : IsDomain O) (_ : IsDiscreteValuationRing O),
      IsAdicComplete (IsLocalRing.maximalIdeal O) O ∧ CharZero O := by
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

attribute [instance] Fr.eeRing Fr.eeAlgA Fr.eeAlgO Fr.eeTow

open Classical

namespace Fr

variable {l : ℕ} {O : Type} [CommRing O] (R : Fr l O)

abbrev ι : O⟦X⟧ →+* R.EE := algebraMap O⟦X⟧ R.EE

def N0 (r : ℕ) : Submodule O⟦X⟧ (Fin r → R.EE) :=
  Submodule.pi Set.univ fun _ => LinearMap.range (Algebra.linearMap O⟦X⟧ R.EE)

variable [IsDomain O]

end Fr

structure Sys {l : ℕ} {O : Type} [CommRing O] (R : Fr l O) (n r : ℕ) where
  M : ℕ
  Φ : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧
  G : ZMod n → Matrix (Fin r) (Fin r) O⟦X⟧
  G_one : ∀ i, ∃ B : Matrix (Fin r) (Fin r) O⟦X⟧, G i = 1 + (X : O⟦X⟧) • B
  Φ_inv : ∀ i, ∃ (k : ℕ) (Ψ : Matrix (Fin r) (Fin r) O⟦X⟧), Φ i * Ψ = R.E ^ k • (1 : Matrix _ _ _)
  comm : ∀ i, R.E ^ M • (G i * (Φ i).map R.γ) = R.γ R.E ^ M • (Φ i * (G (i - 1)).map R.φ)

abbrev DD {l : ℕ} {O : Type} [CommRing O] (R : Fr l O) (n r : ℕ) : Type := ZMod n → Fin r → R.EE

namespace Sys

variable {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r : ℕ} (S : Sys R n r)

def φl (i : ZMod n) : (Fin r → R.EE) →ₗ[O] (Fin r → R.EE) :=
  ((Ring.inverse (R.ι R.E) ^ S.M • (S.Φ i).map R.ι).mulVecLin.restrictScalars O).comp
    (R.φE.toLinearMap.compLeft (Fin r))

def γl (i : ZMod n) : (Fin r → R.EE) →ₗ[O] (Fin r → R.EE) :=
  (((S.G i).map R.ι).mulVecLin.restrictScalars O).comp (R.γE.toLinearMap.compLeft (Fin r))

def φD : DD R n r →ₗ[O] DD R n r := LinearMap.pi fun i => (S.φl i).comp (LinearMap.proj (i - 1))

def γD : DD R n r →ₗ[O] DD R n r := LinearMap.pi fun i => (S.γl i).comp (LinearMap.proj i)

def Z1 : Submodule O (DD R n r × DD R n r) :=
  LinearMap.ker ((S.γD - LinearMap.id).coprod (-(S.φD - LinearMap.id)))

def B1 : Submodule O (DD R n r × DD R n r) :=
  LinearMap.range ((S.φD - LinearMap.id).prod (S.γD - LinearMap.id))

variable [IsDomain O]

end Sys

structure Hom {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r r' : ℕ} (S : Sys R n r)
    (S' : Sys R n r') where
  F : ZMod n → Matrix (Fin r') (Fin r) O⟦X⟧
  φ_comm : ∀ i x, ((F i).map R.ι).mulVec (S.φl i x) = S'.φl i (((F (i - 1)).map R.ι).mulVec x)
  γ_comm : ∀ i x, ((F i).map R.ι).mulVec (S.γl i x) = S'.γl i (((F i).map R.ι).mulVec x)

namespace Hom

variable {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r r' r'' : ℕ} {S : Sys R n r} {S' : Sys R n r'}
  {S'' : Sys R n r''} (F : Hom S S')

def comp (F' : Hom S' S'') (F : Hom S S') : Hom S S'' where
  F := fun i => F'.F i * F.F i
  φ_comm := fun i x => by
    rw [Matrix.map_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, F.φ_comm,
      F'.φ_comm]
  γ_comm := fun i x => by
    rw [Matrix.map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, F.γ_comm, F'.γ_comm]

end Hom

end GlobalTheory.NB
end
end
