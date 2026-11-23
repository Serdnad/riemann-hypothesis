module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RepresentationTheory.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Polynomial

noncomputable section

namespace Formalism.NG

universe u

def StatBurnside : Prop :=
  ∀ (k A V : Type*) [Field k] [Ring A] [Algebra k A] [AddCommGroup V] [Module k V] [Module A V]
    [IsScalarTower k A V] [FiniteDimensional k V], IsSimpleModule A V →
    (∀ φ : V →ₗ[A] V, ∃ c : k, ∀ v, φ v = c • v) →
    Function.Surjective (fun a : A => DistribSMul.toLinearMap k V a)

def StatSplitAlg : Prop :=
  ∀ (T : Type u) [CommRing T] (P : T[X]), P.Monic →
    ∃ (T' : Type u) (_ : CommRing T') (_ : Algebra T T') (rr : Fin P.natDegree → T'),
      Module.Free T T' ∧ Module.Finite T T' ∧ Module.finrank T T' = P.natDegree.factorial ∧
      P.map (algebraMap T T') = ∏ i, (X - C (rr i)) ∧
      Algebra.adjoin T (Set.range rr) = ⊤ ∧
      ∀ (B : Type u) [CommRing B] [Algebra T B] (a : Fin P.natDegree → B),
        P.map (algebraMap T B) = ∏ i, (X - C (a i)) →
        ∃! φ : T' →ₐ[T] B, ∀ i, φ (rr i) = a i

def StatSplitFibre : Prop :=
  ∀ (T T' K : Type*) [CommRing T] [CommRing T'] [Algebra T T'] [Field K] (P : T[X]), P.Monic →
    ∀ (rr : Fin P.natDegree → T'), P.map (algebraMap T T') = ∏ i, (X - C (rr i)) →
      Algebra.adjoin T (Set.range rr) = ⊤ →
    ∀ (b : Module.Basis (Fin P.natDegree.factorial) T T') (x : T →+* K) (a : Fin P.natDegree → K),
      Function.Injective a → P.map x = ∏ i, (X - C (a i)) →
      ∀ c : Fin P.natDegree.factorial → K,
        (∀ φ : T' →+* K, φ.comp (algebraMap T T') = x → ∑ k, c k * φ (b k) = 0) → c = 0

end Formalism.NG
end
end

section

open Finset Polynomial

noncomputable section

namespace Formalism.NG

section Idem

variable {T A : Type*} [CommRing T] [Ring A] [Algebra T A]

end Idem

section Pres

variable {R : Type*} [Ring R] {m g : Type*} [Fintype m] [Fintype g]

def relSpan (Θ : Matrix m g R) : Submodule R (g → R) := Submodule.span R (Set.range Θ)

abbrev Coker (Θ : Matrix m g R) : Type _ := (g → R) ⧸ relSpan Θ

def relMap (O : Type*) [CommRing O] (M : Type*) [AddCommGroup M] [Module R M] [Module O M]
    [SMulCommClass R O M] (Θ : Matrix m g R) : (g → M) →ₗ[O] (m → M) where
  toFun v i := ∑ j, Θ i j • v j
  map_add' v w := by ext i; simp [smul_add, Finset.sum_add_distrib]
  map_smul' c v := by ext i; simp [Finset.smul_sum, smul_comm]

end Pres

section DVR

variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

abbrev KO : Type _ := FractionRing O ⧸ (1 : Submodule O (FractionRing O))

def matQ {ι : Type*} [Fintype ι] (A : Matrix ι ι O) : (ι → KO O) →ₗ[O] (ι → KO O) :=
  relMap O (KO O) A

end DVR

def StatLenKer : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ι : Type) [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι O),
    Module.length O (LinearMap.ker (matQ O A)) = IsDiscreteValuationRing.addVal O A.det

def bigMat {R O : Type*} [CommRing O] {g d : Type*} (ρ : R → Matrix d d O) (Θ : Matrix g g R) :
    Matrix (g × d) (g × d) O :=
  fun p q => ρ (Θ p.1 q.1) p.2 q.2

abbrev baseChange {T : Type*} (T' : Type*) [CommRing T] [CommRing T'] [Algebra T T'] (J : Ideal T) :
    Type _ :=
  T' ⧸ Ideal.map (algebraMap T T') J

end Formalism.NG
end
end

section

noncomputable section

namespace Formalism.NG

def characterColumnKernelLengthBound : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (s₀ : ℕ), 1 ≤ s₀ → (l = 2 → 2 ≤ s₀) →
    ∀ (x : ℤ), (l : ℤ) ^ s₀ ∣ x - 1 → ¬ (l : ℤ) ^ (s₀ + 1) ∣ x - 1 →
    ∀ a b : ℕ, a < b → padicValInt l (x ^ b - x ^ a) = s₀ + padicValNat l (b - a)

end Formalism.NG
end
end

section

open Finset Classical

noncomputable section

namespace Formalism.NG

section Cochains
variable {O : Type*} [CommRing O] {D : Type*} [Group D] {M : Type*} [AddCommGroup M] [Module O M]

def coD0 (ρ : Representation O D M) : M →ₗ[O] (D → M) where
  toFun v g := ρ g v - v
  map_add' v w := by ext g; simp only [map_add (f := _), Pi.add_apply]; abel
  map_smul' c v := by ext g; simp only [map_smul, Pi.smul_apply, RingHom.id_apply, smul_sub]

def coB1 (ρ : Representation O D M) : Submodule O (D → M) := LinearMap.range (coD0 ρ)

def characterColumnKernelSet (ρ : Representation O D M) : Set (D → M) :=
  {c | ∀ g h, c (g * h) = c g + ρ g (c h)}

def characterColumnKernelPairSetVariant (ρ : Representation O D M) : Set (D → D → M) :=
  {c | ∀ g h k, ρ g (c h k) - c (g * h) k + c g (h * k) - c g h = 0}

end Cochains

def cup1 {O D M₁ M₂ N : Type*} [CommRing O] [Group D] [AddCommGroup M₁] [Module O M₁]
    [AddCommGroup M₂] [Module O M₂] [AddCommGroup N] [Module O N]
    (ρ₂ : Representation O D M₂) (β : M₁ →ₗ[O] M₂ →ₗ[O] N) (a : D → M₁) (b : D → M₂) :
    D → D → N :=
  fun g h => β (a g) (ρ₂ g (b h))

def IsEquivPairing {O D M₁ M₂ N : Type*} [CommRing O] [Group D] [AddCommGroup M₁] [Module O M₁]
    [AddCommGroup M₂] [Module O M₂] [AddCommGroup N] [Module O N]
    (ρ₁ : Representation O D M₁) (ρ₂ : Representation O D M₂) (ρN : Representation O D N)
    (β : M₁ →ₗ[O] M₂ →ₗ[O] N) : Prop :=
  ∀ g m n, β (ρ₁ g m) (ρ₂ g n) = ρN g (β m n)

def IsEquivMap {O D M M' : Type*} [CommRing O] [Group D] [AddCommGroup M] [Module O M]
    [AddCommGroup M'] [Module O M'] (ρ : Representation O D M) (ρ' : Representation O D M')
    (f : M →ₗ[O] M') : Prop :=
  ∀ g m, f (ρ g m) = ρ' g (f m)

def colD {A T' K V G : Type*} [Ring A] [CommRing T'] [Algebra T' A] [Field K] [Group G]
    [AddCommGroup V] [Module A V] [Module K V] [SMulCommClass A K V]
    (r : G →* A) (χ : G →* T'ˣ) (D : Subgroup G) : V →ₗ[K] (D → V) where
  toFun v g := ((((χ g)⁻¹ : T'ˣ) : T') • r g) • v - v
  map_add' v w := by ext g; simp only [smul_add, Pi.add_apply]; abel
  map_smul' c v := by ext g; simp only [Pi.smul_apply, RingHom.id_apply, smul_sub, smul_comm]

end Formalism.NG
end
end

section

open Finset

namespace Formalism.NG

universe uO uT uT' uΩ uR

theorem addVal_prod {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ι : Type*} (s : Finset ι) (f : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, f i) = ∑ i ∈ s, IsDiscreteValuationRing.addVal O (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

end Formalism.NG
end
