module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BundleObjects
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def TwistedDualGensExpress.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (ϖ : R) (Ω : Type) [Field Ω] [Algebra R Ω]
    (K : Type) [Fintype K] (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle R (segreVec y) N E),
    SameGenericFibre ϖ B B' →
    ∀ (a a' : K → ℤ) (M M' : ℕ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a φ → IsTwistedDualGens y B' a' φ' →
    ∀ c, segreVec y c ≠ 0 → ∀ m, ∃ (n : ℕ) (r : Fin M → Ω),
      (∀ l, r l ∈ chartRing R (segreVec y) c) ∧
      algebraMap R Ω ϖ ^ n • φ' m = ∑ l, (r l * ∏ k, y ⟨k, c k⟩ ^ (a' k - a k)) • φ l

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def TwistedDualGensSpan.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (Ω : Type) [Field Ω] [Algebra R Ω]
    (K : Type) [Fintype K] (ι : K → Type) (y : (Σ k, ι k) → Ω)
    (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B : ChartBundle R (segreVec y) N E)
    (a : K → ℤ) (M : ℕ) (φ : Fin M → Module.Dual Ω E),
    IsTwistedDualGens y B a φ → ∀ c, segreVec y c ≠ 0 →
      Submodule.span Ω (Set.range φ) = ⊤

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SpanBundleDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (y : (Σ k, ι k) → Ω) (e : ℕ),
    IsMultiProjPrime (pointIdeal F y) →
    ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ (M i : ℕ) (G : Fin M → Fin i → Ω), 0 < i → LinearIndependent Ω (fun j l => G l j) →
    ∀ (c : ∀ k, ι k) (a : K → ℤ) (H : Matrix (Fin i) (Fin i) Ω), segreVec y c ≠ 0 → IsUnit H.det →
      (∀ l m, (Matrix.of G * H) l m ∈ degLat F y a c) →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (s : Fin i → Φ), AlgebraicIndependent Ω s →
      IsMultiProjPrime (projIdeal F y (Pi.basisFun Ω (Fin i))
          (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) ∧
        FieldNumbers.relDim (projIdeal F y (Pi.basisFun Ω (Fin i))
          (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) =
          ((e + i - 1 : ℕ) : WithBot (WithTop ℤ))

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

def SpanBundleTrdegGe.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) (ι : K → Type) (y : (Σ k, ι k) → Ω) (M i : ℕ) (G : Fin M → Fin i → Ω),
    LinearIndependent Ω (fun j l => G l j) →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (s : Fin i → Φ), AlgebraicIndependent Ω s →
      Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) + i ≤
        Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ projIdeal F y (Pi.basisFun Ω (Fin i))
          (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def SpanBundleTrdegLe.Statement : Prop :=
  ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω]
    (K : Type) [Fintype K] (ι : K → Type) (y : (Σ k, ι k) → Ω) (M i : ℕ) (G : Fin M → Fin i → Ω)
    (c : ∀ k, ι k) (a : K → ℤ) (H : Matrix (Fin i) (Fin i) Ω), segreVec y c ≠ 0 → IsUnit H.det →
      (∀ l m, (Matrix.of G * H) l m ∈ degLat F y a c) →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] (s : Fin i → Φ),
      Algebra.trdeg F (MRing (bundleIdx ι M) F ⧸ projIdeal F y (Pi.basisFun Ω (Fin i))
          (fun l => LinearMap.proj l ∘ₗ (Matrix.of G).mulVecLin) s) ≤
        Algebra.trdeg F (MRing ι F ⧸ pointIdeal F y) + i

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

section Objects

variable {K : Type*} {ι : K → Type} {Ω : Type*} [Field Ω] {N M M' : ℕ} {E : Type*} [AddCommGroup E]
  [Module Ω E] {Φ : Type*} [Field Φ] [Algebra Ω Φ]

def pairProjCoord (y : (Σ k, ι k) → Ω) (e : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E) (t : Fin N → Φ) :
    (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ
  | ⟨none, l⟩ => ∑ i, t i * algebraMap Ω Φ (φ' l (e i))
  | ⟨some o, j⟩ => projCoord y e φ t ⟨o, j⟩

def zetaFirst (a : K → ℤ) : Option (Option K) → ℤ
  | none => 0
  | some none => 1
  | some (some k) => -a k

def zetaSecond (a : K → ℤ) : Option (Option K) → ℤ
  | none => 1
  | some none => 0
  | some (some k) => -a k

def liftPairDeg (L : K → ℤ) : Option (Option K) → ℤ
  | some (some k) => L k
  | _ => 0

def liftPairForm {R : Type*} [CommRing R] (M M' : ℕ) (f : MRing ι R) :
    MRing (bundleIdx (bundleIdx ι M) M') R :=
  rename (fun p : Σ k, ι k => (⟨some (some p.1), p.2⟩ : Σ o, bundleIdx (bundleIdx ι M) M' o)) f

end Objects

def zetaPowTimes (n m : ℕ) (R : MvPolynomial (Fin n) ℤ) : MvPolynomial (Fin (1 + n)) ℤ :=
  X (Fin.castAdd n 0) ^ m * rename (Fin.natAdd 1) R

def GenericProjClosureModel.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ), 0 < N → ∀ (E : Type) [AddCommGroup E] [Module Ω E]
      (B B' : ChartBundle O (segreVec y) N E), SameGenericFibre ϖ B B' →
    ∀ (Φ : Type) [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
      (e : Module.Basis (Fin N) Ω E) (t : Fin N → Φ), AlgebraicIndependent Ω t →
    ∃ (M M' : ℕ) (a₀ a₀' : K → ℤ) (φ : Fin M → Module.Dual Ω E) (φ' : Fin M' → Module.Dual Ω E),
      IsTwistedDualGens y B a₀ φ ∧ IsTwistedDualGens y B' a₀' φ' ∧
      IsModelOver (pointIdeal O (pairProjCoord y e φ φ' t)) (d + (N - 1)) ∧
      ∃ f₀ g₀ : MRing (bundleIdx (bundleIdx ι M) M') O,
        IsVerticalDivisor (pointIdeal O (pairProjCoord y e φ φ' t)) ϖ
          (zetaFirst a₀ - zetaSecond a₀') f₀ g₀ ∧
        aeval (pairProjCoord y e φ φ' t) f₀ = aeval (pairProjCoord y e φ φ' t) g₀

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def PairNumberExpansionIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
    ∀ (n : ℕ) (z z' : Fin n → K → ℤ) (f g : Fin n → MRing ι O),
      (∀ i, IsVerticalDivisor P ϖ (z i - z' i) (f i) (g i)) →
    ∀ (m : ℕ) (A : MvPolynomial (Fin n) ℤ), A.IsHomogeneous m →
    ∀ (As Bs : Fin n → MvPolynomial (Fin n ⊕ Fin n) ℤ), IsPairExpansion m A As →
      IsPairExpansion m A Bs →
    ∀ Q : List (K → ℤ), Q.length + m = d + 1 →
      pairNum P z z' f g As Q = pairNum P z z' f g Bs Q

def hsymmTimes (N n a : ℕ) (R : MvPolynomial (Fin n) ℤ) : MvPolynomial (Fin (N + n)) ℤ :=
  rename (Fin.castAdd n) (hsymm (Fin N) ℤ a) * rename (Fin.natAdd N) R

def HsymmPairFlagIndependence.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (Ω : Type) [Field Ω] [Algebra O Ω]
      (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (y : (Σ k, ι k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d →
    ∀ (N : ℕ) (E : Type) [AddCommGroup E] [Module Ω E] (B B' : ChartBundle O (segreVec y) N E),
      SameGenericFibre ϖ B B' →
    ∀ (w w' v v' : Module.Basis (Fin N) Ω E) (x x' u u' : Fin N → K → ℤ)
      (f g f₂ g₂ : Fin N → MRing ι O),
      IsFlagPair ϖ y B B' w w' x x' f g → IsFlagPair ϖ y B B' v v' u u' f₂ g₂ →
    ∀ (n : ℕ) (z z' : Fin n → K → ℤ) (fz gz : Fin n → MRing ι O),
      (∀ j, IsVerticalDivisor (pointIdeal O y) ϖ (z j - z' j) (fz j) (gz j)) →
    ∀ (a r : ℕ) (R : MvPolynomial (Fin n) ℤ), R.IsHomogeneous r →
    ∀ (As Bs : Fin (N + n) → MvPolynomial (Fin (N + n) ⊕ Fin (N + n)) ℤ),
      IsPairExpansion (a + r) (hsymmTimes N n a R) As →
      IsPairExpansion (a + r) (hsymmTimes N n a R) Bs →
    ∀ Q : List (K → ℤ), Q.length + (a + r) = d + 1 →
      pairNum (pointIdeal O y) (Fin.append x z) (Fin.append x' z') (Fin.append f fz)
          (Fin.append g gz) As Q =
        pairNum (pointIdeal O y) (Fin.append u z) (Fin.append u' z') (Fin.append f₂ fz)
          (Fin.append g₂ gz) Bs Q

def SymmetricSpanHsymm.Statement : Prop :=
  ∀ (N m : ℕ) (G : MvPolynomial (Fin N) ℤ), G.IsHomogeneous m → G.IsSymmetric →
    G ∈ Submodule.span ℤ (Set.range fun μ : m.Partition => hsymmPart (Fin N) ℤ μ)

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace Objects

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

section Ring

variable {R : Type*} [CommRing R]

theorem weight_blockWeight_apply (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype m (fun i c => c • blockWeight ι i) (fun i => zero_smul ℕ _),
    Finset.sum_apply, Fintype.sum_sigma]
  simp [blockWeight, Pi.single_apply]

theorem isMultiHomog_iff (f : MRing ι R) (b : K → ℕ) :
    IsMultiHomog f b ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f b := by
  constructor
  · intro h m hm k
    rw [← weight_blockWeight_apply, h (mem_support_iff.mp hm)]
  · intro h m hm
    funext k
    rw [weight_blockWeight_apply, h m (mem_support_iff.mpr hm) k]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomogIdeal_iff (I : Ideal (MRing ι R)) :
    IsMultiHomogIdeal I ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal I := by
  classical
  constructor
  · intro h
    refine ⟨{x | x ∈ I ∧ ∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog x a}, fun f hf => hf.2, ?_⟩
    refine le_antisymm (fun f hf => ?_) (Ideal.span_le.mpr fun x hx => hx.1)
    rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    refine Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨h f hf b, b, ?_⟩
    exact (isMultiHomog_iff _ b).mp (weightedHomogeneousComponent_isWeightedHomogeneous b f)
  · rintro ⟨S, hS, rfl⟩ f hf b
    have hI : (Ideal.span S).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) := by
      refine Ideal.homogeneous_span _ _ fun x hx => ?_
      obtain ⟨a, ha⟩ := hS x hx
      exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ((isMultiHomog_iff x a).mpr ha)⟩
    exact weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) hI hf b

theorem isMultiProjPrime_iff (P : Ideal (MRing ι R)) :
    IsMultiProjPrime P ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P :=
  ⟨fun h => ⟨h.isPrime, (isMultiHomogIdeal_iff P).mp h.multiHomog, h.relevant⟩,
    fun h => ⟨h.1, (isMultiHomogIdeal_iff P).mpr h.2.1, h.2.2⟩⟩


end Ring

section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]



end DVR

end Objects

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem IsVerticalDivisor.uniformiser_pow_mul {K : Type*} [DecidableEq K] {ι : K → Type*}
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {H : Ideal (MRing ι O)}
    [hH : H.IsPrime] {ϖ : O} (hϖ : (C ϖ : MRing ι O) ∉ H) {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor H ϖ b f g) (n : ℕ) :
    IsVerticalDivisor H ϖ b (C ϖ ^ n * f) g := by
  obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
  refine IsVerticalDivisor.of_unit_off_special ⟨bf, bg, ?_, hg, hb⟩ ?_ hD.den_not_mem ?_
  · have h0 : IsMultiHomog (C ϖ ^ n : MRing ι O) 0 := by
      rw [← map_pow]
      exact isWeightedHomogeneous_C _ _
    have := h0.mul hf
    rwa [zero_add] at this
  · exact hH.mul_notMem (fun h => hϖ (hH.mem_of_pow_mem n h)) hD.num_not_mem
  · intro W hW hHW hrel hϖW
    obtain ⟨u, v, hu, hv, huv⟩ := hD.unit_off_special W hW hHW hrel hϖW
    refine ⟨u, C ϖ ^ n * v, hu, hW.mul_notMem (fun h => hϖW (hW.mem_of_pow_mem n h)) hv, ?_⟩
    have e : u * (C ϖ ^ n * f) - C ϖ ^ n * v * g = C ϖ ^ n * (u * f - v * g) := by ring
    rw [e]
    exact H.mul_mem_left _ huv

theorem CutByEffectiveDivisor.proof (h1 : EffectiveCase.Statement.{u})
    (h2 : UniformiserCase.Statement.{u}) (h3 : ShiftByUniformiser.Statement.{u})
    (h4 : EffectiveShift.Statement.{u}) : CutByEffectiveDivisor.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hH L
  obtain ⟨n, hEff⟩ := h4 O ϖ hϖ K ι P (d + 1) hP b f g hD
  have hH' : ∀ H, divCycle P s H ≠ 0 → (C ϖ : MRing ι O) ∉ H →
      IsVerticalDivisor H ϖ b (C ϖ ^ n * f) g := by
    intro H hsH hϖH
    have := (le_and_isRelevant_of_divCycle_ne_zero hsH).1
    exact (hH H hsH hϖH).uniformiser_pow_mul hϖH n
  have e1 := h1 O ϖ hϖ K ι P d hP b (C ϖ ^ n * f) g hEff c s hs hsP hH' L
  have e2 := h2 O ϖ hϖ K ι P d hP c s hs hsP L
  exact h3 O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH L n e1 e2

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem ConservationOfNumber.proof (h1 : IntNumAssoc.Statement.{u})
    (h2 : SpecialCycleEval.Statement.{u}) (h3 : SpecialPieceRank.Statement.{u})
    (h4 : GenericPieceRank.Statement.{u}) (h5 : SpecialIdealMultiHomog.Statement.{u})
    (h6 : SpecialDimBound.Statement.{u}) : ConservationOfNumber.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP a

  have hPprime : P.IsPrime := hP.multiProj.isPrime
  have hϖP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have hmem : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have htors : ∀ x, C ϖ * x ∈ P → x ∈ P := fun x hx =>
    (hPprime.mem_or_mem hx).resolve_left hϖP
  have hhom : IsMultiHomogIdeal P := hP.multiProj.multiHomog

  have hhilb : hilbFn (genFib P) = hilbFn (specialIdeal P) := by
    funext m
    unfold hilbFn
    split_ifs
    · rw [h4 O K ι P hhom, h3 O ϖ hϖ K ι P hhom htors]
    · rfl
  have hg : gNum P a = intNum (IsLocalRing.ResidueField O) (specialIdeal P) a := by
    unfold gNum intNum
    rw [hhilb]
  rw [hg, h1 (IsLocalRing.ResidueField O) K ι d (specialIdeal P) (h5 O K ι P hhom)
    (h6 O ϖ hϖ K ι P d hP) a]
  exact h2 O ϖ hϖ K ι P (fun V => intNum (IsLocalRing.ResidueField O) V a)

end GroundTheory.Heights₂.Heights.NumbersDVR
end
