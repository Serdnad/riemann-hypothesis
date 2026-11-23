module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.LinearAlgebra.UnitaryGroup
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
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.FieldTheory.PrimitiveElement

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric

noncomputable section

def ParametricCircleIntegralAnalytic.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] (Φ : (ι → ℂ) × ℂ → ℂ) (O : Set ((ι → ℂ) × ℂ)) (U : Set (ι → ℂ)) (c : ℂ) (r : ℝ),
    0 ≤ r → IsOpen O → IsOpen U → DifferentiableOn ℂ Φ O →
    (∀ x ∈ U, ∀ s ∈ sphere c r, (x, s) ∈ O) →
    AnalyticOnNhd ℂ (fun x => ∮ s in C(c, r), Φ (x, s)) U

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

noncomputable section

def FiniteCoverPuncturedPolydisc.Statement : Prop :=
  ∀ (e N : ℕ) (c : Fin (e + 1) → ℂ) (r : ℝ) (Y : Type) [TopologicalSpace Y]
    (p : Y → ↥(Metric.ball c r ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0})),
    0 < r → c 0 = 0 → IsCoveringMap p → (∀ z, (p ⁻¹' {z}).encard = N) →
    ∃ (m : ℕ) (ord : Fin m → ℕ) (δ : ℝ)
      (ψ : Fin m → ↥(Metric.ball c δ ∩ {t : Fin (e + 1) → ℂ | t 0 ≠ 0}) → Y),
      0 < δ ∧ δ ≤ 1 ∧ ∑ b, ord b = N ∧ (∀ b, 1 ≤ ord b) ∧ (∀ b, Continuous (ψ b)) ∧
      (∀ b t, ((p (ψ b t) : Fin (e + 1) → ℂ)) =
        Function.update (t : Fin (e + 1) → ℂ) 0 ((t : Fin (e + 1) → ℂ) 0 ^ ord b)) ∧
      (∀ b, Function.Injective (ψ b)) ∧
      (∀ b b', b ≠ b' → ∀ t t', ψ b t ≠ ψ b' t') ∧
      (∀ y, dist ((p y : Fin (e + 1) → ℂ)) c < δ ^ N → ∃ b t, ψ b t = y)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric
open scoped ENNReal

def HolomorphicZeroSetDimH.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (h : (Fin k → ℂ) → ℂ),
    IsOpen U → DifferentiableOn ℂ h U →
    (∀ W ⊆ U, IsOpen W → W.Nonempty → ∃ w ∈ W, h w ≠ 0) →
      dimH {v | v ∈ U ∧ h v = 0} ≤ 2 * ((k - 1 : ℕ) : ℝ≥0∞)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ENNReal NNReal

noncomputable section

def AreaGraphPartition.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (EuclideanSpace ℝ (Fin k)))
    (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)),
    IsOpen U → ContDiffOn ℝ 1 F U →
      ∀ r : (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) → ℝ≥0, (∀ A, r A ≠ 0) →
        ∃ (t : ℕ → Set (EuclideanSpace ℝ (Fin k)))
          (A : ℕ → EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)),
          Pairwise (Function.onFun Disjoint t) ∧ (∀ n, MeasurableSet (t n)) ∧ (∀ n, t n ⊆ U) ∧
            U ⊆ ⋃ n, t n ∧ (∀ n, ApproximatesLinearOn F (A n) (t n) (r (A n))) ∧
              ∀ n, ∀ x ∈ t n, ‖fderiv ℝ F x - A n‖₊ ≤ r (A n)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

open scoped ContDiff

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def ChangeOfVariablesDegree.Statement : Prop :=
  ∀ (n : ℕ) (φ : (Fin n → ℝ) → Fin n → ℝ), ContDiff ℝ ∞ φ →
    HasCompactSupport (fun x => φ x - x) →
      ∀ f : (Fin n → ℝ) → ℝ, ContDiff ℝ ∞ f → HasCompactSupport f →
        ∫ x, f (φ x) * (fderiv ℝ φ x).det = ∫ x, f x

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module

open scoped ENNReal

noncomputable section

def areaJacobian {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] (L : E →ₗ[ℝ] F) : ℝ :=
  √(LinearMap.det (LinearMap.adjoint L ∘ₗ L))

def AreaMultiplicity.Statement : Prop :=
  ∀ (E F : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] (k : ℕ),
    finrank ℝ E = k → finrank ℝ F = k →
    ∀ (A : Set E) (f : E → F) (f' : E → E →L[ℝ] F), MeasurableSet A →
      (∀ x ∈ A, HasFDerivWithinAt f (f' x) A x) →
      ∫⁻ x in A, ENNReal.ofReal (areaJacobian (f' x : E →ₗ[ℝ] F)) ∂(μH[(k : ℝ)]) =
        ∫⁻ y, (({x ∈ A | f x = y}.encard : ℕ∞) : ℝ≥0∞) ∂(μH[(k : ℝ)])

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

def WeightedAreaFormula.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (A : Set E) (f : E → E) (H : E → ℝ),
    IsOpen A → DifferentiableOn ℝ f A → (∀ y, {x | x ∈ A ∧ f x = y}.Finite) →
    IntegrableOn (fun x => |(fderiv ℝ f x).det| * H x) A μ →
      Integrable (fun y => ∑ᶠ x ∈ {x | x ∈ A ∧ f x = y}, H x) μ ∧
        ∫ y, (∑ᶠ x ∈ {x | x ∈ A ∧ f x = y}, H x) ∂μ = ∫ x in A, |(fderiv ℝ f x).det| * H x ∂μ

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ENNReal NNReal

noncomputable section

def graphJac {k m : ℕ} (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) : ℝ :=
  √(LinearMap.det ((1 : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) +
    LinearMap.adjoint B ∘ₗ B))

def GraphJacContinuous.Statement : Prop :=
  ∀ (k m : ℕ) (A : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) (ε : ℝ), 0 < ε →
    ∃ r : ℝ, 0 < r ∧ ∀ B : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m), ‖B - A‖ ≤ r →
      graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≤
          (1 + ε) * graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ∧
        graphJac (A : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m)) ≤
          (1 + ε) * graphJac (B : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Matrix

noncomputable section

def GeneralProjection.Statement : Prop :=
  ∀ (n d m : ℕ) (L : Fin m → (Fin d → ℂ) →ₗ[ℂ] (Fin n → ℂ)), (∀ b, Function.Injective (L b)) →
    ∃ π : Matrix (Fin d) (Fin n) ℂ, ∀ b, Function.Injective fun v => π *ᵥ L b v

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open Polynomial TensorProduct

noncomputable section

namespace PrimitiveLinearForm

variable (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]

abbrev tensorRightAlgebra : Algebra B (FractionRing R ⊗[R] B) := Algebra.TensorProduct.rightAlgebra

attribute [local instance] tensorRightAlgebra

theorem isLocalization_tensor :
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) (FractionRing R ⊗[R] B) := by
  refine isLocalizedModule_iff_isLocalization.mp ?_
  have h := (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) (FractionRing R)
    (IsScalarTower.toAlgHom R B (FractionRing R ⊗[R] B)).toLinearMap).mpr ?_
  · exact h
  · exact TensorProduct.isBaseChange R B (FractionRing R)

theorem exists_linear_primitive {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] {n : ℕ} (ι : ℂ →+* K) (x : Fin n → L)
    (hx : ∀ φ ψ : L →ₐ[K] AlgebraicClosure K, (∀ j, φ (x j) = ψ (x j)) → φ = ψ) :
    ∃ c : Fin n → ℂ, IntermediateField.adjoin K {∑ j, algebraMap K L (ι (c j)) * x j} = ⊤ := by
  classical
  let A := AlgebraicClosure K
  let ι' : ℂ →+* A := (algebraMap K A).comp ι
  let p : (L →ₐ[K] A) × (L →ₐ[K] A) → Polynomial A := fun φψ =>
    ∑ j : Fin n, Polynomial.monomial (j : ℕ) (φψ.1 (x j) - φψ.2 (x j))
  have hp : ∀ φψ : (L →ₐ[K] A) × (L →ₐ[K] A), φψ.1 ≠ φψ.2 → p φψ ≠ 0 := by
    intro φψ hne h
    apply hne
    apply hx
    intro j
    have hc := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q (j : ℕ)) h
    simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Polynomial.coeff_zero] at hc
    rw [Finset.sum_eq_single j] at hc
    · simpa [sub_eq_zero] using hc
    · intro b _ hb
      simp [Finsupp.single_apply, show (b : ℕ) ≠ (j : ℕ) from fun h => hb (Fin.ext h)]
    · simp
  have hev : ∀ φψ : (L →ₐ[K] A) × (L →ₐ[K] A), ∀ t : A,
      (p φψ).eval t = ∑ j : Fin n, (φψ.1 (x j) - φψ.2 (x j)) * t ^ (j : ℕ) := by
    intro φψ t
    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  let S : Finset A := (Finset.univ.filter (fun φψ : (L →ₐ[K] A) × (L →ₐ[K] A) => φψ.1 ≠ φψ.2)).biUnion
    (fun φψ => (p φψ).roots.toFinset)
  have hSf : {t : ℂ | ι' t ∈ S}.Finite :=
    (S.finite_toSet.preimage (ι'.injective.injOn))
  obtain ⟨t, ht⟩ := hSf.infinite_compl.nonempty
  refine ⟨fun j => t ^ (j : ℕ), ?_⟩
  have hA : ∀ y : L, ((minpoly K y).map (algebraMap K A)).Splits := fun y => IsAlgClosed.splits _
  rw [Field.primitive_element_iff_algHom_eq_of_eval' K A hA]
  intro φ ψ hφψ
  by_contra hne
  apply ht
  simp only [Set.mem_ofPred_eq, S, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨(φ, ψ), hne, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hp (φ, ψ) hne), Polynomial.IsRoot, hev]
  have h1 : ∀ χ : L →ₐ[K] A, χ (∑ j : Fin n, algebraMap K L (ι (t ^ (j : ℕ))) * x j) =
      ∑ j : Fin n, ι' t ^ (j : ℕ) * χ (x j) := by
    intro χ

    simp [map_sum, map_mul, AlgHom.commutes, ι', map_pow]
  have h2 := congrArg id hφψ
  simp only [id] at h2
  rw [h1, h1] at h2
  rw [← sub_eq_zero] at h2
  rw [← h2, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem exists_primitive_data {R B : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing B] [IsDomain B] [Algebra R B] [Module.Finite R B]
    (hinj : Function.Injective (algebraMap R B)) (ι : ℂ →+* R) {n : ℕ} (x : Fin n → B)
    (hx : Algebra.adjoin R (Set.range x) = ⊤) :
    ∃ (c : Fin n → ℂ) (m : R[X]) (D : R) (Q : Fin n → R[X]),
      m.Monic ∧ m.natDegree = Module.finrank (FractionRing R) (FractionRing R ⊗[R] B) ∧
      (∀ p : R[X], aeval (∑ j, algebraMap R B (ι (c j)) * x j) p = 0 ↔ m ∣ p) ∧
      D ≠ 0 ∧ (∃ a b : R[X], a * m + b * derivative m = C D) ∧
      ∀ j, algebraMap R B D * x j = aeval (∑ j, algebraMap R B (ι (c j)) * x j) (Q j) := by
  classical
  let K := FractionRing R
  let L := K ⊗[R] B
  let _ : Algebra B L := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) L :=
    isLocalization_tensor R B
  have hM : Algebra.algebraMapSubmonoid B (nonZeroDivisors R) ≤ nonZeroDivisors B := by
    rintro _ ⟨r, hr, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      (fun h => nonZeroDivisors.ne_zero hr (hinj (by rw [h, map_zero])))
  have : IsDomain L := IsLocalization.isDomain_of_le_nonZeroDivisors L hM
  have hBL : Function.Injective (algebraMap B L) := IsLocalization.injective L hM
  have : Algebra.IsIntegral K L := Algebra.IsIntegral.of_finite K L
  let _ : Field L := (isField_of_isIntegral_of_isField' (R := K) (Field.toIsField K)).toField
  let ιK : ℂ →+* K := (algebraMap R K).comp ι
  have : CharZero K := ⟨fun a b h => by
    have h' : ιK (a : ℂ) = ιK (b : ℂ) := by simpa [map_natCast] using h
    exact_mod_cast ιK.injective h'⟩
  have : Algebra.IsSeparable K L := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hxgen : ∀ φ ψ : L →ₐ[K] AlgebraicClosure K,
      (∀ j, φ (algebraMap B L (x j)) = ψ (algebraMap B L (x j))) → φ = ψ := by
    intro φ ψ h
    have h1 : (φ.restrictScalars R).comp (IsScalarTower.toAlgHom R B L) =
        (ψ.restrictScalars R).comp (IsScalarTower.toAlgHom R B L) := by
      apply AlgHom.ext_of_adjoin_eq_top hx
      rintro _ ⟨j, rfl⟩
      exact h j
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid B (nonZeroDivisors R))
    exact RingHom.ext fun b => AlgHom.congr_fun h1 b
  obtain ⟨c, hc⟩ := exists_linear_primitive ιK (fun j => algebraMap B L (x j)) hxgen
  refine ⟨c, ?_⟩
  set ℓ : B := ∑ j, algebraMap R B (ι (c j)) * x j with hℓ
  have hℓL : algebraMap B L ℓ = ∑ j, algebraMap K L (ιK (c j)) * algebraMap B L (x j) := by

    rw [hℓ, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ← IsScalarTower.algebraMap_apply R B L, IsScalarTower.algebraMap_apply R K L]
    rfl
  rw [← hℓL] at hc
  have : Algebra.IsIntegral R B := Algebra.IsIntegral.of_finite R B
  have hint : IsIntegral R ℓ := Algebra.IsIntegral.isIntegral ℓ
  have hmK : minpoly K (algebraMap B L ℓ) = (minpoly R ℓ).map (algebraMap R K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions K L hint
  have hdeg : (minpoly R ℓ).natDegree = Module.finrank K L := by
    rw [← (minpoly.monic hint).natDegree_map (algebraMap R K), ← hmK]
    exact (Field.primitive_element_iff_minpoly_natDegree_eq K _).mp hc
  have : Module.IsTorsionFree R B := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have hdiv : ∀ p : R[X], aeval ℓ p = 0 ↔ minpoly R ℓ ∣ p := fun p =>
    ⟨minpoly.isIntegrallyClosed_dvd hint, fun ⟨q, hq⟩ => by rw [hq, map_mul, minpoly.aeval, zero_mul]⟩

  have hirr : Irreducible ((minpoly R ℓ).map (algebraMap R K)) :=
    hmK ▸ minpoly.irreducible (IsIntegral.of_finite K _)
  have hsep : IsCoprime ((minpoly R ℓ).map (algebraMap R K))
      (derivative ((minpoly R ℓ).map (algebraMap R K))) := hirr.separable
  obtain ⟨a, b, hab⟩ := hsep
  rw [Polynomial.derivative_map] at hab
  obtain ⟨α, hα, hαa⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) a
  obtain ⟨β, hβ, hβb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) b
  have hinjK : Function.Injective (Polynomial.map (algebraMap R K)) :=
    Polynomial.map_injective _ (IsFractionRing.injective R K)
  have hid : C β * IsLocalization.integerNormalization (nonZeroDivisors R) a * minpoly R ℓ +
      C α * IsLocalization.integerNormalization (nonZeroDivisors R) b * derivative (minpoly R ℓ) =
      C (α * β) := by
    apply hinjK
    simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_C, hαa, hβb,
      Algebra.smul_def, Polynomial.algebraMap_apply, map_mul]
    linear_combination (C (algebraMap R K α) * C (algebraMap R K β)) * hab

  have hmem : ∀ j, ∃ P : K[X], aeval (algebraMap B L ℓ) P = algebraMap B L (x j) := by
    intro j
    have h1 : algebraMap B L (x j) ∈ (IntermediateField.adjoin K {algebraMap B L ℓ}).toSubalgebra := by
      rw [hc]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic _), Algebra.adjoin_singleton_eq_range_aeval] at h1
    obtain ⟨P, hP⟩ := h1
    exact ⟨P, hP⟩
  choose P hP using hmem
  have hclear : ∀ j, ∃ e ∈ nonZeroDivisors R, ∃ P' : R[X], aeval ℓ P' = algebraMap R B e * x j := by
    intro j
    obtain ⟨e, he, hPe⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors R) (P j)
    refine ⟨e, he, IsLocalization.integerNormalization (nonZeroDivisors R) (P j), hBL ?_⟩
    rw [← Polynomial.aeval_algebraMap_apply, ← Polynomial.aeval_map_algebraMap K, hPe,
      Algebra.smul_def, Polynomial.algebraMap_apply, map_mul, Polynomial.aeval_C, hP j, map_mul,
      ← IsScalarTower.algebraMap_apply R B L, IsScalarTower.algebraMap_apply R K L]
  choose e he Q' hQ' using hclear
  refine ⟨minpoly R ℓ, α * β * ∏ j, e j,
    fun j => C (α * β * ∏ k ∈ Finset.univ.erase j, e k) * Q' j, minpoly.monic hint, hdeg, hdiv,
    ?_, ?_, ?_⟩
  · refine mul_ne_zero (mul_ne_zero (nonZeroDivisors.ne_zero hα) (nonZeroDivisors.ne_zero hβ)) ?_
    exact Finset.prod_ne_zero_iff.mpr fun j _ => nonZeroDivisors.ne_zero (he j)
  · refine ⟨C (∏ j, e j) * (C β * IsLocalization.integerNormalization (nonZeroDivisors R) a),
      C (∏ j, e j) * (C α * IsLocalization.integerNormalization (nonZeroDivisors R) b), ?_⟩
    rw [C_mul (a := α * β)]
    linear_combination C (∏ j, e j) * hid
  · intro j
    rw [map_mul (aeval ℓ), Polynomial.aeval_C, hQ' j, ← Finset.mul_prod_erase Finset.univ e
      (Finset.mem_univ j)]
    simp only [map_mul]
    ring

end PrimitiveLinearForm

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def UnitaryZariskiDense.Statement : Prop :=
  ∀ (n : ℕ) (p : MvPolynomial (Fin n × Fin n) ℂ), p ≠ 0 →
    ∃ U ∈ Matrix.unitaryGroup (Fin n) ℂ, eval (fun ij : Fin n × Fin n => U ij.1 ij.2) p ≠ 0

end

end GroundTheory.Heights₂.Heights.ComplexSets
end
