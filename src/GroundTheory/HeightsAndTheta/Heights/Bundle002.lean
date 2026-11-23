module

public import GroundTheory.HeightsAndTheta.Heights.HermitianLattice
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ConsCompSuccAboveZero

@[expose] public section

section

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt

noncomputable section

variable {K : Type*} [Field K]

section RealToFibre

variable (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E]

variable {σ E}

end RealToFibre

variable [NumberField K]

section General

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]

variable (h : HermitianMetric K E)

def RealSpace (_h : HermitianMetric K E) : Type _ := ℝ ⊗[ℤ] E

namespace RealSpace

instance : AddCommGroup (RealSpace h) := inferInstanceAs (AddCommGroup (ℝ ⊗[ℤ] E))

def ofModule : E →+ RealSpace h := (TensorProduct.mk ℤ ℝ E 1).toAddMonoidHom

def lattice : Submodule ℤ (RealSpace h) := LinearMap.range (ofModule h).toIntLinearMap

end RealSpace

end General

end

end GroundTheory.Heights₂.Heights
end

section

namespace GroundTheory.Heights₂.Heights

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt

noncomputable section

variable {K : Type*} [Field K]

section SMul

variable (σ : K →+* ℂ) (E : Type*) [AddCommGroup E] [Module (𝓞 K) E]

theorem fibre_smul_eq (a : ComplexAt σ) (x : Fibre σ E) :
    a • x = (ofComplex σ).symm a • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [smul_zero]
  | tmul z e => rw [smul_tmul', smul_tmul', complex_smul_def, smul_eq_mul]; rfl
  | add x y hx hy => rw [smul_add, smul_add, hx, hy]

end SMul

variable [NumberField K]

variable {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
  [Module.Projective (𝓞 K) E]

def FibreSpace (_h : HermitianMetric K E) (σ : K →+* ℂ) : Type _ := Fibre σ E

namespace FibreSpace

variable (h : HermitianMetric K E) (σ : K →+* ℂ)

instance : AddCommGroup (FibreSpace h σ) := inferInstanceAs (AddCommGroup (Fibre σ E))

instance : Module ℂ (FibreSpace h σ) := inferInstanceAs (Module ℂ (Fibre σ E))

instance : NormedAddCommGroup (FibreSpace h σ) :=
  letI : InnerProductSpace.Core ℂ (FibreSpace h σ) := h.form σ
  this.toNormedAddCommGroup

instance : InnerProductSpace ℂ (FibreSpace h σ) := InnerProductSpace.ofCore _

def equiv : Fibre σ E ≃ₗ[ℂ] FibreSpace h σ := LinearEquiv.refl ℂ _

theorem inner_equiv (x y : Fibre σ E) :
    inner ℂ (equiv h σ x) (equiv h σ y) = (h.form σ).inner x y := rfl

end FibreSpace

variable {F : Type*} [AddCommGroup F] [Module (𝓞 K) F] [Module.Finite (𝓞 K) F]
  [Module.Projective (𝓞 K) F]

variable (hE : HermitianMetric K E) (hF : HermitianMetric K F)

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

noncomputable section

abbrev CP (N : ℕ) := ℙ ℂ (Fin (N + 1) → ℂ)

variable {N : ℕ}

namespace CP

def conjVec : (Fin (N + 1) → ℂ) →ₛₗ[starRingEnd ℂ] (Fin (N + 1) → ℂ) where
  toFun w k := starRingEnd ℂ (w k)
  map_add' w w' := by ext k; simp
  map_smul' c w := by ext k; simp

lemma conjVec_injective : Function.Injective (conjVec (N := N)) := by
  intro w w' h
  ext k
  exact (starRingEnd ℂ).injective (congrFun h k)

def conj : CP N → CP N := Projectivization.map (conjVec (N := N)) conjVec_injective

end CP

variable {A : Type*} [CommRing A]

abbrev evalAt (ρ : A →+* ℂ) (w : Fin (N + 1) → ℂ) (f : MvPolynomial (Fin (N + 1)) A) : ℂ :=
  eval₂ ρ w f

lemma evalAt_smul (ρ : A →+* ℂ) {f : MvPolynomial (Fin (N + 1)) A} {d : ℕ}
    (hf : f.IsHomogeneous d) (c : ℂ) (w : Fin (N + 1) → ℂ) :
    evalAt ρ (c • w) f = c ^ d * evalAt ρ w f := by
  rw [evalAt, evalAt, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ k, m k = d := by
    have := hf (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, hd]
  ring

attribute [local instance] MvPolynomial.gradedAlgebra

end

end GroundTheory.Heights₂.Heights
end
