module

public import GroundTheory.AutomorphicForms.GL2.GJFERat
public import GroundTheory.AutomorphicForms.GL2.GJLocalZeta
public import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import GroundTheory.AutomorphicForms.GL2.GJLeviZeta
public import GroundTheory.AutomorphicForms.GL2.GJParabolicFubini
public import GroundTheory.AutomorphicForms.InductionParabolic
public import GroundTheory.AutomorphicForms.GL2.GJGlobalDefs
public import GroundTheory.AutomorphicForms.GL2.GJMatrixSchwartz
public import GroundTheory.AutomorphicForms.GL2.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic MeasureTheory Measures GJMatrix Polynomial
open scoped NNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] {n : ℕ} [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]

universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) F) V}


variable (F) in
def IsGammaFactor (π : Representation ℂ (GL (Fin n) F) V) (μ : Measure (GL (Fin n) F))
    (ψ : AddChar F Circle) (γ : RatFunc ℂ) : Prop :=
  ∀ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ → ∀ v : V,
    ∀ ℓ ∈ smoothVectors (Representation.dual π),
      RatFE F γ (zetaIntegral μ Φ (matrixCoeff π v ℓ))
        (fun s => zetaIntegral μ (localMatrixFourier ψ Φ) (fun g => matrixCoeff π v ℓ g⁻¹) (1 - s))




variable (F) in
abbrev qInv : ℂ := ((LocalField.residueCard F : ℂ))⁻¹



omit [MeasurableSpace F] [BorelSpace F] in
theorem qs_one_sub (s : ℂ) : qs F (1 - s) = qInv F / qs F s := by
  have h1 : qs F (1 - s) * qs F s = qs F 1 := by rw [← qs_add, sub_add_cancel]
  have h2 : qs F 1 = qInv F := by rw [qs, Complex.cpow_neg_one]
  rw [eq_div_iff (qs_ne_zero s), h1, h2]












omit [MeasurableSpace F] [BorelSpace F] in
theorem exists_eq_C_mul_X_pow_of_mem {ε : RatFunc ℂ} (h : ε ∈ laurentSubalgebra)
    (h' : ε⁻¹ ∈ laurentSubalgebra) (hε : ε ≠ 0) :
    ∃ (r : ℂ) (i a : ℕ), r ≠ 0 ∧
      ε = algebraMap ℂ[X] (RatFunc ℂ) (C r * X ^ i) / algebraMap ℂ[X] (RatFunc ℂ) (X ^ a) := by
  obtain ⟨P₁, a, h1⟩ := mem_laurentSubalgebra_iff.1 h
  obtain ⟨P₂, b, h2⟩ := mem_laurentSubalgebra_iff.1 h'
  have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  have e1 : algebraMap ℂ[X] (RatFunc ℂ) P₁ = ε * RatFunc.X ^ a := by
    rw [h1, div_mul_cancel₀ _ (pow_ne_zero _ hX)]
  have e2 : algebraMap ℂ[X] (RatFunc ℂ) P₂ = ε⁻¹ * RatFunc.X ^ b := by
    rw [h2, div_mul_cancel₀ _ (pow_ne_zero _ hX)]
  have hprod : P₁ * P₂ = X ^ (a + b) := by
    apply IsFractionRing.injective ℂ[X] (RatFunc ℂ)
    rw [map_mul, e1, e2, map_pow, RatFunc.algebraMap_X, pow_add]
    field_simp
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow Polynomial.prime_X (a + b)).1 ⟨P₂, hprod.symm⟩
  obtain ⟨u, hu⟩ := hi
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.1 (u⁻¹).isUnit
  have hP₁ : P₁ = C r * X ^ i := by
    rw [hru, ← hu, mul_comm P₁ (u : ℂ[X]), ← mul_assoc, Units.inv_mul, one_mul]
  exact ⟨r, i, a, hr.ne_zero, by rw [h1, hP₁, map_pow, RatFunc.algebraMap_X]⟩

section Contragredient

variable [π.IsIrreducible] (hπ : IsAdmissible π) {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]
  {ψ : AddChar F Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1) {γ : RatFunc ℂ}
  (hγ : IsGammaFactor F π μ ψ γ)
include hπ hψ hψ1 hγ

end Contragredient


end GodementJacquet

end GroundTheory.Automorphic
end
end

section

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic MeasureTheory
open scoped NNReal

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]


variable (F) in
def centralUnif (m : ℕ) : GL (Fin m) F := Cartan.diagPow F m fun _ => 1

section Block

variable {m : ℕ} [MeasurableSpace (GL (Fin m) F)] {H : Type*} [Group H]
  {W : Type*} [AddCommGroup W] [Module ℂ W]

def blockA (μ : Measure (GL (Fin m) F)) (σ : Representation ℂ (GL (Fin m) F × H) W)
    (Φ : Matrix (Fin m) (Fin m) F → ℂ) (v : W) (ℓ : Module.Dual ℂ W) (s : ℂ) : ℂ :=
  ∫ g, Φ (g : Matrix (Fin m) (Fin m) F) * detPow g s * ℓ (σ (g, 1) v) ∂μ

def blockB (μ : Measure (GL (Fin m) F)) (σ : Representation ℂ (GL (Fin m) F × H) W)
    (Φ : Matrix (Fin m) (Fin m) F → ℂ) (v : W) (ℓ : Module.Dual ℂ W) (s : ℂ) : ℂ :=
  ∫ g, Φ (g : Matrix (Fin m) (Fin m) F) * detPow g (m - s) * ℓ (σ (g⁻¹, 1) v) ∂μ

end Block

section Levi

variable {n : ℕ} {α : Type*} [LinearOrder α] {W : Type*} [AddCommGroup W] [Module ℂ W]

variable (β : Fin n → α)

def leviTensor (φ : LeviIndex n β → F → ℂ) (X : Matrix (Fin n) (Fin n) F) : ℂ :=
  ∏ ij : LeviIndex n β, φ ij (X ij.1.1 ij.1.2)

def leviModulus (m : levi F n β) : ℝ≥0 :=
  ∏ a : Set.range β,
    LocalField.modulus ((leviBlock F m a : Matrix (Fiber β a) (Fiber β a) F).det) ^ blockSize β a

variable [MeasurableSpace F] [BorelSpace F]

def leviTensorHat (ψ : AddChar F Circle) (φ : LeviIndex n β → F → ℂ)
    (Y : Matrix (Fin n) (Fin n) F) : ℂ :=
  ∏ ij : LeviIndex n β, LocalField.localFourier (LocalField.selfDualMeasure ψ) ψ (φ ij) (Y ij.1.2 ij.1.1)

variable {β}

def leviIntegrandB (σ : Representation ℂ (levi F n β) W) (κ : levi F n β →* ℝ≥0)
    (Ψ : Matrix (Fin n) (Fin n) F → ℂ) (w : W) (ℓ : Module.Dual ℂ W) (s : ℂ) (m : levi F n β) : ℂ :=
  Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (((κ m)⁻¹ * leviModulus β m : ℝ≥0) : ℂ) *
    detPow (m : GL (Fin n) F) (-s) * ℓ (σ m⁻¹ w)


variable (F) in
def LeviFE (σ : Representation ℂ (levi F n β) W) (κ : levi F n β →* ℝ≥0)
    (μM : Measure (levi F n β)) (ψ : AddChar F Circle) (γ : RatFunc ℂ) : Prop :=
  ∀ φ : LeviIndex n β → F → ℂ, (∀ ij, φ ij ∈ LocalField.schwartzBruhat F) → ∀ w : W,
    ∀ ℓ ∈ smoothVectors (Representation.dual σ),
      (∃ s₁ : ℝ, ∀ s : ℂ, s₁ < s.re → Integrable (leviIntegrand σ κ (leviTensor β φ) w ℓ s) μM) ∧
      (∃ s₁ : ℝ, ∀ s : ℂ, s.re < s₁ →
        Integrable (leviIntegrandB σ κ (leviTensorHat β ψ φ) w ℓ s) μM) ∧
      RatFE F γ (fun s => ∫ m, leviIntegrand σ κ (leviTensor β φ) w ℓ s m ∂μM)
        (fun s => ∫ m, leviIntegrandB σ κ (leviTensorHat β ψ φ) w ℓ s m ∂μM)

end Levi

section Induced

variable {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] [MeasurableSpace F] [BorelSpace F]


variable (F) in
def InducedFE [MeasurableSpace (GL (Fin n) F)] (σ : Representation ℂ (levi F n β) W)
    (μG : Measure (GL (Fin n) F)) (ψ : AddChar F Circle) (γ : RatFunc ℂ) : Prop :=
  ∀ Φ : Matrix (Fin n) (Fin n) F → ℂ, IsSchwartzBruhat Φ → ∀ φ ∈ parabolicIndSpace F n β σ,
    ∀ ℓ ∈ smoothVectors (Representation.dual σ),
      (∃ s₁ : ℝ, ∀ s : ℂ, s₁ < s.re → Integrable (fun g : GL (Fin n) F =>
        Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2) * ℓ (φ g)) μG) ∧
      (∃ s₁ : ℝ, ∀ s : ℂ, s.re < s₁ → Integrable (fun g : GL (Fin n) F =>
        GJMatrix.localMatrixFourier ψ Φ (g : Matrix (Fin n) (Fin n) F) *
          detPow g (1 - s + ((n : ℂ) - 1) / 2) * ℓ (φ g⁻¹)) μG) ∧
      RatFE F γ
        (fun s => ∫ g, Φ (g : Matrix (Fin n) (Fin n) F) * detPow g (s + ((n : ℂ) - 1) / 2) *
          ℓ (φ g) ∂μG)
        (fun s => ∫ g, GJMatrix.localMatrixFourier ψ Φ (g : Matrix (Fin n) (Fin n) F) *
          detPow g (1 - s + ((n : ℂ) - 1) / 2) * ℓ (φ g⁻¹) ∂μG)

end Induced

end GodementJacquet

end GroundTheory.Automorphic
end
end

section

open NumberField
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GJGlobal

open GJMatrix

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem summable_norm_ratMat {Φ : Matrix (Fin n) (Fin n) 𝔸[K] → ℂ}
    (hΦ : Φ ∈ matrixSchwartzBruhat K n) (t : {r : ℝ // 0 < r}) (a b : AdelicGLn.AdelicGL K n) :
    Summable (fun ξ : Matrix (Fin n) (Fin n) K => ‖Φ (((Reduction.centralSection K n t * a :
      AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) * ratMat ξ *
        (b : Matrix (Fin n) (Fin n) 𝔸[K]))‖) := by
  obtain ⟨u, hu, hbd⟩ := exists_summable_bound hΦ t (isCompact_singleton (x := a))
    (isCompact_singleton (x := b))
  exact hu.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun ξ => hbd t le_rfl a rfl b rfl ξ)

end GJGlobal

end

end GroundTheory.Automorphic
end
