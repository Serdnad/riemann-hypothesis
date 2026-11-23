module

public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Lean.Meta.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle003
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Defs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import GroundTheory.HeightsAndTheta.Heights.HermitianLattice
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

noncomputable section

namespace ChartLatSection

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ} {Ω : Type} [Field Ω]



end ChartLatSection


end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial NumberField

noncomputable section

variable {K : Type} [Field K] [NumberField K]

theorem exists_int_smul_mem_latticeDual {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) (hL : L.FG)
    (v : Fin m → K) : ∃ D : ℤ, D ≠ 0 ∧ D • v ∈ latticeDual L := by
  classical
  obtain ⟨S, hS⟩ := hL
  have hint : ∀ k : ℤ, IsIntegral ℤ (k : K) := fun k ↦ by
    simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ K k))
  have h1 : ∀ s : Fin m → K, ∃ D : ℤ, D ≠ 0 ∧ IsIntegral ℤ ((D : K) * (v ⬝ᵥ s)) := by
    intro s
    have halg : IsAlgebraic ℤ (v ⬝ᵥ s) :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic _)
    obtain ⟨D, hD, hD'⟩ := halg.exists_integral_multiple
    exact ⟨D, hD, by rwa [zsmul_eq_mul] at hD'⟩
  choose D hD0 hDint using h1
  refine ⟨∏ s ∈ S, D s, Finset.prod_ne_zero_iff.mpr fun s _ ↦ hD0 s, ?_⟩
  intro u hu
  rw [← hS] at hu
  rw [Set.mem_range, ← IsIntegralClosure.isIntegral_iff (R := ℤ) (A := 𝓞 K)]
  induction hu using Submodule.span_induction with
  | mem x hx =>
    rw [smul_dotProduct, zsmul_eq_mul, ← Finset.mul_prod_erase S D hx, Int.cast_mul,
      mul_comm (D x : K), mul_assoc]
    exact (hint _).mul (hDint x)
  | zero => simpa using (isIntegral_zero : IsIntegral ℤ (0 : K))
  | add x y _ _ hx hy => rw [dotProduct_add]; exact hx.add hy
  | smul c x _ hx =>
    rw [dotProduct_smul, Algebra.smul_def]
    exact ((IsIntegralClosure.isIntegral_iff (R := ℤ) (A := 𝓞 K)).mpr ⟨c, rfl⟩).mul hx

variable {r N : ℕ}

theorem exists_int_comb {F : HermLattice K (r + 1)} {φ : Fin (N + 1) → Fin (r + 1) → K}
    (hφ : IsDualBasis F.lattice φ) (v : Fin (r + 1) → K) :
    ∃ D : ℤ, D ≠ 0 ∧ ∃ c : Fin (N + 1) → ℤ, ∑ b, c b • φ b = D • v := by
  obtain ⟨D, hD, hmem⟩ := exists_int_smul_mem_latticeDual F.lattice F.fg v
  have h : D • v ∈ Submodule.span ℤ (Set.range φ) := by rw [hφ.span_eq]; exact hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h
  exact ⟨D, hD, c, hc⟩







end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

def latticeValue {K K' : Type*} [Field K] [Field K'] [Algebra K K'] {m N : ℕ}
    (φ : Fin (N + 1) → Fin m → K) (v : Fin m → K') (b : Fin (N + 1)) : K' :=
  ∑ j, algebraMap K K' (φ b j) * v j

def latticeExtend {K : Type*} [Field K] [NumberField K] (K' : Type*) [Field K'] [NumberField K']
    [Algebra K K'] {m : ℕ} (L : Submodule (𝓞 K) (Fin m → K)) : Submodule (𝓞 K') (Fin m → K') :=
  Submodule.span (𝓞 K') ((fun w : Fin m → K ↦ fun j ↦ algebraMap K K' (w j)) '' L)

def multiplierIdeal {L : Type*} [Field L] [NumberField L] {ι : Type*} (y : ι → L) :
    Submodule (𝓞 L) L where
  carrier := {a | ∀ i, a * y i ∈ Set.range (algebraMap (𝓞 L) L)}
  add_mem' := by
    intro a a' ha ha' i
    obtain ⟨c, hc⟩ := ha i
    obtain ⟨c', hc'⟩ := ha' i
    exact ⟨c + c', by rw [map_add (f := _), hc, hc', add_mul]⟩
  zero_mem' := fun _ ↦ ⟨0, by rw [map_zero, zero_mul]⟩
  smul_mem' := by
    intro c a ha i
    obtain ⟨d, hd⟩ := ha i
    exact ⟨c * d, by rw [map_mul, hd, Algebra.smul_def, mul_assoc]⟩

def LineIdealDual.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (r N : ℕ) (F : HermLattice K (r + 1))
    (φ : Fin (N + 1) → Fin (r + 1) → K), IsDualBasis F.lattice φ →
    ∀ (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] (v : Fin (r + 1) → K') (a : K'),
      a • v ∈ latticeExtend K' F.lattice ↔
        ∀ b, a * latticeValue φ v b ∈ Set.range (algebraMap (𝓞 K') K')

def IdealIndexPlaces.Statement : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (ι : Type) [Fintype ι] (y : ι → L), y ≠ 0 →
    genIndex (multiplierIdeal y).toAddSubgroup (1 : Submodule (𝓞 L) L).toAddSubgroup *
      ∏ᶠ w : FinitePlace L, ⨆ i, w (y i) = 1

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder nonZeroDivisors

noncomputable section

theorem LineDegreeBundle.sum_log_norm {L : Type*} [Field L] [NumberField L] {x : L} (hx : x ≠ 0) :
    ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = Real.log |(Algebra.norm ℚ x : ℝ)| := by
  classical
  rw [← Real.log_prod (fun σ _ ↦ norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hx))]
  congr 1
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ (fun φ ↦ ‖φ x‖)
    (fun _ ↦ by simp [RingHom.equivRatAlgHom_apply]), ← norm_prod,
    ← Algebra.norm_eq_prod_embeddings ℚ ℂ x, eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real,
    Real.norm_eq_abs]

theorem LineDegreeBundle.quad_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (u : Fin n → ℂ) :
    star (z • u) ⬝ᵥ (H *ᵥ (z • u)) = (star z * z) * (star u ⬝ᵥ (H *ᵥ u)) := by
  simp only [Matrix.mulVec_smul, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem LineDegreeBundle.quad_pos {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) {u : Fin n → ℂ}
    (hu : u ≠ 0) :
    ‖star u ⬝ᵥ (H *ᵥ u)‖ = (star u ⬝ᵥ (H *ᵥ u)).re ∧ 0 < (star u ⬝ᵥ (H *ᵥ u)).re := by
  have h := hH.dotProduct_mulVec_pos hu
  obtain ⟨hre, him⟩ := Complex.lt_def.mp h
  have hQ : star u ⬝ᵥ (H *ᵥ u) = ((star u ⬝ᵥ (H *ᵥ u)).re : ℂ) :=
    Complex.ext rfl (by simp only [Complex.ofReal_im]; rw [← him]; rfl)
  refine ⟨?_, by simpa using hre⟩
  conv_lhs => rw [hQ]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by simpa using hre)]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
end
