module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle001
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Bundle002
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

@[expose] public section

section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.scinv :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ) (A : Matrix (Fin N) (Fin N) (𝓞 L)), A.det ≠ 0 →
    0 < nrmDet A ∧ ∃ B : Matrix (Fin N) (Fin N) (𝓞 L), A * B = ((nrmDet A : ℕ) : 𝓞 L) • (1 : Matrix (Fin N) (Fin N) (𝓞 L)) ∧
      B * A = ((nrmDet A : ℕ) : 𝓞 L) • (1 : Matrix (Fin N) (Fin N) (𝓞 L)) := by
  intro L _ _ N A hA
  refine ⟨Int.natAbs_pos.mpr (Algebra.norm_ne_zero_iff.mpr hA), ?_⟩
  have hmem : ((Ideal.absNorm (Ideal.span {A.det}) : ℕ) : 𝓞 L) ∈ Ideal.span {A.det} :=
    Ideal.absNorm_mem _
  rw [Ideal.absNorm_span_singleton, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hc' : ((nrmDet A : ℕ) : 𝓞 L) = A.det * c := hc
  refine ⟨c • A.adjugate, ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul, hc', mul_comm]
  · rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul, hc', mul_comm]
end

section

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.rankhs :
    ∀ (L : Type) [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (N : ℕ), Module.finrank ℝ (HS L N) ≤ dd L N * N := by
  intro L _ _ _ N
  refine (Submodule.finrank_le (HSsub L N)).trans (le_of_eq ?_)
  have h1 := IsTotallyComplex.finrank L
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces L
  have h3 := IsTotallyComplex.nrRealPlaces_eq_zero L
  simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, dd]
  rw [h1, h2, h3]
  ring
end

section

open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.mink3 :
    ∀ (R : Type) [Ring R] [Module.Free ℤ R] [Module.Finite ℤ R] (H : Subgroup Rˣ), Finite H →
    Nat.card H ≤ 3 ^ Module.finrank ℤ R := by
  intro R _ _ _ H hH
  let f : H → R := fun h => ((h : Rˣ) : R)
  have hinj : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (Units.ext hab)
  have hsep : ∀ a ∈ Set.range f, ∀ b ∈ Set.range f, ∀ x : R, a - b = (3 : ℕ) • x → a = b := by
    rintro _ ⟨h1, rfl⟩ _ ⟨h2, rfl⟩ x hx
    have ha : f h1 = f h2 + 3 * x := by
      rw [sub_eq_iff_eq_add'] at hx
      rw [hx, nsmul_eq_mul, Nat.cast_ofNat]
    let u : H := h2⁻¹ * h1
    have hu : f u = 1 + 3 * (f h2⁻¹ * x) := by
      have e : f u = f h2⁻¹ * f h1 := by
        simp [f, u]
      have e2 : f h2⁻¹ * f h2 = 1 := by
        simp [f]
      rw [e, ha, mul_add, e2]
      congr 1
      noncomm_ring
    have hpow : f u ^ orderOf u = 1 := by
      have : u ^ orderOf u = 1 := pow_orderOf_eq_one u
      simp only [f]
      rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, this]
      rfl
    have h1u := UpperTheory.V.KT.torsfree R (f u) _ (orderOf u) (orderOf_pos u) hu hpow
    have hu1 : u = 1 := hinj (by rw [h1u]; simp [f])
    have : h2 = h1 := inv_mul_eq_one.mp hu1
    rw [this]
  obtain ⟨_, hcard⟩ := UpperTheory.V.KT.cardsep R 3 (by norm_num) (Set.range f) hsep
  rw [Set.ncard_range_of_injective hinj] at hcard
  exact hcard
end
