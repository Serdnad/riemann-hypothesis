module

public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.LocalRing.Module

@[expose] public section

section

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem pow_eq_one_of_isIntegral_of_mul_complexConj_eq_one
    (E : Type) [Field E] [NumberField E] [IsCMField E] (z : E) (hz : IsIntegral ℤ z)
    (h : z * IsCMField.complexConj E z = 1) : ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
  have hn : ∀ φ : E →+* ℂ, ‖φ z‖ = 1 := by
    intro φ
    have h1 := congrArg φ h
    rw [map_mul, map_one, IsCMField.complexEmbedding_complexConj] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one, RCLike.norm_conj] at h2
    have h0 := norm_nonneg (φ z)
    nlinarith
  obtain ⟨n, hn0, hn1⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ hz hn
  exact ⟨n, hn0, hn1⟩

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem pow_eq_one_of_isIntegral_of_mul_complexConj_eq_one :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (u : E), IsIntegral ℤ u →
      u * IsCMField.complexConj E u = 1 → ∃ n : ℕ, 0 < n ∧ u ^ n = 1 := by
  intro E _ _ _ u hu h
  have hn : ∀ s : E →+* ℂ, ‖s u‖ = 1 := by
    intro s
    have h1 : s u * (starRingEnd ℂ) (s u) = 1 := by
      rw [← IsCMField.complexEmbedding_complexConj, ← map_mul, h, map_one]
    have h2 : ‖s u‖ ^ 2 = 1 := by
      have := congrArg norm h1
      rw [norm_mul, Complex.norm_conj, norm_one] at this
      rw [sq, this]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  obtain ⟨n, hn0, hn1⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ hu hn
  exact ⟨n, hn0, hn1⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

private theorem eq_of_forall_trace_mul_eq_trace_mul {E : Type} [Field E] [NumberField E] {b c : E}
    (h : ∀ a : E, Algebra.trace ℚ E (a * b) = Algebra.trace ℚ E (a * c)) : b = c := by
  apply ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).injective
  ext a
  rw [LinearMap.BilinForm.toDual_def, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply,
    Algebra.traceForm_apply, mul_comm b, mul_comm c]
  exact h a

theorem existsUnique_sesq_of_trace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (V : Type) [AddCommGroup V] [Module E V] [Module ℚ V] [IsScalarTower ℚ E V] (B : LinearMap.BilinForm ℚ V), (∀ (a : E) x y, B (a • x) y = B x (IsCMField.complexConj E a • y)) → ∃! h : V → V → E, (∀ x y (a : E), Algebra.trace ℚ E (a * h x y) = B (a • x) y) ∧ (∀ x x' y, h (x + x') y = h x y + h x' y) ∧ (∀ x y y', h x (y + y') = h x y + h x y') ∧ (∀ (a : E) x y, h (a • x) y = a * h x y) ∧ (∀ (a : E) x y, h x (a • y) = IsCMField.complexConj E a * h x y) := by
  intro E _ _ _ V _ _ _ _ B hB
  obtain ⟨h, htr⟩ : ∃ h : V → V → E,
      ∀ x y (a : E), Algebra.trace ℚ E (a * h x y) = B (a • x) y := by
    refine ⟨fun x y => ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm
      { toFun := fun a => B (a • x) y
        map_add' := fun a b => by simp only [add_smul, map_add (f := _), LinearMap.add_apply]
        map_smul' := fun q a => by
          simp only [smul_assoc, map_smul, LinearMap.smul_apply, RingHom.id_apply] }, ?_⟩
    intro x y a
    dsimp only
    rw [mul_comm, ← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
    rfl
  refine ⟨h, ⟨htr, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x x' y
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [mul_add, map_add (f := _), htr, htr, htr, smul_add, map_add (f := _), LinearMap.add_apply]
  · intro x y y'
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [mul_add, map_add (f := _), htr, htr, htr, map_add (f := _)]
  · intro b x y
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [htr, ← mul_assoc, htr, mul_smul]
  · intro b x y
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [htr, ← mul_assoc, htr, mul_comm a, mul_smul, hB (IsCMField.complexConj E b) (a • x) y,
      IsCMField.complexConj_apply_apply]
  · rintro h' ⟨htr', -⟩
    funext x y
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [htr', htr]

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem comap_fg_of_valuationRing (R : Type) [CommRing R] [IsDomain R] [ValuationRing R]
    (ι κ : Type) [Fintype ι] [Fintype κ] (φ : (ι → R) →ₗ[R] (κ → R)) (W : Submodule R (κ → R))
    (hW : W.FG) : (W.comap φ).FG := by
  obtain ⟨c, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hW
  let ψ : ((ι → R) × (Fin c → R)) →ₗ[R] (κ → R) := φ.coprod (Fintype.linearCombination R w)
  have hflat : Module.Flat R (LinearMap.range ψ) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    exact Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance
  have hfree : Module.Free R (LinearMap.range ψ) := Module.free_of_flat_of_isLocalRing
  have hfp : Module.FinitePresentation R (LinearMap.range ψ) :=
    Module.finitePresentation_of_projective _ _
  have hsurj : Function.Surjective ψ.rangeRestrict := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  have hker : (LinearMap.ker ψ.rangeRestrict).FG :=
    Module.FinitePresentation.fg_ker _ hsurj
  have heq : W.comap φ = (LinearMap.ker ψ.rangeRestrict).map (LinearMap.fst R (ι → R) (Fin c → R)) := by
    ext l
    simp only [Submodule.mem_comap, Submodule.mem_map, LinearMap.mem_ker, LinearMap.fst_apply]
    constructor
    · intro hl
      rw [← hw, ← Fintype.range_linearCombination] at hl
      obtain ⟨a, ha⟩ := hl
      refine ⟨(l, -a), ?_, rfl⟩
      apply Subtype.ext
      simp [ψ, ha]
    · rintro ⟨⟨l', a⟩, h, rfl⟩
      have h' : φ l' + Fintype.linearCombination R w a = 0 := by
        simpa [ψ] using congrArg Subtype.val h
      have hm : Fintype.linearCombination R w a ∈ W := by
        rw [← hw, ← Fintype.range_linearCombination]
        exact ⟨a, rfl⟩
      rw [eq_neg_of_add_eq_zero_left h']
      exact W.neg_mem hm
  rw [heq]
  exact hker.map _

end GlobalTheory.CompanionTheory.Ar.GR
end
