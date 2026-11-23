module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.RegularHypothesesAndConclusion
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Valuation.Integral
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle002
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.Bundle001

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

theorem projSum_sum_embeddings_eq_trace (K : Type) [Field K] [CharZero K] (E : Type) [Field E]
    [NumberField E] [Fintype (E →+* K)] (h : Fintype.card (E →+* K) = Module.finrank ℚ E) (y : E) :
    ∑ σ : E →+* K, σ y = ((Algebra.trace ℚ E y : ℚ) : K) := by
  classical
  let L := AlgebraicClosure K
  let f : (E →+* K) → (E →ₐ[ℚ] L) := fun σ => ((algebraMap K L).comp σ).toRatAlgHom
  have hinj : Function.Injective f := by
    intro σ τ hst
    ext x
    apply (algebraMap K L).injective
    have := DFunLike.congr_fun hst x
    simpa [f] using this
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [h, AlgHom.card]
  apply (algebraMap K L).injective
  have ht := trace_eq_sum_embeddings L (K := ℚ) (L := E) (x := y)

  rw [map_sum, map_ratCast, ← eq_ratCast (algebraMap ℚ L), ht]
  exact Fintype.sum_bijective f hbij _ _ (fun σ => by simp [f])

theorem projSum_trace_dualInt (E : Type) [Field E] [NumberField E]
    (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E (dualInt E k) = (((RingOfIntegers.basis E).repr 1 k : ℤ) : ℚ) := by
  classical
  have h1 : (1 : E) = ∑ j, (((RingOfIntegers.basis E).repr 1 j : ℤ) : ℚ) • integralBasis E j := by
    have := congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr 1)

    rw [map_sum, (algebraMap (𝓞 E) E).map_one] at this
    refine this.symm.trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integralBasis_apply, map_zsmul, Int.cast_smul_eq_zsmul]
  have h2 : Algebra.trace ℚ E (dualInt E k) = Algebra.traceForm ℚ E (dualInt E k) 1 := by
    rw [Algebra.traceForm_apply, mul_one]
  rw [h2]
  conv_lhs => rw [h1]

  rw [map_sum]
  simp only [map_smul, dualInt, LinearMap.BilinForm.apply_dualBasis_left]
  simp

theorem sum_eigProj_eq_one (K : Type) [Field K] [CharZero K] (V : Type) [AddCommGroup V]
    [Module K V] (E : Type) [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End K V)
    [Fintype (E →+* K)] (h : Fintype.card (E →+* K) = Module.finrank ℚ E) :
    ∑ σ : E →+* K, eigProj ρ σ = 1 := by
  classical
  unfold eigProj
  rw [Finset.sum_comm]
  have := congrArg ρ ((RingOfIntegers.basis E).sum_repr 1)

  rw [map_sum, ρ.map_one] at this
  refine Eq.trans ?_ this
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul, projSum_sum_embeddings_eq_trace K E h, projSum_trace_dualInt,
    Rat.cast_intCast, map_zsmul, Int.cast_smul_eq_zsmul]

end GlobalTheory.CompanionTheory.Ar.HT
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.ProjEig

open Module NumberField

section

variable {E : Type} [Field E] [NumberField E]

theorem trace_dualInt_mul (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (x : E) :
    Algebra.trace ℚ E (dualInt E k * x) = (integralBasis E).repr x k := by
  classical
  have h : ∀ l, Algebra.trace ℚ E (dualInt E k * integralBasis E l) = if l = k then 1 else 0 := by
    intro l
    have := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E)
      (traceForm_nondegenerate ℚ E) (integralBasis E) k l
    rw [Algebra.traceForm_apply] at this
    unfold dualInt
    convert this
  conv_lhs => rw [← (integralBasis E).sum_repr x]

  simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, h]
  simp

theorem mul_dualInt_eq (a : 𝓞 E) (l : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (a : E) * dualInt E l =
      ∑ k, (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E k) l : ℤ) : E) *
        dualInt E k := by
  classical
  have h := ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E)
    (integralBasis E)).sum_repr ((a : E) * dualInt E l)
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm (a : E),
    mul_assoc, trace_dualInt_mul, integralBasis_apply]
  have : (a : E) * algebraMap (𝓞 E) E (RingOfIntegers.basis E k)
      = algebraMap (𝓞 E) E (a * RingOfIntegers.basis E k) := by simp
  rw [this, integralBasis_repr_apply, Algebra.smul_def]
  simp [dualInt]

theorem sum_dualInt_mul :
    ∑ k, dualInt E k * ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
  classical
  rw [← sub_eq_zero]
  refine (traceForm_nondegenerate ℚ E).1 _ fun y => ?_

  rw [Algebra.traceForm_apply, sub_mul, map_sub, one_mul, Finset.sum_mul, map_sum,
  Algebra.trace_eq_matrix_trace (integralBasis E) y, sub_eq_zero, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, trace_dualInt_mul, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    integralBasis_apply, mul_comm y]

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem mem_eigSp_iff_apply (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (x : V) :
    x ∈ eigSp ρ σ ↔ ∀ a : 𝓞 E, ρ a x = σ (a : E) • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem rho_mul_eigProj (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (a : 𝓞 E) :
    ρ a * eigProj ρ σ = σ (a : E) • eigProj ρ σ := by
  classical
  unfold eigProj
  rw [Finset.mul_sum, Finset.smul_sum]
  have h1 : ∀ k, ρ a * (σ (dualInt E k) • ρ (RingOfIntegers.basis E k)) =
      ∑ l, (σ (dualInt E k) *
        (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E k) l : ℤ) : K)) •
          ρ (RingOfIntegers.basis E l) := by
    intro k
    rw [mul_smul_comm, ← map_mul]
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E k)]

    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, mul_smul, Int.cast_smul_eq_zsmul]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_

  rw [smul_smul, ← map_mul, mul_dualInt_eq, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul σ, map_intCast, mul_comm]

theorem eigProj_mul_rho_comm (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (a : 𝓞 E) :
    eigProj ρ σ * ρ a = ρ a * eigProj ρ σ := by
  unfold eigProj
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← map_mul, ← map_mul, mul_comm]

end

theorem eigProj_spec : ∀ (K : Type) [Field K] [CharZero K] (V : Type) [AddCommGroup V] [Module K V]
    (E : Type) [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K),
    (∀ x, eigProj ρ σ x ∈ eigSp ρ σ) ∧ (∀ x ∈ eigSp ρ σ, eigProj ρ σ x = x) ∧
    (∀ σ' : E →+* K, σ' ≠ σ → ∀ x ∈ eigSp ρ σ', eigProj ρ σ x = 0) ∧
    ∀ a : 𝓞 E, eigProj ρ σ * ρ a = ρ a * eigProj ρ σ := by
  intro K _ _ V _ _ E _ _ ρ σ
  refine ⟨fun x => ?_, fun x hx => ?_, fun σ' hσ x hx => ?_, eigProj_mul_rho_comm ρ σ⟩
  · rw [mem_eigSp_iff_apply]
    intro a
    rw [← Module.End.mul_apply, rho_mul_eigProj, LinearMap.smul_apply]
  · rw [mem_eigSp_iff_apply] at hx
    unfold eigProj
    rw [LinearMap.sum_apply]
    simp_rw [LinearMap.smul_apply, hx, smul_smul, ← map_mul]

    rw [← Finset.sum_smul, ← map_sum, sum_dualInt_mul, map_one, one_smul]
  · rw [mem_eigSp_iff_apply] at hx
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, σ' (a : E) ≠ σ (a : E) := by
      by_contra hcon
      push Not at hcon
      exact hσ (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hcon))
    have h1 : eigProj ρ σ (ρ a x) = ρ a (eigProj ρ σ x) := by
      rw [← Module.End.mul_apply, eigProj_mul_rho_comm, Module.End.mul_apply]
    rw [← Module.End.mul_apply (ρ a), rho_mul_eigProj, LinearMap.smul_apply, hx, map_smul,
      ← sub_eq_zero, ← sub_smul, smul_eq_zero] at h1
    exact h1.resolve_left (sub_ne_zero.mpr ha)

end GlobalTheory.CompanionTheory.Ar.HT.ProjEig
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

theorem diffGen_v_le_one {C : Type} [Field C] (v : Valuation C NNReal)
    {E : Type} [Field E] [NumberField E] (σ : E →+* C) (a : 𝓞 E) : v (σ (a : E)) ≤ 1 := by
  have h1 : IsIntegral ℤ (σ (a : E)) := (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
  have h2 : IsIntegral v.integer (σ (a : E)) := h1.tower_top
  exact (Valuation.integer.integers v).mem_of_integral h2

theorem diffGen_exists_max {C : Type} [Field C] (v : Valuation C NNReal)
    {E : Type} [Field E] [NumberField E] (σ : E →+* C) (D : Ideal (𝓞 E)) :
    ∃ x₀ ∈ D, ∀ x ∈ D, v (σ ((x : 𝓞 E) : E)) ≤ v (σ ((x₀ : 𝓞 E) : E)) := by
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian D : D.FG)
  rcases s.eq_empty_or_nonempty with h | h
  · refine ⟨0, D.zero_mem, fun x hx => ?_⟩
    rw [← hs, h, Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hx
    simp [hx]
  · obtain ⟨x₀, hx₀s, hmax⟩ := s.exists_max_image (fun g : 𝓞 E => v (σ (g : E))) h
    refine ⟨x₀, ?_, fun x hx => ?_⟩
    · rw [← hs]
      exact Submodule.subset_span hx₀s
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact hmax y hy
    | zero => simp
    | add y z _ _ hy hz =>
      calc v (σ ((y + z : 𝓞 E) : E)) = v (σ (y : E) + σ (z : E)) := by simp
        _ ≤ max (v (σ (y : E))) (v (σ (z : E))) := v.map_add _ _
        _ ≤ _ := max_le hy hz
    | smul r y _ hy =>
      calc v (σ ((r • y : 𝓞 E) : E)) = v (σ (r : E)) * v (σ (y : E)) := by simp [smul_eq_mul]
        _ ≤ 1 * v (σ (x₀ : E)) := mul_le_mul' (diffGen_v_le_one v σ r) hy
        _ = _ := one_mul _

theorem exists_diff_generator (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O]
    [Algebra O C] (hv : v.Integers O) [CharZero C] (E : Type) [Field E] [NumberField E]
    (σ : E →+* C) :
    (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O C).range) ∧
      ∃ d : O, algebraMap O C d ≠ 0 ∧ v (algebraMap O C d) = diffAbs v σ ∧
        Submodule.span O {algebraMap O C d} =
          Submodule.span O {y : C | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} := by
  have hint : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap O C).range := by
    intro a
    have h1 : IsIntegral ℤ (σ (a : E)) := (a.isIntegral_coe).map σ.toIntAlgHom
    have h3 : σ (a : E) ∈ v.integer := hv.mem_of_integral (h1.tower_top (A := O))
    exact RingHom.mem_range.2 (hv.exists_of_le_one ((Valuation.mem_integer_iff v _).1 h3))
  refine ⟨hint, ?_⟩
  obtain ⟨x₀, hx₀, hmax⟩ := diffGen_exists_max v σ (differentIdeal ℤ (𝓞 E))
  obtain ⟨d, hd⟩ := RingHom.mem_range.1 (hint x₀)
  have hne : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hσz : σ (z : E) ≠ 0 := (map_ne_zero σ).2 (by simpa using hz0)
  have hx0ne : σ (x₀ : E) ≠ 0 := by
    intro h
    have hle := hmax z hz
    rw [h, map_zero] at hle
    exact (v.ne_zero_iff.2 hσz) (le_antisymm hle zero_le)
  refine ⟨d, by rw [hd]; exact hx0ne, ?_, ?_⟩
  · rw [hd, diffAbs]
    apply le_antisymm
    · exact le_ciSup (f := fun x : differentIdeal ℤ (𝓞 E) => v (σ ((x : 𝓞 E) : E)))
        ⟨v (σ (x₀ : E)), by rintro _ ⟨x, rfl⟩; exact hmax x x.2⟩ ⟨x₀, hx₀⟩
    · exact ciSup_le fun x => hmax x x.2
  · rw [hd]
    apply le_antisymm
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact Submodule.subset_span ⟨x₀, hx₀, rfl⟩
    · rw [Submodule.span_le]
      rintro y ⟨x, hx, rfl⟩
      have hle : v (σ (x : E) / σ (x₀ : E)) ≤ 1 := by
        rw [map_div₀]
        exact div_le_one_of_le₀ (hmax x hx) zero_le
      obtain ⟨c, hc⟩ := hv.exists_of_le_one hle
      rw [SetLike.mem_coe, Submodule.mem_span_singleton]
      refine ⟨c, ?_⟩
      rw [Algebra.smul_def, hc, div_mul_cancel₀ _ hx0ne]

end GlobalTheory.CompanionTheory.Ar.HT
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField
open scoped nonZeroDivisors

section

variable (E : Type) [Field E] [NumberField E]

theorem mem_dual_one_iff_span_dualInt (y : E) :
    y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
      y ∈ Submodule.span ℤ (Set.range (dualInt E)) := by
  classical
  have h := Submodule.traceDual_span_of_basis ℤ (1 : Submodule (𝓞 E) E) (integralBasis E) (by
    ext x
    rw [Submodule.restrictScalars_mem, mem_span_integralBasis, Submodule.mem_one]
    rfl)
  have h2 : y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔
      y ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one]
  rw [h2, ← Submodule.restrictScalars_mem ℤ, h]
  have : (⇑(integralBasis E).traceDual) = dualInt E := by
    funext k
    unfold dualInt Module.Basis.traceDual
    congr!
  rw [this]

theorem different_mul_dual_one :
    ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) *
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
  rw [coeIdeal_differentIdeal ℤ ℚ, inv_mul_cancel₀
    (FractionalIdeal.dual_ne_zero ℤ ℚ (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E)))]

theorem exists_different_mul_dualInt (x : 𝓞 E) (hx : x ∈ differentIdeal ℤ (𝓞 E))
    (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    ∃ z : 𝓞 E, (z : E) = (x : E) * dualInt E k := by
  have h1 : dualInt E k ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) :=
    (mem_dual_one_iff_span_dualInt E _).2 (Submodule.subset_span ⟨k, rfl⟩)
  have h2 : (x : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) :=
    FractionalIdeal.mem_coeIdeal_of_mem _ hx
  have h3 := FractionalIdeal.mul_mem_mul h2 h1
  rw [different_mul_dual_one, FractionalIdeal.mem_one_iff] at h3
  exact h3

end

theorem different_generator_dualInt :
    ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (E : Type) [Field E]
      [NumberField E] (σ : E →+* K) (d : A), Function.Injective (algebraMap A K) →
      (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) →
      Submodule.span A {algebraMap A K d} =
        Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} →
      algebraMap A K d ≠ 0 ∧
        (∀ k, algebraMap A K d * σ (dualInt E k) ∈ (algebraMap A K).range) ∧
        ∃ u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A,
          ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) = 1 := by
  intro A K _ _ _ _ E _ _ σ d _ hσ hd
  have key : ∃ u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A,
      ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) = 1 := by
    set M : Submodule A K :=
      Submodule.span A (Set.range fun k => algebraMap A K d * σ (dualInt E k)) with hM
    have hy : ∀ y ∈ Submodule.span ℤ (Set.range (dualInt E)), algebraMap A K d * σ y ∈ M := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨k, rfl⟩ := hy
        exact Submodule.subset_span ⟨k, rfl⟩
      | zero => simp
      | add a b _ _ ha hb => rw [map_add (f := _), mul_add]; exact M.add_mem ha hb
      | smul n a _ ha =>
        rw [map_zsmul, mul_smul_comm]
        exact zsmul_mem ha n
    have h1 : (1 : E) ∈ ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) *
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [different_mul_dual_one]
      exact FractionalIdeal.one_mem_one _
    have h2 : σ 1 ∈ M := by
      refine FractionalIdeal.mul_induction_on (C := fun z => σ z ∈ M) h1 ?_ ?_
      · intro x hx y hy'
        obtain ⟨x, hx0, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hx
        have hx' : σ (x : E) ∈ Submodule.span A {algebraMap A K d} := by
          rw [hd]; exact Submodule.subset_span ⟨x, hx0, rfl⟩
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hx'
        change σ ((x : E) * y) ∈ M
        rw [map_mul, ← ha, smul_mul_assoc]
        exact M.smul_mem a (hy y ((mem_dual_one_iff_span_dualInt E y).1 hy'))
      · intro x y hx hy
        rw [map_add (f := _)]; exact M.add_mem hx hy
    rw [map_one, hM, Submodule.mem_span_range_iff_exists_fun] at h2
    obtain ⟨u, hu⟩ := h2
    exact ⟨u, by simpa only [Algebra.smul_def] using hu⟩
  refine ⟨?_, ?_, key⟩
  · intro h0
    obtain ⟨u, hu⟩ := key
    simp [h0] at hu
  · intro k
    have hy : ∀ y ∈ Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)},
        y * σ (dualInt E k) ∈ (algebraMap A K).range := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨x, hx, rfl⟩ := hy
        obtain ⟨z, hz⟩ := exists_different_mul_dualInt E x hx k
        rw [← map_mul, ← hz]
        exact hσ z
      | zero => simp
      | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
      | smul n a _ ha =>
        rw [smul_mul_assoc, Algebra.smul_def]
        exact mul_mem ⟨n, rfl⟩ ha
    exact hy _ (hd ▸ Submodule.mem_span_singleton_self _)

end GlobalTheory.CompanionTheory.Ar.HT
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot

namespace GlobalTheory.CompanionTheory.FreeQuotProof

theorem mem_orbit_self {S : Scheme.{0}} (G X : Over S) [GrpObj G] [ModObj G X] (x : X.left) :
    x ∈ orbit G X x := by
  have h1 : lift (1 : X ⟶ G) (𝟙 X) ≫ snd G X = 𝟙 X := lift_snd _ _
  have h2 : lift (1 : X ⟶ G) (𝟙 X) ≫ (γ[G, X] : G ⊗ X ⟶ X) = 𝟙 X := by
    have := one_smul (X ⟶ G) (𝟙 X)
    rwa [Hom.smul_def] at this
  have h1' : (lift (1 : X ⟶ G) (𝟙 X)).left ≫ (snd G X).left = 𝟙 X.left := by
    rw [← Over.comp_left, h1, Over.id_left]
  have h2' : (lift (1 : X ⟶ G) (𝟙 X)).left ≫ (γ[G, X] : G ⊗ X ⟶ X).left = 𝟙 X.left := by
    rw [← Over.comp_left, h2, Over.id_left]
  refine ⟨(lift (1 : X ⟶ G) (𝟙 X)).left x, ?_, ?_⟩
  · change (snd G X).left ((lift (1 : X ⟶ G) (𝟙 X)).left x) = x
    rw [← Scheme.Hom.comp_apply, h1']; rfl
  · rw [← Scheme.Hom.comp_apply, h2']; rfl

end GlobalTheory.CompanionTheory.FreeQuotProof
end

section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.negDef_block_of_posDef : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → B.IsHermitian → (-(C * Matrix.fromBlocks A 0 0 B * Cᴴ)).PosDef → (-B).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.Sylvester.neg_posDef_of_compl_posDef | exact GlobalTheory.CompanionTheory.Ar.Fl.Sylvester.neg_posDef_of_compl_posDef | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.Sylvester.neg_posDef_of_compl_posDef <;> assumption)
end
