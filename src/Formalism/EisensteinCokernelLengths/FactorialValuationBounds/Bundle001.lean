module

public import Formalism.EisensteinCokernelLengths.Bundle001
public import Formalism.FrobeniusContraction.FrobeniusContractionProofs.Bundle001
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Basic.ENNReal.Real

@[expose] public section

section

noncomputable section

namespace Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria

theorem exponentChainBound : ExponentChainBound := by
  unfold ExponentChainBound
  intro ℓ b b' S E lam σ₂ h'' c' hℓ hb hS hE hσ hlam hc
  have h1 : 0 < ℓ - 1 := by linarith
  have h0 : 0 < ℓ := by linarith
  have h1' : ℓ - 1 ≠ 0 := h1.ne'
  have h0' : ℓ ≠ 0 := h0.ne'
  have key : b / (ℓ - 1) - b / ℓ = b / (ℓ * (ℓ - 1)) := by
    field_simp; ring
  have hS1 : (S + 1) / (ℓ - 1) ≤ S + 1 := div_le_self (by linarith) (by linarith)
  have hsplit : ((b + S) + 1) / (ℓ - 1) = b / (ℓ - 1) + (S + 1) / (ℓ - 1) := by ring
  have hnn : 0 ≤ b / (ℓ * (ℓ - 1)) := div_nonneg hb (mul_pos h0 h1).le
  apply max_le
  · linarith
  · linarith

lemma numC_cubic (ℓ : ℝ) (hℓ : 11 ≤ ℓ) :
    8 * (2 * ℓ - 1) * ℓ ^ 2 + 8 * ℓ ^ 2 * (ℓ - 1) + ℓ * (ℓ - 1) ^ 2 ≤ 3111 / 100 * (ℓ - 1) ^ 3 := by
  have ht : 0 ≤ ℓ - 11 := by linarith
  nlinarith [mul_nonneg ht ht, mul_nonneg (mul_nonneg ht ht) ht]

theorem rationalTailBoundCubic : NumC := by
  unfold NumC
  intro ℓ hℓ
  have h1 : 0 < ℓ - 1 := by linarith
  have h0 : 0 < ℓ := by linarith
  have h1' : ℓ - 1 ≠ 0 := h1.ne'
  have h0' : ℓ ≠ 0 := h0.ne'
  have key := numC_cubic ℓ hℓ
  have e : 8 * (2 * ℓ - 1) / (ℓ - 1) ^ 3 + 8 / (ℓ - 1) ^ 2 + 1 / (ℓ * (ℓ - 1)) =
      (8 * (2 * ℓ - 1) * ℓ ^ 2 + 8 * ℓ ^ 2 * (ℓ - 1) + ℓ * (ℓ - 1) ^ 2) / (ℓ ^ 2 * (ℓ - 1) ^ 3) := by
    field_simp
  have c : (31.11 : ℝ) = 3111 / 100 := by norm_num
  rw [e, div_le_div_iff₀ (mul_pos (pow_pos h0 2) (pow_pos h1 3)) (pow_pos h0 2), c]
  nlinarith [mul_le_mul_of_nonneg_right key (sq_nonneg ℓ)]

end Formalism.ZetaNonvanishing.ZetaNonvanishingCriteria

namespace Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds

end Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds
end
end

section

open scoped ENNReal

namespace Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds

private theorem le_addVal_of_mem_span_pow {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} {c : O}
    (hc : c ∈ Ideal.span {ϖ ^ e}) : (e : ℕ∞) ≤ IsDiscreteValuationRing.addVal O c := by
  rw [Ideal.mem_span_singleton] at hc
  have h := (IsDiscreteValuationRing.addVal_le_iff_dvd (R := O)).2 hc
  rwa [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ,
    nsmul_one] at h

private theorem addVal_eq_of_mem_span_pow_not_mem_succ {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) {e : ℕ} {c : O}
    (h1 : c ∈ Ideal.span {ϖ ^ e}) (h2 : c ∉ Ideal.span {ϖ ^ (e + 1)}) :
    IsDiscreteValuationRing.addVal O c = e := by
  refine le_antisymm ?_ (le_addVal_of_mem_span_pow hϖ h1)
  by_contra h
  rw [not_le] at h
  apply h2
  rw [Ideal.mem_span_singleton]
  apply (IsDiscreteValuationRing.addVal_le_iff_dvd (R := O)).1
  rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ,
    nsmul_one, Nat.cast_succ]
  exact Order.add_one_le_of_lt h

theorem gaussValEisenstein : GaussEisRam := by
  intro O _ _ _ ϖ hϖ e he x hx E N hN hE
  obtain ⟨hmon, hdeg, hcoef, h0⟩ := hE
  have hc0 : IsDiscreteValuationRing.addVal O (E.coeff 0) = e :=
    addVal_eq_of_mem_span_pow_not_mem_succ hϖ (hcoef 0 (by omega)) h0
  have hcN : E.coeff N = 1 := by
    have := hmon.leadingCoeff
    rwa [Polynomial.leadingCoeff, hdeg] at this
  unfold Formalism.NOK.gaussV
  simp only [Polynomial.coeff_coe]
  apply le_antisymm
  · have h1 := iInf_le (fun n : ℕ => ((IsDiscreteValuationRing.addVal O (E.coeff n) : ℕ∞) : ℝ≥0∞) +
      ENNReal.ofReal (x * n)) 0
    have h2 := iInf_le (fun n : ℕ => ((IsDiscreteValuationRing.addVal O (E.coeff n) : ℕ∞) : ℝ≥0∞) +
      ENNReal.ofReal (x * n)) N
    simp only [hc0, hcN, AddValuation.map_one, ENat.toENNReal_zero, ENat.toENNReal_coe,
      Nat.cast_zero, mul_zero, ENNReal.ofReal_zero, add_zero, zero_add] at h1 h2
    rcases le_total (e : ℝ) (x * N) with h | h
    · rw [min_eq_left h, ENNReal.ofReal_natCast]
      exact h1
    · rw [min_eq_right h]
      exact h2
  · apply le_iInf
    intro n
    rcases lt_trichotomy n N with h | h | h
    · have hv := le_addVal_of_mem_span_pow hϖ (hcoef n h)
      calc ENNReal.ofReal (min (e : ℝ) (x * N)) ≤ ENNReal.ofReal (e : ℝ) :=
            ENNReal.ofReal_le_ofReal (min_le_left _ _)
        _ = ((e : ℕ∞) : ℝ≥0∞) := by rw [ENNReal.ofReal_natCast, ENat.toENNReal_coe]
        _ ≤ ((IsDiscreteValuationRing.addVal O (E.coeff n) : ℕ∞) : ℝ≥0∞) :=
            ENat.toENNReal_le.2 hv
        _ ≤ _ := le_self_add
    · subst h
      rw [hcN, AddValuation.map_one, ENat.toENNReal_zero, zero_add]
      exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact h)]
      simp

end Formalism.ZetaNonvanishing.EisensteinGaussValuationBounds
end

section

namespace Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts.FactorialValuationBoundsFacts
open Formalism.WachCohomologyFacts

theorem key {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] (Z Z₀ I : Submodule O M)
    (hZ₀Z : Z₀ ≤ Z) :
    Module.length O (↥Z ⧸ I.comap Z.subtype) =
      Module.length O (↥Z₀ ⧸ I.comap Z₀.subtype) + Module.length O (↥Z ⧸ (Z₀ ⊔ I).comap Z.subtype) := by
  set I' := I.comap Z.subtype
  set J' := (Z₀ ⊔ I).comap Z.subtype
  set I₀ := I.comap Z₀.subtype
  have hIJ : I' ≤ J' := Submodule.comap_mono le_sup_right
  let f : ↥Z₀ →ₗ[O] ↥Z ⧸ I' := I'.mkQ ∘ₗ Submodule.inclusion hZ₀Z
  have hker : LinearMap.ker f = I₀ := by
    ext x
    simp only [f, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero, I', I₀, Submodule.mem_comap, Submodule.subtype_apply,
      Submodule.coe_inclusion]
  let f' := I₀.liftQ f hker.ge
  let g := I'.mapQ J' LinearMap.id hIJ
  have hf' : Function.Injective f' := by
    rw [← LinearMap.ker_eq_bot]; exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  have hg : Function.Surjective g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H z => exact ⟨Submodule.Quotient.mk z, rfl⟩
  have hex : Function.Exact f' g := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H z =>
      simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero, J',
        Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_sup]
      constructor
      · rintro ⟨a, ha, b, hb, hab⟩
        refine ⟨Submodule.Quotient.mk ⟨a, ha⟩, ?_⟩
        simp only [f', Submodule.liftQ_apply, f, LinearMap.coe_comp, Function.comp_apply,
          Submodule.mkQ_apply]
        rw [Submodule.Quotient.eq]
        simp only [I', Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
          Submodule.coe_inclusion]
        have : (a : M) - z = -b := by rw [← hab]; abel
        rw [this]; exact I.neg_mem hb
      · rintro ⟨w, hw⟩
        induction w using Submodule.Quotient.induction_on with
        | H a =>
          simp only [f', Submodule.liftQ_apply, f, LinearMap.coe_comp, Function.comp_apply,
            Submodule.mkQ_apply] at hw
          rw [Submodule.Quotient.eq] at hw
          simp only [I', Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
            Submodule.coe_inclusion] at hw
          refine ⟨a, a.2, (z : M) - a, ?_, by abel⟩
          have := I.neg_mem hw; simpa using this
  exact Module.length_eq_add_of_exact f' g hf' hg hex

theorem lenBound2 : Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts.LenBound2 := by
  intro O M _ _ _ ℓ g g₀ e e' Z Bc I s s₀ hs hZ hBc hs₀ hs₀Z hke hke'
  have hZ₀Z : Submodule.span O (s₀ : Set M) ≤ Z := Submodule.span_le.mpr hs₀Z
  have h1 := quotientLengthBound_holds O M ℓ g e Z Bc (Submodule.span O (s₀ : Set M) ⊔ I) s hs hZ
    (hBc.trans le_sup_right) hke
  have h2 := quotientLengthBound_holds O M ℓ g₀ e' (Submodule.span O (s₀ : Set M)) ⊥ I s₀ hs₀ (by simp)
    bot_le hke'
  rw [key Z _ I hZ₀Z]
  calc _ ≤ (g₀ : ℕ∞) * (e' : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) +
        (g : ℕ∞) * (e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)}) := add_le_add h2 h1
    _ = _ := by ring

end Formalism.ZetaNonvanishing.EisensteinCokernelLengthsFacts.FactorialValuationBoundsFacts
end
