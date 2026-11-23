module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle050
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle058
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle056
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle076
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle059
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Basic
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Order.Basic

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.modular_form_symmetric_function_decomp : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (act : ι → SL(2, ℤ) → ι) (m k N : ℕ) (t F : ι → ℍ → ℂ), 0 < N → ActBij act → IsFam act m t → IsFam act k F → (∀ i, ∃ a, HasQ N (t i) a) → (∀ i, ∃ a, HasQ N (F i) a) → ∃ c : ℕ → ℍ → ℂ, (∀ j, (∀ γ : SL(2, ℤ), c j ∣[((k + m * j : ℕ) : ℤ)] γ = c j) ∧ ∃ a, HasQ N (c j) a) ∧ ∀ i τ, F i τ * ∏ l ∈ Finset.univ.erase i, (t i τ - t l τ) = ∑ j ∈ Finset.range (Fintype.card ι), c j τ * t i τ ^ (Fintype.card ι - 1 - j) := by
  first | exact @GlobalTheory.QFam.LagrangeFam.lagrange_fam | exact GlobalTheory.QFam.LagrangeFam.lagrange_fam | (intros; apply GlobalTheory.QFam.LagrangeFam.lagrange_fam <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.permutedModularFamily_monic_poly_coeff_invariant : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (k N : ℕ) (F : ι → ℍ → ℂ) (R : Subring ℂ), 0 < N → ActBij act → IsFam act k F → (∀ i, QAll (· ∈ R) N (F i)) → ∃ s : Fin (Fintype.card ι) → ℍ → ℂ, (∀ j : Fin (Fintype.card ι), (∀ γ : SL(2, ℤ), s j ∣[((k * (Fintype.card ι - j) : ℕ) : ℤ)] γ = s j) ∧ QAll (· ∈ R) N (s j)) ∧ ∀ i τ, F i τ ^ Fintype.card ι + ∑ j, s j τ * F i τ ^ (j : ℕ) = 0 := by
  first | exact @GlobalTheory.QFam.minpoly_coeff_invariant | exact GlobalTheory.QFam.minpoly_coeff_invariant | (intros; apply GlobalTheory.QFam.minpoly_coeff_invariant <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.hasQExpansion_of_periodic_bounded_holomorphic : ∀ (N : ℕ) (f : ℍ → ℂ), 0 < N → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → (∀ τ : ℍ, f ((N : ℝ) +ᵥ τ) = f τ) → UpperHalfPlane.IsBoundedAtImInfty f → ∃ a, HasQ N f a := by
  first | exact @GlobalTheory.FN.hasQ_of_periodic_bounded | exact GlobalTheory.FN.hasQ_of_periodic_bounded | (intros; apply GlobalTheory.FN.hasQ_of_periodic_bounded <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

theorem _root_.GlobalTheory.T.polynomial_relation_passes_to_qExpansions : ∀ (N n : ℕ) (f : ℍ → ℂ) (b : ℕ → ℂ) (p : ℕ → ℍ → ℂ) (c : ℕ → ℕ → ℂ), 0 < N → HasQ N f b → (∀ i, HasQ N (p i) (c i)) → (∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * f τ ^ i = 0) → (∑ i ∈ Finset.range (n + 1), Polynomial.monomial i (PowerSeries.mk (c i))).eval (PowerSeries.mk b) = 0 := by
  first | exact @GlobalTheory.QFam.polyRel_qSeries | exact GlobalTheory.QFam.polyRel_qSeries | (intros; apply GlobalTheory.QFam.polyRel_qSeries <;> assumption)
end

section


theorem _root_.GlobalTheory.T.hasQExpansion_smoothedEisensteinFx_weightOne : ∀ (c M : ℕ) (a b : ℤ), 0 < M → GlobalTheory.QFam.HasQ M (GlobalTheory.Sieg.cF c 1 ![(a : ℚ) / M, (b : ℚ) / M]) (GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M (GlobalTheory.Sieg.ee (1 / (M : ℂ))) a b) := by
  first | exact @GlobalTheory.Sieg.EisQ.hasQ_cF_one | exact GlobalTheory.Sieg.EisQ.hasQ_cF_one | (intros; apply GlobalTheory.Sieg.EisQ.hasQ_cF_one; all_goals assumption)
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_integer_coset_trace_eq (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L] (hv : ∀ (g : G) (x : L), v (g • x) = v x) (U : Subgroup G)
    [Fintype (G ⧸ U)] (hU : AlmostSep v U) (e : L) (he : ∀ g : G, g • e = e) (he1 : v e < 1) :
    ∃ y ∈ Fix L U, v y ≤ 1 ∧ cosetTrace U y = e := by
  obtain ⟨n, a, b, c, hs, hc⟩ := hU (v e) he1
  have hid := GlobalTheory.T.sum_mul_cosetRepresentativeTrace_eq L v G U n a b c hs 1 (one_mem _)
  simp only [mul_one] at hid

  obtain ⟨i, hi⟩ : ∃ i, v e < v (cosetTrace U (b i)) := by
    by_contra h
    push_neg at h
    have : v (∑ i, a i * cosetTrace U (b i)) ≤ v e := by
      apply v.map_sum_le
      intro i _
      rw [v.map_mul]
      calc v (a i) * v (cosetTrace U (b i)) ≤ 1 * v (cosetTrace U (b i)) :=
            mul_le_mul_of_nonneg_right (hs.a_le i) zero_le
        _ = v (cosetTrace U (b i)) := one_mul _
        _ ≤ v e := h i
    rw [hid] at this
    exact absurd hc (not_lt.mpr this)
  set t := cosetTrace U (b i) with ht
  have hfix := GlobalTheory.AlmostEt.cosetTrace_fixed_props L v G hv U (b i) (hs.b_mem i)
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, v.map_zero] at hi; exact absurd hi (not_lt.mpr zero_le)
  have hvt0 : v t ≠ 0 := by rwa [Ne, Valuation.zero_iff]
  have hq : ∀ g : G, g • (e / t) = e / t := by
    intro g
    rw [smul_div₀', he g, hfix.1 g]
  refine ⟨e / t * b i, ?_, ?_, ?_⟩
  · have hb := hs.b_mem i
    intro m
    rw [smul_mul', hb m]
    congr 1
    exact hq (m : G)
  · rw [v.map_mul, map_div₀]
    calc v e / v t * v (b i) ≤ 1 * 1 := by
          apply mul_le_mul' _ (hs.b_le i)
          rw [div_le_one₀ (pos_iff_ne_zero.mpr hvt0)]
          exact hi.le
      _ = 1 := one_mul 1
  · rw [hfix.2.2 (e / t) hq, div_mul_cancel₀ e ht0]

theorem exists_integer_coset_trace_eq' : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (U : Subgroup G) [Fintype (G ⧸ U)], AlmostSep v U → ∀ e : L, (∀ g : G, g • e = e) → v e < 1 → ∃ y ∈ Fix L U, v y ≤ 1 ∧ cosetTrace U y = e :=
  fun L _ v G _ _ hv U _ hU e he he1 => exists_integer_coset_trace_eq L v G hv U hU e he he1

end GlobalTheory.AlmostEt
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem cpow_mul_approx_pow_of_isSep :
    ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ (N : Subgroup G) [Fintype (G ⧸ N)] (θ : ℝ≥0), θ ≤ 1 → (∀ u ∈ Fix L (⊤ : Subgroup G), ∃ w ∈ Fix L (⊤ : Subgroup G), v (u - w ^ p) ≤ θ * v u) → ∀ (n : ℕ) (a b : Fin n → L) (c : L), IsSep v N a b c → ∀ x ∈ Fix L N, v x ≤ 1 → ∃ w ∈ Fix L N, v (c ^ p * x - w ^ p) ≤ max θ (v (p : L)) := by
  intro L _ v p hp G _ _ hv N _ θ hθ hroot n a b c hs x hx hx1
  have frob := GlobalTheory.T.valuation_frobenius_sum_sub_le_natCast_prime L v p hp
  have trfix := GlobalTheory.T.cosetRepresentativeTrace_fixed_properties L v G hv N
  have memN : ∀ y : L, y ∈ Fix L N ↔ ∀ g ∈ N, g • y = y := by
    intro y
    constructor
    · intro h g hg; exact h ⟨g, hg⟩
    · intro h g; exact h g g.2
  have memTop : ∀ y : L, y ∈ Fix L (⊤ : Subgroup G) ↔ ∀ g : G, g • y = y := by
    intro y
    constructor
    · intro h g; exact h ⟨g, Subgroup.mem_top g⟩
    · intro h g; exact h g
  set q₀ : G ⧸ N := ((1 : G) : G ⧸ N) with hq₀
  have hout : ∀ q : G ⧸ N, q.out ∈ N ↔ q = q₀ := fun q => by
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [hq₀, QuotientGroup.eq, mul_one, inv_mem_iff]
  set T : Fin n → L := fun i => cosetTrace N (b i ^ p * x) with hTdef
  have hbx : ∀ i, b i ^ p * x ∈ Fix L N := fun i =>
    Subfield.mul_mem _ (Subfield.pow_mem _ (hs.b_mem i) p) hx
  have hT : ∀ i, (∀ g : G, g • T i = T i) ∧ v (T i) ≤ 1 := fun i => by
    obtain ⟨h1, h2, -⟩ := trfix _ (hbx i)
    refine ⟨h1, h2 ?_⟩
    rw [map_mul, map_pow]
    exact mul_le_one' (pow_le_one' (hs.b_le i) p) hx1
  choose w hwmem hwle using fun i => hroot (T i) ((memTop _).2 (hT i).1)
  have hwθ : ∀ i, v (T i - w i ^ p) ≤ θ := fun i =>
    le_trans (hwle i) (mul_le_of_le_one_right zero_le' (hT i).2)
  have hw1 : ∀ i, v (w i) ≤ 1 := fun i => by
    have : v (w i ^ p) ≤ 1 := by
      have e : w i ^ p = T i - (T i - w i ^ p) := by ring
      rw [e]
      exact Valuation.map_sub_le v (hT i).2 (le_trans (hwθ i) hθ)
    rw [map_pow] at this
    exact (pow_le_one_iff_of_nonneg zero_le' hp.ne_zero).1 this
  set W : L := ∑ i, a i * w i with hWdef
  have hWmem : W ∈ Fix L N := by
    refine Subfield.sum_mem _ fun i _ => Subfield.mul_mem _ (hs.a_mem i) ?_
    exact (memN _).2 fun g _ => (memTop _).1 (hwmem i) g
  refine ⟨W, hWmem, ?_⟩

  have key1 : ∑ i, a i ^ p * T i = ∑ q : G ⧸ N, (∑ i, (a i * q.out • b i) ^ p) * q.out • x := by
    simp only [hTdef, cosetTrace, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul', smul_pow', mul_pow]
    ring
  have key2 : c ^ p * x = ∑ q : G ⧸ N, (∑ i, a i * q.out • b i) ^ p * q.out • x := by
    rw [Finset.sum_eq_single q₀]
    · rw [hs.sum_in _ ((hout q₀).2 rfl), (memN x).1 hx _ ((hout q₀).2 rfl)]
    · intro q _ hq
      rw [hs.sum_out _ (fun h => hq ((hout q).1 h)), zero_pow hp.ne_zero, zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have bound1 : v (c ^ p * x - ∑ i, a i ^ p * T i) ≤ v (p : L) := by
    rw [key1, key2, ← Finset.sum_sub_distrib]
    apply Valuation.map_sum_le
    intro q _
    rw [← sub_mul, map_mul]
    have h1 : v (q.out • x) ≤ 1 := by rw [hv]; exact hx1
    have h2 := frob (Fin n) Finset.univ (fun i => a i * q.out • b i)
      (fun i _ => by rw [map_mul, hv]; exact mul_le_one' (hs.a_le i) (hs.b_le i))
    calc _ ≤ v (p : L) * 1 := mul_le_mul' h2 h1
      _ = _ := mul_one _
  have bound2 : v (∑ i, a i ^ p * T i - ∑ i, a i ^ p * w i ^ p) ≤ θ := by
    rw [← Finset.sum_sub_distrib]
    apply Valuation.map_sum_le
    intro i _
    rw [← mul_sub, map_mul]
    calc _ ≤ 1 * θ := mul_le_mul' (by rw [map_pow]; exact pow_le_one' (hs.a_le i) p) (hwθ i)
      _ = θ := one_mul θ
  have bound3 : v (∑ i, a i ^ p * w i ^ p - W ^ p) ≤ v (p : L) := by
    have h := frob (Fin n) Finset.univ (fun i => a i * w i)
      (fun i _ => by rw [map_mul]; exact mul_le_one' (hs.a_le i) (hw1 i))
    simp only [mul_pow] at h
    rw [Valuation.map_sub_swap]
    exact h
  have e : c ^ p * x - W ^ p = (c ^ p * x - ∑ i, a i ^ p * T i)
      + (∑ i, a i ^ p * T i - ∑ i, a i ^ p * w i ^ p) + (∑ i, a i ^ p * w i ^ p - W ^ p) := by ring
  rw [e]
  refine Valuation.map_add_le v (Valuation.map_add_le v ?_ ?_) ?_
  · exact le_trans bound1 (le_max_right _ _)
  · exact le_trans bound2 (le_max_left _ _)
  · exact le_trans bound3 (le_max_right _ _)

end GlobalTheory.AlmostEt
end

section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.NeedB.TwistCochain

theorem pow_mod_of_pow_eq_one' {Ω : Type} [Field Ω] {N : ℕ} {ζ : Ω} (hN : ζ ^ N = 1) (n : ℕ) :
    ζ ^ (n % N) = ζ ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n N, pow_add, pow_mul, hN, one_pow, one_mul]

theorem twist_cochain : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω] (N : ℕ) (ζ : Ω), 0 < N →
  IsPrimitiveRoot ζ N → (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ) →
  ∀ (a b : K) (α β : Ω), a ≠ 0 → b ≠ 0 → α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
  ∀ w : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant w → (∀ g h, (w g : Ω) * g (w h) * α ^ (kum (N := N) ζ β (g * h)).val =
    α ^ ((kum (N := N) ζ β g).val + (kum (N := N) ζ β h).val) * w (g * h)) →
  ∃ v : (Ω ≃ₐ[K] Ω) → Ωˣ, IsLocallyConstant v ∧
    ∀ g h, (v g : Ω) * g (v h) = ζ ^ (kum (N := N) ζ α g * kum (N := N) ζ β h).val * v (g * h) := by
  intro K Ω _ _ _ _ N ζ hN hζ hζfix a b α β ha hb hα hβ w hw hcoc
  haveI : NeZero N := ⟨hN.ne'⟩
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hα
    exact ha ((algebraMap K Ω).injective (by rw [← hα, map_zero]))
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [zero_pow hN.ne'] at hβ
    exact hb ((algebraMap K Ω).injective (by rw [← hβ, map_zero]))
  obtain ⟨-, hgα, -, -⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ α hN hζ hζfix hα0 ⟨a, hα.symm⟩
  obtain ⟨hylc, -, -, -⟩ := GlobalTheory.T.kummerExponentOfGaloisElement_isKummerCharacter K Ω N ζ β hN hζ hζfix hβ0 ⟨b, hβ.symm⟩
  refine ⟨fun g => Units.mk0 α hα0 ^ (kum (N := N) ζ β g).val * (w g)⁻¹, ?_, ?_⟩
  · exact IsLocallyConstant.comp₂ hylc hw (fun (i : ZMod N) (u : Ωˣ) => Units.mk0 α hα0 ^ i.val * u⁻¹)
  · intro g h
    have hwg : (w g : Ω) ≠ 0 := (w g).ne_zero
    have hwh : g (w h : Ω) ≠ 0 := by simpa using (w h).ne_zero
    have hwgh : (w (g * h) : Ω) ≠ 0 := (w (g * h)).ne_zero
    have hz : ζ ^ (kum (N := N) ζ α g * kum (N := N) ζ β h).val =
        (ζ ^ (kum (N := N) ζ α g).val) ^ (kum (N := N) ζ β h).val := by
      rw [ZMod.val_mul, pow_mod_of_pow_eq_one' hζ.pow_eq_one, pow_mul]
    have hc := hcoc g h
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, map_mul, map_pow, Units.val_inv_eq_inv_val,
      map_inv₀, hgα g, hz]
    rw [pow_add] at hc
    field_simp
    rw [mul_pow]
    linear_combination -(ζ ^ (kum (N := N) ζ α g).val) ^ (kum (N := N) ζ β h).val * hc

end GlobalTheory.NeedB.TwistCochain
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem moves_top_of_coprime_order : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime →
    ∀ F : Subfield L, ApproxRoot p v F → 0 < v (p : L) → v (p : L) < 1 →
    ∀ (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) →
    ∀ σ : G, (∀ x ∈ F, σ • x = x) → ∀ l : ℕ, Nat.Coprime l p → σ ^ l = 1 →
    (∃ y : L, σ • y ≠ y) → Moves v ⊤ σ := by
  intro L _ v p hp F hF hp0 hp1 G _ _ hv σ hσF l hl hσl ⟨y, hy⟩ r hr
  obtain ⟨d, hdF, _hd0, hrx, hx1⟩ :=
    GlobalTheory.T.exists_pth_power_scale_thin_shell L v p hp F hF hp0 hp1 r hr (σ • y - y) (sub_ne_zero.mpr hy)
  set x := (σ • y - y) * d ^ p with hxdef
  refine ⟨x, Subfield.mem_top x, hx1, ?_⟩
  by_contra hle
  push_neg at hle
  have hfix : ∀ j : ℕ, (σ ^ j) • d = d := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, mul_smul, hσF d hdF, ih]
  have hterm : ∀ j : ℕ, (σ ^ j) • x = ((σ ^ (j + 1)) • y - (σ ^ j) • y) * d ^ p := by
    intro j
    rw [hxdef, smul_mul', smul_pow', hfix, smul_sub, pow_succ, mul_smul]
  have hsum : ∑ j ∈ Finset.range l, (σ ^ j) • x = 0 := by
    simp_rw [hterm]
    rw [← Finset.sum_mul, Finset.sum_range_sub (fun j => (σ ^ j) • y), hσl, one_smul, pow_zero,
      one_smul, sub_self, zero_mul]
  have hstep : ∀ j : ℕ, v ((σ ^ j) • x - x) ≤ r := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e : (σ ^ (j + 1)) • x - x = σ • ((σ ^ j) • x - x) + (σ • x - x) := by
        rw [smul_sub, pow_succ', mul_smul]; ring
      rw [e]
      refine le_trans (Valuation.map_add _ _ _) (max_le ?_ hle)
      rw [hv]; exact ih
  have hlx : (l : L) * x = ∑ j ∈ Finset.range l, (x - (σ ^ j) • x) := by
    rw [Finset.sum_sub_distrib, hsum, sub_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have h1 : v ((l : L) * x) ≤ r := by
    rw [hlx]
    apply Valuation.map_sum_le
    intro j _
    rw [← Valuation.map_neg, neg_sub]
    exact hstep j
  rw [map_mul, GlobalTheory.T.valuation_natCast_eq_one_of_coprime' L v p l hp1 hl, one_mul] at h1
  exact absurd (lt_of_lt_of_le hrx h1) (lt_irrefl _)

end GlobalTheory.AlmostEt
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

open Topology

lemma exists_lt_one_lt_pow (r : ℝ≥0) (hr : r < 1) (k : ℕ) : ∃ t : ℝ≥0, t < 1 ∧ r < t ^ k := by
  have hopen : IsOpen {t : ℝ≥0 | r < t ^ k} := isOpen_lt continuous_const (continuous_pow k)
  have hmem : {t : ℝ≥0 | r < t ^ k} ∈ 𝓝 (1 : ℝ≥0) := hopen.mem_nhds (by simpa using hr)
  obtain ⟨l, hl, hsub⟩ := exists_Ioc_subset_of_mem_nhds hmem ⟨0, zero_lt_one⟩
  obtain ⟨t, hlt, ht1⟩ := exists_between hl
  exact ⟨t, ht1, hsub ⟨hlt, ht1.le⟩⟩

lemma smul_mem_fix {L : Type} [Field L] {G : Type} [Group G] [MulSemiringAction G L]
    (N : Subgroup G) [hN : N.Normal] (g : G) {y : L} (hy : y ∈ Fix L N) : g • y ∈ Fix L N := by
  intro n
  have hc : g⁻¹ * (n : G) * g ∈ N := by
    have := hN.conj_mem (n : G) n.2 g⁻¹
    simpa using this
  have h1 : (g⁻¹ * (n : G) * g) • y = y := hy ⟨_, hc⟩
  show (n : G) • g • y = g • y
  calc (n : G) • g • y = g • ((g⁻¹ * (n : G) * g) • y) := by
        simp only [mul_smul, smul_inv_smul]
    _ = g • y := by rw [h1]

lemma fix_smul {L : Type} [Field L] {G : Type} [Group G] [MulSemiringAction G L]
    (N : Subgroup G) {y : L} (hy : y ∈ Fix L N) {σ : G} (hσ : σ ∈ N) : σ • y = y :=
  hy ⟨σ, hσ⟩

theorem almostSep_of_moves : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ N : Subgroup G, N.Normal →
    N.FiniteIndex → (∀ σ : G, σ ∉ N → Moves v (Fix L N) σ) → AlmostSep v N := by
  intro L _ v G _ _ hv N hN hfi hmov r hr
  classical
  haveI : Finite (G ⧸ N) := inferInstance
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  set s : Finset (G ⧸ N) := Finset.univ.erase 1 with hs
  obtain ⟨t, ht1, hrt⟩ := exists_lt_one_lt_pow r hr s.card
  have hex : ∀ q : G ⧸ N, ∃ y : L, y ∈ Fix L N ∧ v y ≤ 1 ∧ (q ≠ 1 → t < v (q.out • y - y)) := by
    intro q
    by_cases hq : q = 1
    · exact ⟨0, zero_mem _, by simp, fun h => absurd hq h⟩
    · have hout : q.out ∉ N := by
        intro hm
        apply hq
        rw [← QuotientGroup.out_eq' q]
        exact (QuotientGroup.eq_one_iff _).2 hm
      obtain ⟨y, hyF, hyv, hyt⟩ := hmov _ hout t ht1
      exact ⟨y, hyF, hyv, fun _ => hyt⟩
  choose y hyF hyv hyt using hex
  let x : G ⧸ N → L := fun q => q.out • y q
  have hxF : ∀ q, x q ∈ Fix L N := fun q => smul_mem_fix N _ (hyF q)
  have hxv : ∀ q, v (x q) ≤ 1 := fun q => by simp only [x, hv]; exact hyv q
  obtain ⟨n, a, b, hab, hsum⟩ := GlobalTheory.T.separating_family_sum_closed_under_prod L v G (Fix L N) (G ⧸ N) s x y
    (fun j _ => ⟨hxF j, hyF j, hxv j, hyv j⟩)
  refine ⟨n, a, b, ∏ q ∈ s, (x q - y q), ?_, ?_⟩
  · refine
      { a_mem := fun i => (hab i).1
        b_mem := fun i => (hab i).2.1
        c_mem := ?_
        a_le := fun i => (hab i).2.2.1
        b_le := fun i => (hab i).2.2.2
        c_le := ?_
        sum_in := ?_
        sum_out := ?_ }
    · exact prod_mem fun q _ => sub_mem (hxF q) (hyF q)
    · rw [map_prod]
      refine Finset.prod_le_one₀ (fun _ _ => zero_le) fun q _ => ?_
      exact (Valuation.map_sub v _ _).trans (max_le (hxv q) (hyv q))
    · intro σ hσ
      rw [hsum σ]
      refine Finset.prod_congr rfl fun q _ => ?_
      rw [fix_smul N (hyF q) hσ]
    · intro σ hσ
      rw [hsum σ]
      have hq : (σ : G ⧸ N) ∈ s := by
        rw [hs, Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        intro h
        exact hσ ((QuotientGroup.eq_one_iff σ).1 h)
      refine Finset.prod_eq_zero hq ?_
      obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul N σ
      simp only [x]
      rw [hm, mul_smul, fix_smul N (hyF _) m.2, sub_self]
  · rw [map_prod]
    calc r < t ^ s.card := hrt
      _ = ∏ _q ∈ s, t := by rw [Finset.prod_const]
      _ ≤ ∏ q ∈ s, v (x q - y q) := by
        refine Finset.prod_le_prod₀ (fun _ _ => zero_le) fun q hq => ?_
        exact (hyt q (Finset.ne_of_mem_erase hq)).le

end GlobalTheory.AlmostEt
end

section

open GlobalTheory.KummerEisensteinGalois Finset
open scoped Classical

theorem _root_.GlobalTheory.T.smoothedEisensteinFx_sum_row_lifts_distribution : ∀ (p : ℕ) [Fact p.Prime] (N n j : ℕ) (K : Type) [Field K] [CharZero K] (ζ : K) (c : ℤ) (x₁ x₂ : ZMod (p ^ n)) (u₁ u₂ w₁ w₂ : ℤ), IsPrimitiveRoot ζ (N * p ^ (n + 1)) → 0 < N → ¬ p ∣ N → 1 ≤ n → 1 ≤ j → ¬ (p : ℤ) ∣ c → ¬ p ∣ x₁.val → (p : ℤ) * u₁ ≡ w₁ [ZMOD N] → (p : ℤ) * u₂ ≡ w₂ [ZMOD N] → ∀ r : ℕ, ∑ y₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = x₁)), ∑ y₂ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = x₂)), smF c j (N * p ^ (n + 1)) ζ ((N : ℤ) * (y₁.val : ℤ) + (p : ℤ) ^ (n + 1) * u₁) ((N : ℤ) * (y₂.val : ℤ) + (p : ℤ) ^ (n + 1) * u₂) r = (p : K) ^ ((2 : ℤ) - (j : ℤ)) * vp p (smF c j (N * p ^ n) (ζ ^ p) ((N : ℤ) * (x₁.val : ℤ) + (p : ℤ) ^ n * w₁) ((N : ℤ) * (x₂.val : ℤ) + (p : ℤ) ^ n * w₂)) r := by
  first | exact @GlobalTheory.KummerEisensteinGalois.RowFibre.smF_sum_lifts | exact GlobalTheory.KummerEisensteinGalois.RowFibre.smF_sum_lifts | (intros; apply GlobalTheory.KummerEisensteinGalois.RowFibre.smF_sum_lifts <;> assumption)
end
