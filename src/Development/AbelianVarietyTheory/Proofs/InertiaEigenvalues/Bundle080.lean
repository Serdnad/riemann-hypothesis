module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Aesop.Main
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle018
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle019
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.IsOpenUnits
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle020
public import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Calculus.FDeriv.Pow

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.CosetIntegral

theorem integral_sum_indicator_translate {G ι : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (m : Measure G)
    [m.IsMulRightInvariant] (H : Set G) (hH : IsOpen H) (hm : m H = 1) (T : Finset ι)
    (r : ι → G) (c : ι → ℂ) :
    ∫ x, ∑ q ∈ T, ((fun y => y * (r q)⁻¹) ⁻¹' H).indicator (fun _ => c q) x ∂m
      = ∑ q ∈ T, c q := by
  have hmeas : ∀ q, MeasurableSet ((fun y => y * (r q)⁻¹) ⁻¹' H) := fun q =>
    (hH.preimage (continuous_mul_const _)).measurableSet
  have hmq : ∀ q, m ((fun y => y * (r q)⁻¹) ⁻¹' H) = 1 := fun q => by
    rw [measure_preimage_mul_right, hm]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_indicator_const _ (hmeas q), measureReal_def, hmq q]
    simp
  · intro q _
    exact (integrable_indicator_iff (hmeas q)).2 (integrableOn_const (by rw [hmq q]; simp))

theorem integral_eq_of_coset_support
    (R S : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [LocallyCompactSpace R]
    [T2Space R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] [Group S]
    [TopologicalSpace S] [IsTopologicalGroup S] [MeasurableSpace S] [BorelSpace S]
    (i : S →* R) (hi : Topology.IsClosedEmbedding i) (μ : Measure R) (ν : Measure S)
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    (R₀ : Subgroup R) (hR₀o : IsOpen (R₀ : Set R)) (_hR₀c : IsCompact (R₀ : Set R))
    (hμ : μ R₀ = 1) (hν : ν (i ⁻¹' R₀) = 1) (h : R → ℂ)
    (hinv : ∀ k ∈ R₀, ∀ g, h (k * g) = h g)
    (hsupp : ∀ g, h g ≠ 0 → ∃ k ∈ R₀, ∃ s, g = k * i s)
    (hcs : HasCompactSupport (fun s => h (i s))) :
    ∫ g, h g ∂μ = ∫ s, h (i s) ∂ν := by
  classical
  let S₀ : Subgroup S := R₀.comap i
  have hS₀o : IsOpen (i ⁻¹' (R₀ : Set R)) := hR₀o.preimage hi.continuous
  have hconst : ∀ g r, g * (i r)⁻¹ ∈ R₀ → h (i r) = h g := by
    intro g r hg
    have := hinv _ hg (i r)
    simpa using this.symm
  let U : S → Set S := fun s => (fun x => x * s⁻¹) ⁻¹' (i ⁻¹' (R₀ : Set R))
  have hUo : ∀ s, IsOpen (U s) := fun s => hS₀o.preimage (continuous_mul_const _)
  obtain ⟨t, ht⟩ := hcs.isCompact.elim_finite_subcover U hUo
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [U, R₀.one_mem]⟩)
  let mk : S → Quotient (QuotientGroup.rightRel S₀) := fun s => Quotient.mk _ s
  let T := t.image mk
  have hrel : ∀ a b : S, mk a = mk b ↔ i b * (i a)⁻¹ ∈ R₀ := fun a b => by
    simp only [mk, Quotient.eq, QuotientGroup.rightRel_apply, S₀, Subgroup.mem_comap,
      map_mul, map_inv]
  have hout : ∀ q, mk q.out = q := fun q => Quotient.out_eq q
  have hsuppT : ∀ x, h (i x) ≠ 0 → mk x ∈ T := by
    intro x hx
    have hx' : x ∈ tsupport (fun s => h (i s)) := subset_tsupport _ hx
    obtain ⟨s, hs, hxs⟩ := Set.mem_iUnion₂.1 (ht hx')
    refine Finset.mem_image.2 ⟨s, hs, (hrel s x).2 ?_⟩
    simpa [U] using hxs
  have hrep : ∀ x, h (i (mk x).out) = h (i x) := by
    intro x
    apply hconst
    exact (hrel _ x).1 (hout _)

  have hR : (fun g => h g) = fun g => ∑ q ∈ T,
      ((fun y => y * (i q.out)⁻¹) ⁻¹' (R₀ : Set R)).indicator (fun _ => h (i q.out)) g := by
    funext g
    by_cases hg : h g = 0
    · rw [hg]
      symm
      refine Finset.sum_eq_zero fun q _ => ?_
      by_cases hm : g ∈ ((fun y => y * (i q.out)⁻¹) ⁻¹' (R₀ : Set R))
      · rw [Set.indicator_of_mem hm, hconst g _ hm, hg]
      · rw [Set.indicator_of_notMem hm]
    · obtain ⟨k, hk, s, rfl⟩ := hsupp g hg
      have hs : h (i s) ≠ 0 := by rwa [hinv k hk] at hg
      have hmem : ∀ q, (k * i s ∈ ((fun y => y * (i q.out)⁻¹) ⁻¹' (R₀ : Set R))) ↔ mk s = q := by
        intro q
        have e : mk s = q ↔ i s * (i q.out)⁻¹ ∈ R₀ := by rw [← hrel q.out s, hout q, eq_comm]
        rw [e]
        simp only [Set.mem_preimage, SetLike.mem_coe, mul_assoc]
        exact Subgroup.mul_mem_cancel_left R₀ hk
      simp only [Set.indicator, hmem, Finset.sum_ite_eq, if_pos (hsuppT s hs), hrep, hinv k hk]
  have hS : (fun x => h (i x)) = fun x => ∑ q ∈ T,
      ((fun y => y * q.out⁻¹) ⁻¹' (i ⁻¹' (R₀ : Set R))).indicator (fun _ => h (i q.out)) x := by
    funext x
    have hmem : ∀ q, x ∈ ((fun y => y * q.out⁻¹) ⁻¹' (i ⁻¹' (R₀ : Set R))) ↔ mk x = q := by
      intro q
      have e : mk x = q ↔ i x * (i q.out)⁻¹ ∈ R₀ := by rw [← hrel q.out x, hout q, eq_comm]
      rw [e]
      simp
    simp only [Set.indicator, hmem, Finset.sum_ite_eq]
    split_ifs with hx
    · rw [hrep]
    · by_contra hne
      exact hx (hsuppT x hne)
  rw [hR, hS, integral_sum_indicator_translate μ _ hR₀o hμ,
    integral_sum_indicator_translate ν _ hS₀o hν]

end GlobalTheory.CosetIntegral
end

section

open GlobalTheory.UnitLemma Matrix MeasureTheory

namespace GlobalTheory

theorem integral_rightCoset_fun_eq_finsum (G Λ : Type) [Group G] [TopologicalSpace G] [ContinuousMul G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulRightInvariant] (H : Set G)
    (hH : IsOpen H) (hμ : μ H = 1) (π : G → Λ) (hπ : ∀ g g', π g' = π g ↔ g' * g⁻¹ ∈ H)
    (s : Λ → ℂ) (hs : ∀ l, s l = 0 ∨ ‖s l‖ = 1) :
    ∫ g, s (π g) ∂μ = ∑ᶠ l ∈ Set.range π, s l := by
  classical

  have hfib : ∀ g, π ⁻¹' {π g} = (fun x => x * g⁻¹) ⁻¹' H := by
    intro g; ext x; simp [hπ g x]
  have hfibO : ∀ g, IsOpen (π ⁻¹' {π g}) := by
    intro g; rw [hfib g]; exact hH.preimage (continuous_mul_const _)
  have hfibM : ∀ l, MeasurableSet (π ⁻¹' {l}) := by
    intro l
    by_cases hl : l ∈ Set.range π
    · obtain ⟨g, rfl⟩ := hl; exact (hfibO g).measurableSet
    · have : π ⁻¹' {l} = ∅ := by
        ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        exact fun h => hl ⟨x, h⟩
      rw [this]; exact MeasurableSet.empty
  have hfib1 : ∀ g, μ (π ⁻¹' {π g}) = 1 := by
    intro g; rw [hfib g, measure_preimage_mul_right, hμ]
  set S := Set.range π ∩ Function.support s with hSdef
  by_cases hS : S.Finite
  · set T := hS.toFinset with hT
    have hfun : (fun g => s (π g)) = fun g => ∑ l ∈ T, (π ⁻¹' {l}).indicator (fun _ => s l) g := by
      funext g
      have : ∀ l, (π ⁻¹' {l}).indicator (fun _ => s l) g = if π g = l then s (π g) else 0 := by
        intro l
        by_cases h : π g = l
        · subst h; simp
        · simp [Set.indicator_apply, h]
      simp only [this, Finset.sum_ite_eq]
      split_ifs with h
      · rfl
      · have : π g ∉ S := by rw [hT, Set.Finite.mem_toFinset] at *; exact h
        by_contra hne
        exact this ⟨⟨g, rfl⟩, Ne.symm hne |>.symm⟩
    rw [hfun, MeasureTheory.integral_finsetSum]
    · rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hS]
      refine Finset.sum_congr rfl ?_
      intro l hl
      rw [integral_indicator_const _ (hfibM l)]
      have hl' : l ∈ Set.range π := ((Set.Finite.mem_toFinset hS).1 hl).1
      obtain ⟨g, rfl⟩ := hl'
      simp [Measure.real, hfib1 g]
    · intro l _
      exact (integrable_indicator_iff (hfibM l)).2 (by
        by_cases hl : l ∈ Set.range π
        · obtain ⟨g, rfl⟩ := hl
          haveI : IsFiniteMeasure (μ.restrict (π ⁻¹' {π g})) := ⟨by simp [hfib1 g]⟩
          exact integrable_const _
        · have : π ⁻¹' {l} = ∅ := by
            ext x; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
            exact fun h => hl ⟨x, h⟩
          rw [this]; exact integrableOn_empty)
  · rw [finsum_mem_eq_zero_of_infinite hS]
    apply integral_undef
    intro hint
    have hfin := hint.2

    have hbound : ∀ F : Finset Λ, (↑F : Set Λ) ⊆ S → (F.card : ENNReal) ≤ ∫⁻ g, ‖s (π g)‖ₑ ∂μ := by
      intro F hF
      calc (F.card : ENNReal) = ∑ l ∈ F, μ (π ⁻¹' {l}) := by
            rw [Finset.card_eq_sum_ones, Nat.cast_sum]
            refine Finset.sum_congr rfl ?_
            intro l hl
            obtain ⟨⟨g, rfl⟩, _⟩ := hF hl
            simp [hfib1 g]
        _ = ∫⁻ g, ∑ l ∈ F, (π ⁻¹' {l}).indicator 1 g ∂μ := by
            rw [MeasureTheory.lintegral_finsetSum]
            · refine Finset.sum_congr rfl ?_
              intro l _
              rw [lintegral_indicator_one (hfibM l)]
            · intro l _
              exact (measurable_one.indicator (hfibM l))
        _ ≤ ∫⁻ g, ‖s (π g)‖ₑ ∂μ := by
            apply lintegral_mono
            intro g
            have : ∀ l, (π ⁻¹' {l}).indicator (1 : G → ENNReal) g = if π g = l then 1 else 0 := by
              intro l; simp [Set.indicator_apply]
            simp only [this, Finset.sum_ite_eq]
            split_ifs with h
            · obtain ⟨_, hsupp⟩ := hF h
              rcases hs (π g) with h0 | h1
              · exact absurd h0 hsupp
              · rw [← ofReal_norm_eq_enorm, h1]; simp
            · exact bot_le
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfin.ne
    obtain ⟨F, hFS, hFc⟩ := Set.Infinite.exists_subset_card_eq (hS : S.Infinite) n
    have := hbound F hFS
    rw [hFc] at this
    exact absurd (lt_of_le_of_lt this hn) (lt_irrefl _)

end GlobalTheory
end

section

open Polynomial

theorem _root_.GlobalTheory.T.norm_taylor_coeff_sub_coeff_le_norm_l : ∀ (l : ℕ) [Fact l.Prime] (E : ℕ) (a : ℕ → ℂ_[l]) (W : ℂ_[l]), (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖W‖ ≤ 1 → ∀ j : ℕ, 1 ≤ j → ‖(Polynomial.taylor W (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l])).coeff j - (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).coeff j‖ ≤ ‖(l : ℂ_[l])‖ := by
  first | exact @GlobalTheory.additive_poly_taylor_coeff_sub_norm_le | exact GlobalTheory.additive_poly_taylor_coeff_sub_norm_le | (intros; apply GlobalTheory.additive_poly_taylor_coeff_sub_norm_le <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.indep_over_padic_of_indep_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (d : ℕ) (ι : Type) (w : Fin d → ι → ℂ_[l]) (γ : ι → ℝ), (∀ a i, ‖w a i‖ ≤ γ i) → (∀ n : Fin d → ℕ, (∀ i, ‖∑ a, (n a : ℂ_[l]) * w a i‖ ≤ ‖(l : ℂ_[l])‖ * γ i) → ∀ a, l ∣ n a) → ∀ c : Fin d → ℚ_[l], (∀ i, ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * w a i = 0) → c = 0 := by
  first | exact @GlobalTheory.indep_over_Ql_of_indep_mod_l | exact GlobalTheory.indep_over_Ql_of_indep_mod_l | (intros; apply GlobalTheory.indep_over_Ql_of_indep_mod_l <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.lift_hasSum_zero_of_surjective_mod_prime : ∀ (l : ℕ) [Fact l.Prime] (X ι : Type) (η : X → ι → ℂ_[l]) (τ : ι → ℝ) (S : Set X), (∀ t : ι → ℂ_[l], (∀ i, ‖t i‖ ≤ τ i) → ∃ y ∈ S, ∀ i, ‖η y i - t i‖ ≤ ‖(l : ℂ_[l])‖ * τ i) → ∀ x ∈ S, (∀ i, ‖η x i‖ ≤ ‖(l : ℂ_[l])‖ * τ i) → ∃ y : ℕ → X, y 0 = x ∧ (∀ k, y k ∈ S) ∧ ∀ i, HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * η (y k) i) 0 := by
  first | exact @GlobalTheory.lift_hasSum_zero | exact GlobalTheory.lift_hasSum_zero | (intros; apply GlobalTheory.lift_hasSum_zero <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_eigenvector_hasSum_adicComplete_frobenius : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (w : ℕ → A), (∀ k, φ^[h] (w k) = (l : A) * w k) → ∃ W : A, φ^[h] W = (l : A) * W ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) → HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * Θ (w k)) (Θ W) := by
  first | exact @GlobalTheory.abssum_eigen_lim | exact GlobalTheory.abssum_eigen_lim | (intros; apply GlobalTheory.abssum_eigen_lim <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.twoSided_shift_series_hasSum : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (c : ℤ → A), (∀ n : ℤ, (l : A) ^ n.natAbs ∣ c n) → (∀ n : ℤ, φ^[h] (c n) = (l : A) * c (n + 1)) → ∃ w : A, φ^[h] w = (l : A) * w ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) → HasSum (fun n : ℤ => Θ (c n)) (Θ w) := by
  first | exact @GlobalTheory.twoSided_shift_series | exact GlobalTheory.twoSided_shift_series | (intros; apply GlobalTheory.twoSided_shift_series <;> assumption)
end

section

open Polynomial
open Classical

theorem _root_.GlobalTheory.T.exists_finset_separated_of_multiset_bounded_cluster : ∀ (K : Type) [NormedAddCommGroup K] (s : Multiset K) (ρ : ℝ) (A B : ℕ), 0 ≤ ρ → 0 < B → A * B ≤ Multiset.card s → (∀ W ∈ s, Multiset.card (s.filter fun z => ‖z - W‖ ≤ ρ) ≤ B) → ∃ Z : Finset K, A ≤ Z.card ∧ (∀ W ∈ Z, W ∈ s) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by
  first | exact @GlobalTheory.multiset_many_separated_points | exact GlobalTheory.multiset_many_separated_points | (intros; apply GlobalTheory.multiset_many_separated_points <;> assumption)
end

section

open GlobalTheory.JR MeasureTheory Filter Topology

namespace GlobalTheory


open MeasureTheory Filter Topology in
theorem _root_.GlobalTheory.isOpenUnits_and_eventually_sq_normed (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] [CharZero F] (R : Type) [NormedCommRing R] [NormedAlgebra F R]
    [Module.Finite F R] :
    IsOpenUnits R ∧ ∀ᶠ v in 𝓝 (1 : R), ∃ s : R, s ^ 2 = v := by
  haveI : CompleteSpace R := FiniteDimensional.complete F R
  refine ⟨⟨Units.isOpenEmbedding_val⟩, ?_⟩
  have hd := hasStrictFDerivAt_pow (𝕜 := F) 2 (x := (1 : R))
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hsurj : LinearMap.range
      ((((2 : ℕ) • (1 : R) ^ (2 - 1)) • ContinuousLinearMap.id F R : R →L[F] R) : R →ₗ[F] R)
        = ⊤ := by
    refine LinearMap.range_eq_top.2 fun v => ⟨(2 : F)⁻¹ • v, ?_⟩
    have hc : ((2 : ℕ) • (1 : R) ^ (2 - 1)) = algebraMap F R 2 := by
      simp [two_smul, map_ofNat, one_add_one_eq_two]
    simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_id', Pi.smul_apply,
      id_eq, hc, ContinuousLinearMap.coe_coe, smul_eq_mul]
    rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ h2, one_smul]
  have hmap := hd.map_nhds_eq_of_surj hsurj
  rw [one_pow] at hmap
  rw [← hmap, Filter.eventually_map]
  exact Filter.Eventually.of_forall fun s => ⟨s, rfl⟩


open MeasureTheory Filter Topology in
theorem _root_.GlobalTheory.finiteNormedAlgebra_eq_moduleTopology (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] (R : Type) [N : NormedCommRing R] [NormedAlgebra F R]
    [Module.Finite F R] :
    N.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      = moduleTopology F R := by
  haveI : IsModuleTopology F R := isModuleTopologyOfFiniteDimensional
  exact eq_moduleTopology F R


open MeasureTheory Filter Topology in
theorem _root_.GlobalTheory.isOpenUnits_and_eventually_sq (F : Type) [NontriviallyNormedField F]
    [CompleteSpace F] [CharZero F] (R : Type) [CommRing R] [Algebra F R] [Module.Finite F R]
    [τ : TopologicalSpace R] [IsModuleTopology F R] :
    IsOpenUnits R ∧ ∀ᶠ v in 𝓝 (1 : R), ∃ s : R, s ^ 2 = v := by
  classical
  have h := eq_moduleTopology F R
  let b := Module.finBasis F R
  letI : NormedRing (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedRing
  letI : NormedAlgebra F (Matrix (Fin (Module.finrank F R)) (Fin (Module.finrank F R)) F) :=
    Matrix.linftyOpNormedAlgebra
  letI N : NormedCommRing R :=
    NormedCommRing.induced R _ (Algebra.leftMulMatrix b) (Algebra.leftMulMatrix_injective b)
  letI : NormedAlgebra F R := NormedAlgebra.induced F R _ (Algebra.leftMulMatrix b)
  have key := _root_.GlobalTheory.isOpenUnits_and_eventually_sq_normed F R
  have h2 := _root_.GlobalTheory.finiteNormedAlgebra_eq_moduleTopology F R
  have h3 : τ = N.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace :=
    h.trans h2.symm
  rw [h3]
  exact key

end GlobalTheory
end

section

open Filter Topology

theorem _root_.GlobalTheory.T.spectralNorm_closedBall_isOpen_isCompact_nhds : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [LocallyCompactSpace F] (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [TopologicalSpace L] [IsModuleTopology F L], IsOpen {y : L | spectralNorm F L y ≤ 1} ∧ IsCompact {y : L | spectralNorm F L y ≤ 1} ∧ ∀ U ∈ 𝓝 (0 : L), ∃ r : ℝ, 0 < r ∧ ∀ y : L, spectralNorm F L y < r → y ∈ U := by
  first | exact @GlobalTheory.spectralNorm_closedBall_isOpen_isCompact_nhds_basis | exact GlobalTheory.spectralNorm_closedBall_isOpen_isCompact_nhds_basis | (intros; apply GlobalTheory.spectralNorm_closedBall_isOpen_isCompact_nhds_basis <;> assumption)
end

section

open ValuativeRel

theorem _root_.GlobalTheory.T.exists_localField_structure_spectralNorm : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [LocallyCompactSpace F] (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K], ∃ (_ : ValuativeRel K) (_ : TopologicalSpace K), IsNonarchimedeanLocalField K ∧ ∀ x y : K, x ≤ᵥ y ↔ spectralNorm F K x ≤ spectralNorm F K y := by
  first | exact @GlobalTheory.exists_isNonarchimedeanLocalField_spectralNorm | exact GlobalTheory.exists_isNonarchimedeanLocalField_spectralNorm | (intros; apply GlobalTheory.exists_isNonarchimedeanLocalField_spectralNorm <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

open Polynomial

noncomputable section

namespace GlobalTheory.JR.Spec

variable {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F]
  {k : Type} [Field k] [Algebra F k]

theorem isIntegral_integer_of_spectralNorm_le_one [FiniteDimensional F k] {y : k}
    (h : spectralNorm F k y ≤ 1) : IsIntegral (NormedField.valuation (K := F)).integer y := by
  have hyF : IsIntegral F y := Algebra.IsIntegral.isIntegral y
  rw [spectralNorm, spectralValue_le_one_iff (minpoly.monic hyF)] at h
  have hl : minpoly F y ∈ lifts (algebraMap (NormedField.valuation (K := F)).integer F) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    refine ⟨⟨_, ?_⟩, rfl⟩
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    exact_mod_cast h n
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl (minpoly.monic hyF)
  refine ⟨q, hqm, ?_⟩
  rw [← aeval_def, ← aeval_map_algebraMap F, hq, minpoly.aeval]

theorem isIntegral_or_isIntegral_inv : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 →
    IsIntegral (NormedField.valuation (K := F)).integer y ∨
      IsIntegral (NormedField.valuation (K := F)).integer y⁻¹ := by
  intro F _ _ _ k _ _ _ y hy0
  have hmul : spectralNorm F k y * spectralNorm F k y⁻¹ = 1 := by
    have := spectralAlgNorm_mul (K := F) (L := k) y y⁻¹
    rw [spectralAlgNorm_def, spectralAlgNorm_def, spectralAlgNorm_def, mul_inv_cancel₀ hy0,
      spectralNorm_one] at this
    exact this.symm
  by_cases h : spectralNorm F k y ≤ 1
  · exact Or.inl (isIntegral_integer_of_spectralNorm_le_one h)
  · right
    apply isIntegral_integer_of_spectralNorm_le_one
    have h1 : 1 < spectralNorm F k y := lt_of_not_ge h
    by_contra h2
    have h2 : 1 < spectralNorm F k y⁻¹ := lt_of_not_ge h2
    have : 1 < spectralNorm F k y * spectralNorm F k y⁻¹ := one_lt_mul_of_lt_of_le h1 h2.le
    linarith

end GlobalTheory.JR.Spec
end
end
