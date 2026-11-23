module

public import GroundTheory.LocalFields.Interface
public import Mathlib.RingTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Trace.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle080
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle077
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle177
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle061
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle181
public import Mathlib.RingTheory.PowerSeries.Substitution
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle050
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle182
public import ReciprocityTheory.Hypotheses.GalCohDefs
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle155
import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import ReciprocityTheory.Hypotheses.GalCoh

@[expose] public section

section

open ValuativeRel

theorem _root_.GlobalTheory.T.unramified_quadratic_norm_trace_surjective : ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L], (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1 → Module.finrank K L = 2 → ∃ ϖ : K, ϖ ≠ 0 ∧ ϖ ≤ᵥ 1 ∧ ¬ (1 : K) ≤ᵥ ϖ ∧ (¬ ∃ y : L, Algebra.norm K y = ϖ) ∧ (∀ y : L, y ≤ᵥ 1 → (∃ z : L, z ≤ᵥ 1 ∧ y = algebraMap K L ϖ * z) ∨ ∃ z : L, z ≤ᵥ 1 ∧ y * z = 1) ∧ (∀ s : K, s ≤ᵥ 1 → ∃ z : L, z ≤ᵥ 1 ∧ Algebra.trace K L z = s) ∧ ∀ s : K, s ≤ᵥ 1 → 1 ≤ᵥ s → ∃ w : L, w ≤ᵥ 1 ∧ Algebra.norm K w = s := by
  first | exact @GlobalTheory.unramified_quadratic_uniformizer_trace_norm | exact GlobalTheory.unramified_quadratic_uniformizer_trace_norm | (intros; apply GlobalTheory.unramified_quadratic_uniformizer_trace_norm <;> assumption)
end

section

open Polynomial
open Classical

namespace GlobalTheory

theorem roots_taylor_eq_map_sub {K : Type*} [Field K] (p : K[X]) (w : K) :
    (taylor w p).roots = p.roots.map (fun x => x - w) := by
  have h := roots_comp_C_mul_X_add_C p (1 : K) w isUnit_one
  rw [taylor_apply]
  simpa using h

theorem coeff_sum_monomial_pow (l : ℕ) [Fact l.Prime] (E : ℕ) (a : ℕ → ℂ_[l]) (k : ℕ)
    (hk : k ≤ E) :
    (∑ i ∈ Finset.range (E + 1), monomial (l ^ i) (a i) : ℂ_[l][X]).coeff (l ^ k) = a k := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  rw [finsetSum_coeff, Finset.sum_eq_single k]
  · simp [coeff_monomial]
  · intro i _ hik
    rw [coeff_monomial, Finsupp.single_apply, if_neg]
    intro h
    exact hik (Nat.pow_right_injective hl h)
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem coeff_sum_monomial_small (l : ℕ) [Fact l.Prime] (E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ)
    (hρ : 0 < ρ)
    (hgt : ∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) (j : ℕ) (hj : l ^ M < j) :
    ‖(∑ i ∈ Finset.range (E + 1), monomial (l ^ i) (a i) : ℂ_[l][X]).coeff j‖ * ρ ^ j
      < ‖(l : ℂ_[l])‖ := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := by
    rw [norm_pos_iff]; exact_mod_cast (by omega : l ≠ 0)
  by_cases h : ∃ k, k ≤ E ∧ l ^ k = j
  · obtain ⟨k, hkE, rfl⟩ := h
    rw [coeff_sum_monomial_pow l E a k hkE]
    have hMk : M < k := (Nat.pow_lt_pow_iff_right (by omega)).mp hj
    exact hgt k hMk hkE
  · have h0 : (∑ i ∈ Finset.range (E + 1), monomial (l ^ i) (a i) : ℂ_[l][X]).coeff j = 0 := by
      rw [finsetSum_coeff]
      refine Finset.sum_eq_zero fun i hi => ?_
      rw [coeff_monomial, Finsupp.single_apply, if_neg]
      intro hij
      exact h ⟨i, by have := Finset.mem_range.mp hi; omega, hij⟩
    rw [h0, norm_zero, zero_mul]
    exact hlpos

theorem few_roots_small_disc : ∀ (l : ℕ) [Fact l.Prime] (E M : ℕ) (a : ℕ → ℂ_[l]) (ρ : ℝ) (W : ℂ_[l]), M ≤ E → (∀ k, k ≤ E → ‖a k‖ ≤ 1) → 0 < ρ → ρ < 1 → ‖a M‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ → (∀ k, M < k → k ≤ E → ‖a k‖ * ρ ^ l ^ k < ‖(l : ℂ_[l])‖) → ‖W‖ ≤ 1 → Multiset.card ((∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).roots.filter fun z => ‖z - W‖ ≤ ρ) ≤ l ^ M := by
  intro l _ E M a ρ W hME ha hρ0 hρ1 hM hgt hW
  set G : ℂ_[l][X] := ∑ k ∈ Finset.range (E + 1), monomial (l ^ k) (a k) with hG
  set H := taylor W G with hH
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := by
    rw [norm_pos_iff]; exact_mod_cast (by omega : l ≠ 0)
  have hroots : Multiset.card (G.roots.filter fun z => ‖z - W‖ ≤ ρ)
      = Multiset.card (H.roots.filter fun z => ‖z‖ ≤ ρ) := by
    rw [hH, roots_taylor_eq_map_sub, Multiset.filter_map, Multiset.card_map]
    rfl
  rw [hroots]
  have hd1 : 1 ≤ l ^ M := Nat.one_le_pow _ _ (by omega)
  have hGd : G.coeff (l ^ M) = a M := coeff_sum_monomial_pow l E a M hME
  have hdiff : ∀ j, 1 ≤ j → ‖H.coeff j - G.coeff j‖ ≤ ‖(l : ℂ_[l])‖ :=
    GlobalTheory.T.norm_taylor_coeff_sub_coeff_le_norm_l l E a W ha hW
  have hρj : ∀ j, 1 ≤ j → ρ ^ j < 1 := fun j hj => pow_lt_one₀ hρ0.le hρ1 (by omega)
  have hdiffsmall : ∀ j, 1 ≤ j → ‖H.coeff j - G.coeff j‖ * ρ ^ j < ‖(l : ℂ_[l])‖ := by
    intro j hj
    calc ‖H.coeff j - G.coeff j‖ * ρ ^ j ≤ ‖(l : ℂ_[l])‖ * ρ ^ j :=
          mul_le_mul_of_nonneg_right (hdiff j hj) (by positivity)
      _ < ‖(l : ℂ_[l])‖ := mul_lt_of_lt_one_right hlpos (hρj j hj)
  have hHd : ‖H.coeff (l ^ M)‖ * ρ ^ l ^ M = ‖(l : ℂ_[l])‖ := by
    have hlt : ‖H.coeff (l ^ M) - G.coeff (l ^ M)‖ < ‖G.coeff (l ^ M)‖ := by
      have h1 : ‖H.coeff (l ^ M) - G.coeff (l ^ M)‖ * ρ ^ l ^ M
          < ‖G.coeff (l ^ M)‖ * ρ ^ l ^ M := by
        rw [hGd, hM]; have h0 := hdiffsmall _ hd1; rwa [hGd] at h0
      exact lt_of_mul_lt_mul_right h1 (by positivity)
    have h2 : H.coeff (l ^ M) = G.coeff (l ^ M) + (H.coeff (l ^ M) - G.coeff (l ^ M)) := by ring
    rw [h2, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le, hGd, hM]
  have hHd0 : H.coeff (l ^ M) ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_mul] at hHd
    exact hlpos.ne hHd
  have hbig : ∀ j, l ^ M < j → ‖H.coeff j‖ * ρ ^ j < ‖H.coeff (l ^ M)‖ * ρ ^ l ^ M := by
    intro j hj
    rw [hHd]
    have h2 : H.coeff j = G.coeff j + (H.coeff j - G.coeff j) := by ring
    have h3 := IsUltrametricDist.norm_add_le_max (G.coeff j) (H.coeff j - G.coeff j)
    rw [← h2] at h3
    have hρ : 0 ≤ ρ ^ j := by positivity
    calc ‖H.coeff j‖ * ρ ^ j ≤ max ‖G.coeff j‖ ‖H.coeff j - G.coeff j‖ * ρ ^ j :=
          mul_le_mul_of_nonneg_right h3 hρ
      _ = max (‖G.coeff j‖ * ρ ^ j) (‖H.coeff j - G.coeff j‖ * ρ ^ j) := max_mul_of_nonneg _ _ hρ
      _ < ‖(l : ℂ_[l])‖ := max_lt (coeff_sum_monomial_small l E M a ρ hρ0 hgt j hj)
          (hdiffsmall j (by omega))
  exact (GlobalTheory.T.card_roots_closedBall_bounds_ultrametric ℂ_[l] H ρ (l ^ M) hρ0 hHd0).2 hbig

end GlobalTheory
end

section

open scoped NNReal

namespace GlobalTheory.PointsKey

def oneSubMul {R : Type} [CommRing R] (u : R) : Submonoid R where
  carrier := {x | ∃ r, x = 1 - u * r}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b - u * a * b, by ring⟩
  one_mem' := ⟨0, by simp⟩

theorem dvd_of_one_sub_mul {R : Type} [CommRing R] (u r D a : R) (m : ℕ)
    (h : (1 - u * r) * D = u ^ m * a) : u ^ m ∣ D := by
  have hg : (1 - u * r) * (∑ i ∈ Finset.range m, (u * r) ^ i) = 1 - (u * r) ^ m := by
    rw [mul_comm, geom_sum_mul_neg]
  refine ⟨a * ∑ i ∈ Finset.range m, (u * r) ^ i + r ^ m * D, ?_⟩
  calc D = (1 - (u * r) ^ m) * D + (u * r) ^ m * D := by ring
    _ = (∑ i ∈ Finset.range m, (u * r) ^ i) * ((1 - u * r) * D) + (u * r) ^ m * D := by
        rw [← hg]; ring
    _ = _ := by rw [h]; ring

theorem key : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R), ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R) (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) → (∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : R →+* O), f u ≠ 0 → ¬ IsUnit (f u) → IsAdicComplete (Ideal.span {f u}) O → ∀ j, f (D j) = 0) → ∀ (m : ℕ) j, u ^ m ∣ D j := by
  intro l _ R _ u hl hu κ _ D c h heq hpts m j
  set S := oneSubMul u with hS
  let R' := Localization S
  let φ : R →+* R' := algebraMap R R'
  have hl' : ((l : ℕ) : R') = 0 := by rw [← map_natCast φ, hl, map_zero]
  have hu' : φ u ∈ nonZeroDivisors R' := by
    rw [mem_nonZeroDivisors_iff_right]
    intro x hx
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S x
    have hx' : φ u * IsLocalization.mk' R' a s = 0 := by rw [mul_comm]; exact hx
    rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_zero_iff] at hx'
    obtain ⟨t, ht⟩ := hx'
    have hta : (t : R) * a = 0 := by
      rw [mem_nonZeroDivisors_iff_right] at hu
      exact hu _ (by rw [← ht]; ring)
    exact (IsLocalization.mk'_eq_zero_iff a s).2 ⟨t, hta⟩
  have hunit : ∀ r', IsUnit (1 - φ u * r') := by
    intro r'
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S r'
    obtain ⟨b, hb⟩ := s.2
    have hmem : (s : R) - u * a ∈ S := ⟨b + a, by rw [hb]; ring⟩
    have hsp := IsLocalization.mk'_spec R' a s
    have : (1 - φ u * IsLocalization.mk' R' a s) * φ s = φ ((s : R) - u * a) := by
      rw [map_sub, map_mul, sub_mul, one_mul, mul_assoc, hsp]
    exact isUnit_of_mul_isUnit_left (this ▸ IsLocalization.map_units R' ⟨_, hmem⟩)
  have heq' : ∀ j, φ u ^ h * φ (D j) = ∑ i, φ (D i) ^ l * φ (c i j) := by
    intro j; simpa [map_sum, map_mul, map_pow] using congrArg φ (heq j)
  have hpts' : ∀ j, ∀ (O : Type) [CommRing O] [IsDomain O] [ValuationRing O] [CharP O l] [PerfectRing O l] (f : R' →+* O), f (φ u) ≠ 0 → ¬ IsUnit (f (φ u)) → IsAdicComplete (Ideal.span {f (φ u)}) O → f (φ (D j)) = 0 := by
    intro j O _ _ _ _ _ f h1 h2 h3
    exact hpts O (f.comp φ) h1 h2 h3 j
  have hb : ∀ j (M : ℕ), ∃ c : ℕ, ∀ n : ℕ, φ u ^ (M * n) ∣ φ u ^ c * φ (D j) ^ n := fun j M =>
    GlobalTheory.T.pow_dvd_of_vanishing_at_perfect_valuation_points l R' (φ u) (φ (D j)) hl' hu' hunit (hpts' j) M
  obtain ⟨y, hy⟩ := GlobalTheory.T.frobeniusPowEquation_dvd_all_pow l R' (φ u) hl' hu' κ (fun i => φ (D i)) (fun i j => φ (c i j)) h heq' hb m j
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S y
  have h2 : φ (D j * s) = φ (u ^ m * a) := by
    rw [map_mul, hy, map_mul, map_pow, mul_assoc, IsLocalization.mk'_spec]
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists S R').1 h2
  obtain ⟨r, hr⟩ := (t * s).2
  refine dvd_of_one_sub_mul u r (D j) (t * a) m ?_
  rw [← hr]
  simp only [Submonoid.coe_mul]
  linear_combination ht

end GlobalTheory.PointsKey
end

section

open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.FinPlaceApproxPos

theorem exists_approx_totally_positive (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) (t : HeightOneSpectrum (𝓞 F) → F) (M : ℕ) :
    ∃ a : F, (∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ))) ∧
      ∀ φ : F →+* ℝ, 0 < φ a := by
  classical
  obtain ⟨a₀, ha₀⟩ := GlobalTheory.FinPlaceApprox.approx_target F T t M
  set J : Ideal (𝓞 F) := ∏ v ∈ T, v.asIdeal ^ M with hJ
  have hJ0 : J ≠ ⊥ := by
    rw [hJ, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro v _
    exact pow_ne_zero _ v.ne_bot
  set d : ℕ := Ideal.absNorm J with hd
  have hd0 : d ≠ 0 := by
    rw [hd]; exact fun h => hJ0 (Ideal.absNorm_eq_zero_iff.1 h)
  have hdJ : ((d : ℤ) : 𝓞 F) ∈ J := by
    simpa [hd] using Ideal.absNorm_mem J
  have hJv : ∀ v ∈ T, J ≤ v.asIdeal ^ M := fun v hv =>
    Ideal.prod_le_inf.trans (Finset.inf_le hv)
  obtain ⟨B, hB⟩ := (Set.finite_range (fun φ : F →+* ℝ => |φ a₀|)).bddAbove
  set N : ℕ := ⌈B⌉₊ + 1 with hN
  refine ⟨a₀ + (N * d : ℕ), fun v hv => ?_, fun φ => ?_⟩
  · have hmem : ((N * d : ℕ) : 𝓞 F) ∈ v.asIdeal ^ M := by
      apply hJv v hv
      have : ((N * d : ℕ) : 𝓞 F) = (N : 𝓞 F) * ((d : ℤ) : 𝓞 F) := by push_cast; ring
      rw [this]; exact Ideal.mul_mem_left _ _ hdJ
    have hval : v.valuation F ((N * d : ℕ) : F) ≤ WithZero.exp (-(M : ℤ)) := by
      have : ((N * d : ℕ) : F) = algebraMap (𝓞 F) F ((N * d : ℕ) : 𝓞 F) := by simp
      rw [this, HeightOneSpectrum.valuation_of_algebraMap]
      exact (v.intValuation_le_pow_iff_mem _ _).2 hmem
    have : a₀ + ((N * d : ℕ) : F) - t v = (a₀ - t v) + ((N * d : ℕ) : F) := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans (max_le (ha₀ v hv) hval)
  · have h1 : φ a₀ ≥ -B := by
      have := hB ⟨φ, rfl⟩
      have := neg_abs_le (φ a₀)
      simp only at *
      linarith
    have hdpos : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hd0
    have hNB : B < N := by
      rw [hN]; push_cast
      exact lt_of_le_of_lt (Nat.le_ceil B) (by linarith)
    have hN0 : (0 : ℝ) ≤ N := by positivity
    rw [map_add (f := _), map_natCast]
    push_cast
    nlinarith

theorem approxpos_target : ∀ (F : Type) [Field F] [NumberField F]
    (T : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)))
    (t : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → F) (M : ℕ),
    ∃ a : F, (∀ v ∈ T, v.valuation F (a - t v) ≤ WithZero.exp (-(M : ℤ))) ∧ ∀ φ : F →+* ℝ, 0 < φ a :=
  fun F _ _ T t M => exists_approx_totally_positive F T t M

end GlobalTheory.FinPlaceApproxPos
end
end

section

open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

theorem _root_.GlobalTheory.T.exists_finiteExtension_entries_of_compact_rep : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l)), Continuous r → ∃ L : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] L ∧ ∀ g i j, ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) i j ∈ L := by
  first | exact @GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem_of_continuous | exact GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem_of_continuous | (intros; apply GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem_of_continuous <;> assumption)
end

section

open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal GlobalTheory.LocDualInt
open Formalism.NG (KO)

theorem _root_.GlobalTheory.T.exists_padicInt_ringHom_congr_toZModPow : ∀ {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O], IsTopologicalRing O → CompactSpace O → T2Space O → IsAdic (IsLocalRing.maximalIdeal O) → (p : O) ∈ IsLocalRing.maximalIdeal O → ∃ ι : ℤ_[p] →+* O, ∀ (x : ℤ_[p]) (k : ℕ), ι x - ((PadicInt.toZModPow k x).val : O) ∈ Ideal.span {(p : O) ^ k} := by
  first | exact @GlobalTheory.ZpHomAdic.zp_ringHom | exact GlobalTheory.ZpHomAdic.zp_ringHom | (intros; apply GlobalTheory.ZpHomAdic.zp_ringHom <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

theorem _root_.GlobalTheory.T.powerSeries_eq_C_of_subst_fixed_not_root_of_unity : ∀ (L : Type) [Field L] (y : PowerSeries L), PowerSeries.constantCoeff y = 0 → (∀ k : ℕ, 0 < k → (PowerSeries.coeff 1 y) ^ k ≠ 1) → ∀ a : PowerSeries L, (PowerSeries.subst y a : PowerSeries L) = a → a = PowerSeries.C (PowerSeries.constantCoeff a) := by
  first | exact @GlobalTheory.powerSeries_eq_C_of_subst_eq_self | exact GlobalTheory.powerSeries_eq_C_of_subst_eq_self | (intros; apply GlobalTheory.powerSeries_eq_C_of_subst_eq_self <;> assumption)
end

section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField

theorem _root_.GlobalTheory.T.cyclotomicChar_inertia_surjective : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ v : ℤ_[l]ˣ, ∃ σ ∈ Ine (F := ℚ) A, cycZ (F := ℚ) (Ω := Ω) l σ = v := by
  first | exact @GlobalTheory.CycInertia.cycZ_Ine_surjective | exact GlobalTheory.CycInertia.cycZ_Ine_surjective | (intros; apply GlobalTheory.CycInertia.cycZ_Ine_surjective <;> assumption)
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.DualSide

section Anti

variable {R : Type*} [CommRing R] {G : Type*} [Group G] [TopologicalSpace G]
  {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
  {M' : Type*} [AddCommGroup M'] [Module R M'] [TopologicalSpace M']
  [IsTopologicalAddGroup M'] [ContinuousConstSMul R M']
  {P : Type*} [AddCommGroup P] [Module R P] [TopologicalSpace P]
  [IsTopologicalAddGroup P] [ContinuousConstSMul R P]

end Anti

section Dual

variable {R : Type*} [CommRing R] {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module R M]

theorem finite_TDual [Finite R] [Finite M] : Finite (TDual R M) :=
  Finite.of_injective _ (DFunLike.coe_injective (F := TDual R M))

variable [TopologicalSpace R] [DiscreteTopology R] [TopologicalSpace M] [DiscreteTopology M]

theorem contAction_twDual [TopologicalSpace Γ] [ContinuousInv Γ] [Finite M] {χ : Γ →* Rˣ}
    {rho : Representation R Γ M} (hχ : ContAction (charRep χ)) (h : ContAction rho) :
    ContAction (twDual χ rho) := by
  have h1 : Continuous fun (p : Γ × TDual R M) (m : M) => twDual χ rho p.1 p.2 m :=
    continuous_pi fun m => hχ.comp (continuous_fst.prodMk
      ((continuous_of_discreteTopology (f := fun q : TDual R M × M => q.1 q.2)).comp
        (continuous_snd.prodMk (h.comp (continuous_fst.inv.prodMk continuous_const)))))
  exact (IsLocallyConstant.desc _ (fun (φ : TDual R M) (m : M) => φ m)
    ((IsLocallyConstant.iff_continuous _).2 h1) DFunLike.coe_injective).continuous

variable {D : Type*} [Group D] [TopologicalSpace D]

end Dual

section Global

open GlobalTheory.Published GlobalTheory.Published.PoitouTate

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {l : ℕ} [Fact l.Prime] {r : ℕ} {S : Finset (HeightOneSpectrum (𝓞 F))}
  {Av : S → ValuationSubring Ω}
  {μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ}
  {j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)}
  {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M]
  [DiscreteTopology M]
  {ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M}

omit [TopologicalSpace M] [DiscreteTopology M] in
theorem finite_TDual_pow : Finite (TDual (ZMod (l ^ r)) M) :=
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  finite_TDual

end Global


end GlobalTheory.DualSide
end
end
