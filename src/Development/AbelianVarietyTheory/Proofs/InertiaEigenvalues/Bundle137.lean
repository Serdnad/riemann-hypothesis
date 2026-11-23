module

public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.WittVector.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle113
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle115
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle117
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.RingTheory.WittVector.Frobenius
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle118
public import ReciprocityTheory.GaloisValuations.Global
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
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

theorem _root_.GlobalTheory.T.exists_conj_valuationSubring_of_same_below : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] (A B : ValuationSubring Ω), (∀ x ∈ K, IsIntegral ℤ x → (A.valuation x < 1 ↔ B.valuation x < 1)) → ∃ ρ : G E Ω, (∀ x ∈ K, ρ x = x) ∧ ρ • A = B := by
  first | exact @GlobalTheory.conj_places_of_same_prime_below | exact GlobalTheory.conj_places_of_same_prime_below | (intros; apply GlobalTheory.conj_places_of_same_prime_below <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

theorem _root_.GlobalTheory.T.exists_integral_near_one_small_off_decomposition : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] (A : ValuationSubring Ω) (c : ℕ), c ≠ 0 → ∃ t ∈ K, IsIntegral ℤ t ∧ A.valuation (t - 1) ≤ A.valuation (c : Ω) ∧ ∀ σ : G E Ω, (∃ x ∈ K, IsIntegral ℤ x ∧ ¬(A.valuation (σ x) < 1 ↔ A.valuation x < 1)) → A.valuation (σ t) ≤ A.valuation (c : Ω) := by
  first | exact @GlobalTheory.crt_approx_integral | exact GlobalTheory.crt_approx_integral | (intros; apply GlobalTheory.crt_approx_integral <;> assumption)
end

section

open Polynomial
open Classical

theorem _root_.GlobalTheory.T.card_roots_closedBall_dominant_coeff : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ), 0 < ρ → f ≠ 0 → (∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧ ∀ j, Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) := by
  first | exact @GlobalTheory.card_roots_closedBall_eq_dominantIndex | exact GlobalTheory.card_roots_closedBall_eq_dominantIndex | (intros; apply GlobalTheory.card_roots_closedBall_eq_dominantIndex <;> assumption)
end

section

namespace GlobalTheory

namespace WittGaussMul

theorem exists_lt_bound (f : ℕ → ℝ) (B : ℝ) (hB : 0 < B) (i : ℕ) (h : ∀ k < i, f k < B) :
    ∃ c, 0 ≤ c ∧ c < B ∧ ∀ k < i, f k ≤ c := by
  induction i with
  | zero => exact ⟨0, le_rfl, hB, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ i ih =>
    obtain ⟨c, hc0, hcB, hc⟩ := ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
    refine ⟨max c (f i), le_max_of_le_left hc0, max_lt hcB (h i (Nat.lt_succ_self i)), ?_⟩
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact le_max_of_le_left (hc k hk)
    · exact le_max_right _ _

theorem exists_first_max (f : ℕ → ℝ) (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1)
    (hf : ∀ n, f n ≤ r ^ n) (hpos : 0 < ⨆ n, f n) :
    ∃ i, f i = (⨆ n, f n) ∧ ∀ k < i, f k < ⨆ n, f n := by
  classical
  have hb : BddAbove (Set.range f) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (hf n).trans (pow_le_one₀ hr0.le hr1.le)⟩
  have hle : ∀ n, f n ≤ ⨆ n, f n := fun n => le_ciSup hb n
  have hex : ∃ i, f i = ⨆ n, f n := by
    by_contra hne
    push Not at hne
    obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one hpos hr1
    obtain ⟨c, -, hcB, hc⟩ := exists_lt_bound f _ hpos M
      (fun k _ => lt_of_le_of_ne (hle k) (hne k))
    have : (⨆ n, f n) ≤ max c (r ^ M) := by
      refine ciSup_le fun n => ?_
      rcases lt_or_ge n M with h | h
      · exact le_max_of_le_left (hc n h)
      · exact le_max_of_le_right ((hf n).trans (pow_le_pow_of_le_one hr0.le hr1.le h))
    exact absurd (max_lt hcB hM) (not_lt.mpr this)
  exact ⟨Nat.find hex, Nat.find_spec hex,
    fun k hk => lt_of_le_of_ne (hle k) (Nat.find_min hex hk)⟩

end WittGaussMul


open WittGaussMul in
theorem witt_gaussNorm_mul : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (a : R → ℝ), (∀ x, 0 ≤ a x ∧ a x ≤ 1) → a 0 = 0 → a 1 = 1 → (∀ x y, a (x * y) = a x * a y) → (∀ x y, a (x + y) ≤ max (a x) (a y)) → ∀ r : ℝ, 0 < r → r < 1 → ∀ N : WittVector l R → ℝ, (∀ x, N x = ⨆ n : ℕ, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ x y, N (x * y) = N x * N y := by
  intro l hl R _ _ _ a h01 h0 h1 hmul hadd r hr0 hr1 N hN x y
  obtain ⟨Nadd, Nneg, Nmul⟩ := GlobalTheory.T.witt_vector_gauss_norm_ultrametric l R a h01 h0 h1 hmul hadd r hr0 hr1 N hN
  set T : WittVector l R → ℕ → ℝ := fun x n => a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n
    with hT
  have hN' : ∀ x, N x = ⨆ n, T x n := hN
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hexp : ∀ n : ℕ, (0 : ℝ) < 1 / (l : ℝ) ^ n := fun n => by positivity
  have hT0 : ∀ x n, 0 ≤ T x n := fun x n =>
    mul_nonneg (Real.rpow_nonneg (h01 _).1 _) (pow_pos hr0 n).le
  have hTr : ∀ x n, T x n ≤ r ^ n := fun x n =>
    mul_le_of_le_one_left (pow_pos hr0 n).le
      (Real.rpow_le_one (h01 _).1 (h01 _).2 (hexp n).le)
  have hTN : ∀ x n, T x n ≤ N x := fun x n => by
    rw [hN']
    exact le_ciSup (f := T x)
      ⟨1, by rintro _ ⟨n, rfl⟩; exact (hTr x n).trans (pow_le_one₀ hr0.le hr1.le)⟩ n
  have hN0 : ∀ x, 0 ≤ N x := fun x => (hT0 x 0).trans (hTN x 0)
  have hTz : ∀ x n, x.coeff n = 0 → T x n = 0 := fun x n h => by
    simp only [hT, h, h0, Real.zero_rpow (hexp n).ne', zero_mul]
  have hpow : ∀ w (n : ℕ), a (w ^ n) = a w ^ n := fun w n => by
    induction n with
    | zero => simpa using h1
    | succ n ih => rw [pow_succ, hmul, ih, pow_succ]
  have hTp : ∀ (u : WittVector l R) (n : ℕ), T (u * (l : WittVector l R) ^ n) n
      = a (u.coeff 0) * r ^ n := fun u n => by
    have h := WittVector.mul_pow_charP_coeff_succ u (m := 0) (n := n)
    rw [zero_add] at h
    simp only [hT, h, hpow]
    congr 1
    have := Real.pow_rpow_inv_natCast (h01 (u.coeff 0)).1 (pow_pos hl.out.pos n).ne'
    simpa using this
  have key : ∀ x, 0 < N x → ∃ (i : ℕ) (x0 u : WittVector l R),
      x = x0 + u * (l : WittVector l R) ^ i ∧ N x0 < N x ∧
      N (u * (l : WittVector l R) ^ i) ≤ N x ∧ a (u.coeff 0) * r ^ i = N x := by
    intro x hx
    obtain ⟨i, hi, hlt⟩ := exists_first_max (T x) r hr0 hr1 (hTr x) (by rw [← hN']; exact hx)
    rw [← hN'] at hi hlt
    have hmem : WittVector.tail i x ∈ Ideal.span {((l : WittVector l R) ^ i)} := by
      rw [WittVector.mem_span_p_pow_iff_le_coeff_eq_zero]
      intro m hm
      simp [WittVector.tail, WittVector.select, WittVector.coeff_mk, not_le.mpr hm]
    obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨i, WittVector.init i x, u, ?_, ?_, ?_, ?_⟩
    · rw [hu, WittVector.init_add_tail]
    · obtain ⟨c, hc0, hcB, hc⟩ := exists_lt_bound (T x) _ hx i hlt
      refine lt_of_le_of_lt ?_ hcB
      rw [hN']
      refine ciSup_le fun n => ?_
      rcases lt_or_ge n i with h | h
      · have : (WittVector.init i x).coeff n = x.coeff n := by
          simp [WittVector.init, WittVector.select, WittVector.coeff_mk, h]
        have h2 : T (WittVector.init i x) n = T x n := by simp only [hT, this]
        rw [h2]; exact hc n h
      · rw [hTz]
        · exact hc0
        · simp [WittVector.init, WittVector.select, WittVector.coeff_mk, not_lt.mpr h]
    · rw [hu, hN' (WittVector.tail i x)]
      refine ciSup_le fun n => ?_
      rcases lt_or_ge n i with h | h
      · rw [hTz]
        · exact hN0 x
        · simp [WittVector.tail, WittVector.select, WittVector.coeff_mk, not_le.mpr h]
      · have : (WittVector.tail i x).coeff n = x.coeff n := by
          simp [WittVector.tail, WittVector.select, WittVector.coeff_mk, h]
        have h2 : T (WittVector.tail i x) n = T x n := by simp only [hT, this]
        rw [h2]; exact hTN x n
    · rw [← hTp, hu, ← hi]
      have : (WittVector.tail i x).coeff i = x.coeff i := by
        simp [WittVector.tail, WittVector.select, WittVector.coeff_mk]
      simp only [hT, this]
  refine le_antisymm (Nmul x y) ?_
  rcases (hN0 x).eq_or_lt with hx | hx
  · rw [← hx, zero_mul]; exact hN0 _
  rcases (hN0 y).eq_or_lt with hy | hy
  · rw [← hy, mul_zero]; exact hN0 _
  obtain ⟨i, x0, u, hxe, hx0, hu, hui⟩ := key x hx
  obtain ⟨j, y0, v, hye, hy0, hv, hvj⟩ := key y hy
  have hmain : N x * N y ≤ N ((u * v) * (l : WittVector l R) ^ (i + j)) := by
    refine le_trans (le_of_eq ?_) (hTN _ (i + j))
    rw [hTp, WittVector.mul_coeff_zero, hmul, ← hui, ← hvj]
    ring
  have hrest : N (x0 * y + (u * (l : WittVector l R) ^ i) * y0) < N x * N y := by
    refine lt_of_le_of_lt (Nadd _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt (Nmul _ _) (mul_lt_mul_of_pos_right hx0 hy)
    · refine lt_of_le_of_lt (Nmul _ _) ?_
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hu (hN0 _)) (mul_lt_mul_of_pos_left hy0 hx)
  have heq : (u * v) * (l : WittVector l R) ^ (i + j)
      = x * y + -(x0 * y + (u * (l : WittVector l R) ^ i) * y0) := by
    have : x * y = x0 * y + (u * (l : WittVector l R) ^ i) * (y0 + v * (l : WittVector l R) ^ j) := by
      rw [← hye, ← add_mul, ← hxe]
    rw [this]; ring
  have h3 := Nadd (x * y) (-(x0 * y + (u * (l : WittVector l R) ^ i) * y0))
  rw [← heq, Nneg] at h3
  rcases le_max_iff.mp (hmain.trans h3) with h | h
  · exact h
  · exact absurd hrest (not_lt.mpr h)

end GlobalTheory
end

section

open Polynomial

theorem _root_.GlobalTheory.T.algebraEtale_of_separable_charpoly_mulLeft : ∀ (E A : Type) [Field E] [CommRing A] [Algebra E A] [Module.Finite E A] (g : A), (LinearMap.mulLeft E g).charpoly.Separable → Algebra.Etale E A := by
  first | exact @GlobalTheory.etale_of_separable_charpoly_mulLeft | exact GlobalTheory.etale_of_separable_charpoly_mulLeft | (intros; apply GlobalTheory.etale_of_separable_charpoly_mulLeft <;> assumption)
end

section

open ReciprocityTheory.Gal Pointwise NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.exists_frob_at_valuationSubring_over_prime : ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime] (A : ValuationSubring Ω), A.valuation (p : Ω) < 1 → ∃ σ : Ω ≃ₐ[F] Ω, σ • A = A ∧ ∃ q : ℕ, q ≠ 1 ∧ ∀ x : Ω, A.valuation x ≤ 1 → A.valuation (σ x - x ^ q) < 1 := by
  first | exact @GlobalTheory.exists_frob_at_place_over_prime | exact GlobalTheory.exists_frob_at_place_over_prime | (intros; apply GlobalTheory.exists_frob_at_place_over_prime <;> assumption)
end

section

open scoped NNReal

theorem _root_.GlobalTheory.T.exists_frobenius_compatible_wittVector_lift : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (φ : A →+* A), (∀ a, ((l : ℕ) : A) ∣ φ a - a ^ l) → (∀ a : A, ((l : ℕ) : A) * a = 0 → a = 0) → ∀ (O : Type) [CommRing O] [CharP O l] (f : A →+* O), ∃ F : A →+* WittVector l O, (∀ a, (F a).coeff 0 = f a) ∧ ∀ a, F (φ a) = WittVector.frobenius (F a) := by
  first | exact @GlobalTheory.DworkLift.exists_frobenius_compatible_lift | exact GlobalTheory.DworkLift.exists_frobenius_compatible_lift | (intros; apply GlobalTheory.DworkLift.exists_frobenius_compatible_lift <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.InertiaAlmostAll

theorem val_le_one_of_isIntegral {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {w : Ω}
    (hw : IsIntegral ℤ w) : B.valuation w ≤ 1 := by
  have h : IsIntegral B w := hw.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  rw [B.valuation_le_one_iff, ← hy]
  exact y.2

theorem exists_int_mul (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (y : Ω) : ∃ c : ℤ, c ≠ 0 ∧ IsIntegral ℤ ((c : Ω) * y) := by
  haveI : Algebra.IsAlgebraic ℤ F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := F)).mpr inferInstance
  haveI : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ F Ω
  obtain ⟨c, hc, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) y).exists_integral_multiple
  exact ⟨c, hc, by simpa [zsmul_eq_mul] using h⟩

theorem finite_mem (F : Type) [Field F] [NumberField F] {c : ℤ} (hc : c ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | (c : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h : Ideal.span {(c : 𝓞 F)} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hc
  refine (Ideal.finite_factors h).subset fun v hv => ?_
  simpa [Ideal.dvd_span_singleton] using hv

theorem finite_moves (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (x : Ω) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧
      ∃ τ ∈ Ine (F := F) B, τ x ≠ x}.Finite := by
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨c₀, hc₀, hx⟩ := exists_int_mul F x
  set a : Ω := (c₀ : Ω) * x with ha
  choose c hc hci using fun β : Ω => exists_int_mul F (β - a)⁻¹
  have hfin : ((minpoly F a).rootSet Ω).Finite := Polynomial.rootSet_finite _ _
  refine (hfin.biUnion (t := fun β => {v : HeightOneSpectrum (𝓞 F) | (c β : 𝓞 F) ∈ v.asIdeal})
    fun β _ => finite_mem F (hc β)).subset ?_
  rintro v ⟨B, hB, τ, hτ, hne⟩
  have hne' : τ a - a ≠ 0 := by
    rw [ha, map_mul, map_intCast, ← mul_sub]
    exact mul_ne_zero (by exact_mod_cast hc₀) (sub_ne_zero.mpr hne)
  have hint : IsIntegral F a := Algebra.IsIntegral.isIntegral a
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  refine ⟨τ a, ?_, ?_⟩
  · rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  · rw [← hB]
    have h1 := hτ.2 a (val_le_one_of_isIntegral B hx)
    have h2 := val_le_one_of_isIntegral B (hci (τ a))
    have e : algebraMap F Ω (((c (τ a) : ℤ) : 𝓞 F) : F)
        = ((c (τ a) : Ω) * (τ a - a)⁻¹) * (τ a - a) := by
      rw [inv_mul_cancel_right₀ hne']
      simp
    rw [e, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right h2 zero_le h1

theorem finite_ramified (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (L : IntermediateField F Ω) [FiniteDimensional F L] :
    {v : HeightOneSpectrum (𝓞 F) | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧
      ¬ Ine (F := F) B ≤ L.fixingSubgroup}.Finite := by
  let b := Module.finBasis F L
  refine (Set.finite_iUnion fun i => finite_moves F Ω (b i : Ω)).subset ?_
  rintro v ⟨B, hB, hn⟩
  by_contra hv
  apply hn
  intro τ hτ
  have hb : ∀ i, τ (b i : Ω) = b i := by
    intro i
    by_contra h
    exact hv (Set.mem_iUnion.mpr ⟨i, B, hB, τ, hτ, h⟩)
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have : τ.toLinearMap.comp L.val.toLinearMap = L.val.toLinearMap :=
    b.ext fun i => by simpa using hb i
  simpa using LinearMap.congr_fun this ⟨y, hy⟩

end GlobalTheory.InertiaAlmostAll
end
