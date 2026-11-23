module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Algebra.Spectrum.Basic

@[expose] public section

section

open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise

namespace GlobalTheory

theorem measure_univ_le_two_mul_sublevel_of_drift :
    (∀ (Y σ : Type) [MeasurableSpace Y] [Fintype σ] [Nonempty σ] (μ : Measure Y)
      (R : Y → Y → Prop) (t : σ → Y → Y) (f : Y → ℝ) (c b : ℝ), (∀ s, Measurable (t s)) →
      (∀ s y y', R y y' → R (t s y) (t s y')) →
      (∀ φ : Y → ℝ≥0∞, Measurable φ → (∀ y y', R y y' → φ y = φ y') →
        ∀ s, ∫⁻ y, φ (t s y) ∂μ = ∫⁻ y, φ y ∂μ) →
      Measurable f → (∀ y, 0 ≤ f y) → (∀ y y', R y y' → f y = f y') → 0 ≤ c → c < 1 → 0 ≤ b →
      (∀ y, ∑ s, f (t s y) ≤ Fintype.card σ * (c * f y + b)) →
      ∃ M : ℝ, μ Set.univ ≤ 2 * μ {y | f y ≤ M}) := by
  intro Y σ _ _ _ μ R t f c b ht hR hinv hf hf0 hfR hc0 hc1 hb hdrift
  classical
  have h1c : 0 < 1 - c := by linarith
  obtain ⟨K, hK, hK0⟩ : ∃ K : ℝ, b = K * (1 - c) ∧ 0 ≤ K :=
    ⟨b / (1 - c), by field_simp, div_nonneg hb h1c.le⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 * K + 1 := ⟨_, rfl⟩
  have hM0 : 0 < M := by rw [hM]; linarith
  refine ⟨M, ?_⟩
  have hN : (0 : ℝ) < Fintype.card σ := by exact_mod_cast Fintype.card_pos
  have hA : MeasurableSet {y | f y ≤ M} := measurableSet_le hf measurable_const
  let g : ℕ → Y → ℝ := fun n =>
    Nat.rec (fun y => if f y ≤ M then 1 else 0)
      (fun _ h y => (Fintype.card σ : ℝ)⁻¹ * ∑ s, h (t s y)) n
  have g0 : ∀ y, g 0 y = if f y ≤ M then 1 else 0 := fun y => rfl
  have gs : ∀ n y, g (n + 1) y = (Fintype.card σ : ℝ)⁻¹ * ∑ s, g n (t s y) := fun n y => rfl
  clear_value g
  have gmeas : ∀ n, Measurable (g n) := by
    intro n
    induction n with
    | zero =>
      rw [show g 0 = _ from funext g0]
      exact Measurable.ite hA measurable_const measurable_const
    | succ n ih =>
      rw [show g (n + 1) = _ from funext (gs n)]
      exact measurable_const.mul (Finset.measurable_sum _ fun s _ => ih.comp (ht s))
  have gnn : ∀ n y, 0 ≤ g n y := by
    intro n
    induction n with
    | zero => intro y; rw [g0]; split_ifs <;> norm_num
    | succ n ih =>
      intro y; rw [gs]
      exact mul_nonneg (inv_nonneg.2 hN.le) (Finset.sum_nonneg fun s _ => ih _)
  have gR : ∀ n y y', R y y' → g n y = g n y' := by
    intro n
    induction n with
    | zero => intro y y' h; rw [g0, g0, hfR y y' h]
    | succ n ih =>
      intro y y' h; rw [gs, gs]
      congr 1
      exact Finset.sum_congr rfl fun s _ => ih _ _ (hR s _ _ h)
  have gint : ∀ n, ∫⁻ y, ENNReal.ofReal (g n y) ∂μ = μ {y | f y ≤ M} := by
    intro n
    induction n with
    | zero =>
      rw [← lintegral_indicator_one hA]
      refine lintegral_congr fun y => ?_
      rw [g0]
      by_cases h : f y ≤ M <;> simp [h, Set.indicator]
    | succ n ih =>
      have hm : Measurable fun y => ENNReal.ofReal (g n y) := (gmeas n).ennreal_ofReal
      have e : ∀ y, ENNReal.ofReal (g (n + 1) y) =
          (Fintype.card σ : ℝ≥0∞)⁻¹ * ∑ s, ENNReal.ofReal (g n (t s y)) := by
        intro y
        rw [gs, ENNReal.ofReal_mul (inv_nonneg.2 hN.le), ENNReal.ofReal_inv_of_pos hN,
          ENNReal.ofReal_natCast, ENNReal.ofReal_sum_of_nonneg fun s _ => gnn n _]
      simp_rw [e]
      have hN0 : (Fintype.card σ : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
      have hms : ∀ s, Measurable fun y => ENNReal.ofReal (g n (t s y)) :=
        fun s => hm.comp (ht s)
      rw [lintegral_const_mul _ (Finset.measurable_sum _ fun s _ => hms s),
        MeasureTheory.lintegral_finsetSum _ fun s _ => hms s]
      have : ∀ s, ∫⁻ y, ENNReal.ofReal (g n (t s y)) ∂μ = μ {y | f y ≤ M} := fun s => by
        rw [← ih]
        exact hinv (fun y => ENNReal.ofReal (g n y)) hm
          (fun y y' h => by simp only [gR n y y' h]) s
      simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, ENNReal.inv_mul_cancel hN0 (ENNReal.natCast_ne_top _), one_mul]
  have glow : ∀ n y, M - (c ^ n * f y + K * (1 - c ^ n)) ≤ M * g n y := by
    intro n
    induction n with
    | zero =>
      intro y; rw [g0]
      have := hf0 y
      split_ifs with h
      · simp [this]
      · simp only [pow_zero, one_mul, sub_self, mul_zero, add_zero]
        linarith [not_le.1 h]
    | succ n ih =>
      intro y
      have hcn : 0 ≤ c ^ n := pow_nonneg hc0 n
      have h1 : ∑ s, (M - (c ^ n * f (t s y) + K * (1 - c ^ n))) ≤ ∑ s, M * g n (t s y) :=
        Finset.sum_le_sum fun s _ => ih _
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        at h1
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
      have h2 := mul_le_mul_of_nonneg_left (hdrift y) hcn
      rw [gs, mul_left_comm, le_inv_mul_iff₀ hN, pow_succ]
      rw [hK] at h2
      rw [← Finset.mul_sum] at h1
      nlinarith
  have hlim : ∀ y, (2⁻¹ : ℝ≥0∞) ≤
      Filter.liminf (fun n => ENNReal.ofReal (g n y)) Filter.atTop := by
    intro y
    refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
    have h0 : Filter.Tendsto (fun n : ℕ => c ^ n * f y) Filter.atTop (𝓝 (0 * f y)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1).mul_const _
    rw [zero_mul] at h0
    filter_upwards [h0.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))] with n hn
    have h1 := glow n y
    have h2 : 0 ≤ K * c ^ n := mul_nonneg hK0 (pow_nonneg hc0 n)
    have h3 : M * 2⁻¹ ≤ M * g n y := by nlinarith
    have h4 : (2⁻¹ : ℝ) ≤ g n y := le_of_mul_le_mul_left h3 hM0
    have := ENNReal.ofReal_le_ofReal h4
    rwa [ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat] at this
  have hF : 2⁻¹ * μ Set.univ ≤ μ {y | f y ≤ M} := by
    rw [← lintegral_const]
    refine (lintegral_mono hlim).trans ?_
    refine (lintegral_liminf_le fun n => (gmeas n).ennreal_ofReal).trans ?_
    simp only [gint, Filter.liminf_const, le_refl]
  calc μ Set.univ = 2 * (2⁻¹ * μ Set.univ) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
    _ ≤ _ := by gcongr

end GlobalTheory
end

section

open NumberField

namespace GlobalTheory

open NumberField Polynomial Matrix in
private lemma charpoly_dvd_pow_card_of_aeval_eq_zero {K : Type} [Field K] {r : ℕ} [NeZero r]
    (N : Matrix (Fin r) (Fin r) K) (φ : K[X]) (h : aeval N φ = 0) : N.charpoly ∣ φ ^ r := by
  let Ω := AlgebraicClosure K
  rw [← Polynomial.map_dvd_map' (algebraMap K Ω), Polynomial.map_pow, ← Matrix.charpoly_map]
  set N' := N.map (algebraMap K Ω)
  have hs := IsAlgClosed.splits N'.charpoly
  have hroot : ∀ μ ∈ N'.charpoly.roots, (φ.map (algebraMap K Ω)).IsRoot μ := by
    intro μ hμ
    have h1 := Matrix.mem_spectrum_of_isRoot_charpoly
      ((Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).1 hμ)
    have h2 := spectrum.subset_polynomial_aeval N' (φ.map (algebraMap K Ω)) ⟨μ, h1, rfl⟩
    have h3 : aeval N' (φ.map (algebraMap K Ω)) = 0 := by
      rw [Polynomial.aeval_map_algebraMap]
      have := Polynomial.aeval_algHom_apply
        (AlgHom.mapMatrix (Algebra.ofId K Ω) : Matrix (Fin r) (Fin r) K →ₐ[K] _) N φ
      rw [h, map_zero] at this
      exact this
    rw [h3, spectrum.zero_eq] at h2
    exact h2
  have hcard : N'.charpoly.roots.card = r := by
    rw [← hs.natDegree_eq_card_roots, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  rw [hs.eq_prod_roots_of_monic (Matrix.charpoly_monic _)]
  calc (Multiset.map (fun x ↦ X - C x) N'.charpoly.roots).prod
      ∣ (Multiset.map (fun _ ↦ φ.map (algebraMap K Ω)) N'.charpoly.roots).prod :=
        Multiset.prod_dvd_prod_of_dvd _ _ fun μ hμ => Polynomial.dvd_iff_isRoot.2 (hroot μ hμ)
    _ = (φ.map (algebraMap K Ω)) ^ r := by
        rw [Multiset.map_const', Multiset.prod_replicate, hcard]


open NumberField Polynomial Matrix in
theorem _root_.GlobalTheory.trace_mem_prime_of_pow_mulVec_mem_smul : ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (L : Submodule (𝓞 K) (Fin r → K))
      (N : Matrix (Fin r) (Fin r) K) (P : Ideal (𝓞 K)) (n : ℕ), L.FG →
      Submodule.span K (L : Set (Fin r → K)) = ⊤ → P.IsPrime → (∀ x ∈ L, N.mulVec x ∈ L) →
      (∀ x ∈ L, (N ^ n).mulVec x ∈ P • L) → ∃ z ∈ P, ((z : 𝓞 K) : K) = N.trace := by
  intro K _ _ r L N P n hL hspan hP hN hNn
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨0, P.zero_mem, by simp [Matrix.trace]⟩
  haveI : NeZero r := ⟨hr.ne'⟩
  set m := n + 1 with hm
  have hNm : ∀ x ∈ L, (N ^ m) *ᵥ x ∈ P • L := fun x hx => by
    rw [hm, pow_succ, ← Matrix.mulVec_mulVec]
    exact hNn _ (hN x hx)
  have hLm : ∀ x ∈ L, (N ^ m) *ᵥ x ∈ L := fun x hx => Submodule.smul_le_right (hNm x hx)
  haveI : Module.Finite (𝓞 K) L := Module.Finite.iff_fg.mpr hL
  let f : Module.End (𝓞 K) L :=
    ((Matrix.toLin' (N ^ m)).restrictScalars (𝓞 K)).restrict (fun x hx => by
      show Matrix.toLin' (N ^ m) x ∈ L
      rw [Matrix.toLin'_apply]
      exact hLm x hx)
  have hf : ∀ y : L, ((f y : L) : Fin r → K) = (N ^ m) *ᵥ (y : Fin r → K) := fun y => by
    show Matrix.toLin' (N ^ m) (y : Fin r → K) = _
    exact Matrix.toLin'_apply _ _
  have hpow : ∀ (i : ℕ) (y : L), (((f ^ i) y : L) : Fin r → K) = ((N ^ m) ^ i) *ᵥ (y : Fin r → K) := by
    intro i
    induction i with
    | zero => intro y; simp
    | succ i ih => intro y; rw [pow_succ', Module.End.mul_apply, hf, ih, Matrix.mulVec_mulVec, ← pow_succ']
  have hrange : LinearMap.range f ≤ P • ⊤ := by
    rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_smul_top_iff, hf]
    exact hNm _ y.2
  obtain ⟨q, hqm, -, hqc, hq0⟩ := LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero (𝓞 K) f P hrange
  have hzero : aeval (N ^ m) q = 0 := by
    have hon : ∀ x ∈ L, (aeval (N ^ m) q) *ᵥ x = 0 := by
      intro x hx
      have := congrArg (fun g : Module.End (𝓞 K) L => ((g ⟨x, hx⟩ : L) : Fin r → K)) hq0
      simp only [Polynomial.aeval_eq_sum_range, LinearMap.sum_apply,
        Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul, hpow, LinearMap.zero_apply,
        Submodule.coe_zero] at this
      rw [Polynomial.aeval_eq_sum_range, Matrix.sum_mulVec]
      refine (Finset.sum_congr rfl fun i _ => ?_).trans this
      exact Matrix.smul_mulVec _ _ _
    have h1 : Matrix.toLin' (aeval (N ^ m) q) = 0 :=
      LinearMap.ext_on hspan (fun x hx => by simpa using hon x hx)
    exact Matrix.toLin'.injective (h1.trans (map_zero _).symm)
  have hmpos : 0 < m := by omega
  set φ := expand (𝓞 K) m q with hφdef
  have hφm : φ.Monic := hqm.expand hmpos
  have hφ : aeval N (φ.map (algebraMap (𝓞 K) K)) = 0 := by
    rw [aeval_map_algebraMap, hφdef, expand_aeval, hzero]
  have hdvd := charpoly_dvd_pow_card_of_aeval_eq_zero N _ hφ
  rw [← Polynomial.map_pow] at hdvd
  obtain ⟨χ, hχ⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K (hφm.pow r) hdvd
  rw [(Matrix.charpoly_monic N).leadingCoeff, C_1, mul_one] at hχ
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
  have hχm : χ.Monic := by
    have := Matrix.charpoly_monic N
    rw [← hχ] at this
    exact Polynomial.monic_of_injective hinj this
  have hχdvd : χ ∣ φ ^ r := (Polynomial.map_dvd_map _ hinj hχm).1 (hχ ▸ hdvd)
  have hχdeg : χ.natDegree = r := by
    rw [← natDegree_map_eq_of_injective hinj, hχ, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have hqπ : q.map (Ideal.Quotient.mk P) = X ^ q.natDegree := by
    ext k
    rw [coeff_map, coeff_X_pow]
    rcases lt_trichotomy k q.natDegree with hk | rfl | hk
    · rw [if_neg hk.ne, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.pow_le_self (by omega) (hqc k)
    · simp [hqm.coeff_natDegree]
    · rw [if_neg hk.ne', coeff_eq_zero_of_natDegree_lt hk, map_zero]
  have hφπ : φ.map (Ideal.Quotient.mk P) = X ^ (m * q.natDegree) := by
    rw [hφdef, map_expand, hqπ, map_pow, expand_X, ← pow_mul]
  have hdvdπ : χ.map (Ideal.Quotient.mk P) ∣ X ^ (m * q.natDegree * r) := by
    rw [pow_mul, ← hφπ, ← Polynomial.map_pow]
    exact Polynomial.map_dvd _ hχdvd
  haveI : IsDomain (𝓞 K ⧸ P) := Ideal.Quotient.isDomain P
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow Polynomial.prime_X _).1 hdvdπ
  have hχπ : χ.map (Ideal.Quotient.mk P) = X ^ i :=
    eq_of_monic_of_associated (hχm.map _) (monic_X_pow i) hi
  have hir : i = r := by
    have := congrArg natDegree hχπ
    rw [hχm.natDegree_map, natDegree_X_pow, hχdeg] at this
    exact this.symm
  have hcoeff : χ.coeff (r - 1) ∈ P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have := congrArg (fun p => p.coeff (r - 1)) hχπ
    simp only [coeff_map, coeff_X_pow, hir] at this
    rw [this, if_neg (by omega)]
  refine ⟨-χ.coeff (r - 1), P.neg_mem hcoeff, ?_⟩
  rw [Matrix.trace_eq_neg_charpoly_coeff, Fintype.card_fin, ← hχ, coeff_map]
  show algebraMap (𝓞 K) K (-χ.coeff (r - 1)) = _
  rw [map_neg]

end GlobalTheory
end
