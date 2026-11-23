module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
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
public import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

@[expose] public section

section

open MeasureTheory Finset

namespace GlobalTheory

theorem setIntegral_cube_prod (a : ℕ) (S : Set ℝ) (f : Fin a → ℝ → ℝ) :
    ∫ τ in Set.pi Set.univ (fun _ : Fin a => S), ∏ i, f i (τ i) = ∏ i, ∫ t in S, f i t := by
  have hμ : (volume : Measure (Fin a → ℝ)).restrict (Set.pi Set.univ (fun _ : Fin a => S)) =
      Measure.pi (fun _ : Fin a => (volume : Measure ℝ).restrict S) := by
    rw [volume_pi]
    exact Measure.restrict_pi_pi (fun _ : Fin a => (volume : Measure ℝ)) (fun _ => S)
  rw [hμ]
  exact integral_fintype_prod_eq_prod (ι := Fin a) f

theorem setIntegral_Icc_const_div (c lo : ℝ) (h0 : 0 < lo) (h1 : lo ≤ 1 / 2) :
    ∫ t in Set.Icc lo (1 / 2), c / t = c * Real.log (1 / (2 * lo)) := by
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h1]
  have hfun : (fun t : ℝ => c / t) = fun t => c * t⁻¹ := by
    funext t; rw [div_eq_mul_inv]
  rw [hfun, intervalIntegral.integral_const_mul, integral_inv_of_pos h0 hhalf]
  congr 2
  field_simp

private lemma setIntegral_Ioo_pow_mul_div_eq (c m : ℕ) (hm : 1 ≤ m) (hc : 1 ≤ c) :
    ∫ t in Set.Ioo (0 : ℝ) (1 / 2), t ^ (c * m) * ((c : ℝ) / t) =
      (c : ℝ) * ((1 / 2 : ℝ) ^ (c * m) / ((c * m : ℕ) : ℝ)) := by
  obtain ⟨k, hk⟩ : ∃ k, c * m = k + 1 := ⟨c * m - 1, by have := Nat.mul_le_mul hc hm; omega⟩
  have hcongr : Set.EqOn (fun t : ℝ => t ^ (c * m) * ((c : ℝ) / t)) (fun t => (c : ℝ) * t ^ k)
      (Set.Ioo (0 : ℝ) (1 / 2)) := by
    intro t ht
    have htne : t ≠ 0 := ne_of_gt ht.1
    simp only
    rw [hk, pow_succ]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioo hcongr, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by norm_num), intervalIntegral.integral_const_mul,
    integral_pow, hk]
  push_cast
  ring

theorem setIntegral_Ioo_pow_mul_div (c m : ℕ) (hm : 1 ≤ m) (hc : 1 ≤ c) :
    0 ≤ ∫ t in Set.Ioo (0 : ℝ) (1 / 2), t ^ (c * m) * ((c : ℝ) / t) ∧
    ∫ t in Set.Ioo (0 : ℝ) (1 / 2), t ^ (c * m) * ((c : ℝ) / t) ≤ 1 := by
  rw [setIntegral_Ioo_pow_mul_div_eq c m hm hc]
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  have hmpos : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hpow0 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (c * m) := by positivity
  have hpow1 : (1 / 2 : ℝ) ^ (c * m) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hcm : ((c * m : ℕ) : ℝ) = (c : ℝ) * m := by push_cast; ring
  rw [hcm]
  have hden : (0 : ℝ) < (c : ℝ) * m := by positivity
  refine ⟨by positivity, ?_⟩
  rw [mul_div_assoc', div_le_one hden]
  calc (c : ℝ) * (1 / 2 : ℝ) ^ (c * m) ≤ (c : ℝ) * 1 := by gcongr
    _ ≤ (c : ℝ) * m := by gcongr

theorem sum_card_composition_lt (q : ℕ) :
    ∑ j ∈ Finset.Icc 1 q, Fintype.card (Composition j) < 2 ^ q := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), composition_card, Nat.add_sub_cancel, pow_succ]
    omega

theorem sizeIntegrals_and_card_compositions :
    (∀ (a : ℕ) (c : Fin a → ℝ) (lo : ℝ), 0 < lo → lo ≤ 1 / 2 → (∀ i, 0 ≤ c i) → ∫ τ in Set.pi Set.univ (fun _ : Fin a => Set.Icc lo (1 / 2)), ∏ i, c i / τ i = ∏ i, c i * Real.log (1 / (2 * lo))) ∧ (∀ (a : ℕ) (c : Fin a → ℕ) (m : ℕ), 1 ≤ m → (∀ i, 1 ≤ c i) → ∫ τ in Set.pi Set.univ (fun _ : Fin a => Set.Ioo (0 : ℝ) (1 / 2)), ∏ i, τ i ^ (c i * m) * ((c i : ℝ) / τ i) ≤ 1) ∧ ∀ q : ℕ, ∑ j ∈ Finset.Icc 1 q, Fintype.card (Composition j) < 2 ^ q := by
  refine ⟨fun a c lo h0 h1 _ => ?_, fun a c m hm hc => ?_, sum_card_composition_lt⟩
  · refine (setIntegral_cube_prod a (Set.Icc lo (1 / 2)) (fun i t => c i / t)).trans ?_
    exact Finset.prod_congr rfl fun i _ => setIntegral_Icc_const_div (c i) lo h0 h1
  · refine (setIntegral_cube_prod a (Set.Ioo (0 : ℝ) (1 / 2))
      (fun i t => t ^ (c i * m) * ((c i : ℝ) / t))).trans_le ?_
    exact Finset.prod_le_one₀ (fun i _ => (setIntegral_Ioo_pow_mul_div (c i) m hm (hc i)).1)
      fun i _ => (setIntegral_Ioo_pow_mul_div (c i) m hm (hc i)).2

end GlobalTheory
end

section

open MeasureTheory

namespace GlobalTheory

theorem iwasawa_slice_lintegral_le :
    ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul₂ G] (N M K : Subgroup G) (μN μM μK : Measure G) [SFinite μN] [SFinite μM] [SFinite μK] (δ : G → ENNReal) (κ : G → G) (D DN DM : Set G), Measurable δ → Measurable κ → MeasurableSet DN → MeasurableSet DM → μN (N : Set G)ᶜ = 0 → μM (M : Set G)ᶜ = 0 → μK (K : Set G)ᶜ = 0 → μK Set.univ = 1 → (∀ k ∈ K, κ k ∈ K ⊓ M) → (∀ l ∈ K ⊓ M, μM.map (fun g => g * l) = μM) → (∀ l ∈ K ⊓ M, ∀ m ∈ M, δ (m * l) = δ m) → (∀ u ∈ N, ∀ m ∈ M, ∀ k ∈ K, u * m * k ∈ D → u ∈ DN ∧ m * κ k ∈ DM) → ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM ∂μN ≤ μN DN * ∫⁻ m in DM, δ m ∂μM := by
  intro G _ _ _ N M K μN μM μK _ _ _ δ κ D DN DM hδ hκ hDN hDM hN hM hK hK1 hκK hinv hδinv hD
  have aeM : ∀ᵐ m ∂μM, m ∈ (M : Set G) := mem_ae_iff.2 hM
  have aeK : ∀ᵐ k ∂μK, k ∈ (K : Set G) := mem_ae_iff.2 hK
  have aeN : ∀ᵐ u ∂μN, u ∈ (N : Set G) := mem_ae_iff.2 hN

  have htrans : ∀ l ∈ K ⊓ M,
      ∫⁻ m, δ m * DM.indicator (1 : G → ENNReal) (m * l) ∂μM = ∫⁻ m in DM, δ m ∂μM := by
    intro l hl
    have hfun : (fun m => δ m * DM.indicator (1 : G → ENNReal) (m * l))
        =ᵐ[μM] fun m => DM.indicator δ (m * l) := by
      filter_upwards [aeM] with m hm
      have hδml := hδinv l hl m hm
      by_cases hml : m * l ∈ DM
      · simp [hml, hδml]
      · simp [hml]
    rw [lintegral_congr_ae hfun, ← lintegral_map (hδ.indicator hDM) (measurable_mul_const l),
      hinv l hl, lintegral_indicator hDM]

  have hF : Measurable (Function.uncurry
      (fun (m k : G) => δ m * DM.indicator (1 : G → ENNReal) (m * κ k))) :=
    (hδ.comp measurable_fst).mul
      ((measurable_one.indicator hDM).comp (measurable_fst.mul (hκ.comp measurable_snd)))

  have hinner : ∀ u ∈ (N : Set G),
      ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM
        ≤ DN.indicator (fun _ => ∫⁻ m in DM, δ m ∂μM) u := by
    intro u hu
    by_cases huD : u ∈ DN
    · rw [Set.indicator_of_mem huD]
      calc ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM
          ≤ ∫⁻ m, δ m * ∫⁻ k, DM.indicator (1 : G → ENNReal) (m * κ k) ∂μK ∂μM := by
            apply lintegral_mono_ae
            filter_upwards [aeM] with m hm
            gcongr δ m * ?_
            apply lintegral_mono_ae
            filter_upwards [aeK] with k hk
            by_cases hmem : u * m * k ∈ D
            · have h2 := (hD u hu m hm k hk hmem).2
              simp [hmem, h2]
            · simp [hmem]
        _ = ∫⁻ m, ∫⁻ k, δ m * DM.indicator (1 : G → ENNReal) (m * κ k) ∂μK ∂μM := by
            apply lintegral_congr
            intro m
            have hmeas : Measurable (fun k => DM.indicator (1 : G → ENNReal) (m * κ k)) :=
              (measurable_one.indicator hDM).comp (measurable_const.mul hκ)
            exact (lintegral_const_mul (δ m) hmeas).symm
        _ = ∫⁻ k, ∫⁻ m, δ m * DM.indicator (1 : G → ENNReal) (m * κ k) ∂μM ∂μK :=
            lintegral_lintegral_swap hF.aemeasurable
        _ = ∫⁻ _k, ∫⁻ m in DM, δ m ∂μM ∂μK := by
            apply lintegral_congr_ae
            filter_upwards [aeK] with k hk
            exact htrans (κ k) (hκK k hk)
        _ = ∫⁻ m in DM, δ m ∂μM := by
            rw [lintegral_const, hK1, mul_one]
    · have hind : DN.indicator (fun _ => ∫⁻ m in DM, δ m ∂μM) u = 0 := by
        simp [huD]
      rw [hind]
      calc ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM
          ≤ ∫⁻ _m, (0 : ENNReal) ∂μM := by
            apply lintegral_mono_ae
            filter_upwards [aeM] with m hm
            have hae : (fun k => D.indicator (1 : G → ENNReal) (u * m * k))
                =ᵐ[μK] fun _ => (0 : ENNReal) := by
              filter_upwards [aeK] with k hk
              have hmem : u * m * k ∉ D := fun h => huD (hD u hu m hm k hk h).1
              simp [hmem]
            rw [lintegral_congr_ae hae, lintegral_zero, mul_zero]
        _ = 0 := lintegral_zero
  calc ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, D.indicator (1 : G → ENNReal) (u * m * k) ∂μK ∂μM ∂μN
      ≤ ∫⁻ u, DN.indicator (fun _ => ∫⁻ m in DM, δ m ∂μM) u ∂μN := by
        apply lintegral_mono_ae
        filter_upwards [aeN] with u hu
        exact hinner u hu
    _ = μN DN * ∫⁻ m in DM, δ m ∂μM := by
        rw [lintegral_indicator hDN, setLIntegral_const]
        exact mul_comm _ _

end GlobalTheory
end

section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.HaarDensChart

def upperDens {V : Type} [PseudoMetricSpace V] [MeasurableSpace V] (l ν : Measure V) (x : V) : ℝ≥0∞ :=
  limsup (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) (𝓝[>] 0)

end GlobalTheory.HaarDensChart
end
end

section

open NumberField UniqueFactorizationMonoid

namespace GlobalTheory.SplitRadical

theorem isRadical_of_squarefree {S : Type} [CommRing S] [IsDedekindDomain S] {I : Ideal S}
    (hI : Squarefree I) : I.IsRadical := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  have h1 : I ∣ Ideal.span {x} ^ n := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_pow, Ideal.span_singleton_le_iff_mem]
    exact hn
  have h2 : I ∣ Ideal.span {x} := hI.isRadical n _ h1
  exact (Ideal.span_singleton_le_iff_mem I).1 (Ideal.dvd_iff_le.1 h2)

theorem isRadical_span_of_ncard_primesOver : ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime →
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E →
    (Ideal.span {(p : 𝓞 E)}).IsRadical := by
  intro E _ _ p hp hcard
  haveI : Fact p.Prime := ⟨hp⟩
  set P : Ideal ℤ := Ideal.span {(p : ℤ)} with hP
  have hPmax : P.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hP0 : P ≠ ⊥ := by
    rw [hP, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hmap : Ideal.span {(p : 𝓞 E)} = P.map (algebraMap ℤ (𝓞 E)) := by
    rw [hP, Ideal.map_span, Set.image_singleton, map_natCast]
  have hmap0 : P.map (algebraMap ℤ (𝓞 E)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hP0

  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 E)
  rw [NumberField.RingOfIntegers.rank, ← hcard, ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    ← Finset.card_univ, Finset.card_eq_sum_ones] at hsum

  have hge : ∀ q ∈ (Finset.univ : Finset (P.primesOver (𝓞 E))),
      1 ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    intro q _
    haveI : q.1.IsPrime := q.2.1
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (Ideal.ramificationIdx_pos (R := ℤ) q.1).ne'
      (Ideal.inertiaDeg_pos q.1 ℤ).ne')
  have hone : ∀ q : P.primesOver (𝓞 E), q.1.ramificationIdx ℤ = 1 := by
    intro q
    have := (Finset.sum_eq_sum_iff_of_le hge).1 hsum.symm q (Finset.mem_univ q)
    exact Nat.eq_one_of_mul_eq_one_right this.symm

  rw [hmap]
  apply isRadical_of_squarefree
  rw [UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hmap0,
    Multiset.nodup_iff_count_le_one]
  intro q
  by_cases hq : q ∈ UniqueFactorizationMonoid.normalizedFactors (P.map (algebraMap ℤ (𝓞 E)))
  · have hqprime : q.IsPrime :=
      Ideal.isPrime_of_prime (UniqueFactorizationMonoid.prime_of_normalized_factor q hq)
    have hle : P.map (algebraMap ℤ (𝓞 E)) ≤ q :=
      Ideal.le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq)
    have hlo : q.LiesOver P :=
      ⟨hPmax.eq_of_le (Ideal.comap_ne_top _ hqprime.ne_top) (Ideal.map_le_iff_le_comap.1 hle)⟩
    rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count P q hmap0]
    exact (hone ⟨q, hqprime, hlo⟩).le
  · rw [Multiset.count_eq_zero.2 hq]
    exact zero_le_one

end GlobalTheory.SplitRadical
end

section

namespace GlobalTheory.IntegerMultipleIntegral

theorem exists_int_mul_integral {K : Type} [Field K] [NumberField K] (k : K) :
    ∃ M : ℤ, M ≠ 0 ∧ ∃ a : NumberField.RingOfIntegers K,
      algebraMap (NumberField.RingOfIntegers K) K a = M • k := by
  have h1 : IsAlgebraic ℚ k := Algebra.IsAlgebraic.isAlgebraic k
  have h2 : IsAlgebraic ℤ k := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr h1
  obtain ⟨M, hM, hint⟩ := h2.exists_integral_multiple
  exact ⟨M, hM, ⟨M • k, hint⟩, rfl⟩

theorem exists_int_smul_mem {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {A : Submodule (NumberField.RingOfIntegers K) V} (hA : Submodule.span K (A : Set V) = ⊤)
    (x : V) : ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ A := by
  have hx : x ∈ Submodule.span K (A : Set V) := by rw [hA]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨M, hM, hy⟩ := hy
    obtain ⟨N, hN, hz⟩ := hz
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    rw [smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact A.toAddSubgroup.zsmul_mem hy N
    · rw [mul_smul]; exact A.toAddSubgroup.zsmul_mem hz M
  | smul k y _ hy =>
    obtain ⟨N, hN, hy⟩ := hy
    obtain ⟨M, hM, a, ha⟩ := exists_int_mul_integral k
    refine ⟨M * N, mul_ne_zero hM hN, ?_⟩
    have : (M * N) • k • y = a • (N • y) := by
      rw [← algebraMap_smul K a, ha, smul_assoc, mul_smul, smul_comm N k y]
    rw [this]
    exact A.smul_mem a hy

theorem exists_int_smul_le {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    {A : Submodule (NumberField.RingOfIntegers K) V} (hA : Submodule.span K (A : Set V) = ⊤)
    {B : Submodule (NumberField.RingOfIntegers K) V} (hB : B.FG) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ x ∈ B, N • x ∈ A := by
  obtain ⟨s, rfl⟩ := hB
  choose f hf0 hf using exists_int_smul_mem hA
  refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.mpr fun y _ => hf0 y, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f (Finset.mem_coe.mp hy)
    rw [hc, mul_comm, mul_smul]
    exact A.toAddSubgroup.zsmul_mem (hf y) c
  | zero => simp
  | add y z _ _ hy hz => rw [smul_add]; exact A.add_mem hy hz
  | smul a y _ hy => rw [smul_comm]; exact A.smul_mem a hy

end GlobalTheory.IntegerMultipleIntegral
end

section

namespace GlobalTheory.TargetStatementBis

open NumberField

theorem main {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V)
    (h : Submodule.span K (Λ : Set V) = ⊤) (v : V) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • v ∈ Λ := by
  have hv : v ∈ Submodule.span K (Λ : Set V) := h ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, hd₁, h₁⟩ := hx
    obtain ⟨d₂, hd₂, h₂⟩ := hy
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine Λ.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.smul_mem _ h₁
    · rw [mul_smul]; exact Λ.smul_mem _ h₂
  | smul c x _ hx =>
    obtain ⟨d, hd, h₁⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) c
    refine ⟨d * b, mul_ne_zero hd (nonZeroDivisors.ne_zero b.2), ?_⟩
    have key : ((b : 𝓞 K)) • (c • x) = a • x := by
      rw [← algebraMap_smul K (b : 𝓞 K) (c • x), smul_smul, mul_comm, hab, algebraMap_smul]
    rw [mul_smul, key, smul_comm d a x]
    exact Λ.smul_mem a h₁

theorem target : ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V] [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V] (Λ : Submodule (NumberField.RingOfIntegers K) V), Submodule.span K (↑Λ : Set V) = ⊤ → ∀ (v : V), ∃ (d : NumberField.RingOfIntegers K), d ≠ (0 : NumberField.RingOfIntegers K) ∧ d • v ∈ Λ :=
  fun Λ h v => main Λ h v

end GlobalTheory.TargetStatementBis
end

section

namespace GlobalTheory.UpperUnitriangularMul

open Matrix

theorem upperUnitriangular_mul {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}
    {U W : Matrix (Fin N) (Fin N) E}
    (hU : ∀ a b : Fin N, b < a → U a b = (0 : E)) (hU1 : ∀ a : Fin N, U a a = (1 : E))
    (hW : ∀ a b : Fin N, b < a → W a b = (0 : E)) (hW1 : ∀ a : Fin N, W a a = (1 : E)) :
    (∀ a b : Fin N, b < a → (U * W) a b = (0 : E)) ∧ ∀ a : Fin N, (U * W) a a = (1 : E) := by
  constructor
  · intro a b hba
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro c _
    rcases lt_or_ge c a with h | h
    · rw [hU a c h, zero_mul]
    · rw [hW c b (lt_of_lt_of_le hba h), mul_zero]
  · intro a
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hU1, hW1, one_mul]
    · intro c _ hca
      rcases lt_or_gt_of_ne hca with h | h
      · rw [hU a c h, zero_mul]
      · rw [hW c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h

end GlobalTheory.UpperUnitriangularMul
end

section

open NumberField

namespace GlobalTheory


open NumberField in
theorem _root_.GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top (F E : Type) [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E] :
    Algebra.FormallyUnramified (𝓞 F) (𝓞 E) ↔ differentIdeal (𝓞 F) (𝓞 E) = ⊤ := by
  rw [← Algebra.unramifiedLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  constructor
  · intro h
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    exact (dvd_differentIdeal_iff (P := M)).1 (Ideal.dvd_iff_le.2 hle) (h ⟨M, hM.isPrime⟩)
  · intro h P
    show Algebra.IsUnramifiedAt _ P.asIdeal
    rw [← not_dvd_differentIdeal_iff, h, Ideal.dvd_iff_le, top_le_iff]
    exact P.isPrime.ne_top

end GlobalTheory
end
