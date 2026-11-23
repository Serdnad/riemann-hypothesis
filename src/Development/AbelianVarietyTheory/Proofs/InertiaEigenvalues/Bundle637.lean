module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle607
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle590
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.FirstCoordinateAdmissible
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle035
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetIdealSelfDualLatticeAndInterStandard
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle495
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle609
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle516
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle612
import GroundTheory.GlobalFields.TateThesis.SchwartzBruhatDual
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InvertibleSpanSingleton
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle015
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001

@[expose] public section

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.DiscRem

theorem norm_add_le_max' (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (x y : Disc l u ρ) :
    ‖x + y‖ ≤ max ‖x‖ ‖y‖ := by
  refine (denseRange_ofPre l u ρ).induction_on₂ (p := fun x y => ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (isClosed_le (by fun_prop) (by fun_prop)) (fun a b => ?_) x y
  rw [← map_add (f := _), norm_ofPre, norm_ofPre, norm_ofPre]
  exact gauge_add_le_max l u ρ a b

theorem norm_toDisc_l_le (l : ℕ) [hl : Fact l.Prime] {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) :
    ‖toDisc l u ρ (l : A)‖ ≤ (l : ℝ)⁻¹ := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.2 hl.out.pos
  exact (norm_ofPre l u ρ _).trans_le (gauge_le l u ρ (by positivity)
    (Submodule.subset_span ⟨1, 0, 0, by simp [hl0.ne'], by simp⟩))

theorem coeff_mul_disc (l : ℕ) {R : Type} [CommRing R] (ρ : ℝ≥0)
    (a : ℕ → (Disc l (X : R⟦X⟧) ρ →+ Disc l (0 : R) 1))
    (h1 : ∀ n x, a n (toDisc l (X : R⟦X⟧) ρ x) = toDisc l (0 : R) 1 (coeff n x))
    (hc : ∀ n, Continuous (a n)) (s : R⟦X⟧) (n : ℕ) (y : Disc l (X : R⟦X⟧) ρ) :
    a n (toDisc l (X : R⟦X⟧) ρ s * y) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, toDisc l (0 : R) 1 (coeff p.1 s) * a p.2 y := by
  refine (denseRange_ofPre l (X : R⟦X⟧) ρ).induction_on y
    (isClosed_eq ((hc n).comp (continuous_const.mul continuous_id))
      (continuous_finsetSum _ fun p _ => continuous_const.mul (hc p.2))) fun z => ?_
  obtain ⟨k, b, h⟩ := IsLocalization.Away.surj (l : R⟦X⟧) z
  have h' : (l ^ k : ℕ) • ofPre l (X : R⟦X⟧) ρ z = toDisc l (X : R⟦X⟧) ρ b := by
    have := congrArg (ofPre l (X : R⟦X⟧) ρ) h
    rw [map_mul, map_pow, map_natCast, map_natCast] at this
    rw [nsmul_eq_mul, Nat.cast_pow, mul_comm]
    exact this
  refine ((isUnit_l_disc l (0 : R) 1).pow k).mul_left_cancel ?_

  rw [← Nat.cast_pow, ← nsmul_eq_mul, ← nsmul_eq_mul, ← map_nsmul, ← mul_smul_comm, h', ← map_mul, h1,
  coeff_mul, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← mul_smul_comm, ← map_nsmul, h', h1, map_mul]

theorem rho_zero {l : ℕ} [hl : Fact l.Prime] {K : FinExt l} (bk : BK K) :
    0 < bk.ρ₀ ∧ bk.ρ₀ < 1 ∧ (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree = (l : ℝ)⁻¹ := by
  have he : (0 : ℝ) < bk.Ep.natDegree := Nat.cast_pos.2 bk.deg_pos
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  refine ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (by
    have : 0 < 1 / (bk.Ep.natDegree : ℝ) := by positivity
    linarith), ?_⟩
  rw [BK.ρ₀, NNReal.coe_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (NNReal.coe_nonneg _), neg_mul,
    one_div_mul_cancel he.ne', Real.rpow_neg_one, NNReal.coe_natCast]

theorem eq_zero_of_dvd : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (r : Polynomial (Wq l bk.a)),
    r.degree < bk.Ep.degree →
    toDisc l (X : bk.S) bk.ρ₀ bk.E ∣ toDisc l (X : bk.S) bk.ρ₀ (r : bk.S) → r = 0 := by
  intro l hl K bk r hr ⟨y, hy⟩
  obtain ⟨h0, h1, hpow⟩ := rho_zero bk
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := GlobalTheory.T.exists_gaussNorm_coeff_wittDisc l K bk bk.ρ₀ h0 h1
  obtain ⟨-, -, hinj, -⟩ := GlobalTheory.T.closedDiscGaugeCompletion_zero_one_properties l K bk
  have h0' : (0 : ℝ) < bk.ρ₀ := h0
  have h1' : (bk.ρ₀ : ℝ) < 1 := h1
  have hc : ∀ n, Continuous (a n) := fun n =>
    AddMonoidHomClass.continuous_of_bound _ ((bk.ρ₀ : ℝ) ^ n)⁻¹ fun z => by
      rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]; exact ha2 n z
  have hy0 : y = 0 := by
    refine norm_le_zero_iff.1 (ha3 y 0 le_rfl fun m₀ => ?_)
    by_contra hneg
    push Not at hneg
    set c := ‖a m₀ y‖ * (bk.ρ₀ : ℝ) ^ m₀ with hcdef
    have hfin : {n | c ≤ ‖a n y‖ * (bk.ρ₀ : ℝ) ^ n}.Finite := by
      have := (ha4 y).eventually (gt_mem_nhds hneg)
      rw [← Nat.cofinite_eq_atTop, Filter.eventually_cofinite] at this
      simpa only [not_lt] using this
    obtain ⟨m, hm, hmax⟩ := hfin.exists_maximal ⟨m₀, le_refl c⟩
    have hlt : ∀ n, m < n → ‖a n y‖ * (bk.ρ₀ : ℝ) ^ n < c := fun n hn => by
      by_contra h
      exact (hmax (not_lt.1 h) hn.le).not_gt hn
    have key := coeff_mul_disc l bk.ρ₀ a ha1 hc bk.E (bk.Ep.natDegree + m) y
    have hz : coeff (bk.Ep.natDegree + m) (r : bk.S) = 0 := by
      rw [Polynomial.coeff_coe]
      refine Polynomial.coeff_eq_zero_of_degree_lt (hr.trans_le ?_)
      rw [Polynomial.degree_eq_natDegree bk.monic.ne_zero]
      exact_mod_cast Nat.le_add_right _ _
    rw [← hy, ha1, hz, map_zero, ← Finset.add_sum_erase _ _
      (show (bk.Ep.natDegree, m) ∈ Finset.HasAntidiagonal.antidiagonal (bk.Ep.natDegree + m) by simp)] at key
    have hlead : coeff bk.Ep.natDegree bk.E = 1 := by
      rw [Polynomial.coeff_coe]; exact bk.monic
    simp only [hlead, map_one, one_mul] at key
    have hsum : ‖∑ p ∈ (Finset.HasAntidiagonal.antidiagonal (bk.Ep.natDegree + m)).erase (bk.Ep.natDegree, m),
        toDisc l (0 : Wq l bk.a) 1 (coeff p.1 bk.E) * a p.2 y‖ * (bk.ρ₀ : ℝ) ^ m < c := by
      refine Finset.sum_induction _ (fun x => ‖x‖ * (bk.ρ₀ : ℝ) ^ m < c) (fun x z hx hz => ?_)
        (by simpa using hneg) fun p hp => ?_
      · refine (mul_le_mul_of_nonneg_right (norm_add_le_max' l _ _ x z) (by positivity)).trans_lt ?_
        rcases max_cases ‖x‖ ‖z‖ with h | h <;> rw [h.1] <;> assumption
      · obtain ⟨i, j⟩ := p
        simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq, Prod.mk.injEq] at hp
        rw [Polynomial.coeff_coe]
        rcases lt_trichotomy i bk.Ep.natDegree with h | h | h
        · obtain ⟨w, hw⟩ := bk.dvd_coeff i h
          have hn : ‖toDisc l (0 : Wq l bk.a) 1 (bk.Ep.coeff i)‖ ≤ (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree := by
            rw [hw, map_mul, hpow]
            exact (norm_mul_le _ _).trans ((mul_le_mul (norm_toDisc_l_le l _ _) (norm_toDisc_le _)
              (norm_nonneg _) (by positivity)).trans (mul_one _).le)
          refine lt_of_le_of_lt ?_ (hlt j (by omega))
          have hp2 : (bk.ρ₀ : ℝ) ^ (bk.Ep.natDegree + m) ≤ (bk.ρ₀ : ℝ) ^ j :=
            pow_le_pow_of_le_one h0'.le h1'.le (by omega)
          calc _ ≤ (bk.ρ₀ : ℝ) ^ bk.Ep.natDegree * ‖a j y‖ * (bk.ρ₀ : ℝ) ^ m :=
                mul_le_mul_of_nonneg_right ((norm_mul_le _ _).trans
                  (mul_le_mul_of_nonneg_right hn (norm_nonneg _))) (by positivity)
            _ = ‖a j y‖ * (bk.ρ₀ : ℝ) ^ (bk.Ep.natDegree + m) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hp2 (norm_nonneg _)
        · exact (hp.1 ⟨h, by omega⟩).elim
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt h]
          simpa using hneg
    rw [eq_neg_of_add_eq_zero_right key.symm, norm_neg] at hsum
    exact hsum.not_ge hm
  apply Polynomial.ext
  intro n
  apply hinj
  have := ha1 n (r : bk.S)
  rw [hy, hy0, mul_zero, map_zero, Polynomial.coeff_coe] at this
  rw [← this, Polynomial.coeff_zero, map_zero]

end GlobalTheory.BSP.DiscRem
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.LatPow

theorem pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [NormedField K] [Algebra O K]
    [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (G : Type) [Group G] [TopologicalSpace G]
    (T : LocLat G ℚ_[l] K O) (v : T.V), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∃ x : ↥T.L.T, (x : T.V) = (l : K) ^ n • v := by
  intro l _ O K _ _ _ _ _ G _ _ T v
  have hv : v ∈ Submodule.span K (T.L.T : Set T.V) := by rw [T.L.span]; trivial
  suffices h : ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (l : K) ^ n • v ∈ T.L.T by
    obtain ⟨n₀, h⟩ := h
    exact ⟨n₀, fun n hn => ⟨⟨_, h n hn⟩, rfl⟩⟩
  induction hv using Submodule.span_induction with
  | mem x hx =>
    refine ⟨0, fun n _ => ?_⟩
    have : (l : K) ^ n • x = ((l : O) ^ n) • x := by
      rw [← algebraMap_smul K ((l : O) ^ n) x, map_pow, map_natCast]
    rw [this]
    exact T.L.T.smul_mem _ hx
  | zero => exact ⟨0, fun n _ => by rw [smul_zero]; exact T.L.T.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨max a b, fun n hn => by
      rw [smul_add]
      exact T.L.T.add_mem (ha n (le_of_max_le_left hn)) (hb n (le_of_max_le_right hn))⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨m, b, hb⟩ := exists_pow_mul_mem (O := O) l c
    refine ⟨a + m, fun n hn => ?_⟩
    have e : (l : K) ^ n • c • x = b • ((l : K) ^ (n - m) • x) := by
      rw [← algebraMap_smul K b, ← hb, smul_smul, smul_smul]
      congr 1
      rw [mul_comm ((l : K) ^ m) c, mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega), mul_comm]
    rw [e]
    exact T.L.T.smul_mem _ (ha _ (by omega))

end GlobalTheory.LatPow
end

section

set_option autoImplicit false

namespace GlobalTheory.ScalarUnit

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GoodPts
open scoped nonZeroDivisors

section Ideals

variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem smul_eq_idlE_mul (J : Ideal (𝓞 E)) (M : Submodule (𝓞 E) E) : J • M = idlE J * M := by
  unfold idlE
  apply le_antisymm
  · refine Submodule.smul_le.mpr fun r hr m hm => ?_
    rw [Algebra.smul_def]
    exact Submodule.mul_mem_mul (Submodule.mem_map_of_mem hr) hm
  · refine Submodule.mul_le.mpr fun x hx m hm => ?_
    obtain ⟨r, hr, rfl⟩ := Submodule.mem_map.mp hx
    rw [Algebra.linearMap_apply, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul hr hm

omit [NumberField E] in
theorem idlE_mul (I J : Ideal (𝓞 E)) : idlE (I * J) = idlE I * idlE J := IsLocalization.coeSubmodule_mul E I J

theorem idlE_cancel {G : Ideal (𝓞 E)} (hG : G ≠ ⊥) {X Y : Submodule (𝓞 E) E} (h : idlE G * X = idlE G * Y) :
    X = Y := by
  have hG' : (G : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hG
  have e : idlE G = ((G : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) := rfl
  have key : ∀ Z : Submodule (𝓞 E) E,
      (((G : FractionalIdeal (𝓞 E)⁰ E)⁻¹ : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E) *
        (idlE G * Z) = Z := by
    intro Z
    rw [e, ← mul_assoc, ← FractionalIdeal.coe_mul, inv_mul_cancel₀ hG', FractionalIdeal.coe_one, one_mul]
  rw [← key X, h, key Y]

theorem index_coprime {n p : ℕ} (hp : p.Prime) (Λ : GenLat E n) (h : Λ.TrivAt p)
    (h0 : (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ≠ 0) :
    Nat.Coprime (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index p := by
  obtain ⟨k, hk, hk1, -⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Λ.La.toAddSubgroup ⧸ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero h0
  let _ := Fintype.ofFinite (Λ.La.toAddSubgroup ⧸ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup)
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp]
  intro hdvd
  have hdvd' : p ∣ Fintype.card
      (Λ.La.toAddSubgroup ⧸ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup) := by
    rw [← Nat.card_eq_fintype_card]; exact hdvd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hdvd'
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hmem : k • y ∈ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup := by
    rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup]
    have hc : ((k • y : Λ.La.toAddSubgroup) : Fin n → E) = (k : 𝓞 E) • (y : Fin n → E) := by
      rw [Nat.cast_smul_eq_nsmul]
      rfl
    rw [hc]
    have h1 : (k : 𝓞 E) • (y : Fin n → E) ∈ Ideal.span {(k : 𝓞 E)} • Λ.La :=
      Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) y.2
    show (k : 𝓞 E) • (y : Fin n → E) ∈ Λ.La ⊓ stdLat E n
    exact Submodule.mem_inf.mpr ⟨Λ.La.smul_mem _ y.2, hk1 h1⟩
  have hz : k • (QuotientAddGroup.mk y :
      Λ.La.toAddSubgroup ⧸ Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup) = 0 := by
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact hmem
  have hpk : p ∣ k := hx ▸ addOrderOf_dvd_of_nsmul_eq_zero hz
  exact hp.ne_one (Nat.Coprime.eq_one_of_dvd hk.symm hpk)

theorem val_natCast {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {p a : ℕ}
    (hp : (p : 𝓞 K) ∈ la.asIdeal) (h : Nat.Coprime a p) : la.valuation K (a : K) = 1 := by
  have hnot : (a : 𝓞 K) ∉ la.asIdeal := by
    intro ha
    obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.mpr h).map (Int.castRingHom (𝓞 K))
    have huv' : u * (a : 𝓞 K) + v * (p : 𝓞 K) = 1 := by simpa using huv
    apply la.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← huv']
    exact la.asIdeal.add_mem (la.asIdeal.mul_mem_left u ha) (la.asIdeal.mul_mem_left v hp)
  rw [← map_natCast (algebraMap (𝓞 K) K) a]
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (v := la) (K := K)).mpr hnot

variable [IsCMField E]

theorem bar_bar (H : Host E) (a : 𝓞 E) : H.bar (H.bar a) = a := by
  apply RingOfIntegers.ext
  rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]

theorem map_bar_bar (H : Host E) (J : Ideal (𝓞 E)) :
    (J.map (H.bar : 𝓞 E →+* 𝓞 E)).map (H.bar : 𝓞 E →+* 𝓞 E) = J := by
  rw [Ideal.map_map]
  have hid : (H.bar : 𝓞 E →+* 𝓞 E).comp (H.bar : 𝓞 E →+* 𝓞 E) = RingHom.id _ :=
    RingHom.ext fun a => bar_bar H a
  rw [hid, Ideal.map_id]

theorem conjI_eq (H : Host E) (J : Ideal (𝓞 E)) : GlobalTheory.SW.conjI J = J.map (H.bar : 𝓞 E →+* 𝓞 E) := by
  unfold GlobalTheory.SW.conjI
  rw [Ideal.map]
  congr 1
  ext a
  constructor
  · rintro ⟨b, hb, hab⟩
    refine ⟨b, hb, ?_⟩
    apply RingOfIntegers.ext
    exact (H.bar_eq b).trans hab.symm
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b, hb, H.bar_eq b⟩

theorem exists_numerator (H : Host E) {n : ℕ} (Λ : GenLat E n) (h : Λ.Unimod) :
    (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index ≠ 0 ∧
    ∃ cc : Ideal (𝓞 E), cc ⊔ cc.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ ∧
      Submodule.span (𝓞 E) (detSet Λ.La) * idlE (cc.map (H.bar : 𝓞 E →+* 𝓞 E)) = idlE cc ∧
      (((Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℕ) : 𝓞 E) ∈ cc := by
  obtain ⟨J, hJ0, hJn, hJd, hJc, -⟩ := GlobalTheory.DetIdeal.detIdeal_selfDual E n Λ h
  refine ⟨?_, ?_⟩
  · rw [← hJn]
    exact fun h0 => hJ0 (Ideal.absNorm_eq_zero_iff.mp h0)
  have hrel : idlE J * Submodule.span (𝓞 E) (detSet Λ.La) = idlE (J.map (H.bar : 𝓞 E →+* 𝓞 E)) := by
    rw [← smul_eq_idlE_mul, ← hJd, hJc, conjI_eq H]
    rfl
  obtain ⟨A, hA⟩ : J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E) ∣ J := Ideal.dvd_iff_le.mpr le_sup_left
  have hG0 : J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ ⊥ := fun h0 => hJ0 (eq_bot_iff.mpr (h0 ▸ le_sup_left))
  have hGbar : (J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E)).map (H.bar : 𝓞 E →+* 𝓞 E) =
      J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    rw [Ideal.map_sup, map_bar_bar, sup_comm]
  have hJbar : J.map (H.bar : 𝓞 E →+* 𝓞 E) =
      (J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E)) * A.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    conv_lhs => rw [hA]
    rw [Ideal.map_mul, hGbar]
  have hcop : A ⊔ A.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ := by
    have e : (J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E)) * (A ⊔ A.map (H.bar : 𝓞 E →+* 𝓞 E)) =
        (J ⊔ J.map (H.bar : 𝓞 E →+* 𝓞 E)) * ⊤ := by
      rw [Ideal.mul_sup, ← hA, ← hJbar, Ideal.mul_top]
    exact mul_left_cancel₀ hG0 e
  have hJA : J ≤ A := by
    rw [hA]
    exact Ideal.mul_le_right
  refine ⟨A.map (H.bar : 𝓞 E →+* 𝓞 E), ?_, ?_, ?_⟩
  · rw [map_bar_bar, sup_comm]
    exact hcop
  · rw [map_bar_bar, mul_comm]
    apply idlE_cancel hG0
    rw [← mul_assoc, ← idlE_mul, ← hA, hrel]
    conv_lhs => rw [hJbar]
    rw [idlE_mul]
  · have hm : (((Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index : ℕ) : 𝓞 E) ∈ J := by
      rw [← hJn]
      exact Ideal.absNorm_mem J
    have h2 := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hm
    rw [map_natCast] at h2
    exact Ideal.map_mono hJA h2

end Ideals

end GlobalTheory.ScalarUnit
end

section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

theorem _root_.GlobalTheory.T.haar_measure_uniformizer_translate : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ))
    (A : Set (GlobalTheory.CellDec.NA E n)), MeasurableSet A →
    ν {u : GlobalTheory.CellDec.NA E n | ∃ a ∈ A, (a : GA E n) = GlobalTheory.CellDec.tl n ϖ l * (u : GA E n) * (GlobalTheory.CellDec.tl n ϖ l)⁻¹} =
      ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) * ν A := by
  first | exact @GlobalTheory.CellDec.ModulusPf.modulus_conj | exact GlobalTheory.CellDec.ModulusPf.modulus_conj | (intros; apply GlobalTheory.CellDec.ModulusPf.modulus_conj <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan

noncomputable section

namespace GlobalTheory.RSNonvan.GoodSet

variable {E : Type} [Field E] [NumberField E]

theorem psiLoc_cond (w : HeightOneSpectrum (𝓞 E))
    (hw : FractionalIdeal.count E w ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 0) (x : w.adicCompletion E) :
    (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔ x ∈ Ov E w := by
  have key : (∀ y ∈ Ov E w, (GroundTheory.Global.adelicChar _ (GlobalTheory.CuspRep.sFin _ (GlobalTheory.CuspRep.sLoc _ w (x * y))) : ℂ) = 1) ↔
      ∀ a ∈ w.adicCompletionIntegers E, GroundTheory.Global.localAdelicChar E w (a * x) = 1 := by
    refine forall_congr' fun y => imp_congr Iff.rfl ?_
    change GlobalTheory.StdCharConductor.psi E (sFin E (sLoc E w (x * y))) = 1 ↔ _
    rw [GlobalTheory.StdCharConductor.psi_loc_eq_one_iff, mul_comm]
  rw [key, GroundTheory.Global.forall_localAdelicChar_mul_eq_one_iff, GroundTheory.Global.mem_localInvDifferent_iff_valued, hw]
  change _ ↔ x ∈ w.adicCompletionIntegers E
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  rfl

theorem finite_sameBelow (u : HeightOneSpectrum (𝓞 E)) :
    {w' : HeightOneSpectrum (𝓞 E) | Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal}.Finite := by
  set N : ℕ := Ideal.absNorm u.asIdeal
  have hN : N ≠ 0 := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm u
    omega
  have hI : Ideal.span {(N : 𝓞 E)} ≠ 0 := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine (Ideal.finite_factors hI).subset fun w' hw' => ?_
  simp only [Set.mem_setOf_eq] at hw' ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_le, Set.singleton_subset_iff]
  have h1 : ((N : ℤ)) ∈ Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal := by
    rw [Ideal.mem_comap, map_natCast]
    exact Ideal.absNorm_mem u.asIdeal
  rw [← hw', Ideal.mem_comap, map_natCast] at h1
  exact h1

variable [_root_.NumberField.IsTotallyComplex E]

theorem exists_isGood_superset (T : Finset (HeightOneSpectrum (𝓞 E))) :
    ∃ T' : Finset (HeightOneSpectrum (𝓞 E)), T ⊆ T' ∧ IsGood T' := by
  classical
  have hD : {w : HeightOneSpectrum (𝓞 E) | FractionalIdeal.count E w ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E) ≠ 0}.Finite :=
    FractionalIdeal.finite_factors (K := E) ((differentIdeal ℤ (𝓞 E) : Ideal (𝓞 E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
  set T₁ : Finset (HeightOneSpectrum (𝓞 E)) := T ∪ hD.toFinset
  set S : Set (HeightOneSpectrum (𝓞 E)) := {w' | ∃ u ∈ T₁, Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
      Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal}
  have hS : S.Finite := by
    have : S = ⋃ u ∈ T₁, {w' : HeightOneSpectrum (𝓞 E) | Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal =
        Ideal.comap (algebraMap ℤ (𝓞 E)) u.asIdeal} := by
      ext w'
      simp [S]
    rw [this]
    exact T₁.finite_toSet.biUnion fun u _ => finite_sameBelow u
  have hT₁ : ∀ w ∈ T₁, w ∈ hS.toFinset := fun w hw => by
    rw [Set.Finite.mem_toFinset]
    exact ⟨w, hw, rfl⟩
  refine ⟨hS.toFinset, fun w hw => hT₁ w (Finset.mem_union_left _ hw), ?_, ?_⟩
  · intro w hw w' hw'
    rw [Set.Finite.mem_toFinset] at hw ⊢
    obtain ⟨u, hu, hwu⟩ := hw
    exact ⟨u, hu, hw'.trans hwu⟩
  · intro w hw x
    refine psiLoc_cond w ?_ x
    by_contra h
    exact hw (hT₁ w (Finset.mem_union_right _ (by simpa using h)))

end GlobalTheory.RSNonvan.GoodSet

theorem GlobalTheory.RSNonvan.exists_isGood_superset_all : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (T : Finset (HeightOneSpectrum (𝓞 E))), ∃ T' : Finset (HeightOneSpectrum (𝓞 E)), T ⊆ T' ∧ IsGood T' :=
  fun _ _ _ _ T => GlobalTheory.RSNonvan.GoodSet.exists_isGood_superset T

end
end
