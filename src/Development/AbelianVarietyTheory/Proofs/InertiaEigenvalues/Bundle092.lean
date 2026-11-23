module

public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerDistinguishedRegularSequence
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle052
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle051
public import ReciprocityTheory.GaloisValuations.SeparatedDvrSecondCohomologyMem
public import ReciprocityTheory.NeutralLocalFields.Bundle001
public import Formalism.ConjugateSelfDual.Bundle001
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.RingTheory.PowerSeries.Basic
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open scoped NNReal

theorem _root_.GlobalTheory.T.wittVector_ringHom_eq_map_of_coeff_zero : ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l] [PerfectRing R l] [CommRing O] [CharP O l] [PerfectRing O l] (F : WittVector l R →+* WittVector l O) (ψ : R →+* O), (∀ a, (F a).coeff 0 = ψ (a.coeff 0)) → F = WittVector.map ψ := by
  first | exact @GlobalTheory.WittMapUniq.eq_map_of_coeff_zero | exact GlobalTheory.WittMapUniq.eq_map_of_coeff_zero | (intros; apply GlobalTheory.WittMapUniq.eq_map_of_coeff_zero <;> assumption)
end

section

open scoped NNReal

theorem _root_.GlobalTheory.T.teichmuller_distinguished_regular_sequence : ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [CharP O l] [PerfectRing O l] (x : O) (e : ℕ) (w E' : WittVector l O), x ≠ 0 → 0 < e → IsUnit w → E' = WittVector.teichmuller l x ^ e + ((l : ℕ) : WittVector l O) * w → ∀ (k : ℕ) (a : WittVector l O), (WittVector.teichmuller l x ^ k ∣ E' * a → WittVector.teichmuller l x ^ k ∣ a) ∧ (E' ∣ WittVector.teichmuller l x ^ k * a → E' ∣ a) := by
  first | exact @GlobalTheory.teichmuller_distinguished_regular | exact GlobalTheory.teichmuller_distinguished_regular | (intros; apply GlobalTheory.teichmuller_distinguished_regular <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.prod_one_sub_bounded_below_of_summable : ∀ (ι : Type) (s : ι → ℝ), (∀ v, 0 ≤ s v) → (∀ v, s v < 1) → Summable s → ∃ δ : ℝ, 0 < δ ∧ ∀ S : Finset ι, δ ≤ ∏ v ∈ S, (1 - s v) := by
  first | exact @GlobalTheory.prod_one_sub_bounded_below | exact GlobalTheory.prod_one_sub_bounded_below | (intros; apply GlobalTheory.prod_one_sub_bounded_below <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.summable_finprod_of_finite_support_euler_sum : ∀ (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v) (a : ∀ v, X v → ℝ) (s : ι → ℝ), (∀ v x, 0 ≤ a v x) → (∀ v, a v (x0 v) = 1) → Summable s → (∀ v (C : Finset (X v)), x0 v ∉ C → ∑ x ∈ C, a v x ≤ s v) → Summable (fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => ∏ᶠ v, a v (f.1 v)) := by
  first | exact @GlobalTheory.summable_finprod_of_finite_support_euler | exact GlobalTheory.summable_finprod_of_finite_support_euler | (intros; apply GlobalTheory.summable_finprod_of_finite_support_euler <;> assumption)
end

section

open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory

theorem tendsto_const_pow_mul_pow_pow_zero : ∀ (C r : ℝ) (l : ℕ), 0 ≤ C → 0 ≤ r → r < 1 → 2 ≤ l →
    Tendsto (fun n : ℕ => C ^ n * r ^ (l ^ n)) atTop (𝓝 0) := by
  intro C r l hC hr hr1 hl
  have h1 : Tendsto (fun m : ℕ => C * r ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr hr1).const_mul C
  obtain ⟨m, hm⟩ := (h1.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/2))).exists
  have h2 : ∀ᶠ n : ℕ in atTop, m * n ≤ l ^ n := by
    have ht := (tendsto_pow_const_div_const_pow_of_one_lt 1 (by norm_num : (1:ℝ) < 2)).const_mul (m:ℝ)
    rw [mul_zero] at ht
    filter_upwards [ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hn
    have h2pos : (0:ℝ) < 2 ^ n := by positivity
    rw [pow_one, ← mul_div_assoc, div_lt_one h2pos] at hn
    have h3 : m * n ≤ 2 ^ n := by exact_mod_cast hn.le
    exact h3.trans (Nat.pow_le_pow_left hl n)
  have hbound : ∀ᶠ n : ℕ in atTop, C ^ n * r ^ (l ^ n) ≤ (1/2 : ℝ) ^ n := by
    filter_upwards [h2] with n hn
    calc C ^ n * r ^ (l ^ n) ≤ C ^ n * r ^ (m * n) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr hr1.le hn) (pow_nonneg hC n)
      _ = (C * r ^ m) ^ n := by rw [mul_pow, ← pow_mul]
      _ ≤ (1/2) ^ n := pow_le_pow_left₀ (by positivity) hm.le n
  exact squeeze_zero' (Eventually.of_forall fun n => by positivity) hbound
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

end GlobalTheory
end

section

open Polynomial

theorem _root_.GlobalTheory.T.window_around_last_max_null_sequence : ∀ (β : ℤ → ℝ) (c : ℝ) (h : ℕ), 0 < c → (∀ k, 0 ≤ β k) → (∃ k, β k ≠ 0) → Filter.Tendsto β Filter.cofinite (nhds 0) → ∃ (D E M : ℕ), h ≤ D ∧ M + h ≤ E ∧ 0 < β ((M + h : ℕ) - D) ∧ (∀ k, β k ≤ β ((M + h : ℕ) - D)) ∧ (∀ k, ((M + h : ℕ) : ℤ) - D < k → β k < β ((M + h : ℕ) - D)) ∧ ∀ k : ℤ, (k < -(D : ℤ) ∨ (E : ℤ) - D < k) → β k ≤ c * β ((M + h : ℕ) - D) := by
  first | exact @GlobalTheory.window_around_last_max | exact GlobalTheory.window_around_last_max | (intros; apply GlobalTheory.window_around_last_max <;> assumption)
end

section

open ReciprocityTheory.Gal

namespace GlobalTheory

theorem cocycle_lift_mod_uniformizer
    {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul O M] {G : Type} [Group G] [TopologicalSpace G]
    (ρ : Representation O G M) (hρ : ContAction ρ) (ϖ : O)
    (hemb : Topology.IsEmbedding (fun m : M => ϖ • m)) (s : Finset (Z1 ρ))
    (hs : ∀ c : Z1 ρ, ∃ i ∈ s, ∃ x : M, ∀ g, (c : G → M) g - (i : G → M) g - (ρ g x - x) ∈
      LinearMap.range (LinearMap.lsmul O M ϖ))
    (c : Z1 ρ) : ∃ (a : Z1 ρ → O) (c' : Z1 ρ) (x : M),
      (c : G → M) = ∑ i ∈ s, a i • (i : G → M) + ϖ • (c' : G → M) + d0 ρ x := by
  classical
  obtain ⟨i, his, x, hx⟩ := hs c
  let d : Z1 ρ := ⟨d0 ρ x, coboundaries_le_cocycles ρ hρ ⟨x, rfl⟩⟩
  let E : Z1 ρ := c - i - d
  have hE : ∀ g, (E : G → M) g = (c : G → M) g - (i : G → M) g - (ρ g x - x) := fun g => rfl
  have hx' : ∀ g, ∃ y : M, ϖ • y = (E : G → M) g := by
    intro g
    obtain ⟨y, hy⟩ := hx g
    exact ⟨y, by rw [hE]; simpa using hy⟩
  choose f hf using hx'
  have hfE : (fun g => ϖ • f g) = (E : G → M) := funext hf
  have hfc : Continuous f := by
    rw [hemb.continuous_iff]
    change Continuous (fun g => ϖ • f g)
    rw [hfE]
    exact E.2.1
  have hfco : ∀ g h, f (g * h) = f g + ρ g (f h) := by
    intro g h
    apply hemb.injective
    change ϖ • f (g * h) = ϖ • (f g + ρ g (f h))
    rw [smul_add, ← map_smul, hf, hf, hf]
    exact E.2.2 g h
  refine ⟨fun j => if j = i then 1 else 0, ⟨f, hfc, hfco⟩, x, ?_⟩
  have hsum : ∑ j ∈ s, (if j = i then (1 : O) else 0) • (j : G → M) = (i : G → M) := by
    simp only [ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq' s i (fun j => (j : G → M))]
    simp [his]
  rw [hsum]
  funext g
  have := hf g
  rw [hE] at this
  simp only [Pi.add_apply, Pi.smul_apply, amitsur_d0_apply]
  rw [this]
  abel

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Neutral.HilbertClassField

namespace GlobalTheory

theorem complexConjugation_mul_self {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (c : Ω ≃ₐ[E] Ω) (hc : IsComplexConjugation c) : c * c = 1 := by
  obtain ⟨j, hj⟩ := hc
  ext x
  apply j.injective
  show j (c (c x)) = j x
  rw [hj, hj, Complex.conj_conj]

theorem not_isComplexConjugation_of_nrRealPlaces_eq_zero {E Ω : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] (hE : InfinitePlace.nrRealPlaces E = 0)
    (c : Ω ≃ₐ[E] Ω) : ¬ IsComplexConjugation c := by
  rintro ⟨j, hj⟩
  let φ : E →+* ℂ := j.comp (algebraMap E Ω)
  have hφ : ComplexEmbedding.IsReal φ := by
    ext x
    show starRingEnd ℂ (j (algebraMap E Ω x)) = j (algebraMap E Ω x)
    rw [← hj, AlgEquiv.commutes]
  have hw : (InfinitePlace.mk φ).IsReal := InfinitePlace.isReal_mk_iff.mpr hφ
  have : IsEmpty {w : InfinitePlace E // w.IsReal} := by
    classical
    rw [InfinitePlace.nrRealPlaces] at hE
    exact Fintype.card_eq_zero_iff.mp (by convert hE)
  exact this.false ⟨_, hw⟩

theorem addHom_complexConjugation_eq_zero : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O],
    (l ≠ 2 ∨ InfinitePlace.nrRealPlaces E = 0) →
    ∀ (M : Type) [AddCommGroup M] [Module O M] (z : G E Ω → M), (∀ g h, z (g * h) = z g + z h) →
    ∀ (c : Ω ≃ₐ[E] Ω), IsComplexConjugation c → z c = 0 := by
  intro E Ω _ _ _ _ l _ O _ _ hl M _ _ z hz c hc
  rcases hl with hl | hE
  · have h1 : z 1 = 0 := by
      have := hz 1 1
      simp only [mul_one] at this
      simpa using this
    have h2 : z c + z c = 0 := by
      rw [← hz, show (c * c : G E Ω) = 1 from complexConjugation_mul_self c hc, h1]
    have hu : IsUnit (2 : ℤ_[l]) := by
      have := (PadicInt.norm_natCast_eq_one_iff (p := l) (n := 2)).mpr
        ((Nat.coprime_primes (Fact.out) Nat.prime_two).mpr hl)
      rw [PadicInt.isUnit_iff]; exact_mod_cast this
    have hu' : IsUnit (2 : O) := by
      have := hu.map (algebraMap ℤ_[l] O)
      rwa [map_ofNat] at this
    have h3 : (2 : O) • z c = 0 := by rw [two_smul]; exact h2
    exact (hu'.smul_left_cancel).mp (h3.trans (smul_zero _).symm)
  · exact absurd hc (not_isComplexConjugation_of_nrRealPlaces_eq_zero hE c)

end GlobalTheory
end
