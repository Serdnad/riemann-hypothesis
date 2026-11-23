module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.RingTheory.HahnSeries.Multiplication
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Ultra.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Data.Nat.Multiplicity
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

namespace GlobalTheory.NewPrime

theorem aeval_eq_zero_of_low_coeff_of_pow_eq_zero :
    ∀ (O B : Type) [CommRing O] [CommRing B] [Algebra O B] (ι : Type) (t : B) (K : ℕ) (ξ : ι → B)
      (F : MvPolynomial ι O), t ^ K = 0 → (∀ q, t ∣ ξ q) →
      (∀ u : ι →₀ ℕ, u.degree < K → algebraMap O B (F.coeff u) = 0) →
      MvPolynomial.aeval ξ F = 0 := by
  intro O B _ _ _ ι t K ξ F htK hdvd hlow
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Finset.sum_eq_zero fun u _ => ?_
  by_cases hu : u.degree < K
  · rw [hlow u hu, zero_mul]
  ·
    have hmon : t ^ u.degree ∣ ∏ i ∈ u.support, ξ i ^ u i := by
      rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => pow_dvd_pow_of_dvd (hdvd i) _
    have hK : t ^ K ∣ ∏ i ∈ u.support, ξ i ^ u i :=
      (pow_dvd_pow t (not_lt.mp hu)).trans hmon
    rw [htK, zero_dvd_iff] at hK
    rw [hK, mul_zero]

end GlobalTheory.NewPrime
end

section

open scoped BigOperators

namespace GlobalTheory

open scoped BigOperators in
private theorem C_dvd_prod_pow_sub_X_pow_sum_of_C_dvd {O σ : Type} [CommRing O] [Fintype σ] (ϖ : O)
    (g : σ → Polynomial O) (k : σ → ℕ) (hg : ∀ q, Polynomial.C ϖ ∣ g q - Polynomial.X ^ k q)
    (m : σ → ℕ) :
    Polynomial.C ϖ ∣ ∏ q, g q ^ m q - Polynomial.X ^ (∑ q, m q * k q) := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  rw [← Finset.prod_pow_eq_pow_sum, map_prod, map_prod]
  refine Finset.prod_congr rfl fun q _ => ?_
  have hq := Ideal.Quotient.eq.2 (Ideal.mem_span_singleton.2 (hg q))
  rw [map_pow, hq, ← map_pow, ← pow_mul, mul_comm]

open scoped BigOperators in
private theorem C_dvd_one_add_X_pow_prime_pow_sub_one_sub_X_pow {O : Type} [CommRing O] (ϖ : O) (l e : ℕ)
    (hl : l.Prime) (h : ϖ ∣ (l : O)) :
    Polynomial.C ϖ ∣ (1 + Polynomial.X : Polynomial O) ^ (l ^ e) - 1 - Polynomial.X ^ (l ^ e) := by
  rw [Polynomial.C_dvd_iff_dvd_coeff]
  intro i
  simp only [Polynomial.coeff_sub, Polynomial.coeff_one_add_X_pow, Polynomial.coeff_one,
    Polynomial.coeff_X_pow]
  have hN : l ^ e ≠ 0 := (pow_pos hl.pos _).ne'
  by_cases h0 : i = 0
  · subst h0
    simp [hN.symm]
  by_cases hN' : i = l ^ e
  · subst hN'
    simp [h0, hl.ne_zero]
  · simp only [h0, hN', if_false, sub_zero]
    exact h.trans (Nat.cast_dvd_cast (hl.dvd_choose_pow h0 hN'))


open scoped BigOperators in
theorem _root_.GlobalTheory.not_dvd_coeff_aeval_oneAddX_pow_sub_one :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (σ : Type) [Fintype σ] (l μ : ℕ), l.Prime → ϖ ∣ (l : O) → ∀ (F : MvPolynomial σ O) (e : σ → ℕ) (m₀ : σ →₀ ℕ), (∀ m : σ →₀ ℕ, m.degree ≤ ∑ q, m₀ q * l ^ e q → ϖ ^ μ ∣ F.coeff m) → ¬ ϖ ^ (μ + 1) ∣ F.coeff m₀ → (∀ m : σ →₀ ℕ, m ≠ m₀ → ∑ q, m q * l ^ e q ≤ ∑ q, m₀ q * l ^ e q → ϖ ^ (μ + 1) ∣ F.coeff m) → ¬ ϖ ^ (μ + 1) ∣ (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) F).coeff (∑ q, m₀ q * l ^ e q) := by
  intro O _ _ _ ϖ _ σ _ l μ hl hϖl F e m₀ hlow hm₀ hoth
  classical
  set W := ∑ q, m₀ q * l ^ e q with hW
  set g : σ → Polynomial O := fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1 with hgdef
  set c : (σ →₀ ℕ) → O := fun m => (∏ q, g q ^ m q).coeff W with hc
  have hexp : (MvPolynomial.aeval g F).coeff W = ∑ m ∈ F.support, F.coeff m * c m := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Polynomial.algebraMap_eq, Polynomial.coeff_C_mul]
  have hcong : ∀ m : σ →₀ ℕ, ϖ ∣ c m - if W = ∑ q, m q * l ^ e q then 1 else 0 := by
    intro m
    have h := (Polynomial.C_dvd_iff_dvd_coeff _ _).1 (C_dvd_prod_pow_sub_X_pow_sum_of_C_dvd ϖ g (fun q => l ^ e q)
      (fun q => by simpa [g] using C_dvd_one_add_X_pow_prime_pow_sub_one_sub_X_pow ϖ l (e q) hl hϖl) m) W
    simpa [Polynomial.coeff_X_pow] using h
  have hvanish : ∀ m : σ →₀ ℕ, W < m.degree → c m = 0 := by
    intro m hm
    have hX : ∀ q, Polynomial.X ∣ g q := fun q => by
      rw [Polynomial.X_dvd_iff]
      simp [g, Polynomial.coeff_one_add_X_pow]
    have hdvd : Polynomial.X ^ (∑ q, m q) ∣ ∏ q, g q ^ m q := by
      rw [← Finset.prod_pow_eq_pow_sum]
      exact Finset.prod_dvd_prod_of_dvd _ _ fun q _ => pow_dvd_pow_of_dvd (hX q) _
    rw [Finsupp.degree_eq_sum] at hm
    exact (Polynomial.X_pow_dvd_iff.1 hdvd) W hm
  have hdeg : ∀ m : σ →₀ ℕ, m.degree ≤ ∑ q, m q * l ^ e q := by
    intro m
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_le_sum fun q _ => Nat.le_mul_of_pos_right _ (pow_pos hl.pos _)
  have hterm : ∀ m, m ≠ m₀ → ϖ ^ (μ + 1) ∣ F.coeff m * c m := by
    intro m hne
    by_cases hw : ∑ q, m q * l ^ e q ≤ W
    · exact dvd_mul_of_dvd_left (hoth m hne hw) _
    by_cases hd : m.degree ≤ W
    · have h1 := hcong m
      rw [if_neg (by omega), sub_zero] at h1
      rw [pow_succ]
      exact mul_dvd_mul (hlow m hd) h1
    · rw [hvanish m (by omega), mul_zero]
      exact dvd_zero _
  have hmain : ϖ ^ (μ + 1) ∣ F.coeff m₀ * c m₀ - F.coeff m₀ := by
    have h1 := hcong m₀
    rw [if_pos rfl] at h1
    rw [← mul_sub_one, pow_succ]
    exact mul_dvd_mul (hlow m₀ (hdeg m₀)) h1
  have hmem : m₀ ∈ F.support := by
    rw [MvPolynomial.mem_support_iff]
    intro h0
    exact hm₀ (h0 ▸ dvd_zero _)
  intro hdiv
  rw [hexp, ← Finset.add_sum_erase _ _ hmem] at hdiv
  have hrest : ϖ ^ (μ + 1) ∣ ∑ m ∈ F.support.erase m₀, F.coeff m * c m :=
    Finset.dvd_sum fun m hm => hterm m (Finset.ne_of_mem_erase hm)
  have h2 := (dvd_add_left hrest).1 hdiv
  exact hm₀ (by simpa using dvd_sub h2 hmain)

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory

theorem laurent_degeneration_abstract (k : Type) [Field k] (K : Type) [Field K] [Algebra k K] (σ : K)
    (O : K → Prop) (π0 π1 : K →ₗ[k] k) (h0 : ∀ z, O z → π0 (σ * z) = 0)
    (h1 : ∀ z, π1 (σ * z) = π0 z) (hone : π0 1 = 1)
    (hnorm : ∀ (a : ℕ) (y : Fin a → K), y ≠ 0 → ∃ (f : K) (c0 : Fin a), f * y c0 = 1 ∧ ∀ c, O (f * y c))
    (a e : ℕ) (V : Submodule k (Fin a → k)) (U : Type) [AddCommGroup U] [Module k U]
    (t u : V →ₗ[k] U) (he : e ≤ 1)
    (H : ∀ x0 x1 : Fin (e + 1) → V, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) →
      ¬ LinearIndependent k x0)
    (y : Fin (e + 1) → Fin a → K)
    (hy : ∀ j (π : K →ₗ[k] k), ∃ x x' : V, (∀ c, x.1 c = π (y j c)) ∧
      (∀ c, x'.1 c = π (σ * y j c)) ∧ t x = u x') :
    ¬ LinearIndependent K y := by
  let P : (Fin a → K) → Prop := fun z => ∀ (π : K →ₗ[k] k), ∃ x x' : V, (∀ c, x.1 c = π (z c)) ∧
      (∀ c, x'.1 c = π (σ * z c)) ∧ t x = u x'
  have Psmul : ∀ (f : K) z, P z → P (f • z) := by
    intro f z hz π
    obtain ⟨x, x', h, h', h''⟩ := hz (π ∘ₗ LinearMap.mulLeft k f)
    refine ⟨x, x', fun c => by simpa using h c, fun c => ?_, h''⟩
    rw [h' c]
    simp [mul_left_comm]
  have Psub : ∀ z w, P z → P w → P (z - w) := by
    intro z w hz hw π
    obtain ⟨x, x', h, h', h''⟩ := hz π
    obtain ⟨v, v', g, g', g''⟩ := hw π
    refine ⟨x - v, x' - v', fun c => by simp [h c, g c], fun c => by simp [h' c, g' c, mul_sub],
      by simp [h'', g'']⟩
  have key : ∀ z, P z → z ≠ 0 → ∃ (f : K) (c0 : Fin a) (x0 x1 : V), f * z c0 = 1 ∧
      (∀ c, x0.1 c = π0 (f * z c)) ∧ t x0 = 0 ∧ t x1 = u x0 := by
    intro z hz hz0
    obtain ⟨f, c0, hf, hO⟩ := hnorm a z hz0
    have hP := Psmul f z hz
    obtain ⟨x, x', h, h', h''⟩ := hP π0
    obtain ⟨v, v', g, g', g''⟩ := hP π1
    have hx' : x' = 0 := by
      ext c
      rw [h' c]
      simpa using h0 _ (hO c)
    have hv' : v' = x := by
      ext c
      rw [g' c, h c, h1]
    refine ⟨f, c0, x, v, hf, fun c => by simpa using h c, by rw [h'', hx', map_zero],
      by rw [g'', hv']⟩
  intro hli
  obtain rfl | rfl : e = 0 ∨ e = 1 := by omega
  · obtain ⟨f, c0, x0, x1, hf, hx, ht, ht'⟩ := key (y 0) (hy 0) (hli.ne_zero 0)
    refine H (fun _ => x0) (fun _ => x1) (fun _ => ⟨ht, ht'⟩) ?_
    have hne : x0 ≠ 0 := by
      intro h
      have := hx c0
      rw [h, hf, hone] at this
      simp at this
    exact (linearIndependent_unique_iff (ι := Fin 1) (v := fun _ => x0)).2 hne
  · obtain ⟨f, c0, x0, x1, hf, hx, ht, ht'⟩ := key (y 0) (hy 0) (hli.ne_zero 0)
    have hw : y 1 - (y 1 c0 * f) • y 0 ≠ 0 := by
      intro h
      have hy2 : y = ![y 0, y 1] := by
        ext i : 1
        fin_cases i <;> rfl
      rw [hy2, LinearIndependent.pair_iff] at hli
      have := (hli (-(y 1 c0 * f)) 1 (by rw [← h]; simp [sub_eq_neg_add])).2
      exact one_ne_zero this
    obtain ⟨g, c1, z0, z1, hg, hz, hs, hs'⟩ :=
      key _ (Psub _ _ (hy 1) (Psmul (y 1 c0 * f) _ (hy 0))) hw
    have e1 : x0.1 c0 = 1 := by rw [hx, hf, hone]
    have e2 : z0.1 c0 = 0 := by
      rw [hz]
      simp [mul_assoc, hf]
    have e3 : z0.1 c1 = 1 := by rw [hz, hg, hone]
    refine H ![x0, z0] ![x1, z1] (fun j => by fin_cases j <;> simp [ht, ht', hs, hs']) ?_
    rw [LinearIndependent.pair_iff]
    intro s r h
    have a0 := congrArg (fun v : V => v.1 c0) h
    have a1 := congrArg (fun v : V => v.1 c1) h
    simp [e1, e2] at a0
    simp [a0, e3] at a1
    exact ⟨a0, a1⟩

theorem laurent_vector_normalise (k : Type) [Field k] (a : ℕ) (y : Fin a → HahnSeries ℤ k)
    (hy : y ≠ 0) : ∃ (f : HahnSeries ℤ k) (c0 : Fin a), f * y c0 = 1 ∧
      ∀ c, (f * y c).coeff (-1) = 0 := by
  classical
  have hne : (Finset.univ.filter fun c => y c ≠ 0).Nonempty := by
    obtain ⟨c, hc⟩ := Function.ne_iff.1 hy
    exact ⟨c, by simpa using hc⟩
  obtain ⟨c0, hc0, hmin⟩ := Finset.exists_min_image _ (fun c => (y c).order) hne
  have h0 : y c0 ≠ 0 := by simpa using hc0
  refine ⟨(y c0)⁻¹, c0, inv_mul_cancel₀ h0, fun c => ?_⟩
  by_cases hc : y c = 0
  · simp [hc]
  · have h1 := hmin c (by simpa using hc)
    have h2 := HahnSeries.order_mul (inv_ne_zero h0) h0
    rw [inv_mul_cancel₀ h0, HahnSeries.order_one] at h2
    apply HahnSeries.coeff_eq_zero_of_lt_order
    rw [HahnSeries.order_mul (inv_ne_zero h0) hc]
    omega

noncomputable def laurentCoeffForm (k : Type) [Field k] (n : ℤ) :
    letI : Algebra k (HahnSeries ℤ k) := HahnSeries.instAlgebra
    HahnSeries ℤ k →ₗ[k] k :=
  HahnSeries.coeff.linearMap n

theorem laurent_degeneration : ∀ (k : Type) [Field k], ∃ (K : Type) (_ : Field K) (_ : Algebra k K) (σ : K), ∀ (a e : ℕ) (V : Submodule k (Fin a → k)) (U : Type) [AddCommGroup U] [Module k U] (t u : V →ₗ[k] U), e ≤ 1 → (∀ x0 x1 : Fin (e + 1) → V, (∀ j, t (x0 j) = 0 ∧ t (x1 j) = u (x0 j)) → ¬ LinearIndependent k x0) → ∀ y : Fin (e + 1) → Fin a → K, (∀ j (π : K →ₗ[k] k), ∃ x x' : V, (∀ c, x.1 c = π (y j c)) ∧ (∀ c, x'.1 c = π (σ * y j c)) ∧ t x = u x') → ¬ LinearIndependent K y := by
  intro k _
  letI : Algebra k (HahnSeries ℤ k) := HahnSeries.instAlgebra
  refine ⟨HahnSeries ℤ k, inferInstance, this, HahnSeries.single 1 1, ?_⟩
  intro a e V U _ _ t u
  have hs : ∀ (z : HahnSeries ℤ k) (n : ℤ),
      (HahnSeries.single (1 : ℤ) (1 : k) * z).coeff (n + 1) = z.coeff n := by
    intro z n
    rw [HahnSeries.coeff_single_mul_add, one_mul]
  refine laurent_degeneration_abstract k (HahnSeries ℤ k) (HahnSeries.single 1 1)
    (fun z => z.coeff (-1) = 0) (laurentCoeffForm k 0) (laurentCoeffForm k 1) ?_ ?_ ?_
    (laurent_vector_normalise k) a e V U t u
  · intro z hz
    exact (hs z (-1)).trans hz
  · intro z
    exact hs z 0
  · show (1 : HahnSeries ℤ k).coeff 0 = 1
    simp

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory

theorem newton_step_root_in_disc :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ),
      0 < ρ → ‖a‖ ≤ ρ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) →
      (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) →
      (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1)) ∧
        ∀ j, d + 1 < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j <
          ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1) := by
  intro K _ _ g a ρ d hρ ha hle hlt
  have hsub : ∀ x y : K, ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
    intro x y
    simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)
  have hcoef : ∀ k, ((X - C a) * g).coeff (k + 1) = g.coeff k - g.coeff (k + 1) * a := by
    intro k
    rw [mul_comm]
    exact coeff_mul_X_sub_C
  have hcoef0 : ((X - C a) * g).coeff 0 = -a * g.coeff 0 := by
    rw [mul_coeff_zero]
    simp

  have hM : 0 < ‖g.coeff d‖ * ρ ^ d := by
    have h := hlt (d + 1) (Nat.lt_succ_self d)
    have : 0 ≤ ‖g.coeff (d + 1)‖ * ρ ^ (d + 1) := by positivity
    linarith
  have hsmall : ‖g.coeff (d + 1) * a‖ < ‖g.coeff d‖ := by
    rw [norm_mul]
    have hp : 0 < ρ ^ (d + 1) := by positivity
    have h := hlt (d + 1) (Nat.lt_succ_self d)
    have hn : 0 ≤ ‖g.coeff (d + 1)‖ * ρ ^ (d + 1) := by positivity
    have h2 : ‖g.coeff (d + 1)‖ * ‖a‖ * ρ ^ (d + 1) < ‖g.coeff d‖ * ρ ^ (d + 1) := by
      calc ‖g.coeff (d + 1)‖ * ‖a‖ * ρ ^ (d + 1)
          = (‖g.coeff (d + 1)‖ * ρ ^ (d + 1)) * ‖a‖ := by ring
        _ ≤ (‖g.coeff (d + 1)‖ * ρ ^ (d + 1)) * ρ := mul_le_mul_of_nonneg_left ha hn
        _ < (‖g.coeff d‖ * ρ ^ d) * ρ := mul_lt_mul_of_pos_right h hρ
        _ = ‖g.coeff d‖ * ρ ^ (d + 1) := by ring
    exact lt_of_mul_lt_mul_right h2 hp.le
  have htopn : ‖((X - C a) * g).coeff (d + 1)‖ = ‖g.coeff d‖ := by
    rw [hcoef d, sub_eq_add_neg,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact hsmall.ne'),
      norm_neg]
    exact max_eq_left hsmall.le
  have htop : ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1) = ρ * (‖g.coeff d‖ * ρ ^ d) := by
    rw [htopn]; ring

  have key : ∀ k, ‖((X - C a) * g).coeff (k + 1)‖ * ρ ^ (k + 1) ≤
      max (ρ * (‖g.coeff k‖ * ρ ^ k)) (ρ * (‖g.coeff (k + 1)‖ * ρ ^ (k + 1))) := by
    intro k
    rw [hcoef k]
    have h1 := hsub (g.coeff k) (g.coeff (k + 1) * a)
    rw [norm_mul] at h1
    have hp : 0 ≤ ρ ^ (k + 1) := by positivity
    have hn : 0 ≤ ‖g.coeff (k + 1)‖ * ρ ^ (k + 1) := by positivity
    calc ‖g.coeff k - g.coeff (k + 1) * a‖ * ρ ^ (k + 1)
        ≤ max ‖g.coeff k‖ (‖g.coeff (k + 1)‖ * ‖a‖) * ρ ^ (k + 1) :=
          mul_le_mul_of_nonneg_right h1 hp
      _ = max (‖g.coeff k‖ * ρ ^ (k + 1)) (‖g.coeff (k + 1)‖ * ‖a‖ * ρ ^ (k + 1)) :=
          max_mul_of_nonneg _ _ hp
      _ ≤ max (ρ * (‖g.coeff k‖ * ρ ^ k)) (ρ * (‖g.coeff (k + 1)‖ * ρ ^ (k + 1))) := by
          apply max_le_max
          · exact le_of_eq (by ring)
          · calc ‖g.coeff (k + 1)‖ * ‖a‖ * ρ ^ (k + 1)
                = (‖g.coeff (k + 1)‖ * ρ ^ (k + 1)) * ‖a‖ := by ring
              _ ≤ (‖g.coeff (k + 1)‖ * ρ ^ (k + 1)) * ρ := mul_le_mul_of_nonneg_left ha hn
              _ = ρ * (‖g.coeff (k + 1)‖ * ρ ^ (k + 1)) := by ring
  constructor
  · intro j
    rw [htop]
    cases j with
    | zero =>
      rw [hcoef0, norm_mul, norm_neg, pow_zero, mul_one]
      have h0 := hle 0
      rw [pow_zero, mul_one] at h0
      calc ‖a‖ * ‖g.coeff 0‖ ≤ ρ * ‖g.coeff 0‖ :=
            mul_le_mul_of_nonneg_right ha (norm_nonneg _)
        _ ≤ ρ * (‖g.coeff d‖ * ρ ^ d) := mul_le_mul_of_nonneg_left h0 hρ.le
    | succ k =>
      exact (key k).trans (max_le (mul_le_mul_of_nonneg_left (hle k) hρ.le)
        (mul_le_mul_of_nonneg_left (hle (k + 1)) hρ.le))
  · intro j hj
    rw [htop]
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact (key k).trans_lt (max_lt (mul_lt_mul_of_pos_left (hlt k (by omega)) hρ)
      (mul_lt_mul_of_pos_left (hlt (k + 1) (by omega)) hρ))

end GlobalTheory
end

section

namespace GlobalTheory

theorem sq_dvd_choose_prime_pow (l : ℕ) (hl : l.Prime) (b k : ℕ) (hb : 1 ≤ b) (hk0 : k ≠ 0)
    (hk : k < l ^ (b - 1)) : l ^ 2 ∣ (l ^ b).choose k := by
  haveI : Fact l.Prime := ⟨hl⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := Nat.exists_eq_succ_of_ne_zero hk0
  obtain ⟨m, hm⟩ : ∃ m, l ^ b = m + 1 := Nat.exists_eq_succ_of_ne_zero (pow_pos hl.pos b).ne'
  have hkb : j + 1 ≤ l ^ b := le_trans hk.le (Nat.pow_le_pow_right hl.pos (Nat.sub_le b 1))
  have hC : (l ^ b).choose (j + 1) ≠ 0 := (Nat.choose_pos hkb).ne'

  have hid : l ^ b * m.choose j = (l ^ b).choose (j + 1) * (j + 1) := by
    rw [hm]; exact Nat.add_one_mul_choose_eq m j

  have hv : padicValNat l (j + 1) < b - 1 := by
    by_contra hcon
    push_neg at hcon
    have h1 : l ^ padicValNat l (j + 1) ≤ j + 1 :=
      Nat.le_of_dvd (Nat.succ_pos j) (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
    have h2 : l ^ (b - 1) ≤ l ^ padicValNat l (j + 1) := Nat.pow_le_pow_right hl.pos hcon
    omega
  have hdiv : l ^ b ∣ (l ^ b).choose (j + 1) * (j + 1) := by
    rw [← hid]; exact dvd_mul_right _ _
  have hne : (l ^ b).choose (j + 1) * (j + 1) ≠ 0 := mul_ne_zero hC (Nat.succ_ne_zero j)
  rw [(by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hne, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hC (by omega : j + 1 ≠ 0)] at hdiv
  exact ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hC).mpr (by omega)

theorem one_add_X_pow_prime_pow_sub_one_mem_span (l : ℕ) [Fact l.Prime] (b : ℕ) (hb : 1 ≤ b) :
    ((1 + Polynomial.X) ^ (l ^ b) - 1 : Polynomial ℤ) ∈
      Ideal.span {((l : Polynomial ℤ)) ^ 2, Polynomial.X ^ (l ^ (b - 1))} := by

  have key : ((1 + Polynomial.X) ^ (l ^ b) - 1 : Polynomial ℤ) =
      ∑ i ∈ Finset.range (l ^ b),
        Polynomial.X ^ (i + 1) * (((l ^ b).choose (i + 1) : ℕ) : Polynomial ℤ) := by
    rw [add_comm, add_pow, Finset.sum_range_succ']
    simp
  rw [key]
  refine Ideal.sum_mem _ (fun i _ => ?_)
  by_cases hi : i + 1 < l ^ (b - 1)
  ·
    obtain ⟨c, hc⟩ := sq_dvd_choose_prime_pow l (Fact.out) b (i + 1) hb (Nat.succ_ne_zero i) hi
    rw [hc, Nat.cast_mul, Nat.cast_pow, mul_left_comm]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_insert _ _))
  ·
    push_neg at hi
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hi
    rw [hd, pow_add, mul_assoc]
    exact Ideal.mul_mem_right _ _
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

end GlobalTheory
end

section

namespace GlobalTheory

theorem matrix_mul_entry_norm_le_ultrametric :
    ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n]
      (A B : Matrix n n E) (a b : ℝ), 0 ≤ a → 0 ≤ b → (∀ i j, ‖A i j‖ ≤ a) → (∀ i j, ‖B i j‖ ≤ b) →
      ∀ i j, ‖(A * B) i j‖ ≤ a * b := by
  intro E _ _ n _ _ A B a b ha hb hA hB i j
  rw [Matrix.mul_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha hb)
  intro k _
  rw [norm_mul]
  exact mul_le_mul (hA i k) (hB k j) (norm_nonneg _) ha

end GlobalTheory
end
