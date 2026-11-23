module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Ring.Hom.InjSurj
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Integral

@[expose] public section

section

open Module Filter Topology

namespace GlobalTheory

theorem eq_zero_of_forall_pow_nsmul {X : Type} [AddCommGroup X] [Module.Free ℤ X] {n : ℕ}
    (hn : 2 ≤ n) {x : X} (hx : ∀ j : ℕ, ∃ μ : X, x = n ^ j • μ) : x = 0 := by
  let b := Module.Free.chooseBasis ℤ X
  apply b.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  obtain ⟨μ, hμ⟩ := hx (b.repr x i).natAbs
  have hd : ((n : ℤ) ^ (b.repr x i).natAbs) ∣ b.repr x i := by
    refine ⟨b.repr μ i, ?_⟩
    conv_lhs => rw [hμ]
    simp [map_nsmul]
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self (by omega)

theorem tendsto_tsum_zero_of_eventually_notMem_range {K X Y : Type} [NontriviallyNormedField K]
    [IsUltrametricDist K] (τ : X → K) (hτ : Tendsto τ cofinite (𝓝 0)) (f : ℕ → Y → X)
    (hf : ∀ z, τ z ≠ 0 → ∀ᶠ j in atTop, ∀ μ, f j μ ≠ z) :
    Tendsto (fun j => ∑' μ, τ (f j μ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hS : {z | ¬ ‖τ z‖ < ε / 2}.Finite := by
    have := hτ (Metric.ball_mem_nhds (0 : K) (half_pos hε))
    rw [Filter.mem_map, Filter.mem_cofinite] at this
    convert this using 1
    ext z
    simp
  have hev : ∀ᶠ j in atTop, ∀ z ∈ {z | ¬ ‖τ z‖ < ε / 2}, ∀ μ, f j μ ≠ z :=
    (hS.eventually_all).2 fun z hz => hf z (fun h0 => hz (by rw [h0, norm_zero]; exact half_pos hε))
  filter_upwards [hev] with j hj
  rw [dist_zero_right]
  refine lt_of_le_of_lt
    (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (half_pos hε).le fun μ => ?_) (half_lt_self hε)
  by_contra h
  exact hj (f j μ) (show ¬ ‖τ (f j μ)‖ < ε / 2 from fun h' => h h'.le) μ rfl

theorem mem_class_of_le {X : Type} [AddCommGroup X] {n : ℕ} {α : ℕ → X}
    (hα : ∀ j, ∃ μ, α (j + 1) = α j + n ^ j • μ) {z : X} {j k : ℕ} (hjk : j ≤ k)
    (hz : ∃ μ, z = α k + n ^ k • μ) : ∃ μ, z = α j + n ^ j • μ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  clear hjk
  induction d generalizing z with
  | zero => simpa using hz
  | succ d ih =>
    obtain ⟨μ, rfl⟩ := hz
    obtain ⟨ν, hν⟩ := hα (j + d)
    apply ih
    refine ⟨ν + n • μ, ?_⟩
    rw [← add_assoc, hν, pow_succ, mul_smul, smul_add]
    abel

theorem tendsto_tsum_pow_classes :
    ∀ (K X : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (n : ℕ), 2 ≤ n →
      ∀ (σ : X → K), Filter.Tendsto σ Filter.cofinite (nhds 0) → ∀ α : ℕ → X,
      (∀ j, ∃ μ, α (j + 1) = α j + n ^ j • μ) →
      (∀ χ : X, (∀ j, ∃ μ, χ = α j + n ^ j • μ) →
        Filter.Tendsto (fun j => ∑' μ, σ (α j + n ^ j • μ)) Filter.atTop (nhds (σ χ))) ∧
      ((¬ ∃ χ : X, ∀ j, ∃ μ, χ = α j + n ^ j • μ) →
        Filter.Tendsto (fun j => ∑' μ, σ (α j + n ^ j • μ)) Filter.atTop (nhds 0)) := by
  classical
  intro K X _ _ _ _ _ _ n hn σ hσ α hα
  have hinj : ∀ j, Function.Injective (fun μ : X => α j + n ^ j • μ) := by
    intro j μ ν h
    simp only [add_right_inj] at h
    have hne : ((n ^ j : ℕ) : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero j (by omega : n ≠ 0)
    have h' : ((n ^ j : ℕ) : ℤ) • μ = ((n ^ j : ℕ) : ℤ) • ν := by
      rw [natCast_zsmul, natCast_zsmul]
      exact h
    exact smul_right_injective X hne h'
  have hsum : ∀ τ : X → K, Tendsto τ cofinite (𝓝 0) → ∀ j, Summable (fun μ => τ (α j + n ^ j • μ)) :=
    fun τ hτ j => NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (hτ.comp (hinj j).tendsto_cofinite)
  have hfar : ∀ z w : X, z ≠ w → ∀ᶠ j in atTop, ¬ ∃ μ, z = w + n ^ j • μ := by
    intro z w hzw
    by_contra h
    rw [Filter.not_eventually] at h
    simp only [not_not] at h
    apply hzw
    have h0 : z - w = 0 := by
      refine eq_zero_of_forall_pow_nsmul hn (fun j => ?_)
      obtain ⟨i, ⟨μ, hμ⟩, hji⟩ := (h.and_eventually (eventually_ge_atTop j)).exists
      refine ⟨n ^ (i - j) • μ, ?_⟩
      rw [hμ, add_sub_cancel_left, ← mul_smul, ← pow_add, Nat.add_sub_cancel' hji]
    exact sub_eq_zero.mp h0
  constructor
  · intro χ hχ
    let τ := Function.update σ χ 0
    have hτ : Tendsto τ cofinite (𝓝 0) := by
      apply hσ.congr'
      filter_upwards [(Set.finite_singleton χ).compl_mem_cofinite] with z hz
      simp [τ, Set.mem_compl_singleton_iff.mp hz]
    have h2 := tendsto_tsum_zero_of_eventually_notMem_range τ hτ (fun j μ => α j + n ^ j • μ) (by
      intro z hz
      have hzχ : z ≠ χ := by
        rintro rfl
        simp [τ] at hz
      filter_upwards [hfar z χ hzχ] with j hj μ hμ
      apply hj
      obtain ⟨ν, hν⟩ := hχ j
      have hμ' : z = α j + n ^ j • μ := hμ.symm
      refine ⟨μ - ν, ?_⟩
      rw [hμ', hν, smul_sub]
      abel)
    have heq : ∀ j, ∑' μ, σ (α j + n ^ j • μ) = σ χ + ∑' μ, τ (α j + n ^ j • μ) := by
      intro j
      obtain ⟨μj, hμj⟩ := hχ j
      rw [(hsum σ hσ j).tsum_eq_add_tsum_ite μj]
      congr 1
      · rw [hμj]
      · refine tsum_congr fun μ => ?_
        by_cases h : μ = μj
        · subst h
          simp [τ, ← hμj]
        · have hne : α j + n ^ j • μ ≠ χ := fun h' => h (hinj j (h'.trans hμj))
          simp [τ, h, hne]
    have h3 := tendsto_const_nhds (x := σ χ) |>.add h2
    rw [add_zero] at h3
    exact h3.congr (fun j => (heq j).symm)
  · intro hno
    apply tendsto_tsum_zero_of_eventually_notMem_range σ hσ (fun j μ => α j + n ^ j • μ)
    intro z _
    obtain ⟨j0, hj0⟩ : ∃ j0, ¬ ∃ μ, z = α j0 + n ^ j0 • μ := by
      by_contra h
      exact hno ⟨z, fun j => by
        by_contra h'
        exact h ⟨j, h'⟩⟩
    filter_upwards [eventually_ge_atTop j0] with j hj μ hμ
    exact hj0 (mem_class_of_le hα hj ⟨μ, hμ.symm⟩)

end GlobalTheory
end

section

open scoped BigOperators

namespace GlobalTheory

theorem hasSum_conv_of_ultrametric {C : Type} [NormedField C] [IsUltrametricDist C]
    {X : Type} [AddCommGroup X] {a a' a'' : X → C} {S S' : C}
    (h : HasSum a S) (h' : HasSum a' S')
    (hc : ∀ α, HasSum (fun χ => a χ * a' (α - χ)) (a'' α)) : HasSum a'' (S * S') := by
  have : NonarchimedeanRing C := ⟨fun U hU => NonarchimedeanAddGroup.is_nonarchimedean U hU⟩
  have hp : HasSum (fun i : X × X => a i.1 * a' i.2) (S * S') := h.mul_of_nonarchimedean h'
  let e : X × X ≃ X × X :=
    { toFun := fun p => (p.2, p.1 - p.2)
      invFun := fun q => (q.1 + q.2, q.1)
      left_inv := by rintro ⟨x, y⟩; simp
      right_inv := by rintro ⟨x, y⟩; simp }
  have hq : HasSum (fun p : X × X => a p.2 * a' (p.1 - p.2)) (S * S') := e.hasSum_iff.2 hp
  exact hq.prod_fiberwise hc

theorem hasSum_graded_of_mul_degree :
    ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] (X : Type) [AddCommGroup X] (Rel : ℕ → (X → C) → C → Prop) (n k : ℕ), 1 ≤ n → 1 ≤ k → (∀ (l l' : ℕ) (a a' : X → C) (c c' : C), 1 ≤ l → 1 ≤ l' → Rel l a c → Rel l' a' c' → ∃ a'', Rel (l + l') a'' (c * c') ∧ ∀ α, HasSum (fun χ => a χ * a' (α - χ)) (a'' α)) → (∃ κ : C, κ ≠ 0 ∧ ∀ a c, Rel (n * k) a c → HasSum a (κ * c)) → ∃ u : C, u ≠ 0 ∧ ∀ a c, Rel k a c → Summable a → HasSum a (u * c) := by
  intro C _ _ _ X _ Rel n k hn hk hmul hkap
  obtain ⟨κ, hκ, hkap⟩ := hkap
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩

  have key : ∀ a c S, Rel k a c → HasSum a S → ∀ b d T, Rel k b d → HasSum b T →
      ∀ j : ℕ, ∃ e, Rel ((j + 1) * k) e (c ^ j * d) ∧ HasSum e (S ^ j * T) := by
    intro a c S hac hS b d T hbd hT j
    induction j with
    | zero => exact ⟨b, by simpa using hbd, by simpa using hT⟩
    | succ j ih =>
      obtain ⟨e, he, heT⟩ := ih
      have hjk : 1 ≤ (j + 1) * k := le_trans hk (Nat.le_mul_of_pos_left k (Nat.succ_pos j))
      obtain ⟨e', he', hconv⟩ := hmul ((j + 1) * k) k e a (c ^ j * d) c hjk hk he hac
      refine ⟨e', ?_, ?_⟩
      · have h2 : (j + 1) * k + k = (j + 1 + 1) * k := by ring
        have h3 : c ^ j * d * c = c ^ (j + 1) * d := by ring
        rw [h2, h3] at he'
        exact he'
      · have h4 := hasSum_conv_of_ultrametric heT hS hconv
        have h5 : S ^ j * T * S = S ^ (j + 1) * T := by ring
        rw [h5] at h4
        exact h4
  have eqn : ∀ a c S, Rel k a c → HasSum a S → ∀ b d T, Rel k b d → HasSum b T →
      S ^ m * T = κ * (c ^ m * d) := by
    intro a c S hac hS b d T hbd hT
    obtain ⟨e, he, heT⟩ := key a c S hac hS b d T hbd hT m
    exact heT.unique (hkap e _ he)
  by_cases hex : ∃ a c, Rel k a c ∧ Summable a ∧ c ≠ 0
  · obtain ⟨a, c, hac, hsa, hc0⟩ := hex
    set S := ∑' x, a x with hSdef
    have h0 := eqn a c S hac hsa.hasSum a c S hac hsa.hasSum
    have hSn : S ^ (m + 1) = κ * c ^ (m + 1) := by linear_combination h0
    have hS0 : S ≠ 0 := by
      intro hz
      rw [hz, zero_pow (Nat.succ_ne_zero m)] at hSn
      exact (mul_ne_zero hκ (pow_ne_zero _ hc0)) hSn.symm
    refine ⟨S / c, div_ne_zero hS0 hc0, ?_⟩
    intro b d hbd hsb
    have h1 := eqn a c S hac hsa.hasSum b d (∑' x, b x) hbd hsb.hasSum
    have hT : ∑' x, b x = S / c * d := by
      rw [div_mul_eq_mul_div, eq_div_iff hc0]
      apply mul_left_cancel₀ (pow_ne_zero m hS0)
      linear_combination c * h1 - d * hSn
    rw [← hT]
    exact hsb.hasSum
  · push Not at hex
    refine ⟨1, one_ne_zero, ?_⟩
    intro b d hbd hsb
    have hd := hex b d hbd hsb
    subst hd
    have h1 := eqn b 0 _ hbd hsb.hasSum b 0 _ hbd hsb.hasSum
    have hpow : (∑' x, b x) ^ (m + 1) = 0 := by
      rw [pow_succ, h1]
      simp
    have hT : ∑' x, b x = 0 := pow_eq_zero_iff (Nat.succ_ne_zero m) |>.1 hpow
    rw [one_mul, ← hT]
    exact hsb.hasSum

end GlobalTheory
end

section

open scoped BigOperators

namespace GlobalTheory

theorem exists_common_nat_denominator {R F α : Type*} [CommRing R] [CommRing F] (φ : R →+* F)
    (h : ∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ r = n * x) (g : α → F) (S : Finset α) :
    ∃ n : ℕ, 0 < n ∧ ∀ s ∈ S, ∃ r : R, φ r = n * g s := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a S ha ih =>
    obtain ⟨n, hn, hS⟩ := ih
    obtain ⟨r, m, hm, hr⟩ := h (g a)
    refine ⟨n * m, Nat.mul_pos hn hm, fun s hs => ?_⟩
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact ⟨n * r, by rw [map_mul, map_natCast, hr]; push_cast; ring⟩
    · obtain ⟨r', hr'⟩ := hS s hs
      exact ⟨m * r', by rw [map_mul, map_natCast, hr']; push_cast; ring⟩

theorem exists_homogeneous_lift_nat_mul {R F J : Type*} [CommRing R] [CommRing F] (φ : R →+* F)
    (h : ∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ r = n * x) (G : MvPolynomial J F) (d : ℕ)
    (hG : G.IsHomogeneous d) :
    ∃ (n : ℕ) (G' : MvPolynomial J R), 0 < n ∧ G'.IsHomogeneous d ∧
      MvPolynomial.map φ G' = (n : MvPolynomial J F) * G := by
  classical
  obtain ⟨n, hn, hS⟩ := exists_common_nat_denominator φ h (fun s => G.coeff s) G.support
  choose! r hr using hS
  refine ⟨n, ∑ s ∈ G.support, MvPolynomial.monomial s (r s), hn, ?_, ?_⟩
  · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun s hs => ?_
    refine MvPolynomial.isHomogeneous_monomial _ ?_
    have := hG (MvPolynomial.mem_support_iff.1 hs)
    rw [Finsupp.degree_eq_weight_one]
    exact this

  · rw [map_sum]
    conv_rhs => rw [G.as_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [MvPolynomial.map_monomial, hr s hs, ← map_natCast (MvPolynomial.C : F →+* MvPolynomial J F),
      MvPolynomial.C_mul_monomial]

theorem cone_closure_arc_of_integral_image_reduction :
    (∀ (F K J ι : Type) [Field F] [Field K] [Algebra F K] [Fintype J] [Finite ι] (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)], (∀ i, Algebra.FiniteType F (A i)) → ∀ (w : ∀ i, J → A i) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J F) (d : ℕ), G.IsHomogeneous d → (∀ i, MvPolynomial.aeval (w i) G = 0) → MvPolynomial.aeval v G = 0) → ∃ (i : ι) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A i →+* FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ (∀ x : F, f (algebraMap F (A i) x) = algebraMap W (FractionRing W) (algebraMap K W (algebraMap F K x))) ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w i j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W) → (∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∃ (F : Type) (_ : Field F) (_ : CharZero F) (φ' : R →+* F), (∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ' r = n * x) ∧ ∀ (A : Type) [CommRing A] [Algebra ℚ A] (χ : R →+* A), (∀ r, φ r = 0 → χ r = 0) → ∃ χ' : F →+* A, χ'.comp φ' = χ) → ∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∀ (K J ι : Type) [Field K] [CharZero K] [Fintype J] [Finite ι] (ψ : R →+* K), (∀ r, φ r = 0 → ψ r = 0) → ∀ (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra ℚ (A i)], (∀ i, Algebra.FiniteType ℚ (A i)) → ∀ (χ : ∀ i, R →+* A i), (∀ i r, φ r = 0 → χ i r = 0) → ∀ (w : ∀ i, J → A i) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J R) (d : ℕ), G.IsHomogeneous d → (∀ i, MvPolynomial.eval₂ (χ i) (w i) G = 0) → MvPolynomial.eval₂ ψ v G = 0) → ∃ (i : ι) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A i →+* FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ (∀ r : R, f (χ i r) = algebraMap W (FractionRing W) (algebraMap K W (ψ r))) ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w i j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W := by
  intro H1 H2 R _ φ hφ K J ι _ _ _ _ ψ hψ A _ _ hA χ hχ w v hv hG
  obtain ⟨F, _, _, φ', hF, hlift⟩ := H2 R φ hφ
  obtain ⟨ψ', hψ'⟩ := hlift K ψ hψ
  choose χ' hχ' using fun i => hlift (A i) (χ i) (hχ i)
  letI : Algebra F K := ψ'.toAlgebra
  letI : ∀ i, Algebra F (A i) := fun i => (χ' i).toAlgebra
  have hA' : ∀ i, Algebra.FiniteType F (A i) := fun i => by
    haveI : IsScalarTower ℚ F (A i) :=
      IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
    haveI := hA i
    exact Algebra.FiniteType.of_restrictScalars_finiteType ℚ F (A i)
  obtain ⟨i, W, _, _, _, _, f, s, w', h1, h2, h3, h4⟩ := H1 F K J ι A hA' w v hv (by
    intro G d hd h0
    obtain ⟨n, G', hn, hG', hmap⟩ := exists_homogeneous_lift_nat_mul φ' hF G d hd
    have key := hG G' d hG' (fun i => by
      have : MvPolynomial.eval₂ (χ i) (w i) G'
          = MvPolynomial.aeval (w i) (MvPolynomial.map φ' G') := by
        rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← hχ' i]; rfl
      rw [this, hmap, map_mul, h0 i, mul_zero])
    have : MvPolynomial.eval₂ ψ v G' = MvPolynomial.aeval v (MvPolynomial.map φ' G') := by
      rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map, ← hψ']; rfl
    rw [this, hmap, map_mul, map_natCast] at key
    exact (mul_eq_zero.1 key).resolve_left (Nat.cast_ne_zero.2 hn.ne'))
  refine ⟨i, W, inferInstance, inferInstance, inferInstance, inferInstance, f, s, w', h1, h2, fun r => ?_, h4⟩
  have := h3 (φ' r)
  rw [← hχ' i, ← hψ']
  exact this

end GlobalTheory
end

section

open scoped BigOperators

namespace GlobalTheory

theorem exists_mul_eq_natCast_of_isIntegral_int {S : Type*} [CommRing S] [IsDomain S]
    {y : S} (hy : IsIntegral ℤ y) (hy0 : y ≠ 0) :
    ∃ (t : S) (n : ℕ), 0 < n ∧ y * t = n := by
  obtain ⟨m, hm, t, ht⟩ :=
    hy.isAlgebraic.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hy0)
  have ht' : (m : S) = y * t := by simpa using ht
  refine ⟨(m.sign : S) * t, m.natAbs, Int.natAbs_pos.mpr hm, ?_⟩
  have h1 : ((m.natAbs : ℤ) : S) = ((m.sign * m : ℤ) : S) := by
    rw [Int.sign_mul_self_eq_natAbs]
  have h2 : (m.natAbs : S) = (m.sign : S) * (m : S) := by
    rw [← Int.cast_mul, ← h1, Int.cast_natCast]
  rw [h2, ht']; ring

theorem exists_field_of_isIntegral_image :
    ∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∃ (F : Type) (_ : Field F) (_ : CharZero F) (φ' : R →+* F), (∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ' r = n * x) ∧ ∀ (A : Type) [CommRing A] [Algebra ℚ A] (χ : R →+* A), (∀ r, φ r = 0 → χ r = 0) → ∃ χ' : F →+* A, χ'.comp φ' = χ := by
  intro R _ φ hφ
  let S := R ⧸ RingHom.ker φ
  have hinj : Function.Injective (RingHom.kerLift φ) := RingHom.kerLift_injective φ
  haveI : IsDomain S := hinj.isDomain (RingHom.kerLift φ)
  haveI : CharZero S := (RingHom.kerLift φ).charZero
  have hint : ∀ y : S, @IsIntegral ℤ S _ _ (Ring.toIntAlgebra S) y := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← isIntegral_algHom_iff (RingHom.kerLift φ).toIntAlgHom hinj]
    exact hφ r
  haveI : CharZero (FractionRing S) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective S (FractionRing S))
  refine ⟨FractionRing S, inferInstance, inferInstance,
    (algebraMap S (FractionRing S)).comp (Ideal.Quotient.mk _), ?_, ?_⟩
  · intro x
    obtain ⟨a, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := S) x
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    obtain ⟨t, n, hn, ht⟩ := exists_mul_eq_natCast_of_isIntegral_int (hint y) hy0
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (a * t)
    refine ⟨r, n, hn, ?_⟩
    have hy' : algebraMap S (FractionRing S) y ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective S (FractionRing S))).mpr hy0
    have hn' : (n : FractionRing S) =
        algebraMap S (FractionRing S) y * algebraMap S (FractionRing S) t := by
      rw [← map_mul, ht, map_natCast]
    rw [RingHom.comp_apply, hr, hn', map_mul]
    field_simp
  · intro A _ _ χ hχ
    let ψ : S →+* A := Ideal.Quotient.lift (RingHom.ker φ) χ (fun r hr => hχ r hr)
    have hu : ∀ y : nonZeroDivisors S, IsUnit (ψ y) := by
      intro y
      obtain ⟨t, n, hn, ht⟩ :=
        exists_mul_eq_natCast_of_isIntegral_int (hint y) (nonZeroDivisors.ne_zero y.2)
      have hnu : IsUnit (n : A) := by
        have : IsUnit (n : ℚ) := IsUnit.mk0 _ (Nat.cast_ne_zero.mpr hn.ne')
        simpa using this.map (algebraMap ℚ A)
      have : ψ y * ψ t = n := by rw [← map_mul, ht, map_natCast]
      exact isUnit_of_mul_isUnit_left (this ▸ hnu)
    refine ⟨IsLocalization.lift (M := nonZeroDivisors S) (S := FractionRing S) hu, ?_⟩
    ext r
    simp only [RingHom.comp_apply, IsLocalization.lift_eq]
    rfl

end GlobalTheory
end

section

open scoped BigOperators
open Matrix

namespace GlobalTheory

private lemma eq_one_of_pow_eq_one_of_dvd_two_mul_sub_one {U : Type} [CommGroup U] (k : ℕ) (b : ℤ) (hb : (k : ℤ) ∣ 2 * b - 1)
    (u : U) (hu : u ^ k = 1) (h : u ^ b * u ^ b = 1) : u = 1 := by
  obtain ⟨m, hm⟩ := hb
  have h2 : u ^ (2 * b) = 1 := by rw [two_mul, _root_.zpow_add]; exact h
  have hk : u ^ (k : ℤ) = 1 := by rw [zpow_natCast]; exact hu
  have hsplit : 2 * b = k * m + 1 := by linarith
  rw [hsplit, _root_.zpow_add, _root_.zpow_mul, hk, _root_.one_zpow, one_mul, _root_.zpow_one] at h2
  exact h2

private lemma eq_one_of_hom_eq_one_on_basis {X U : Type} [AddCommGroup X] [CommGroup U] {d : ℕ}
    (e : Module.Basis (Fin d) ℤ X) (f : X → U) (hf : ∀ x x', f (x + x') = f x * f x')
    (he : ∀ i, f (e i) = 1) (x : X) : f x = 1 := by
  have h0 : f 0 = 1 := by
    have h := hf 0 0
    rw [add_zero] at h
    simpa using h
  let g : X →+ Additive U :=
    { toFun := fun x => Additive.ofMul (f x)
      map_zero' := by simp [h0]
      map_add' := fun x x' => by simp [hf] }
  have hg : g.toIntLinearMap = 0 := e.ext fun i => by simp [g, he]
  have hx := LinearMap.congr_fun hg x
  simpa [g] using hx

theorem symm_pairing_eq_one_of_odd_of_diag :
    ∀ (X U : Type) [AddCommGroup X] [CommGroup U] (d k : ℕ) (e : Module.Basis (Fin d) ℤ X) (b : ℤ), Odd k → (k : ℤ) ∣ 2 * b - 1 → ∀ δ : X → X → U, (∀ x x' y, δ (x + x') y = δ x y * δ x' y) → (∀ x y, δ x y = δ y x) → (∀ x y, δ x y ^ k = 1) → (∀ i, δ (e i) (e i) ^ b = 1) → (∀ i j, δ (e i + e j) (e i + e j) ^ b = 1) → ∀ x y, δ x y = 1 := by
  intro X U _ _ d k e b _ hb δ hadd hsymm hk1 hdiag hdiag2
  have hadd2 : ∀ x y y', δ x (y + y') = δ x y * δ x y' := by
    intro x y y'
    rw [hsymm x, hadd, hsymm y, hsymm y']
  have hoff : ∀ i j, δ (e i) (e j) = 1 := by
    intro i j
    have h := hdiag2 i j
    rw [hadd, hadd2, hadd2, hsymm (e j) (e i), _root_.mul_zpow, _root_.mul_zpow, _root_.mul_zpow, hdiag i, hdiag j] at h
    apply eq_one_of_pow_eq_one_of_dvd_two_mul_sub_one k b hb _ (hk1 _ _)
    simpa using h
  have hrow : ∀ i y, δ (e i) y = 1 := fun i =>
    eq_one_of_hom_eq_one_on_basis e (δ (e i)) (hadd2 (e i)) (hoff i)
  intro x y
  exact eq_one_of_hom_eq_one_on_basis e (fun x => δ x y) (fun x x' => hadd x x' y) (fun i => hrow i y) x

end GlobalTheory
end
