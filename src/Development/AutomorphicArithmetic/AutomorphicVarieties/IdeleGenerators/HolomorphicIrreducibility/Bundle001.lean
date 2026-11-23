module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.WeilBound.SimpleEigenvalues.SimpleEigenvalueExtension.SimEig
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TwoNeZeroNat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Module

section
variable {K M : Type} [Field K] [IsAlgClosed K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

omit [IsAlgClosed K] in
private theorem finrank_map_lt (U : Submodule K M) (S : Module.End K M) (v : M) (hv : v ∈ U) (hv0 : v ≠ 0)
    (hS : S v = 0) : finrank K (U.map S) < finrank K U := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (S.domRestrict U)
  rw [LinearMap.range_domRestrict] at h1
  have h2 : LinearMap.ker (S.domRestrict U) ≠ ⊥ := (Submodule.ne_bot_iff _).mpr
    ⟨⟨v, hv⟩, by simpa using hS, fun h => hv0 (congrArg Subtype.val h)⟩
  have h3 : finrank K (LinearMap.ker (S.domRestrict U)) ≠ 0 := fun h => h2 (Submodule.finrank_eq_zero.mp h)
  omega

end

section
variable {K : Type} [NormedField K] [IsUltrametricDist K]

private theorem sub_le_one' {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x - y‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx (by simpa using hy))

private theorem sub_lt_one' {x y : K} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx (by simpa using hy))

private def bdd {I : Type} (V : Submodule K (I → K)) : Submodule K V where
  carrier := {v | ∃ c : K, c ≠ 0 ∧ ∀ n, ‖(c • v).1 n‖ ≤ 1}
  zero_mem' := ⟨1, one_ne_zero, fun n => by simp⟩
  add_mem' := by
    have key : ∀ (c e x : K), e ≠ 0 → ‖c‖ ≤ ‖e‖ → ‖e * x‖ ≤ 1 → ‖c * x‖ ≤ 1 := by
      intro c e x _ hce hx
      rw [norm_mul] at hx ⊢
      exact (mul_le_mul_of_nonneg_right hce (norm_nonneg _)).trans hx
    rintro v w ⟨c, hc, hv⟩ ⟨e, he, hw⟩
    rcases le_total ‖c‖ ‖e‖ with h | h
    · refine ⟨c, hc, fun n => ?_⟩
      have : (c • (v + w)).1 n = c * v.1 n + c * w.1 n := by simp [mul_add]
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hv n) (key c e _ he h (hw n)))
    · refine ⟨e, he, fun n => ?_⟩
      have : (e • (v + w)).1 n = e * v.1 n + e * w.1 n := by simp [mul_add]
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (key e c _ hc h (hv n)) (hw n))
  smul_mem' := by
    rintro s v ⟨c, hc, hv⟩
    by_cases hs : s = 0
    · exact ⟨1, one_ne_zero, fun n => by simp [hs]⟩
    · refine ⟨c / s, div_ne_zero hc hs, fun n => ?_⟩
      rw [smul_smul, div_mul_cancel₀ c hs]
      exact hv n

omit [IsUltrametricDist K] in
private theorem eig_le_one {I : Type} {V : Submodule K (I → K)} (T : Module.End K V)
    (hT : ∀ v : V, (∀ n, ‖v.1 n‖ ≤ 1) → ∀ n, ‖(T v).1 n‖ ≤ 1) (v : V) (hv0 : v ≠ 0) (hv : ∀ n, ‖v.1 n‖ ≤ 1)
    (c : K) (hc : T v = c • v) : ‖c‖ ≤ 1 := by
  by_contra h
  push Not at h
  have hk : ∀ k : ℕ, ∀ n, ‖(c ^ k • v).1 n‖ ≤ 1 := by
    intro k
    induction k with
    | zero => simpa using hv
    | succ k ih =>
      have := hT _ ih
      rwa [map_smul, hc, smul_smul, ← pow_succ] at this
  obtain ⟨n, hn⟩ : ∃ n, v.1 n ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hv0 (Subtype.ext (funext h'))
  have hpos : 0 < ‖v.1 n‖ := norm_pos_iff.mpr hn
  obtain ⟨k, hk'⟩ := pow_unbounded_of_one_lt (‖v.1 n‖⁻¹) h
  have h1 := hk k n
  have h2 : (c ^ k • v).1 n = c ^ k * v.1 n := by simp
  rw [h2, norm_mul, norm_pow] at h1
  have h3 := mul_lt_mul_of_pos_right hk' hpos
  rw [inv_mul_cancel₀ hpos.ne'] at h3
  linarith

private theorem main [IsAlgClosed K] {I J : Type} (V : Submodule K (I → K)) [FiniteDimensional K V]
    (T : J → Module.End K V) (hc : ∀ i j, T i * T j = T j * T i)
    (h1 : ∀ j (v : V), (∀ n, ‖v.1 n‖ ≤ 1) → ∀ n, ‖(T j v).1 n‖ ≤ 1)
    (h2 : ∀ j (v : V), (∀ n, ‖v.1 n‖ < 1) → ∀ n, ‖(T j v).1 n‖ < 1) (a : J → K) (ha : ∀ j, ‖a j‖ ≤ 1) :
    ∀ (d : ℕ) (U : Submodule K V), finrank K U = d → U ≤ bdd V → (∀ j, ∀ x ∈ U, T j x ∈ U) →
      ∀ f ∈ U, (∀ n, ‖f.1 n‖ ≤ 1) → (∃ n, ‖f.1 n‖ = 1) → (∀ j n, ‖(T j f).1 n - a j * f.1 n‖ < 1) →
      ∃ (h : V) (b : J → K), h ≠ 0 ∧ (∀ n, ‖h.1 n‖ ≤ 1) ∧ (∀ j, T j h = b j • h) ∧ ∀ j, ‖b j - a j‖ < 1 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro U hd hb hT f hfU hf hf1 hfa
    by_cases h : ∀ j (c : K), ∀ v ∈ U, v ≠ 0 → T j v = c • v → ‖c - a j‖ < 1
    · have hU : U ≠ ⊥ := by
        refine (Submodule.ne_bot_iff U).mpr ⟨f, hfU, ?_⟩
        rintro rfl
        obtain ⟨n, hn⟩ := hf1
        simp at hn
      obtain ⟨v, hv, hv0, hve⟩ := UpperTheory.V.LinAlg.simEig T hc _ U rfl hU hT
      choose b hbv using hve
      obtain ⟨c, hc0, hcv⟩ := hb hv
      refine ⟨c • v, b, smul_ne_zero hc0 hv0, hcv, fun j => ?_, fun j => h j (b j) v hv hv0 (hbv j)⟩
      rw [map_smul, hbv j, smul_comm]
    · push Not at h
      obtain ⟨j, c, v, hv, hv0, hcv, hca⟩ := h
      have hc1 : ‖c‖ ≤ 1 := by
        obtain ⟨e, he0, hev⟩ := hb hv
        refine eig_le_one (T j) (h1 j) (e • v) (smul_ne_zero he0 hv0) hev c ?_
        rw [map_smul, hcv, smul_comm]
      have hca1 : ‖c - a j‖ = 1 := le_antisymm (sub_le_one' hc1 (ha j)) hca
      let S : Module.End K V := T j - c • 1
      have hS : ∀ x, S x = T j x - c • x := fun x => by simp [S]
      have hcomm : ∀ i x, T i (S x) = S (T i x) := by
        intro i x
        have h3 : T j (T i x) = T i (T j x) := by
          have := congrArg (fun S : Module.End K V => S x) (hc j i)
          simpa using this
        rw [hS, hS, map_sub, map_smul, h3]
      have hle : U.map S ≤ U := by
        rintro _ ⟨x, hx, rfl⟩
        rw [hS]
        exact U.sub_mem (hT j x hx) (U.smul_mem c hx)
      have hSn : ∀ (x : V) n, (S x).1 n = (T j x).1 n - c * x.1 n := fun x n => by rw [hS]; simp
      refine ih _ (hd ▸ finrank_map_lt U S v hv hv0 (by rw [hS, hcv, sub_self])) (U.map S) rfl (hle.trans hb) ?_
        (S f) ⟨f, hfU, rfl⟩ ?_ ?_ ?_
      · rintro i _ ⟨x, hx, rfl⟩
        exact ⟨T i x, hT i x hx, (hcomm i x).symm⟩
      · intro n
        rw [hSn]
        refine sub_le_one' (h1 j f hf n) ?_
        rw [norm_mul]
        exact mul_le_one₀ hc1 (norm_nonneg _) (hf n)
      · obtain ⟨n, hn⟩ := hf1
        refine ⟨n, le_antisymm ?_ ?_⟩
        · rw [hSn]
          refine sub_le_one' (h1 j f hf n) ?_
          rw [norm_mul]
          exact mul_le_one₀ hc1 (norm_nonneg _) (hf n)
        · by_contra hlt
          push Not at hlt
          have h4 := sub_lt_one' (hfa j n) hlt
          have h5 : (T j f).1 n - a j * f.1 n - (S f).1 n = (c - a j) * f.1 n := by rw [hSn]; ring
          rw [h5, norm_mul, hca1, hn] at h4
          simp at h4
      · intro i n
        have hg : ∀ n, ‖(T i f - a i • f).1 n‖ < 1 := fun n => by simpa using hfa i n
        have h6 : (T i (S f)).1 n - a i * (S f).1 n = (S (T i f - a i • f)).1 n := by
          rw [map_sub, map_smul, hcomm]; simp
        rw [h6, hSn]
        refine sub_lt_one' (h2 j _ hg n) ?_
        rw [norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right hc1 (norm_nonneg _) (hg n)

end

theorem UpperTheory.V.Sd.delSerre :
    UpperTheory.V.Sd.DelSerre := by
  intro l _ I J V hV T hc h1 h2 f a hf hf1 ha hfa
  refine main V T hc h1 h2 a ha _ (bdd V) rfl le_rfl ?_ f ⟨1, one_ne_zero, by simpa using hf⟩ hf hf1 hfa
  rintro j x ⟨c, hc0, hx⟩
  refine ⟨c, hc0, ?_⟩
  rw [← map_smul]
  exact h1 j _ hx
end

section

open Formalism.ConjugateSelfDual Polynomial

namespace UpperTheory.V.Sd

section
variable {K : Type} [NormedField K] [IsUltrametricDist K]

private lemma nsub_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a - b‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha (by rwa [norm_neg]))

private lemma nadd_le {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)

private lemma nadd_eq {a b : K} (ha : ‖a‖ = 1) (hb : ‖b‖ < 1) : ‖a + b‖ = 1 := by
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [ha]; exact hb.ne'), ha]
  exact max_eq_left hb.le

private lemma norm_root {N : ℕ} (hN : 0 < N) {x : K} (hx : x ^ N = 1) : ‖x‖ = 1 := by
  have h : ‖x‖ ^ N = 1 := by rw [← norm_pow, hx, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) hN.ne').1 h

private lemma norm_one_sub_pow_le {x : K} (hx : ‖x‖ = 1) (i : ℕ) : ‖1 - x ^ i‖ ≤ ‖1 - x‖ := by
  induction i with
  | zero => simp
  | succ i ih =>
    have : 1 - x ^ (i + 1) = (1 - x) + x * (1 - x ^ i) := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le le_rfl ?_)
    rw [norm_mul, hx, one_mul]; exact ih

private lemma norm_one_sub {N : ℕ} (hN : 0 < N) (hn : ‖(N : K)‖ = 1) {x : K} (hx : x ^ N = 1) (h1 : x ≠ 1) :
    ‖1 - x‖ = 1 := by
  have hx1 := norm_root hN hx
  refine le_antisymm (nsub_le (by simp) hx1.le) ?_
  have hs : ∑ i ∈ Finset.range N, x ^ i = 0 := by
    have := mul_geom_sum x N
    rw [hx, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1)
  have hN' : (N : K) = ∑ i ∈ Finset.range N, (1 - x ^ i) := by
    rw [Finset.sum_sub_distrib, hs]; simp
  rw [← hn, hN']
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _)
    fun i _ => norm_one_sub_pow_le hx1 i

private lemma norm_aeval_le {x : K} (hx : ‖x‖ ≤ 1) (p : ℤ[X]) : ‖aeval x p‖ ≤ 1 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _)]; exact nadd_le hp hq
  | monomial n a =>
    rw [aeval_monomial, norm_mul, norm_pow]
    have h1 : ‖algebraMap ℤ K a‖ ≤ 1 := by
      rw [eq_intCast]; exact IsUltrametricDist.norm_intCast_le_one K a
    exact mul_le_one₀ h1 (by positivity) (pow_le_one₀ (norm_nonneg _) hx)

end

private lemma eulerian_numerator_three : numL 3 = X * (1 + X) := by
  simp only [numL]; simp; ring

private lemma eulerian_numerator_four : numL 4 = X * (1 + 4 * X + X ^ 2) := by
  have : numL 4 = X * (derivative (numL 3) * (1 - X) + C (((2 : ℕ) : ℤ) + 1) * numL 3) := rfl
  rw [this, eulerian_numerator_three]; simp; ring

private lemma eulerian_numerator_five : numL 5 = X * (1 + X) * (1 + 10 * X + X ^ 2) := by
  have : numL 5 = X * (derivative (numL 4) * (1 - X) + C (((3 : ℕ) : ℤ) + 1) * numL 4) := rfl
  rw [this, eulerian_numerator_four]; simp; ring

section
variable {K : Type} [Field K]

private lemma eulerian_three_eq (x : K) : Lk 3 x = x * (1 + x) / (1 - x) ^ 3 := by
  simp [Lk, eulerian_numerator_three]

private lemma eulerian_four_eq {x : K} (h : 1 - x ≠ 0) :
    Lk 4 x = (x / (1 - x) ^ 2) * (1 + 6 * (x / (1 - x) ^ 2)) := by
  have : Lk 4 x = x * (1 + 4 * x + x ^ 2) / (1 - x) ^ 4 := by
    simp [Lk, eulerian_numerator_four, map_ofNat]
  rw [this]; field_simp; ring

private lemma eulerian_five_eq {x : K} (h : 1 - x ≠ 0) :
    Lk 5 x = Lk 3 x * (1 + 12 * (x / (1 - x) ^ 2)) := by
  have : Lk 5 x = x * (1 + x) * (1 + 10 * x + x ^ 2) / (1 - x) ^ 5 := by
    simp [Lk, eulerian_numerator_five, map_ofNat]
  rw [this, eulerian_three_eq]; field_simp; ring

end

private lemma norm_nat {l : ℕ} [Fact l.Prime] {N : ℕ} (h : ¬ l ∣ N) : ‖(N : Qbar l)‖ = 1 := by
  have h1 : (N : Qbar l) = algebraMap ℚ_[l] (Qbar l) (N : ℚ_[l]) := by simp
  rw [h1, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 h

private lemma norm_nat_lt {l : ℕ} [Fact l.Prime] {N : ℕ} (h : l ∣ N) : ‖(N : Qbar l)‖ < 1 := by
  have h1 : (N : Qbar l) = algebraMap ℚ_[l] (Qbar l) (N : ℚ_[l]) := by simp
  rw [h1, norm_algebraMap', Padic.norm_natCast_lt_one_iff]
  exact h

end UpperTheory.V.Sd

open UpperTheory.V.Sd in
theorem UpperTheory.V.Sd.lkSep :
    UpperTheory.V.Sd.LkSep := by
  intro l _ hl2 N hN hlN
  have hn : ‖(N : Qbar l)‖ = 1 := norm_nat hlN
  have h1 : ∀ (k : ℕ) (x : Qbar l), x ^ N = 1 → x ≠ 1 → ‖Lk k x‖ ≤ 1 := by
    intro k x hx h
    rw [Lk, norm_div, norm_pow, norm_one_sub hN hn hx h, one_pow, div_one]
    exact norm_aeval_le (norm_root hN hx).le _
  have hne : ∀ x : Qbar l, x ^ 2 ≠ 1 → x ≠ 1 := by
    rintro x h rfl; exact h (one_pow 2)
  have h3 : ∀ x : Qbar l, x ^ N = 1 → x ^ 2 ≠ 1 → ‖Lk 3 x‖ = 1 := by
    intro x hx h
    have ha := norm_one_sub hN hn hx (hne x h)
    have hb : ‖1 - x ^ 2‖ = 1 :=
      norm_one_sub hN hn (by rw [← pow_mul, mul_comm, pow_mul, hx, one_pow]) h
    have hc : ‖1 + x‖ = 1 := by
      have : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
      rwa [this, norm_mul, ha, one_mul] at hb
    rw [eulerian_three_eq, norm_div, norm_mul, norm_pow, ha, hc, norm_root hN hx]; norm_num
  refine ⟨h1, h3, ?_⟩
  intro x y hx hy hx2 hy2 hyx hyx'
  have hax := norm_one_sub hN hn hx (hne x hx2)
  have hay := norm_one_sub hN hn hy (hne y hy2)
  have hnx := norm_root hN hx
  have hny := norm_root hN hy
  have hx0 : x ≠ 0 := by rintro rfl; simp at hnx
  have hx1 : 1 - x ≠ 0 := sub_ne_zero.2 (hne x hx2).symm
  have hy1 : 1 - y ≠ 0 := sub_ne_zero.2 (hne y hy2).symm
  have hxy : ‖1 - x * y‖ = 1 := by
    refine norm_one_sub hN hn (by rw [mul_pow, hx, hy, one_mul]) fun h => hyx' ?_
    exact eq_inv_of_mul_eq_one_right h
  have hxy' : ‖1 - y / x‖ = 1 := by
    refine norm_one_sub hN hn (by rw [div_pow, hx, hy, div_one]) fun h => hyx ?_
    exact (div_eq_one_iff_eq hx0).1 h
  have h4x := eulerian_four_eq hx1
  have h4y := eulerian_four_eq hy1
  have h5x := eulerian_five_eq hx1
  have h5y := eulerian_five_eq hy1
  have hu : ‖x / (1 - x) ^ 2‖ = 1 := by rw [norm_div, norm_pow, hax, hnx]; norm_num
  have hv : ‖y / (1 - y) ^ 2‖ = 1 := by rw [norm_div, norm_pow, hay, hny]; norm_num
  have huv : ‖x / (1 - x) ^ 2 - y / (1 - y) ^ 2‖ = 1 := by
    have : x / (1 - x) ^ 2 - y / (1 - y) ^ 2
        = x * (1 - y / x) * (1 - x * y) / ((1 - x) ^ 2 * (1 - y) ^ 2) := by
      field_simp; ring
    rw [this, norm_div, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, hax, hay, hnx, hxy, hxy']
    norm_num
  generalize x / (1 - x) ^ 2 = u at *
  generalize y / (1 - y) ^ 2 = v at *
  by_cases h6 : l ∣ 6
  · left
    have h6' : ‖(6 : Qbar l)‖ < 1 := by exact_mod_cast norm_nat_lt h6
    have : Lk 4 x - Lk 4 y = (u - v) * (1 + 6 * (u + v)) := by rw [h4x, h4y]; ring
    rw [this, norm_mul, huv, one_mul]
    refine nadd_eq norm_one ?_
    rw [norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h6' (nadd_le hu.le hv.le)
  · right
    have h12 : ¬ l ∣ 12 := by
      intro h
      have hp : l.Prime := Fact.out
      have h' : l ∣ 6 ^ 2 := h.trans (by norm_num)
      exact h6 (hp.dvd_of_dvd_pow h')
    have h12' : ‖(12 : Qbar l)‖ = 1 := by exact_mod_cast norm_nat h12
    have hA := h3 x hx hx2
    have hB := h3 y hy hy2
    have hle : ‖Lk 3 x ^ 2 - Lk 3 y ^ 2‖ ≤ 1 :=
      nsub_le (by rw [norm_pow, hA]; norm_num) (by rw [norm_pow, hB]; norm_num)
    rcases hle.eq_or_lt with h | h
    · exact Or.inl h
    · right
      have : Lk 3 x * Lk 5 x - Lk 3 y * Lk 5 y
          = 12 * Lk 3 x ^ 2 * (u - v) + (Lk 3 x ^ 2 - Lk 3 y ^ 2) * (1 + 12 * v) := by
        rw [h5x, h5y]; ring
      rw [this]
      refine nadd_eq (by rw [norm_mul, norm_mul, norm_pow, h12', hA, huv]; norm_num) ?_
      rw [norm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h
        (nadd_le norm_one.le (by rw [norm_mul, h12', hv]; norm_num))
end

section

theorem UpperTheory.V.Sd.ePrim :
    UpperTheory.V.Sd.EPrim := by
  intro l M w φ θ χ D
  have hM := D.one_lt
  have hw := D.prime
  haveI : NeZero M := ⟨by omega⟩
  haveI : NeZero w := ⟨hw.ne_zero⟩
  haveI : NeZero (M * w) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne w)⟩
  set A := DirichletCharacter.changeLevel (dvd_mul_right M w) φ with hA
  set B := DirichletCharacter.changeLevel (dvd_mul_left w M) θ with hB
  have hχ : χ = A * B := by
    ext u
    have h1 := D.mul (u : ZMod (M * w)).val
    rw [MulChar.mul_apply, hA, hB, DirichletCharacter.changeLevel_eq_cast_of_dvd,
      DirichletCharacter.changeLevel_eq_cast_of_dvd, ← ZMod.natCast_val, ← ZMod.natCast_val,
      ← h1, ZMod.natCast_zmod_val]
  have hAc : A.conductor = M := by
    rw [hA, DirichletCharacter.conductor_changeLevel]
    exact D.prim
  have hBc : B.conductor = w := by
    rw [hB, DirichletCharacter.conductor_changeLevel]
    rcases (Nat.dvd_prime hw).mp θ.conductor_dvd_level with h | h
    · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h) D.θne
    · exact h
  have hcop : M.Coprime w := ((Nat.Prime.coprime_iff_not_dvd hw).mpr D.wM).symm
  have h1 : M ∣ χ.conductor := by
    have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor χ B⁻¹
    rw [DirichletCharacter.conductor_inv, hBc] at h
    have e : χ * B⁻¹ = A := by rw [hχ, mul_inv_cancel_right]
    rw [e, hAc] at h
    exact hcop.dvd_of_dvd_mul_right (h.trans (Nat.lcm_dvd_mul _ _))
  have h2 : w ∣ χ.conductor := by
    have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor A⁻¹ χ
    rw [DirichletCharacter.conductor_inv, hAc] at h
    have e : A⁻¹ * χ = B := by rw [hχ, inv_mul_cancel_left]
    rw [e, hBc] at h
    exact hcop.symm.dvd_of_dvd_mul_left (h.trans (Nat.lcm_dvd_mul _ _))
  exact Nat.dvd_antisymm χ.conductor_dvd_level (hcop.mul_dvd_of_dvd_of_dvd h1 h2)
end

section

noncomputable section

open CongruenceSubgroup UpperHalfPlane ModularForm UpperTheory.V.Af
open scoped MatrixGroups ModularForm Manifold

namespace UpperTheory.V.Sd

private def hM (p : ℕ) : Option (Fin p) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(p : ℤ), 0; 0, 1]
  | some u => !![1, ((u : ℕ) : ℤ); 0, (p : ℤ)]

private theorem hM_det (p : ℕ) (x : Option (Fin p)) : (hM p x).det = p := by
  cases x <;> simp [hM, Matrix.det_fin_two_of]

private def hG {p : ℕ} (hp : p.Prime) (x : Option (Fin p)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((Int.castRingHom ℝ).mapMatrix (hM p x)) (by
    rw [← RingHom.map_det, hM_det]; simpa using hp.ne_zero)

private def hT {p : ℕ} (hp : p.Prime) (k : ℕ) {N : ℕ} (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ x : Option (Fin p), χ ((hM p x 0 0 : ℤ) : ZMod N) • f ∣[(k : ℤ)] hG hp x

end UpperTheory.V.Sd

theorem UpperTheory.V.Sd.heckeEx :
    UpperTheory.V.Sd.HeckeEx :=
  _root_.UpperTheory.Reformulated.B.hecke_existence.heckeEx
end
end
