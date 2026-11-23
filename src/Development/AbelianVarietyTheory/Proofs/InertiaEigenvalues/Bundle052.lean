module

public import Mathlib.RingTheory.WittVector.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
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
public import Mathlib.NumberTheory.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.DiscreteValuationRing
public import Mathlib.RingTheory.WittVector.Teichmuller
public import Mathlib.RingTheory.WittVector.TeichmullerSeries
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.WittVector.Complete
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

section

namespace GlobalTheory

open WittVector

theorem wittVector_coeff_pow_mul_eq_zero {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R]
    [CharP R l] : ∀ (m : ℕ) (t : WittVector l R) (j : ℕ), j < m →
      ((l : WittVector l R) ^ m * t).coeff j = 0 := by
  intro m
  induction m with
  | zero => intro t j hj; omega
  | succ m ih =>
    intro t j hj
    have h : (l : WittVector l R) ^ (m + 1) * t
        = verschiebung (frobenius ((l : WittVector l R) ^ m * t)) := by
      rw [verschiebung_frobenius]; ring
    rw [h]
    cases j with
    | zero => exact verschiebung_coeff_zero _
    | succ j =>
      rw [verschiebung_coeff_succ, coeff_frobenius_charP, ih t j (by omega)]
      exact zero_pow hl.out.ne_zero

theorem wittVector_coeff_add_pow_mul {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R]
    [CharP R l] (x t : WittVector l R) (m j : ℕ) (hj : j < m) :
    (x + (l : WittVector l R) ^ m * t).coeff j = x.coeff j := by
  have h0 : truncate m ((l : WittVector l R) ^ m * t) = 0 := by
    ext i
    rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
    exact wittVector_coeff_pow_mul_eq_zero m t i i.2
  have h1 : truncate m (x + (l : WittVector l R) ^ m * t) = truncate m x := by
    rw [map_add (f := _), h0, add_zero]
  have := congrArg (fun y => TruncatedWittVector.coeff ⟨j, hj⟩ y) h1
  simpa only [WittVector.coeff_truncate] using this

theorem wittVector_dvd_of_coeff_zero {l : ℕ} [hl : Fact l.Prime] {R : Type} [CommRing R]
    [CharP R l] [PerfectRing R l] (x : WittVector l R) (hx : x.coeff 0 = 0) :
    ∃ y, x = (l : WittVector l R) * y := by
  by_cases h : x = 0
  · exact ⟨0, by rw [h, mul_zero]⟩
  obtain ⟨m, b, hb, hxb⟩ := exists_eq_pow_p_mul x h
  cases m with
  | zero => rw [pow_zero, one_mul] at hxb; exact absurd (hxb ▸ hx) hb
  | succ m => exact ⟨(l : WittVector l R) ^ m * b, by rw [hxb]; ring⟩

theorem wittVector_dvd_of_saturated_ideal : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R]
    [CharP R l] [PerfectRing R l] (J : Ideal (WittVector l R)) (μ : WittVector l R), μ ∈ J →
    (∀ a, (l : WittVector l R) * a ∈ J → a ∈ J) → (∀ a ∈ J, μ.coeff 0 ∣ a.coeff 0) →
    ∀ a ∈ J, μ ∣ a := by
  intro l _ R _ _ _ J μ hμ hsat hdiv a ha

  have step : ∀ d : J, ∃ c : WittVector l R, ∃ d' : J,
      (d : WittVector l R) = μ * c + (l : WittVector l R) * d' := by
    intro d
    obtain ⟨c₀, hc₀⟩ := hdiv d d.2
    set x := (d : WittVector l R) - μ * teichmuller l c₀ with hxdef
    have hx0 : x.coeff 0 = 0 := by
      have e : (d : WittVector l R) = x + μ * teichmuller l c₀ := by rw [hxdef]; ring
      have h2 := congrArg (fun y : WittVector l R => y.coeff 0) e
      simp only [add_coeff_zero, mul_coeff_zero, teichmuller_coeff_zero] at h2
      rw [hc₀] at h2
      linear_combination -h2
    obtain ⟨y, hy⟩ := wittVector_dvd_of_coeff_zero x hx0
    have hyJ : y ∈ J := by
      apply hsat
      rw [← hy, hxdef]
      exact J.sub_mem d.2 (J.mul_mem_right _ hμ)
    refine ⟨teichmuller l c₀, ⟨y, hyJ⟩, ?_⟩
    rw [← hy, hxdef]; ring
  choose cf df hcd using step
  let seq : ℕ → J := fun n => Nat.rec ⟨a, ha⟩ (fun _ d => df d) n
  let s : ℕ → WittVector l R := fun n =>
    ∑ k ∈ Finset.range n, (l : WittVector l R) ^ k * cf (seq k)
  have hs_succ : ∀ n, s (n + 1) = s n + (l : WittVector l R) ^ n * cf (seq n) := by
    intro n; simp only [s, Finset.sum_range_succ]
  have hmain : ∀ n, a = μ * s n + (l : WittVector l R) ^ n * (seq n).1 := by
    intro n
    induction n with
    | zero => simp [s, seq]
    | succ n ih =>
      have e : (seq (n + 1)).1 = (df (seq n)).1 := rfl
      rw [hs_succ, e]
      have := hcd (seq n)
      rw [ih, this]; ring
  have hstab : ∀ n m, n ≤ m → ∃ t, s m = s n + (l : WittVector l R) ^ n * t := by
    intro n m hnm
    induction m, hnm using Nat.le_induction with
    | base => exact ⟨0, by ring⟩
    | succ m hnm ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨t + (l : WittVector l R) ^ (m - n) * cf (seq m), ?_⟩
      rw [hs_succ, ht, mul_add, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hnm]; ring
  let c : WittVector l R := WittVector.mk l (fun k => (s (k + 1)).coeff k)
  refine ⟨c, ?_⟩
  ext k

  have htc : truncate (k + 1) c = truncate (k + 1) (s (k + 1)) := by
    ext i
    rw [WittVector.coeff_truncate, WittVector.coeff_truncate]
    obtain ⟨t, ht⟩ := hstab ((i : ℕ) + 1) (k + 1) (by omega)
    show (s ((i : ℕ) + 1)).coeff i = _
    rw [ht, wittVector_coeff_add_pow_mul _ _ _ _ (by omega)]
  have hta : truncate (k + 1) a = truncate (k + 1) (μ * c) := by
    have e := hmain (k + 1)
    have h0 : truncate (k + 1) ((l : WittVector l R) ^ (k + 1) * (seq (k + 1)).1)
        = 0 := by
      ext i
      rw [WittVector.coeff_truncate, TruncatedWittVector.coeff_zero]
      exact wittVector_coeff_pow_mul_eq_zero _ _ i i.2
    conv_lhs => rw [e]
    rw [map_add (f := _), h0, add_zero, map_mul, map_mul, htc]
  have := congrArg (fun y => TruncatedWittVector.coeff ⟨k, Nat.lt_succ_self k⟩ y) hta
  simpa only [WittVector.coeff_truncate] using this

end GlobalTheory
end

section

open scoped NNReal

namespace GlobalTheory.WittMapUniq

open WittVector

theorem exists_pow_pow_eq (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l]
    [PerfectRing R l] : ∀ (n : ℕ) (r : R), ∃ s : R, s ^ l ^ n = r := by
  intro n
  induction n with
  | zero => intro r; exact ⟨r, by simp⟩
  | succ n ih =>
    intro r
    obtain ⟨t, ht⟩ := surjective_frobenius R l r
    obtain ⟨s, hs⟩ := ih t
    refine ⟨s, ?_⟩
    rw [pow_succ, pow_mul, hs, ← ht, frobenius_def]

theorem eq_map_of_coeff_zero : ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l]
    [PerfectRing R l] [CommRing O] [CharP O l] [PerfectRing O l]
    (F : WittVector l R →+* WittVector l O) (ψ : R →+* O),
    (∀ a, (F a).coeff 0 = ψ (a.coeff 0)) → F = WittVector.map ψ := by
  intro l _ R O _ _ _ _ _ _ F ψ hF
  have hdiff : ∀ x : WittVector l R, (l : WittVector l O) ∣ F x - WittVector.map ψ x := by
    intro x
    rw [← Ideal.mem_span_singleton, mem_span_p_iff_coeff_zero_eq_zero]
    have h := (WittVector.constantCoeff : WittVector l O →+* O).map_sub (F x) (WittVector.map ψ x)
    simp only [WittVector.constantCoeff_apply] at h
    rw [h, hF, WittVector.map_coeff, sub_self]
  have hteich : ∀ (n : ℕ) (r : R),
      (l : WittVector l O) ^ (n + 1) ∣ F (teichmuller l r) - teichmuller l (ψ r) := by
    intro n r
    obtain ⟨s, rfl⟩ := exists_pow_pow_eq l R n r
    have h1 : (l : WittVector l O) ∣ F (teichmuller l s) - teichmuller l (ψ s) := by
      have := hdiff (teichmuller l s)
      rwa [WittVector.map_teichmuller] at this
    have h2 := dvd_sub_pow_of_dvd_sub h1 n
    rw [map_pow, map_pow, map_pow, map_pow]
    exact h2
  ext x m
  have key : ∀ n : ℕ, F x - WittVector.map ψ x ∈ Ideal.span {((l : WittVector l O) ^ n)} := by
    intro n
    let I : Ideal (WittVector l O) := Ideal.span {((l : WittVector l O) ^ n)}
    have hfg : (Ideal.Quotient.mk I).comp F = (Ideal.Quotient.mk I).comp (WittVector.map ψ) := by
      refine WittVector.eq_of_apply_teichmuller_eq _ _ ⟨n, ?_⟩ ?_
      · rw [← map_natCast (Ideal.Quotient.mk I), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.subset_span rfl
      · intro r
        simp only [RingHom.comp_apply, WittVector.map_teichmuller]
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
        exact dvd_trans (pow_dvd_pow _ n.le_succ) (hteich n r)
    have := congrArg (fun f => f x) hfg
    simp only [RingHom.comp_apply] at this
    exact Ideal.Quotient.eq.mp this
  have h := (mem_span_p_pow_iff_le_coeff_eq_zero _ (m + 1)).mp (key (m + 1))
  have h' := (le_coeff_eq_iff_le_sub_coeff_eq_zero (n := m + 1)).mpr h
  exact h' m (Nat.lt_succ_self m)

end GlobalTheory.WittMapUniq
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem summable_finprod_of_finite_support_euler : ∀ (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v)
    (a : ∀ v, X v → ℝ) (s : ι → ℝ), (∀ v x, 0 ≤ a v x) → (∀ v, a v (x0 v) = 1) → Summable s →
    (∀ v (C : Finset (X v)), x0 v ∉ C → ∑ x ∈ C, a v x ≤ s v) →
    Summable (fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => ∏ᶠ v, a v (f.1 v)) := by
  intro ι _ X x0 a s ha h1 hs hC
  classical
  have hs0 : ∀ v, 0 ≤ s v := fun v => by simpa using hC v ∅ (Finset.notMem_empty _)
  refine summable_of_sum_le (c := Real.exp (∑' v, s v)) (fun f => finprod_nonneg fun v => ha v _) ?_
  intro u
  set S : Finset ι := u.biUnion (fun f => f.2.toFinset) with hSdef
  have hsub : ∀ f ∈ u, ∀ w, f.1 w ≠ x0 w → w ∈ S := by
    intro f hf w hw
    exact Finset.mem_biUnion.2 ⟨f, hf, by simpa using hw⟩
  have hval : ∀ f ∈ u, ∏ᶠ v, a v (f.1 v) = ∏ x ∈ S.attach, a x.1 (f.1 x.1) := by
    intro f hf
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
    · exact (Finset.prod_attach S (fun v => a v (f.1 v))).symm
    · intro w hw
      by_contra hwS
      apply hw
      have : f.1 w = x0 w := by
        by_contra hne; exact hwS (hsub f hf w hne)
      simp [this, h1]
  let C : ∀ v, Finset (X v) := fun v => u.image (fun f => f.1 v)
  let φ : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} → (∀ v ∈ S, X v) := fun f v _ => f.1 v
  have hφinj : Set.InjOn φ u := by
    intro f hf g hg hfg
    apply Subtype.ext
    funext w
    by_cases hw : w ∈ S
    · exact congrFun (congrFun hfg w) hw
    · have hf' : f.1 w = x0 w := by by_contra h; exact hw (hsub f hf w h)
      have hg' : g.1 w = x0 w := by by_contra h; exact hw (hsub g hg w h)
      rw [hf', hg']
  have step1 : ∑ f ∈ u, ∏ᶠ v, a v (f.1 v) = ∑ p ∈ u.image φ, ∏ x ∈ S.attach, a x.1 (p x.1 x.2) := by
    rw [Finset.sum_image hφinj]
    exact Finset.sum_congr rfl hval
  have himg : u.image φ ⊆ S.pi C := by
    intro p hp
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hp
    exact Finset.mem_pi.2 fun v hv => Finset.mem_image_of_mem _ hf
  have step2 : ∑ p ∈ u.image φ, ∏ x ∈ S.attach, a x.1 (p x.1 x.2) ≤
      ∑ p ∈ S.pi C, ∏ x ∈ S.attach, a x.1 (p x.1 x.2) :=
    Finset.sum_le_sum_of_subset_of_nonneg himg fun p _ _ => Finset.prod_nonneg fun x _ => ha _ _
  have hCv : ∀ v, ∑ x ∈ C v, a v x ≤ 1 + s v := by
    intro v
    calc ∑ x ∈ C v, a v x ≤ ∑ x ∈ insert (x0 v) ((C v).erase (x0 v)), a v x :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.insert_erase_subset _ _) fun x _ _ => ha v x
      _ = 1 + ∑ x ∈ (C v).erase (x0 v), a v x := by
          rw [Finset.sum_insert (Finset.notMem_erase _ _), h1]
      _ ≤ 1 + s v := by gcongr; exact hC v _ (Finset.notMem_erase _ _)
  calc ∑ f ∈ u, ∏ᶠ v, a v (f.1 v) ≤ ∑ p ∈ S.pi C, ∏ x ∈ S.attach, a x.1 (p x.1 x.2) := step1 ▸ step2
    _ = ∏ v ∈ S, ∑ x ∈ C v, a v x := (Finset.prod_sum S C a).symm
    _ ≤ ∏ v ∈ S, Real.exp (s v) := Finset.prod_le_prod₀ (fun v _ => Finset.sum_nonneg fun x _ => ha v x)
          fun v _ => (hCv v).trans (by linarith [Real.add_one_le_exp (s v)])
    _ = Real.exp (∑ v ∈ S, s v) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (∑' v, s v) := Real.exp_le_exp.2 (hs.sum_le_tsum _ (fun v _ => hs0 v))

end GlobalTheory
end
