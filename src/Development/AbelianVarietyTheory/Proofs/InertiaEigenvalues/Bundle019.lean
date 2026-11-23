module

public import Mathlib.Analysis.Normed.Field.Instances
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Basic.Real.Basic
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
public import Mathlib.NumberTheory.Padics.RingHoms
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
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.Padics.PadicIntegers
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Normed.Group.Basic

@[expose] public section

section

open Polynomial

namespace GlobalTheory

theorem padicComplex_norm_prime (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [← PadicComplex.coe_natCast, PadicComplex.norm_extends,
    ← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)),
    PadicAlgCl.norm_extends, Padic.norm_p]

theorem lift_hasSum_zero : ∀ (l : ℕ) [Fact l.Prime] (X ι : Type) (η : X → ι → ℂ_[l]) (τ : ι → ℝ) (S : Set X), (∀ t : ι → ℂ_[l], (∀ i, ‖t i‖ ≤ τ i) → ∃ y ∈ S, ∀ i, ‖η y i - t i‖ ≤ ‖(l : ℂ_[l])‖ * τ i) → ∀ x ∈ S, (∀ i, ‖η x i‖ ≤ ‖(l : ℂ_[l])‖ * τ i) → ∃ y : ℕ → X, y 0 = x ∧ (∀ k, y k ∈ S) ∧ ∀ i, HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * η (y k) i) 0 := by
  intro l _ X ι η τ S hS x hx hxb
  have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := padicComplex_norm_prime l
  have hp : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hlpos : 0 < ‖(l : ℂ_[l])‖ := by rw [hl]; positivity
  have hllt : ‖(l : ℂ_[l])‖ < 1 := by rw [hl]; exact inv_lt_one_of_one_lt₀ hp
  have hl0 : (l : ℂ_[l]) ≠ 0 := norm_pos_iff.mp hlpos
  let T := {t : ι → ℂ_[l] // ∀ i, ‖t i‖ ≤ τ i}
  have hg : ∀ t : T, ∃ y ∈ S, ∀ i, ‖η y i + t.1 i‖ ≤ ‖(l : ℂ_[l])‖ * τ i := by
    intro t
    obtain ⟨y, hyS, hy⟩ := hS (-t.1) (fun i => by simpa using t.2 i)
    exact ⟨y, hyS, fun i => by simpa [sub_eq_add_neg] using hy i⟩
  choose g hgS hgb using hg
  have hdiv : ∀ z : ℂ_[l], ∀ i, ‖z‖ ≤ ‖(l : ℂ_[l])‖ * τ i → ‖z / l‖ ≤ τ i := by
    intro z i hz
    rw [norm_div, div_le_iff₀ hlpos]; linarith [mul_comm (‖(l : ℂ_[l])‖) (τ i)]
  let step : T → T := fun t => ⟨fun i => (t.1 i + η (g t) i) / l,
    fun i => hdiv _ i (by rw [add_comm]; exact hgb t i)⟩
  let t0 : T := ⟨fun i => η x i / l, fun i => hdiv _ i (hxb i)⟩
  let ts : ℕ → T := fun k => step^[k] t0
  let y : ℕ → X := fun k => Nat.casesOn k x (fun k => g (ts k))
  have hy0 : y 0 = x := rfl
  have hysucc : ∀ k, y (k+1) = g (ts k) := fun k => rfl
  have htsucc : ∀ k, ts (k+1) = step (ts k) := fun k => Function.iterate_succ_apply' step k t0
  refine ⟨y, hy0, ?_, ?_⟩
  · intro k; cases k with
    | zero => exact hx
    | succ k => exact hgS _
  intro i

  have hinv : ∀ k, ∑ m ∈ Finset.range (k+1), (l : ℂ_[l]) ^ m * η (y m) i = (l : ℂ_[l]) ^ (k+1) * (ts k).1 i := by
    intro k
    induction k with
    | zero => simp [hy0, ts, t0]; field_simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih, hysucc, htsucc]
      simp only [step]
      field_simp
      ring

  have hτ : ∀ k, 0 ≤ τ i := fun k => le_trans (norm_nonneg _) ((ts k).2 i)
  have hbd : ∀ k, ‖η (y k) i‖ ≤ τ i := by
    intro k; cases k with
    | zero => exact le_trans (hxb i) (by nlinarith [hτ 0])
    | succ k =>
      rw [hysucc]
      have h1 := hgb (ts k) i
      have h2 := (ts k).2 i
      have : η (g (ts k)) i = (η (g (ts k)) i + (ts k).1 i) - (ts k).1 i := by ring
      rw [this]
      rw [sub_eq_add_neg]
      refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ (by rw [norm_neg]; exact h2))
      exact le_trans h1 (by nlinarith [hτ 0])
  have hterm : ∀ k, ‖(l : ℂ_[l]) ^ k * η (y k) i‖ ≤ τ i * ‖(l : ℂ_[l])‖ ^ k := by
    intro k; rw [norm_mul, norm_pow, mul_comm]
    exact mul_le_mul_of_nonneg_right (hbd k) (pow_nonneg (norm_nonneg _) _)
  have hsum : Summable (fun k : ℕ => (l : ℂ_[l]) ^ k * η (y k) i) :=
    Summable.of_norm_bounded ((summable_geometric_of_lt_one (norm_nonneg _) hllt).mul_left (τ i)) hterm
  rw [hsum.hasSum_iff_tendsto_nat]
  have hlim : Filter.Tendsto (fun k : ℕ => (l : ℂ_[l]) ^ (k+1) * (ts k).1 i) Filter.atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) (g := fun k : ℕ => ‖(l : ℂ_[l])‖ ^ (k+1) * τ i) ?_
    · rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left ((ts k).2 i) (pow_nonneg (norm_nonneg _) _)
    · have := (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hllt).comp (Filter.tendsto_add_atTop_nat 1)
      simpa using this.mul_const (τ i)
  have hlim2 : Filter.Tendsto (fun k : ℕ => ∑ m ∈ Finset.range (k+1), (l : ℂ_[l]) ^ m * η (y m) i) Filter.atTop (nhds 0) := by
    simpa only [hinv] using hlim
  exact (Filter.tendsto_add_atTop_iff_nat 1).mp hlim2

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory

theorem indep_over_Ql_of_indep_mod_l : ∀ (l : ℕ) [Fact l.Prime] (d : ℕ) (ι : Type) (w : Fin d → ι → ℂ_[l]) (γ : ι → ℝ), (∀ a i, ‖w a i‖ ≤ γ i) → (∀ n : Fin d → ℕ, (∀ i, ‖∑ a, (n a : ℂ_[l]) * w a i‖ ≤ ‖(l : ℂ_[l])‖ * γ i) → ∀ a, l ∣ n a) → ∀ c : Fin d → ℚ_[l], (∀ i, ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * w a i = 0) → c = 0 := by
  intro l _ d ι w γ hw hn c hc
  by_contra hne
  obtain ⟨a1, ha1⟩ := Function.ne_iff.mp hne
  obtain ⟨a₀, -, ha₀⟩ := Finset.exists_max_image Finset.univ (fun a => ‖c a‖) ⟨a1, Finset.mem_univ _⟩
  have hc0 : c a₀ ≠ 0 := by
    intro h
    have := ha₀ a1 (Finset.mem_univ _)
    simp only [h, norm_zero] at this
    exact ha1 (norm_le_zero_iff.mp this)
  set c' : Fin d → ℚ_[l] := fun a => c a / c a₀ with hc'
  have hc'le : ∀ a, ‖c' a‖ ≤ 1 := by
    intro a
    simp only [hc', norm_div]
    exact div_le_one_of_le₀ (ha₀ a (Finset.mem_univ _)) (norm_nonneg _)
  have hc'a₀ : c' a₀ = 1 := div_self hc0
  have hsum' : ∀ i, ∑ a, algebraMap ℚ_[l] ℂ_[l] (c' a) * w a i = 0 := by
    intro i
    have : ∑ a, algebraMap ℚ_[l] ℂ_[l] (c' a) * w a i
        = algebraMap ℚ_[l] ℂ_[l] (c a₀)⁻¹ * ∑ a, algebraMap ℚ_[l] ℂ_[l] (c a) * w a i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      simp only [hc', div_eq_mul_inv, map_mul]
      ring
    rw [this, hc i, mul_zero]
  let e : Fin d → ℤ_[l] := fun a => ⟨c' a, hc'le a⟩
  let n : Fin d → ℕ := fun a => (e a).appr 1
  have hen : ∀ a, ‖e a - (n a : ℤ_[l])‖ ≤ (l : ℝ)⁻¹ := by
    intro a
    have h := (PadicInt.norm_le_pow_iff_mem_span_pow _ 1).mpr (by simpa using PadicInt.appr_spec 1 (e a))
    simpa using h
  have hlC : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]) l, norm_algebraMap', Padic.norm_p]
  have hsmall : ∀ i, ‖∑ a, (n a : ℂ_[l]) * w a i‖ ≤ ‖(l : ℂ_[l])‖ * γ i := by
    intro i
    have heq : ∑ a, (n a : ℂ_[l]) * w a i
        = ∑ a, ((n a : ℂ_[l]) - algebraMap ℚ_[l] ℂ_[l] (c' a)) * w a i := by
      simp only [sub_mul, Finset.sum_sub_distrib, hsum' i, sub_zero]
    rw [heq, hlC]
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    · exact mul_nonneg (by positivity) ((norm_nonneg _).trans (hw a₀ i))
    · intro a _
      rw [norm_mul]
      refine mul_le_mul ?_ (hw a i) (norm_nonneg _) (by positivity)
      have : (n a : ℂ_[l]) - algebraMap ℚ_[l] ℂ_[l] (c' a)
          = algebraMap ℚ_[l] ℂ_[l] (-(((e a - (n a : ℤ_[l]) : ℤ_[l]) : ℚ_[l]))) := by
        have hea : ((e a : ℤ_[l]) : ℚ_[l]) = c' a := rfl
        rw [map_neg, PadicInt.coe_sub, PadicInt.coe_natCast, hea, map_sub, map_natCast]
        ring
      rw [this, norm_algebraMap', norm_neg, PadicInt.padic_norm_e_of_padicInt]
      exact hen a
  have hdiv := hn n hsmall a₀
  have hlt : ‖(n a₀ : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_lt_one_iff_dvd]
    obtain ⟨k, hk⟩ := hdiv
    exact ⟨k, by rw [hk]; push_cast; ring⟩
  have he1 : ‖e a₀‖ = 1 := by
    show ‖c' a₀‖ = 1
    rw [hc'a₀, norm_one]
  have hlinv : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have : ‖e a₀‖ ≤ max ‖e a₀ - (n a₀ : ℤ_[l])‖ ‖(n a₀ : ℤ_[l])‖ := by
    simpa using IsUltrametricDist.norm_add_le_max (e a₀ - (n a₀ : ℤ_[l])) (n a₀ : ℤ_[l])
  rw [he1] at this
  have := this.trans_lt (max_lt ((hen a₀).trans_lt hlinv) hlt)
  exact lt_irrefl _ this

end GlobalTheory
end

section

open Polynomial

namespace GlobalTheory.TwoSidedShift

theorem mem_pow_span_iff (l : ℕ) (A : Type) [CommRing A] (n : ℕ) (x : A) :
    x ∈ ((Ideal.span {(l : A)}) ^ n • ⊤ : Submodule A A) ↔ (l : A) ^ n ∣ x := by
  simp [Ideal.span_singleton_pow, Ideal.mem_span_singleton]

theorem exists_sum_shift : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A]
    [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (c : ℤ → A),
    (∀ n : ℤ, (l : A) ^ n.natAbs ∣ c n) → (∀ n : ℤ, φ^[h] (c n) = (l : A) * c (n + 1)) →
    ∃ w : A, φ^[h] w = (l : A) * w ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) →
      HasSum (fun n : ℤ => Θ (c n)) (Θ w) := by
  intro l _ A _ _ φ h c hc hsh
  set ψ : A →+* A := φ ^ h with hψdef
  have hψ : ∀ x, φ^[h] x = ψ x := fun x => by rw [hψdef, RingHom.coe_pow]
  have hsh' : ∀ n : ℤ, ψ (c n) = (l : A) * c (n + 1) := fun n => by rw [← hψ]; exact hsh n
  set T : ℕ → A := fun N => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, c n with hT
  have hIcc : ∀ N : ℕ, Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ)
      = insert (-((N + 1 : ℕ) : ℤ)) (insert ((N + 1 : ℕ) : ℤ) (Finset.Icc (-(N : ℤ)) N)) := by
    intro N; ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
  have hstep : ∀ N : ℕ, T (N + 1) = T N + c ((N + 1 : ℕ) : ℤ) + c (-((N + 1 : ℕ) : ℤ)) := by
    intro N
    simp only [hT]
    rw [hIcc N, Finset.sum_insert, Finset.sum_insert]
    · ring
    · simp only [Finset.mem_Icc]; push_cast; omega
    · simp only [Finset.mem_insert, Finset.mem_Icc]; push_cast; omega
  have hdstep : ∀ N : ℕ, (l : A) ^ (N + 1) ∣ T (N + 1) - T N := by
    intro N
    rw [hstep N, show T N + c ((N + 1 : ℕ) : ℤ) + c (-((N + 1 : ℕ) : ℤ)) - T N
      = c ((N + 1 : ℕ) : ℤ) + c (-((N + 1 : ℕ) : ℤ)) by ring]
    refine dvd_add ?_ ?_
    · have := hc ((N + 1 : ℕ) : ℤ)
      rwa [show (((N + 1 : ℕ) : ℤ)).natAbs = N + 1 by omega] at this
    · have := hc (-((N + 1 : ℕ) : ℤ))
      rwa [show (-((N + 1 : ℕ) : ℤ)).natAbs = N + 1 by omega] at this
  have hcauchy : ∀ m n : ℕ, m ≤ n → (l : A) ^ m ∣ T n - T m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      rw [show T (n + 1) - T m = (T (n + 1) - T n) + (T n - T m) by ring]
      exact dvd_add ((pow_dvd_pow _ (by omega)).trans (hdstep n)) ih
  obtain ⟨w, hw⟩ := IsPrecomplete.prec (I := Ideal.span {(l : A)}) inferInstance (f := T)
    (fun {m n} hmn => by
      rw [SModEq.sub_mem, mem_pow_span_iff]
      rw [← dvd_neg, neg_sub]; exact hcauchy m n hmn)
  have hwT : ∀ N : ℕ, (l : A) ^ N ∣ w - T N := by
    intro N
    have := hw N
    rw [SModEq.sub_mem, mem_pow_span_iff] at this
    rw [← dvd_neg, neg_sub]; exact this

  have hE : ∀ N : ℕ, ψ (T N) - (l : A) * T N = (l : A) * (c ((N : ℤ) + 1) - c (-(N : ℤ))) := by
    intro N
    induction N with
    | zero => simp [hT, hsh']; ring
    | succ N ih =>
      rw [hstep N, map_add (f := _), map_add (f := _), hsh', hsh']
      have e1 : (-((N + 1 : ℕ) : ℤ) + 1) = -(N : ℤ) := by push_cast; ring
      have e2 : (((N + 1 : ℕ) : ℤ) + 1) = ((N + 1 : ℕ) : ℤ) + 1 := rfl
      rw [e1]
      push_cast at ih ⊢
      linear_combination ih
  have hEd : ∀ N : ℕ, (l : A) ^ N ∣ ψ (T N) - (l : A) * T N := by
    intro N
    rw [hE N]
    have h1 : (l : A) ^ (N + 1) ∣ c ((N : ℤ) + 1) := by
      have := hc ((N : ℤ) + 1)
      rwa [show ((N : ℤ) + 1).natAbs = N + 1 by omega] at this
    have h2 : (l : A) ^ N ∣ c (-(N : ℤ)) := by simpa using hc (-(N : ℤ))
    exact dvd_mul_of_dvd_right (dvd_sub ((pow_dvd_pow _ (by omega)).trans h1) h2) _
  refine ⟨w, ?_, ?_⟩
  · rw [hψ, ← sub_eq_zero]
    refine IsHausdorff.haus (I := Ideal.span {(l : A)}) inferInstance _ (fun N => ?_)
    rw [SModEq.sub_mem, sub_zero, mem_pow_span_iff]
    rw [show ψ w - (l : A) * w = ψ (w - T N) + (ψ (T N) - (l : A) * T N) - (l : A) * (w - T N) by
      rw [map_sub]; ring]
    refine dvd_sub (dvd_add ?_ (hEd N)) (dvd_mul_of_dvd_right (hwT N) _)
    have := map_dvd ψ (hwT N)
    simpa [map_pow, map_natCast] using this
  · intro Θ hΘ
    set r : ℝ := ‖(l : ℂ_[l])‖ with hr
    have hr1 : r < 1 := by
      have h := PadicComplex.norm_extends' l (l : ℚ_[l])
      have h2 : ‖(l : ℚ_[l])‖ < 1 := Padic.norm_p_lt_one
      rw [← h] at h2
      simpa using h2
    have hr0 : 0 ≤ r := norm_nonneg _
    have hbound : ∀ (n : ℕ) (a : A), (l : A) ^ n ∣ a → ‖Θ a‖ ≤ r ^ n := by
      intro n a ⟨b, hb⟩
      rw [hb, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (pow_nonneg hr0 _) (hΘ b)
    change Filter.Tendsto (fun s : Finset ℤ => ∑ b ∈ s, Θ (c b)) Filter.atTop (nhds (Θ w))
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hr1
    refine ⟨Finset.Icc (-(N : ℤ)) N, fun s hs => ?_⟩
    rw [dist_eq_norm, ← Finset.sum_sdiff hs]
    have hrest : ‖∑ n ∈ s \ Finset.Icc (-(N : ℤ)) N, Θ (c n)‖ ≤ r ^ N := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr0 _) fun n hn => ?_
      have hn' : n ∉ Finset.Icc (-(N : ℤ)) N := (Finset.mem_sdiff.1 hn).2
      rw [Finset.mem_Icc] at hn'
      refine (hbound _ _ (hc n)).trans (pow_le_pow_of_le_one hr0 hr1.le (by omega))
    have hhead : ‖∑ n ∈ Finset.Icc (-(N : ℤ)) N, Θ (c n) - Θ w‖ ≤ r ^ N := by

      rw [← map_sum, ← map_sub]
      refine hbound N _ ?_
      rw [← dvd_neg, neg_sub]; exact hwT N
    rw [add_sub_assoc]
    exact lt_of_le_of_lt ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le hrest hhead)) hN

end GlobalTheory.TwoSidedShift

theorem GlobalTheory.twoSided_shift_series : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (c : ℤ → A), (∀ n : ℤ, (l : A) ^ n.natAbs ∣ c n) → (∀ n : ℤ, φ^[h] (c n) = (l : A) * c (n + 1)) → ∃ w : A, φ^[h] w = (l : A) * w ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) → HasSum (fun n : ℤ => Θ (c n)) (Θ w) :=
  GlobalTheory.TwoSidedShift.exists_sum_shift
end

section

open Polynomial

namespace GlobalTheory

theorem abssum_eigen_lim : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] [IsAdicComplete (Ideal.span {(l : A)}) A] (φ : A →+* A) (h : ℕ) (w : ℕ → A), (∀ k, φ^[h] (w k) = (l : A) * w k) → ∃ W : A, φ^[h] W = (l : A) * W ∧ ∀ Θ : A →+* ℂ_[l], (∀ a, ‖Θ a‖ ≤ 1) → HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * Θ (w k)) (Θ W) := by
  intro l _ A _ _ φ h w hw
  have key : ∀ (n : ℕ) (x : A), x ∈ (Ideal.span {(l : A)} ^ n • ⊤ : Submodule A A) ↔ (l : A) ^ n ∣ x := by
    intro n x
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  let S : ℕ → A := fun N => ∑ k ∈ Finset.range N, (l : A) ^ k * w k
  have hS : ∀ m n, m ≤ n → (l : A) ^ m ∣ S n - S m := by
    intro m n hmn
    simp only [S]
    rw [← Finset.sum_range_add_sum_Ico _ hmn, add_sub_cancel_left]
    apply Finset.dvd_sum
    intro k hk
    exact Dvd.dvd.mul_right (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1) _
  obtain ⟨W, hW⟩ := IsPrecomplete.prec (I := Ideal.span {(l : A)}) (M := A) inferInstance (f := S)
    (fun {m n} hmn => by rw [SModEq.sub_mem, key]; exact dvd_sub_comm.1 (hS m n hmn))
  have hWN : ∀ N, ∃ c : A, W = S N + (l : A) ^ N * c := by
    intro N
    have h1 := SModEq.sub_mem.1 (hW N)
    rw [key] at h1
    obtain ⟨c, hc⟩ := dvd_sub_comm.1 h1
    exact ⟨c, by rw [← hc]; ring⟩
  simp only [← RingHom.coe_pow] at hw ⊢
  have hSψ : ∀ N, (φ ^ h) (S N) = (l : A) * S N := by
    intro N

    simp only [S, map_sum, map_mul, map_pow, map_natCast, hw, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  refine ⟨W, ?_, ?_⟩
  · rw [← sub_eq_zero]
    apply IsHausdorff.haus (I := Ideal.span {(l : A)}) inferInstance
    intro n
    rw [SModEq.sub_mem, sub_zero, key]
    obtain ⟨c, hc⟩ := hWN n
    rw [hc, map_add (f := _), map_mul, map_pow, map_natCast, hSψ]
    exact ⟨(φ ^ h) c - (l : A) * c, by ring⟩
  · intro Θ hΘ
    have hl : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
      rw [show (l : ℂ_[l]) = (((l : ℚ_[l])) : ℂ_[l]) by simp, PadicComplex.norm_extends', Padic.norm_p]
    have hlt : ‖(l : ℂ_[l])‖ < 1 := by
      rw [hl]
      apply inv_lt_one_of_one_lt₀
      exact_mod_cast (Fact.out : l.Prime).one_lt
    have hbound : ∀ k, ‖(l : ℂ_[l]) ^ k * Θ (w k)‖ ≤ ‖(l : ℂ_[l])‖ ^ k := by
      intro k
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (hΘ _)
    have hsum : Summable (fun k => (l : ℂ_[l]) ^ k * Θ (w k)) :=
      Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg _) hlt) hbound
    rw [hsum.hasSum_iff_tendsto_nat]
    have hpart : ∀ N, ∑ i ∈ Finset.range N, (l : ℂ_[l]) ^ i * Θ (w i) = Θ (S N) := by
      intro N

      simp [S, map_sum, map_mul, map_pow, map_natCast]
    simp only [hpart]
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun N => ?_)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hlt)
    obtain ⟨c, hc⟩ := hWN N
    rw [hc, map_add (f := _), sub_add_cancel_left, norm_neg, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (hΘ _)

end GlobalTheory
end

section

open Polynomial
open Classical

namespace GlobalTheory

theorem multiset_many_separated_points : ∀ (K : Type) [NormedAddCommGroup K] (s : Multiset K) (ρ : ℝ) (A B : ℕ), 0 ≤ ρ → 0 < B → A * B ≤ Multiset.card s → (∀ W ∈ s, Multiset.card (s.filter fun z => ‖z - W‖ ≤ ρ) ≤ B) → ∃ Z : Finset K, A ≤ Z.card ∧ (∀ W ∈ Z, W ∈ s) ∧ ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖ := by
  intro K _ s ρ A B hρ hB hAB hball
  set S := s.toFinset.powerset.filter
    (fun Z : Finset K => ∀ W ∈ Z, ∀ W' ∈ Z, W ≠ W' → ρ < ‖W - W'‖) with hS
  have hne : S.Nonempty := ⟨∅, by simp [hS]⟩
  obtain ⟨Z, hZS, hZmax⟩ := Finset.exists_max_image S Finset.card hne
  rw [hS, Finset.mem_filter, Finset.mem_powerset] at hZS
  obtain ⟨hZsub, hZsep⟩ := hZS
  have hZs : ∀ W ∈ Z, W ∈ s := fun W hW => Multiset.mem_toFinset.mp (hZsub hW)
  have hcov : ∀ z ∈ s, ∃ W ∈ Z, ‖z - W‖ ≤ ρ := by
    intro z hz
    by_contra h
    push_neg at h
    have hzZ : z ∉ Z := by
      intro hzZ
      have := h z hzZ
      simp at this
      linarith
    have hmem : insert z Z ∈ S := by
      rw [hS, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.insert_subset (Multiset.mem_toFinset.mpr hz) hZsub, ?_⟩
      intro W hW W' hW' hne
      rw [Finset.mem_insert] at hW hW'
      rcases hW with rfl | hW <;> rcases hW' with rfl | hW'
      · exact absurd rfl hne
      · exact h W' hW'
      · rw [norm_sub_rev]; exact h W hW
      · exact hZsep W hW W' hW' hne
    have := hZmax _ hmem
    rw [Finset.card_insert_of_notMem hzZ] at this
    omega
  have hle : s ≤ ∑ W ∈ Z, s.filter (fun z => ‖z - W‖ ≤ ρ) := by
    rw [Multiset.le_iff_count]
    intro a
    rw [Multiset.count_sum']
    by_cases ha : a ∈ s
    · obtain ⟨W, hW, hd⟩ := hcov a ha
      calc Multiset.count a s = Multiset.count a (s.filter (fun z => ‖z - W‖ ≤ ρ)) := by
            rw [Multiset.count_filter_of_pos (p := fun z => ‖z - W‖ ≤ ρ) hd]
        _ ≤ _ := Finset.single_le_sum
            (f := fun W => Multiset.count a (s.filter (fun z => ‖z - W‖ ≤ ρ)))
            (fun _ _ => Nat.zero_le _) hW
    · rw [Multiset.count_eq_zero_of_notMem ha]; exact Nat.zero_le _
  have hcard : Multiset.card s ≤ Z.card * B := by
    calc Multiset.card s ≤ Multiset.card (∑ W ∈ Z, s.filter (fun z => ‖z - W‖ ≤ ρ)) :=
          Multiset.card_le_card hle
      _ = ∑ W ∈ Z, Multiset.card (s.filter (fun z => ‖z - W‖ ≤ ρ)) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp [map_sum]
      _ ≤ ∑ W ∈ Z, B := Finset.sum_le_sum fun W hW => hball W (hZs W hW)
      _ = Z.card * B := by simp
  exact ⟨Z, Nat.le_of_mul_le_mul_right (hAB.trans hcard) hB, hZs, hZsep⟩

end GlobalTheory
end

section

namespace GlobalTheory.OneAddPowBound

theorem one_add_pow_le : ∀ {t : ℝ}, (0 : ℝ) ≤ t → ∀ (k : ℕ),
    ((1 : ℝ) + t) ^ k ≤ (2 : ℝ) ^ k * ((1 : ℝ) + t ^ k) := by
  intro t ht k
  have htk : 0 ≤ t ^ k := pow_nonneg ht k
  have h2 : (0 : ℝ) ≤ 2 ^ k := pow_nonneg (by norm_num) k
  have h1 : (0 : ℝ) ≤ 1 + t := by linarith
  rcases le_total t 1 with h | h
  · have ha : (1 + t) ^ k ≤ (2 : ℝ) ^ k := pow_le_pow_left₀ h1 (by linarith) k
    have hb : (2 : ℝ) ^ k * 1 ≤ 2 ^ k * (1 + t ^ k) :=
      mul_le_mul_of_nonneg_left (by linarith) h2
    linarith
  · have ha : (1 + t) ^ k ≤ (2 * t) ^ k := pow_le_pow_left₀ h1 (by linarith) k
    rw [mul_pow] at ha
    have hb : (2 : ℝ) ^ k * t ^ k ≤ 2 ^ k * (1 + t ^ k) :=
      mul_le_mul_of_nonneg_left (by linarith) h2
    linarith

end GlobalTheory.OneAddPowBound
end
