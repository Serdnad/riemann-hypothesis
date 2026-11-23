module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1307
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionIsLieAction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicTypeEqZeroOfTorusLawAtOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038

@[expose] public section

section

set_option autoImplicit false

open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_ncard_ball_exp_le : ∀ (G : Type) [AddCommGroup G] (Λ : ℕ → AddSubgroup G) (B : ℕ → ℝ → Set G) (d : ℕ),
    0 < d → (∀ m, IsBallFam (Λ m) (B m)) → (∀ m R, (B m R).Finite) → ∀ C : ℝ,
    (∀ᶠ m : ℕ in atTop, Real.log ((B m (Real.exp (3 * m))).ncard : ℝ) ≤ C * (m : ℝ) ^ d) →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ m : ℕ in atTop,
      Real.log ((B m (Real.exp (δ * m))).ncard : ℝ) ≤ Real.log ((B m 1).ncard : ℝ) + ε * (m : ℝ) ^ d := by
  intro G _ Λ B d _ hB hfin C hC ε hε
  set e : ℕ := max 1 ⌈C / ε⌉₊ with he_def
  have he1 : 1 ≤ e := le_max_left _ _
  have heR : (0 : ℝ) < e := by exact_mod_cast he1
  have he1R : (1 : ℝ) ≤ e := by exact_mod_cast he1
  have hCe : C ≤ ε * e := by
    have h1 : C / ε ≤ (⌈C / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈C / ε⌉₊ : ℝ) ≤ e := by exact_mod_cast le_max_right _ _
    rw [div_le_iff₀ hε] at h1
    nlinarith
  refine ⟨1 / e, by positivity, ?_⟩
  filter_upwards [hC, eventually_ge_atTop (3 * e)] with m hm hm3
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set R := Real.exp (1 / e * m) with hR
  have hR1 : 1 ≤ R := Real.one_le_exp (by positivity)
  set Q := ⌈2 * R + 1⌉₊ with hQdef
  have hQ : 2 * R + 1 ≤ Q := Nat.le_ceil _
  have hQ4 : (Q : ℝ) ≤ 4 * R := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 2 * R + 1 by linarith)
    linarith
  have key := GlobalTheory.T.encard_seminormBall_pow_le_radius_change G (Λ m) (B m) (hB m) R Q e hR1 hQ (hfin m R)
  have mono : ∀ r s : ℝ, r ≤ s → B m r ⊆ B m s := by
    intro r s hrs x hx
    have := (hB m).sub_mem r (s - r) x 0 hx ((hB m).zero_mem _ (by linarith))
    simpa using this
  have hRe : R ^ (e + 1) ≤ Real.exp (2 * m) := by
    rw [hR, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have : (m : ℝ) / e ≤ m := div_le_self hm0 he1R
    have h3 : ((e + 1 : ℕ) : ℝ) * (1 / e * m) = m + m / e := by
      push_cast; field_simp
    rw [h3]; linarith
  have hbig : R * (Q : ℝ) ^ e ≤ Real.exp (3 * m) := by
    have h4 : (4 : ℝ) ≤ Real.exp 3 := by
      have := Real.add_one_le_exp 3; linarith
    have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
    calc R * (Q : ℝ) ^ e ≤ R * (4 * R) ^ e := by gcongr
      _ = 4 ^ e * R ^ (e + 1) := by ring
      _ ≤ Real.exp 3 ^ e * Real.exp (2 * m) := by gcongr
      _ = Real.exp (3 * e + 2 * m) := by rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (3 * m) := by
        apply Real.exp_le_exp.mpr
        have : (3 * e : ℝ) ≤ m := by exact_mod_cast hm3
        linarith
  have hsub := mono _ _ hbig
  have hN : (B m R).ncard ^ e ≤ (B m 1).ncard ^ e * (B m (Real.exp (3 * m))).ncard := by
    rw [← (hfin m R).cast_ncard_eq, ← (hfin m 1).cast_ncard_eq, ← (hfin m _).cast_ncard_eq] at key
    norm_cast at key
    have hsub' : B m (R * ((Q ^ e : ℕ) : ℝ)) ⊆ B m (Real.exp (3 * m)) := by push_cast; exact hsub
    exact key.trans (Nat.mul_le_mul_left _ (Set.ncard_le_ncard hsub' (hfin m _)))
  have pos : ∀ r : ℝ, 0 ≤ r → (0 : ℝ) < (B m r).ncard := fun r hr => by
    exact_mod_cast (Set.ncard_pos (hfin m r)).mpr ⟨0, (hB m).zero_mem r hr⟩
  have hA := pos R (by linarith)
  have h1 := pos 1 zero_le_one
  have h3 := pos (Real.exp (3 * m)) (Real.exp_pos _).le
  have hNR : ((B m R).ncard : ℝ) ^ e ≤ ((B m 1).ncard : ℝ) ^ e * (B m (Real.exp (3 * m))).ncard := by
    exact_mod_cast hN
  have hlog := Real.log_le_log (by positivity) hNR
  rw [Real.log_mul (by positivity) h3.ne', Real.log_pow, Real.log_pow] at hlog
  have hCm : C * (m : ℝ) ^ d ≤ ε * e * (m : ℝ) ^ d := mul_le_mul_of_nonneg_right hCe (pow_nonneg hm0 d)
  have : (e : ℝ) * Real.log ((B m R).ncard : ℝ) ≤
      e * (Real.log ((B m 1).ncard : ℝ) + ε * (m : ℝ) ^ d) := by nlinarith
  exact le_of_mul_le_mul_left this heR

end GlobalTheory.VolBr
end

section

open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem IsBallFam.subset_of_le_radius {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (h : IsBallFam Λ B) {r r' : ℝ} (hr : r ≤ r') : B r ⊆ B r' := by
  intro x hx
  have := h.sub_mem r (r' - r) x 0 hx (h.zero_mem _ (by linarith))
  simpa using this

theorem IsBallFam.ncard_sq_le_of_ceil {G : Type} [AddCommGroup G] {Λ : AddSubgroup G} {B : ℝ → Set G}
    (h : IsBallFam Λ B) (hfin : ∀ R, (B R).Finite) {e E : ℝ} (he : 1 ≤ e)
    (hE : (⌈2 * e⌉₊ : ℝ) ^ 2 + (⌈2 * e⌉₊ : ℝ) / 2 ≤ E) :
    ((B e).ncard : ℝ) ^ 2 ≤ (B 1).ncard * (B E).ncard := by
  have hn2 : 2 * e ≤ (⌈2 * e⌉₊ : ℝ) := Nat.le_ceil _
  have hnpos : 0 < ⌈2 * e⌉₊ := by
    have : (0:ℝ) < (⌈2 * e⌉₊ : ℝ) := by linarith
    exact_mod_cast this
  have key := GlobalTheory.T.encard_seminormBall_mul_le_convexity G Λ B h _ hnpos (hfin _)
  rw [← (hfin _).cast_ncard_eq, ← (hfin _).cast_ncard_eq, ← (hfin _).cast_ncard_eq,
    ← (hfin _).cast_ncard_eq] at key
  have key' : (B (⌈2 * e⌉₊ : ℝ)).ncard * (B ((⌈2 * e⌉₊ : ℝ) / 2)).ncard ≤
      (B 1).ncard * (B ((⌈2 * e⌉₊ : ℝ) ^ 2 + (⌈2 * e⌉₊ : ℝ) / 2)).ncard := by
    have := key
    exact_mod_cast this
  have h1 : (B e).ncard ≤ (B (⌈2 * e⌉₊ : ℝ)).ncard :=
    Set.ncard_le_ncard (h.subset_of_le_radius (by linarith)) (hfin _)
  have h2 : (B e).ncard ≤ (B ((⌈2 * e⌉₊ : ℝ) / 2)).ncard :=
    Set.ncard_le_ncard (h.subset_of_le_radius (by linarith)) (hfin _)
  have h3 : (B ((⌈2 * e⌉₊ : ℝ) ^ 2 + (⌈2 * e⌉₊ : ℝ) / 2)).ncard ≤ (B E).ncard :=
    Set.ncard_le_ncard (h.subset_of_le_radius hE) (hfin _)
  have : (B e).ncard ^ 2 ≤ (B 1).ncard * (B E).ncard := by
    calc (B e).ncard ^ 2 = (B e).ncard * (B e).ncard := sq _
      _ ≤ (B (⌈2 * e⌉₊ : ℝ)).ncard * (B ((⌈2 * e⌉₊ : ℝ) / 2)).ncard := Nat.mul_le_mul h1 h2
      _ ≤ (B 1).ncard * (B ((⌈2 * e⌉₊ : ℝ) ^ 2 + (⌈2 * e⌉₊ : ℝ) / 2)).ncard := key'
      _ ≤ _ := Nat.mul_le_mul_left _ h3
  exact_mod_cast this

theorem log_ncard_ball_one_eventually_ge : ∀ (G : Type) [AddCommGroup G] (Λ : ℕ → AddSubgroup G)
    (B : ℕ → ℝ → Set G) (d : ℕ), 0 < d → (∀ m, IsBallFam (Λ m) (B m)) → (∀ m R, (B m R).Finite) →
    ∀ α β t₀ : ℝ, (∀ t, t₀ ≤ t → Tendsto (fun m : ℕ => Real.log ((B m (Real.exp (t * m))).ncard : ℝ) /
      (m : ℝ) ^ d) atTop (𝓝 (α + β * t))) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      (α - ε) * (m : ℝ) ^ d ≤ Real.log ((B m 1).ncard : ℝ) := by
  intro G _ Λ B d _ hB hfin α β t₀ hlim ε hε
  obtain ⟨t, ht0, ht⟩ : ∃ t, t₀ ≤ t ∧ 0 ≤ t := ⟨max t₀ 0, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨η, hη, hβη⟩ : ∃ η : ℝ, 0 < η ∧ β * η < ε := by
    refine ⟨ε / (2 * (|β| + 1)), by positivity, ?_⟩
    have hpos : 0 < 2 * (|β| + 1) := by positivity
    have hηe : ε / (2 * (|β| + 1)) * (2 * (|β| + 1)) = ε := div_mul_cancel₀ _ hpos.ne'
    have hη : 0 < ε / (2 * (|β| + 1)) := by positivity
    have hb : β * (ε / (2 * (|β| + 1))) ≤ |β| * (ε / (2 * (|β| + 1))) :=
      mul_le_mul_of_nonneg_right (le_abs_self β) hη.le
    nlinarith [mul_nonneg (abs_nonneg β) hη.le]
  have hw := ((hlim t ht0).const_mul 2).sub (hlim (2 * t + η) (by linarith))
  have hlt : α - ε < 2 * (α + β * t) - (α + β * (2 * t + η)) := by
    have : 2 * (α + β * t) - (α + β * (2 * t + η)) = α - β * η := by ring
    rw [this]; linarith
  have ev1 := hw.eventually (lt_mem_nhds hlt)
  have ev2 : ∀ᶠ m : ℕ in atTop, Real.log 12 ≤ η * m :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop hη).eventually_ge_atTop _
  filter_upwards [ev1, ev2, eventually_ge_atTop 1] with m h1 h2 hm
  have hmpos : (0:ℝ) < m := by exact_mod_cast hm
  have hmd : (0:ℝ) < (m:ℝ) ^ d := pow_pos hmpos d
  have he : 1 ≤ Real.exp (t * m) := Real.one_le_exp (mul_nonneg ht hmpos.le)
  have h12 : 12 ≤ Real.exp (η * m) := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 12)]; exact Real.exp_le_exp.mpr h2
  have hE : (⌈2 * Real.exp (t * m)⌉₊ : ℝ) ^ 2 + (⌈2 * Real.exp (t * m)⌉₊ : ℝ) / 2 ≤
      Real.exp ((2 * t + η) * m) := by
    have hc : (⌈2 * Real.exp (t * m)⌉₊ : ℝ) ≤ 3 * Real.exp (t * m) := by
      have := Nat.ceil_lt_add_one (show 0 ≤ 2 * Real.exp (t * m) by linarith); linarith
    have hc0 : (0:ℝ) ≤ ⌈2 * Real.exp (t * m)⌉₊ := Nat.cast_nonneg _
    rw [show (2 * t + η) * (m:ℝ) = t * m + t * m + η * m by ring, Real.exp_add, Real.exp_add]
    nlinarith [mul_le_mul hc hc hc0 (by linarith), mul_le_mul_of_nonneg_left h12
      (mul_nonneg (by linarith : (0:ℝ) ≤ Real.exp (t * m)) (by linarith : (0:ℝ) ≤ Real.exp (t * m)))]
  have hsq := (hB m).ncard_sq_le_of_ceil (hfin m) he hE
  have hpos : ∀ R, 0 ≤ R → (0:ℝ) < (B m R).ncard := fun R hR => by
    have := (Set.ncard_pos (hfin m R)).mpr ⟨0, (hB m).zero_mem R hR⟩
    exact_mod_cast this
  have hlog := Real.log_le_log (pow_pos (hpos _ (by linarith)) 2) hsq
  rw [Real.log_pow, Real.log_mul (hpos 1 zero_le_one).ne' (hpos _ (Real.exp_pos _).le).ne'] at hlog
  push_cast at hlog
  have hdiv : (2 * Real.log ((B m (Real.exp (t * m))).ncard) - Real.log ((B m (Real.exp ((2 * t + η) * m))).ncard))
      / (m:ℝ) ^ d ≤ Real.log ((B m 1).ncard) / (m:ℝ) ^ d :=
    div_le_div_of_nonneg_right (by linarith) hmd.le
  rw [sub_div, mul_div_assoc] at hdiv
  rw [← le_div_iff₀ hmd]
  linarith

end GlobalTheory.VolBr
end

section

open Filter Topology
open GlobalTheory GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem log_ncard_unit_ball_le_of_indep_bound :
    ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B →
      (B 1).Finite → ∀ (q : ℕ) (T : ℝ), 3 ≤ q → 0 ≤ T →
      (∀ (r : ℕ) (e : Fin r → G) (n : Fin r → ℕ), LinearIndependent ℤ e → (∀ j, e j ∈ B ((2 / q : ℝ) ^ n j)) →
        ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ T) → Real.log ((B 1).ncard : ℝ) ≤ Real.log q * T := by
  classical
  intro G _ _ Λ B hB hfin q T hq hT hbound
  set S : ℕ → Set G := fun i => B ((2 / q : ℝ) ^ i) with hS
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hmono := (isBallFam_mono_neg_add G Λ B hB).1
  have hSdec : ∀ i, S (i + 1) ⊆ S i := by
    intro i
    apply hmono
    have h0 : (0 : ℝ) ≤ 2 / q := by positivity
    have h1 : (2 / q : ℝ) ≤ 1 := by
      rw [div_le_one hqpos]; exact_mod_cast (by omega : 2 ≤ q)
    exact pow_le_pow_of_le_one h0 h1 (Nat.le_succ i)
  set K : ℕ := ⌊T⌋₊ with hK

  have hsize : ∀ i m (e : Fin m → G), LinearIndependent ℤ e → (∀ j, e j ∈ S i) → m ≤ K := by
    intro i m e he hmem
    have h := hbound m e (fun _ => i) he hmem
    apply Nat.le_floor
    refine le_trans ?_ h
    have : m ≤ ∑ _j : Fin m, (i + 1) := by simp; exact Nat.le_mul_of_pos_right m (Nat.succ_pos i)
    exact_mod_cast this
  let P : ℕ → ℕ → Prop := fun i m => ∃ e : Fin m → G, LinearIndependent ℤ e ∧ ∀ j, e j ∈ S i
  let r : ℕ → ℕ := fun i => Nat.findGreatest (P i) K
  have hP0 : ∀ i, P i 0 := fun i => ⟨Fin.elim0, linearIndependent_empty_type, fun j => j.elim0⟩
  have hrspec : ∀ i, P i (r i) := fun i => Nat.findGreatest_spec (Nat.zero_le K) (hP0 i)
  have hrmax : ∀ i m (e : Fin m → G), LinearIndependent ℤ e → (∀ j, e j ∈ S i) → m ≤ r i := by
    intro i m e he hmem
    exact Nat.le_findGreatest (hsize i m e he hmem) ⟨e, he, hmem⟩
  have hrdec : ∀ i, r (i + 1) ≤ r i := by
    intro i
    obtain ⟨e, he, hmem⟩ := hrspec (i + 1)
    exact hrmax i _ e he (fun j => hSdec i (hmem j))

  have hstep : ∀ i, (S i).encard ≤ ((q ^ r i : ℕ) : ℕ∞) * (S (i + 1)).encard := by
    intro i
    have h := GlobalTheory.T.encard_seminormBall_le_pow_mul_smaller G Λ B hB ((2 / q : ℝ) ^ i) q (r i) (by omega)
      (fun n e he hmem => hrmax i n e he hmem)
    have heq : 2 * (2 / q : ℝ) ^ i / q = (2 / q : ℝ) ^ (i + 1) := by
      rw [pow_succ]; ring
    simpa [hS, heq] using h
  have hiter : ∀ k, (S 0).encard ≤ ((q ^ (∑ i ∈ Finset.range k, r i) : ℕ) : ℕ∞) * (S k).encard := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      refine ih.trans ?_
      rw [Finset.sum_range_succ, pow_add, Nat.cast_mul, mul_assoc]
      gcongr
      exact hstep k

  have hSK : S K ⊆ {0} := by
    intro x hx
    by_contra hx0
    have hli : LinearIndependent ℤ (fun _ : Fin 1 => x) := by
      letI : HasUniqueDiv G := ⟨by
        intro n hn a b h
        exact eq_of_nsmul_eq_nsmul_of_addCommute hn (AddCommute.all _ _) h⟩
      rw [linearIndependent_unique_iff]; exact hx0
    have h := hbound 1 (fun _ => x) (fun _ => K) hli (fun _ => hx)
    have hlt : T < (K : ℝ) + 1 := Nat.lt_floor_add_one T
    simp at h
    linarith
  have hSK1 : (S K).encard ≤ 1 := by
    calc (S K).encard ≤ ({0} : Set G).encard := Set.encard_le_encard hSK
      _ = 1 := Set.encard_singleton 0

  obtain ⟨e, n, he, hmem, hsum⟩ := GlobalTheory.T.exists_linearIndependent_adapted_to_decreasing_chain' G S hSdec K r hrspec hrdec
  have hM : ((∑ i ∈ Finset.range K, r i : ℕ) : ℝ) ≤ T := by
    have h1 := hbound (r 0) e n he hmem
    have h2 : ∑ i ∈ Finset.range K, r i ≤ ∑ i ∈ Finset.range (K + 1), r i :=
      Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (Nat.le_succ K))
    have h3 : ((∑ i ∈ Finset.range K, r i : ℕ) : ℝ) ≤ ((∑ j, (n j + 1) : ℕ) : ℝ) := by
      exact_mod_cast h2.trans hsum
    linarith
  set M := ∑ i ∈ Finset.range K, r i with hMdef
  have hS0 : S 0 = B 1 := by simp [hS]
  have hcard : (B 1).encard ≤ ((q ^ M : ℕ) : ℕ∞) := by
    rw [← hS0]
    calc (S 0).encard ≤ ((q ^ M : ℕ) : ℕ∞) * (S K).encard := hiter K
      _ ≤ ((q ^ M : ℕ) : ℕ∞) * 1 := by gcongr
      _ = _ := mul_one _
  have hncard : (B 1).ncard ≤ q ^ M := by
    rw [← hfin.cast_ncard_eq] at hcard
    exact_mod_cast hcard
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  rcases Nat.eq_zero_or_pos (B 1).ncard with h0 | hpos
  · rw [h0]; simp; positivity
  · have hpos' : (0 : ℝ) < (B 1).ncard := by exact_mod_cast hpos
    calc Real.log ((B 1).ncard : ℝ) ≤ Real.log ((q ^ M : ℕ) : ℝ) :=
          Real.log_le_log hpos' (by exact_mod_cast hncard)
      _ = M * Real.log q := by rw [Nat.cast_pow, Real.log_pow]
      _ ≤ T * Real.log q := by gcongr
      _ = Real.log q * T := mul_comm _ _

end GlobalTheory.VolBr
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VolBr.SmallBall

theorem nsq_shift_pow {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} (L : HermLB p) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (m : ℕ) (σ : k →+* ℂ) (f : (L.pow m).B.ι → CxPts p σ → ℂ)
    (y : CxPts p σ) :
    (((L.shift t ht).pow m).φ σ).nsq f y = ((L.pow m).φ σ).nsq f y * Real.exp (-(2 * m * t σ)) := by
  simp only [Weight.nsq, HermLB.pow, HermLB.shift, Weight.pow]
  erw [Weight.zpow_φ, Weight.zpow_φ]
  rw [mul_assoc, ← Real.exp_add]
  simp only [Weight.addFn]
  congr 2
  push_cast
  ring

theorem mul_exp_le_one_iff (x c d : ℝ) (h : d = 2 * c) : x * Real.exp (-d) ≤ 1 ↔ x ≤ Real.exp c ^ 2 := by
  rw [sq, ← Real.exp_add, ← two_mul, ← h, Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos d)]

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}

theorem nu_nonneg (P : Pair p) (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    0 ≤ P.nu a b σ y f := by
  unfold Pair.nu; positivity

theorem encard_eq_Bl (P : Pair p) {a b : ℤ} {N : HermLB p} (h : P.Rep a b N) (S : Set N.B.Sec) (R : ℝ) (hR : 0 ≤ R)
    (hS : ∀ u, u ∈ S ↔ ∀ σ (y : CxPts p σ), (N.φ σ).nsq (secVal p σ u) y ≤ R ^ 2) :
    S.encard = (P.Bl a b R).encard := by
  obtain ⟨e, he, hr, hn, -⟩ := GlobalTheory.T.representedBundle_sections_rationalFunctions_dict k X p P a b N h
  have hi : e '' S = P.Bl a b R := by
    ext f
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨?_, fun σ y => ?_⟩
      · have : e u ∈ Set.range e := ⟨u, rfl⟩
        rw [hr] at this
        exact this
      · have h1 := (hS u).1 hu σ y
        rw [← hn] at h1
        exact (pow_le_pow_iff_left₀ (nu_nonneg P a b σ y _) hR two_ne_zero).1 h1
    · rintro ⟨hf, hb⟩
      have : f ∈ Set.range e := by rw [hr]; exact hf
      obtain ⟨u, rfl⟩ := this
      refine ⟨u, (hS u).2 fun σ y => ?_, rfl⟩
      rw [← hn]
      exact pow_le_pow_left₀ (nu_nonneg P a b σ y _) (hb σ y) 2
  rw [← hi, he.encard_image]

theorem main : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (M : HermLB p), P.Rep a b M → ∀ (t : ℝ) (m : ℕ), ((M.shift (fun _ => t) fun _ => rfl).pow m).smallSec.encard = (P.Bl (m * a) (m * b) (Real.exp (t * m))).encard ∧ (M.pow m).smallSec.encard = (P.Bl (m * a) (m * b) 1).encard ∧ (M.shift (fun _ => t) fun _ => rfl).smallSec.encard = (P.Bl a b (Real.exp t)).encard := by
  intro k _ X _ p P a b M hM t m
  have hm := GlobalTheory.T.represents_hermitianLineBundle_pow k X p P a b M m hM
  refine ⟨?_, ?_, ?_⟩
  · refine encard_eq_Bl P hm _ _ (Real.exp_pos _).le fun u => ?_
    simp only [HermLB.smallSec, Set.mem_setOf_eq]
    refine forall_congr' fun σ => forall_congr' fun y => ?_
    have e := nsq_shift_pow M (fun _ => t) (fun _ => rfl) m σ (secVal p σ u) y
    exact (iff_of_eq (congrArg (· ≤ (1 : ℝ)) e)).trans (mul_exp_le_one_iff _ _ _ (by ring))
  · refine encard_eq_Bl P hm _ _ zero_le_one fun u => ?_
    simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  · refine encard_eq_Bl P hM _ _ (Real.exp_pos _).le fun u => ?_
    simp only [HermLB.smallSec, Set.mem_setOf_eq]
    refine forall_congr' fun σ => forall_congr' fun y => ?_
    have e := HermLB.nsq_shift M (fun _ => t) (fun _ => rfl) (σ := σ) (secVal p σ u) y
    exact (iff_of_eq (congrArg (· ≤ (1 : ℝ)) e)).trans (mul_exp_le_one_iff _ _ _ (by ring))

end GlobalTheory.VolBr.SmallBall
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.div_pow_mem_sections_of_mul_pow_mem_twisted : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, ∀ (N m : ℕ) (u : X.functionField), u ∈ P.H N (m - c) → u * t ^ N / s ^ m ∈ P.H 0 (b * N - c) → u / s ^ m ∈ P.H N (-c) := by
  first | exact @GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow_sub | exact GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow_sub | (intros; apply GlobalTheory.VolBr.Pair.div_pow_mem_H_of_mul_pow_sub <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.exists_ampleSection_clearing_rationalFunction_denominator : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.A.B → ∀ (f : X.functionField), ∃ (c : ℕ) (g : X.functionField), 0 < c ∧ g ≠ 0 ∧ g ∈ P.H 0 c ∧ g * f ∈ P.H 0 c := by
  first | exact @GlobalTheory.HSNef.DenOne.exists_den_one | exact GlobalTheory.HSNef.DenOne.exists_den_one | (intros; apply GlobalTheory.HSNef.DenOne.exists_den_one <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

theorem _root_.GlobalTheory.T.exists_hermPairSections_change_of_isometric_combinations : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k), ∀ (P : Pair p) (a b a' b' : ℤ) (M N : HermLB p), P.Rep a b M → P.Rep a' b' N → ∃ Q : Pair p, Q.L = M ∧ Q.A = N ∧ ∀ (i j : ℤ) (R : ℝ), Q.Bl i j R = P.Bl (i * a + j * a') (i * b + j * b') R := by
  first | exact @GlobalTheory.HSNef.change_pair | exact GlobalTheory.HSNef.change_pair | (intros; apply GlobalTheory.HSNef.change_pair <;> assumption)
end

section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr.NuPow

theorem pow_mem_H_and_nu_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p), ∀ (a b : ℤ) (f : X.functionField), f ∈ P.H a b → ∀ n : ℕ, f ^ n ∈ P.H (n * a) (n * b) ∧ ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu (n * a) (n * b) σ y (f ^ n) = P.nu a b σ y f ^ n := by
  intro k _ X _ p P a b f hf n
  induction n with
  | zero =>
    refine ⟨fun x i j _ _ => ⟨1, by simp [Pair.loc]⟩, fun σ y => ?_⟩
    have e := ratVal_fnOf (y := y) mem_ptsIn_top trivial 1
    rw [map_one, ev_one mem_ptsIn_top] at e
    simp [Pair.nu, Pair.loc, e]
  | succ n ih =>
    obtain ⟨h1, h2⟩ := GlobalTheory.T.hermLineBundlePair_sections_mul_mem_norm_mul k X p P _ _ a b _ f ih.1 hf
    have ea : ((n + 1 : ℕ) : ℤ) * a = n * a + a := by push_cast; ring
    have eb : ((n + 1 : ℕ) : ℤ) * b = n * b + b := by push_cast; ring
    rw [ea, eb, pow_succ]
    exact ⟨h1, fun σ y => by rw [h2 σ y, ih.2 σ y, pow_succ]⟩

end GlobalTheory.VolBr.NuPow
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.complexifiedDerivedAction_isLieAction : ∀ (n : ℕ) (Hm : Mt n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mt n → (H →L[ℂ] H)), Hm.IsHermitian → Hm.det ≠ 0 → IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → ∀ v v', SmoothVec (lieH Hm) σ v → SmoothVec (lieH Hm) σ v' → (∀ (a : ℂ) (Z Z' : Mt n), dRepC Hm σ (a • Z + Z') v = a • dRepC Hm σ Z v + dRepC Hm σ Z' v ∧ dRepC Hm σ Z (a • v + v') = a • dRepC Hm σ Z v + dRepC Hm σ Z v' ∧ dRepC Hm σ (Z * Z' - Z' * Z) v = dRepC Hm σ Z (dRepC Hm σ Z' v) - dRepC Hm σ Z' (dRepC Hm σ Z v)) ∧ (∀ X ∈ lieH Hm, dRepC Hm σ X v = dRep σ X v) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ∀ Z, σ g (dRepC Hm σ Z v) = dRepC Hm σ (g * Z * g⁻¹) (σ g v)) ∧ ∀ Z, ⟪dRepC Hm σ Z v, v'⟫_ℂ = -⟪v, dRepC Hm σ (conjH Hm Z) v'⟫_ℂ := by
  first | exact @GlobalTheory.HolDict.LieAct.main | exact GlobalTheory.HolDict.LieAct.main | (intros; apply GlobalTheory.HolDict.LieAct.main <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.holomorphicType_eq_zero_of_torus_law_at_one : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Hm : ι → Mt n) (q : ι → ℕ) (x₀ : ι → Mt n) (w : ι → Fin n → ℤ), (∀ τ, OrthFr (Hm τ) (q τ) (x₀ τ)) → ∀ f, HolFn Hm q x₀ w f → (∀ u ∈ UG Hm, ∀ s, f (torEl x₀ s * u) = torCh w s * f u) → f 1 = 0 → ∀ u ∈ UG Hm, f u = 0 := by
  first | exact @GlobalTheory.HolDict.Uniq.eq_zero_of_torus_law | exact GlobalTheory.HolDict.Uniq.eq_zero_of_torus_law | (intros; apply GlobalTheory.HolDict.Uniq.eq_zero_of_torus_law <;> assumption)
end
