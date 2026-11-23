module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.RingTheory.Valuation.Integers
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.FieldTheory.Galois.Infinite

@[expose] public section

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

open Polynomial

theorem moves_fix_of_moves : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L] [Finite G], (∀ (g : G) (x : L), v (g • x) = v x) →
    ∀ (N : Subgroup G) (i : ℝ≥0), i < 1 → (∀ τ ∈ N, ∀ x : L, v x ≤ 1 → v (τ • x - x) ≤ i) →
    ∀ σ : G, Moves v ⊤ σ → Moves v (Fix L N) σ := by
  intro L _ v G _ _ _ hinv N i hi hN σ hσ r hr
  classical
  by_contra hcon
  push_neg at hcon
  haveI := Fintype.ofFinite G
  set n := Fintype.card N with hn_def
  have hn : n ≠ 0 := Fintype.card_ne_zero
  set t : ℝ≥0 := max i (r ^ ((n : ℝ)⁻¹)) with ht_def
  have ht1 : t < 1 := max_lt hi (NNReal.rpow_lt_one hr (by positivity))
  have hrt : r ≤ t ^ n := by
    calc r = (r ^ ((n : ℝ)⁻¹)) ^ n := (NNReal.rpow_inv_natCast_pow r hn).symm
      _ ≤ t ^ n := pow_le_pow_left₀ zero_le (le_max_right _ _) n
  obtain ⟨x, -, hx1, hxt⟩ := hσ t ht1

  have hfac : ∀ τ : N, v (x - σ • ((τ : G) • x)) = v (σ • x - x) := by
    intro τ
    have h1 : v (σ • x - σ • ((τ : G) • x)) < v (x - σ • x) := by
      rw [← smul_sub, hinv, Valuation.map_sub_swap, Valuation.map_sub_swap v x]
      exact lt_of_le_of_lt (le_trans (hN τ τ.2 x hx1) (le_max_left _ _)) hxt
    have h2 : x - σ • ((τ : G) • x) = (x - σ • x) + (σ • x - σ • ((τ : G) • x)) := by ring
    rw [h2, Valuation.map_add_eq_of_lt_left v h1, Valuation.map_sub_swap]

  set P : L[X] := ∏ τ : N, (X - C ((τ : G) • x)) with hP_def
  have hint : ∀ τ : N, (τ : G) • x ∈ v.integer := fun τ => by
    rw [Valuation.mem_integer_iff, hinv]; exact hx1
  set Q : (v.integer)[X] := ∏ τ : N, (X - C (⟨(τ : G) • x, hint τ⟩ : v.integer)) with hQ_def
  have hPQ : P = Q.map (v.integer.subtype) := by
    simp [hP_def, hQ_def, Polynomial.map_prod]
  have hcint : ∀ k, v (P.coeff k) ≤ 1 := by
    intro k
    rw [hPQ, coeff_map]
    exact (Q.coeff k).2
  have hcfix : ∀ k, P.coeff k ∈ Fix L N := by
    intro k m
    have hmap : P.map (MulSemiringAction.toRingHom G L (m : G)) = P := by
      rw [hP_def, Polynomial.map_prod]
      simp only [Polynomial.map_sub, map_X, map_C, MulSemiringAction.toRingHom_apply, smul_smul]
      exact Fintype.prod_equiv (Equiv.mulLeft m) _ _ (fun τ => by simp)
    have := congrArg (fun p => p.coeff k) hmap
    have h' : (m : G) • P.coeff k = P.coeff k := by simpa [coeff_map] using this
    exact h'
  have hPx : P.eval x = 0 := by
    rw [hP_def, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simp)
  have hPσx : (P.map (MulSemiringAction.toRingHom G L σ)).eval x = ∏ τ : N, (x - σ • ((τ : G) • x)) := by
    simp [hP_def, Polynomial.map_prod, eval_prod]

  have hdiff : v ((P.map (MulSemiringAction.toRingHom G L σ) - P).eval x) ≤ r := by
    rw [eval_eq_sum, Polynomial.sum_def]
    apply Valuation.map_sum_le
    intro k _
    rw [map_mul, map_pow, coeff_sub, coeff_map, MulSemiringAction.toRingHom_apply]
    calc v (σ • P.coeff k - P.coeff k) * v x ^ k ≤ r * 1 :=
          mul_le_mul' (hcon _ (hcfix k) (hcint k)) (pow_le_one₀ zero_le hx1)
      _ = r := mul_one r
  rw [eval_sub, hPx, sub_zero, hPσx, map_prod] at hdiff
  simp only [hfac, Finset.prod_const, Finset.card_univ] at hdiff
  have := pow_lt_pow_left₀ hxt zero_le hn
  exact absurd (lt_of_le_of_lt (hdiff.trans hrt) this) (lt_irrefl _)

end GlobalTheory.AlmostEt
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem almostSep_subgroupOf (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L] (U H : Subgroup G) (hU : AlmostSep v U) :
    AlmostSep v (U.subgroupOf H) := by
  intro r hr
  obtain ⟨n, a, b, c, hs, hc⟩ := hU r hr
  have hfix : ∀ x : L, x ∈ Fix L U → x ∈ Fix L (U.subgroupOf H) := by
    intro x hx σ
    exact hx ⟨(σ.1 : G), Subgroup.mem_subgroupOf.mp σ.2⟩
  refine ⟨n, a, b, c, ⟨fun i => hfix _ (hs.a_mem i), fun i => hfix _ (hs.b_mem i),
    hfix _ hs.c_mem, hs.a_le, hs.b_le, hs.c_le, ?_, ?_⟩, hc⟩
  · intro σ hσ
    exact hs.sum_in (σ : G) (Subgroup.mem_subgroupOf.mp hσ)
  · intro σ hσ
    exact hs.sum_out (σ : G) (fun h => hσ (Subgroup.mem_subgroupOf.mpr h))

end GlobalTheory.AlmostEt
end

section

open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem sum_mul_cosetTrace_eq (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G]
    [MulSemiringAction G L] (N : Subgroup G) [Fintype (G ⧸ N)] (n : ℕ) (a b : Fin n → L) (c : L)
    (h : IsSep v N a b c) : ∀ x ∈ Fix L N, ∑ i, a i * cosetTrace N (b i * x) = c * x := by
  classical
  intro x hx
  have hmem : ∀ q : G ⧸ N, q.out ∈ N ↔ q = ((1 : G) : G ⧸ N) := by
    intro q
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rw [QuotientGroup.eq, mul_one, inv_mem_iff]
  have key : ∀ q : G ⧸ N, (∑ i, a i * q.out • b i) * q.out • x
      = if ((1 : G) : G ⧸ N) = q then c * x else 0 := by
    intro q
    by_cases hq : q.out ∈ N
    · rw [if_pos ((hmem q).mp hq).symm, h.sum_in _ hq]
      congr 1
      exact hx ⟨_, hq⟩
    · rw [if_neg (fun h1 => hq ((hmem q).mpr h1.symm)), h.sum_out _ hq, zero_mul]
  calc ∑ i, a i * cosetTrace N (b i * x)
      = ∑ q : G ⧸ N, (∑ i, a i * q.out • b i) * q.out • x := by
        simp only [cosetTrace, smul_mul', Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = c * x := by rw [Finset.sum_congr rfl fun q _ => key q]; simp

end GlobalTheory.AlmostEt
end

section

open Finset

namespace GlobalTheory.KummerEisensteinGalois


open Finset in
theorem _root_.GlobalTheory.KummerEisensteinGalois.smF_one_mem_subring : ∀ (K : Type) [Field K] [CharZero K]
    (R : Subring K) (c M : ℕ) (ζ : K) (a b : ℤ),
    0 < M → Nat.Coprime c M → ¬ (M : ℤ) ∣ a → ζ ^ b ∈ R → ζ ^ (-b) ∈ R →
    ∀ n : ℕ, _root_.GlobalTheory.KummerEisensteinGalois.smF (c : ℤ) 1 M ζ a b n ∈ R := by
  intro K _ _ R c M ζ a b hM hcop ha hb hbneg n
  have hca : ¬ (M : ℤ) ∣ (c : ℤ) * a := by
    intro h
    apply ha
    refine Int.dvd_of_dvd_mul_right_of_gcd_one h ?_
    rw [Int.gcd_natCast_natCast]
    exact Nat.Coprime.symm hcop
  have hpow : ∀ m : ℕ, ζ ^ (b * (m : ℤ)) ∈ R ∧ ζ ^ (-(b * (m : ℤ))) ∈ R := by
    intro m
    refine ⟨?_, ?_⟩
    · rw [zpow_mul, zpow_natCast]; exact R.pow_mem hb m
    · rw [← neg_mul, zpow_mul, zpow_natCast]; exact R.pow_mem hbneg m
  have hpow' : ∀ m : ℕ, ζ ^ ((c : ℤ) * b * (m : ℤ)) ∈ R ∧ ζ ^ (-((c : ℤ) * b * (m : ℤ))) ∈ R := by
    intro m
    have h := hpow (c * m)
    rwa [show (c : ℤ) * b * (m : ℤ) = b * ((c * m : ℕ) : ℤ) by push_cast; ring]
  unfold _root_.GlobalTheory.KummerEisensteinGalois.smF _root_.GlobalTheory.KummerEisensteinGalois.eisF
  split_ifs with hn
  · unfold _root_.GlobalTheory.KummerEisensteinGalois.const0
    simp only [if_true, if_neg ha, if_neg hca]
    have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
    have key : (c : ℚ) ^ 2 * (1 / 2 - _root_.GlobalTheory.KummerEisensteinGalois.frc M a) -
        c * (1 / 2 - _root_.GlobalTheory.KummerEisensteinGalois.frc M (c * a)) =
        (((c.choose 2 : ℕ) : ℤ) - ((c : ℤ) * ((c : ℤ) * a / M) - (c : ℤ) ^ 2 * (a / M)) : ℤ) := by
      unfold _root_.GlobalTheory.KummerEisensteinGalois.frc
      rw [Int.emod_def, Int.emod_def]
      push_cast
      rw [Nat.cast_choose_two]
      field_simp
      ring
    convert intCast_mem R (((c.choose 2 : ℕ) : ℤ) - ((c : ℤ) * ((c : ℤ) * a / M) -
      (c : ℤ) ^ 2 * (a / M))) using 1
    have hK := congrArg (fun q : ℚ => (q : K)) key
    simp only [Rat.cast_intCast] at hK
    rw [← hK]
    push_cast
    norm_num
  · unfold _root_.GlobalTheory.KummerEisensteinGalois.coefPos
    refine R.sub_mem (R.mul_mem (R.pow_mem (intCast_mem R _) 2) (R.sum_mem fun d _ => ?_))
      (R.mul_mem ?_ (R.sum_mem fun d _ => ?_))
    · simp only [Nat.sub_self, pow_zero, one_mul]
      refine R.sub_mem ?_ ?_ <;> split_ifs
      · exact (hpow d).1
      · exact R.zero_mem
      · exact (hpow d).2
      · exact R.zero_mem
    · norm_num
    · simp only [Nat.sub_self, pow_zero, one_mul]
      refine R.sub_mem ?_ ?_ <;> split_ifs
      · exact (hpow' d).1
      · exact R.zero_mem
      · exact (hpow' d).2
      · exact R.zero_mem

end GlobalTheory.KummerEisensteinGalois
end

section

noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois.UpSplit

open GlobalTheory.KummerEisensteinGalois

variable {K : Type*} [Field K] [CharZero K]

theorem cmul_vp_vp (p : ℕ) (hp : 0 < p) (f g : ℕ → K) (r : ℕ) :
    cmul (vp p f) (vp p g) (p * r) = cmul f g r := by
  unfold cmul
  symm
  have h1 : ∀ j ∈ range (r + 1), f j * g (r - j) = vp p f (p * j) * vp p g (p * r - p * j) := by
    intro j _
    simp only [vp, dvd_mul_right, if_true, ← Nat.mul_sub, Nat.mul_div_cancel_left _ hp]
  rw [sum_congr rfl h1, ← sum_image (f := fun i => vp p f i * vp p g (p * r - i)) (g := fun j => p * j)
    (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp h)]
  apply sum_subset
  · intro i hi
    simp only [mem_image, mem_range] at hi ⊢
    obtain ⟨j, hj, rfl⟩ := hi
    have : j ≤ r := by omega
    have := Nat.mul_le_mul_left p this
    omega
  · intro i hi hni
    simp only [mem_image, mem_range, not_exists, not_and] at hi hni
    by_cases hpi : p ∣ i
    · obtain ⟨j, rfl⟩ := hpi
      exact absurd rfl (hni j (by
        have : p * j ≤ p * r := by omega
        have := Nat.le_of_mul_le_mul_left this hp
        omega))
    · simp [vp, hpi]

end GlobalTheory.KummerEisensteinGalois.UpSplit

namespace GlobalTheory.KummerEisensteinGalois


end GlobalTheory.KummerEisensteinGalois
end
end

section

noncomputable section

open GlobalTheory.KummerEisensteinGalois Finset
open scoped Classical

namespace GlobalTheory.KummerEisensteinGalois

theorem glFibre_val_map {p n : ℕ} [NeZero p] (x : ZMod (p ^ (n + 1))) :
    (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x).val = x.val % p ^ n := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

theorem glFibre_isUnit_iff {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) (x : ZMod (p ^ n)) :
    IsUnit x ↔ ¬ p ∣ x.val := by
  have hp : p.Prime := Fact.out
  conv_lhs => rw [← ZMod.natCast_zmod_val x]
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff (by omega), Nat.coprime_comm,
    hp.coprime_iff_not_dvd]

theorem glFibre_dvd_map_iff {p : ℕ} [Fact p.Prime] {n : ℕ} (hn : 1 ≤ n) (x : ZMod (p ^ (n + 1))) :
    p ∣ (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) x).val ↔ p ∣ x.val := by
  rw [glFibre_val_map, Nat.dvd_mod_iff (dvd_pow_self p (by omega))]

theorem sum_unitSet_succ_fibre : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (K : Type) [CommRing K] (G : GL (Fin 2) (ZMod (p ^ n)) → K) (Φ : ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → ZMod (p ^ (n + 1)) → K), 1 ≤ n → ∑ γ ∈ unitSet p (n + 1), G (Matrix.GeneralLinearGroup.map (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))) γ) * Φ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0) ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1) = ∑ γ ∈ unitSet p n, G γ * ∑ y₀₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 0)), ∑ y₀₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 0 1)), ∑ y₁₀ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 0)), ∑ y₁₁ ∈ (univ.filter (fun y : ZMod (p ^ (n + 1)) => ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) y = (γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) 1 1)), Φ y₀₀ y₀₁ y₁₀ y₁₁ := by
  intro p _ n K _ G Φ hn
  set ρ := ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n)) with hρ
  have hent : ∀ (γ : GL (Fin 2) (ZMod (p ^ (n + 1)))) (a b : Fin 2),
      (Matrix.GeneralLinearGroup.map ρ γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) a b =
        ρ ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) a b) := fun _ _ _ => rfl
  have hmaps : ∀ γ ∈ unitSet p (n + 1), Matrix.GeneralLinearGroup.map ρ γ ∈ unitSet p n := by
    intro γ hγ
    simp only [unitSet, mem_filter, mem_univ, true_and] at hγ ⊢
    rw [hent, hent, hρ, glFibre_dvd_map_iff hn, glFibre_dvd_map_iff hn]
    exact hγ
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl (fun g hg => ?_)
  rw [Finset.sum_congr rfl (fun γ hγ => by rw [(mem_filter.mp hγ).2]), ← Finset.mul_sum]
  congr 1
  simp only [← Finset.sum_product']
  refine Finset.sum_bij (fun γ _ => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 0),
      ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 0 1),
      ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 0),
      ((γ : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1)))) 1 1))) ?_ ?_ ?_ ?_
  · intro γ hγ
    obtain ⟨_, hγg⟩ := mem_filter.mp hγ
    simp only [mem_product, mem_filter, mem_univ, true_and, ← hγg, hent, and_self]
  · intro γ _ δ _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    ext a b
    fin_cases a <;> fin_cases b
    exacts [h1, h2, h3, h4]
  · rintro ⟨a, b, c, d⟩ hb
    simp only [mem_product, mem_filter, mem_univ, true_and] at hb
    obtain ⟨ha, hb', hc, hd⟩ := hb
    let B : Matrix (Fin 2) (Fin 2) (ZMod (p ^ (n + 1))) := !![a, b; c, d]
    have hBm : ρ.mapMatrix B = (g : Matrix (Fin 2) (Fin 2) (ZMod (p ^ n))) := by
      ext i j
      fin_cases i <;> fin_cases j
      exacts [ha, hb', hc, hd]
    have hdet : IsUnit B.det := by
      have h1 : IsUnit (ρ B.det) := by
        rw [RingHom.map_det, hBm]; exact (Matrix.isUnit_iff_isUnit_det _).mp g.isUnit
      rw [glFibre_isUnit_iff hn, hρ, glFibre_dvd_map_iff hn] at h1
      exact (glFibre_isUnit_iff (by omega) _).mpr h1
    obtain ⟨γ, hγ⟩ := (Matrix.isUnit_iff_isUnit_det B).mpr hdet
    have hmap : Matrix.GeneralLinearGroup.map ρ γ = g := by
      apply Units.ext
      rw [← hBm, ← hγ]; rfl
    refine ⟨γ, ?_, ?_⟩
    · refine mem_filter.mpr ⟨?_, hmap⟩
      simp only [unitSet, mem_filter, mem_univ, true_and] at hg ⊢
      rw [← glFibre_dvd_map_iff hn, ← glFibre_dvd_map_iff hn, ← hρ, ← hent, ← hent, hmap]
      exact hg
    · simp only [hγ, B]
      rfl
  · intro γ _
    rfl

end GlobalTheory.KummerEisensteinGalois
end
end

section

open GlobalTheory.K5

noncomputable section

namespace GlobalTheory.K5.GeoFix

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem exists_finset_of_mem_closure (R A : Set Ω) {x : Ω} (hx : x ∈ Subfield.closure (R ∪ A)) :
    ∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ x ∈ Subfield.closure (R ∪ (S : Set Ω)) := by
  classical
  have mono : ∀ {S S' : Finset Ω}, S ⊆ S' →
      Subfield.closure (R ∪ (S : Set Ω)) ≤ Subfield.closure (R ∪ (S' : Set Ω)) := fun h =>
    Subfield.closure_mono (Set.union_subset_union_right _ (Finset.coe_subset.2 h))
  have two : ∀ {y z : Ω}, (∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ y ∈ Subfield.closure (R ∪ (S : Set Ω))) →
      (∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ z ∈ Subfield.closure (R ∪ (S : Set Ω))) →
      ∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ y ∈ Subfield.closure (R ∪ (S : Set Ω)) ∧
        z ∈ Subfield.closure (R ∪ (S : Set Ω)) := by
    rintro y z ⟨S, hS, hy⟩ ⟨S', hS', hz⟩
    refine ⟨S ∪ S', ?_, mono Finset.subset_union_left hy, mono Finset.subset_union_right hz⟩
    rw [Finset.coe_union]; exact Set.union_subset hS hS'
  let F : Subfield Ω :=
    { carrier := {y | ∃ S : Finset Ω, (S : Set Ω) ⊆ A ∧ y ∈ Subfield.closure (R ∪ (S : Set Ω))}
      mul_mem' := fun {a b} ha hb => by
        obtain ⟨S, hS, h1, h2⟩ := two ha hb
        exact ⟨S, hS, mul_mem h1 h2⟩
      one_mem' := ⟨∅, by simp, one_mem _⟩
      add_mem' := fun {a b} ha hb => by
        obtain ⟨S, hS, h1, h2⟩ := two ha hb
        exact ⟨S, hS, add_mem h1 h2⟩
      zero_mem' := ⟨∅, by simp, zero_mem _⟩
      neg_mem' := fun {a} ⟨S, hS, h1⟩ => ⟨S, hS, neg_mem h1⟩
      inv_mem' := fun a ⟨S, hS, h1⟩ => ⟨S, hS, inv_mem h1⟩ }
  have hle : Subfield.closure (R ∪ A) ≤ F := by
    rw [Subfield.closure_le]
    rintro y (hy | hy)
    · exact ⟨∅, by simp, Subfield.subset_closure (Or.inl hy)⟩
    · refine ⟨{y}, by simpa using hy, Subfield.subset_closure (Or.inr (by simp))⟩
  exact hle hx


variable (p Ω) in
def geoField : Subfield Ω :=
  Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x : Ω | IsAlgZp (p := p) x})

theorem mem_geoField_of_fixed (h : IsClo p Ω) (x : Ω) (hx : ∀ g ∈ Ggeo (p := p) Ω, g x = x) :
    x ∈ geoField p Ω := by
  haveI := h.clo
  haveI : CharZero Ω := Basic.charZero_of_isClo h
  have hR : ∀ a : O0 p, algebraMap (O0 p) Ω a ∈ geoField p Ω := fun a =>
    Subfield.subset_closure (Or.inl ⟨a, rfl⟩)
  let f : O0 p →+* geoField p Ω := (algebraMap (O0 p) Ω).codRestrict (geoField p Ω) hR
  have hf : (algebraMap (geoField p Ω) Ω).comp f = algebraMap (O0 p) Ω := by ext; rfl
  have hfi : Function.Injective f := fun a b hab => h.inj (congrArg Subtype.val hab)
  have hAlg : Algebra.IsAlgebraic (geoField p Ω) Ω := ⟨fun a => by
    obtain ⟨P, hP0, hP⟩ := h.alg.isAlgebraic a
    refine ⟨P.map f, (Polynomial.map_ne_zero_iff hfi).2 hP0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map, hf, ← Polynomial.aeval_def, hP]⟩
  letI : Algebra.IsAlgebraic (geoField p Ω) Ω := hAlg
  haveI : IsAlgClosure (geoField p Ω) Ω := ⟨h.clo, hAlg⟩
  haveI : CharZero (geoField p Ω) := ⟨fun m n e =>
    CharZero.cast_injective (congrArg Subtype.val e)⟩
  haveI : IsGalois (geoField p Ω) Ω := inferInstance
  have hbot : x ∈ (⊥ : IntermediateField (geoField p Ω) Ω) := by
    refine (InfiniteGalois.mem_bot_iff_fixed x).2 fun σ => ?_
    let τ : Ω ≃ₐ[O0 p] Ω := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv)
      (fun a => σ.commutes ⟨_, hR a⟩)
    have hτ : τ ∈ Ggeo (p := p) Ω := fun y hy => σ.commutes ⟨y, Subfield.subset_closure (Or.inr hy)⟩
    exact hx τ hτ
  obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hbot
  exact y.2

theorem fixed_mem_closure : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ x : Ω, (∀ g ∈ Ggeo (p := p) Ω, g x = x) → ∃ S : Finset Ω, (∀ s ∈ S, IsAlgZp (p := p) s) ∧
      x ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ (S : Set Ω)) := by
  intro p _ Ω _ _ h x hx
  obtain ⟨S, hS, hxS⟩ := exists_finset_of_mem_closure _ _ (mem_geoField_of_fixed h x hx)
  exact ⟨S, fun s hs => hS hs, hxS⟩

end GlobalTheory.K5.GeoFix
end
end
