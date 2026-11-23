module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem rest_bound (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (k : ℕ) (Q : RP Ψ N) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (p : ℕ) (fr : ℕ → Ψ ⊕ Ψ), 2 ≤ p →
      |restTerm j p fr k Q| ≤ c * Real.log p / (p : ℝ) ^ 2 := by
  set M : ℝ := ∑ σ : Ψ ⊕ Ψ, |degFl (pLie j (k - 1) σ * Q)| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hMle : ∀ σ, |degFl (pLie j (k - 1) σ * Q)| ≤ M := fun σ =>
    Finset.single_le_sum (f := fun σ => |degFl (pLie j (k - 1) σ * Q)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ σ)
  refine ⟨2 * k * M, by positivity, fun p fr hp => ?_⟩
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  unfold restTerm
  split_ifs with hk
  · set r : ℝ := ((p : ℝ) ^ k)⁻¹ with hr
    have hr0 : 0 ≤ r := by positivity
    have hpk : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ k := pow_le_pow_right₀ (by linarith) hk
    have hp4 : (4 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have hr1 : r ≤ ((p : ℝ) ^ 2)⁻¹ := inv_anti₀ (by positivity) hpk
    have hr2 : r ≤ 1 / 2 := by
      refine hr1.trans ?_
      rw [one_div]
      exact inv_anti₀ (by norm_num) (by linarith)
    have hs : HasSum (fun n : ℕ => (r * M) * (1 / 2 : ℝ) ^ n) ((r * M) * 2) :=
      hasSum_geometric_two.mul_left _
    have hb : ‖∑' n : ℕ, r ^ (n + 1) * degFl (pLie j (k - 1) (fr n) * Q)‖ ≤ (r * M) * 2 := by
      refine tsum_of_norm_bounded hs fun n => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : 0 ≤ r ^ (n + 1)), pow_succ]
      have h1 : r ^ n ≤ (1 / 2 : ℝ) ^ n := pow_le_pow_left₀ hr0 hr2 n
      calc r ^ n * r * |degFl (pLie j (k - 1) (fr n) * Q)| ≤ (1 / 2 : ℝ) ^ n * r * M := by
            gcongr
            exact hMle _
        _ = _ := by ring
    rw [Real.norm_eq_abs] at hb
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.log p * (k : ℝ))]
    calc Real.log p * (k : ℝ) * |∑' n : ℕ, r ^ (n + 1) * degFl (pLie j (k - 1) (fr n) * Q)|
        ≤ Real.log p * (k : ℝ) * ((((p : ℝ) ^ 2)⁻¹ * M) * 2) := by
          gcongr
          refine hb.trans ?_
          gcongr
      _ = _ := by ring
  · rw [abs_zero]
    positivity

theorem summable_log_div_sq : Summable fun p : ℕ => Real.log p / (p : ℝ) ^ 2 := by
  have h : Summable fun p : ℕ => 2 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
    (Real.summable_nat_rpow_inv.2 (by norm_num)).mul_left 2
  refine Summable.of_nonneg_of_le (fun p => div_nonneg (Real.log_natCast_nonneg p) (by positivity))
    (fun p => ?_) h
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have h1 := Real.log_le_rpow_div hp'.le (by norm_num : (0 : ℝ) < 1 / 2)
  have h2 : (p : ℝ) ^ 2 = (p : ℝ) ^ (1 / 2 : ℝ) * (p : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add hp']
    norm_num
  have h3 : 0 < (p : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have h4 : 0 < (p : ℝ) ^ (3 / 2 : ℝ) := by positivity
  rw [h2, div_le_iff₀ (by positivity)]
  refine h1.trans (le_of_eq ?_)
  field_simp

theorem rest_term_bound_convergent : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (bad : Finset ℕ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (τ : Ψ) (k : ℕ) (Q : RP Ψ N), (∃ c : ℝ, ∀ p : ℕ, 2 ≤ p → |restTerm j p (frob p τ) k Q| ≤ c * Real.log p / (p : ℝ) ^ 2) ∧ ∀ B₀ : ℕ, Tendsto (fun B : ℕ => ∑ p ∈ (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ bad), restTerm j p (frob p τ) k Q) atTop (𝓝 (restSum j bad frob B₀ τ k Q)) := by
  intro Ψ _ _ N j bad frob τ k Q
  obtain ⟨c, hc0, hc⟩ := rest_bound Ψ N j k Q
  refine ⟨⟨c, fun p hp => hc p _ hp⟩, fun B₀ => ?_⟩
  have hs : Summable fun p : ℕ =>
      if p.Prime ∧ B₀ < p ∧ p ∉ bad then restTerm j p (frob p τ) k Q else 0 := by
    refine Summable.of_norm_bounded (summable_log_div_sq.mul_left c) fun p => ?_
    split_ifs with h
    · rw [Real.norm_eq_abs, ← mul_div_assoc]
      exact hc p _ h.1.two_le
    · rw [norm_zero]
      exact mul_nonneg hc0 (div_nonneg (Real.log_natCast_nonneg p) (by positivity))
  have ht := hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  refine ht.congr fun B => ?_
  simp only [Function.comp_apply]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h3, by omega⟩, h2, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨by omega, h3, h1, h4⟩

end RootFieldNumerics
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

private theorem degFl_sum' {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {ι : Type} (s : Finset ι)
    (f : ι → RP Ψ N) : degFl (∑ i ∈ s, f i) = ∑ i ∈ s, degFl (f i) := by
  unfold degFl
  simp only [MvPolynomial.coeff_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
private theorem Sh_sum {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {ι : Type} (j : ℕ) (τ : Ψ)
    (s : Finset ι) (f : ι → RP Ψ N) : Sh j τ (∑ i ∈ s, f i) = ∑ i ∈ s, Sh j τ (f i) := by

  simp only [Sh, map_sum]
  rw [Finset.sum_comm, degFl_sum']
private theorem Tot_sum {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} {ι : Type} (τ : Ψ)
    (s : Finset ι) (f : ι → RP Ψ N) : Tot τ (∑ i ∈ s, f i) = ∑ i ∈ s, Tot τ (f i) := by

  simp only [Tot, map_sum]
  rw [Finset.sum_comm, degFl_sum']
private theorem PPt_sum {Ψ : Type} [Fintype Ψ] {N : ℕ} {ι : Type} (T : RootTower Ψ N)
    (II : IntersectionSystem) (B : ℕ) (s : Finset ι) (f : ι → RP Ψ N) :
    T.PPt II B (∑ i ∈ s, f i) = ∑ i ∈ s, T.PPt II B (f i) := by

  simp only [RootTower.PPt, RootTower.PPc, toA, map_sum]
  rw [Finset.sum_comm]

theorem tower_point_count_identity : ∀ II : IntersectionSystem, ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (hh : RP Ψ N →ₗ[ℝ] ℝ) (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) (B₀ : ℕ) (A₀ b₀ : ℝ) (F : RP Ψ N) (Q : Ψ → ℕ → RP Ψ N), T.IdentAt II hh frob B₀ A₀ b₀ → IsDecomp F Q → T.PPt II B₀ F = T.volT * (hh F - A₀ * ∑ σ, Sh T.j σ F - b₀ * ∑ σ, Tot σ F + ∑ τ, ∑ k ∈ Finset.Icc 1 N, restSum T.j T.bad frob B₀ τ k (Q τ k)) := by
  intro II Ψ _ _ N T hh frob B₀ A₀ b₀ F Q hI hD
  obtain ⟨hQ, rfl⟩ := hD
  have key : ∀ τ, ∀ k ∈ Finset.Icc 1 N, T.PPt II B₀ (pk τ k * Q τ k) = T.volT * (hh (pk τ k * Q τ k)
      - A₀ * ∑ σ, Sh T.j σ (pk τ k * Q τ k) - b₀ * ∑ σ, Tot σ (pk τ k * Q τ k)
      + restSum T.j T.bad frob B₀ τ k (Q τ k)) := by
    intro τ k hk
    have hk' := Finset.mem_Icc.1 hk
    exact hI τ k hk'.1 hk'.2 _ (hQ τ k hk'.1 hk'.2)

  simp_rw [PPt_sum, map_sum, Sh_sum, Tot_sum]
  rw [Finset.sum_congr rfl (fun τ _ => Finset.sum_congr rfl (key τ))]
  have e1 : ∑ σ, ∑ τ, ∑ k ∈ Finset.Icc 1 N, Sh T.j σ (pk τ k * Q τ k)
      = ∑ τ, ∑ k ∈ Finset.Icc 1 N, ∑ σ, Sh T.j σ (pk τ k * Q τ k) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have e2 : ∑ σ, ∑ τ, ∑ k ∈ Finset.Icc 1 N, Tot σ (pk τ k * Q τ k)
      = ∑ τ, ∑ k ∈ Finset.Icc 1 N, ∑ σ, Tot σ (pk τ k * Q τ k) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  rw [e1, e2]
  simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_add, mul_sub]

end RootFieldNumerics
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem dominant_of_gaps {Ψ : Type} {N : ℕ} (mu : Wt Ψ N)
    (h : ∀ τ (i : ℕ), i + 1 < N → 0 ≤ ent mu τ i - ent mu τ (i + 1)) : Dominant mu := by
  intro τ a b hab
  have hab' : (a : ℕ) ≤ b := hab
  have key : ∀ k : ℕ, (a : ℕ) + k < N → ent mu τ ((a : ℕ) + k) ≤ ent mu τ a := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := h τ ((a : ℕ) + k) (by omega)
      have h2 := ih (by omega)
      show ent mu τ ((a : ℕ) + k + 1) ≤ ent mu τ a
      linarith
  have h3 := key ((b : ℕ) - a) (by omega)
  rw [Nat.add_sub_cancel' hab'] at h3
  simpa [ent, a.isLt, b.isLt] using h3

theorem abs_ent_le {Ψ : Type} [Fintype Ψ] {N : ℕ} (mu : Wt Ψ N) (τ : Ψ) (i : ℕ) : |ent mu τ i| ≤ ‖mu‖ := by
  unfold ent
  split_ifs with h
  · exact (norm_le_pi_norm (mu τ) _).trans (norm_le_pi_norm mu τ)
  · simp

theorem perturbed_weight_wall_bounds : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (c₀ θ₀ : ℝ), 0 < c₀ → 0 < θ₀ → ∃ B₁ : ℕ, ∀ B : ℕ, B₁ ≤ B → ∀ (τ₀ : Ψ) (lam₀ : Wt Ψ N), InWall T.j τ₀ c₀ lam₀ → let θ : ℝ := 5 * Fintype.card Ψ / B; let lam : Wt Ψ N := fun τ i => lam₀ τ i + (if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0); 3 ≤ B ∧ 0 < θ ∧ θ ≤ θ₀ ∧ θ ≤ 1 ∧ ‖lam‖ ≤ 1 ∧ ‖T.lamS lam (θ ^ 2)‖ ≤ 1 ∧ (∀ τ, θ ≤ gap T.j lam τ) ∧ gap T.j lam τ₀ = 2 * θ ∧ CompactGapsGE T.j c₀ lam ∧ Dominant lam ∧ Dominant (T.lamS lam (θ ^ 2)) ∧ NefThreshold T.j B (T.lamS lam (θ ^ 2)) ∧ ‖T.lamS lam (θ ^ 2) - lam₀‖ ≤ 2 * θ + ‖T.nu‖ * θ ^ 2 := by
  intro Ψ _ _ N T c₀ θ₀ hc₀ hθ₀
  set R := ‖T.nu‖ with hR
  have hR0 : 0 ≤ R := norm_nonneg _
  set δ : ℝ := min (min θ₀ (1 / 8)) (min (c₀ / 2) (1 / (4 * (R + 1)))) with hδ
  have hδpos : 0 < δ :=
    lt_min (lt_min hθ₀ (by norm_num)) (lt_min (by linarith) (by positivity))
  refine ⟨max 10 ⌈5 * (Fintype.card Ψ : ℝ) / δ⌉₊, ?_⟩
  intro B hB τ₀ lam₀ hW
  intro θ lam
  obtain ⟨hn0, hg0, hgo, hcg⟩ := hW
  have hcard : (1 : ℝ) ≤ Fintype.card Ψ := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨τ₀⟩
  have hB10 : (10 : ℝ) ≤ B := by exact_mod_cast (le_max_left _ _).trans hB
  have hBpos : (0 : ℝ) < B := by linarith
  have hBc : 5 * (Fintype.card Ψ : ℝ) / δ ≤ B :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hB)
  have hθdef : θ = 5 * (Fintype.card Ψ : ℝ) / B := rfl
  have hθpos : 0 < θ := by rw [hθdef]; exact div_pos (by linarith) hBpos
  have hθδ : θ ≤ δ := by
    rw [hθdef, div_le_iff₀ hBpos]
    have := (div_le_iff₀ hδpos).mp hBc
    linarith [mul_comm (B : ℝ) δ]
  have hθθ₀ : θ ≤ θ₀ := hθδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hθ8 : θ ≤ 1 / 8 := hθδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hθc : θ ≤ c₀ / 2 := hθδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθR' : θ ≤ 1 / (4 * (R + 1)) := hθδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hθR : θ * R ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hθR'
    nlinarith
  have hθB : θ * B = 5 * (Fintype.card Ψ : ℝ) := by
    rw [hθdef]; field_simp
  let D : Wt Ψ N := fun τ i => if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0
  have hD : ‖D‖ ≤ 2 * θ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun τ => ?_)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => ?_)
    simp only [D]
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    · simp; positivity
  have hlamD : lam = lam₀ + D := by funext τ i; rfl
  have hnlam : ‖lam‖ ≤ 1 / 2 + 2 * θ := by
    rw [hlamD]; exact (norm_add_le _ _).trans (by linarith)
  have hnmu : ‖T.lamS lam (θ ^ 2)‖ ≤ 1 / 2 + 2 * θ + θ ^ 2 * R := by
    show ‖lam - θ ^ 2 • T.nu‖ ≤ _
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have hθ2R : θ ^ 2 * R ≤ θ / 4 := by
    have : θ ^ 2 * R = θ * (θ * R) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hθR hθpos.le
    linarith
  have hnmu1 : ‖T.lamS lam (θ ^ 2)‖ ≤ 1 := by linarith
  have hent : ∀ τ i, ent lam τ i = ent lam₀ τ i + (if τ = τ₀ ∧ i < T.j then 2 * θ else 0) := by
    intro τ i
    by_cases hi : i < N
    · simp [ent, hi, lam]
    · have : ¬ (i < T.j) := by have := T.j_lt; omega
      simp [ent, hi, this]
  have hentS : ∀ (mu : Wt Ψ N) (s : ℝ) τ i,
      ent (T.lamS mu s) τ i = ent mu τ i - s * ent T.nu τ i := by
    intro mu s τ i
    by_cases hi : i < N <;> simp [ent, hi, RootTower.lamS]
  have hnuD : ∀ τ i, ent T.nu τ i - ent T.nu τ (i + 1) ≤ 2 * R := by
    intro τ i
    have h1 := abs_ent_le T.nu τ i
    have h2 := abs_ent_le T.nu τ (i + 1)
    have h3 := le_abs_self (ent T.nu τ i)
    have h4 := neg_abs_le (ent T.nu τ (i + 1))
    linarith
  have hgapLam : ∀ τ i, i + 1 < N → 2 * θ ≤ ent lam τ i - ent lam τ (i + 1) := by
    intro τ i hi
    rw [hent, hent]
    rcases lt_trichotomy (i + 1) T.j with hlt | heq | hgt
    · have hc := hcg τ i hi hlt.ne
      have h1 : i < T.j := by omega
      by_cases hτ : τ = τ₀
      · subst hτ
        simp [h1, hlt]
        linarith
      · simp [hτ]
        linarith
    · have h1 : i < T.j := by omega
      have h2 : ¬ i + 1 < T.j := by omega
      have hg : gap T.j lam₀ τ = ent lam₀ τ i - ent lam₀ τ (i + 1) := by
        simp only [gap]; rw [← heq]; simp
      by_cases hτ : τ = τ₀
      · subst hτ
        simp [h1, h2]
        linarith [hg0, hg]
      · have := hgo τ hτ
        simp [hτ]
        linarith
    · have hc := hcg τ i hi hgt.ne'
      have h1 : ¬ i < T.j := by omega
      have h2 : ¬ i + 1 < T.j := by omega
      simp [h1, h2]
      linarith
  have hj1 : T.j - 1 + 1 = T.j := by have := T.j_pos; omega
  have hj2 : T.j - 1 + 1 < N := by have := T.j_pos; have := T.j_lt; omega
  have hgapj : ∀ τ, 2 * θ ≤ gap T.j lam τ := by
    intro τ
    have h := hgapLam τ (T.j - 1) hj2
    rw [hj1] at h
    exact h
  have hgapmu : ∀ τ, θ ≤ gap T.j (T.lamS lam (θ ^ 2)) τ := by
    intro τ
    have h := hgapj τ
    have hn := hnuD τ (T.j - 1)
    rw [hj1] at hn
    simp only [gap] at h ⊢
    rw [hentS, hentS]
    have : θ ^ 2 * (ent T.nu τ (T.j - 1) - ent T.nu τ T.j) ≤ θ ^ 2 * (2 * R) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    linarith
  refine ⟨?_, hθpos, hθθ₀, by linarith, by linarith, hnmu1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := (le_max_left 10 _).trans hB
    omega
  · intro τ; have := hgapj τ; linarith
  · have h1 : T.j - 1 < T.j := by have := T.j_pos; omega
    simp only [gap]
    rw [hent, hent]
    have := hg0
    simp only [gap] at this
    simp [h1]
    linarith
  · intro τ i hi hij
    rw [hent, hent]
    have hc := hcg τ i hi hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have h1 : i < T.j := by omega
      by_cases hτ : τ = τ₀
      · subst hτ
        simp [h1, hlt]
        linarith
      · simp [hτ]
        linarith
    · have h1 : ¬ i < T.j := by omega
      have h2 : ¬ i + 1 < T.j := by omega
      simp [h1, h2]
      linarith
  · exact dominant_of_gaps lam (fun τ i hi => by have := hgapLam τ i hi; linarith)
  · refine dominant_of_gaps _ (fun τ i hi => ?_)
    rw [hentS, hentS]
    have h := hgapLam τ i hi
    have hn := hnuD τ i
    have : θ ^ 2 * (ent T.nu τ i - ent T.nu τ (i + 1)) ≤ θ ^ 2 * (2 * R) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    linarith
  · intro τ
    have hg := hgapmu τ
    have hB2 : (0 : ℝ) ≤ (B : ℝ) - 2 := by linarith
    have h1 : ((B : ℝ) - 2) * θ ≤ ((B : ℝ) - 2) * gap T.j (T.lamS lam (θ ^ 2)) τ :=
      mul_le_mul_of_nonneg_left hg hB2
    have he : ((B : ℝ) - 2) * θ = θ * B - 2 * θ := by ring
    have h3 : 4 * (Fintype.card Ψ : ℝ) * ‖T.lamS lam (θ ^ 2)‖ ≤ 4 * (Fintype.card Ψ : ℝ) :=
      mul_le_of_le_one_right (by positivity) hnmu1
    linarith
  · have hsub : T.lamS lam (θ ^ 2) - lam₀ = D - θ ^ 2 • T.nu := by
      funext τ i
      simp [RootTower.lamS, lam, D]
      ring
    rw [hsub]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith

end RootFieldNumerics
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem exists_rat_near_le (δ : ℝ) (hδ : 0 < δ) (x : ℝ) : ∃ q : ℚ, |(q : ℝ)| ≤ |x| ∧ |(q : ℝ) - x| ≤ δ := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show x < min (x + δ) 0 from lt_min (by linarith) hx)
    have m1 := min_le_left (x + δ) 0
    have m2 := min_le_right (x + δ) 0
    refine ⟨q, ?_, ?_⟩
    · rw [abs_of_neg hx, abs_of_nonpos (by linarith)]
      linarith
    · rw [abs_le]
      constructor <;> linarith
  · exact ⟨0, by simp [hx], by simp [hx, hδ.le]⟩
  · obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show max (x - δ) 0 < x from max_lt (by linarith) hx)
    have m1 := le_max_left (x - δ) 0
    have m2 := le_max_right (x - δ) 0
    refine ⟨q, ?_, ?_⟩
    · rw [abs_of_pos hx, abs_of_nonneg (by linarith)]
      linarith
    · rw [abs_le]
      constructor <;> linarith

theorem continuous_bound_wall_extension : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (j : ℕ) (c₀ b : ℝ) (τ₀ : Ψ) (Φ : Wt Ψ N → ℝ), 1 ≤ j → j < N → 0 < c₀ → Continuous Φ → (∀ lam, IsRatWt lam → InWall j τ₀ (c₀ / 2) lam → |Φ lam| ≤ b) → ∀ lam, InWall j τ₀ c₀ lam → |Φ lam| ≤ b := by
  intro Ψ _ _ N j c₀ b τ₀ Φ hj hjN hc hΦ hrat lam hlam
  have hex : ∀ n : ℕ, ∀ x : ℝ, ∃ q : ℚ, |(q:ℝ)| ≤ |x| ∧ |(q:ℝ) - x| ≤ c₀ / 4 * (1 / ((n:ℝ) + 1)) :=
    fun n x => exists_rat_near_le _ (by positivity) x
  choose F hF1 hF2 using hex
  let A : ℕ → Wt Ψ N := fun n τ i => (F n (lam τ i) : ℝ)
  have hδ : ∀ n : ℕ, c₀ / 4 * (1 / ((n:ℝ) + 1)) ≤ c₀ / 4 := by
    intro n
    have h1 : 1 / ((n:ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
    exact mul_le_of_le_one_right (by positivity) h1
  have hent : ∀ n τ k, k < N → ent (A n) τ k = (F n (ent lam τ k) : ℝ) := by
    intro n τ k hk
    simp [ent, hk, A]
  have hclose : ∀ n τ k, k < N → |ent (A n) τ k - ent lam τ k| ≤ c₀ / 4 := by
    intro n τ k hk
    rw [hent n τ k hk]
    exact (hF2 n _).trans (hδ n)
  have hin : ∀ n, InWall j τ₀ (c₀ / 2) (A n) := by
    intro n
    obtain ⟨hn, hg0, hgτ, hcg⟩ := hlam
    have hj1 : j - 1 < N := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun τ =>
        (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
      have h1 : ‖lam τ i‖ ≤ 1 / 2 := (norm_le_pi_norm (lam τ) i).trans ((norm_le_pi_norm lam τ).trans hn)
      simp only [Real.norm_eq_abs, A] at h1 ⊢
      exact (hF1 n _).trans h1
    · simp only [gap] at hg0 ⊢
      rw [hent n τ₀ _ hj1, hent n τ₀ _ hjN, show ent lam τ₀ (j - 1) = ent lam τ₀ j by linarith]
      ring
    · intro τ hτ
      have h := hgτ τ hτ
      simp only [gap] at h ⊢
      have a1 := abs_le.1 (hclose n τ _ hj1)
      have a2 := abs_le.1 (hclose n τ _ hjN)
      linarith [a1.1, a1.2, a2.1, a2.2]
    · intro τ i hi hij
      have h := hcg τ i hi hij
      have a1 := abs_le.1 (hclose n τ i (by omega))
      have a2 := abs_le.1 (hclose n τ (i + 1) hi)
      linarith [a1.1, a1.2, a2.1, a2.2]
  have hAr : ∀ n, IsRatWt (A n) := fun n τ i => ⟨F n (lam τ i), rfl⟩
  have htend : Tendsto A atTop (𝓝 lam) := by
    rw [tendsto_pi_nhds]
    intro τ
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Tendsto (fun n : ℕ => c₀ / 4 * (1 / ((n:ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (c₀ / 4)
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    simp only [A, Real.norm_eq_abs]
    exact hF2 n _
  have hΦt : Tendsto (fun n => |Φ (A n)|) atTop (𝓝 |Φ lam|) :=
    (continuous_abs.tendsto _).comp ((hΦ.tendsto lam).comp htend)
  exact le_of_tendsto' hΦt fun n => hrat _ (hAr n) (hin n)

end RootFieldNumerics
end
