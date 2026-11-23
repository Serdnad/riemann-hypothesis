module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Formalism.CharacterColumnKernels.Bundle001
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
public import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

section

open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory.BK

theorem exists_mul_frob_E_eq_one_of_lt (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
    [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (k : ℝ)
    (hk : 1 / ((e : ℝ) * l) < k) :
    ∃ g ∈ R O K l k, g * frob K l (E K l e) = 1 := by
  have hl := (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have : NeZero (e * l) := ⟨(Nat.mul_pos (NeZero.pos e) hl).ne'⟩
  have hl0 := l_ne_zero (K := K) l
  have hel : (0 : ℝ) < (e : ℝ) * l := by
    have := NeZero.pos e
    positivity
  have hk0 : 0 < k := lt_trans (by positivity) hk
  let c : K⟦X⟧ := expand (e * l) (NeZero.ne _) (rescale (-(l : K)⁻¹) (PowerSeries.mk 1))
  set r : ℝ := (l : ℝ) * rad l k ^ (e * l) with hr
  have hr0 : 0 ≤ r := mul_nonneg (by positivity) (pow_nonneg (rad_nonneg l k) _)
  have hr1 : r < 1 := by
    have h1 : rad l k ^ (e * l) = (l : ℝ) ^ (-(k * ((e : ℝ) * l))) := by
      rw [rad, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg l)]
      push_cast
      ring_nf
    have h2 : (l : ℝ) ^ (-(k * ((e : ℝ) * l))) < (l : ℝ) ^ (-1 : ℝ) := by
      apply Real.rpow_lt_rpow_of_exponent_lt hl1
      have : 1 < k * ((e : ℝ) * l) := by
        rw [div_lt_iff₀ hel] at hk
        linarith
      linarith
    rw [Real.rpow_neg_one] at h2
    rw [hr, h1]
    calc (l : ℝ) * (l : ℝ) ^ (-(k * ((e : ℝ) * l))) < (l : ℝ) * (l : ℝ)⁻¹ :=
          mul_lt_mul_of_pos_left h2 (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  have hc (n : ℕ) : ‖coeff n c‖ * rad l k ^ n ≤ r ^ (n / (e * l)) := by
    simp only [c]
    rw [coeff_expand]
    split_ifs with h
    · obtain ⟨j, rfl⟩ := h
      rw [Nat.mul_div_cancel_left _ (NeZero.pos (e * l)), coeff_rescale, coeff_mk, Pi.one_apply,
        mul_one, norm_pow, norm_neg, norm_inv, norm_l, inv_inv, hr, mul_pow, pow_mul]
    · simpa using pow_nonneg hr0 _
  have hcR : c ∈ R O K l k := mem_R.2 <| squeeze_zero
    (fun n => mul_nonneg (norm_nonneg _) (pow_nonneg (rad_nonneg l k) n)) hc
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp
      (Nat.tendsto_div_const_atTop (NeZero.ne _)))
  refine ⟨C (l : K)⁻¹ * c, mul_mem (HasK.C_mem _) hcR, ?_⟩
  have h := congrArg (fun f => expand (e * l) (NeZero.ne _) (rescale (-(l : K)⁻¹) f))
    (mk_one_mul_one_sub_eq_one K)
  simp only [map_mul, map_sub, map_one, rescale_X, expand_X, expand_C, map_neg] at h
  have h2 : (C (l : K)⁻¹ : K⟦X⟧) * l = 1 := by
    rw [← map_natCast (C : K →+* K⟦X⟧), ← map_mul, inv_mul_cancel₀ hl0, map_one]
  rw [E, map_add (f := _), map_pow, frob_X, map_natCast, ← pow_mul, mul_comm l e]
  change c * _ = 1 at h
  linear_combination h + c * h2
end GlobalTheory.BK

namespace GlobalTheory.BK

theorem frob_mem_R_of_mem_invE_A : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (k : ℝ), 1 / ((e : ℝ) * l) < k → ∀ f ∈ invE l e (A O K), frob K l f ∈ R O K l k := by
  intro O K _ _ _ _ _ l e _ _ _ k hk f hf
  have hk0 : 0 < k := lt_trans (by
    have := NeZero.pos e
    have := (Fact.out : l.Prime).pos
    positivity) hk
  obtain ⟨g, hg, hgE⟩ := exists_mul_frob_E_eq_one_of_lt O K l e k hk
  obtain ⟨n, hn⟩ := mem_away.1 hf
  rw [coe_EIn] at hn
  have h1 : frob K l (E K l e ^ n * f) ∈ R O K l k := A_le_R l hk0 (frob_mem_A l hn)
  have h2 : frob K l f = g ^ n * frob K l (E K l e ^ n * f) := by
    rw [map_mul, map_pow, ← mul_assoc, ← mul_pow, hgE, one_pow, one_mul]
  rw [h2]
  exact mul_mem (pow_mem hg n) h1

end GlobalTheory.BK
end

section

open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory.BK.FrobDecay

variable {K : Type} [NormedField K] [IsUltrametricDist K]

def CoeffBd (ρ b : ℝ) (f : K⟦X⟧) : Prop := ∀ m, ‖coeff m f‖ * ρ ^ m ≤ b

theorem bd_mul {ρ a b : ℝ} {f g : K⟦X⟧} (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : CoeffBd ρ a f) (hg : CoeffBd ρ b g) : CoeffBd ρ (a * b) (f * g) := fun m =>
  norm_coeff_mul_le (w := fun m => ρ ^ m) (fun n => pow_nonneg hρ n)
    (fun i j => (pow_add ρ i j).le) ha hb hf hg m

theorem bd_add {ρ b : ℝ} {f g : K⟦X⟧} (hρ : 0 ≤ ρ) (hf : CoeffBd ρ b f) (hg : CoeffBd ρ b g) :
    CoeffBd ρ b (f + g) := fun m =>
  (norm_coeff_add_le (w := fun m => ρ ^ m) (fun n => pow_nonneg hρ n) f g m).trans
    (max_le (hf m) (hg m))

theorem bd_zero {ρ b : ℝ} (hb : 0 ≤ b) : CoeffBd ρ b (0 : K⟦X⟧) := fun m => by simp [hb]

theorem bd_sum {α : Type} (s : Finset α) (f : α → K⟦X⟧) {ρ b : ℝ} (hρ : 0 ≤ ρ) (hb : 0 ≤ b)
    (h : ∀ i ∈ s, CoeffBd ρ b (f i)) : CoeffBd ρ b (∑ i ∈ s, f i) :=
  Finset.sum_induction f (CoeffBd ρ b) (fun _ _ => bd_add hρ) (bd_zero hb) h

theorem bd_C {ρ : ℝ} (x : K) : CoeffBd ρ ‖x‖ (C x) := fun m => by
  rw [coeff_C]
  split_ifs with h
  · subst h; simp
  · simp

theorem bd_le {ρ b b' : ℝ} {f : K⟦X⟧} (hbb : b ≤ b') (hf : CoeffBd ρ b f) : CoeffBd ρ b' f :=
  fun m => (hf m).trans hbb

theorem bd_mono {ρ ρ' b : ℝ} {f : K⟦X⟧} (hρ : 0 ≤ ρ') (h : ρ' ≤ ρ) (hf : CoeffBd ρ b f) :
    CoeffBd ρ' b f := fun m =>
  (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ h m) (norm_nonneg _)).trans (hf m)

theorem bd_frob (l : ℕ) [Fact l.Prime] {ρ b : ℝ} {f : K⟦X⟧} (hb : 0 ≤ b)
    (hf : CoeffBd (ρ ^ l) b f) : CoeffBd ρ b (frob K l f) := fun m => by
  rw [coeff_frob]
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    rw [Nat.mul_div_cancel_left _ (Fact.out : l.Prime).pos, pow_mul]
    exact hf q
  · simpa using hb

theorem bd_of_coeff_zero {r ρ N : ℝ} {f : K⟦X⟧} (hr : 0 < r) (hρ : 0 ≤ ρ) (hρr : ρ ≤ r)
    (hf : CoeffBd r N f) (h0 : coeff 0 f = 0) : CoeffBd ρ (N / r * ρ) f := fun m => by
  have hN : 0 ≤ N := (mul_nonneg (norm_nonneg _) (pow_nonneg hr.le 0)).trans (hf 0)
  cases m with
  | zero => simpa [h0] using mul_nonneg (div_nonneg hN hr.le) hρ
  | succ m =>
    have key : ρ ^ (m + 1) * r ≤ r ^ (m + 1) * ρ := by
      have h1 := pow_le_pow_left₀ hρ hρr m
      calc ρ ^ (m + 1) * r = ρ ^ m * (ρ * r) := by ring
        _ ≤ r ^ m * (ρ * r) := mul_le_mul_of_nonneg_right h1 (mul_nonneg hρ hr.le)
        _ = r ^ (m + 1) * ρ := by ring
    rw [div_mul_eq_mul_div, le_div_iff₀ hr]
    calc ‖coeff (m + 1) f‖ * ρ ^ (m + 1) * r = ‖coeff (m + 1) f‖ * (ρ ^ (m + 1) * r) := by ring
      _ ≤ ‖coeff (m + 1) f‖ * (r ^ (m + 1) * ρ) := mul_le_mul_of_nonneg_left key (norm_nonneg _)
      _ = (‖coeff (m + 1) f‖ * r ^ (m + 1)) * ρ := by ring
      _ ≤ N * ρ := mul_le_mul_of_nonneg_right (hf _) hρ

end GlobalTheory.BK.FrobDecay

open GlobalTheory.BK.FrobDecay

theorem GlobalTheory.BK.frob_recursion_decay : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l a : ℕ) [Fact l.Prime] [NeZero a] (ι : Type) [Fintype ι] [DecidableEq ι] (k : ℝ), 0 < k → ∀ (B : ZMod a → Matrix ι ι K⟦X⟧) (c : ZMod a → Matrix ι ι K) (Z : ℕ → ZMod a → Matrix ι ι K⟦X⟧), (∀ τ i j, B τ i j ∈ R O K l k) → (∀ τ, Z 0 τ = (c τ).map C) → (∀ n τ, Z (n + 1) τ = B τ * (Z n (τ - 1)).map (frob K l) * (c τ).map C) → (∀ τ i j, (X : K⟦X⟧) ∣ Z 1 τ i j - Z 0 τ i j) → ∃ M β : ℝ, 0 ≤ β ∧ ∀ n τ i j, Z n τ i j ∈ R O K l k ∧ normR l k (Z (n + 1) τ i j - Z n τ i j) ≤ M * β ^ n * rad l k ^ (l ^ n) := by
  intro O K _ _ _ _ _ l a _ _ ι _ _ k hk B c Z hB h0 hrec hX
  have hr : 0 < rad l k := rad_pos l k
  have hr1 : rad l k ≤ 1 := rad_le_one l hk.le
  have hmem : ∀ n τ i j, Z n τ i j ∈ R O K l k := by
    intro n
    induction n with
    | zero =>
      intro τ i j
      rw [h0, Matrix.map_apply]
      exact HasK.C_mem _
    | succ n ih =>
      intro τ i j
      rw [hrec, Matrix.mul_apply]
      refine Subalgebra.sum_mem _ fun q _ => mul_mem ?_ (by rw [Matrix.map_apply]; exact HasK.C_mem _)
      rw [Matrix.mul_apply]
      exact Subalgebra.sum_mem _ fun p _ => mul_mem (hB _ _ _)
        (by rw [Matrix.map_apply]; exact frob_mem_R l hk.le (ih _ _ _))
  have hnn : ∀ f ∈ R O K l k, 0 ≤ normR l k f := fun f hf =>
    (mul_nonneg (norm_nonneg _) (pow_nonneg hr.le 0)).trans (le_normR hf 0)
  let D : ℕ → ZMod a → Matrix ι ι K⟦X⟧ := fun n τ => Z (n + 1) τ - Z n τ
  have hD : ∀ n τ i j, D (n + 1) τ i j =
      ∑ q, (∑ p, B τ i p * frob K l (D n (τ - 1) p q)) * C (c τ q j) := by
    intro n τ i j
    simp only [D, Matrix.sub_apply]
    rw [hrec (n + 1) τ, hrec n τ]
    simp only [Matrix.mul_apply, Matrix.map_apply, ← Finset.sum_sub_distrib, ← sub_mul, ← mul_sub,
      map_sub, Matrix.sub_apply]
  obtain ⟨β, hβ0, hBbd⟩ : ∃ β : ℝ, 0 ≤ β ∧ ∀ τ i j, CoeffBd (rad l k) β (B τ i j) :=
    ⟨∑ x : ZMod a × ι × ι, normR l k (B x.1 x.2.1 x.2.2),
      Finset.sum_nonneg fun x _ => hnn _ (hB _ _ _), fun τ i j m =>
      (le_normR (hB τ i j) m).trans (Finset.single_le_sum
        (f := fun x : ZMod a × ι × ι => normR l k (B x.1 x.2.1 x.2.2))
        (fun x _ => hnn _ (hB _ _ _)) (Finset.mem_univ (τ, i, j)))⟩
  obtain ⟨γ, hγ0, hcbd⟩ : ∃ γ : ℝ, 0 ≤ γ ∧ ∀ τ i j, ‖c τ i j‖ ≤ γ :=
    ⟨∑ x : ZMod a × ι × ι, ‖c x.1 x.2.1 x.2.2‖, Finset.sum_nonneg fun x _ => norm_nonneg _,
      fun τ i j => Finset.single_le_sum (f := fun x : ZMod a × ι × ι => ‖c x.1 x.2.1 x.2.2‖)
        (fun x _ => norm_nonneg _) (Finset.mem_univ (τ, i, j))⟩
  have hD0mem : ∀ τ i j, D 0 τ i j ∈ R O K l k := fun τ i j =>
    sub_mem (hmem 1 τ i j) (hmem 0 τ i j)
  obtain ⟨N, hN0, hNbd⟩ : ∃ N : ℝ, 0 ≤ N ∧ ∀ τ i j, CoeffBd (rad l k) N (D 0 τ i j) :=
    ⟨∑ x : ZMod a × ι × ι, normR l k (D 0 x.1 x.2.1 x.2.2),
      Finset.sum_nonneg fun x _ => hnn _ (hD0mem _ _ _), fun τ i j m =>
      (le_normR (hD0mem τ i j) m).trans (Finset.single_le_sum
        (f := fun x : ZMod a × ι × ι => normR l k (D 0 x.1 x.2.1 x.2.2))
        (fun x _ => hnn _ (hD0mem _ _ _)) (Finset.mem_univ (τ, i, j)))⟩
  have key : ∀ n, ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ rad l k → ∀ τ i j,
      CoeffBd ρ (N / rad l k * (β * γ) ^ n * ρ ^ (l ^ n)) (D n τ i j) := by
    intro n
    induction n with
    | zero =>
      intro ρ hρ hρr τ i j
      simp only [pow_zero, mul_one, pow_one]
      refine bd_of_coeff_zero hr hρ hρr (hNbd τ i j) ?_
      rw [coeff_zero_eq_constantCoeff_apply]
      exact X_dvd_iff.1 (hX τ i j)
    | succ n ih =>
      intro ρ hρ hρr τ i j
      rw [hD]
      have hρl : ρ ^ l ≤ rad l k :=
        (pow_le_of_le_one hρ (hρr.trans hr1) (Fact.out : l.Prime).ne_zero).trans hρr
      have hM0 : 0 ≤ N / rad l k * (β * γ) ^ n * (ρ ^ l) ^ (l ^ n) :=
        mul_nonneg (mul_nonneg (div_nonneg hN0 hr.le) (pow_nonneg (mul_nonneg hβ0 hγ0) _))
          (pow_nonneg (pow_nonneg hρ _) _)
      have bnd : N / rad l k * (β * γ) ^ (n + 1) * ρ ^ (l ^ (n + 1)) =
          (β * (N / rad l k * (β * γ) ^ n * (ρ ^ l) ^ (l ^ n))) * γ := by
        rw [← pow_mul, ← pow_succ']
        ring
      rw [bnd]
      refine bd_sum _ _ hρ (mul_nonneg (mul_nonneg hβ0 hM0) hγ0) fun q _ =>
        bd_mul hρ (mul_nonneg hβ0 hM0) hγ0 ?_ (bd_le (hcbd τ q j) (bd_C (c τ q j)))
      exact bd_sum _ _ hρ (mul_nonneg hβ0 hM0) fun p _ =>
        bd_mul hρ hβ0 hM0 (bd_mono hρ hρr (hBbd τ i p))
          (bd_frob l hM0 (ih (ρ ^ l) (pow_nonneg hρ _) hρl (τ - 1) p q))
  refine ⟨N / rad l k, β * γ, mul_nonneg hβ0 hγ0, fun n τ i j => ⟨hmem n τ i j, ?_⟩⟩
  exact ciSup_le fun m => key n (rad l k) hr.le le_rfl τ i j m
end

section

noncomputable section

open PowerSeries GlobalTheory.BK Matrix

namespace GlobalTheory.LiftCoker

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]

theorem map_mem_A (f : O⟦X⟧) : PowerSeries.map (algebraMap O K) f ∈ A O K := by
  rw [← coe_equivA]
  exact (equivA O K f).2


variable (O K) in
def colon {ι κ : Type} [Fintype ι] (G : Matrix κ ι K⟦X⟧) : Ideal O⟦X⟧ where
  carrier := {α | ∀ w : κ → K⟦X⟧, (∀ i, w i ∈ A O K) →
    ∃ m : ι → K⟦X⟧, (∀ j, m j ∈ A O K) ∧ PowerSeries.map (algebraMap O K) α • w = G *ᵥ m}
  add_mem' {α β} hα hβ w hw := by
    obtain ⟨m, hm, h⟩ := hα w hw
    obtain ⟨m', hm', h'⟩ := hβ w hw
    exact ⟨m + m', fun j => add_mem (hm j) (hm' j), by rw [map_add (f := _), add_smul, h, h', Matrix.mulVec_add]⟩
  zero_mem' w _ := ⟨0, fun _ => zero_mem _, by simp⟩
  smul_mem' c α hα w hw := by
    obtain ⟨m, hm, h⟩ := hα w hw
    refine ⟨PowerSeries.map (algebraMap O K) c • m, fun j => ?_, ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul]
      exact mul_mem (map_mem_A c) (hm j)
    · rw [smul_eq_mul, map_mul, mul_smul, h, Matrix.mulVec_smul]

theorem mem_colon {ι κ : Type} [Fintype ι] {G : Matrix κ ι K⟦X⟧} {α : O⟦X⟧} :
    α ∈ colon O K G ↔ ∀ w : κ → K⟦X⟧, (∀ i, w i ∈ A O K) →
      ∃ m : ι → K⟦X⟧, (∀ j, m j ∈ A O K) ∧ PowerSeries.map (algebraMap O K) α • w = G *ᵥ m := Iff.rfl

end GlobalTheory.LiftCoker
end
end

section

open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory

theorem mem_R_of_adic_limit (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l : ℕ) (k : ℝ) (f : K⟦X⟧) (s : ℕ → K⟦X⟧)
    (hs : ∀ n, s n ∈ R O K l k) (hf : ∀ n, (X : K⟦X⟧) ^ (n + 1) ∣ f - s n)
    (ht : Tendsto (fun n => normR l k (s (n + 1) - s n)) atTop (𝓝 0)) : f ∈ R O K l k := by
  rw [mem_R]
  have hr : ∀ m : ℕ, 0 ≤ rad l k ^ m := fun m => pow_nonneg (rad_nonneg l k) m
  have hc : ∀ m, coeff m f = coeff m (s m) := fun m => by
    have := X_pow_dvd_iff.1 (hf m) m (Nat.lt_succ_self m)
    rwa [map_sub, sub_eq_zero] at this
  rw [Metric.tendsto_atTop] at ht ⊢
  intro ε hε
  obtain ⟨j, hj⟩ := ht ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (mem_R.1 (hs j)) ε hε
  refine ⟨max j N, fun m hm => ?_⟩
  have key : ∀ t, j ≤ t → ‖coeff m (s t)‖ * rad l k ^ m < ε := by
    intro t h
    induction t, h using Nat.le_induction with
    | base =>
      have := hN m (le_of_max_le_right hm)
      rw [Real.dist_eq, sub_zero] at this
      exact (le_abs_self _).trans_lt this
    | succ t h ih =>
      have h1 := hj t h
      rw [Real.dist_eq, sub_zero] at h1
      have h2 : ‖coeff m (s (t + 1) - s t)‖ * rad l k ^ m < ε :=
        (le_normR (O := O) (sub_mem (hs (t + 1)) (hs t)) m).trans_lt ((le_abs_self _).trans_lt h1)
      have h3 : coeff m (s (t + 1)) = coeff m (s t) + coeff m (s (t + 1) - s t) := by
        rw [map_sub]; ring
      rw [h3]
      refine (mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (hr m)).trans_lt ?_
      rw [max_mul_of_nonneg _ _ (hr m)]
      exact max_lt ih h2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hr m)), hc]
  exact key m (le_of_max_le_left hm)

end GlobalTheory
end

section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.CoeffComplete

open Filter Topology

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]

theorem norm_natCast_prime_eq : ‖(l : K)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] K) l, norm_algebraMap']
  exact Padic.norm_p

theorem natCast_smul_pow_eq (k : ℕ) (z : O) : ((l : ℤ_[l]) ^ k) • z = (l : O) ^ k * z := by
  rw [Algebra.smul_def, map_pow, map_natCast]

theorem norm_intCoord_le_one {ι : Type} [Fintype ι] (v : ι → ℤ_[l]) : ‖v‖ ≤ 1 :=
  (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => PadicInt.norm_le_one _

variable {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ_[l] O)

theorem coord_small_of_small (y : O) (k : ℕ) (h : ‖algebraMap O K y‖ ≤ ‖(l : K)‖ ^ k) :
    ‖b.equivFun y‖ ≤ ‖(l : ℤ_[l])‖ ^ k := by
  have hl : (l : K) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_natCast_prime_eq (l := l)]
    exact inv_ne_zero (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have hw : ‖algebraMap O K y / (l : K) ^ k‖ ≤ 1 := by
    rw [norm_div, norm_pow]
    exact div_le_one_of_le₀ h (by positivity)
  obtain ⟨z, hz⟩ := (IsUnitBall.mem_range_iff (O := O) _).2 hw
  have hy : y = (l : O) ^ k * z := by
    apply IsUnitBall.inj (K := K)
    rw [map_mul, hz, map_pow, map_natCast, mul_div_cancel₀ _ (pow_ne_zero _ hl)]
  rw [hy, ← natCast_smul_pow_eq, map_smul]
  calc ‖((l : ℤ_[l]) ^ k) • b.equivFun z‖ ≤ ‖(l : ℤ_[l]) ^ k‖ * ‖b.equivFun z‖ := norm_smul_le _ _
    _ ≤ ‖(l : ℤ_[l]) ^ k‖ * 1 := by gcongr; exact norm_intCoord_le_one _
    _ = ‖(l : ℤ_[l])‖ ^ k := by rw [mul_one, norm_pow]

theorem small_of_coord_small (y : O) (k : ℕ) (h : ‖b.equivFun y‖ ≤ ‖(l : ℤ_[l])‖ ^ k) :
    ‖algebraMap O K y‖ ≤ ‖(l : K)‖ ^ k := by
  have hd : ∀ i, ((l : ℤ_[l]) ^ k) ∣ b.equivFun y i := by
    intro i
    rw [← Ideal.mem_span_singleton, ← PadicInt.norm_le_pow_iff_mem_span_pow]
    have := (pi_norm_le_iff_of_nonneg (by positivity)).1 h i
    rw [PadicInt.norm_p, inv_pow, ← zpow_natCast, ← zpow_neg] at this
    exact this
  choose e he using hd
  have hy : y = (l : O) ^ k * b.equivFun.symm e := by
    rw [← natCast_smul_pow_eq, ← map_smul, ← b.equivFun.symm_apply_apply y]
    congr 1
    funext i
    simp [he i]
  rw [hy, map_mul, map_pow, map_natCast, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (by positivity) (norm_algebraMap_le _)

theorem completeSpace_of_finite_unitBall : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K], CompleteSpace K := by
  intro l _ O K _ _ _ _ _ _ _ _ _
  let b := Module.Free.chooseBasis ℤ_[l] O
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hϖ0 : 0 < ‖(l : K)‖ := by rw [norm_natCast_prime_eq (l := l)]; positivity
  have hϖ1 : ‖(l : K)‖ < 1 := by
    rw [norm_natCast_prime_eq (l := l)]; exact inv_lt_one_of_one_lt₀ hl1
  have hπ0 : 0 < ‖(l : ℤ_[l])‖ := by rw [PadicInt.norm_p]; positivity
  have hπ1 : ‖(l : ℤ_[l])‖ < 1 := by rw [PadicInt.norm_p]; exact inv_lt_one_of_one_lt₀ hl1
  refine Metric.complete_of_convergent_controlled_sequences (fun N => ‖(l : K)‖ ^ N)
    (fun n => pow_pos hϖ0 n) ?_
  intro u hu
  have h0 : ∀ n, ‖u n - u 0‖ ≤ 1 := fun n => by
    have := hu 0 n 0 (Nat.zero_le _) le_rfl
    rw [dist_eq_norm, pow_zero] at this
    exact this.le
  choose y hy using fun n => (IsUnitBall.mem_range_iff (O := O) _).2 (h0 n)
  have hc : CauchySeq (fun n => b.equivFun (y n)) := by
    refine cauchySeq_of_le_tendsto_0 (fun N => ‖(l : ℤ_[l])‖ ^ N) (fun n m N hn hm => ?_) ?_
    · rw [dist_eq_norm, ← map_sub]
      apply coord_small_of_small (K := K) b
      rw [map_sub, hy, hy, show u n - u 0 - (u m - u 0) = u n - u m by abel]
      have := hu N n m hn hm
      rw [dist_eq_norm] at this
      exact this.le
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one hπ0.le hπ1
  obtain ⟨γ, hγ⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨u 0 + algebraMap O K (b.equivFun.symm γ), ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε hϖ1
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hγ _ (pow_pos hπ0 k)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  have e : u n - (u 0 + algebraMap O K (b.equivFun.symm γ)) =
      algebraMap O K (y n - b.equivFun.symm γ) := by
    rw [map_sub, hy]; abel
  rw [e]
  refine lt_of_le_of_lt (small_of_coord_small b _ k ?_) hk
  rw [map_sub, LinearEquiv.apply_symm_apply]
  have := hN n hn
  rw [dist_eq_norm] at this
  exact this.le

end GlobalTheory.CoeffComplete
end

section

open ReciprocityTheory.Gal

namespace GlobalTheory.ShapeNeg

theorem ko_killed_by_pow_uniformizer : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}, Irreducible ϖ →
    ∀ x : Formalism.NG.KO O, ∃ n : ℕ, ϖ ^ n • x = 0 := by
  intro O _ _ _ ϖ hϖ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) y
  have hb : (b : O) ≠ 0 := nonZeroDivisors.ne_zero b.2
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
  refine ⟨n, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
  refine ⟨a * ((u⁻¹ : Oˣ) : O), ?_⟩
  rw [Algebra.smul_def, IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.eq_mk'_iff_mul_eq,
    ← map_mul]
  congr 1
  rw [hu]
  calc a * ((u⁻¹ : Oˣ) : O) * ((u : O) * ϖ ^ n) = a * ϖ ^ n * (((u⁻¹ : Oˣ) : O) * u) := by ring
    _ = ϖ ^ n * a := by simp [mul_comm]

end GlobalTheory.ShapeNeg
end
