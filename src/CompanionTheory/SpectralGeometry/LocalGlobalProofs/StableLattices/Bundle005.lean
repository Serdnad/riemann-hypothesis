module

public import Mathlib.Basic.Real.Basic
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle002
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CapelliComplements.Bundle001
public import Mathlib.Tactic.Bound
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

@[expose] public section

section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL.Lower

theorem conj_entry {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}
    (p : Lˣ) (a : Fin n → ℤ) (w : GL (Fin n) L) (i j : Fin n) :
    (((GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ * w * GlobalTheory.CompanionTheory.CartGL.dPow p a : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) i j =
      ((p ^ (-a i) : Lˣ) : L) * (w : Matrix (Fin n) (Fin n) L) i j * ((p ^ a j : Lˣ) : L) := by
  have h : (((GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      diagonal fun i => ((p ^ (-a i) : Lˣ) : L) := rfl
  rw [Units.val_mul, Units.val_mul, h, GlobalTheory.CompanionTheory.CartGL.dPow_val, mul_diagonal, diagonal_mul]

theorem norm_conj_le {L : Type} [NontriviallyNormedField L] (p : Lˣ) (hp : ‖(p : L)‖ < 1)
    {b c : ℤ} (hbc : b ≤ c) (x : L) :
    ‖((p ^ (-b) : Lˣ) : L) * x * ((p ^ c : Lˣ) : L)‖ ≤ ‖x‖ := by
  have hp0 : (0 : ℝ) < ‖(p : L)‖ := norm_pos_iff.mpr p.ne_zero
  obtain ⟨m, hm⟩ : ∃ m : ℕ, c = b + m := ⟨(c - b).toNat, by omega⟩
  have e : ‖((p ^ (-b) : Lˣ) : L) * x * ((p ^ c : Lˣ) : L)‖ = ‖x‖ * ‖(p : L)‖ ^ m := by
    rw [norm_mul, norm_mul, Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, norm_zpow,
      norm_zpow, hm, zpow_add₀ hp0.ne', _root_.zpow_neg, zpow_natCast]
    have : ‖(p : L)‖ ^ b ≠ 0 := (zpow_pos hp0 b).ne'
    field_simp
  rw [e]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hp0.le hp.le)

theorem conj_lower_contract : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ), ‖(p : L)‖ < 1 → ∀ (a : Fin n → ℤ), Antitone a → ∀ (r : ℝ) (w : GL (Fin n) L), (∀ i j, i < j → (w : Matrix (Fin n) (Fin n) L) i j = 0) → (∀ i j, ‖((w : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r) → ∀ i j, ‖((((GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ * w * GlobalTheory.CompanionTheory.CartGL.dPow p a : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := by
  intro L _ _ n p hp a ha r w hl hr i j
  rw [Matrix.sub_apply, conj_entry]
  rcases lt_trichotomy i j with h | h | h
  · have h0 := hr i j
    rw [Matrix.sub_apply, hl i j h, Matrix.one_apply_ne h.ne] at h0
    rw [hl i j h, Matrix.one_apply_ne h.ne]
    simpa using h0
  · subst h
    have hne : ((p ^ (-a i) : Lˣ) : L) * ((p ^ a i : Lˣ) : L) = 1 := by
      rw [← Units.val_mul, _root_.zpow_neg, inv_mul_cancel, Units.val_one]
    have e : ((p ^ (-a i) : Lˣ) : L) * (w : Matrix (Fin n) (Fin n) L) i i * ((p ^ a i : Lˣ) : L) =
        (w : Matrix (Fin n) (Fin n) L) i i := by
      rw [mul_right_comm, hne, one_mul]
    rw [e]
    simpa [Matrix.sub_apply] using hr i i
  · have h0 := hr i j
    rw [Matrix.sub_apply, Matrix.one_apply_ne h.ne', sub_zero] at h0
    rw [Matrix.one_apply_ne h.ne', sub_zero]
    exact (norm_conj_le p hp (ha h.le) _).trans h0

end GlobalTheory.CompanionTheory.CartGL.Lower
end
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem conj_upper_contract : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (p : Lˣ), ‖(p : L)‖ < 1 → ∀ (a : Fin n → ℤ), Antitone a → ∀ (r : ℝ) (u : GL (Fin n) L), (∀ i j, j < i → (u : Matrix (Fin n) (Fin n) L) i j = 0) → (∀ i j, ‖((u : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r) → ∀ i j, ‖(((GlobalTheory.CompanionTheory.CartGL.dPow p a * u * (GlobalTheory.CompanionTheory.CartGL.dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j‖ ≤ r := by
  intro L _ _ n p hp a ha r u hlow hr i j
  have hinv : (((dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) =
      diagonal fun i => ((p ^ (-a i) : Lˣ) : L) := rfl
  have hent : ((dPow p a * u * (dPow p a)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j =
      ((p ^ (a i - a j) : Lˣ) : L) * (u : Matrix (Fin n) (Fin n) L) i j := by
    rw [Units.val_mul, Units.val_mul, dPow_val, hinv, Matrix.mul_diagonal, Matrix.diagonal_mul,
      sub_eq_add_neg, _root_.zpow_add, Units.val_mul]
    ring
  rw [Matrix.sub_apply, hent]
  have hri := hr i j
  rw [Matrix.sub_apply] at hri
  rcases lt_trichotomy i j with hij | hij | hij
  · have hne : i ≠ j := ne_of_lt hij
    rw [Matrix.one_apply_ne hne] at hri ⊢
    rw [sub_zero] at hri ⊢
    have hexp : 0 ≤ a i - a j := sub_nonneg.mpr (ha hij.le)
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hexp
    have hpow : ‖((p ^ (a i - a j) : Lˣ) : L)‖ ≤ 1 := by
      rw [hm, zpow_natCast, Units.val_pow_eq_pow_val, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) hp.le
    rw [norm_mul]
    calc _ ≤ 1 * ‖(u : Matrix (Fin n) (Fin n) L) i j‖ :=
          mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ = _ := one_mul _
      _ ≤ r := hri
  · subst hij
    simpa using hri
  · rw [hlow i j hij, mul_zero]
    rw [hlow i j hij] at hri
    exact hri

end GlobalTheory.CompanionTheory.CartGL
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

theorem exists_tExp_eq_indicator (b : Fin n → ℤ) (hb : Antitone b) :
    ∃ i : Fin (n + 2), tExp n i = fun j => if 0 < b j then 1 else 0 := by
  classical
  have hex : ∃ i : ℕ, i = n ∨ ∃ h : i < n, b ⟨i, h⟩ ≤ 0 := ⟨n, Or.inl rfl⟩
  have hle : Nat.find hex ≤ n := Nat.find_min' hex (Or.inl rfl)
  refine ⟨⟨Nat.find hex, by omega⟩, ?_⟩
  funext j
  have hne : Nat.find hex ≠ n + 1 := by omega
  simp only [tExp, hne, if_false]
  by_cases hj : (j : ℕ) < Nat.find hex
  · have hnot := Nat.find_min hex hj
    have hpos : 0 < b j := by
      by_contra hcon
      exact hnot (Or.inr ⟨j.2, not_lt.mp hcon⟩)
    rw [if_pos hj, if_pos hpos]
  · have hspec := Nat.find_spec hex
    have hnpos : ¬ 0 < b j := by
      rcases hspec with h | ⟨h, h'⟩
      · have := j.2
        omega
      · have hmono : b j ≤ b ⟨Nat.find hex, h⟩ := hb (by
          rw [Fin.le_def]
          exact not_lt.mp hj)
        omega
    rw [if_neg hj, if_neg hnpos]

theorem dPow_mem_closure_of_nonneg (p : Lˣ) (N : ℕ) :
    ∀ b : Fin n → ℤ, Antitone b → (∀ j, 0 ≤ b j) → (∀ j, b j ≤ N) →
      dPow p b ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  induction N with
  | zero =>
    intro b _ h0 hN
    have hb : b = 0 := by
      funext j
      have h1 := h0 j
      have h2 := hN j
      simp only [Nat.cast_zero] at h2
      simp only [Pi.zero_apply]
      omega
    rw [hb, dPow_zero]
    exact Submonoid.one_mem _
  | succ N ih =>
    intro b hb h0 hN
    obtain ⟨i, hi⟩ := exists_tExp_eq_indicator b hb
    have hdecomp : b = (fun j => b j - if 0 < b j then 1 else 0) + tExp n i := by
      rw [hi]
      funext j
      simp
    rw [hdecomp, dPow_add]
    refine Submonoid.mul_mem _ (ih _ ?_ ?_ ?_) (Submonoid.subset_closure ⟨i, rfl⟩)
    · intro x y hxy
      have hm := hb hxy
      have hx := h0 x
      have hy := h0 y
      show (b y - if 0 < b y then 1 else 0) ≤ (b x - if 0 < b x then 1 else 0)
      split_ifs <;> omega
    · intro j
      have h1 := h0 j
      show 0 ≤ (b j - if 0 < b j then 1 else 0)
      split_ifs <;> omega
    · intro j
      have h1 := h0 j
      have h2 := hN j
      push_cast at h2
      show (b j - if 0 < b j then 1 else 0) ≤ (N : ℤ)
      split_ifs <;> omega

theorem dPow_mem_closure_of_ge (p : Lˣ) (C : ℕ) :
    ∀ a : Fin n → ℤ, Antitone a → (∀ j, -(C : ℤ) ≤ a j) →
      dPow p a ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  induction C with
  | zero =>
    intro a ha h0
    have hbd : ∀ j, a j ≤ ((∑ k, (a k).natAbs : ℕ) : ℤ) := by
      intro j
      have h1 : (a j).natAbs ≤ ∑ k, (a k).natAbs :=
        Finset.single_le_sum (f := fun k => (a k).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ j)
      omega
    refine dPow_mem_closure_of_nonneg p _ a ha (fun j => ?_) hbd
    have := h0 j
    simpa using this
  | succ C ih =>
    intro a ha h0
    have hlast : tExp n (Fin.last (n + 1)) = fun _ => -1 := by
      funext j
      simp [tExp]
    have hdecomp : a = (fun j => a j + 1) + tExp n (Fin.last (n + 1)) := by
      rw [hlast]
      funext j
      simp
    rw [hdecomp, dPow_add]
    refine Submonoid.mul_mem _ (ih _ ?_ ?_)
      (Submonoid.subset_closure ⟨Fin.last (n + 1), rfl⟩)
    · intro x y hxy
      have := ha hxy
      show a y + 1 ≤ a x + 1
      omega
    · intro j
      have := h0 j
      push_cast at this
      show -(C : ℤ) ≤ a j + 1
      omega

theorem dPow_antitone_mem_closure (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]
    (n : ℕ) (p : Lˣ) (a : Fin n → ℤ) (ha : Antitone a) :
    dPow p a ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L)) := by
  refine dPow_mem_closure_of_ge p (∑ k, (a k).natAbs) a ha (fun j => ?_)
  have h1 : (a j).natAbs ≤ ∑ k, (a k).natAbs :=
    Finset.single_le_sum (f := fun k => (a k).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ j)
  omega

end GlobalTheory.CompanionTheory.CartGL
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem tExp_antitone (n : ℕ) (i : Fin (n + 2)) : Antitone (tExp n i) := by
  intro j k hjk
  have hjk' : (j : ℕ) ≤ (k : ℕ) := hjk
  unfold tExp
  by_cases h : (i : ℕ) = n + 1
  · simp [h]
  · simp only [h, if_false]
    by_cases hk : (k : ℕ) < i
    · have hj : (j : ℕ) < i := lt_of_le_of_lt hjk' hk
      simp [hj, hk]
    · by_cases hj : (j : ℕ) < i <;> simp [hj, hk]

theorem closure_tGen_antitone (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ)
    (p : Lˣ) (s : GL (Fin n) L)
    (hs : s ∈ Submonoid.closure (Set.range (tGen p : Fin (n + 2) → GL (Fin n) L))) :
    ∃ a : Fin n → ℤ, Antitone a ∧ s = dPow p a := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨tExp n i, tExp_antitone n i, rfl⟩
  | one => exact ⟨0, fun _ _ _ => le_rfl, (dPow_zero p).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a + b, ha.add hb, (dPow_add p a b).symm⟩

end GlobalTheory.CompanionTheory.CartGL
end

section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

section SlopeTestRemainingChoices

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

theorem norm_prod_sub_prod_le {ι : Type} (s : Finset ι) (f g : ι → L) {r : ℝ} (h0 : 0 ≤ r)
    (hf : ∀ i, ‖f i‖ ≤ 1) (hg : ∀ i, ‖g i‖ ≤ 1) (hfg : ∀ i, ‖f i - g i‖ ≤ r) :
    ‖∏ i ∈ s, f i - ∏ i ∈ s, g i‖ ≤ r :=
  _root_.Bl.FirstLemmaE.goal1 s f g h0 hf hg hfg

theorem norm_det_sub_det_le {A B : Matrix (Fin n) (Fin n) L} {r : ℝ} (h0 : 0 ≤ r)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ i j, ‖B i j‖ ≤ 1) (hAB : ∀ i j, ‖(A - B) i j‖ ≤ r) :
    ‖A.det - B.det‖ ≤ r := by
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0 fun σ _ => ?_
  rw [← smul_sub]
  have h := norm_prod_sub_prod_le Finset.univ (fun i => A (σ i) i) (fun i => B (σ i) i) h0
    (fun i => hA _ _) (fun i => hB _ _) (fun i => by simpa using hAB (σ i) i)
  have h' : ‖∏ i, B (σ i) i - ∏ i, A (σ i) i‖ ≤ r := by
    rw [norm_sub_rev]
    exact h
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs, Units.smul_def] using h
  · simpa [hs, Units.smul_def] using h'

theorem norm_det_le_one {A : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  have h : ‖∏ i, A (σ i) i‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => hA _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simpa [hs, Units.smul_def] using h

theorem norm_one_entry_le (i j : Fin n) : ‖(1 : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 := by
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, norm_one]
  · rw [Matrix.one_apply_ne h, norm_zero]
    exact zero_le_one

theorem norm_adjugate_entry_le {A : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, ‖A i j‖ ≤ 1) (i j : Fin n) :
    ‖A.adjugate i j‖ ≤ 1 := by
  rw [Matrix.adjugate_apply]
  refine norm_det_le_one fun a b => ?_
  by_cases h : a = j
  · subst h
    rw [Matrix.updateRow_self]
    by_cases h' : b = i
    · simp [h']
    · simp [Pi.single_eq_of_ne h']
  · rw [Matrix.updateRow_ne h]
    exact hA a b

end SlopeTestRemainingChoices

theorem exists_mem_congK_of_entries : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L]
    (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r < 1 → ∀ A : Matrix (Fin n) (Fin n) L,
    (∀ i j, ‖(A - 1) i j‖ ≤ r) →
    ∃ k ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1, (k : Matrix (Fin n) (Fin n) L) = A := by
  intro L _ _ n r h0 h1 hr A hA
  have hA1 : ∀ i j, ‖A i j‖ ≤ 1 := by
    intro i j
    have e : A i j = (A - 1) i j + (1 : Matrix (Fin n) (Fin n) L) i j := by simp
    rw [e]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((hA i j).trans h1) (norm_one_entry_le i j))
  have hd : ‖A.det - 1‖ ≤ r := by
    have := norm_det_sub_det_le h0 hA1 norm_one_entry_le hA
    rwa [Matrix.det_one] at this
  have hd1 : 1 ≤ ‖A.det‖ := by
    have e : (1 : L) = A.det + -(A.det - 1) := by ring
    have h2 : ‖(1 : L)‖ ≤ max ‖A.det‖ ‖A.det - 1‖ := by
      conv_lhs => rw [e]
      rw [← norm_neg (A.det - 1)]
      exact IsUltrametricDist.norm_add_le_max _ _
    rw [norm_one] at h2
    rcases le_max_iff.mp h2 with h | h
    · exact h
    · linarith
  have hne : A.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hd1
    linarith
  have hinv : ∀ i j, ‖A⁻¹ i j‖ ≤ 1 := by
    intro i j
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv]
    exact mul_le_one₀ (inv_le_one_of_one_le₀ hd1) (norm_nonneg _) (norm_adjugate_entry_le hA1 i j)
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hne
  have hk : ((Matrix.GeneralLinearGroup.mkOfDetNeZero A hne : GL (Fin n) L) :
      Matrix (Fin n) (Fin n) L) = A := rfl
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hne, ?_, hk⟩
  rw [mem_congK]
  intro i j
  refine ⟨by rw [hk]; exact hA i j, ?_⟩
  rw [Matrix.coe_units_inv, hk]
  have e : A⁻¹ - 1 = -(A⁻¹ * (A - 1)) := by
    rw [Matrix.mul_sub, Matrix.nonsing_inv_mul A hu, Matrix.mul_one]
    abel
  rw [e, Matrix.neg_apply, norm_neg]
  simpa using entry_mul zero_le_one h0 hinv hA i j

end GlobalTheory.CompanionTheory.CartGL
end
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL.Normal

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}

theorem entry_le_one {A : Matrix (Fin n) (Fin n) L} (hA : ∀ i j, ‖(A - 1) i j‖ ≤ 1) (i j : Fin n) :
    ‖A i j‖ ≤ 1 := by
  have e : A i j = (A - 1) i j + (1 : Matrix (Fin n) (Fin n) L) i j := by simp
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hA i j) ?_)
  by_cases h : i = j
  · subst h
    rw [Matrix.one_apply_eq, norm_one]
  · rw [Matrix.one_apply_ne h, norm_zero]
    exact zero_le_one

theorem entry_conj {C D X : Matrix (Fin n) (Fin n) L} {r : ℝ} (h0 : 0 ≤ r)
    (hC : ∀ i j, ‖C i j‖ ≤ 1) (hD : ∀ i j, ‖D i j‖ ≤ 1) (hCD : C * D = 1)
    (hX : ∀ i j, ‖(X - 1) i j‖ ≤ r) (i j : Fin n) : ‖(C * X * D - 1) i j‖ ≤ r := by
  have e : C * X * D - 1 = C * (X - 1) * D := by
    rw [mul_sub, sub_mul, mul_one, hCD]
  rw [e]
  have h := entry_mul (mul_nonneg zero_le_one h0) zero_le_one
    (entry_mul zero_le_one h0 hC hX) hD i j
  simpa using h

theorem conj_mem_congK (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r ≤ 1) (c x : GL (Fin n) L)
    (hc : c ∈ GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl)
    (hx : x ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1) :
    c * x * c⁻¹ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 := by
  have hC : ∀ i j, ‖((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 :=
    entry_le_one fun i j => (hc i j).1
  have hD : ∀ i j, ‖(((c⁻¹ : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) i j‖ ≤ 1 :=
    entry_le_one fun i j => (hc i j).2
  have hCD : ((c : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((c⁻¹ : GL (Fin n) L)) : Matrix (Fin n) (Fin n) L) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  intro i j
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact entry_conj h0 hC hD hCD (fun i j => (hx i j).1) i j
  · have e : (c * x * c⁻¹)⁻¹ = c * x⁻¹ * c⁻¹ := by group
    rw [e, Units.val_mul, Units.val_mul]
    exact entry_conj h0 hC hD hCD (fun i j => (hx i j).2) i j

end GlobalTheory.CompanionTheory.CartGL.Normal
end

section

theorem _root_.GlobalTheory.T.exists_gap_interval_avoiding_finite_family : ∀ (n : ℕ) (l : Fin n → ℝ) (L : ℝ), 0 < L → (∀ i, 0 ≤ l i ∧ l i ≤ L) → (∃ i, l i = L) → ∃ r : ℕ, r < n ∧ ∀ i, l i < r * (L / (n + 1)) ∨ (r + 1) * (L / (n + 1)) ≤ l i := by
  exact GlobalTheory.CompanionTheory.UGeoGap.exists_gap_of_mem_Icc_top
end
