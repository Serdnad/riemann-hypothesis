module

public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

section Abstract

open MulAction

variable {Γ 𝒳 𝒴 : Type} [Group Γ] [MulAction Γ 𝒳] [MulAction Γ 𝒴]

theorem card_orbit_mul_card_stabilizer (A : Subgroup Γ) (x : 𝒳) (hle : stabilizer Γ x ≤ A) :
    Nat.card (orbit A x) * Nat.card (stabilizer Γ x) = Nat.card A := by
  have h1 : Nat.card (orbit A x) = Nat.card (A ⧸ stabilizer A x) :=
    Nat.card_congr (orbitEquivQuotientStabilizer A x)
  have h2 : stabilizer A x = (stabilizer Γ x).subgroupOf A := by
    ext a
    simp [mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.smul_def]
  have h3 : Nat.card (stabilizer A x) = Nat.card (stabilizer Γ x) := by
    rw [h2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [h1, ← h3, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

theorem card_stabilizer_smul_eq (g : Γ) (y : 𝒳) :
    Nat.card (stabilizer Γ (g • y)) = Nat.card (stabilizer Γ y) :=
  Nat.card_congr (stabilizerEquivStabilizerOfOrbitRel (G := Γ) (a := g • y) (b := y) ⟨g, rfl⟩).toEquiv

theorem sum_fibre_inv_card_stabilizer (m : 𝒳 → 𝒴) (hm : ∀ (γ : Γ) x, m (γ • x) = γ • m x) (R : Set 𝒳)
    (hR : ∀ (γ : Γ), ∀ x ∈ R, γ • x ∈ R) (s : Finset 𝒳) (hsR : ∀ x ∈ s, x ∈ R)
    (hs : ∀ x ∈ R, ∃! y, y ∈ s ∧ ∃ γ : Γ, γ • y = x) (M : 𝒴) (hA : Finite (stabilizer Γ M))
    (hfin : {x | x ∈ R ∧ m x = M}.Finite) [DecidablePred fun y : 𝒳 => ∃ γ : Γ, γ • M = m y] :
    ∑ y ∈ s.filter (fun y => ∃ γ : Γ, γ • M = m y), ((Nat.card (stabilizer Γ y) : ℕ) : ℝ)⁻¹ =
      ({x | x ∈ R ∧ m x = M}.ncard : ℝ) / (Nat.card (stabilizer Γ M) : ℝ) := by
  classical
  let O : 𝒳 → Set 𝒳 := fun y => {x | (x ∈ R ∧ m x = M) ∧ ∃ γ : Γ, γ • y = x}
  have hOfin : ∀ y, (O y).Finite := fun y => hfin.subset fun x hx => hx.1
  have hApos : (0 : ℝ) < (Nat.card (stabilizer Γ M) : ℝ) := by exact_mod_cast Nat.card_pos
  have hcard : ∀ y ∈ s.filter (fun y => ∃ γ : Γ, γ • M = m y),
      (O y).ncard * Nat.card (stabilizer Γ y) = Nat.card (stabilizer Γ M) := by
    intro y hy
    obtain ⟨hys, γ0, hγ0⟩ := Finset.mem_filter.1 hy
    have hmx : m (γ0⁻¹ • y) = M := by rw [hm, ← hγ0, inv_smul_smul]
    have hle : stabilizer Γ (γ0⁻¹ • y) ≤ stabilizer Γ M := by
      intro γ hγ
      rw [mem_stabilizer_iff] at hγ ⊢
      rw [← hmx, ← hm, hγ]
    have hO : O y = orbit (stabilizer Γ M) (γ0⁻¹ • y) := by
      ext x
      constructor
      · rintro ⟨⟨_, hxM⟩, γ, rfl⟩
        refine ⟨⟨γ * γ0, ?_⟩, ?_⟩
        · rw [mem_stabilizer_iff, mul_smul, hγ0, ← hm, hxM]
        · change (γ * γ0) • γ0⁻¹ • y = γ • y
          rw [mul_smul, smul_inv_smul]
      · rintro ⟨⟨a, ha⟩, rfl⟩
        rw [mem_stabilizer_iff] at ha
        refine ⟨⟨hR a _ (hR _ _ (hsR y hys)), ?_⟩, a * γ0⁻¹, ?_⟩
        · change m (a • γ0⁻¹ • y) = M
          rw [hm, hmx, ha]
        · change (a * γ0⁻¹) • y = a • γ0⁻¹ • y
          rw [mul_smul]
    rw [hO, ← card_stabilizer_smul_eq γ0⁻¹ y, ← Nat.card_coe_set_eq]
    exact card_orbit_mul_card_stabilizer _ _ hle
  have hpart : {x | x ∈ R ∧ m x = M}.ncard = ∑ y ∈ s.filter (fun y => ∃ γ : Γ, γ • M = m y), (O y).ncard := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    have hU : hfin.toFinset = (s.filter (fun y => ∃ γ : Γ, γ • M = m y)).biUnion fun y => (hOfin y).toFinset := by
      ext x
      simp only [Set.Finite.mem_toFinset, Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · intro hx
        obtain ⟨y, ⟨hy, γ, hγ⟩, _⟩ := hs x hx.1
        refine ⟨y, ⟨hy, γ⁻¹, ?_⟩, hx, γ, hγ⟩
        rw [← hx.2, ← hγ, hm, inv_smul_smul]
      · rintro ⟨y, _, hx, _⟩
        exact hx
    rw [hU, Finset.card_biUnion]
    · exact Finset.sum_congr rfl fun y _ => (Set.ncard_eq_toFinset_card _ (hOfin y)).symm
    · intro y hy y' hy' hne
      rw [Function.onFun, Finset.disjoint_left]
      rw [Finset.mem_coe] at hy hy'
      intro x hx hx'
      rw [Set.Finite.mem_toFinset] at hx hx'
      obtain ⟨y0, _, huniq⟩ := hs x hx.1.1
      exact hne ((huniq y ⟨(Finset.mem_filter.1 hy).1, hx.2⟩).trans
        (huniq y' ⟨(Finset.mem_filter.1 hy').1, hx'.2⟩).symm)
  rw [hpart, Nat.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h := hcard y hy
  have h' : ((O y).ncard : ℝ) * (Nat.card (stabilizer Γ y) : ℝ) = (Nat.card (stabilizer Γ M) : ℝ) := by
    exact_mod_cast h
  have hs0 : (Nat.card (stabilizer Γ y) : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h'
    exact hApos.ne h'
  rw [← h']
  have hO0 : ((O y).ncard : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h'
    exact hApos.ne h'
  field_simp

end Abstract

end Formalism.MainNotions.BridgeLemma₂

end
end

section

namespace Formalism.MainNotions.BridgeLemma₂

private theorem const_20736_le_exp_15 : (20736 : ℝ) ≤ Real.exp 15 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h2 : Real.exp 15 = Real.exp 1 ^ 15 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h2]
  calc (20736 : ℝ) ≤ 2 ^ 15 := by norm_num
    _ ≤ Real.exp 1 ^ 15 := pow_le_pow_left₀ (by norm_num) h1 15

theorem mass_pow_le_exp_rpow (f m : ℕ) (rd L B₁ C κ : ℝ) (hf : 1 ≤ f) (hm : 2 ≤ m) (hrd : 2 ≤ rd) (hL : 1 ≤ L) (hκ : 1 ≤ κ)
    (hlf : Real.log f ≤ m) (hlrd : Real.log rd ≤ κ * L) (hB0 : 0 ≤ B₁) (hB : B₁ ≤ 4 * f * rd) (hC : 55 * κ ≤ C ^ 2) :
    (1 + 2 * B₁) ^ (2 * (2 * f)) * (1 + 2 * (B₁ * rd)) ^ (2 * (2 * f)) * (B₁ * (B₁ * rd)) ^ (4 * (2 * f)) ≤
      (Real.exp L ^ (C * (m : ℝ) ^ 2 * f)) ^ C := by
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hfpos : (0 : ℝ) < f := by linarith
  have hrdpos : (0 : ℝ) < rd := by linarith
  have hfe : (f : ℝ) ≤ Real.exp m := (Real.log_le_iff_le_exp hfpos).1 hlf
  have hre : rd ≤ Real.exp (κ * L) := (Real.log_le_iff_le_exp hrdpos).1 hlrd
  have hfr : (1 : ℝ) ≤ f * rd := by nlinarith
  have hfr2 : (1 : ℝ) ≤ f * rd ^ 2 := by nlinarith
  have hBr0 : 0 ≤ B₁ * rd := mul_nonneg hB0 hrdpos.le
  have hBr : B₁ * rd ≤ 4 * f * rd * rd := mul_le_mul_of_nonneg_right hB hrdpos.le
  have ha : 1 + 2 * B₁ ≤ 9 * f * rd := by nlinarith
  have hb : 1 + 2 * (B₁ * rd) ≤ 9 * f * rd ^ 2 := by nlinarith
  have hc : B₁ * (B₁ * rd) ≤ 16 * (f : ℝ) ^ 2 * rd ^ 3 := by
    have h := mul_le_mul hB hBr hBr0 (by linarith)
    calc B₁ * (B₁ * rd) ≤ 4 * f * rd * (4 * f * rd * rd) := h
      _ = 16 * (f : ℝ) ^ 2 * rd ^ 3 := by ring
  have hQ0 : 0 ≤ (1 + 2 * B₁) * (1 + 2 * (B₁ * rd)) * (B₁ * (B₁ * rd)) ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)
  have hQ : (1 + 2 * B₁) * (1 + 2 * (B₁ * rd)) * (B₁ * (B₁ * rd)) ^ 2 ≤
      Real.exp (15 + 6 * (m : ℝ) + 9 * (κ * L)) := by
    have hc2 : (B₁ * (B₁ * rd)) ^ 2 ≤ (16 * (f : ℝ) ^ 2 * rd ^ 3) ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hB0 hBr0) hc 2
    have hab : (1 + 2 * B₁) * (1 + 2 * (B₁ * rd)) ≤ (9 * f * rd) * (9 * f * rd ^ 2) :=
      mul_le_mul ha hb (by linarith) (by linarith)
    have h1 : (1 + 2 * B₁) * (1 + 2 * (B₁ * rd)) * (B₁ * (B₁ * rd)) ^ 2 ≤
        (9 * f * rd) * (9 * f * rd ^ 2) * (16 * (f : ℝ) ^ 2 * rd ^ 3) ^ 2 :=
      mul_le_mul hab hc2 (sq_nonneg _) (mul_nonneg (by linarith) (by linarith))
    have h2 : (9 * f * rd) * (9 * f * rd ^ 2) * (16 * (f : ℝ) ^ 2 * rd ^ 3) ^ 2 =
        20736 * (f : ℝ) ^ 6 * rd ^ 9 := by ring
    have hf6 : (f : ℝ) ^ 6 ≤ Real.exp m ^ 6 := pow_le_pow_left₀ hfpos.le hfe 6
    have hr9 : rd ^ 9 ≤ Real.exp (κ * L) ^ 9 := pow_le_pow_left₀ hrdpos.le hre 9
    have h3 : 20736 * (f : ℝ) ^ 6 * rd ^ 9 ≤ Real.exp 15 * Real.exp m ^ 6 * Real.exp (κ * L) ^ 9 :=
      mul_le_mul (mul_le_mul const_20736_le_exp_15 hf6 (by positivity) (by positivity)) hr9
        (pow_nonneg hrdpos.le 9) (by positivity)
    have h4 : Real.exp (15 + 6 * (m : ℝ) + 9 * (κ * L)) =
        Real.exp 15 * Real.exp m ^ 6 * Real.exp (κ * L) ^ 9 := by
      rw [Real.exp_add, Real.exp_add, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
      norm_num
    rw [h4]
    calc _ ≤ _ := h1
      _ = _ := h2
      _ ≤ _ := h3
  have key : 60 + 24 * (m : ℝ) + 36 * (κ * L) ≤ C ^ 2 * ((m : ℝ) ^ 2 * L) := by
    have y1 : 1 ≤ κ * L := by nlinarith
    have hmm : 2 * (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    have hyl : (m : ℝ) ^ 2 ≤ κ * L * (m : ℝ) ^ 2 := by nlinarith
    have hy4 : 4 * (κ * L) ≤ κ * L * (m : ℝ) ^ 2 := by nlinarith
    have hCk : 55 * κ * ((m : ℝ) ^ 2 * L) ≤ C ^ 2 * ((m : ℝ) ^ 2 * L) :=
      mul_le_mul_of_nonneg_right hC (mul_nonneg (sq_nonneg _) (by linarith))
    nlinarith
  have hexp : ((2 * (2 * f) : ℕ) : ℝ) * (15 + 6 * (m : ℝ) + 9 * (κ * L)) ≤
      L * (C * (m : ℝ) ^ 2 * f) * C := by
    have e1 : ((2 * (2 * f) : ℕ) : ℝ) * (15 + 6 * (m : ℝ) + 9 * (κ * L)) =
        (f : ℝ) * (60 + 24 * (m : ℝ) + 36 * (κ * L)) := by push_cast; ring
    have e2 : L * (C * (m : ℝ) ^ 2 * f) * C = (f : ℝ) * (C ^ 2 * ((m : ℝ) ^ 2 * L)) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left key hfpos.le
  have hpow : 4 * (2 * f) = 2 * (2 * (2 * f)) := by ring
  rw [hpow, pow_mul (B₁ * (B₁ * rd)) 2 (2 * (2 * f)), ← mul_pow, ← mul_pow, ← Real.exp_mul,
    ← Real.exp_mul]
  calc _ ≤ (Real.exp (15 + 6 * (m : ℝ) + 9 * (κ * L))) ^ (2 * (2 * f)) :=
        pow_le_pow_left₀ hQ0 hQ _
    _ = Real.exp (((2 * (2 * f) : ℕ) : ℝ) * (15 + 6 * (m : ℝ) + 9 * (κ * L))) :=
        (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (L * (C * (m : ℝ) ^ 2 * f) * C) := Real.exp_le_exp.2 hexp

end Formalism.MainNotions.BridgeLemma₂
end

section

namespace Formalism.MainNotions.BridgeLemma₂

private theorem pow_rpow_eq_rpow_mul {x : ℝ} (hx : 0 ≤ x) (n : ℕ) (z : ℝ) :
    (x ^ n) ^ z = x ^ ((n : ℝ) * z) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

theorem rows_num_l {P σ h cr Γ a2 dq : ℝ} (hP : 1 ≤ P) (hσ : 1 ≤ σ) (h1 : 1 ≤ h) (hh : h ≤ P * σ ^ 4)
    (hcr : 0 ≤ cr) (hΓ : 0 ≤ Γ) :
    (h ^ cr) ^ 2 * (Γ * σ ^ a2) * σ ^ (-dq) ≤ (P ^ cr) ^ 2 * Γ * σ ^ (8 * cr + a2 - dq) := by
  have hσ0 : 0 < σ := by linarith
  have hP0 : 0 < P := by linarith
  have hh0 : 0 ≤ h := by linarith
  have key : h ^ cr ≤ P ^ cr * σ ^ (4 * cr) := by
    calc h ^ cr ≤ (P * σ ^ 4) ^ cr := Real.rpow_le_rpow hh0 hh hcr
      _ = P ^ cr * (σ ^ 4) ^ cr := Real.mul_rpow hP0.le (pow_nonneg hσ0.le 4)
      _ = P ^ cr * σ ^ (4 * cr) := by rw [pow_rpow_eq_rpow_mul hσ0.le]; norm_num
  have hsq : (h ^ cr) ^ 2 ≤ (P ^ cr * σ ^ (4 * cr)) ^ 2 := by
    rw [sq, sq]
    exact mul_le_mul key key (Real.rpow_nonneg hh0 _) (le_trans (Real.rpow_nonneg hh0 _) key)
  have e : σ ^ (8 * cr + a2 - dq) = σ ^ (4 * cr) * σ ^ (4 * cr) * σ ^ a2 * σ ^ (-dq) := by
    rw [← Real.rpow_add hσ0, ← Real.rpow_add hσ0, ← Real.rpow_add hσ0]
    congr 1
    ring
  have hnn : 0 ≤ Γ * σ ^ a2 * σ ^ (-dq) :=
    mul_nonneg (mul_nonneg hΓ (Real.rpow_nonneg hσ0.le _)) (Real.rpow_nonneg hσ0.le _)
  calc (h ^ cr) ^ 2 * (Γ * σ ^ a2) * σ ^ (-dq) = (h ^ cr) ^ 2 * (Γ * σ ^ a2 * σ ^ (-dq)) := by ring
    _ ≤ (P ^ cr * σ ^ (4 * cr)) ^ 2 * (Γ * σ ^ a2 * σ ^ (-dq)) := mul_le_mul_of_nonneg_right hsq hnn
    _ = (P ^ cr) ^ 2 * Γ * σ ^ (8 * cr + a2 - dq) := by rw [e]; ring

theorem rows_num_pair {P σ₁ σ₂ h₁ h₂ cr Γ a2 dq E1 F6 XiH XiP ck e l₁ l₂ : ℝ} (hP : 1 ≤ P) (hσ₁ : 1 ≤ σ₁) (hσ₂ : 1 ≤ σ₂)
    (h1₁ : 1 ≤ h₁) (h1₂ : 1 ≤ h₂) (hh₁ : h₁ ≤ P * σ₁ ^ 4) (hh₂ : h₂ ≤ P * σ₂ ^ 4) (hcr : 0 ≤ cr) (hΓ : 0 ≤ Γ)
    (hE1 : 0 ≤ E1) (hF6 : 0 ≤ F6) (hXiH : 0 ≤ XiH) (hXi : XiH ≤ XiP * (σ₁ * σ₂) ^ (4 * ck))
    (hl₁ : l₁ = (h₁ ^ cr) ^ 2 * (Γ * σ₁ ^ a2) * σ₁ ^ (-dq)) (hl₂ : l₂ = (h₂ ^ cr) ^ 2 * (Γ * σ₂ ^ a2) * σ₂ ^ (-dq))
    (he : 4 * ck + 4 * E1 + 4 * cr + a2 / 2 - dq / 2 ≤ -e) :
    XiH * ((h₁ * h₂) ^ E1 * F6) * Real.sqrt (l₁ * l₂) ≤
      XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) * (σ₁ ^ (-e) * σ₂ ^ (-e)) := by
  have hP0 : 0 < P := by linarith
  have hσ₁0 : 0 < σ₁ := by linarith
  have hσ₂0 : 0 < σ₂ := by linarith
  have hS1 : 1 ≤ σ₁ * σ₂ := by nlinarith
  have hS0 : 0 < σ₁ * σ₂ := by linarith
  have hA : 0 ≤ (P ^ cr) ^ 2 * Γ := mul_nonneg (sq_nonneg _) hΓ
  have hb₁ : l₁ ≤ (P ^ cr) ^ 2 * Γ * σ₁ ^ (8 * cr + a2 - dq) := by
    rw [hl₁]; exact rows_num_l hP hσ₁ h1₁ hh₁ hcr hΓ
  have hb₂ : l₂ ≤ (P ^ cr) ^ 2 * Γ * σ₂ ^ (8 * cr + a2 - dq) := by
    rw [hl₂]; exact rows_num_l hP hσ₂ h1₂ hh₂ hcr hΓ
  have hl₂0 : 0 ≤ l₂ := by
    rw [hl₂]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg hΓ (Real.rpow_nonneg hσ₂0.le _)))
      (Real.rpow_nonneg hσ₂0.le _)
  have hhalf : (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2) * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2)
      = σ₁ ^ (8 * cr + a2 - dq) * σ₂ ^ (8 * cr + a2 - dq) := by
    rw [← Real.rpow_add hS0, ← Real.mul_rpow hσ₁0.le hσ₂0.le]
    congr 1
    ring
  have hsq : Real.sqrt (l₁ * l₂) ≤ (P ^ cr) ^ 2 * Γ * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2) := by
    have hprod : l₁ * l₂ ≤ ((P ^ cr) ^ 2 * Γ * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2)) ^ 2 := by
      calc l₁ * l₂ ≤ ((P ^ cr) ^ 2 * Γ * σ₁ ^ (8 * cr + a2 - dq)) *
            ((P ^ cr) ^ 2 * Γ * σ₂ ^ (8 * cr + a2 - dq)) :=
            mul_le_mul hb₁ hb₂ hl₂0 (mul_nonneg hA (Real.rpow_nonneg hσ₁0.le _))
        _ = ((P ^ cr) ^ 2 * Γ) ^ 2 * (σ₁ ^ (8 * cr + a2 - dq) * σ₂ ^ (8 * cr + a2 - dq)) := by ring
        _ = ((P ^ cr) ^ 2 * Γ * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2)) ^ 2 := by rw [← hhalf]; ring
    calc Real.sqrt (l₁ * l₂)
        ≤ Real.sqrt (((P ^ cr) ^ 2 * Γ * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2)) ^ 2) :=
          Real.sqrt_le_sqrt hprod
      _ = (P ^ cr) ^ 2 * Γ * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2) :=
          Real.sqrt_sq (mul_nonneg hA (Real.rpow_nonneg hS0.le _))
  have hE : (h₁ * h₂) ^ E1 ≤ (P ^ E1) ^ 2 * (σ₁ * σ₂) ^ (4 * E1) := by
    have hprod : h₁ * h₂ ≤ P ^ 2 * (σ₁ * σ₂) ^ 4 := by
      calc h₁ * h₂ ≤ (P * σ₁ ^ 4) * (P * σ₂ ^ 4) :=
            mul_le_mul hh₁ hh₂ (by linarith) (mul_nonneg hP0.le (pow_nonneg hσ₁0.le 4))
        _ = P ^ 2 * (σ₁ * σ₂) ^ 4 := by ring
    calc (h₁ * h₂) ^ E1 ≤ (P ^ 2 * (σ₁ * σ₂) ^ 4) ^ E1 :=
          Real.rpow_le_rpow (mul_nonneg (by linarith) (by linarith)) hprod hE1
      _ = (P ^ 2) ^ E1 * ((σ₁ * σ₂) ^ 4) ^ E1 :=
          Real.mul_rpow (pow_nonneg hP0.le 2) (pow_nonneg hS0.le 4)
      _ = (P ^ E1) ^ 2 * (σ₁ * σ₂) ^ (4 * E1) := by
          rw [pow_rpow_eq_rpow_mul hS0.le, sq, sq, Real.mul_rpow hP0.le hP0.le]
          norm_num
  have hSck : 0 < (σ₁ * σ₂) ^ (4 * ck) := Real.rpow_pos_of_pos hS0 _
  have hXiP : 0 ≤ XiP := by
    by_contra hneg
    push_neg at hneg
    have := mul_neg_of_neg_of_pos hneg hSck
    linarith
  have hC : 0 ≤ XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) :=
    mul_nonneg hXiP (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hF6) hΓ)
  calc XiH * ((h₁ * h₂) ^ E1 * F6) * Real.sqrt (l₁ * l₂)
      ≤ (XiP * (σ₁ * σ₂) ^ (4 * ck)) * ((P ^ E1) ^ 2 * (σ₁ * σ₂) ^ (4 * E1) * F6) *
          ((P ^ cr) ^ 2 * Γ * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2)) := by
        refine mul_le_mul ?_ hsq (Real.sqrt_nonneg _) ?_
        · exact mul_le_mul hXi (mul_le_mul_of_nonneg_right hE hF6)
            (mul_nonneg (Real.rpow_nonneg (mul_nonneg (by linarith) (by linarith)) _) hF6)
            (mul_nonneg hXiP hSck.le)
        · exact mul_nonneg (mul_nonneg hXiP hSck.le)
            (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hS0.le _)) hF6)
    _ = XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) *
          ((σ₁ * σ₂) ^ (4 * ck) * (σ₁ * σ₂) ^ (4 * E1) * (σ₁ * σ₂) ^ ((8 * cr + a2 - dq) / 2)) := by
        ring
    _ = XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) *
          (σ₁ * σ₂) ^ (4 * ck + 4 * E1 + (8 * cr + a2 - dq) / 2) := by
        rw [Real.rpow_add hS0, Real.rpow_add hS0]
    _ ≤ XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) * (σ₁ * σ₂) ^ (-e) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hS1 (by linarith)) hC
    _ = XiP * ((P ^ E1) ^ 2 * (P ^ cr) ^ 2 * F6 * Γ) * (σ₁ ^ (-e) * σ₂ ^ (-e)) := by
        rw [Real.mul_rpow hσ₁0.le hσ₂0.le]

end Formalism.MainNotions.BridgeLemma₂
end

section

namespace Formalism.MainNotions.BridgeLemma₂

theorem rpow_le_rpow_mul_rpow {P σ h c : ℝ} (hP : 1 ≤ P) (hσ : 1 ≤ σ) (h1 : 1 ≤ h) (hh : h ≤ P * σ ^ 4) (hc : 0 ≤ c) :
    h ^ c ≤ P ^ c * σ ^ (4 * c) := by
  have h0 : 0 ≤ h := by linarith
  have hσ0 : 0 ≤ σ := by linarith
  calc h ^ c ≤ (P * σ ^ 4) ^ c := Real.rpow_le_rpow h0 hh hc
    _ = P ^ c * (σ ^ 4) ^ c := Real.mul_rpow (by linarith) (by positivity)
    _ = P ^ c * σ ^ (4 * c) := by
      rw [← Real.rpow_natCast σ 4, ← Real.rpow_mul hσ0] <;> norm_num

private theorem le_of_sq_le_sq_of_nonneg' {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith [mul_self_nonneg (a - b)]

private theorem sq_le_pow_four_of_one_le {x : ℝ} (hx : 1 ≤ x) : x ^ 2 ≤ x ^ 4 := by
  have hx2 : 1 ≤ x ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hx2 (sq_nonneg x)]

private theorem rpow_product_le_rpow_neg_sq_with_a4 {σ cS c4 cV a2 a4 dq e : ℝ} (hσ : 1 ≤ σ) (hcS : 0 ≤ cS)
    (he : 4 * c4 + 4 * cS + 4 * cV + a2 / 2 + |a4| - dq / 2 ≤ -e) :
    σ ^ (4 * cS) * (σ ^ (4 * c4)) ^ 2 * (σ ^ (4 * cV)) ^ 2 * (σ ^ a2 * (σ ^ a4) ^ 2 * σ ^ (-dq)) ≤
      (σ ^ (-e)) ^ 2 := by
  have h0 : 0 < σ := by linarith
  have hsq : ∀ x : ℝ, (σ ^ x) ^ 2 = σ ^ (2 * x) := fun x => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le, mul_comm] <;> norm_num
  simp only [hsq, ← Real.rpow_add h0]
  apply Real.rpow_le_rpow_of_exponent_le hσ
  linarith [le_abs_self a4]

private theorem rpow_product_le_rpow_neg_sq {σ cS c4 cV a2 a4 dq e : ℝ} (hσ : 1 ≤ σ) (hcS : 0 ≤ cS)
    (he : 4 * c4 + 4 * cS + 4 * cV + a2 / 2 + |a4| - dq / 2 ≤ -e) :
    σ ^ (4 * cS) * (σ ^ (4 * c4)) ^ 2 * (σ ^ (4 * cV)) ^ 2 * (σ ^ a2 * σ ^ (-dq)) ≤
      (σ ^ (-e)) ^ 2 := by
  have h0 : 0 < σ := by linarith
  have hsq : ∀ x : ℝ, (σ ^ x) ^ 2 = σ ^ (2 * x) := fun x => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul h0.le, mul_comm] <;> norm_num
  simp only [hsq, ← Real.rpow_add h0]
  apply Real.rpow_le_rpow_of_exponent_le hσ
  linarith [abs_nonneg a4]



theorem mul_sqrt_div_mul_sqrt_div_le {P σ₁ σ₂ hS₁ hS₂ h4₁ h4₂ hV₁ hV₂ cS c4 cV Γ Ex a2 a4 dq τ Q n₁ n₂ K4 N L₁ L₂ e : ℝ}
    (hP : 1 ≤ P) (hσ₁ : 1 ≤ σ₁) (hσ₂ : 1 ≤ σ₂)
    (hS1₁ : 1 ≤ hS₁) (hS1₂ : 1 ≤ hS₂) (h41₁ : 1 ≤ h4₁) (h41₂ : 1 ≤ h4₂) (hV1₁ : 1 ≤ hV₁) (hV1₂ : 1 ≤ hV₂)
    (hSP₁ : hS₁ ≤ P * σ₁ ^ 4) (hSP₂ : hS₂ ≤ P * σ₂ ^ 4) (h4P₁ : h4₁ ≤ P * σ₁ ^ 4) (h4P₂ : h4₂ ≤ P * σ₂ ^ 4)
    (hVP₁ : hV₁ ≤ P * σ₁ ^ 4) (hVP₂ : hV₂ ≤ P * σ₂ ^ 4) (hcS : 0 ≤ cS) (hc4 : 0 ≤ c4) (hcV : 0 ≤ cV)
    (hΓ : 0 ≤ Γ) (hEx : 0 ≤ Ex) (hτ : 0 ≤ τ) (hQ : 0 ≤ Q) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hK4 : 0 ≤ K4)
    (hN₁ : N ≤ hS₁ ^ cS * n₁ * (K4 * (h4₁ * h4₂) ^ c4)) (hN₂ : N ≤ hS₂ ^ cS * n₂ * (K4 * (h4₂ * h4₁) ^ c4))
    (hL₁ : L₁ = (hV₁ ^ cV) ^ 2 * (Γ * σ₁ ^ a2) * (Ex * σ₁ ^ a4) ^ 2 * τ * Q * σ₁ ^ (-dq))
    (hL₂ : L₂ = (hV₂ ^ cV) ^ 2 * (Γ * σ₂ ^ a2) * σ₂ ^ (-dq) * τ)
    (he : 4 * c4 + 4 * cS + 4 * cV + a2 / 2 + |a4| - dq / 2 ≤ -e) :
    N * (Real.sqrt (L₁ / n₁) * Real.sqrt (L₂ / n₂)) ≤
      (K4 * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) * Γ * Ex * τ * Real.sqrt Q) * (σ₁ ^ (-e) * σ₂ ^ (-e)) := by
  have hσ₁0 : 0 < σ₁ := by linarith
  have hσ₂0 : 0 < σ₂ := by linarith
  have hS0₁ : 0 < hS₁ := by linarith
  have hS0₂ : 0 < hS₂ := by linarith
  have h40₁ : 0 < h4₁ := by linarith
  have h40₂ : 0 < h4₂ := by linarith
  have hV0₁ : 0 < hV₁ := by linarith
  have hV0₂ : 0 < hV₂ := by linarith
  have hP0 : 0 < P := by linarith
  have hL0₁ : 0 ≤ L₁ := by rw [hL₁]; positivity
  have hL0₂ : 0 ≤ L₂ := by rw [hL₂]; positivity
  have hs0 : 0 ≤ Real.sqrt (L₁ / n₁) * Real.sqrt (L₂ / n₂) := by positivity
  have hR0 : 0 ≤ (K4 * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) * Γ * Ex * τ * Real.sqrt Q) *
      (σ₁ ^ (-e) * σ₂ ^ (-e)) := by positivity
  by_cases hN : N ≤ 0
  · have h1 : 0 ≤ (-N) * (Real.sqrt (L₁ / n₁) * Real.sqrt (L₂ / n₂)) := mul_nonneg (by linarith) hs0
    linarith
  push_neg at hN
  apply le_of_sq_le_sq_of_nonneg' hR0
  have hlhs : (N * (Real.sqrt (L₁ / n₁) * Real.sqrt (L₂ / n₂))) ^ 2 = N ^ 2 * (L₁ / n₁ * (L₂ / n₂)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (div_nonneg hL0₁ hn₁.le), Real.sq_sqrt (div_nonneg hL0₂ hn₂.le)]
  have hrhs : ((K4 * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) * Γ * Ex * τ * Real.sqrt Q) *
      (σ₁ ^ (-e) * σ₂ ^ (-e))) ^ 2 = K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q *
      ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 * ((σ₁ ^ (-e)) ^ 2 * (σ₂ ^ (-e)) ^ 2) := by
    have hq := Real.sq_sqrt hQ
    linear_combination (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 *
      ((σ₁ ^ (-e)) ^ 2 * (σ₂ ^ (-e)) ^ 2)) * hq
  rw [hlhs, hrhs]
  have e1 : n₁ * (L₁ / n₁) = L₁ := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hn₁.ne', mul_one]
  have e2 : n₂ * (L₂ / n₂) = L₂ := by
    rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hn₂.ne', mul_one]
  have hN2 : N ^ 2 ≤ (hS₁ ^ cS * n₁ * (K4 * (h4₁ * h4₂) ^ c4)) * (hS₂ ^ cS * n₂ * (K4 * (h4₂ * h4₁) ^ c4)) := by
    rw [sq]; exact mul_le_mul hN₁ hN₂ hN.le (by positivity)
  have b1 := rpow_le_rpow_mul_rpow hP hσ₁ hS1₁ hSP₁ hcS
  have b2 := rpow_le_rpow_mul_rpow hP hσ₂ hS1₂ hSP₂ hcS
  have b3 := rpow_le_rpow_mul_rpow hP hσ₁ h41₁ h4P₁ hc4
  have b4 := rpow_le_rpow_mul_rpow hP hσ₂ h41₂ h4P₂ hc4
  have b5 := rpow_le_rpow_mul_rpow hP hσ₁ hV1₁ hVP₁ hcV
  have b6 := rpow_le_rpow_mul_rpow hP hσ₂ hV1₂ hVP₂ hcV
  have hPp : (P ^ cS) ^ 2 * (P ^ c4) ^ 4 * (P ^ cV) ^ 4 ≤ ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 := by
    have hx : 1 ≤ P ^ cS := Real.one_le_rpow hP hcS
    have h2 : (P ^ cS) ^ 2 ≤ (P ^ cS) ^ 4 := sq_le_pow_four_of_one_le hx
    calc (P ^ cS) ^ 2 * (P ^ c4) ^ 4 * (P ^ cV) ^ 4 ≤ (P ^ cS) ^ 4 * (P ^ c4) ^ 4 * (P ^ cV) ^ 4 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (by positivity)) (by positivity)
      _ = ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 := by ring
  have hσ1b := rpow_product_le_rpow_neg_sq_with_a4 hσ₁ hcS he
  have hσ2b := rpow_product_le_rpow_neg_sq hσ₂ hcS he
  calc N ^ 2 * (L₁ / n₁ * (L₂ / n₂))
      ≤ ((hS₁ ^ cS * n₁ * (K4 * (h4₁ * h4₂) ^ c4)) * (hS₂ ^ cS * n₂ * (K4 * (h4₂ * h4₁) ^ c4))) *
          (L₁ / n₁ * (L₂ / n₂)) := mul_le_mul_of_nonneg_right hN2 (by positivity)
    _ = K4 ^ 2 * (hS₁ ^ cS * hS₂ ^ cS) * (h4₁ ^ c4 * h4₂ ^ c4) ^ 2 * (n₁ * (L₁ / n₁)) *
          (n₂ * (L₂ / n₂)) := by
        rw [mul_comm h4₂ h4₁, Real.mul_rpow h40₁.le h40₂.le]; ring
    _ = K4 ^ 2 * (hS₁ ^ cS * hS₂ ^ cS) * (h4₁ ^ c4 * h4₂ ^ c4) ^ 2 * L₁ * L₂ := by rw [e1, e2]
    _ = (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q) * ((hS₁ ^ cS * hS₂ ^ cS) * (h4₁ ^ c4 * h4₂ ^ c4) ^ 2 *
          (hV₁ ^ cV) ^ 2 * (hV₂ ^ cV) ^ 2 * (σ₁ ^ a2 * (σ₁ ^ a4) ^ 2 * σ₁ ^ (-dq)) *
          (σ₂ ^ a2 * σ₂ ^ (-dq))) := by
        rw [hL₁, hL₂]; ring
    _ ≤ (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q) * (((P ^ cS * σ₁ ^ (4 * cS)) * (P ^ cS * σ₂ ^ (4 * cS))) *
          ((P ^ c4 * σ₁ ^ (4 * c4)) * (P ^ c4 * σ₂ ^ (4 * c4))) ^ 2 *
          (P ^ cV * σ₁ ^ (4 * cV)) ^ 2 * (P ^ cV * σ₂ ^ (4 * cV)) ^ 2 *
          (σ₁ ^ a2 * (σ₁ ^ a4) ^ 2 * σ₁ ^ (-dq)) * (σ₂ ^ a2 * σ₂ ^ (-dq))) := by
        gcongr
    _ = (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q) * (((P ^ cS) ^ 2 * (P ^ c4) ^ 4 * (P ^ cV) ^ 4) *
          (σ₁ ^ (4 * cS) * (σ₁ ^ (4 * c4)) ^ 2 * (σ₁ ^ (4 * cV)) ^ 2 * (σ₁ ^ a2 * (σ₁ ^ a4) ^ 2 * σ₁ ^ (-dq))) *
          (σ₂ ^ (4 * cS) * (σ₂ ^ (4 * c4)) ^ 2 * (σ₂ ^ (4 * cV)) ^ 2 * (σ₂ ^ a2 * σ₂ ^ (-dq)))) := by
        ring
    _ ≤ (K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q) * (((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 *
          (σ₁ ^ (-e)) ^ 2 * (σ₂ ^ (-e)) ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (mul_le_mul hPp hσ1b (by positivity) (by positivity)) hσ2b (by positivity)
          (by positivity)
    _ = K4 ^ 2 * Γ ^ 2 * Ex ^ 2 * τ ^ 2 * Q * ((P ^ c4) ^ 2 * (P ^ cS) ^ 2 * (P ^ cV) ^ 2) ^ 2 *
          ((σ₁ ^ (-e)) ^ 2 * (σ₂ ^ (-e)) ^ 2) := by ring

end Formalism.MainNotions.BridgeLemma₂
end
