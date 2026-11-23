module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle002
public import Formalism.PeriodIntegrals.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LocalAbstract
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace PI.EF

theorem localAbstract_of (hDF : PI.DiscFactor) (hDL : PI.DiscLog) : LocalAbstract := by
  intro r R' R hr hrR' hR'R
  exact ⟨Loc.locC r R' R, Loc.locC_pos hr hrR' hR'R, fun f s₀ M hf hf0 hM hb =>
    Loc.local_abstract hDF hDL hr hrR' hR'R f s₀ M hf hf0 hM hb⟩

end PI.EF
end

section

noncomputable section

namespace PI.EF

open Complex Filter Topology Set DirichletCharacter

lemma isCompact_rect (x₀ x₁ y₀ y₁ : ℝ) : IsCompact (rect x₀ x₁ y₀ y₁) :=
  isCompact_Icc.reProdIm isCompact_Icc

lemma mem_rect {x₀ x₁ y₀ y₁ : ℝ} {s : ℂ} :
    s ∈ rect x₀ x₁ y₀ y₁ ↔ (x₀ ≤ s.re ∧ s.re ≤ x₁) ∧ (y₀ ≤ s.im ∧ s.im ≤ y₁) := by
  simp only [rect, Complex.mem_reProdIm, Set.mem_Icc]

variable {N : ℕ} [NeZero N]

def Lent (χ : DirichletCharacter ℂ N) : ℂ → ℂ :=
  open Classical in if χ = 1 then LFunctionTrivChar₁ N else LFunction χ

lemma differentiable_Lent (χ : DirichletCharacter ℂ N) : Differentiable ℂ (Lent χ) := by
  unfold Lent
  split_ifs with h
  · exact differentiable_LFunctionTrivChar₁ N
  · exact differentiable_LFunction h

lemma Lent_of_ne {χ : DirichletCharacter ℂ N} (h : χ ≠ 1) : Lent χ = LFunction χ := by
  unfold Lent
  rw [if_neg h]

lemma Lent_one_apply {χ : DirichletCharacter ℂ N} (h : χ = 1) {s : ℂ} (hs : s ≠ 1) :
    Lent χ s = (s - 1) * LFunction χ s := by
  subst h
  unfold Lent
  rw [if_pos rfl]
  first
    | (rw [LFunctionTrivChar₁, Function.update_of_ne hs]; rfl)
    | (simp [LFunctionTrivChar₁, Function.update_of_ne hs])
    | (simp [LFunctionTrivChar₁, hs])

lemma Lent_two_ne_zero (χ : DirichletCharacter ℂ N) : Lent χ 2 ≠ 0 := by
  have h2 : (2 : ℂ) ≠ 1 := by norm_num
  have hL : LFunction χ 2 ≠ 0 := LFunction_ne_zero_of_one_le_re χ (Or.inr h2) (by norm_num)
  by_cases h : χ = 1
  · rw [Lent_one_apply h h2]
    exact mul_ne_zero (sub_ne_zero.mpr h2) hL
  · rw [Lent_of_ne h]
    exact hL

lemma Lent_one_ne_zero (χ : DirichletCharacter ℂ N) : Lent χ 1 ≠ 0 := by
  by_cases h : χ = 1
  · unfold Lent
    rw [if_pos h]
    exact LFunctionTrivChar₁_apply_one_ne_zero N
  · rw [Lent_of_ne h]
    exact LFunction_ne_zero_of_one_le_re χ (Or.inl h) (by simp)

lemma Lent_eq_zero_iff (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    Lent χ s = 0 ↔ LFunction χ s = 0 := by
  by_cases h : χ = 1
  · rw [Lent_one_apply h hs, mul_eq_zero]
    simp [sub_eq_zero, hs]
  · rw [Lent_of_ne h]

lemma Lent_eventuallyEq {χ : DirichletCharacter ℂ N} (h : χ = 1) {s : ℂ} (hs : s ≠ 1) :
    Lent χ =ᶠ[𝓝 s] (fun z => z - 1) * LFunction χ := by
  filter_upwards [isOpen_ne.mem_nhds hs] with z hz
  rw [Lent_one_apply h hz]
  rfl

lemma order_Lent (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) :
    analyticOrderNatAt (Lent χ) s = analyticOrderNatAt (LFunction χ) s := by
  by_cases h : χ = 1
  · have hL : AnalyticAt ℂ (LFunction χ) s := by
      apply DifferentiableOn.analyticAt (s := {z | z ≠ 1})
      · intro z hz
        exact (differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
      · exact isOpen_ne.mem_nhds hs
    have h1 : AnalyticAt ℂ (fun z : ℂ => z - 1) s := analyticAt_id.sub analyticAt_const
    have h0 : analyticOrderAt (fun z : ℂ => z - 1) s = 0 :=
      h1.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hs)
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr (Lent_eventuallyEq h hs), analyticOrderAt_mul h1 hL, h0, zero_add]
  · rw [Lent_of_ne h]

lemma logDeriv_Lent (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : s ≠ 1) (h0 : LFunction χ s ≠ 0) :
    logDeriv (LFunction χ) s = logDeriv (Lent χ) s - del1 χ / (s - 1) := by
  by_cases h : χ = 1
  · have hd : DifferentiableAt ℂ (LFunction χ) s := differentiableAt_LFunction χ s (Or.inl hs)
    have he := Lent_eventuallyEq h hs
    have h1 : logDeriv (Lent χ) s = logDeriv (fun z => (z - 1) * LFunction χ z) s := by
      unfold logDeriv
      simp only [Pi.div_apply]
      rw [he.deriv_eq, he.eq_of_nhds]
      rfl
    have h2 : logDeriv (fun z : ℂ => z - 1) s = 1 / (s - 1) := by
      simp [logDeriv_apply]
    have hdz : DifferentiableAt ℂ (fun z : ℂ => z - 1) s := differentiableAt_id.sub_const (1 : ℂ)
    rw [h1, logDeriv_fun_mul (f := fun z : ℂ => z - 1) (g := LFunction χ) s
      (sub_ne_zero.mpr hs) h0 hdz hd, h2]
    simp only [del1, if_pos h]
    ring
  · rw [Lent_of_ne h]
    simp [del1, h]

theorem zerosFinite : ZerosFinite := by
  intro N _ χ hχ T
  have h := finite_zeros_of_compact (differentiable_Lent χ) (Lent_two_ne_zero χ)
    (isCompact_rect 0 1 (-T) T)
  refine h.subset ?_
  intro ρ hρ
  obtain ⟨hre0, hre1, him, hL⟩ := hρ
  have h1 : ρ ≠ 1 := fun e => by rw [e] at hre1; simp at hre1
  refine ⟨mem_rect.mpr ⟨⟨hre0.le, hre1.le⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · linarith [neg_abs_le ρ.im]
  · linarith [le_abs_self ρ.im]
  · exact (Lent_eq_zero_iff χ h1).mpr hL

theorem regularPart : RegularPart := by
  intro N _ χ hχ x₁ T' hx₁ hT' hNO
  classical
  have hSfin : (ZerosBelow χ T').Finite := zerosFinite N χ hχ T'

  obtain ⟨E0, hE0⟩ : ∃ E0 : Finset ℂ, E0 = if χ.Even ∧ χ ≠ 1 then {0} else ∅ := ⟨_, rfl⟩
  have hE0mem : ∀ ρ, ρ ∈ E0 ↔ ρ = 0 ∧ χ.Even ∧ χ ≠ 1 := by
    intro ρ
    rw [hE0]
    by_cases he : χ.Even ∧ χ ≠ 1
    · rw [if_pos he, Finset.mem_singleton]
      exact ⟨fun h => ⟨h, he⟩, fun h => h.1⟩
    · rw [if_neg he]
      simp only [Finset.notMem_empty, false_iff]
      exact fun h => he h.2
  have hre1 : ∀ ρ ∈ ZerosBelow χ T', ρ ≠ 1 := by
    intro ρ hρ e
    have h := hρ.2.1
    rw [e] at h
    simp at h
  have hZ0 : ∀ ρ ∈ hSfin.toFinset ∪ E0, Lent χ ρ = 0 := by
    intro ρ hρ
    rcases Finset.mem_union.mp hρ with h | h
    · have h' := hSfin.mem_toFinset.mp h
      exact (Lent_eq_zero_iff χ (hre1 ρ h')).mpr h'.2.2.2
    · obtain ⟨rfl, he, h1⟩ := (hE0mem ρ).mp h
      exact (Lent_eq_zero_iff χ zero_ne_one).mpr (mult_zero_of_even hχ he h1).1
  have hK : ∀ s ∈ rect (-1 / 2) x₁ (-T') T', Lent χ s = 0 → s ∈ hSfin.toFinset ∪ E0 := by
    intro s hs hz
    have hs1 : s ≠ 1 := fun e => Lent_one_ne_zero χ (e ▸ hz)
    have hL : LFunction χ s = 0 := (Lent_eq_zero_iff χ hs1).mp hz
    obtain ⟨⟨hsre0, hsre1⟩, him0, him1⟩ := mem_rect.mp hs
    rcases zeroLocus N χ hχ s (by linarith) hs1 hL with h | h | h
    · apply Finset.mem_union_left
      rw [hSfin.mem_toFinset]
      refine ⟨h.1, h.2, ?_, hL⟩
      have hle : |s.im| ≤ T' := abs_le.mpr ⟨him0, him1⟩
      exact lt_of_le_of_ne hle (hNO s h.1 h.2 hL)
    · exact Finset.mem_union_right _ ((hE0mem s).mpr h)
    · exfalso
      rw [h.1] at hsre0
      norm_num at hsre0
  have hf : AnalyticOnNhd ℂ (Lent χ) (rect (-1 / 2) x₁ (-T') T') := fun x _ =>
    (differentiable_Lent χ).analyticAt x
  have hfin : ∀ ρ ∈ rect (-1 / 2) x₁ (-T') T', analyticOrderAt (Lent χ) ρ ≠ ⊤ := fun ρ _ =>
    order_ne_top_of_entire (differentiable_Lent χ) (Lent_two_ne_zero χ) ρ
  obtain ⟨H, hH, hHeq⟩ := exists_regular_part hf (hSfin.toFinset ∪ E0) hZ0 hK hfin
  refine ⟨H, hH.differentiableOn, ?_⟩
  intro s hs hL0 hs1
  have hLe : Lent χ s ≠ 0 := fun e => hL0 ((Lent_eq_zero_iff χ hs1).mp e)
  have hdisj : Disjoint hSfin.toFinset E0 := by
    rw [Finset.disjoint_left]
    intro ρ h1 h2
    have h1' := (hSfin.mem_toFinset.mp h1).1
    rw [((hE0mem ρ).mp h2).1] at h1'
    simp at h1'
  have hS : ∑ ρ ∈ hSfin.toFinset, (analyticOrderNatAt (Lent χ) ρ : ℂ) / (s - ρ) =
      ∑ ρ ∈ hSfin.toFinset, (mult χ ρ : ℂ) / (s - ρ) := by
    refine Finset.sum_congr rfl fun ρ hρ => ?_
    rw [order_Lent χ (hre1 ρ (hSfin.mem_toFinset.mp hρ))]
  have hE : ∑ ρ ∈ E0, (analyticOrderNatAt (Lent χ) ρ : ℂ) / (s - ρ) = eps0 χ / s := by
    rw [hE0]
    by_cases he : χ.Even ∧ χ ≠ 1
    · rw [if_pos he, Finset.sum_singleton, order_Lent χ zero_ne_one,
        (mult_zero_of_even hχ he.1 he.2).2]
      simp only [eps0, if_pos he]
      simp
    · rw [if_neg he]
      simp only [eps0, if_neg he]
      simp
  rw [logDeriv_Lent χ hs1 hL0, hHeq s hs hLe, Finset.sum_union hdisj,
    finsum_mem_eq_finite_toFinset_sum _ hSfin, hS, hE]
  ring

end PI.EF
end
end

section

noncomputable section

namespace PI.EF

open Complex Filter Topology Set DirichletCharacter

lemma mem_rect_iff {x₀ x₁ y₀ y₁ : ℝ} {s : ℂ} :
    s ∈ rect x₀ x₁ y₀ y₁ ↔ (x₀ ≤ s.re ∧ s.re ≤ x₁) ∧ (y₀ ≤ s.im ∧ s.im ≤ y₁) := by
  rw [rect, Complex.mem_reProdIm]
  simp only [Set.mem_Icc]

lemma rectInt_congr_sides {f g : ℂ → ℂ} {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (h : ∀ s ∈ rect x₀ x₁ y₀ y₁, (s.re = x₀ ∨ s.re = x₁ ∨ s.im = y₀ ∨ s.im = y₁) → f s = g s) :
    rectInt f x₀ x₁ y₀ y₁ = rectInt g x₀ x₁ y₀ y₁ := by
  have hre : ∀ a b : ℝ, ((a : ℂ) + b * I).re = a := fun a b => by simp
  have him : ∀ a b : ℝ, ((a : ℂ) + b * I).im = b := fun a b => by simp
  have hxI := Set.uIcc_of_le hx
  have hyI := Set.uIcc_of_le hy
  have e1 : ∀ y : ℝ, y₀ ≤ y → y ≤ y₁ → (y = y₀ ∨ y = y₁) →
      (∫ x : ℝ in x₀..x₁, f (x + y * I)) = ∫ x : ℝ in x₀..x₁, g (x + y * I) := by
    intro y hy0 hy1 hyy
    refine intervalIntegral.integral_congr fun x hxm => ?_
    rw [hxI] at hxm
    apply h
    · rw [mem_rect_iff, hre, him]
      exact ⟨hxm, hy0, hy1⟩
    · rw [hre, him]
      rcases hyy with e | e
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr e))
  have e2 : ∀ x : ℝ, x₀ ≤ x → x ≤ x₁ → (x = x₀ ∨ x = x₁) →
      (∫ y : ℝ in y₀..y₁, f (x + y * I)) = ∫ y : ℝ in y₀..y₁, g (x + y * I) := by
    intro x hx0 hx1 hxx
    refine intervalIntegral.integral_congr fun y hym => ?_
    rw [hyI] at hym
    apply h
    · rw [mem_rect_iff, hre, him]
      exact ⟨⟨hx0, hx1⟩, hym⟩
    · rw [hre, him]
      rcases hxx with e | e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
  unfold rectInt
  rw [e1 y₀ le_rfl hy (Or.inl rfl), e1 y₁ hy le_rfl (Or.inr rfl), e2 x₁ hx le_rfl (Or.inr rfl),
    e2 x₀ le_rfl hx (Or.inl rfl)]

theorem glueContour : GlueContour := by
  intro hR hZ hF N _ χ hχ u T' H hu hT hno hreg
  have hlog : 0 < Real.log u := Real.log_pos (by linarith)
  have hc : 1 < cLine u := by
    unfold cLine
    have := one_div_pos.2 hlog
    linarith
  have hfin := hF N χ hχ T'
  set S := hfin.toFinset with hS
  have hmemS : ∀ ρ, ρ ∈ S ↔ ρ ∈ ZerosBelow χ T' := fun ρ => hfin.mem_toFinset
  have h1S : (1 : ℂ) ∉ S := by
    rw [hmemS]
    intro h
    have := h.2.1
    simp at this
  set Z := insert (1 : ℂ) S with hZdef
  set wt : ℂ → ℂ := fun ρ => if ρ = 1 then -del1 χ else (mult χ ρ : ℂ) with hwt
  have hfs : ∀ g : ℂ → ℂ, (∑ᶠ ρ ∈ ZerosBelow χ T', g ρ) = ∑ ρ ∈ S, g ρ := fun g =>
    finsum_mem_eq_finite_toFinset_sum g hfin

  have hsumZ : ∀ F : ℂ → ℂ → ℂ, ∑ ρ ∈ Z, F (wt ρ) ρ = F (-del1 χ) 1 + ∑ ρ ∈ S, F (mult χ ρ) ρ := by
    intro F
    rw [hZdef, Finset.sum_insert h1S]
    congr 1
    · simp [hwt]
    · refine Finset.sum_congr rfl fun ρ hρ => ?_
      have : ρ ≠ 1 := fun e => h1S (e ▸ hρ)
      simp [hwt, this]

  have hbd : rectInt (fun s => logDeriv (DirichletCharacter.LFunction χ) s * ((u : ℂ) ^ s / s))
        (-1 / 2) (cLine u) (-T') T' =
      rectInt (fun s => (H s + (∑ ρ ∈ Z, wt ρ / (s - ρ)) + eps0 χ / s) * ((u : ℂ) ^ s / s))
        (-1 / 2) (cLine u) (-T') T' := by
    apply rectInt_congr_sides (by linarith) (by linarith)
    intro s hs hside
    have hs' := mem_rect_iff.1 hs
    have hs1 : s ≠ 1 := by
      intro e
      have r1 : s.re = 1 := by rw [e]; simp
      have i1 : s.im = 0 := by rw [e]; simp
      rcases hside with e' | e' | e' | e' <;> linarith
    have hL : DirichletCharacter.LFunction χ s ≠ 0 := by
      intro h0
      rcases hZ N χ hχ s (by linarith [hs'.1.1]) hs1 h0 with h | ⟨h, -⟩ | ⟨h, -⟩
      · rcases hside with e | e | e | e
        · linarith [h.1]
        · linarith [h.2]
        · exact hno s h.1 h.2 h0 (by rw [e, abs_neg, abs_of_pos (by linarith)])
        · exact hno s h.1 h.2 h0 (by rw [e, abs_of_pos (by linarith)])
      · have r1 : s.re = 0 := by rw [h]; simp
        have i1 : s.im = 0 := by rw [h]; simp
        rcases hside with e' | e' | e' | e' <;> linarith
      · have r1 : s.re = -1 := by rw [h]; simp
        have i1 : s.im = 0 := by rw [h]; simp
        rcases hside with e' | e' | e' | e' <;> linarith
    rw [hreg.2 s hs hL hs1, hfs]
    have := hsumZ (fun w ρ => w / (s - ρ))
    rw [this]
    ring
  rw [hbd, hR (-1 / 2) (cLine u) (-T') T' H Z wt (eps0 χ) u (by linarith) (by norm_num) (by linarith)
    (by linarith) (by linarith) hreg.1 ?_]
  · have := hsumZ (fun w ρ => w * (((u : ℂ) ^ ρ - 1) / ρ))
    rw [this, zsum, hfs, hfs, Complex.cpow_one]
    have e : ∑ ρ ∈ S, (mult χ ρ : ℂ) * (((u : ℂ) ^ ρ - 1) / ρ) =
        ∑ ρ ∈ S, (mult χ ρ : ℂ) * ((u : ℂ) ^ ρ / ρ) - ∑ ρ ∈ S, (mult χ ρ : ℂ) / ρ := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun ρ _ => by ring
    rw [e]
    ring
  · intro ρ hρ
    rw [hZdef, Finset.mem_insert] at hρ
    rcases hρ with e | hρ
    · subst e
      simp only [Complex.one_re, Complex.one_im]
      exact ⟨one_ne_zero, by norm_num, hc, by linarith, by linarith⟩
    · obtain ⟨h0, h1, him, -⟩ := (hmemS ρ).1 hρ
      rw [abs_lt] at him
      refine ⟨fun e => by rw [e] at h0; simp at h0, by linarith, by linarith, him.1, him.2⟩

end PI.EF
end
end
