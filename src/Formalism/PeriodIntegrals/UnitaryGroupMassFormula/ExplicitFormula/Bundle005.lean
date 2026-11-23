module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Bundle002
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
public import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LucasLehmer
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
import Mathlib.Tactic.Lemma
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

namespace PI.EF

open Complex DirichletCharacter Filter Topology

theorem regAtZero_of {Cw Cl : ℝ} (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) :
    RegAtZero (Cw + Cl) := by
  intro N _ χ hχ x₁ T' H hx₁ hT' hH
  classical
  obtain ⟨hZ0, hZ0sum⟩ := hW N χ hχ 0
  have hlog : Real.log (N * (|(0:ℝ)| + 2)) = Real.log (2 * N) := by
    rw [abs_zero, zero_add, mul_comm]
  have hne0 : ∀ ρ ∈ ZerosNear χ 0, ρ ≠ 0 := by
    rintro ρ hρ rfl
    have := hρ.1
    simp at this
  have hB : (ZerosBelow χ T').Finite := by
    refine ((Finset.Icc ⌊-T'⌋ ⌊T'⌋).finite_toSet.biUnion
      (fun k _ => (hW N χ hχ (k : ℝ)).1)).subset ?_
    intro ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hρ
    rw [abs_lt] at h3
    refine Set.mem_iUnion₂.mpr ⟨⌊ρ.im⌋, ?_, h1, h2, ?_, h4⟩
    · rw [Finset.mem_coe, Finset.mem_Icc]
      exact ⟨Int.floor_mono h3.1.le, Int.floor_mono h3.2.le⟩
    · rw [abs_le]
      constructor <;> linarith [Int.floor_le ρ.im, Int.lt_floor_add_one ρ.im]
  have hneB : ∀ ρ ∈ ZerosBelow χ T', ρ ≠ 0 := by
    rintro ρ hρ rfl
    have := hρ.1
    simp at this
  have hofR : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Complex.continuous_ofReal.tendsto (0:ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using h
  have h0rect : (0 : ℂ) ∈ rect (-1 / 2) x₁ (-T') T' := by
    show (0 : ℂ) ∈ Set.Icc (-1 / 2 : ℝ) x₁ ×ℂ Set.Icc (-T') T'
    rw [Complex.mem_reProdIm]
    simp only [Complex.zero_re, Complex.zero_im, Set.mem_Icc]
    constructor <;> constructor <;> linarith
  have hrect : ∀ ε : ℝ, 0 < ε → ε < 1 / 2 → (ε : ℂ) ∈ rect (-1 / 2) x₁ (-T') T' := by
    intro ε h1 h2
    show (ε : ℂ) ∈ Set.Icc (-1 / 2 : ℝ) x₁ ×ℂ Set.Icc (-T') T'
    rw [Complex.mem_reProdIm]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Set.mem_Icc]
    constructor <;> constructor <;> linarith
  have hHt : Tendsto (fun ε : ℝ => ‖H ε - H 0‖) (𝓝[>] 0) (𝓝 0) := by
    have hc : ContinuousWithinAt H (rect (-1 / 2) x₁ (-T') T') 0 :=
      hH.1.continuousOn.continuousWithinAt h0rect
    have hr : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝[rect (-1 / 2) x₁ (-T') T'] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨hofR, ?_⟩
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 / 2 by norm_num)] with ε hε
      exact hrect ε hε.1 hε.2
    have := ((hc.tendsto.comp hr).sub_const (H 0)).norm
    simpa using this
  have hevZ : ∀ᶠ ε : ℝ in 𝓝[>] 0, (ε : ℂ) ∉ ZerosNear χ 0 := by
    have hc : (ZerosNear χ 0)ᶜ ∈ 𝓝 (0 : ℂ) :=
      hZ0.isClosed.isOpen_compl.mem_nhds (fun h => hne0 0 h rfl)
    exact hofR.eventually_mem hc
  have hpt : ∀ᶠ ε : ℝ in 𝓝[>] 0,
      ‖(∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) - H 0‖ ≤
        ‖H ε - H 0‖ + ‖(∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) +
          ∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ((ε : ℂ) - ρ)‖ +
          Cl * Real.log (2 * N) + ‖∑ᶠ ρ ∈ ZerosNear χ 0, (mult χ ρ : ℂ) / ((ε : ℂ) - ρ)‖ := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 / 2 by norm_num), hevZ] with ε hε hεZ
    obtain ⟨hε0, hε1⟩ := hε
    have hLε : DirichletCharacter.LFunction χ ε ≠ 0 := by
      intro h
      apply hεZ
      refine ⟨?_, ?_, ?_, h⟩
      · simpa using hε0
      · simp only [Complex.ofReal_re]; linarith
      · simp
    have hε1' : (ε : ℂ) ≠ 1 := by
      intro h
      have := congrArg Complex.re h
      simp only [Complex.ofReal_re, Complex.one_re] at this
      linarith
    have hreg := hH.2 ε (hrect ε hε0 hε1) hLε hε1'
    have hloc := hL N χ hχ ε (by simp only [Complex.ofReal_re]; linarith)
      (by simp only [Complex.ofReal_re]; linarith) hLε hε1'
    simp only [Complex.ofReal_im] at hloc
    rw [hlog] at hloc
    have key : (∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) - H 0 =
        (H ε - H 0) + ((∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) +
          ∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ((ε : ℂ) - ρ)) -
        (logDeriv (DirichletCharacter.LFunction χ) ε -
          (∑ᶠ ρ ∈ ZerosNear χ 0, (mult χ ρ : ℂ) / ((ε : ℂ) - ρ)) - eps0 χ / ε +
            del1 χ / (ε - 1)) -
        ∑ᶠ ρ ∈ ZerosNear χ 0, (mult χ ρ : ℂ) / ((ε : ℂ) - ρ) := by
      rw [hreg]; ring
    rw [key]
    have h4 : ∀ a b c d : ℂ, ‖a + b - c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := fun a b c d =>
      calc ‖a + b - c - d‖ ≤ ‖a + b - c‖ + ‖d‖ := norm_sub_le _ _
        _ ≤ ‖a + b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_sub_le _ _
        _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by gcongr; exact norm_add_le _ _
    refine (h4 _ _ _ _).trans ?_
    linarith [hloc]
  have hPt : Tendsto (fun ε : ℝ => ‖(∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ρ) +
      ∑ᶠ ρ ∈ ZerosBelow χ T', (mult χ ρ : ℂ) / ((ε : ℂ) - ρ)‖) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => ∑ ρ ∈ hB.toFinset,
        ((mult χ ρ : ℂ) / ρ + (mult χ ρ : ℂ) / ((ε : ℂ) - ρ))) (𝓝[>] 0)
        (𝓝 (∑ ρ ∈ hB.toFinset, ((mult χ ρ : ℂ) / ρ + (mult χ ρ : ℂ) / (0 - ρ)))) :=
      tendsto_finsetSum _ fun ρ hρ => tendsto_const_nhds.add
        (tendsto_const_nhds.div (hofR.sub_const ρ) (by
          rw [zero_sub, neg_ne_zero]; exact hneB ρ (by simpa using hρ)))
    have h0 : (∑ ρ ∈ hB.toFinset, ((mult χ ρ : ℂ) / ρ + (mult χ ρ : ℂ) / (0 - ρ))) = 0 :=
      Finset.sum_eq_zero fun ρ _ => by rw [zero_sub, div_neg, add_neg_cancel]
    rw [h0] at h
    have := h.norm
    rw [norm_zero] at this
    refine this.congr fun ε => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ hB, finsum_mem_eq_finite_toFinset_sum _ hB,
      Finset.sum_add_distrib]
  have hQt : Tendsto (fun ε : ℝ => ‖∑ᶠ ρ ∈ ZerosNear χ 0, (mult χ ρ : ℂ) / ((ε : ℂ) - ρ)‖)
      (𝓝[>] 0) (𝓝 ‖∑ ρ ∈ hZ0.toFinset, (mult χ ρ : ℂ) / (0 - ρ)‖) := by
    have h : Tendsto (fun ε : ℝ => ∑ ρ ∈ hZ0.toFinset, (mult χ ρ : ℂ) / ((ε : ℂ) - ρ))
        (𝓝[>] 0) (𝓝 (∑ ρ ∈ hZ0.toFinset, (mult χ ρ : ℂ) / (0 - ρ))) :=
      tendsto_finsetSum _ fun ρ hρ => tendsto_const_nhds.div (hofR.sub_const ρ) (by
        rw [zero_sub, neg_ne_zero]; exact hne0 ρ (by simpa using hρ))
    refine h.norm.congr fun ε => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ hZ0]
  have hlim := ((hHt.add hPt).add
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => Cl * Real.log (2 * N)) (𝓝[>] 0) _)).add hQt
  have hmain := ge_of_tendsto hlim hpt
  have hB1 : ZerosBelow χ 1 ⊆ ZerosNear χ 0 := by
    rintro ρ ⟨h1, h2, h3, h4⟩
    exact ⟨h1, h2, by rw [sub_zero]; exact h3.le, h4⟩
  have hB1f : (ZerosBelow χ 1).Finite := hZ0.subset hB1
  have hQ0 : ‖∑ ρ ∈ hZ0.toFinset, (mult χ ρ : ℂ) / (0 - ρ)‖ ≤
      S1 χ + Cw * Real.log (2 * N) := by
    refine (norm_sum_le _ _).trans ?_
    have hn : ∀ ρ, ‖(mult χ ρ : ℂ) / (0 - ρ)‖ = (mult χ ρ : ℝ) / ‖ρ‖ := fun ρ => by
      rw [norm_div, zero_sub, norm_neg, Complex.norm_natCast]
    simp only [hn]
    rw [← Finset.sum_filter_add_sum_filter_not hZ0.toFinset (fun ρ => ρ ∈ ZerosBelow χ 1)]
    have hS1 : S1 χ = ∑ ρ ∈ hZ0.toFinset.filter (fun ρ => ρ ∈ ZerosBelow χ 1),
        (mult χ ρ : ℝ) / ‖ρ‖ := by
      unfold S1
      rw [finsum_mem_eq_finite_toFinset_sum _ hB1f]
      congr 1
      ext ρ
      simp only [Set.Finite.mem_toFinset, Finset.mem_filter]
      exact ⟨fun h => ⟨hB1 h, h⟩, fun h => h.2⟩
    have hrest : ∑ ρ ∈ hZ0.toFinset.filter (fun ρ => ρ ∉ ZerosBelow χ 1),
        (mult χ ρ : ℝ) / ‖ρ‖ ≤ Cw * Real.log (2 * N) := by
      calc _ ≤ ∑ ρ ∈ hZ0.toFinset.filter (fun ρ => ρ ∉ ZerosBelow χ 1), (mult χ ρ : ℝ) := by
            refine Finset.sum_le_sum fun ρ hρ => ?_
            rw [Finset.mem_filter] at hρ
            obtain ⟨hρ1, hρ2⟩ := hρ
            have hρZ : ρ ∈ ZerosNear χ 0 := by simpa using hρ1
            obtain ⟨h1, h2, h3, h4⟩ := hρZ
            have him : 1 ≤ |ρ.im| := by
              by_contra hlt
              push_neg at hlt
              exact hρ2 ⟨h1, h2, hlt, h4⟩
            exact div_le_self (Nat.cast_nonneg _) (him.trans (Complex.abs_im_le_norm ρ))
        _ ≤ ∑ ρ ∈ hZ0.toFinset, (mult χ ρ : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => Nat.cast_nonneg _)
        _ ≤ Cw * Real.log (2 * N) := by
            rw [← hlog, ← finsum_mem_eq_finite_toFinset_sum _ hZ0]
            exact hZ0sum
    linarith
  linarith

end PI.EF
end
end

section

noncomputable section

namespace PI.EF

open Complex Filter Topology Set DirichletCharacter

section prim
variable {N : ℕ}

lemma factorsThrough_inv {χ : DirichletCharacter ℂ N} {d : ℕ} (h : χ.FactorsThrough d) :
    (χ⁻¹).FactorsThrough d := by
  obtain ⟨hd, χ₀, hχ⟩ := h
  exact ⟨hd, χ₀⁻¹, by rw [hχ, map_inv]⟩

lemma conductor_inv (χ : DirichletCharacter ℂ N) : (χ⁻¹).conductor = χ.conductor := by
  unfold DirichletCharacter.conductor
  congr 1
  ext d
  simp only [DirichletCharacter.conductorSet, Set.mem_setOf_eq]
  exact ⟨fun h => by simpa using factorsThrough_inv h, factorsThrough_inv⟩

lemma isPrimitive_inv {χ : DirichletCharacter ℂ N} (h : χ.IsPrimitive) : (χ⁻¹).IsPrimitive := by
  have h' : χ.conductor = N := h
  show (χ⁻¹).conductor = N
  rw [conductor_inv, h']

lemma level_eq_one_of_primitive_one [NeZero N] {χ : DirichletCharacter ℂ N} (h : χ.IsPrimitive)
    (h1 : χ = 1) : N = 1 := by
  have h' : χ.conductor = N := h
  rw [h1, DirichletCharacter.conductor_one] at h'
  exact h'.symm

end prim

variable {N : ℕ} [NeZero N]

lemma completed_ne_zero_right (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 ≤ s.re)
    (h1 : χ ≠ 1 ∨ s ≠ 1) : completedLFunction χ s ≠ 0 := by
  intro h0
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have h2 := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
  rw [h0, zero_div] at h2
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ h1 hs h2

lemma completed_ne_zero_left {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {s : ℂ}
    (hs : s.re ≤ 0) (h1 : χ ≠ 1 ∨ s ≠ 0) : completedLFunction χ s ≠ 0 := by
  intro h0
  have hp := (isPrimitive_inv hχ).completedLFunction_one_sub s
  rw [inv_inv, h0, mul_zero] at hp
  refine completed_ne_zero_right χ⁻¹ (s := 1 - s) (by simp; linarith) ?_ hp
  rcases h1 with h | h
  · left
    exact fun h' => h (inv_eq_one.mp h')
  · right
    intro h'
    apply h
    linear_combination -h'

theorem zeroLocus : ZeroLocus := by
  intro N _ χ hχ s hs hs1 hL
  by_cases hre1 : 1 ≤ s.re
  · exact absurd hL (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr hs1) hre1)
  by_cases hre0 : 0 < s.re
  · left
    exact ⟨hre0, by linarith⟩
  push_neg at hre1 hre0
  right
  by_cases hc : s = 0 ∧ χ = 1
  · exfalso
    obtain ⟨rfl, rfl⟩ := hc
    have hN := level_eq_one_of_primitive_one hχ rfl
    subst hN
    rw [DirichletCharacter.LFunction_modOne_eq, riemannZeta_zero] at hL
    norm_num at hL
  have hc' : χ ≠ 1 ∨ s ≠ 0 := by tauto
  have hne := completed_ne_zero_left hχ hre0 hc'
  have hsN : s ≠ 0 ∨ N ≠ 1 := by
    rcases hc' with h | h
    · right
      intro hN
      subst hN
      exact h (DirichletCharacter.level_one χ)
    · left
      exact h
  have hdiv := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s hsN
  rw [hL, eq_comm, div_eq_zero_iff] at hdiv
  rcases hdiv with h | hg
  · exact absurd h hne
  rcases DirichletCharacter.even_or_odd χ with he | ho
  · rw [he.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hg
    obtain ⟨n, hn⟩ := hg
    have hre := congrArg Complex.re hn
    simp at hre
    have hn1 : (n : ℝ) < 1 := by linarith
    have hn0 : n = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hn1)
    subst hn0
    simp at hn
    refine Or.inl ⟨hn, he, ?_⟩
    intro h1
    exact hc ⟨hn, h1⟩
  · rw [ho.gammaFactor_def, Complex.Gammaℝ_eq_zero_iff] at hg
    obtain ⟨n, hn⟩ := hg
    have hre := congrArg Complex.re hn
    simp at hre
    have hn1 : (n : ℝ) < 1 := by linarith
    have hn0 : n = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hn1)
    subst hn0
    refine Or.inr ⟨?_, ho⟩
    simp at hn
    linear_combination hn

private lemma exists_differentiable_Gammaℝ_inv_eq_mul : ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ g 0 ≠ 0 ∧
    ∀ z : ℂ, (Gammaℝ z)⁻¹ = z * g z := by
  refine ⟨fun s => (Real.pi : ℂ) ^ (s / 2) * (1 / 2 * (Complex.Gamma (s / 2 + 1))⁻¹), ?_, ?_, ?_⟩
  · refine Differentiable.mul ?_ ?_
    · exact (differentiable_id.div_const (2 : ℂ)).const_cpow
        (Or.inl (by exact_mod_cast Real.pi_ne_zero))
    · exact (differentiable_const _).mul
        (Complex.differentiable_one_div_Gamma.comp ((differentiable_id.div_const (2 : ℂ)).add_const 1))
  · simp [Complex.Gamma_one]
  · intro z
    rw [Complex.Gammaℝ_def, neg_div, Complex.cpow_neg, mul_inv, inv_inv]
    by_cases hz : z = 0
    · subst hz
      simp [Complex.Gamma_zero]
    · have key : (Complex.Gamma (z / 2))⁻¹ = z * (1 / 2 * (Complex.Gamma (z / 2 + 1))⁻¹) := by
        rw [Complex.Gamma_add_one _ (div_ne_zero hz two_ne_zero), mul_inv]
        have h2 : z * (1 / 2) * (z / 2)⁻¹ = 1 := by field_simp
        calc (Complex.Gamma (z / 2))⁻¹
            = (z * (1 / 2) * (z / 2)⁻¹) * (Complex.Gamma (z / 2))⁻¹ := by rw [h2, one_mul]
          _ = _ := by ring
      rw [key]
      ring

theorem mult_zero_of_even {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (he : χ.Even)
    (h1 : χ ≠ 1) : LFunction χ 0 = 0 ∧ analyticOrderNatAt (LFunction χ) 0 = 1 := by
  obtain ⟨g, hgd, hg0, hgz⟩ := exists_differentiable_Gammaℝ_inv_eq_mul
  have hN1 : N ≠ 1 := by
    intro hN
    subst hN
    exact h1 (DirichletCharacter.level_one χ)
  have hLeq : ∀ s, LFunction χ s = completedLFunction χ s * (s * g s) := by
    intro s
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hN1),
      he.gammaFactor_def, div_eq_mul_inv, hgz]
  have hc0 : completedLFunction χ 0 ≠ 0 := completed_ne_zero_left hχ (by simp) (Or.inl h1)
  have hcd : Differentiable ℂ (completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction h1
  refine ⟨by rw [hLeq]; simp, ?_⟩
  have hLa : AnalyticAt ℂ (LFunction χ) 0 := (DirichletCharacter.differentiable_LFunction h1).analyticAt 0
  have hord : analyticOrderAt (LFunction χ) 0 = ((1 : ℕ) : ℕ∞) := by
    rw [hLa.analyticOrderAt_eq_natCast]
    refine ⟨fun s => completedLFunction χ s * g s, (hcd.mul hgd).analyticAt 0, mul_ne_zero hc0 hg0, ?_⟩
    filter_upwards with z
    rw [hLeq]
    simp only [sub_zero, pow_one, smul_eq_mul]
    ring
  simp [analyticOrderNatAt, hord]

end PI.EF
end
end
