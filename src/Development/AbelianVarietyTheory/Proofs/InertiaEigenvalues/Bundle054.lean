module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.UniformSpace.Matrix
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem fourU_hasCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∀ f : Hn r F E → ℂ, IsTest f → (∃ U ∈ 𝓝 (0 : Hn r F E), ∀ X : Hn r F E, ∀ u ∈ U, f (X + u) = f X) → HasCompactSupport (fourU M ψ f) := by
  intro F E _ _ _ _ hUn r M ψ hψ htr f hf hloc
  obtain ⟨U, hU, hfU⟩ := hloc
  haveI : CharZero F := hUn.charZero
  haveI : LocallyCompactSpace E := hUn.lcE
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  letI := M.mE
  haveI := M.bE
  haveI := M.haarE
  obtain ⟨x₀, hx₀, -⟩ := hψ.2
  set a : E := algebraMap F E (x₀ / 2) with ha
  have htra : Algebra.trace F E a = x₀ := by
    apply (algebraMap F E).injective
    rw [htr a, ha, hUn.star_fix, ← map_add (f := _), add_halves]

  have hcont : Continuous (fun t : Fin r → E => ((0 : selfAdjoint (Matrix (Fin r) (Fin r) E)), t, (0 : F))) := by
    fun_prop
  have hpre : (fun t : Fin r → E => ((0 : selfAdjoint (Matrix (Fin r) (Fin r) E)), t, (0 : F))) ⁻¹' U ∈ 𝓝 (0 : Fin r → E) :=
    hcont.tendsto 0 hU
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hpre

  have hzero : ∀ X : Hn r F E, ∀ i, ‖a‖ / δ < ‖X.2.1 i‖ → fourU M ψ f X = 0 := by
    intro X i hi
    have hbi : X.2.1 i ≠ 0 := by
      intro h; rw [h, norm_zero] at hi; exact absurd hi (not_lt.2 (by positivity))
    set t : Fin r → E := Pi.single i (star (a / X.2.1 i)) with ht
    have htn : ‖t‖ < δ := by
      rw [ht, Pi.norm_single, hUn.norm_star, norm_div]
      rw [div_lt_iff₀ (norm_pos_iff.2 hbi)]
      rw [div_lt_iff₀ hδ] at hi
      linarith
    have htU : ((0 : selfAdjoint (Matrix (Fin r) (Fin r) E)), t, (0 : F)) ∈ U :=
      hball (mem_ball_zero_iff.2 htn)
    have hst : star t ⬝ᵥ X.2.1 = a := by
      rw [ht, ← Pi.single_star, single_dotProduct, star_star, div_mul_cancel₀ _ hbi]
    have hshift : ∀ c, f (X.1, t + c, X.2.2) = f (X.1, c, X.2.2) := by
      intro c
      have := hfU (X.1, c, X.2.2) _ htU
      rw [← this]
      congr 1
      ext <;> simp [add_comm]
    have hchar : ∀ c : Fin r → E, ψ (Algebra.trace F E (star (t + c) ⬝ᵥ X.2.1)) =
        ψ x₀ * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) := by
      intro c
      rw [star_add, add_dotProduct, map_add (f := _), AddChar.map_add_eq_mul, hst, htra]
    have key : fourU M ψ f X = ψ x₀ * fourU M ψ f X := by
      simp only [fourU]
      calc ∫ c, f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) ∂(Measure.pi fun _ : Fin r => M.μE)
          = ∫ c, f (X.1, t + c, X.2.2) * ψ (Algebra.trace F E (star (t + c) ⬝ᵥ X.2.1)) ∂(Measure.pi fun _ : Fin r => M.μE) :=
            (integral_add_left_eq_self (fun c => f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1))) t).symm
        _ = ∫ c, ψ x₀ * (f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1))) ∂(Measure.pi fun _ : Fin r => M.μE) := by
            congr 1; funext c; rw [hshift, hchar]; ring
        _ = _ := integral_const_mul _ _
    have h1 : (1 - ψ x₀) * fourU M ψ f X = 0 := by rw [sub_mul, one_mul, ← key, sub_self]
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hx₀
    · exact h

  have hzero2 : ∀ X : Hn r F E, (∀ c, f (X.1, c, X.2.2) = 0) → fourU M ψ f X = 0 := by
    intro X h
    simp [fourU, h]
  have hK : IsCompact ((Prod.fst '' tsupport f) ×ˢ (Metric.closedBall (0 : Fin r → E) (‖a‖ / δ) ×ˢ
      ((fun Y : Hn r F E => Y.2.2) '' tsupport f))) :=
    (hf.2.image continuous_fst).prod ((isCompact_closedBall _ _).prod (hf.2.image (by fun_prop)))
  refine HasCompactSupport.intro hK fun X hX => ?_
  by_contra hne
  apply hX
  refine ⟨?_, ?_, ?_⟩
  · by_contra h1
    exact hne (hzero2 X fun c => image_eq_zero_of_notMem_tsupport fun hc => h1 ⟨_, hc, rfl⟩)
  · rw [mem_closedBall_zero_iff]
    by_contra h2
    have hR : 0 ≤ ‖a‖ / δ := by positivity
    rw [pi_norm_le_iff_of_nonneg hR] at h2
    push_neg at h2
    obtain ⟨i, hi⟩ := h2
    exact hne (hzero X i hi)
  · by_contra h3
    exact hne (hzero2 X fun c => image_eq_zero_of_notMem_tsupport fun hc => h3 ⟨_, hc, rfl⟩)

end GlobalTheory
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.FourGUnit

variable {F : Type} [NontriviallyNormedField F]

theorem integral_ball_char {r : ℕ} [MeasurableSpace F] [BorelSpace F] [IsUltrametricDist F] [ProperSpace F]
    (μ : Measure F) [μ.IsAddHaarMeasure] (hvol : μ (Metric.closedBall 0 1) = 1) (ψ : AddChar F ℂ)
    (hψ : IsStdChar ψ) (v : Fin r → F) :
    ∫ x, {x : Fin r → F | ∀ i, ‖x i‖ ≤ 1}.indicator (fun x => ψ (x ⬝ᵥ v)) x ∂(Measure.pi fun _ => μ) =
      {x : Fin r → F | ∀ i, ‖x i‖ ≤ 1}.indicator 1 v := by
  set S : Set (Fin r → F) := {x | ∀ i, ‖x i‖ ≤ 1} with hSdef
  have hS : S = Set.univ.pi fun _ => Metric.closedBall (0 : F) 1 := by
    ext x; simp [S, Metric.mem_closedBall]
  have hSm : MeasurableSet S := hS ▸ MeasurableSet.univ_pi (fun _ => measurableSet_closedBall)
  by_cases hv : v ∈ S
  · rw [Set.indicator_of_mem hv, integral_indicator hSm,
      setIntegral_congr_fun hSm (g := fun _ => (1 : ℂ)) (fun x hx => ?_), setIntegral_const]
    · rw [Measure.real, hS, Measure.pi_pi]
      simp [hvol]
    · apply hψ.1
      rw [dotProduct]
      apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
      intro i _
      rw [norm_mul]
      exact mul_le_one₀ (hx i) (norm_nonneg _) (hv i)
  · rw [Set.indicator_of_notMem hv]
    obtain ⟨i, hi⟩ : ∃ i, 1 < ‖v i‖ := by
      simp only [S, Set.mem_setOf_eq, not_forall, not_le] at hv; exact hv
    obtain ⟨x₀, hx₀, hx₀'⟩ := hψ.2
    have hvi : v i ≠ 0 := by
      intro h; rw [h, norm_zero] at hi; linarith
    set z₀ : Fin r → F := Pi.single i (x₀ * (v i)⁻¹) with hz₀def
    have hz₀ : z₀ ∈ S := by
      intro j
      by_cases hj : j = i
      · subst hj
        rw [hz₀def, Pi.single_eq_same]
        apply hx₀'
        rw [norm_inv]
        exact inv_lt_one_of_one_lt₀ hi
      · rw [hz₀def, Pi.single_eq_of_ne hj, norm_zero]; exact zero_le_one
    have hχ : ψ (z₀ ⬝ᵥ v) ≠ 1 := by
      rw [hz₀def, single_dotProduct, mul_assoc, inv_mul_cancel₀ hvi, mul_one]
      exact hx₀
    have hadd : ∀ a b : Fin r → F, a ∈ S → b ∈ S → a + b ∈ S := fun a b ha hb i =>
      (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ha i) (hb i))
    have key : ∀ z, S.indicator (fun x => ψ (x ⬝ᵥ v)) (z + z₀) =
        S.indicator (fun x => ψ (x ⬝ᵥ v)) z * ψ (z₀ ⬝ᵥ v) := by
      intro z
      by_cases hz : z ∈ S
      · rw [Set.indicator_of_mem (hadd _ _ hz hz₀), Set.indicator_of_mem hz, add_dotProduct,
          AddChar.map_add_eq_mul]
      · have hneg : -z₀ ∈ S := fun j => by rw [Pi.neg_apply, norm_neg]; exact hz₀ j
        have : z + z₀ ∉ S := fun h => hz (by simpa using hadd _ _ h hneg)
        rw [Set.indicator_of_notMem this, Set.indicator_of_notMem hz, zero_mul]
    have h := integral_add_right_eq_self (μ := Measure.pi fun _ : Fin r => μ)
      (fun z => S.indicator (fun x => ψ (x ⬝ᵥ v)) z) z₀
    simp only [key, integral_mul_const] at h
    have h2 : (∫ z, S.indicator (fun x => ψ (x ⬝ᵥ v)) z ∂(Measure.pi fun _ => μ)) * (ψ (z₀ ⬝ᵥ v) - 1) = 0 := by
      rw [mul_sub, mul_one, h, sub_self]
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact h1
    · exact absurd (sub_eq_zero.mp h1) hχ

end GlobalTheory.JR.FourGUnit

namespace GlobalTheory.JR


open FourGUnit in
theorem fourG_unitG : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    fourG M ψ (unitG r F) = unitG r F := by
  intro F E _ _ _ _ U r M ψ hψ
  letI := M.mF
  haveI := M.bF
  haveI := U.ultraF
  haveI := U.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI := M.haarF
  funext Y
  obtain ⟨A, b, c, l⟩ := Y
  unfold fourG
  set S : Set (Fin r → F) := {x | ∀ i, ‖x i‖ ≤ 1} with hSdef
  set T : Set (Gl r F) := {Y | (∀ i j, ‖Y.1 i j‖ ≤ 1) ∧ (∀ i, ‖Y.2.1 i‖ ≤ 1) ∧ (∀ i, ‖Y.2.2.1 i‖ ≤ 1) ∧
    ‖Y.2.2.2‖ ≤ 1} with hTdef
  have hT : unitG r F = T.indicator 1 := rfl
  by_cases hP : (∀ i j, ‖A i j‖ ≤ 1) ∧ ‖l‖ ≤ 1
  · have hint : ∀ b' c' : Fin r → F, unitG r F (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') =
        S.indicator (fun x => ψ (x ⬝ᵥ c)) b' * S.indicator (fun x => ψ (x ⬝ᵥ b)) c' := by
      intro b' c'
      by_cases hb' : b' ∈ S
      · by_cases hc' : c' ∈ S
        · rw [hT, Set.indicator_of_mem (show (A, b', c', l) ∈ T from ⟨hP.1, hb', hc', hP.2⟩),
            Set.indicator_of_mem hb', Set.indicator_of_mem hc', Pi.one_apply, one_mul,
            AddChar.map_add_eq_mul, dotProduct_comm c b', mul_comm]
        · rw [hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hc' h.2.2.1),
            Set.indicator_of_notMem hc', zero_mul, mul_zero]
      · rw [hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hb' h.2.1),
          Set.indicator_of_notMem hb', zero_mul, zero_mul]
    have hball : ∀ v : Fin r → F, ∫ x, S.indicator (fun x => ψ (x ⬝ᵥ v)) x ∂(Measure.pi fun _ => M.μF) =
        S.indicator 1 v := integral_ball_char M.μF M.volF ψ hψ
    simp_rw [hint, integral_const_mul, hball, integral_mul_const, hball]
    by_cases hb : b ∈ S
    · by_cases hc : c ∈ S
      · rw [hT, Set.indicator_of_mem (show (A, b, c, l) ∈ T from ⟨hP.1, hb, hc, hP.2⟩),
          Set.indicator_of_mem hb, Set.indicator_of_mem hc]
        simp
      · rw [hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hc h.2.2.1),
          Set.indicator_of_notMem hc, zero_mul]
    · rw [hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hb h.2.1),
        Set.indicator_of_notMem hb, mul_zero]
  · have h0 : ∀ b' c' : Fin r → F, unitG r F (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') = 0 := by
      intro b' c'
      rw [hT, Set.indicator_of_notMem (show (A, b', c', l) ∉ T from fun h => hP ⟨h.1, h.2.2.2⟩),
        zero_mul]
    simp_rw [h0, integral_zero]
    rw [hT, Set.indicator_of_notMem (show (A, b, c, l) ∉ T from fun h => hP ⟨h.1, h.2.2.2⟩)]

end GlobalTheory.JR
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem integral_eq_zero_of_shift_mul {V : Type} [AddGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (μ : Measure V) [μ.IsAddRightInvariant] (g : V → ℂ) (t : V) (z : ℂ) (hz : z ≠ 1)
    (h : ∀ x, g (x + t) = g x * z) : ∫ x, g x ∂μ = 0 := by
  have h1 : ∫ x, g x ∂μ = (∫ x, g x ∂μ) * z := by
    calc ∫ x, g x ∂μ = ∫ x, g (x + t) ∂μ := (integral_add_right_eq_self g t).symm
      _ = ∫ x, g x * z ∂μ := by simp only [h]
      _ = (∫ x, g x ∂μ) * z := integral_mul_const z g
  have h2 : (∫ x, g x ∂μ) * (1 - z) = 0 := by rw [mul_sub, mul_one, ← h1, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.1 h3).symm hz

theorem exists_short_dot_eq {F : Type} [NormedField F] {r : ℕ} (x₀ : F) {ε : ℝ} (hε : 0 < ε) (b : Fin r → F)
    (hb : b ∉ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε)) :
    ∃ t : Fin r → F, ‖t‖ < ε ∧ t ⬝ᵥ b = x₀ := by
  have hR : 0 ≤ ‖x₀‖ / ε := div_nonneg (norm_nonneg _) hε.le
  have hb' : ‖x₀‖ / ε < ‖b‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hb
  obtain ⟨i, hi⟩ : ∃ i, ‖x₀‖ / ε < ‖b i‖ := by
    by_contra hcon
    push Not at hcon
    exact absurd ((pi_norm_le_iff_of_nonneg hR).2 hcon) (not_le.2 hb')
  have hbi : b i ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hi
    exact absurd hi (not_lt.2 hR)
  refine ⟨Pi.single i (x₀ / b i), (pi_norm_lt_iff hε).2 fun j => ?_, ?_⟩
  · by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, norm_div, div_lt_iff₀ (norm_pos_iff.2 hbi)]
      rw [div_lt_iff₀ hε] at hi
      calc ‖x₀‖ < ‖b j‖ * ε := hi
        _ = ε * ‖b j‖ := mul_comm _ _
    · rw [Pi.single_eq_of_ne hj, norm_zero]
      exact hε
  · rw [single_dotProduct, div_mul_cancel₀ _ hbi]

theorem fourG_hasCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    ∀ f' : Gl r F → ℂ, IsTest f' → (∃ U ∈ 𝓝 (0 : Gl r F), ∀ Y : Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) →
    HasCompactSupport (fourG M ψ f') := by
  intro F E _ _ _ _ _ r M ψ hψ f' hf' hU
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := Unram.lcF (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨U, hU0, hUinv⟩ := hU
  obtain ⟨x₀, hx₀, -⟩ := hψ.2
  set μ : Measure (Fin r → F) := Measure.pi fun _ : Fin r => M.μF with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance
  have h00 : ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), (0 : Fin r → F), (0 : F)) = (0 : Gl r F) := rfl
  obtain ⟨ε2, hε2, hB⟩ : ∃ ε > 0, ∀ t : Fin r → F, ‖t‖ < ε →
      ((0 : Matrix (Fin r) (Fin r) F), t, (0 : Fin r → F), (0 : F)) ∈ U := by
    have hc : Continuous fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), t, (0 : Fin r → F), (0 : F)) := by
      fun_prop
    have hm : (fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), t, (0 : Fin r → F), (0 : F))) ⁻¹' U ∈
        𝓝 (0 : Fin r → F) := hc.continuousAt.preimage_mem_nhds (by rw [h00]; exact hU0)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hm
    exact ⟨ε, hε, fun t ht => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ht)⟩
  obtain ⟨ε3, hε3, hC⟩ : ∃ ε > 0, ∀ t : Fin r → F, ‖t‖ < ε →
      ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), t, (0 : F)) ∈ U := by
    have hc : Continuous fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), t, (0 : F)) := by
      fun_prop
    have hm : (fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), t, (0 : F))) ⁻¹' U ∈
        𝓝 (0 : Fin r → F) := hc.continuousAt.preimage_mem_nhds (by rw [h00]; exact hU0)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hm
    exact ⟨ε, hε, fun t ht => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ht)⟩
  have key2 : ∀ (A : Matrix (Fin r) (Fin r) F) (b c : Fin r → F) (l : F) (t : Fin r → F), ‖t‖ < ε2 →
      f' (A, b + t, c, l) = f' (A, b, c, l) := by
    intro A b c l t ht
    have := hUinv (A, b, c, l) _ (hB t ht)
    simpa only [Prod.mk_add_mk, add_zero] using this
  have key3 : ∀ (A : Matrix (Fin r) (Fin r) F) (b c : Fin r → F) (l : F) (t : Fin r → F), ‖t‖ < ε3 →
      f' (A, b, c + t, l) = f' (A, b, c, l) := by
    intro A b c l t ht
    have := hUinv (A, b, c, l) _ (hC t ht)
    simpa only [Prod.mk_add_mk, add_zero] using this
  let P : Set (Matrix (Fin r) (Fin r) F × F) := (fun Y : Gl r F => (Y.1, Y.2.2.2)) '' tsupport f'
  have hPc : IsCompact P := hf'.2.image (by fun_prop)
  let K : Set (Gl r F) :=
    (fun p : (Matrix (Fin r) (Fin r) F × F) × (Fin r → F) × (Fin r → F) => ((p.1.1, p.2.1, p.2.2, p.1.2) : Gl r F)) ''
      (P ×ˢ (Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε3) ×ˢ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε2)))
  have hKc : IsCompact K :=
    (hPc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).image (by fun_prop)
  refine HasCompactSupport.intro hKc fun Y hY => ?_
  obtain ⟨A, b, c, l⟩ := Y
  show ∫ b', ∫ c', f' (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') ∂μ ∂μ = 0
  by_cases hP : (A, l) ∈ P
  · by_cases hb : b ∈ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε3)
    · by_cases hc : c ∈ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε2)
      · exact absurd ⟨((A, l), b, c), ⟨hP, hb, hc⟩, rfl⟩ hY
      · obtain ⟨t, ht, htc⟩ := exists_short_dot_eq x₀ hε2 c hc
        refine integral_eq_zero_of_shift_mul μ _ t (ψ x₀) hx₀ fun b' => ?_
        rw [← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)
        simp only
        rw [key2 A b' c' l t ht, dotProduct_add, ← add_assoc, AddChar.map_add_eq_mul, dotProduct_comm c t, htc,
          mul_assoc]
    · obtain ⟨t, ht, htb⟩ := exists_short_dot_eq x₀ hε3 b hb
      have hin : ∀ b' : Fin r → F, ∫ c', f' (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') ∂μ = 0 := by
        intro b'
        refine integral_eq_zero_of_shift_mul μ _ t (ψ x₀) hx₀ fun c' => ?_
        rw [key3 A b' c' l t ht, add_dotProduct, add_right_comm, AddChar.map_add_eq_mul, htb, mul_assoc]
      simp only [hin, integral_zero]
  · have hz : ∀ b' c' : Fin r → F, f' (A, b', c', l) = 0 := by
      intro b' c'
      by_contra hne
      exact hP ⟨(A, b', c', l), subset_tsupport _ hne, rfl⟩
    simp only [hz, zero_mul, integral_zero]

end GlobalTheory.JR
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.UnitWitt

variable {E : Type} [Field E] [StarRing E] {r : ℕ}

theorem vecMulVec_mulVec_eq (w v z : Fin r → E) : vecMulVec w v *ᵥ z = (v ⬝ᵥ z) • w := by
  ext i
  simp [mulVec, vecMulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]

theorem conjTranspose_vecMulVec_self (w : Fin r → E) : (vecMulVec w (star w))ᴴ = vecMulVec w (star w) := by
  ext i j
  simp [vecMulVec, conjTranspose_apply, mul_comm]

theorem vecMulVec_self_mul (w : Fin r → E) :
    vecMulVec w (star w) * vecMulVec w (star w) = (star w ⬝ᵥ w) • vecMulVec w (star w) := by
  ext i j
  simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, dotProduct, Pi.star_apply, Finset.sum_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem refl_mem (w : Fin r → E) (a : E) (ha : a ≠ 0) (hN : star w ⬝ᵥ w = a + star a) :
    (1 - a⁻¹ • vecMulVec w (star w)) ∈ unitaryGroup (Fin r) E := by
  rw [mem_unitaryGroup_iff']
  have hs : star (1 - a⁻¹ • vecMulVec w (star w)) = 1 - (star a)⁻¹ • vecMulVec w (star w) := by
    rw [star_sub, star_one, star_smul, star_inv₀]
    congr 2
    exact conjTranspose_vecMulVec_self w
  have ha' : star a ≠ 0 := by simpa using ha
  rw [hs]
  have key : (star a)⁻¹ + a⁻¹ - (star a)⁻¹ * a⁻¹ * (star w ⬝ᵥ w) = 0 := by
    rw [hN]; field_simp; ring
  calc (1 - (star a)⁻¹ • vecMulVec w (star w)) * (1 - a⁻¹ • vecMulVec w (star w))
      = 1 - ((star a)⁻¹ + a⁻¹ - (star a)⁻¹ * a⁻¹ * (star w ⬝ᵥ w)) • vecMulVec w (star w) := by
        rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, smul_mul_smul_comm, vecMulVec_self_mul,
          smul_smul, sub_smul, add_smul]
        abel
    _ = 1 := by rw [key, zero_smul, sub_zero]

theorem refl_mulVec (w u : Fin r → E) (a : E) (ha : star w ⬝ᵥ u = a) (ha0 : a ≠ 0) :
    (1 - a⁻¹ • vecMulVec w (star w)) *ᵥ u = u - w := by
  have h1 : (a⁻¹ • vecMulVec w (star w)) *ᵥ u = a⁻¹ • (vecMulVec w (star w) *ᵥ u) := by
    ext i; simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [sub_mulVec, one_mulVec, h1, vecMulVec_mulVec_eq, ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]

theorem star_dot (x y : Fin r → E) : star (star x ⬝ᵥ y) = star y ⬝ᵥ x := by
  simp [dotProduct, star_sum, mul_comm]

theorem exists_of_ne (u v : Fin r → E) (hc : star u ⬝ᵥ u = star v ⬝ᵥ v) (ha : star (u - v) ⬝ᵥ u ≠ 0) :
    ∃ g : unitaryGroup (Fin r) E, g.1 *ᵥ u = v := by
  have hN : star (u - v) ⬝ᵥ (u - v) = star (u - v) ⬝ᵥ u + star (star (u - v) ⬝ᵥ u) := by
    rw [star_dot]
    simp only [star_sub, sub_dotProduct, dotProduct_sub]
    rw [← hc]
    ring
  refine ⟨⟨_, refl_mem (u - v) _ ha hN⟩, ?_⟩
  show (1 - (star (u - v) ⬝ᵥ u)⁻¹ • vecMulVec (u - v) (star (u - v))) *ᵥ u = v
  rw [refl_mulVec (u - v) u _ rfl ha]
  abel

theorem exists_unitary_mulVec (h2 : (2 : E) ≠ 0) (u v : Fin r → E) (hc : star u ⬝ᵥ u = star v ⬝ᵥ v)
    (h0 : star u ⬝ᵥ u ≠ 0) : ∃ g : unitaryGroup (Fin r) E, g.1 *ᵥ u = v := by
  by_cases ha : star (u - v) ⬝ᵥ u = 0
  · have hvu : star v ⬝ᵥ u = star u ⬝ᵥ u := by
      rw [star_sub, sub_dotProduct, sub_eq_zero] at ha; exact ha.symm
    have hc' : star (-u) ⬝ᵥ (-u) = star v ⬝ᵥ v := by simpa using hc
    have ha' : star (-u - v) ⬝ᵥ (-u) ≠ 0 := by
      have : star (-u - v) ⬝ᵥ (-u) = 2 * (star u ⬝ᵥ u) := by
        simp only [star_sub, star_neg, sub_dotProduct, neg_dotProduct, dotProduct_neg, hvu]
        ring
      rw [this]; exact mul_ne_zero h2 h0
    obtain ⟨g, hg⟩ := exists_of_ne (-u) v hc' ha'
    refine ⟨⟨-g.1, ?_⟩, ?_⟩
    · rw [mem_unitaryGroup_iff', star_neg, neg_mul_neg]; exact mem_unitaryGroup_iff'.1 g.2
    · show (-g.1) *ᵥ u = v
      rw [← hg, neg_mulVec, mulVec_neg]
  · exact exists_of_ne u v hc ha

end GlobalTheory.UnitWitt

theorem GlobalTheory.unitary_transitive_of_norm : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (u v : Fin r → E), star u ⬝ᵥ u = star v ⬝ᵥ v →
    star u ⬝ᵥ u ≠ 0 → ∃ g : Matrix.unitaryGroup (Fin r) E, g.1 *ᵥ u = v := by
  intro F E _ _ _ _ hU r u v hc h0
  haveI : CharZero F := hU.charZero
  have h2 : (2 : E) ≠ 0 := by
    intro h
    apply (two_ne_zero : (2 : F) ≠ 0)
    apply (algebraMap F E).injective
    rw [map_ofNat, map_zero]; exact h
  exact GlobalTheory.UnitWitt.exists_unitary_mulVec h2 u v hc h0
end
