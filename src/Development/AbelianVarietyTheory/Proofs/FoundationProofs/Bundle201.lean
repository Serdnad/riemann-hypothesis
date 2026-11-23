module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle067
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle134
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle136
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle173
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle120
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle135
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle121
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle096
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Group.Tannery
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM.LatBd

theorem continuous_eisensteinLatticeTermWeightS_exponent {j : ℕ} (hj : 1 ≤ j) (z : ℂ) : Continuous fun s : ℝ => trm j s z := by
  by_cases hz : z = 0
  · subst hz
    have : ∀ s : ℝ, trm j s 0 = 0 := fun s => by
      simp [trm, zero_pow (by omega : j ≠ 0)]
    simp only [this]; exact continuous_const
  · unfold trm
    refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
    exact continuous_const.rpow (continuous_const.mul continuous_id) fun _ => Or.inl (norm_ne_zero_iff.2 hz)

theorem lin_ne_zero (x : ℤ × ℤ) (hx : x ≠ 0) (τ : ℍ) : (x.1 : ℂ) * (τ : ℂ) + x.2 ≠ 0 := by
  intro h
  have him : (x.1 : ℝ) * τ.im = 0 := by
    have := congrArg Complex.im h
    simpa using this
  have h1 : x.1 = 0 := by
    rcases mul_eq_zero.1 him with h' | h'
    · exact_mod_cast h'
    · exact absurd h' τ.im_pos.ne'
  have h2 : x.2 = 0 := by
    have := congrArg Complex.re h
    simp [h1] at this
    exact_mod_cast this
  exact hx (Prod.ext h1 h2)

theorem trm_cont_tau {j : ℕ} (hj : 1 ≤ j) (s : ℝ) (x : ℤ × ℤ) :
    Continuous fun τ : ℍ => trm j s ((x.1 : ℂ) * τ + x.2) := by
  by_cases hx : x = 0
  · subst hx
    have : ∀ τ : ℍ, trm j s (((0 : ℤ × ℤ).1 : ℂ) * τ + (0 : ℤ × ℤ).2) = 0 := fun τ => by
      simp [trm, zero_pow (by omega : j ≠ 0)]
    simp only [this]; exact continuous_const
  · have hc : Continuous fun τ : ℍ => (x.1 : ℂ) * (τ : ℂ) + x.2 :=
      (continuous_const.mul UpperHalfPlane.continuous_coe).add continuous_const
    unfold trm
    refine ((hc.pow j).inv₀ fun τ => pow_ne_zero _ (lin_ne_zero x hx τ)).mul
      (Complex.continuous_ofReal.comp ((continuous_norm.comp hc).rpow_const fun τ => Or.inl ?_))
    exact norm_ne_zero_iff.2 (lin_ne_zero x hx τ)

theorem dif_cont {α : Type*} [TopologicalSpace α] (L : ℕ) (v : ℤ × ℤ) (F : α → ℤ × ℤ → ℂ)
    (h : ∀ x, Continuous fun a => F a x) (x : ℤ × ℤ) : Continuous fun a => dif L v (F a) x := by
  unfold dif
  exact (h x).sub (continuous_const.mul (continuous_finsetSum _ fun r _ => h _))

theorem difdif_le (L : ℕ) (v : ℤ × ℤ) (F : ℤ × ℤ → ℂ) (u : ℤ × ℤ → ℝ) (h : ∀ x, ‖dif L v F x‖ ≤ u x)
    (x : ℤ × ℤ) : ‖dif L v (dif L v F) x‖ ≤ u x + (L : ℝ)⁻¹ * ∑ r ∈ Finset.range L, u (x + (r : ℤ) • v) := by
  show ‖dif L v F x - (L : ℂ)⁻¹ * ∑ r ∈ Finset.range L, dif L v F (x + (r : ℤ) • v)‖ ≤ _
  refine (norm_sub_le _ _).trans (add_le_add (h x) ?_)
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => h _))
    (inv_nonneg.2 (Nat.cast_nonneg L))

theorem hasSum_dom (L : ℕ) (hL : 0 < L) (v : ℤ × ℤ) (u : ℤ × ℤ → ℝ) {S : ℝ} (hu : HasSum u S) :
    HasSum (fun x => u x + (L : ℝ)⁻¹ * ∑ r ∈ Finset.range L, u (x + (r : ℤ) • v)) (2 * S) := by
  have h1 : ∀ r : ℕ, HasSum (fun x => u (x + (r : ℤ) • v)) S := fun r =>
    (Equiv.addRight ((r : ℤ) • v)).hasSum_iff.2 hu
  have h2 := hasSum_sum (s := Finset.range L) fun r _ => h1 r
  have h3 := hu.add (h2.mul_left ((L : ℝ)⁻¹))
  convert h3 using 1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  field_simp; ring

theorem measurable_tsum_any {X I : Type} [MeasurableSpace X] [Countable I] [MeasurableSpace I]
    [MeasurableSingletonClass I] (g : X → I → ℂ) (hg : ∀ i, Measurable fun x => g x i) :
    Measurable fun x => ∑' i, g x i := by
  have e : ∀ x, ∑' i, g x i = ∫ i, g x i ∂(Measure.count : Measure I) := fun x => by
    by_cases hf : Summable (g x)
    · have hi : Integrable (g x) (Measure.count : Measure I) := by
        rw [integrable_count_iff]; exact summable_norm_iff.mpr hf
      rw [integral_countable hi]; simp [measureReal_def]
    · rw [tsum_eq_zero_of_not_summable hf, integral_undef]
      intro hi; rw [integrable_count_iff] at hi; exact hf (summable_norm_iff.mp hi)
  simp only [e]
  have hm : Measurable fun p : X × I => g p.1 p.2 := measurable_from_prod_countable_left hg
  exact (StronglyMeasurable.integral_prod_right' (ν := (Measure.count : Measure I))
    hm.stronglyMeasurable).measurable

end GlobalTheory.EisM.LatBd

namespace GlobalTheory.EisM.LatBd

theorem lat_mod_meas_tendsto : ∀ (j L : ℕ) (Φ : ℤ × ℤ → ℂ), 2 ≤ j → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) →
    (∃ (C : ℝ) (A : ℕ), ∀ (s : ℝ) (τ : ℍ), 0 ≤ s → s ≤ 1 → ‖lat j s L (0, 1) Φ τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹)) ∧
    (∀ s : ℝ, Measurable (lat j s L (0, 1) Φ)) ∧
    ∀ τ : ℍ, Tendsto (fun s : ℝ => lat j s L (0, 1) Φ τ) (𝓝[>] 0) (𝓝 (lat j 0 L (0, 1) Φ τ)) := by
  intro j L Φ hj hL ⟨B, hB⟩
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hj1 : 1 ≤ j := by omega
  obtain ⟨C, A, hrow⟩ := GlobalTheory.T.eisensteinLattice_rowDifference_summable_bound j L hj hL

  have dom : ∀ τ : ℍ, ∃ U : ℤ × ℤ → ℝ, ∃ S : ℝ, HasSum U (2 * S) ∧ S ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹) ∧
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 → ∀ x, ‖Φ x * dif L (0, 1) (dif L (0, 1)
        fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x‖ ≤ B * U x := by
    intro τ
    obtain ⟨u, hus, hule, hu⟩ := hrow τ
    refine ⟨_, _, hasSum_dom L hL (0, 1) u hus.hasSum, hule, fun s hs0 hs1 x => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hB x) (difdif_le L (0, 1) _ u (fun x => hu s x hs0 hs1) x) (norm_nonneg _) hB0
  refine ⟨⟨2 * B * C, A, fun s τ hs0 hs1 => ?_⟩, fun s => ?_, fun τ => ?_⟩
  · obtain ⟨U, S, hU, hS, hb⟩ := dom τ
    have h := tsum_of_norm_bounded (hU.mul_left B) (hb s hs0 hs1)
    have hpos : 0 ≤ B * 2 := by positivity
    calc ‖lat j s L (0, 1) Φ τ‖ ≤ B * (2 * S) := h
      _ = (B * 2) * S := by ring
      _ ≤ (B * 2) * (C * (τ.im ^ A + (τ.im ^ A)⁻¹)) := mul_le_mul_of_nonneg_left hS hpos
      _ = 2 * B * C * (τ.im ^ A + (τ.im ^ A)⁻¹) := by ring
  · unfold lat
    refine measurable_tsum_any (fun (τ : ℍ) x => Φ x * dif L (0, 1) (dif L (0, 1)
      fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x) fun x => ?_
    exact (continuous_const.mul (dif_cont L (0, 1) _
      (dif_cont L (0, 1) _ (fun y => trm_cont_tau hj1 s y)) x)).measurable
  · obtain ⟨U, S, hU, -, hb⟩ := dom τ
    unfold lat
    refine tendsto_tsum_of_dominated_convergence (bound := fun x => B * U x) (hU.mul_left B).summable
      (fun x => ?_) ?_
    · have hc : Continuous fun s : ℝ => Φ x * dif L (0, 1) (dif L (0, 1)
          fun y : ℤ × ℤ => trm j s ((y.1 : ℂ) * τ + y.2)) x :=
        continuous_const.mul (dif_cont L (0, 1) _ (dif_cont L (0, 1) _ (fun y => continuous_eisensteinLatticeTermWeightS_exponent hj1 _)) x)
      exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with s hs
      exact hb s hs.1.le hs.2.le

end GlobalTheory.EisM.LatBd
end
end

section

open GlobalTheory.K5

namespace GlobalTheory.K5.NotPow

theorem exists_derivation_fix_q_kill_padicInt (p : ℕ) [Fact p.Prime] : ∃ D : Derivation ℤ (O0 p) (O0 p), D (qO p) = qO p ∧
    ∀ r : ℤ_[p], D (algebraMap ℤ_[p] (O0 p) r) = 0 := GlobalTheory.T.exists_qDerivation_completion_Zp p

theorem derExt (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (h : IsClo p Ω)
    (D : Derivation ℤ (O0 p) (O0 p)) :
    ∃ E : Derivation ℤ Ω Ω, ∀ x, E (algebraMap (O0 p) Ω x) = algebraMap (O0 p) Ω (D x) :=
  GlobalTheory.T.exists_derivation_extend_padicLaurent_to_closure p Ω h D

theorem derAlg (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (h : IsClo p Ω)
    (E : Derivation ℤ Ω Ω) (hE : ∀ r : ℤ_[p], E (algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) r)) = 0) :
    ∀ x : Ω, IsAlgZp p x → E x = 0 := GlobalTheory.T.derivation_eq_zero_of_isAlgebraicOverPadicIntegers p Ω h E hE

theorem repr (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (h : IsClo p Ω) :
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x}),
    ∃ (n : ℕ) (a : Fin n → Ω) (f : Fin n → O0 p) (g : O0 p), (∀ i, IsAlgZp p (a i)) ∧
      LinearIndependent (O0 p) a ∧ g ≠ 0 ∧
      algebraMap (O0 p) Ω g * b = ∑ i, algebraMap (O0 p) Ω (f i) * a i := by
  intro b hb
  obtain ⟨g₁, hg₁, hy⟩ := GlobalTheory.T.exists_mul_mem_span_algebraicOverPadicIntegers p Ω h b hb
  obtain ⟨n, a, f, g₂, ha, hli, hg₂, he⟩ := GlobalTheory.T.exists_mul_linearIndependent_algebraicOverPadicIntegers p Ω h _ hy
  refine ⟨n, a, f, g₂ * g₁, ha, hli, mul_ne_zero hg₂ hg₁, ?_⟩
  rw [map_mul, mul_assoc, he]

theorem primeP (p : ℕ) [Fact p.Prime] : Prime (p : O0 p) := GlobalTheory.T.prime_natCast_completed_laurent_ring p

theorem splitP (p : ℕ) [Fact p.Prime] : ∀ x : O0 p, x ≠ 0 →
    ∃ (k : ℕ) (y : O0 p), x = (p : O0 p) ^ k * y ∧ ¬ (p : O0 p) ∣ y := GlobalTheory.T.exists_eq_prime_pow_mul_not_dvd_O0 p

theorem not_eigen (p : ℕ) [Fact p.Prime] (D : Derivation ℤ (O0 p) (O0 p)) (f g : O0 p)
    (hf : f ≠ 0) (hg : g ≠ 0) : (p : O0 p) * (g * D f - f * D g) ≠ g * f := by
  intro heq
  obtain ⟨a, f0, rfl, hf0⟩ := splitP p f hf
  obtain ⟨c, g0, rfl, hg0⟩ := splitP p g hg
  have hD : ∀ (k : ℕ) (y : O0 p), D ((p : O0 p) ^ k * y) = (p : O0 p) ^ k * D y := by
    intro k y
    rw [Derivation.leibniz, Derivation.leibniz_pow]
    have : D (p : O0 p) = 0 := by
      have := D.map_algebraMap (p : ℤ)
      simpa using this
    simp [this]
  rw [hD, hD] at heq
  have hp0 : (p : O0 p) ≠ 0 := (primeP p).ne_zero
  have h2 : (p : O0 p) ^ (c + a) * ((p : O0 p) * (g0 * D f0 - f0 * D g0)) =
      (p : O0 p) ^ (c + a) * (g0 * f0) := by
    rw [pow_add]; linear_combination heq
  have h3 := mul_left_cancel₀ (pow_ne_zero _ hp0) h2
  have h4 : (p : O0 p) ∣ g0 * f0 := ⟨_, h3.symm⟩
  rcases (primeP p).dvd_or_dvd h4 with h | h
  · exact hg0 h
  · exact hf0 h

theorem q_not_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x}),
      b ^ p ≠ algebraMap (O0 p) Ω (qO p) := by
  intro p _ Ω _ _ h b hb hbp
  have hp : p.Prime := Fact.out
  haveI : CharZero Ω := Basic.charZero_of_isClo h
  obtain ⟨D, hDq, hDr⟩ := exists_derivation_fix_q_kill_padicInt p
  obtain ⟨E, hE⟩ := derExt p Ω h D
  have hEr : ∀ r : ℤ_[p], E (algebraMap (O0 p) Ω (algebraMap ℤ_[p] (O0 p) r)) = 0 := by
    intro r; rw [hE, hDr, map_zero]
  have hEa := derAlg p Ω h E hEr
  have hq0 : algebraMap (O0 p) Ω (qO p) ≠ 0 :=
    ((Basic.isUnit_qO p).map (algebraMap (O0 p) Ω)).ne_zero
  have hb0 : b ≠ 0 := by
    rintro rfl; rw [zero_pow hp.ne_zero] at hbp; exact hq0 hbp.symm
  have hpΩ : (p : Ω) ≠ 0 := by exact_mod_cast hp.ne_zero

  have hEb : (p : Ω) * E b = b := by
    have h1 := congrArg E hbp
    rw [Derivation.leibniz_pow, hE, hDq, ← hbp] at h1
    have h2 : b ^ (p - 1) * ((p : Ω) * E b) = b ^ (p - 1) * b := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le]
      rw [nsmul_eq_mul, smul_eq_mul] at h1
      linear_combination h1
    exact mul_left_cancel₀ (pow_ne_zero _ hb0) h2
  obtain ⟨n, a, f, g, ha, hli, hg, hrep⟩ := repr p Ω h b hb
  set φ := algebraMap (O0 p) Ω with hφ
  have hEsum := congrArg E hrep

  rw [Derivation.leibniz, map_sum] at hEsum
  simp only [Derivation.leibniz, hEa _ (ha _), smul_zero, zero_add, smul_eq_mul, hE, mul_zero] at hEsum
  let c : Fin n → O0 p := fun i => g * f i + (p : O0 p) * D g * f i - (p : O0 p) * g * D (f i)

  have hc : ∑ i, c i • a i = 0 := by
    simp only [c, Algebra.smul_def, ← hφ, map_add (f := _), map_sub, map_mul, map_natCast]
    have e1 : ∑ i, (φ g * φ (f i) + (p : Ω) * φ (D g) * φ (f i) - (p : Ω) * φ g * φ (D (f i))) * a i
        = (φ g + (p : Ω) * φ (D g)) * ∑ i, φ (f i) * a i - (p : Ω) * φ g * ∑ i, a i * φ (D (f i)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [e1, ← hrep, ← hEsum]
    linear_combination -(φ g * φ g) * hEb
  have hc' := (Fintype.linearIndependent_iff.1 hli) c hc
  have : ∃ i, f i ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply hb0
    have : φ g * b = 0 := by rw [hrep]; simp [hall]
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd (h.inj (by rw [h0, map_zero])) hg
    · exact h0
  obtain ⟨i, hi⟩ := this
  apply not_eigen p D (f i) g hi hg
  have := hc' i
  simp only [c] at this
  linear_combination -this

end GlobalTheory.K5.NotPow
end

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem series_weight_lower_bound : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (L : Lev g N) (τ : (ZMod g)[X] → GG g N → ℂ), IsSeries τ → ∀ f ∈ sqSet g N, ∃ w : ℝ, conv (zc (τ f)) L.e 1 = (w : ℂ) * L.e 1 ∧ (1 - 1 / (g : ℝ)) * ((torusCard g f : ℝ))⁻¹ ≤ w := by
  intro g hg N L τ hτ f hf
  obtain ⟨V, hV, hchar, hgen, hdim⟩ := hτ.2 f hf
  obtain ⟨h1, hmul, hc1, hcmul, -⟩ := GlobalTheory.T.levelDatum_submonoid_chi_mul_unipotent g N L
  obtain ⟨hproj, he1, -, -⟩ := GlobalTheory.T.subgroupCharacterIdempotent_properties (GG g N) V V.ρ L.Mem L.chi h1 hmul hc1 hcmul
  have hz := (GlobalTheory.T.centralIdempotent_irreducible_character_props (GG g N) V).2.2.2 L.e hproj.1
  have hT : 0 < torusCard g f := ((GlobalTheory.T.squarefreeLabelTorusCard_bounds_and_mul g).1 N f hf).1
  have hr := GlobalTheory.T.rank_levelIdempotent_lower_bound_generic g N V V.ρ hgen L
  have hJ := GlobalTheory.T.card_levelDatum_group_mul_pow g N L
  have hG := GlobalTheory.T.card_generalLinearGroup_primeField g N
  have hGpos : 0 < Fintype.card (GG g N) := Fintype.card_pos
  have hgpos : 0 < g := hg.out.pos
  set k : ℕ := (if L.sharp = true then L.k else 0) with hk
  rw [← hJ, ← hdim] at hG
  have he : L.e 1 = ((Nat.card {u // L.Mem u} : ℂ))⁻¹ := he1
  set J : ℕ := Nat.card {u // L.Mem u}
  set d : ℕ := Module.finrank ℂ V
  set T : ℕ := torusCard g f
  set r : ℕ := rk V.ρ L.e
  have hJ0 : J ≠ 0 := by
    intro h
    rw [hG, h] at hGpos
    simp at hGpos
  have hd0 : d ≠ 0 := by
    intro h
    rw [hG, h] at hGpos
    simp at hGpos
  refine ⟨(r : ℝ) / ((g : ℝ) ^ k * (T : ℝ)), ?_, ?_⟩
  · rw [← hchar, hz, he, hG]
    have a1 : (J : ℂ) ≠ 0 := by exact_mod_cast hJ0
    have a2 : (d : ℂ) ≠ 0 := by exact_mod_cast hd0
    have a3 : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
    have a4 : (g : ℂ) ≠ 0 := by exact_mod_cast hgpos.ne'
    push_cast
    field_simp
  · have a3 : (0 : ℝ) < T := by exact_mod_cast hT
    have a4 : (0 : ℝ) < (g : ℝ) ^ k := by positivity
    rw [le_div_iff₀ (mul_pos a4 a3)]
    calc (1 - 1 / (g : ℝ)) * (T : ℝ)⁻¹ * ((g : ℝ) ^ k * T) = (1 - 1 / (g : ℝ)) * (g : ℝ) ^ k := by
          field_simp
      _ ≤ r := hr

end GlobalTheory.BadShare
end

section

open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem conv_comm_of_classFun {G : Type} [Group G] [Fintype G] (e : G → ℂ) (he : ∀ x y, e (x * y) = e (y * x))
    (a : G → ℂ) : conv e a = conv a e := by
  funext x
  simp only [conv]
  refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight x)) _ _ fun y => ?_
  simp only [Equiv.trans_apply, Equiv.inv_apply, Equiv.coe_mulRight]
  rw [mul_comm, he (y⁻¹ * x)⁻¹ x]
  congr 2
  group

theorem conv_finsetSum_finsetSum {G κ : Type} [Group G] [Fintype G] (s t : Finset κ) (a b : κ → G → ℂ) :
    conv (∑ i ∈ s, a i) (∑ j ∈ t, b j) = ∑ i ∈ s, ∑ j ∈ t, conv (a i) (b j) := by
  funext x
  simp only [conv, Finset.sum_apply, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem isProj_finsetSum {G κ : Type} [Group G] [Fintype G] (s : Finset κ) (a : κ → G → ℂ) (h : ∀ i ∈ s, IsProj (a i))
    (ho : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → conv (a i) (a j) = 0) : IsProj (∑ i ∈ s, a i) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [conv_finsetSum_finsetSum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single_of_mem i hi fun j hj hne => ho i hi j hj hne.symm, (h i hi).1]

  · simp only [Finset.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun i hi => (h i hi).2 x

theorem eGood_isProj_central : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (m : ℕ) (ι : Type) [Fintype ι] (τ : ι → (ZMod g)[X] → GG g N → ℂ) (ch : ι → Fin m → (ZMod g)ˣ), (∀ v, IsSeries (τ v)) → IsProj (eGood τ ch) ∧ ∀ a, conv (eGood τ ch) a = conv a (eGood τ ch) := by
  intro g _ N m ι _ τ ch hτ
  have hmem : ∀ F ∈ goodSet g N ch, ∀ v, F v ∈ sqSet g N := fun F hF =>
    (good_iff.1 (mem_goodSet_iff_good.1 hF)).1
  refine ⟨isProj_finsetSum _ _ (fun F hF => ?_) fun F hF F' hF' hne => ?_, conv_comm_of_classFun _ fun x y => ?_⟩
  · refine (tens_calculus ι (GG g N) (GG g N)).2.1 _ fun v => ?_
    obtain ⟨V, hV, hχ, -⟩ := (hτ v).2 _ (hmem F hF v)
    rw [← hχ]
    exact (GlobalTheory.T.centralIdempotent_irreducible_character_props _ V).1
  · rw [conv_tens]
    obtain ⟨v, hv⟩ := Function.ne_iff.1 hne
    obtain ⟨V, hV, hχ, -⟩ := (hτ v).2 _ (hmem F hF v)
    obtain ⟨V', hV', hχ', -⟩ := (hτ v).2 _ (hmem F' hF' v)
    have h0 : conv (zc (τ v (F v))) (zc (τ v (F' v))) = 0 := by
      rw [← hχ, ← hχ']
      refine (GlobalTheory.T.centralIdempotent_irreducible_character_props _ V).2.2.1 V' ?_
      rw [hχ, hχ']
      exact fun h => hv ((hτ v).1 (hmem F hF v) (hmem F' hF' v) h)
    funext x
    exact Finset.prod_eq_zero (Finset.mem_univ v) (congrFun h0 (x v))
  · simp only [eGood, Finset.sum_apply, tens]
    refine Finset.sum_congr rfl fun F hF => Finset.prod_congr rfl fun v _ => ?_
    obtain ⟨V, -, hχ, -⟩ := (hτ v).2 _ (hmem F hF v)
    simp only [zc, ← hχ, Pi.mul_apply, mul_inv_rev]
    rw [FDRep.char_mul_comm]

end GlobalTheory.BadShare
end

section

noncomputable section
namespace GlobalTheory.FockDecay
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix

def rectDiag (p q : ℕ) (f : ℕ → ℝ) : Matrix (Fin p) (Fin q) ℂ :=
  Matrix.of fun i j => if (i : ℕ) = (j : ℕ) then ((f i : ℝ) : ℂ) else 0

def diagP (p q : ℕ) (σ : ℕ → ℝ) : Mat p q :=
  Matrix.fromBlocks 0 (rectDiag p q σ) (rectDiag p q σ)ᴴ 0

def tanhDiag (p q : ℕ) (σ : ℕ → ℝ) (t : ℝ) : Mat p q :=
  Matrix.diagonal fun a => (if a.isLeft then 1 else -1) *
    ((σ (posIx a) * Real.tanh (t * σ (posIx a)) : ℝ) : ℂ)

def hypMat (p q : ℕ) (σ : ℕ → ℝ) (t : ℝ) : Mat p q :=
  Matrix.fromBlocks (Matrix.diagonal fun i : Fin p => ((Real.cosh (t * σ i) : ℝ) : ℂ))
    (rectDiag p q fun i => Real.sinh (t * σ i)) (rectDiag p q fun i => Real.sinh (t * σ i))ᴴ
    (Matrix.diagonal fun j : Fin q => ((Real.cosh (t * σ j) : ℝ) : ℂ))

def dil {p q : ℕ} (n : ℕ) (u : Ix p q → ℝ) : Pol p q n 0 →ₗ[ℂ] Pol p q n 0 :=
  ((Real.exp ((∑ l : Ln p q n 0, u l.1) / 2) : ℝ) : ℂ) •
    (MvPolynomial.aeval fun l : Ln p q n 0 =>
      (MvPolynomial.C ((Real.exp (u l.1) : ℝ) : ℂ) * MvPolynomial.X l : Pol p q n 0)).toLinearMap

theorem diagonalElement_mem (p q : ℕ) (σ : ℕ → ℝ) : diagP p q σ ∈ pR p q := pY_mem (rectDiag p q σ)

theorem dil_monomial {p q n : ℕ} (u : Ix p q → ℝ) (α : Ln p q n 0 →₀ ℕ) (c : ℂ) :
    dil n u (MvPolynomial.monomial α c) =
      ((Real.exp (∑ l : Ln p q n 0, ((α l : ℝ) + 1 / 2) * u l.1) : ℝ) : ℂ) • MvPolynomial.monomial α c := by
  have h : Real.exp (∑ l : Ln p q n 0, ((α l : ℝ) + 1 / 2) * u l.1) =
      Real.exp ((∑ l : Ln p q n 0, u l.1) / 2) * ∏ l : Ln p q n 0, Real.exp (u l.1) ^ α l := by
    simp only [← Real.exp_nat_mul, ← Real.exp_sum, ← Real.exp_add, Finset.sum_div, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [h, Complex.ofReal_mul, mul_smul, dil, LinearMap.smul_apply, AlgHom.toLinearMap_apply,
    MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), MvPolynomial.monomial_eq,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  congr 1
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, MvPolynomial.smul_eq_C_mul,
    MvPolynomial.algebraMap_eq, Complex.ofReal_prod, Complex.ofReal_pow]
  ring

theorem dil_dil_neg {p q n : ℕ} (u : Ix p q → ℝ) (Φ : Pol p q n 0) : dil n u (dil n (-u) Φ) = Φ := by
  induction Φ using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add (f := _), map_add (f := _), hP, hQ]
  | monomial α c =>
    rw [dil_monomial, map_smul, dil_monomial, smul_smul, ← Complex.ofReal_mul, ← Real.exp_add,
      ← Finset.sum_add_distrib]
    simp

theorem dil_zero {p q n : ℕ} (Φ : Pol p q n 0) : dil n 0 Φ = Φ := by
  induction Φ using MvPolynomial.induction_on' with
  | add P Q hP hQ => rw [map_add (f := _), hP, hQ]
  | monomial α c => rw [dil_monomial]; simp

end GlobalTheory.FockDecay
end
end
