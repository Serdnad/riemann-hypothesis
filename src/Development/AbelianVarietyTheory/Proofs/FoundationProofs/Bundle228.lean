module

public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle004
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle209
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle175
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet

@[expose] public section

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.CurveLattice

theorem exists_periodPair_of_im_ne_zero {K : Type} [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (σ : K →+* ℂ) (a : 𝓞 K) (ha : (σ (a : K)).im ≠ 0) {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    ∃ L : PeriodPair, ∀ z, z ∈ L.lattice ↔ ∃ a ∈ I, z = σ (a : K) := by
  have hr : Module.finrank ℤ I = 2 :=
    (Ideal.finrank_eq_finrank (RingOfIntegers.basis K) I hI).trans ((RingOfIntegers.rank K).trans hK)
  let b : Module.Basis (Fin 2) ℤ I := Module.finBasisOfFinrankEq ℤ _ hr
  have hs : ∀ x : I, σ ((x : 𝓞 K) : K) =
      b.repr x 0 * σ ((b 0 : 𝓞 K) : K) + b.repr x 1 * σ ((b 1 : 𝓞 K) : K) := by
    intro x
    have := congrArg (fun x : I => σ ((x : 𝓞 K) : K)) (b.sum_repr x)
    rw [Fin.sum_univ_two] at this
    simpa using this.symm
  have hb0 : σ ((b 0 : 𝓞 K) : K) ≠ 0 := by
    rw [map_ne_zero]
    have : (b 0 : 𝓞 K) ≠ 0 := fun h => b.ne_zero 0 (Subtype.ext h)
    exact_mod_cast this
  have h0 : (σ ((b 1 : 𝓞 K) : K) * starRingEnd ℂ (σ ((b 0 : 𝓞 K) : K))).im ≠ 0 := by
    intro h0
    have e := hs ⟨a * b 0, I.mul_mem_left a (b 0).2⟩
    have e' := congrArg (fun z => (z * starRingEnd ℂ (σ ((b 0 : 𝓞 K) : K))).im) e
    simp only [RingOfIntegers.coe_eq_algebraMap, map_mul] at e' h0 ha hb0
    rw [add_mul, _root_.mul_assoc, _root_.mul_assoc, _root_.mul_assoc, Complex.mul_conj, Complex.add_im,
      Complex.mul_im, Complex.mul_im, Complex.mul_im, h0] at e'
    simp [ha, hb0] at e'
  refine ⟨⟨σ ((b 0 : 𝓞 K) : K), σ ((b 1 : 𝓞 K) : K), ?_⟩, fun z => ?_⟩
  · rw [LinearIndependent.pair_iff]
    intro x y e
    have e1 := congrArg Complex.re e
    have e2 := congrArg Complex.im e
    simp at e1 e2 h0
    constructor
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ ((b 1 : 𝓞 K) : K)).im * e1 - (σ ((b 1 : 𝓞 K) : K)).re * e2
    · refine mul_right_cancel₀ h0 ?_
      linear_combination (σ ((b 0 : 𝓞 K) : K)).re * e2 - (σ ((b 0 : 𝓞 K) : K)).im * e1
  · rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨_, (m • b 0 + n • b 1).2, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, _, (hs ⟨x, hx⟩).symm⟩

theorem eisG_eq_periodPair_G (Λ : AddSubgroup ℂ) (L : PeriodPair) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) {k : ℕ} (hk : k ≠ 0) :
    eisG Λ k = L.G (2 * k) := by
  have e1 := tsum_subtype {w : ℂ | w ∈ Λ ∧ w ≠ 0} (fun w : ℂ => 1 / w ^ (2 * k))
  have e2 := tsum_subtype (L.lattice : Set ℂ) (fun w : ℂ => (w ^ (2 * k))⁻¹)
  refine e1.trans (Eq.trans (tsum_congr fun w => ?_) e2.symm)
  by_cases hw : w = 0
  · subst hw
    simp [Set.indicator, hk]
  · simp [Set.indicator, hw, h]

theorem discr_ne_zero (Λ : AddSubgroup ℂ) (L : PeriodPair) (h : ∀ z, z ∈ Λ ↔ z ∈ L.lattice) : TaylorLogMetric.discr Λ ≠ 0 := by
  have := g₂_cube_sub_g₃_sq_ne_zero L
  rw [TaylorLogMetric.discr, g2, g3, eisG_eq_periodPair_G Λ L h two_ne_zero, eisG_eq_periodPair_G Λ L h three_ne_zero]
  exact this

theorem mem_lamOf_iff (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ z : ℂ) :
    z ∈ lamOf D cc δ ↔ ∃ c ∈ cc, z = δ * D.host.φ₀ (((c : D.host.K) : D.host.E)) := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem x hx => exact hx
    | zero => exact ⟨0, cc.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨c', hc', rfl⟩ := hy
      exact ⟨c + c', cc.add_mem hc hc', by simp [mul_add]⟩
    | neg x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact ⟨-c, cc.neg_mem hc, by simp⟩
  · intro hz
    exact AddSubgroup.subset_closure hz

theorem exists_periodPair_one (D : D7) {cc : Ideal (𝓞 D.host.K)} (hc : cc ≠ ⊥) :
    ∃ L : PeriodPair, ∀ z : ℂ, z ∈ lamOf D cc 1 ↔ z ∈ L.lattice := by
  have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq
  have hd : 0 < D.host.d := D.host.hyp.2.1.pos
  have hK : Module.finrank ℚ D.host.K = 2 := Formalism.FrobeniusOrbits.SplitK.finrank_K hd hb
  let s : D.host.K := ⟨D.host.sqrtMinusD, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hs : s ^ 2 = -(D.host.d : D.host.K) := Subtype.ext (by simpa [s] using hb)
  have hint : IsIntegral ℤ s := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hs]
    exact (isIntegral_natCast _).neg
  let σ : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  have him : (σ (((⟨s, hint⟩ : 𝓞 D.host.K) : 𝓞 D.host.K) : D.host.K)).im ≠ 0 := by
    intro h0
    change (σ s).im = 0 at h0
    have e : σ s ^ 2 = -(D.host.d : ℂ) := by rw [← map_pow, hs]; simp
    have e' := congrArg Complex.re e
    simp only [pow_two, Complex.mul_re, h0, Complex.neg_re, Complex.natCast_re] at e'
    have : (0 : ℝ) < D.host.d := by exact_mod_cast hd
    nlinarith [mul_self_nonneg (σ s).re]
  obtain ⟨L, hL⟩ := exists_periodPair_of_im_ne_zero hK σ (⟨s, hint⟩ : 𝓞 D.host.K) him hc
  refine ⟨L, fun z => ?_⟩
  rw [hL, mem_lamOf_iff]
  simp only [one_mul]
  rfl

theorem exists_periodPair_lamOf : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ →
    ∃ L : PeriodPair, ∀ z : ℂ, z ∈ lamOf D cc δ ↔ z ∈ L.lattice := by
  intro D cc δ h
  obtain ⟨L, hL⟩ := exists_periodPair_one D h.1.1
  have hδ : δ ≠ 0 := by
    rintro rfl
    have e : (0 : ℂ) ^ 12 = TaylorLogMetric.discr (lamOf D cc 1) := h.2
    exact discr_ne_zero _ L hL (by rw [← e]; simp)
  have hind : LinearIndependent ℝ ![δ * L.ω₁, δ * L.ω₂] := by
    have h1 := LinearIndependent.pair_iff.1 L.indep
    rw [LinearIndependent.pair_iff]
    intro x y e
    refine h1 x y (mul_left_cancel₀ hδ ?_)
    simp only [Complex.real_smul] at e ⊢
    linear_combination e
  refine ⟨⟨δ * L.ω₁, δ * L.ω₂, hind⟩, fun z => ?_⟩
  rw [mem_lamOf_iff, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨m, n, e⟩ := PeriodPair.mem_lattice.1 ((hL _).1 ((mem_lamOf_iff D cc 1 _).2 ⟨c, hc, rfl⟩))
    exact ⟨m, n, by linear_combination δ * e⟩
  · rintro ⟨m, n, rfl⟩
    obtain ⟨c, hc, e⟩ := (mem_lamOf_iff D cc 1 _).1 ((hL _).2 (PeriodPair.mem_lattice.2 ⟨m, n, rfl⟩))
    exact ⟨c, hc, by linear_combination δ * e⟩

end GlobalTheory.CurveLattice
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem not_dvd_of_prime_of_eq_neg_one {M p : ℕ} (hp : p.Prime) (h : (p : ZMod M) = -1) :
    ¬ p ∣ M := by
  intro hpM
  have h1 : ((p + 1 : ℕ) : ZMod M) = 0 := by push_cast; rw [h]; ring
  have h1' : M ∣ p + 1 := (CharP.cast_eq_zero_iff (ZMod M) M (p + 1)).mp h1
  have : p ∣ p + 1 := hpM.trans h1'
  have : p ∣ 1 := (Nat.dvd_add_right (dvd_refl p)).mp this
  exact hp.one_lt.ne' (Nat.dvd_one.mp this)

theorem lseries_ne_zero_edge : ∀ (M : ℕ) (b ω : ℕ → ℂ) (C : ℝ) (Λ : ℂ → ℂ), 0 < M → b 1 = 1 → b 0 = 0 → (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime M → b n = 0) → (∀ p r : ℕ, p.Prime → ¬ p ∣ M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) → (∀ n : ℕ, ‖b n‖ ^ 2 ≤ C * n) → (∀ s : ℝ, 0 < s → Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s)) → (∀ s : ℝ, 0 < s → s ≤ 1 → s * ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) ≤ C) → (∀ p : ℕ, p.Prime → ¬ p ∣ M → (p : ZMod M) = -1 → (b p).re = 0) → Differentiable ℂ Λ → (∀ s : ℝ, 0 < s → LSeries b ((1 + s : ℝ) : ℂ) = Λ ((1 + s : ℝ) : ℂ)) → ∀ w : ℝ, 1 ≤ w → Λ w ≠ 0 := by
  intro M b ω C Λ hM hb1 hb0 hmul hcop hrec hC hsum hsC hre hdiff hL w hw
  have G := fun s hs => GlobalTheory.T.global_positivity_ineq_multiplicative_coeff M b ω s C hs hb1 hb0 hmul hcop hrec hC (hsum s hs)
  rcases hw.lt_or_eq with hw | rfl
  · intro h0
    have hs : 0 < w - 1 := by linarith
    have := G (w - 1) hs 0
    have e : ((1 + (w - 1) : ℝ) : ℂ) = (w : ℂ) := by push_cast; ring
    rw [hL _ hs, e, h0] at this
    norm_num at this
  · intro h0
    rw [Complex.ofReal_one] at h0

    have hO := (hdiff 1).isBigO_sub
    have ht : Tendsto (fun s : ℝ => ((1 + s : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have : Continuous fun s : ℝ => ((1 + s : ℝ) : ℂ) := by fun_prop
      have h := this.tendsto 0
      simp only [add_zero, Complex.ofReal_one] at h
      exact h.mono_left nhdsWithin_le_nhds
    obtain ⟨c, hc, hcw⟩ := (hO.comp_tendsto ht).exists_pos
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s ≤ 1 ∧ ‖Λ ((1 + s : ℝ) : ℂ)‖ ≤ c * s := by
      have h1 := hcw.bound
      have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s := self_mem_nhdsWithin
      have h3 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ≤ 1 :=
        nhdsWithin_le_nhds (Iic_mem_nhds (by norm_num : (0:ℝ) < 1))
      filter_upwards [h1, h2, h3] with s h1 h2 h3
      refine ⟨h2, h3, ?_⟩
      simp only [Function.comp, h0, sub_zero] at h1
      have : ((1 + s : ℝ) : ℂ) - 1 = (s : ℂ) := by push_cast; ring
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h2] at h1
      exact h1

    have hC0 : 0 ≤ C := by
      have := hsC 1 one_pos le_rfl
      refine le_trans ?_ this
      exact mul_nonneg zero_le_one (tsum_nonneg fun n => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    set B : ℝ := 4 * c ^ 2 * C with hB
    let T : ℕ → Finset ℕ := fun X => (Finset.range X).filter (fun p => p.Prime ∧ (p : ZMod M) = -1)

    have key : ∀ X : ℕ, ∀ s : ℝ, 0 < s → s ≤ 1 → ‖Λ ((1 + s : ℝ) : ℂ)‖ ≤ c * s →
        ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + s) ≤ B := by
      intro X s hs hs1 hΛ
      set S := ∑' n : ℕ, ‖b n‖ ^ 2 / (n : ℝ) ^ (1 + s) with hS
      have hS0 : 0 ≤ S := tsum_nonneg fun n => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have g := G s hs X
      rw [hL s hs] at g
      set F := (Finset.range X).filter (fun p => p.Prime ∧ ¬ p ∣ M)
      have hsub : T X ⊆ F := by
        intro p hp
        simp only [T, F, Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, hp.2.1, not_dvd_of_prime_of_eq_neg_one hp.2.1 hp.2.2⟩
      have h1 : ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + s) ≤ ∑ p ∈ T X, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) := by
        apply Finset.sum_le_sum
        intro p hp
        simp only [T, Finset.mem_filter] at hp
        have hre' := hre p hp.2.1 (not_dvd_of_prime_of_eq_neg_one hp.2.1 hp.2.2) hp.2.2
        have : (1 : ℝ) ≤ ‖1 + b p‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp only [Complex.add_re, Complex.one_re, hre', Complex.add_im, Complex.one_im]
          nlinarith [sq_nonneg (b p).im]
        exact div_le_div_of_nonneg_right this (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      have h2 : ∑ p ∈ T X, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) ≤ ∑ p ∈ F, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => div_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      have h3 := Real.add_one_le_exp (∑ p ∈ F, ‖1 + b p‖ ^ 2 / (p : ℝ) ^ (1 + s))
      have hL2 : ‖Λ ((1 + s : ℝ) : ℂ)‖ ^ 2 ≤ (c * s) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hΛ 2
      have hsS := hsC s hs hs1
      have h4 : 2 * (1 + 1 / s) * ‖Λ ((1 + s : ℝ) : ℂ)‖ ^ 2 * S ≤ B := by
        calc 2 * (1 + 1 / s) * ‖Λ ((1 + s : ℝ) : ℂ)‖ ^ 2 * S
            ≤ 2 * (1 + 1 / s) * (c * s) ^ 2 * S := by gcongr
          _ = 2 * (s + 1) * c ^ 2 * (s * S) := by field_simp
          _ ≤ 2 * (1 + 1) * c ^ 2 * C := by gcongr
          _ = B := by rw [hB]; ring
      linarith

    have hT : ∀ X : ℕ, ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ≤ B := by
      intro X
      have ht : Tendsto (fun s : ℝ => ∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + s)) (𝓝[>] (0 : ℝ))
          (𝓝 (∑ p ∈ T X, (1 : ℝ) / (p : ℝ) ^ (1 + (0:ℝ)))) := by
        apply Tendsto.mono_left _ nhdsWithin_le_nhds
        apply tendsto_finsetSum
        intro p hp
        simp only [T, Finset.mem_filter] at hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.2.1.pos
        apply Continuous.tendsto
        exact continuous_const.div (continuous_const.rpow (continuous_const.add continuous_id) (fun _ => Or.inl hp0.ne'))
          (fun _ => (Real.rpow_pos_of_pos hp0 _).ne')
      simp only [add_zero, Real.rpow_one] at ht
      apply le_of_tendsto ht
      filter_upwards [hev] with s hs
      exact key X s hs.1 hs.2.1 hs.2.2
    apply GlobalTheory.T.not_summable_inv_primes_congr_neg_one M hM
    apply summable_of_sum_range_le (c := B)
    · intro n; split_ifs <;> positivity
    · intro X
      rw [← Finset.sum_filter]
      exact hT X

end GlobalTheory.EisM
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory

theorem hermite_right_factor_prime_det : ∀ (p : ℕ), p.Prime → ∀ (m : Matrix (Fin 2) (Fin 2) ℤ), (p : ℤ) ∣ m.det → (∃ y : Matrix (Fin 2) (Fin 2) ℤ, m = y * !![(p : ℤ), 0; 0, 1]) ∨ ∃ k : ℕ, k < p ∧ ∃ y : Matrix (Fin 2) (Fin 2) ℤ, m = y * !![1, (k : ℤ); 0, (p : ℤ)] := by
  intro p hp m hdet
  haveI := Fact.mk hp
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ℤ, m = !![a, b; c, d] :=
    ⟨m 0 0, m 0 1, m 1 0, m 1 1, by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  rw [Matrix.det_fin_two_of] at hdet
  have hdetZ : (a : ZMod p) * d = b * c := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (a * d - b * c) p).2 hdet
    push_cast at this
    linear_combination this
  have fin : ∀ k : ℕ, k < p → (k : ZMod p) * a = b → (k : ZMod p) * c = d →
      ∃ k : ℕ, k < p ∧ ∃ y : Matrix (Fin 2) (Fin 2) ℤ, !![a, b; c, d] = y * !![1, (k : ℤ); 0, (p : ℤ)] := by
    intro k hk h1 h2
    obtain ⟨u, hu⟩ : (p : ℤ) ∣ b - k * a := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h1]; ring
    obtain ⟨v, hv⟩ : (p : ℤ) ∣ d - k * c := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h2]; ring
    refine ⟨k, hk, !![a, u; c, v], ?_⟩
    rw [Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith
  by_cases ha : (a : ZMod p) = 0
  · by_cases hc : (c : ZMod p) = 0
    · left
      obtain ⟨a', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).1 ha
      obtain ⟨c', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd c p).1 hc
      refine ⟨!![a', b; c', d], ?_⟩
      rw [Matrix.mul_fin_two]
      ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
    · right
      refine fin ((d : ZMod p) * (c : ZMod p)⁻¹).val (ZMod.val_lt _) ?_ ?_
      · rw [ZMod.natCast_zmod_val]
        calc (d : ZMod p) * (c : ZMod p)⁻¹ * a = (a * d) * (c : ZMod p)⁻¹ := by ring
          _ = b * c * (c : ZMod p)⁻¹ := by rw [hdetZ]
          _ = b := by rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
      · rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  · right
    refine fin ((b : ZMod p) * (a : ZMod p)⁻¹).val (ZMod.val_lt _) ?_ ?_
    · rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ ha, mul_one]
    · rw [ZMod.natCast_zmod_val]
      calc (b : ZMod p) * (a : ZMod p)⁻¹ * c = (b * c) * (a : ZMod p)⁻¹ := by ring
        _ = (a * d) * (a : ZMod p)⁻¹ := by rw [hdetZ]
        _ = d := by rw [mul_comm (a : ZMod p) d, mul_assoc, mul_inv_cancel₀ ha, mul_one]

end GlobalTheory
end

section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory

theorem sl2_right_factor_of_coprime_factorizations :
    ∀ (a c : ℤ), IsCoprime a c → c ≠ 0 → ∀ (y y' β β' : Matrix (Fin 2) (Fin 2) ℤ),
      y.det = a → y'.det = a → β.det = c → β'.det = c → y * β = y' * β' →
      ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) * β = β' := by
  intro a c hac hc y y' β β' hy hy' hβ hβ' hyβ
  set P : Matrix (Fin 2) (Fin 2) ℤ := β' * adjugate β with hP
  set Q : Matrix (Fin 2) (Fin 2) ℤ := adjugate y' * y with hQ
  have hPQ : a • P = c • Q := by
    have h1 : adjugate y' * y * β = a • β' := by
      rw [Matrix.mul_assoc, hyβ, ← Matrix.mul_assoc, adjugate_mul, hy', Matrix.smul_mul, Matrix.one_mul]
    have h2 : β * adjugate β = c • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
      rw [mul_adjugate, hβ]
    calc a • P = (a • β') * adjugate β := by rw [hP, Matrix.smul_mul]
      _ = adjugate y' * y * β * adjugate β := by rw [h1]
      _ = Q * (β * adjugate β) := by rw [hQ, Matrix.mul_assoc]
      _ = c • Q := by rw [h2, Matrix.mul_smul, Matrix.mul_one]
  have hdiv : ∀ i j, c ∣ P i j := by
    intro i j
    have := congrFun (congrFun hPQ i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact hac.symm.dvd_of_dvd_mul_left ⟨Q i j, this⟩
  choose M hM using hdiv
  set Mm : Matrix (Fin 2) (Fin 2) ℤ := Matrix.of M with hMm
  have hPM : P = c • Mm := by
    ext i j; simp [hMm, hM i j]
  have hMβ : Mm * β = β' := by
    have : c • (Mm * β) = c • β' := by
      rw [← Matrix.smul_mul, ← hPM, hP, Matrix.mul_assoc, adjugate_mul, hβ, Matrix.mul_smul, Matrix.mul_one]
    ext i j
    have := congrFun (congrFun this i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hc this
  have hdet : Mm.det = 1 := by
    have h1 : P.det = c * c := by
      rw [hP, det_mul, det_adjugate, hβ, hβ']
      simp
    rw [hPM, det_smul] at h1
    simp at h1
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
    have : c ^ 2 * Mm.det = c ^ 2 * 1 := by rw [h1]; ring
    exact mul_left_cancel₀ hc2 this
  exact ⟨⟨Mm, hdet⟩, hMβ⟩

end GlobalTheory
end
