module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle111
public import Formalism.LatticeTheta.Statement
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.Different
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle001
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle122
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle004
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
import Mathlib.Analysis.Fourier.Notation

@[expose] public section

section

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzTR

section
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem inner_remb_eq_trace (a b : F) :
    ⟪remb F a, remb F b⟫ = ((Algebra.trace ℚ F (a * b) : ℚ) : ℝ) := by
  rw [GlobalTheory.trace_eq_sum_realEmbeddings, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [map_mul, mul_comm]

theorem remb_mem_dual_latOf_iff (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0) (ν : F) :
    remb F ν ∈ Formalism.H.dual (latOf N) ↔ ν ∈ FractionalIdeal.dual ℤ ℚ N := by
  rw [Formalism.H.dual, LinearMap.BilinForm.mem_dualSubmodule, FractionalIdeal.mem_dual hN]
  constructor
  · intro h a ha
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp (h (remb F a) ((mem_latOf N _).mpr ⟨a, ha, rfl⟩))
    refine ⟨z, ?_⟩
    rw [Algebra.traceForm_apply]
    have : ((z : ℚ) : ℝ) = ((Algebra.trace ℚ F (ν * a) : ℚ) : ℝ) := by
      have h2 : ((z : ℤ) : ℝ) = ⟪remb F ν, remb F a⟫ := by simpa using hz
      rw [inner_remb_eq_trace] at h2
      exact_mod_cast h2
    exact_mod_cast this
  · intro h y hy
    obtain ⟨a, ha, rfl⟩ := (mem_latOf N y).mp hy
    obtain ⟨z, hz⟩ := h a ha
    rw [Algebra.traceForm_apply] at hz
    refine Submodule.mem_one.mpr ⟨z, ?_⟩
    rw [show (innerₗ (RSp F)) (remb F ν) (remb F a) = ⟪remb F ν, remb F a⟫ from rfl,
      inner_remb_eq_trace, ← hz]
    simp

theorem exists_remb_eq_of_mem_dual {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ F)
    (N : FractionalIdeal (𝓞 F)⁰ F) (hbN : ∀ i, b i ∈ N) (μ : RSp F)
    (hμ : μ ∈ Formalism.H.dual (latOf N)) : ∃ ν : F, remb F ν = μ := by
  set B := Algebra.traceForm ℚ F
  have hB : B.Nondegenerate := traceForm_nondegenerate ℚ F
  set b' := B.dualBasis hB b
  have hdel : ∀ i j, Algebra.trace ℚ F (b' j * b i) = if i = j then 1 else 0 := fun i j => by
    have := LinearMap.BilinForm.apply_dualBasis_left hB b j i
    rwa [Algebra.traceForm_apply] at this
  have hc : ∀ i, ∃ z : ℤ, ⟪μ, remb F (b i)⟫ = z := fun i => by
    have := (LinearMap.BilinForm.mem_dualSubmodule _).mp hμ (remb F (b i))
      ((mem_latOf N _).mpr ⟨b i, hbN i, rfl⟩)
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp this
    exact ⟨z, by simpa using hz.symm⟩
  choose c hc using hc
  set ν : F := ∑ j, (c j : ℚ) • b' j
  have hνb : ∀ i, ⟪remb F ν, remb F (b i)⟫ = c i := fun i => by
    rw [inner_remb_eq_trace]
    have : Algebra.trace ℚ F (ν * b i) = c i := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [ν, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, hdel, smul_eq_mul,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [this]; simp
  have hind : LinearIndependent ℝ (fun i => remb F (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (fun w => ⟪w, remb F (b' j)⟫) hg
    simp only [sum_inner, real_inner_smul_left, inner_remb_eq_trace, inner_zero_left] at this
    simp only [mul_comm (b _) (b' j), hdel] at this
    rw [Finset.sum_eq_single j (fun i _ hi => by rw [if_neg hi]; simp) (by simp)] at this
    simpa using this
  have hcard : Fintype.card ι = Module.finrank ℝ (RSp F) := by
    rw [finrank_euclideanSpace, GlobalTheory.card_realEmbeddings, Module.finrank_eq_card_basis b]
  haveI : Nonempty ι := b.index_nonempty
  let E := basisOfLinearIndependentOfCardEqFinrank hind hcard
  have hz : innerₛₗ ℝ (μ - remb F ν) = 0 := E.ext fun i => by
    simp [E, inner_sub_left, hνb, hc]
  have h0 := LinearMap.congr_fun hz (μ - remb F ν)
  have h1 : ⟪μ - remb F ν, μ - remb F ν⟫ = 0 := by
    rw [LinearMap.zero_apply] at h0; exact h0
  rw [inner_self_eq_zero, sub_eq_zero] at h1
  exact ⟨ν, h1.symm⟩

end

theorem dual_latOf_eq_latOf_traceDual (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F) (hN : N ≠ 0) :
    Formalism.H.dual (latOf N) = latOf (FractionalIdeal.dual ℤ ℚ N) := by
  classical
  ext μ
  constructor
  · intro hμ
    rw [mem_latOf]
    let I : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 N hN
    have hbN : ∀ i, basisOfFractionalIdeal F I i ∈ N := fun i => by
      have := (mem_span_basisOfFractionalIdeal F (I := I) (x := basisOfFractionalIdeal F I i)).mp
        (Submodule.subset_span ⟨i, rfl⟩)
      simpa [I] using this
    obtain ⟨ν, hν⟩ := exists_remb_eq_of_mem_dual (basisOfFractionalIdeal F I) N hbN μ hμ
    subst hν
    exact ⟨ν, (remb_mem_dual_latOf_iff N hN ν).mp hμ, rfl⟩
  · intro hμ
    obtain ⟨ν, hν, rfl⟩ := (mem_latOf _ μ).mp hμ
    exact (remb_mem_dual_latOf_iff N hN ν).mpr hν

end GlobalTheory.LipschitzTR
end
end

section

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

namespace GlobalTheory.LipschitzTR

theorem span_range_remb (F : Type) [Field F] [NumberField F] :
    Submodule.span ℝ (Set.range (remb F)) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hli := (linearIndependent_monoidHom F ℝ).comp
    (fun τ : F →+* ℝ => (τ : F →* ℝ)) (fun τ₁ τ₂ h => by
      ext a; exact congrArg (fun g : F →* ℝ => g a) h)
  have hsum : ∀ a : F, ∑ τ : F →+* ℝ, f (EuclideanSpace.single τ 1) * τ a = 0 := by
    intro a
    have h1 : f (remb F a) = 0 := hle (Submodule.subset_span ⟨a, rfl⟩)
    have h2 : remb F a = ∑ τ : F →+* ℝ, τ a • EuclideanSpace.single τ (1 : ℝ) := by
      ext σ
      simp [PiLp.single_apply, Pi.single_apply]

    rw [h2, map_sum] at h1
    simpa [mul_comm] using h1
  have hcoef := Fintype.linearIndependent_iff.mp hli (fun τ => f (EuclideanSpace.single τ 1))
    (by
      funext a
      simpa [Finset.sum_apply] using hsum a)
  apply hf0
  apply LinearMap.ext
  intro x
  have hx : x = ∑ τ : F →+* ℝ, x τ • EuclideanSpace.single τ (1 : ℝ) := by
    ext σ
    simp [PiLp.single_apply, Pi.single_apply]

  rw [hx, map_sum]
  simp [hcoef]

end GlobalTheory.LipschitzTR

namespace GlobalTheory.LipschitzTR

theorem isZLattice_latOf : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F), N ≠ 0 → ∀ [DiscreteTopology (latOf N)],
    IsZLattice ℝ (latOf N) := by
  intro F _ _ _ N hN _
  refine ⟨?_⟩
  rw [eq_top_iff, ← span_range_remb F, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have hc : ∃ c ∈ N, c ≠ 0 := by
    by_contra h
    push_neg at h
    apply hN
    ext x
    rw [FractionalIdeal.mem_zero_iff]
    exact ⟨h x, fun hx => hx ▸ (N : Submodule (𝓞 F) F).zero_mem⟩
  obtain ⟨c, hcN, hc0⟩ := hc
  obtain ⟨y, hy0, hint⟩ := exists_integral_multiples ℤ ℚ (L := F) {a / c}
  let α : 𝓞 F := ⟨y • (a / c), hint _ (Finset.mem_singleton_self _)⟩
  have hmem : (y : F) * a ∈ N := by
    have h := Submodule.smul_mem (N : Submodule (𝓞 F) F) α hcN
    have he : α • c = (y : F) * a := by
      rw [Algebra.smul_def]
      show (y • (a / c)) * c = (y : F) * a
      rw [zsmul_eq_mul]
      field_simp
    rw [he] at h
    exact h
  have hy : (y : ℝ) ≠ 0 := by exact_mod_cast hy0
  have heq : remb F a = (y : ℝ)⁻¹ • remb F ((y : F) * a) := by
    ext τ
    simp only [remb_apply, PiLp.smul_apply, smul_eq_mul, map_mul, map_intCast]
    field_simp
  rw [heq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ((mem_latOf N _).2 ⟨_, hmem, rfl⟩))

end GlobalTheory.LipschitzTR
end

section

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzTR

theorem mul_im_pos_of_sign_mul_pos {w : ℂ} {t : ℝ} (h : 0 < (SignType.sign w.im : ℝ) * t) :
    0 < t * w.im := by
  rcases lt_trichotomy w.im 0 with hw | hw | hw
  · rw [sign_neg hw] at h
    simp at h
    nlinarith
  · rw [hw, sign_zero] at h
    simp at h
  · rw [sign_pos hw] at h
    simp at h
    positivity

theorem norm_lipschitzOneVariableKernel_le (k : ℕ) (w : ℂ) (t : ℝ) :
    ‖phi1 k w t‖ ≤ |t| ^ (k - 1) * Real.exp (-(2 * Real.pi * |w.im|) * |t|) := by
  unfold phi1
  split_ifs with h
  · have hp := mul_im_pos_of_sign_mul_pos h
    have habs : |t| * |w.im| = t * w.im := by rw [← abs_mul]; exact abs_of_pos hp
    have hre : (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) * w).re = -(2 * Real.pi * |w.im|) * |t| := by
      simp [Complex.mul_re]
      linear_combination (-2 * Real.pi) * habs
    rw [norm_mul, Complex.norm_exp, hre, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  · simp only [norm_zero]
    positivity

theorem abs_pow_mul_exp_le (n : ℕ) {a : ℝ} (ha : 0 < a) (t : ℝ) :
    |t| ^ n * Real.exp (-a * |t|) ≤ (n.factorial * (2 / a) ^ n) * Real.exp (-(a / 2) * |t|) := by
  have h := Real.pow_div_factorial_le_exp (a / 2 * |t|) (by positivity) n
  rw [div_le_iff₀ (by positivity)] at h
  have h1 : |t| ^ n ≤ n.factorial * (2 / a) ^ n * Real.exp (a / 2 * |t|) := by
    calc |t| ^ n = (2 / a) ^ n * (a / 2 * |t|) ^ n := by
          rw [← mul_pow]; congr 1; field_simp
      _ ≤ (2 / a) ^ n * (Real.exp (a / 2 * |t|) * n.factorial) := by gcongr
      _ = _ := by ring
  calc |t| ^ n * Real.exp (-a * |t|)
      ≤ (n.factorial * (2 / a) ^ n * Real.exp (a / 2 * |t|)) * Real.exp (-a * |t|) := by gcongr
    _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring

theorem continuous_lipschitzOneVariableKernel {k : ℕ} (hk : 2 ≤ k) {w : ℂ} (hw : w.im ≠ 0) : Continuous (phi1 k w) := by
  have hg : Continuous fun t : ℝ =>
      ((|t| ^ (k - 1) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t * w) := by fun_prop
  show Continuous fun t => if 0 < (SignType.sign w.im : ℝ) * t then
    ((|t| ^ (k - 1) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * t * w) else 0
  refine continuous_if (fun a ha => ?_) hg.continuousOn continuous_const.continuousOn
  have h0 := frontier_lt_subset_eq (continuous_const (y := (0 : ℝ)))
    (continuous_const.mul continuous_id (f := fun _ : ℝ => (SignType.sign w.im : ℝ))) ha
  simp only [Set.mem_setOf_eq, id] at h0
  have ha0 : a = 0 := by
    rcases mul_eq_zero.1 h0.symm with h | h
    · exfalso
      rcases lt_trichotomy w.im 0 with h' | h' | h'
      · rw [sign_neg h'] at h; norm_num at h
      · exact hw h'
      · rw [sign_pos h'] at h; norm_num at h
    · exact h
  subst ha0
  have : k - 1 ≠ 0 := by omega
  simp [this]

end GlobalTheory.LipschitzTR

namespace GlobalTheory.LipschitzTR

theorem norm_le_sum_abs {F : Type} [Field F] [NumberField F] (v : RSp F) :
    ‖v‖ ≤ ∑ τ, |v τ| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun _ _ => abs_nonneg _, ?_⟩
  simpa [Real.norm_eq_abs] using
    Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun τ => |v τ|) fun _ _ => abs_nonneg _

theorem continuous_and_isBigO_rpow_Phi (F : Type) [Field F] [NumberField F] (k : ℕ) (hk : 2 ≤ k)
    (z : (F →+* ℝ) → ℂ) (hz : ∀ τ, (z τ).im ≠ 0) :
    Continuous (Phi k z) ∧ ∀ b : ℝ, Phi k z =O[Filter.cocompact (RSp F)] fun v => ‖v‖ ^ (-b) := by
  refine ⟨?_, fun b => ?_⟩
  · unfold Phi
    exact continuous_finsetProd _ fun τ _ =>
      (continuous_lipschitzOneVariableKernel hk (hz τ)).comp ((EuclideanSpace.proj τ : RSp F →L[ℝ] ℝ).continuous)
  obtain ⟨c, hc, hcle⟩ : ∃ c > 0, ∀ τ, c ≤ 2 * Real.pi * |(z τ).im| / 2 := by
    rcases isEmpty_or_nonempty (F →+* ℝ) with h | h
    · exact ⟨1, one_pos, fun τ => (IsEmpty.false τ).elim⟩
    · obtain ⟨τ0, hτ0⟩ := Finite.exists_min (fun τ => 2 * Real.pi * |(z τ).im| / 2)
      exact ⟨_, by have := abs_pos.2 (hz τ0); positivity, hτ0⟩
  set K : ℝ := ∏ τ, (((k - 1).factorial : ℝ) * (2 / (2 * Real.pi * |(z τ).im|)) ^ (k - 1)) with hK
  have hbound : ∀ v : RSp F, ‖Phi k z v‖ ≤ K * Real.exp (-c * ‖v‖) := by
    intro v
    have hfac : ∀ τ, ‖phi1 k (z τ) (v τ)‖ ≤
        (((k - 1).factorial : ℝ) * (2 / (2 * Real.pi * |(z τ).im|)) ^ (k - 1)) *
          Real.exp (-c * |v τ|) := by
      intro τ
      have ha : 0 < 2 * Real.pi * |(z τ).im| := by have := abs_pos.2 (hz τ); positivity
      refine (norm_lipschitzOneVariableKernel_le k (z τ) (v τ)).trans ((abs_pow_mul_exp_le (k - 1) ha (v τ)).trans ?_)
      gcongr
      have := hcle τ
      nlinarith [abs_nonneg (v τ)]
    calc ‖Phi k z v‖ = ∏ τ, ‖phi1 k (z τ) (v τ)‖ := by unfold Phi; rw [norm_prod]
      _ ≤ ∏ τ, ((((k - 1).factorial : ℝ) * (2 / (2 * Real.pi * |(z τ).im|)) ^ (k - 1)) *
          Real.exp (-c * |v τ|)) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ _ => hfac τ
      _ = K * Real.exp (-c * ∑ τ, |v τ|) := by
        rw [Finset.prod_mul_distrib, Finset.mul_sum, Real.exp_sum]
      _ ≤ K * Real.exp (-c * ‖v‖) := by
        have hK0 : 0 ≤ K := Finset.prod_nonneg fun τ _ => by positivity
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [norm_le_sum_abs v])) hK0
  have h1 : Phi k z =O[Filter.cocompact (RSp F)] fun v : RSp F => Real.exp (-c * ‖v‖) :=
    Asymptotics.IsBigO.of_bound K (Filter.Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact hbound v)
  have h2 : (fun v : RSp F => Real.exp (-c * ‖v‖)) =O[Filter.cocompact (RSp F)]
      fun v : RSp F => ‖v‖ ^ (-b) :=
    (isLittleO_exp_neg_mul_rpow_atTop hc (-b)).isBigO.comp_tendsto tendsto_norm_cocompact_atTop
  exact h1.trans h2

end GlobalTheory.LipschitzTR
end
end

section

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

namespace GlobalTheory.LipschitzTR

noncomputable def toMixedTR (F : Type) [Field F] [NumberField F] (x : RSp F) :
    mixedEmbedding.mixedSpace F :=
  (fun w => x (InfinitePlace.embedding_of_isReal w.prop), fun _ => 0)

theorem continuous_toMixedTR (F : Type) [Field F] [NumberField F] :
    Continuous (toMixedTR F) := by
  refine Continuous.prodMk (continuous_pi fun w => ?_) continuous_const
  exact (PiLp.continuous_apply 2 _ _)

theorem toMixedTR_remb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : F) :
    toMixedTR F (remb F a) = mixedEmbedding F a := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · simp [toMixedTR, mixedEmbedding.mixedEmbedding_apply_isReal]
  · exact absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.mpr w.2)

theorem discrete_latOf : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F), DiscreteTopology (latOf N) := by
  intro F _ _ _ N
  by_cases hN : N = 0
  · have : Subsingleton (latOf N) := by
      constructor
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      obtain ⟨a, ha, rfl⟩ := (mem_latOf N x).1 hx
      obtain ⟨b, hb, rfl⟩ := (mem_latOf N y).1 hy
      subst hN
      rw [FractionalIdeal.mem_zero_iff] at ha hb
      subst ha; subst hb; rfl
    infer_instance
  · let I : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 N hN
    have hmem : ∀ x : latOf N, toMixedTR F x ∈ mixedEmbedding.idealLattice F I := by
      rintro ⟨x, hx⟩
      obtain ⟨a, ha, rfl⟩ := (mem_latOf N x).1 hx
      rw [mixedEmbedding.mem_idealLattice]
      exact ⟨a, ha, (toMixedTR_remb F a).symm⟩
    let h : latOf N → mixedEmbedding.idealLattice F I := fun x => ⟨toMixedTR F x, hmem x⟩
    refine DiscreteTopology.of_continuous_injective (f := h) ?_ ?_
    · exact Continuous.subtype_mk ((continuous_toMixedTR F).comp continuous_subtype_val) _
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      obtain ⟨a, ha, rfl⟩ := (mem_latOf N x).1 hx
      obtain ⟨b, hb, rfl⟩ := (mem_latOf N y).1 hy
      have : toMixedTR F (remb F a) = toMixedTR F (remb F b) := congrArg Subtype.val hxy
      rw [toMixedTR_remb, toMixedTR_remb] at this
      have hab := NumberField.mixedEmbedding_injective F this
      subst hab; rfl

end GlobalTheory.LipschitzTR
end

section

open scoped TensorProduct

theorem GlobalTheory.GoodEtale.galMap_injective_of_flat : ∀ (A R C O : Type) [CommRing A] [CommRing R] [Algebra A R] [CommRing C] [Algebra R C]
    [CommRing O] [Algebra R O] [Module.Flat R O]
    (G : Type) [Group G] [Fintype G] [DecidableEq G] (act : G →* (C ≃ₐ[R] C)) (T : C →ₗ[R] R),
    (∀ c, algebraMap R C (T c) = ∑ g, act g c) →
    ∀ (a : A), a ≠ 0 → ∀ (n : ℕ) (x y : Fin n → C),
      (∀ g, ∑ i, x i * act g (y i) = if g = 1 then algebraMap R C (algebraMap A R a) else 0) →
    GlobalTheory.GoodEtale.TorsionFreeOver A R C → ∀ σ : C →ₐ[R] O, Function.Injective (GlobalTheory.GoodEtale.galMap act σ) := by
  intro A R C O _ _ _ _ _ _ _ _ G _ _ _ act T hT a ha n x y hxy htf σ
  set b := algebraMap R C (algebraMap A R a) with hb
  have key : ∀ c : C, ∑ i, T (y i * c) • x i = b * c := by
    intro c
    have h1 : ∀ i, T (y i * c) • x i = ∑ g, x i * act g (y i) * act g c := by
      intro i; rw [Algebra.smul_def, hT, mul_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [map_mul, mul_assoc]
    simp_rw [h1]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hxy]
    simp
  let L := LinearMap.lTensor O (LinearMap.mulLeft R b)
  have hL : Function.Injective L := by
    apply Module.Flat.lTensor_preserves_injective_linearMap
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    exact htf a ha c (by rw [Algebra.smul_def]; simpa using hc)
  let Φ : (G → O) → O ⊗[R] C := fun f => ∑ i, (∑ g, σ (act g (y i)) * f g) ⊗ₜ x i
  have hΦ : ∀ m, Φ (GlobalTheory.GoodEtale.galMap act σ m) = L m := by
    intro m
    induction m using TensorProduct.induction_on with
    | zero => simp [Φ]
    | tmul o c =>
      simp only [Φ, GlobalTheory.GoodEtale.galMap_tmul, L, LinearMap.lTensor_tmul, LinearMap.mulLeft_apply]
      have h2 : ∀ i, (∑ g, σ (act g (y i)) * (o * σ (act g c))) = T (y i * c) • o := by
        intro i

        rw [Algebra.smul_def, ← σ.commutes, hT, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [map_mul, map_mul]; ring
      simp_rw [h2, ← key, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
    | add m m' hm hm' =>
      rw [map_add (f := _), map_add (f := _), ← hm, ← hm']
      simp only [Φ, Pi.add_apply, mul_add, Finset.sum_add_distrib, TensorProduct.add_tmul]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro m hm
  apply hL
  rw [← hΦ, hm, map_zero]
  simp [Φ]
end
