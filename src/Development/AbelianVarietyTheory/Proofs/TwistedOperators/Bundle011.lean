module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.Unique

@[expose] public section

section

open scoped InnerProductSpace

namespace GlobalTheory

theorem MultilinearMap.inner_map_eq_const_mul_prod_inner
    {ι : Type} [Fintype ι] {Xs : ι → Type} [∀ i, NormedAddCommGroup (Xs i)]
    [∀ i, InnerProductSpace ℂ (Xs i)] {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : (Π i, Xs i) →ₘₗ[ℂ] E) (K : ℝ) (hf : ∀ x, ‖f x‖ ^ 2 = K * ∏ i, ‖x i‖ ^ 2) :
    ∀ x y, ⟪f x, f y⟫_ℂ = (K : ℂ) * ∏ i, ⟪x i, y i⟫_ℂ := by
  classical
  have hdiag : ∀ x, ⟪f x, f x⟫_ℂ = (K : ℂ) * ∏ i, ⟪x i, x i⟫_ℂ := by
    intro x
    simp only [inner_self_eq_norm_sq_to_K]
    have h := congrArg (fun r : ℝ => (r : ℂ)) (hf x)
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_prod] at h
    exact h
  have hprod : ∀ (x y : ∀ i, Xs i) (j : ι) (u v : Xs j),
      ∏ i, ⟪Function.update x j u i, Function.update y j v i⟫_ℂ
        = ⟪u, v⟫_ℂ * ∏ i ∈ Finset.univ.erase j, ⟪x i, y i⟫_ℂ := by
    intro x y j u v
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
      Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have key : ∀ s : Finset ι, ∀ x y : (∀ i, Xs i), (∀ i ∉ s, x i = y i) →
      ⟪f x, f y⟫_ℂ = (K : ℂ) * ∏ i, ⟪x i, y i⟫_ℂ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x y h
      have hxy : x = y := funext fun i => h i (Finset.notMem_empty i)
      subst hxy
      exact hdiag x
    | insert j s hj ih =>
      intro x y hxy
      set C := ∏ i ∈ Finset.univ.erase j, ⟪x i, y i⟫_ℂ with hC
      have hd : ∀ u : Xs j, ⟪f (Function.update x j u), f (Function.update y j u)⟫_ℂ
          = (K : ℂ) * (⟪u, u⟫_ℂ * C) := by
        intro u
        rw [ih _ _ ?_, hprod]
        intro i hi
        by_cases hij : i = j
        · subst hij; simp
        · rw [Function.update_of_ne hij, Function.update_of_ne hij]
          exact hxy i (by simp [hij, hi])
      have hab : ∀ a b : Xs j, ⟪f (Function.update x j a), f (Function.update y j b)⟫_ℂ
          = (K : ℂ) * (⟪a, b⟫_ℂ * C) := by
        intro a b
        have ha := hd a
        have hb := hd b
        have h1 := hd (a + b)
        have h2 := hd (a + Complex.I • b)
        simp only [MultilinearMap.map_update_add, MultilinearMap.map_update_smul, RingHom.id_apply,
          inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_I] at h1 h2
        have e1 : ⟪f (Function.update x j a), f (Function.update y j b)⟫_ℂ
            + ⟪f (Function.update x j b), f (Function.update y j a)⟫_ℂ
            = (K : ℂ) * C * (⟪a, b⟫_ℂ + ⟪b, a⟫_ℂ) := by
          linear_combination h1 - ha - hb
        have e2 : Complex.I * (⟪f (Function.update x j a), f (Function.update y j b)⟫_ℂ
            - ⟪f (Function.update x j b), f (Function.update y j a)⟫_ℂ
            - (K : ℂ) * C * (⟪a, b⟫_ℂ - ⟪b, a⟫_ℂ)) = 0 := by
          linear_combination h2 - ha + Complex.I * Complex.I * hb
        have e3 := (mul_eq_zero.mp e2).resolve_left Complex.I_ne_zero
        linear_combination (e1 + e3) / 2
      have := hab (x j) (y j)
      simp only [Function.update_eq_self] at this
      rw [this, ← hprod x y j (x j) (y j)]
      simp only [Function.update_eq_self]
  intro x y
  exact key Finset.univ x y (fun i hi => absurd (Finset.mem_univ i) hi)

end GlobalTheory
end

section

open NormedSpace Filter Topology

namespace GlobalTheory.ExponentialIntegralUnits

universe u_1

variable {𝔸 : Type u_1} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem hasDerivAt_primitive (M : ℝ → 𝔸) (hc : Continuous M) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, M s) (M t) t := by
  exact (hc.integral_hasStrictDerivAt 0 t).hasDerivAt

theorem exists_isUnit_integral (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M 0 = 1) :
    ∃ δ : ℝ, IsUnit (∫ s in (0 : ℝ)..δ, M s) := by
  have hd := (hasDerivAt_primitive M hc 0).tendsto_slope_zero
  rw [h0] at hd
  have hev := hd.eventually (Units.isOpen.mem_nhds isUnit_one)
  obtain ⟨δ, hδU, hδ0⟩ := (hev.and self_mem_nhdsWithin).exists
  have hδ0' : δ ≠ 0 := Set.mem_compl_singleton_iff.1 hδ0
  simp only [zero_add, intervalIntegral.integral_same, sub_zero] at hδU
  refine ⟨δ, ?_⟩
  have e : (∫ s in (0 : ℝ)..δ, M s) = algebraMap ℝ 𝔸 δ * (δ⁻¹ • ∫ s in (0 : ℝ)..δ, M s) := by
    rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hδ0', one_smul]
  rw [e]
  exact ((isUnit_iff_ne_zero.2 hδ0').map (algebraMap ℝ 𝔸)).mul hδU

theorem mul_integral (M : ℝ → 𝔸) (hc : Continuous M)
    (hadd : ∀ s t : ℝ, M (s + t) = M s * M t) (t δ : ℝ) :
    M t * (∫ s in (0 : ℝ)..δ, M s)
      = (∫ s in (0 : ℝ)..(t + δ), M s) - ∫ s in (0 : ℝ)..t, M s := by
  have hL := ((ContinuousLinearMap.mul ℝ 𝔸) (M t)).intervalIntegral_comp_comm (hc.intervalIntegrable (μ := MeasureTheory.volume) 0 δ)
  simp only [ContinuousLinearMap.mul_apply'] at hL
  rw [← hL]
  simp_rw [← hadd]
  rw [intervalIntegral.integral_comp_add_left (fun s => M s) t, add_zero,
    intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable (μ := MeasureTheory.volume) _ _) (hc.intervalIntegrable (μ := MeasureTheory.volume) _ _)]

theorem exists_hasDerivAt (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M 0 = 1)
    (hadd : ∀ s t : ℝ, M (s + t) = M s * M t) :
    ∃ X : 𝔸, ∀ t : ℝ, HasDerivAt M (M t * X) t := by
  obtain ⟨δ, hA⟩ := exists_isUnit_integral M hc h0
  have hAA : (∫ s in (0 : ℝ)..δ, M s) * ↑(hA.unit⁻¹) = 1 := hA.mul_val_inv
  refine ⟨(M δ - 1) * ↑(hA.unit⁻¹), fun t => ?_⟩
  have hM : ∀ u, M u = ((∫ s in (0 : ℝ)..(u + δ), M s) - ∫ s in (0 : ℝ)..u, M s) * ↑(hA.unit⁻¹) := fun u => by
    rw [← mul_integral M hc hadd u δ, mul_assoc, hAA, mul_one]
  have hP : HasDerivAt (fun u => ∫ s in (0 : ℝ)..(u + δ), M s) (M (t + δ)) t := by
    first
      | exact (hasDerivAt_primitive M hc (t + δ)).comp_add_const t δ
      | exact HasDerivAt.comp_add_const t δ (hasDerivAt_primitive M hc (t + δ))
  have hF := (hP.sub (hasDerivAt_primitive M hc t)).mul_const (↑(hA.unit⁻¹) : 𝔸)
  have hF' := hF.congr_of_eventuallyEq (Eventually.of_forall hM)
  refine hF'.congr_deriv ?_
  rw [hadd, ← mul_assoc, mul_sub, mul_one]

theorem exists_exp_eq (M : ℝ → 𝔸) (hc : Continuous M) (h0 : M (0 : ℝ) = (1 : 𝔸))
    (hadd : ∀ s t : ℝ, M (s + t) = M s * M t) :
    ∃ X : 𝔸, ∀ t : ℝ, NormedSpace.exp (t • X) = M t := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  obtain ⟨X, hX⟩ := exists_hasDerivAt M hc h0 hadd
  refine ⟨X, fun t => ?_⟩
  have hN : ∀ u : ℝ, HasDerivAt (fun v => M v * NormedSpace.exp (v • (-X))) 0 u := fun u => by
    have h3 := (hX u).mul (hasDerivAt_exp_smul_const (-X) u)
    refine h3.congr_deriv ?_
    have hcomm : Commute (NormedSpace.exp (u • (-X))) X :=
      (((Commute.refl X).neg_left).smul_left u).exp_left
    rw [mul_neg, hcomm.eq, mul_neg, ← mul_assoc, add_neg_cancel]
  have hconst : ∀ u, M u * NormedSpace.exp (u • (-X)) = 1 := fun u => by
    have h4 := is_const_of_deriv_eq_zero (fun v => (hN v).differentiableAt) (fun v => (hN v).deriv) u 0
    rw [h4, h0, zero_smul, NormedSpace.exp_zero, one_mul]
  have hinv : NormedSpace.exp (t • (-X)) * NormedSpace.exp (t • X) = 1 := by
    rw [← NormedSpace.exp_add_of_commute ((((Commute.refl X).neg_left).smul_left t).smul_right t), smul_neg,
      neg_add_cancel, NormedSpace.exp_zero]
  calc NormedSpace.exp (t • X) = (M t * NormedSpace.exp (t • (-X))) * NormedSpace.exp (t • X) := by
        rw [hconst t, one_mul]
    _ = M t := by rw [mul_assoc, hinv, mul_one]

end GlobalTheory.ExponentialIntegralUnits
end

section

open PowerSeries Finset

namespace GlobalTheory.CompleteHomogeneousBound

def WeightedSummable (r : ℝ) (f : ℂ⟦X⟧) : Prop :=
  Summable fun m : ℕ => ‖coeff m f * (r : ℂ) ^ m‖

theorem WeightedSummable.mul {r : ℝ} {f g : ℂ⟦X⟧} (hf : WeightedSummable r f)
    (hg : WeightedSummable r g) : WeightedSummable r (f * g) := by
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
  refine h.congr fun m => ?_
  rw [coeff_mul, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  have hpm : p.1 + p.2 = m := by simpa using hp
  rw [← hpm, pow_add]
  ring

theorem weightedSummable_one (r : ℝ) : WeightedSummable r 1 := by
  refine summable_of_ne_finset_zero (s := {0}) fun m hm => ?_
  have : m ≠ 0 := by simpa using hm
  simp [coeff_one, this]

theorem weightedSummable_linear (r : ℝ) (b : ℂ) : WeightedSummable r (1 - C b * X) := by
  refine summable_of_ne_finset_zero (s := {0, 1}) fun m hm => ?_
  have h0 : m ≠ 0 := fun h => hm (by simp [h])
  have h1 : m ≠ 1 := fun h => hm (by simp [h])
  simp [coeff_one, coeff_X, h0, h1]

theorem weightedSummable_prod {ι : Type*} (r : ℝ) (s : Finset ι) (f : ι → ℂ⟦X⟧)
    (h : ∀ i ∈ s, WeightedSummable r (f i)) : WeightedSummable r (∏ i ∈ s, f i) :=
  Finset.prod_induction f (WeightedSummable r) (fun _ _ ha hb => ha.mul hb)
    (weightedSummable_one r) h

theorem weightedSummable_geom_iff (r : ℝ) (b : ℂ) :
    WeightedSummable r (mk fun m => b ^ m) ↔ ‖b * r‖ < 1 := by
  unfold WeightedSummable
  simp only [coeff_mk, ← mul_pow, norm_pow]
  rw [summable_geometric_iff_norm_lt_one, norm_norm]

theorem geom_mul_linear (b : ℂ) : (mk fun m => b ^ m : ℂ⟦X⟧) * (1 - C b * X) = 1 := by
  ext m
  rw [mul_sub, mul_one, ← mul_assoc, map_sub]
  cases m with
  | zero => simp
  | succ m => simp [coeff_succ_mul_X, coeff_one, pow_succ]

theorem coeff_prod_geom {n : ℕ} (β : Fin n → ℂ) (m : ℕ) :
    coeff m (∏ i, (mk fun k => β i ^ k : ℂ⟦X⟧)) =
      ∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ i, β i ^ a i := by
  rw [coeff_prod]
  simp only [coeff_mk]
  refine Finset.sum_bij' (fun l _ => (l : Fin n → ℕ))
    (fun a _ => Finsupp.equivFunOnFinite.symm a) ?_ ?_ ?_ ?_ ?_
  · intro l hl
    simpa [Finset.mem_piAntidiag, Finset.mem_finsuppAntidiag] using hl
  · intro a ha
    simpa [Finset.mem_piAntidiag, Finset.mem_finsuppAntidiag] using ha
  · intro l _
    simp
  · intro a _
    simp
  · intro l _
    rfl

theorem norm_le_of_completeHomogeneous_le (n : ℕ) (β : Fin n → ℂ) (c : Fin n → ℝ) (Q : ℝ)
    (hc0 : ∀ i, 0 ≤ c i) (hcQ : ∀ i, c i ≤ Q)
    (h : ∀ m : ℕ, ‖∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ i, β i ^ a i‖ ≤
      ∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ i, c i ^ a i) (i : Fin n) : ‖β i‖ ≤ Q := by
  by_contra hlt
  rw [not_le] at hlt
  have hpos : 0 < ‖β i‖ := lt_of_le_of_lt ((hc0 i).trans (hcQ i)) hlt
  set r : ℝ := ‖β i‖⁻¹ with hr
  have hr0 : 0 < r := inv_pos.mpr hpos
  have hc : WeightedSummable r (∏ j, (mk fun k => ((c j : ℝ) : ℂ) ^ k : ℂ⟦X⟧)) := by
    refine weightedSummable_prod r _ _ fun j _ => ?_
    rw [weightedSummable_geom_iff, norm_mul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (hc0 j), Real.norm_of_nonneg hr0.le, hr, ← div_eq_mul_inv,
      div_lt_one hpos]
    exact (hcQ j).trans_lt hlt
  have hβ : WeightedSummable r (∏ j, (mk fun k => β j ^ k : ℂ⟦X⟧)) := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun m => ?_) hc
    rw [norm_mul, norm_mul, coeff_prod_geom, coeff_prod_geom]
    refine mul_le_mul_of_nonneg_right ((h m).trans ?_) (norm_nonneg _)
    have : (∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ j, ((c j : ℝ) : ℂ) ^ a j) =
        ((∑ a ∈ Finset.piAntidiag Finset.univ m, ∏ j, c j ^ a j : ℝ) : ℂ) := by
      push_cast; rfl
    rw [this, Complex.norm_real]
    exact le_abs_self _
  have hlin : WeightedSummable r (∏ j ∈ Finset.univ.erase i, (1 - C (β j) * X)) :=
    weightedSummable_prod r _ _ fun j _ => weightedSummable_linear r _
  have hm := hβ.mul hlin
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_assoc, ← Finset.prod_mul_distrib,
    Finset.prod_eq_one (fun j _ => geom_mul_linear (β j)), mul_one, weightedSummable_geom_iff,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg hr0.le, hr, mul_inv_cancel₀ hpos.ne'] at hm
  exact lt_irrefl _ hm

end GlobalTheory.CompleteHomogeneousBound
end

section

open MeasureTheory

namespace GlobalTheory

theorem integral_haar_eq_zero_of_fibre_integrals_eq_zero :
    ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H), μ.IsHaarMeasure → ∀ (P Q : Subgroup H), IsClosed (P : Set H) → IsClosed (Q : Set H) → (∀ p ∈ P, ∀ q ∈ Q, p * q = q * p) → (∀ h, ∃ p ∈ P, ∃ q ∈ Q, h = p * q) → (∀ h, h ∈ P → h ∈ Q → h = 1) → ∀ F : H → ℂ, (∀ ν : Measure P, ν.IsHaarMeasure → ∀ q ∈ Q, ∫ p, F ((p : H) * q) ∂ν = 0) → ∫ h, F h ∂μ = 0 := by
  intro H _ _ _ _ _ _ _ _ μ hμ P Q hP hQ hcomm hgen hdisj F hF
  haveI : LocallyCompactSpace P := hP.locallyCompactSpace
  haveI : LocallyCompactSpace Q := hQ.locallyCompactSpace
  haveI : SecondCountableTopology P := TopologicalSpace.Subtype.secondCountableTopology (P : Set H)
  haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology (Q : Set H)
  haveI : BorelSpace P := Subtype.borelSpace (fun x => x ∈ (P : Set H))
  haveI : BorelSpace Q := Subtype.borelSpace (fun x => x ∈ (Q : Set H))
  let m : P × Q →* H :=
    { toFun := fun x => (x.1 : H) * x.2
      map_one' := by simp
      map_mul' := by
        rintro ⟨p, q⟩ ⟨p', q'⟩
        simp only [Prod.mk_mul_mk, Subgroup.coe_mul]
        have h := hcomm p' p'.2 q q.2
        calc (p : H) * p' * (q * q') = p * (p' * q) * q' := by simp only [mul_assoc]
          _ = p * (q * p') * q' := by rw [h]
          _ = p * q * (p' * q') := by simp only [mul_assoc] }
  have hm : ∀ x : P × Q, m x = (x.1 : H) * x.2 := fun _ => rfl
  have hcont : Continuous m :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  have hsurj : Function.Surjective m := by
    intro h
    obtain ⟨p, hp, q, hq, rfl⟩ := hgen h
    exact ⟨(⟨p, hp⟩, ⟨q, hq⟩), rfl⟩
  have hinj : Function.Injective m := by
    rw [injective_iff_map_eq_one]
    rintro ⟨p, q⟩ h
    rw [hm] at h
    have h1 : (p : H) = (q : H)⁻¹ := eq_inv_of_mul_eq_one_left h
    have hp1 : (p : H) = 1 := hdisj p p.2 (h1 ▸ Q.inv_mem q.2)
    have hq1 : (q : H) = 1 := by simpa [hp1] using h
    exact Prod.ext (Subtype.ext hp1) (Subtype.ext hq1)
  have hopen : IsOpenMap m := m.isOpenMap_of_sigmaCompact hsurj hcont
  let e : (P × Q) ≃* H := MulEquiv.ofBijective m ⟨hinj, hsurj⟩
  let φ : (P × Q) ≃ₜ H := e.toEquiv.toHomeomorphOfContinuousOpen hcont hopen
  let νP : Measure P := Measure.haar
  let νQ : Measure Q := Measure.haar
  haveI : νP.IsHaarMeasure := inferInstance
  haveI : νQ.IsHaarMeasure := inferInstance
  haveI : (νP.prod νQ).IsHaarMeasure := inferInstance
  haveI : ((νP.prod νQ).map e).IsHaarMeasure :=
    e.isHaarMeasure_map (νP.prod νQ) φ.continuous φ.symm.continuous
  have hμeq := Measure.isMulLeftInvariant_eq_smul μ ((νP.prod νQ).map e)
  have hzero : ∫ h, F h ∂((νP.prod νQ).map e) = 0 := by
    have hemb : MeasurableEmbedding e := φ.measurableEmbedding
    rw [hemb.integral_map]
    by_cases hint : Integrable (fun x => F (e x)) (νP.prod νQ)
    · rw [integral_prod_symm _ hint]
      have : ∀ q : Q, ∫ p : P, F (e (p, q)) ∂νP = 0 := fun q => hF νP inferInstance q q.2
      simp [this]
    · exact integral_undef hint
  rw [hμeq, integral_smul_nnreal_measure, hzero, smul_zero]

end GlobalTheory
end

section

namespace GlobalTheory.PolarU

open Module

theorem det_complexification (E W : Type) [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    [AddCommGroup W] [Module ℂ W] (j : E →+ W) (T : E →ₗ[ℝ] E) (S : W →ₗ[ℂ] W)
    (hj : ∀ (t : ℝ) (x : E), j (t • x) = (t : ℂ) • j x)
    (hspan : ∀ w, ∃ a b, w = j a + Complex.I • j b)
    (hinj : ∀ a b, j a + Complex.I • j b = 0 → a = 0 ∧ b = 0)
    (hS : ∀ x, S (j x) = j (T x)) :
    LinearMap.det S = ((LinearMap.det T : ℝ) : ℂ) := by
  classical
  let bE := Module.finBasis ℝ E
  let v : Fin (Module.finrank ℝ E) → W := fun i => j (bE i)

  have hsum : ∀ c : Fin (Module.finrank ℝ E) → ℝ, j (∑ i, c i • bE i) = ∑ i, (c i : ℂ) • v i := by
    intro c

    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => hj (c i) (bE i))

  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have key : j (∑ k, (g k).re • bE k) + Complex.I • j (∑ k, (g k).im • bE k) = 0 := by
      rw [hsum, hsum, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine (Finset.sum_congr rfl (fun k _ => ?_)).trans hg
      rw [smul_smul, ← add_smul, mul_comm Complex.I, Complex.re_add_im]
    obtain ⟨h1, h2⟩ := hinj _ _ key
    have r1 := Fintype.linearIndependent_iff.mp bE.linearIndependent (fun k => (g k).re) h1 i
    have r2 := Fintype.linearIndependent_iff.mp bE.linearIndependent (fun k => (g k).im) h2 i
    exact Complex.ext (by simpa using r1) (by simpa using r2)

  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    have hmem : ∀ a : E, j a ∈ Submodule.span ℂ (Set.range v) := by
      intro a
      rw [← bE.sum_repr a, hsum]
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    intro w _
    obtain ⟨a, b, rfl⟩ := hspan w
    exact Submodule.add_mem _ (hmem a) (Submodule.smul_mem _ _ (hmem b))
  let bW : Basis (Fin (Module.finrank ℝ E)) ℂ W := Basis.mk hli hsp
  have hbW : ∀ i, bW i = v i := fun i => Basis.mk_apply hli hsp i

  have hmat : LinearMap.toMatrix bW bW S = (LinearMap.toMatrix bE bE T).map Complex.ofRealHom := by
    ext i k
    have e : S (bW k) = ∑ l, ((bE.repr (T (bE k)) l : ℝ) : ℂ) • bW l := by
      simp only [hbW]
      rw [← hsum (bE.repr (T (bE k))), bE.sum_repr]
      exact hS (bE k)
    rw [LinearMap.toMatrix_apply, Matrix.map_apply, LinearMap.toMatrix_apply, e, bW.repr_sum_self]
    rfl
  rw [← LinearMap.det_toMatrix bW S, ← LinearMap.det_toMatrix bE T, hmat]
  exact (RingHom.map_det Complex.ofRealHom _).symm

end GlobalTheory.PolarU
end

section

namespace GlobalTheory.NatCastMemOfPrimeDvdNorm

open NumberField IsDedekindDomain

theorem natCast_mem_of_prime_dvd_absNorm {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (RingOfIntegers K)) {q : ℕ} (hq : Nat.Prime q)
    (hd : q ∣ Ideal.absNorm w.asIdeal) : (q : RingOfIntegers K) ∈ w.asIdeal := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : Finite (RingOfIntegers K ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  have hc : q ∣ Nat.card (RingOfIntegers K ⧸ w.asIdeal) := by
    rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at hd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' q hc
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hq.one_lt.ne hx
  have h1 : (q : RingOfIntegers K ⧸ w.asIdeal) * x = 0 := by
    rw [← nsmul_eq_mul, ← hx]
    exact addOrderOf_nsmul_eq_zero x
  have h2 : (q : RingOfIntegers K ⧸ w.asIdeal) = 0 := (mul_eq_zero.mp h1).resolve_right hx0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h2

end GlobalTheory.NatCastMemOfPrimeDvdNorm
end
