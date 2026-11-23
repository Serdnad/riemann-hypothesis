module

public import Formalism.FilteredPoleLength.ReducedBasisBounds.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.Complex.Exponential

@[expose] public section

section

open scoped BigOperators
open Finset

namespace Formalism.LatticeBaseChangeAlt

private theorem det_le_one_of_posSemidef_of_diag_eq_one {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosSemidef) (hd : ∀ j, G j j = 1) : G.det ≤ 1 := by
  have htr : G.trace = (n : ℝ) := by
    simp [Matrix.trace, hd]
  have hev : ∑ i, hG.1.eigenvalues i = (n : ℝ) := by
    have := hG.1.trace_eq_sum_eigenvalues
    rw [htr] at this
    exact this.symm
  calc G.det = ∏ i, hG.1.eigenvalues i := hG.1.det_eq_prod_eigenvalues
    _ ≤ ∏ i, Real.exp (hG.1.eigenvalues i - 1) :=
        Finset.prod_le_prod₀ (fun i _ => hG.eigenvalues_nonneg i)
          (fun i _ => by linarith [Real.add_one_le_exp (hG.1.eigenvalues i - 1)])
    _ = Real.exp (∑ i, (hG.1.eigenvalues i - 1)) := (Real.exp_sum _ _).symm
    _ = 1 := by
        rw [Finset.sum_sub_distrib, hev]
        simp

theorem gHadamard : GHadamard := by
  intro n M
  have hs0 : ∀ j, 0 ≤ ∑ i, M i j ^ 2 := fun j => Finset.sum_nonneg fun i _ => sq_nonneg _
  by_cases hz : ∃ j, ∑ i, M i j ^ 2 = 0
  · obtain ⟨j, hj⟩ := hz
    have hcol : ∀ i, M i j = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (M i j))).mp hj i
        (Finset.mem_univ _)
      exact pow_eq_zero_iff two_ne_zero |>.mp this
    rw [Matrix.det_eq_zero_of_column_eq_zero j hcol, abs_zero]
    exact Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _
  push_neg at hz
  have hpos : ∀ j, 0 < ∑ i, M i j ^ 2 := fun j => lt_of_le_of_ne (hs0 j) (Ne.symm (hz j))
  obtain ⟨r, hr⟩ : ∃ r : Fin n → ℝ, r = fun j => Real.sqrt (∑ i, M i j ^ 2) := ⟨_, rfl⟩
  have hr0 : ∀ j, 0 < r j := fun j => by
    rw [hr]
    exact Real.sqrt_pos.mpr (hpos j)
  have hrsq : ∀ j, r j ^ 2 = ∑ i, M i j ^ 2 := fun j => by
    rw [hr]
    exact Real.sq_sqrt (hpos j).le
  obtain ⟨N, hN⟩ : ∃ N : Matrix (Fin n) (Fin n) ℝ,
      N = M * Matrix.diagonal (fun j => (r j)⁻¹) := ⟨_, rfl⟩
  have hNe : ∀ i j, N i j = M i j * (r j)⁻¹ := fun i j => by
    rw [hN, Matrix.mul_diagonal]
  have hdiag : ∀ j, (N.conjTranspose * N) j j = 1 := by
    intro j
    rw [Matrix.mul_apply]
    have e : ∀ x, N.conjTranspose j x * N x j = M x j ^ 2 / r j ^ 2 := fun x => by
      rw [Matrix.conjTranspose_apply, star_trivial, hNe]
      ring
    rw [Finset.sum_congr rfl fun x _ => e x, ← Finset.sum_div, hrsq j]
    exact div_self (ne_of_gt (hpos j))
  have hdetG : (N.conjTranspose * N).det = N.det ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_conjTranspose, star_trivial, sq]
  have h1 : N.det ^ 2 ≤ 1 := by
    rw [← hdetG]
    exact det_le_one_of_posSemidef_of_diag_eq_one _ (Matrix.posSemidef_conjTranspose_mul_self N)
      hdiag
  have h1' : |N.det| ≤ 1 := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hP : 0 < ∏ j, r j := Finset.prod_pos fun j _ => hr0 j
  have h2 : N.det = M.det / ∏ j, r j := by
    rw [hN, Matrix.det_mul, Matrix.det_diagonal, Finset.prod_inv_distrib, div_eq_mul_inv]
  rw [h2, abs_div, abs_of_pos hP, div_le_one hP] at h1'
  have h3 : ∏ j, r j = ∏ j, Real.sqrt (∑ i, M i j ^ 2) := by
    rw [hr]
  rw [← h3]
  exact h1'

end Formalism.LatticeBaseChangeAlt
end

section

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Finset

section aux

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private theorem exists_orth_decomp_of_finiteDimensional (K : Submodule ℝ V) [FiniteDimensional ℝ K]
    (a : V) : ∃ w ∈ K, ∃ z : V, (∀ p ∈ K, inner ℝ p z = 0) ∧ a = w + z := by
  have : CompleteSpace K := FiniteDimensional.complete ℝ K
  obtain ⟨w, hw, z, hz, h⟩ : ∃ w ∈ K, ∃ z ∈ K.orthogonal, a = w + z := by
    exact K.exists_add_mem_mem_orthogonal a
  refine ⟨w, hw, z, fun p hp => ?_, h⟩
  exact Submodule.inner_right_of_mem_orthogonal hp hz

theorem exists_orth_split {ι : Type*} (v : ι → V) (T : Finset ι) (a : V) :
    ∃ w ∈ Submodule.span ℝ (v '' (T : Set ι)), ∃ z : V,
      (∀ p ∈ Submodule.span ℝ (v '' (T : Set ι)), inner ℝ p z = 0) ∧ a = w + z ∧
        ‖z‖ ^ 2 ≤ ‖a‖ ^ 2 := by
  have : FiniteDimensional ℝ (Submodule.span ℝ (v '' (T : Set ι))) :=
    FiniteDimensional.span_of_finite ℝ (T.finite_toSet.image v)
  obtain ⟨w, hw, z, hz, hwz⟩ :=
    exists_orth_decomp_of_finiteDimensional (Submodule.span ℝ (v '' (T : Set ι))) a
  refine ⟨w, hw, z, hz, hwz, ?_⟩
  rw [hwz, norm_add_sq_real, hz w hw]
  nlinarith [sq_nonneg ‖w‖]

private theorem exists_sum_repr_of_mem_span_image {R M ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (v : ι → M) (T : Finset ι) (x : M) (hx : x ∈ Submodule.span R (v '' (T : Set ι))) :
    ∃ r : ι → R, x = ∑ i ∈ T, r i • v i := by
  classical
  let S : Submodule R M :=
    { carrier := {y | ∃ r : ι → R, y = ∑ i ∈ T, r i • v i}
      add_mem' := by
        rintro y₁ y₂ ⟨r₁, rfl⟩ ⟨r₂, rfl⟩
        exact ⟨r₁ + r₂, by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c y ⟨r, rfl⟩
        exact ⟨c • r, by simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]⟩ }
  have hle : Submodule.span R (v '' (T : Set ι)) ≤ S := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    show ∃ r : ι → R, v j = ∑ i ∈ T, r i • v i
    refine ⟨fun i => if i = j then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      simp [hij]
    · intro hjT
      exact absurd (Finset.mem_coe.mp hj) hjT
  exact hle hx

theorem nearestPlane_finset {ι : Type*} [DecidableEq ι] (v : ι → V) (T : Finset ι) :
    ∀ x ∈ Submodule.span ℝ (v '' (T : Set ι)),
      ∃ c : ι → ℤ, ‖x - ∑ i ∈ T, (c i : ℝ) • v i‖ ^ 2 ≤ (1 / 4) * ∑ i ∈ T, ‖v i‖ ^ 2 := by
  refine Finset.induction_on T ?_ ?_
  · intro x hx
    refine ⟨0, ?_⟩
    simp at hx
    subst hx
    simp
  · intro a s ha ih x hx
    obtain ⟨r, hr⟩ := exists_sum_repr_of_mem_span_image v (insert a s) x hx
    rw [Finset.sum_insert ha] at hr
    obtain ⟨w, hw, z, hz, hwz, hzle⟩ := exists_orth_split v s (v a)
    have hyK : (∑ i ∈ s, r i • v i) ∈ Submodule.span ℝ (v '' (s : Set ι)) :=
      Submodule.sum_mem _ (fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩))
    obtain ⟨k, hk⟩ : ∃ k : ℤ, k = round (r a) := ⟨_, rfl⟩
    have hy'K : (∑ i ∈ s, r i • v i) + (r a - k) • w ∈ Submodule.span ℝ (v '' (s : Set ι)) :=
      Submodule.add_mem _ hyK (Submodule.smul_mem _ _ hw)
    obtain ⟨c', hc'⟩ := ih _ hy'K
    have hSK : (∑ i ∈ s, (c' i : ℝ) • v i) ∈ Submodule.span ℝ (v '' (s : Set ι)) :=
      Submodule.sum_mem _ (fun i hi =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, Finset.mem_coe.mpr hi, rfl⟩))
    have heK := Submodule.sub_mem _ hy'K hSK
    refine ⟨fun i => if i = a then k else c' i, ?_⟩
    have hsum : ∑ i ∈ s, (((if i = a then k else c' i : ℤ)) : ℝ) • v i
        = ∑ i ∈ s, (c' i : ℝ) • v i := by
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hia : i ≠ a := fun h => ha (by rw [← h]; exact hi)
      rw [if_neg hia]
    show ‖x - ∑ i ∈ insert a s, (((if i = a then k else c' i : ℤ)) : ℝ) • v i‖ ^ 2
      ≤ (1 / 4) * ∑ i ∈ insert a s, ‖v i‖ ^ 2
    rw [Finset.sum_insert ha, Finset.sum_insert ha, if_pos rfl, hsum]
    have hdecomp : x - ((k : ℝ) • v a + ∑ i ∈ s, (c' i : ℝ) • v i) =
        (r a - k) • z + ((∑ i ∈ s, r i • v i) + (r a - k) • w - ∑ i ∈ s, (c' i : ℝ) • v i) := by
      rw [hr, hwz]
      module
    have horth : inner ℝ ((r a - k) • z)
        ((∑ i ∈ s, r i • v i) + (r a - k) • w - ∑ i ∈ s, (c' i : ℝ) • v i) = 0 := by
      rw [real_inner_smul_left, real_inner_comm, hz _ heK, mul_zero]
    have hround : (r a - k) ^ 2 ≤ 1 / 4 := by
      have h1 : |r a - k| ≤ 1 / 2 := by
        rw [hk]
        exact abs_sub_round (r a)
      nlinarith [sq_abs (r a - k), abs_nonneg (r a - k),
        mul_le_mul_of_nonneg_left h1 (abs_nonneg (r a - k))]
    rw [hdecomp, norm_add_sq_real, horth, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h2 := mul_le_mul_of_nonneg_right hround (sq_nonneg ‖z‖)
    have h3 := mul_le_mul_of_nonneg_left hzle (by norm_num : (0 : ℝ) ≤ 1 / 4)
    linarith

end aux

theorem nearestPlane : NearestPlane := by
  unfold NearestPlane
  intro V _ _ n v _ x hx
  have hx' : x ∈ Submodule.span ℝ (v '' ((Finset.univ : Finset (Fin n)) : Set (Fin n))) := by
    rwa [Finset.coe_univ, Set.image_univ]
  exact nearestPlane_finset v Finset.univ x hx'

end Formalism.LatticeBaseChangeAlt
end
end

section

namespace Formalism.LatticeBaseChangeAlt

theorem poleOrderGood : PoleOrderGood := by
  intro ep T ν νs c' vet e hep hc hv hν ⟨n, hn⟩ he
  have hepR : (1 : ℝ) ≤ ep := by exact_mod_cast hep
  have hT0 : (0 : ℝ) ≤ T := by positivity
  have hy : 0 ≤ (ep : ℝ) * (T * c' * vet) := by positivity
  rw [div_le_iff₀ (by linarith)]
  have hint : (ep : ℝ) * ((T : ℝ) * ν - e) = (((T : ℤ) * n - ep * e : ℤ) : ℝ) := by
    push_cast; rw [← hn]; ring
  rw [hint, Int.ceil_intCast, Int.cast_max]
  apply max_le
  · simpa [mul_comm] using hy
  · rw [← hint]
    have : (T : ℝ) * ν - e ≤ T * c' * vet := by nlinarith
    nlinarith

theorem poleOrderBad : PoleOrderBad := by
  intro ep T ν νs c' vet hep hT hc hv hν e
  have hepR : (1 : ℝ) ≤ ep := by exact_mod_cast hep
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have he : (T : ℝ) * (νs + 1) ≤ (e : ℝ) := Int.le_ceil _
  have hy : 0 ≤ (ep : ℝ) * (T * c' * vet) := by positivity
  rw [div_le_iff₀ (by linarith)]
  have hx : (ep : ℝ) * ((T : ℝ) * ν - e) ≤ (ep : ℝ) * (T * c' * vet) - ep := by
    have : (T : ℝ) * ν - e ≤ T * c' * vet - 1 := by nlinarith
    nlinarith
  have hc1 : ((⌈(ep : ℝ) * ((T : ℝ) * ν - e)⌉ : ℤ) : ℝ) < (ep : ℝ) * ((T : ℝ) * ν - e) + 1 :=
    Int.ceil_lt_add_one _
  rw [Int.cast_max]
  apply max_le
  · simpa [mul_comm] using hy
  · nlinarith

end Formalism.LatticeBaseChangeAlt
end

section

namespace Formalism.LatticeBaseChangeAlt

theorem four_term_sum_bound : FourTermSumBound := by
  intro d PP D κ T c RR ga C k f b m δ₂ hd hT hga hPP hD hR hκ h0 h1 h2 h3
  have e1 : PP ^ 2 * (D ^ 3 * κ / T) ≤ PP ^ 2 * D ^ 3 * C * k * f * b / T := by
    have : PP ^ 2 * D ^ 3 * C * k * f * b / T = PP ^ 2 * (D ^ 3 * (C * k * f * b) / T) := by ring
    rw [this]
    gcongr
  have e3 : PP ^ 2 * ((RR ^ 2 * c + 1 / T) * κ / ga) ≤
      PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga := by
    have : PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga =
        PP ^ 2 * ((RR ^ 2 * c + 1 / T) * (C * k * f * b) / ga) := by ring
    rw [this]
    gcongr
  have tot : PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + PP ^ 3 * T ≤
      f * m * b * δ₂ := by
    have : PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) =
        PP ^ 2 * (D ^ 3 * κ / T) + PP ^ 2 * T * c + PP ^ 2 * ((RR ^ 2 * c + 1 / T) * κ / ga) := by
      ring
    rw [this]
    linarith
  calc d * PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + d * PP ^ 3 * T
      = d * (PP ^ 2 * (D ^ 3 * κ / T + T * c + (RR ^ 2 * c + 1 / T) * κ / ga) + PP ^ 3 * T) := by
        ring
    _ ≤ d * (f * m * b * δ₂) := mul_le_mul_of_nonneg_left tot hd
    _ = d * f * m * b * δ₂ := by ring

theorem four_term_sum_bound_of_parameters : FourTermSumBoundOfParameters := by
  intro d PP D κ T c RR ga C k f b m δ₂ q DF g₀ hd hT hTga hPP hD hRR hq hC hk hf hb hm hδ
    hκ h0 hTlow hc hg₀ hTc hqlow hTPP hPP2
  have hga : 0 < ga := lt_of_lt_of_le hT hTga
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hK : 0 ≤ C * k * f * b := by positivity
  have hD0 : 0 ≤ D := by linarith
  have hPP1 : 1 ≤ PP := by nlinarith
  have hT1 : 1 ≤ T := by linarith
  have hRRc : RR ^ 2 * c ≤ 1 / PP ^ 2 := by
    have hP2 : 0 < PP ^ 2 := by positivity
    rw [hc, le_div_iff₀ hP2]
    have e : RR ^ 2 * (RR * PP * DF ^ 2 / q) * PP ^ 2 = RR ^ 3 * PP ^ 3 * DF ^ 2 / q := by ring
    rw [e, div_le_one hq]
    have h34 : RR ^ 3 ≤ RR ^ 4 := pow_le_pow_right₀ hRR (by norm_num)
    have : RR ^ 3 * (PP ^ 3 * DF ^ 2) ≤ RR ^ 4 * (PP ^ 3 * DF ^ 2) :=
      mul_le_mul_of_nonneg_right h34 (by positivity)
    nlinarith [this]
  have hmδ : 0 < m * δ₂ := mul_pos hm hδ
  have h1 : PP ^ 2 * D ^ 3 * C * k * f * b / T ≤ f * m * b * δ₂ / 4 := by
    rw [div_le_iff₀ hmδ] at hTlow
    rw [div_le_iff₀ hT]
    have := mul_le_mul_of_nonneg_right hTlow (mul_nonneg hf hb)
    nlinarith [this]
  have hPPq : PP ^ 2 ≤ f * m * b * δ₂ / 4 := by
    have a : PP ^ 2 * 1 ≤ PP ^ 2 * (PP * T) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    nlinarith [a]
  have h2 : PP ^ 2 * T * c ≤ f * m * b * δ₂ / 4 := by
    have hTc0 : 0 ≤ T * c := mul_nonneg hT.le hc0
    have hTc1 : T * c ≤ 1 := by nlinarith
    have : PP ^ 2 * (T * c) ≤ PP ^ 2 * 1 := mul_le_mul_of_nonneg_left hTc1 (by positivity)
    nlinarith [this]
  have hside : 1 + PP ^ 2 / T ≤ PP ^ 2 * D ^ 3 := by
    have s1 : PP ^ 2 / T ≤ 1 := (div_le_one hT).2 hTPP
    have s2 : (1 : ℝ) ≤ D ^ 3 := one_le_pow₀ hD
    have s3 : PP ^ 2 * 1 ≤ PP ^ 2 * D ^ 3 := mul_le_mul_of_nonneg_left s2 (by positivity)
    linarith
  have h3 : PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga ≤ f * m * b * δ₂ / 4 := by
    have a1 : PP ^ 2 * (RR ^ 2 * c + 1 / T) ≤ PP ^ 2 * D ^ 3 := by
      have : PP ^ 2 * (RR ^ 2 * c) ≤ PP ^ 2 * (1 / PP ^ 2) :=
        mul_le_mul_of_nonneg_left hRRc (by positivity)
      have e : PP ^ 2 * (1 / PP ^ 2) = 1 := by field_simp
      have e' : PP ^ 2 * (1 / T) = PP ^ 2 / T := by ring
      rw [mul_add, e']
      linarith
    have a2 : PP ^ 2 * (RR ^ 2 * c + 1 / T) * (C * k * f * b) ≤ PP ^ 2 * D ^ 3 * (C * k * f * b) :=
      mul_le_mul_of_nonneg_right a1 hK
    calc PP ^ 2 * (RR ^ 2 * c + 1 / T) * C * k * f * b / ga
        = PP ^ 2 * (RR ^ 2 * c + 1 / T) * (C * k * f * b) / ga := by ring
      _ ≤ PP ^ 2 * D ^ 3 * (C * k * f * b) / ga := by gcongr
      _ ≤ PP ^ 2 * D ^ 3 * (C * k * f * b) / T := by gcongr
      _ = PP ^ 2 * D ^ 3 * C * k * f * b / T := by ring
      _ ≤ _ := h1
  exact four_term_sum_bound d PP D κ T c RR ga C k f b m δ₂ hd hT hga hPP.le hD0 (by positivity) hκ
    h0 h1 h2 h3

end Formalism.LatticeBaseChangeAlt
end

section

namespace Formalism.LatticeBaseChangeAlt

open Real

private theorem pow_sub_pow_le_mul_sub_mul_pow {x y M : ℝ} (hy : 0 ≤ y) (hyx : y ≤ x) (hxM : x ≤ M) (hM : 1 ≤ M) :
    ∀ n : ℕ, x ^ n - y ^ n ≤ n * (x - y) * M ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hx : 0 ≤ x := hy.trans hyx
    have hxy : 0 ≤ x - y := sub_nonneg.2 hyx
    have hMn : 0 ≤ M ^ n := pow_nonneg (by linarith) n
    have hyn : y ^ n ≤ M ^ n := by
      first
      | exact pow_le_pow_left hy (hyx.trans hxM) n
      | exact pow_le_pow_left₀ hy (hyx.trans hxM) n
      | (gcongr <;> linarith)
    have hMn1 : M ^ n ≤ M ^ (n + 1) := by
      rw [pow_succ]; nlinarith [mul_nonneg hMn (sub_nonneg.2 hM)]
    have h1 : x * (x ^ n - y ^ n) ≤ x * (n * (x - y) * M ^ n) := mul_le_mul_of_nonneg_left ih hx
    have h2 : x * (n * (x - y) * M ^ n) ≤ M * (n * (x - y) * M ^ n) :=
      mul_le_mul_of_nonneg_right hxM (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hxy) hMn)
    have h3 : (x - y) * y ^ n ≤ (x - y) * M ^ (n + 1) :=
      mul_le_mul_of_nonneg_left (hyn.trans hMn1) hxy
    have e : x ^ (n + 1) - y ^ (n + 1) = x * (x ^ n - y ^ n) + (x - y) * y ^ n := by ring
    have e2 : M * (n * (x - y) * M ^ n) = n * (x - y) * M ^ (n + 1) := by ring
    rw [e]
    push_cast
    linarith

theorem detProductRest : DetProductRest := by
  intro i c ε hε hε1
  have h2 : (0 : ℝ) ≤ 2 ^ c := by positivity
  have hM : (1 : ℝ) ≤ 2 ^ c + 1 := by linarith
  have key := pow_sub_pow_le_mul_sub_mul_pow h2 (by linarith : (2 : ℝ) ^ c ≤ 2 ^ c + ε)
    (by linarith : (2 : ℝ) ^ c + ε ≤ 2 ^ c + 1) hM i
  have e : (2 : ℝ) ^ c + ε - 2 ^ c = ε := by ring
  rw [e] at key
  rw [pow_mul]
  exact key

end Formalism.LatticeBaseChangeAlt
end

section

namespace Formalism.LatticeBaseChangeAlt

open Finset

theorem levelsSum : LevelsSum := by
  intro ι _ ep f mm v T c' h
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun z _ => ?_
  have hf : (0 : ℝ) ≤ (f z : ℝ) := Nat.cast_nonneg _
  calc (mm z : ℝ) * f z ≤ (ep z * T * c' * v z) * f z := mul_le_mul_of_nonneg_right (h z) hf
    _ = T * c' * ((ep z : ℝ) * f z * v z) := by ring

end Formalism.LatticeBaseChangeAlt
end
