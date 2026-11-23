module

public import ReciprocityTheory.SemistableReduction.Bundle013
public import ReciprocityTheory.SemistableReduction.Bundle017
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.SemistableReduction.Bundle003
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.NumberTheory.NumberField.Norm

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix

def sbDp (p r : ℕ) : Matrix (Fin r) (Fin r) ℂ := diagonal fun k => if (k : ℕ) < p then 1 else 0

def sbDn (p r : ℕ) : Matrix (Fin r) (Fin r) ℂ := diagonal fun k => if (k : ℕ) < p then 0 else 1

theorem sb_signMat_eq (p r : ℕ) : signMat p r = sbDp p r - sbDn p r := by
  simp only [signMat, sgn, sbDp, sbDn, diagonal_sub]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dp_add_Dn (p r : ℕ) : sbDp p r + sbDn p r = 1 := by
  simp only [sbDp, sbDn, diagonal_add]
  rw [← diagonal_one]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dp_mul_Dp (p r : ℕ) : sbDp p r * sbDp p r = sbDp p r := by
  simp only [sbDp, diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dn_mul_Dn (p r : ℕ) : sbDn p r * sbDn p r = sbDn p r := by
  simp only [sbDn, diagonal_mul_diagonal]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dp_mul_Dn (p r : ℕ) : sbDp p r * sbDn p r = 0 := by
  simp only [sbDp, sbDn, diagonal_mul_diagonal]
  rw [← diagonal_zero]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dn_mul_Dp (p r : ℕ) : sbDn p r * sbDp p r = 0 := by
  simp only [sbDp, sbDn, diagonal_mul_diagonal]
  rw [← diagonal_zero]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_Dp_herm (p r : ℕ) : (sbDp p r)ᴴ = sbDp p r := by
  simp only [sbDp, diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem sb_Dn_herm (p r : ℕ) : (sbDn p r)ᴴ = sbDn p r := by
  simp only [sbDn, diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem sb_J_herm (p r : ℕ) : (signMat p r)ᴴ = signMat p r := by
  simp only [signMat, sgn, diagonal_conjTranspose]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem sb_J_mul_J (p r : ℕ) : signMat p r * signMat p r = 1 := by
  simp only [signMat, sgn, diagonal_mul_diagonal]
  rw [← diagonal_one]
  refine congrArg Matrix.diagonal (funext fun k => ?_)
  split_ifs <;> norm_num

theorem sb_posSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : posSq p u = normSq (sbDp p r *ᵥ u) := by
  simp only [posSq, normSq, sbDp, mulVec_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem sb_negSq_eq (p : ℕ) {r : ℕ} (u : Fin r → ℂ) : negSq p u = normSq (sbDn p r *ᵥ u) := by
  simp only [negSq, normSq, sbDn, mulVec_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem sb_herm_swap {r : ℕ} {M : Matrix (Fin r) (Fin r) ℂ} (hM : Mᴴ = M) (v w : Fin r → ℂ) :
    star v ⬝ᵥ (M *ᵥ w) = star (M *ᵥ v) ⬝ᵥ w := by
  rw [star_mulVec, hM, dotProduct_mulVec]

theorem sb_dot_Dp (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ (sbDp p r *ᵥ w) = star (sbDp p r *ᵥ v) ⬝ᵥ (sbDp p r *ᵥ w) := by
  have h := sb_herm_swap (sb_Dp_herm p r) v (sbDp p r *ᵥ w)
  rw [mulVec_mulVec, sb_Dp_mul_Dp] at h
  exact h

theorem sb_dot_Dn (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ (sbDn p r *ᵥ w) = star (sbDn p r *ᵥ v) ⬝ᵥ (sbDn p r *ᵥ w) := by
  have h := sb_herm_swap (sb_Dn_herm p r) v (sbDn p r *ᵥ w)
  rw [mulVec_mulVec, sb_Dn_mul_Dn] at h
  exact h

theorem sb_dot_split (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ w = star (sbDp p r *ᵥ v) ⬝ᵥ (sbDp p r *ᵥ w) +
      star (sbDn p r *ᵥ v) ⬝ᵥ (sbDn p r *ᵥ w) := by
  rw [← sb_dot_Dp p v w, ← sb_dot_Dn p v w, ← dotProduct_add, ← add_mulVec, sb_Dp_add_Dn,
    one_mulVec]

theorem sb_dot_J (p : ℕ) {r : ℕ} (v w : Fin r → ℂ) :
    star v ⬝ᵥ (signMat p r *ᵥ w) = star (sbDp p r *ᵥ v) ⬝ᵥ (sbDp p r *ᵥ w) -
      star (sbDn p r *ᵥ v) ⬝ᵥ (sbDn p r *ᵥ w) := by
  rw [sb_signMat_eq, sub_mulVec, dotProduct_sub, sb_dot_Dp p v w, sb_dot_Dn p v w]

private theorem re_star_dotProduct_self_eq_normSq {r : ℕ} (x : Fin r → ℂ) : (star x ⬝ᵥ x).re = normSq x := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, normSq]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (star (x k) * x k).re = (x k).re * (x k).re + (x k).im * (x k).im := by
    simp [Complex.mul_re] <;> ring
  rw [h1, ← Complex.normSq_apply]
  first
    | exact (Complex.sq_norm _).symm
    | exact Complex.normSq_eq_norm_sq _
    | simp [Complex.sq_abs]

theorem sb_re_dot_J (p : ℕ) {r : ℕ} (v : Fin r → ℂ) :
    (star v ⬝ᵥ (signMat p r *ᵥ v)).re = posSq p v - negSq p v := by
  rw [sb_dot_J, Complex.sub_re, re_star_dotProduct_self_eq_normSq, re_star_dotProduct_self_eq_normSq, sb_posSq_eq, sb_negSq_eq]

theorem sb_cs {r : ℕ} (v w : Fin r → ℂ) : (star v ⬝ᵥ w).re ^ 2 ≤ normSq v * normSq w := by
  have h1 : |(star v ⬝ᵥ w).re| ≤ ∑ k, ‖v k‖ * ‖w k‖ := by
    have e1 : |(star v ⬝ᵥ w).re| ≤ ‖star v ⬝ᵥ w‖ := by
      first
        | exact Complex.abs_re_le_norm _
        | exact RCLike.abs_re_le_norm _
        | exact Complex.abs_re_le_abs _
    have e2 : ‖star v ⬝ᵥ w‖ ≤ ∑ k, ‖star (v k) * w k‖ := by
      unfold dotProduct
      exact norm_sum_le _ _
    have e3 : ∑ k, ‖star (v k) * w k‖ = ∑ k, ‖v k‖ * ‖w k‖ := by
      simp [norm_mul, norm_star]
    linarith
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖v k‖) (fun k => ‖w k‖)
  have h3 : (star v ⬝ᵥ w).re ^ 2 ≤ (∑ k, ‖v k‖ * ‖w k‖) ^ 2 :=
    sq_le_sq.mpr (h1.trans (le_abs_self _))
  unfold normSq
  exact h3.trans h2

private theorem two_mul_one_add_mul_le_of_le_mul (a b c d s : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : 0 ≤ s) (hcd : c ≤ s * d) (hs1 : s < 1) (hle : a * c ≤ b * d) :
    2 * (1 + s) * (a * c) ≤ s * (a ^ 2 + d ^ 2) + b ^ 2 + c ^ 2 := by
  rcases eq_or_lt_of_le hd with h0 | hdpos
  · subst h0
    have hc0 : c = 0 := le_antisymm (by simpa using hcd) hc
    subst hc0
    nlinarith [mul_nonneg hs (sq_nonneg a), sq_nonneg b]
  · have hsq : (a * c) * (a * c) ≤ (b * d) * (b * d) :=
      mul_self_le_mul_self (mul_nonneg ha hc) hle
    have hdc : 0 ≤ d - c := by nlinarith
    have hsdc : 0 ≤ s * d - c := by linarith
    have e1 : 0 ≤ (s * d ^ 2 + c ^ 2) * (a - d) ^ 2 :=
      mul_nonneg (add_nonneg (mul_nonneg hs (sq_nonneg d)) (sq_nonneg c)) (sq_nonneg _)
    have e2 : 0 ≤ 2 * a * d * ((d - c) * (s * d - c)) :=
      mul_nonneg (mul_nonneg (mul_nonneg zero_le_two ha) hd) (mul_nonneg hdc hsdc)
    have hd2 : 0 < d ^ 2 := pow_pos hdpos 2
    by_contra hneg
    push_neg at hneg
    have e3 := mul_lt_mul_of_pos_left hneg hd2
    nlinarith

theorem sb_real_bounds (a b c d s t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hs : 0 ≤ s) (hs1 : s < 1) (hba : b ≤ s * a) (hcd : c ≤ s * d) (h1 : |t| ≤ a * c)
    (h2 : |t| ≤ b * d) :
    0 ≤ s * (a ^ 2 + d ^ 2) + b ^ 2 + c ^ 2 + 2 * (1 + s) * t ∧
      0 ≤ s * (a ^ 2 + d ^ 2) - (b ^ 2 + c ^ 2) - 2 * (1 - s) * t := by
  have hTc : |t| ≤ a * c := h1
  have hTad : |t| ≤ s * a * d := by
    have := mul_le_mul_of_nonneg_left hcd ha
    nlinarith
  have hs0 : 0 ≤ 1 - s := by linarith
  have key : 2 * (1 + s) * |t| ≤ s * (a ^ 2 + d ^ 2) + b ^ 2 + c ^ 2 := by
    rcases le_total (a * c) (b * d) with hle | hle
    · have e := two_mul_one_add_mul_le_of_le_mul a b c d s ha hc hd hs hcd hs1 hle
      have e' := mul_le_mul_of_nonneg_left hTc (by linarith : (0 : ℝ) ≤ 2 * (1 + s))
      nlinarith
    · have e := two_mul_one_add_mul_le_of_le_mul d c b a s hd hb ha hs hba hs1
        (by rw [mul_comm d b, mul_comm c a]; exact hle)
      have e' := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ 2 * (1 + s))
      nlinarith
  have htl : 0 ≤ t + |t| := by linarith [neg_abs_le t]
  have htu : t ≤ |t| := le_abs_self t
  have hb2 : b * b ≤ (s * a) * (s * a) := mul_self_le_mul_self hb hba
  have hc2 : c * c ≤ (s * d) * (s * d) := mul_self_le_mul_self hc hcd
  constructor
  · nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (1 + s)) htl]
  · nlinarith [mul_nonneg (mul_nonneg hs hs0) (sq_nonneg (a - d)),
      mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ s * a * d - t)]

end ReciprocityTheory.MultiplicativeHeights
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open Matrix NumberField

theorem latDegBasis_holds : LatDegBasisStatement := by
  intro K _ _ r k H B b b' hH hB hb hb'
  obtain ⟨hbB, hbli, hbsp⟩ := hb
  obtain ⟨hb'B, hb'li, hb'sp⟩ := hb'
  set P := Submodule.span (𝓞 K) (Set.range b) with hP
  set P' := Submodule.span (𝓞 K) (Set.range b') with hP'
  obtain ⟨D, hD, hDB⟩ := exists_smul_le_span b B hB hbsp
  have hcoef : ∀ j, ∃ c : Fin k → 𝓞 K, ∑ i, c i • b i = D • b' j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).mp (hDB _ (hb'B j))
  choose m hm using hcoef
  set M : Matrix (Fin k) (Fin k) (𝓞 K) := Matrix.of fun i j => m j i with hMdef
  set Dm : Matrix (Fin k) (Fin k) (𝓞 K) := Matrix.diagonal fun _ => D with hDm
  have hcM : (fun j => ∑ i, M i j • b i) = fun j => D • b' j := by
    funext j
    exact hm j
  have hcD : (fun j => ∑ i, Dm i j • b' i) = fun j => D • b' j := comb_diagonal b' D
  set NK := M.map (algebraMap (𝓞 K) K) with hNK
  set DK := Dm.map (algebraMap (𝓞 K) K) with hDK
  have hcMK : (fun j => ∑ i, NK i j • b i) = fun j => D • b' j := by
    rw [← hcM]
    funext j
    simp [NK, algebraMap_smul]
  have hcDK : (fun j => ∑ i, DK i j • b' i) = fun j => D • b' j := by
    rw [← hcD]
    funext j
    simp [DK, algebraMap_smul]
  have hNKdet : NK.det = algebraMap (𝓞 K) K M.det := (RingHom.map_det _ M).symm
  have hDKdet : DK.det = algebraMap (𝓞 K) K Dm.det := (RingHom.map_det _ Dm).symm
  have hgc : ∀ σ : K →+* ℂ, (gramC (H σ) σ (fun j => D • b' j)).det =
      ((Complex.normSq (σ NK.det) : ℝ) : ℂ) * (gramC (H σ) σ b).det := fun σ => by
    rw [← hcMK]
    exact det_gramC_comb _ _ _ _
  have hgc' : ∀ σ : K →+* ℂ, (gramC (H σ) σ (fun j => D • b' j)).det =
      ((Complex.normSq (σ DK.det) : ℝ) : ℂ) * (gramC (H σ) σ b').det := fun σ => by
    rw [← hcDK]
    exact det_gramC_comb _ _ _ _
  have hpos : ∀ σ : K →+* ℂ, 0 < (gramC (H σ) σ b).det.re := fun σ =>
    gramC_det_re_pos (H σ) σ b (hH σ) hbli
  have hpos' : ∀ σ : K →+* ℂ, 0 < (gramC (H σ) σ b').det.re := fun σ =>
    gramC_det_re_pos (H σ) σ b' (hH σ) hb'li
  have hDmdet : Dm.det ≠ 0 := by
    simp [Dm, Matrix.det_diagonal, hD]
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
  have hDKne : DK.det ≠ 0 := by
    rw [hDKdet, ← map_zero (algebraMap (𝓞 K) K)]
    exact hinj.ne hDmdet
  have hre : ∀ σ : K →+* ℂ, Complex.normSq (σ NK.det) * (gramC (H σ) σ b).det.re =
      Complex.normSq (σ DK.det) * (gramC (H σ) σ b').det.re := fun σ => by
    have := congrArg Complex.re ((hgc σ).symm.trans (hgc' σ))
    simpa [Complex.re_ofReal_mul] using this
  have hNKne : NK.det ≠ 0 := by
    intro h0
    have h := hre (Classical.arbitrary (K →+* ℂ))
    rw [h0, map_zero, map_zero, zero_mul] at h
    have h1 : 0 < Complex.normSq ((Classical.arbitrary (K →+* ℂ)) DK.det) :=
      Complex.normSq_pos.mpr (by simpa using hDKne)
    have h2 := hpos' (Classical.arbitrary (K →+* ℂ))
    nlinarith
  have hMdet : M.det ≠ 0 := by
    intro h0
    apply hNKne
    rw [hNKdet, h0, map_zero]
  set C := Submodule.span (𝓞 K) (Set.range (fun j => D • b' j)) with hC
  have hIdx1 := relIndex_span_comb b hbli M hMdet
  rw [hcM] at hIdx1
  have hIdx2 := relIndex_span_comb b' hb'li Dm hDmdet
  rw [hcD] at hIdx2
  have hPB : P ≤ B := Submodule.span_le.mpr (Set.range_subset_iff.mpr hbB)
  have hP'B : P' ≤ B := Submodule.span_le.mpr (Set.range_subset_iff.mpr hb'B)
  have hCP : C ≤ P := Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => hDB _ (hb'B j))
  have hCP' : C ≤ P' := Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j =>
    Submodule.smul_mem _ D (Submodule.subset_span ⟨j, rfl⟩))
  have mul1 := AddSubgroup.relIndex_mul_relIndex C.toAddSubgroup P.toAddSubgroup B.toAddSubgroup
    hCP hPB
  have mul2 := AddSubgroup.relIndex_mul_relIndex C.toAddSubgroup P'.toAddSubgroup B.toAddSubgroup
    hCP' hP'B
  have hI := relIndex_span_ne_zero b hbli B hbB D hD hDB
  have e1 : ((Algebra.norm ℤ M.det : ℤ) : ℝ) = ((Algebra.norm ℚ NK.det : ℚ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) (Algebra.coe_norm_int M.det)
    simp only [Rat.cast_intCast] at this
    rw [hNKdet]
    convert this using 3
  have e2 : ((Algebra.norm ℤ Dm.det : ℤ) : ℝ) = ((Algebra.norm ℚ DK.det : ℚ) : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) (Algebra.coe_norm_int Dm.det)
    simp only [Rat.cast_intCast] at this
    rw [hDKdet]
    convert this using 3
  have hcP : ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) =
      |((Algebra.norm ℚ NK.det : ℚ) : ℝ)| := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hIdx1
    simp only [Int.cast_natCast, Int.cast_abs] at this
    rw [this, e1]
  have hcP' : ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) =
      |((Algebra.norm ℚ DK.det : ℚ) : ℝ)| := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hIdx2
    simp only [Int.cast_natCast, Int.cast_abs] at this
    rw [this, e2]
  have hnM : ((Algebra.norm ℚ NK.det : ℚ) : ℝ) ≠ 0 :=
    Rat.cast_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hNKne)
  have hnD : ((Algebra.norm ℚ DK.det : ℚ) : ℝ) ≠ 0 :=
    Rat.cast_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hDKne)
  have hmulR : ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) *
      ((P.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) =
      ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) *
      ((P'.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) := by
    exact_mod_cast mul1.trans mul2.symm
  have hcPne : ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) ≠ 0 := by
    rw [hcP]
    exact abs_ne_zero.mpr hnM
  have hcP'ne : ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) ≠ 0 := by
    rw [hcP']
    exact abs_ne_zero.mpr hnD
  have hIne : ((P.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hI
  have hI'ne : ((P'.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hmulR
    exact mul_ne_zero hcPne hIne hmulR
  have hlog : Real.log ((C.toAddSubgroup.relIndex P.toAddSubgroup : ℕ) : ℝ) +
      Real.log ((P.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) =
      Real.log ((C.toAddSubgroup.relIndex P'.toAddSubgroup : ℕ) : ℝ) +
      Real.log ((P'.toAddSubgroup.relIndex B.toAddSubgroup : ℕ) : ℝ) := by
    rw [← Real.log_mul hcPne hIne, ← Real.log_mul hcP'ne hI'ne, hmulR]
  rw [hcP, hcP'] at hlog
  have hsum : ∑ σ : K →+* ℂ, (Real.log (Complex.normSq (σ NK.det)) +
      Real.log (gramC (H σ) σ b).det.re) = ∑ σ : K →+* ℂ, (Real.log (Complex.normSq (σ DK.det)) +
      Real.log (gramC (H σ) σ b').det.re) := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    have h1 : Complex.normSq (σ NK.det) ≠ 0 := (Complex.normSq_pos.mpr (by simpa using hNKne)).ne'
    have h2 : Complex.normSq (σ DK.det) ≠ 0 := (Complex.normSq_pos.mpr (by simpa using hDKne)).ne'
    rw [← Real.log_mul h1 (hpos σ).ne', ← Real.log_mul h2 (hpos' σ).ne', hre σ]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_log_normSq _ hNKne,
    sum_log_normSq _ hDKne] at hsum
  simp only [latDeg]
  linarith

end ReciprocityTheory.MultiplicativeHeights
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Real Function

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma slice_abs_integral_le (f : MvPolynomial ι ℂ) (i : ι) (θ : ι → ℝ) :
    ∫ t, ‖tmLog f (update θ i t)‖ ∂unitIntervalMeasure ≤
      2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) +
        ∑ k ∈ Finset.range (f.support.sup (fun s => s i) + 1), |tmLog (coeffIn i k f) θ| := by
  have hu : ∀ t, tmLog f (update θ i t) =
      Real.log ‖(tmSlice i (torusPoint θ) f).eval (circPt t)‖ := tmLog_update f θ i
  have hL : 0 ≤ posLog (∑ s ∈ f.support, ‖f.coeff s‖) := posLog_nonneg
  have hI : Integrable (fun t => tmLog f (update θ i t)) unitIntervalMeasure := by
    simp_rw [hu]; exact integrableOn_log_circ _
  have h1 : ∫ t, ‖tmLog f (update θ i t)‖ ∂unitIntervalMeasure ≤
      ∫ t, (2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) - tmLog f (update θ i t)) ∂unitIntervalMeasure := by
    refine integral_mono hI.norm ((integrable_const _).sub hI) fun t => ?_
    have := tmLog_le f (update θ i t)
    simp only [Real.norm_eq_abs]
    rcases abs_cases (tmLog f (update θ i t)) with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have h2 : ∫ t, (2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) - tmLog f (update θ i t)) ∂unitIntervalMeasure =
      2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) -
        (tmSlice i (torusPoint θ) f).logMahlerMeasure := by
    rw [integral_sub (integrable_const _) hI, integral_const]
    simp_rw [hu]
    rw [integral_log_circ]
    simp
  have h3 : |Real.log ‖(tmSlice i (torusPoint θ) f).leadingCoeff‖| ≤
      ∑ k ∈ Finset.range (f.support.sup (fun s => s i) + 1), |tmLog (coeffIn i k f) θ| := by
    rw [Polynomial.leadingCoeff, tmSlice_coeff]
    by_cases hn : (tmSlice i (torusPoint θ) f).natDegree < f.support.sup (fun s => s i) + 1
    · exact Finset.single_le_sum (f := fun k => |tmLog (coeffIn i k f) θ|)
        (fun k _ => abs_nonneg _) (Finset.mem_range.mpr hn)
    · rw [coeffIn_eq_zero_of_lt i f _ (by omega)]
      simp only [map_zero, norm_zero, Real.log_zero, abs_zero]
      exact Finset.sum_nonneg fun k _ => abs_nonneg _
  have h4 := log_norm_leadingCoeff_le (tmSlice i (torusPoint θ) f)
  have h5 := neg_abs_le (Real.log ‖(tmSlice i (torusPoint θ) f).leadingCoeff‖)
  linarith

lemma integrable_log_abs_on_torus (S : Finset ι) :
    ∀ f : MvPolynomial ι ℂ, f.vars ⊆ S → Integrable (tmLog f) (torusProb ι) := by
  induction S using Finset.induction_on with
  | empty =>
    intro f hS
    have : tmLog f = fun _ => Real.log ‖MvPolynomial.constantCoeff f‖ := by
      funext θ; simp [tmLog, eval_const_of_vars_empty f hS]
    rw [this]; exact integrable_const _
  | insert i S' hi ih =>
    intro f hS
    have hsub : ∀ k, (coeffIn i k f).vars ⊆ S' := by
      intro k j hj
      have h1 := vars_coeffIn_subset i k f hj
      rw [Finset.mem_erase] at h1
      have h2 := hS h1.2
      rw [Finset.mem_insert] at h2
      exact h2.resolve_left h1.1
    have hmeas : AEStronglyMeasurable (tmLog f ∘ tmUpd i) ((torusProb ι).prod unitIntervalMeasure) :=
      ((measurable_tmLog f).comp (measurable_tmUpd i)).aestronglyMeasurable
    rw [← tm_integrable_comp i (measurable_tmLog f).aestronglyMeasurable,
      integrable_prod_iff hmeas]
    refine ⟨Filter.Eventually.of_forall fun θ => ?_, ?_⟩
    · show Integrable (fun t => tmLog f (update θ i t)) unitIntervalMeasure
      simp_rw [tmLog_update]
      exact integrableOn_log_circ _
    · have hG : Integrable (fun θ => 2 * posLog (∑ s ∈ f.support, ‖f.coeff s‖) +
          ∑ k ∈ Finset.range (f.support.sup (fun s => s i) + 1), |tmLog (coeffIn i k f) θ|)
          (torusProb ι) :=
        (integrable_const _).add (integrable_finsetSum _ fun k _ => (ih _ (hsub k)).abs)
      refine hG.mono' hmeas.norm.integral_prod_right' (Filter.Eventually.of_forall fun θ => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact slice_abs_integral_le f i θ

lemma tm_int (f : MvPolynomial ι ℂ) : Integrable (tmLog f) (torusProb ι) :=
  integrable_log_abs_on_torus Finset.univ f (Finset.subset_univ _)

lemma tm_ae_ne (f : MvPolynomial ι ℂ) (hf : f ≠ 0) :
    ∀ᵐ θ ∂(torusProb ι), MvPolynomial.eval (torusPoint θ) f ≠ 0 := by
  rw [ae_iff]; simpa using tm_null f hf

end ReciprocityTheory.MultiplicativeHeights
end
end
