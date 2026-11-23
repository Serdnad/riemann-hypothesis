module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.PSeries
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle111
import Mathlib.Analysis.Fourier.Notation
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

noncomputable section

namespace GlobalTheory.LipschitzTR.LhsSum

variable {F : Type} [Field F] [NumberField F]

theorem prod_realEmb_eq_norm [IsTotallyReal F] (x : F) :
    (∏ τ : F →+* ℝ, τ x) = ((Algebra.norm ℚ x : ℚ) : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ x
  rw [show ((Algebra.norm ℚ x : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ x) from rfl, h]
  have hb : Function.Bijective (fun τ : F →+* ℝ => Complex.ofRealHom.comp τ) := by
    refine ⟨fun τ τ' h => ?_, fun φ => ?_⟩
    · ext x
      exact Complex.ofReal_injective (RingHom.congr_fun h x)
    · exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, RingHom.ext fun x =>
        (IsTotallyReal.complexEmbedding_isReal φ).coe_embedding_apply x⟩
  refine Fintype.prod_bijective (fun τ : F →+* ℝ => RingHom.equivRatAlgHom F ℂ (Complex.ofRealHom.comp τ))
    ((RingHom.equivRatAlgHom F ℂ).bijective.comp hb) _ _ (fun τ => ?_)
  rfl

theorem one_le_abs_prod_int [IsTotallyReal F] (y : 𝓞 F) (hy : y ≠ 0) :
    1 ≤ |∏ τ : F →+* ℝ, τ (y : F)| := by
  rw [prod_realEmb_eq_norm, ← Algebra.coe_norm_int]
  have h : Algebra.norm ℤ y ≠ 0 := Algebra.norm_ne_zero_iff.2 hy
  have h1 : (1 : ℤ) ≤ |Algebra.norm ℤ y| := Int.one_le_abs h
  have h2 : (((Algebra.norm ℤ y : ℤ) : ℚ) : ℝ) = ((Algebra.norm ℤ y : ℤ) : ℝ) := by push_cast; rfl
  rw [h2]
  exact_mod_cast h1

theorem exists_lower_norm [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ ν : ℝ, 0 < ν ∧ ∀ a ∈ M, a ≠ 0 → ν ≤ |∏ τ : F →+* ℝ, τ a| := by
  obtain ⟨d, hd, hint⟩ := M.isFractional
  have hd0 : (d : F) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hd
    exact_mod_cast this
  have hP : 0 < |∏ τ : F →+* ℝ, τ (d : F)| :=
    abs_pos.2 (Finset.prod_ne_zero_iff.2 fun τ _ => (map_ne_zero τ).2 hd0)
  refine ⟨1 / |∏ τ : F →+* ℝ, τ (d : F)|, by positivity, fun a ha ha0 => ?_⟩
  obtain ⟨y, hy⟩ := hint a ha
  have hy' : (y : F) = (d : F) * a := by
    rw [← Algebra.smul_def]; exact hy
  have hy0 : y ≠ 0 := by
    intro h; apply mul_ne_zero hd0 ha0; rw [← hy', h]; simp
  have h1 := one_le_abs_prod_int y hy0
  rw [hy'] at h1
  simp only [map_mul, Finset.prod_mul_distrib, abs_mul] at h1
  rw [div_le_iff₀ hP]
  linarith [mul_comm (|∏ τ : F →+* ℝ, τ (d : F)|) (|∏ τ : F →+* ℝ, τ a|)]

theorem exists_lower_one_add (w : ℂ) (hw : w.im ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, c * (1 + |t|) ≤ ‖w + (t : ℂ)‖ := by
  have him : 0 < |w.im| := abs_pos.2 hw
  refine ⟨|w.im| / (|w.im| + 1 + ‖w‖), by positivity, fun t => ?_⟩
  have h1 : |w.im| ≤ ‖w + (t : ℂ)‖ := by
    have := Complex.abs_im_le_norm (w + (t : ℂ))
    simpa using this
  have h2 : |t| ≤ ‖w + (t : ℂ)‖ + ‖w‖ := by
    have := norm_sub_le (w + (t : ℂ)) w
    simp only [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs] at this
    exact this
  have hn : 0 ≤ ‖w‖ := norm_nonneg _
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

theorem floor_bound {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (x : ℝ) :
    s / 2 * (1 + |((⌊x / s⌋ : ℤ) : ℝ)|) ≤ 1 + |x| := by
  set n : ℤ := ⌊x / s⌋ with hn
  have h1 : (n : ℝ) ≤ x / s := Int.floor_le _
  have h2 : x / s < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have h1' : (n : ℝ) * s ≤ x := by rwa [le_div_iff₀ hs0] at h1
  have h2' : x < ((n : ℝ) + 1) * s := by rwa [div_lt_iff₀ hs0] at h2
  rcases le_or_gt 0 (n : ℝ) with hn0 | hn0
  · rw [abs_of_nonneg hn0, abs_of_nonneg (by nlinarith)]
    nlinarith
  · have hn1 : (n : ℝ) ≤ -1 := by
      have : n ≤ -1 := by
        have : n < 0 := by exact_mod_cast hn0
        omega
      exact_mod_cast this
    rw [abs_of_neg hn0]
    have : |x| ≥ -x := neg_le_abs x
    nlinarith

def wt (m : ℤ) : ℝ := ((1 + |(m : ℝ)|) ^ 2)⁻¹

theorem wt_nonneg (m : ℤ) : 0 ≤ wt m := by unfold wt; positivity

theorem summable_wt : Summable wt := by
  have hA : Summable (fun m : ℤ => |(m : ℝ)| ^ (-(2 : ℝ))) := Real.summable_abs_int_rpow (by norm_num)
  have hB : Summable (fun m : ℤ => if m = 0 then (1 : ℝ) else 0) := (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  refine Summable.of_nonneg_of_le wt_nonneg (fun m => ?_) (hA.add hB)
  by_cases hm : m = 0
  · subst hm
    simp [wt, Real.zero_rpow]
  · simp only [hm, if_false, add_zero]
    have hm1 : (1 : ℝ) ≤ |(m : ℝ)| := by
      have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm
      exact_mod_cast this
    rw [Real.rpow_neg (abs_nonneg _), wt]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    apply inv_anti₀ (by positivity)
    nlinarith [abs_nonneg (m : ℝ)]

theorem summable_prod_wt (ι : Type) [Fintype ι] [DecidableEq ι] :
    Summable (fun n : ι → ℤ => ∏ i, wt (n i)) := by
  refine summable_of_sum_le (c := ∏ _i : ι, ∑' m, wt m)
    (fun n => Finset.prod_nonneg fun i _ => wt_nonneg _) (fun u => ?_)
  calc ∑ n ∈ u, ∏ i, wt (n i)
      ≤ ∑ n ∈ Fintype.piFinset (fun i => u.image (fun n : ι → ℤ => n i)), ∏ i, wt (n i) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rw [Fintype.mem_piFinset]
          intro i
          exact Finset.mem_image_of_mem _ hn
        · intro n _ _
          exact Finset.prod_nonneg fun i _ => wt_nonneg _
    _ = ∏ i, ∑ m ∈ u.image (fun n : ι → ℤ => n i), wt m := (Finset.prod_univ_sum _ _).symm
    _ ≤ ∏ _i : ι, ∑' m, wt m := by
        apply Finset.prod_le_prod₀
        · intro i _; exact Finset.sum_nonneg fun m _ => wt_nonneg m
        · intro i _; exact summable_wt.sum_le_tsum _ (fun m _ => wt_nonneg m)

end GlobalTheory.LipschitzTR.LhsSum


open GlobalTheory.LipschitzTR.LhsSum in
theorem GlobalTheory.LipschitzTR.summable_lhsTerm_ideal :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F), M ≠ 0 →
      ∀ (k : ℕ), 2 ≤ k → ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) →
        Summable (fun a : (M : Set F) => lhsTerm k z a) := by
  intro F _ _ _ M _ k hk z hz
  classical
  obtain ⟨ν, hν0, hν⟩ := exists_lower_norm M
  have hcard : 0 < Fintype.card (F →+* ℝ) := by
    rw [card_realEmb]; exact Module.finrank_pos
  set s : ℝ := min 1 (ν / 2) with hs
  have hs0 : 0 < s := lt_min one_pos (by positivity)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsν : s ^ Fintype.card (F →+* ℝ) < ν :=
    lt_of_le_of_lt (pow_le_of_le_one hs0.le hs1 hcard.ne') (lt_of_le_of_lt (min_le_right _ _) (by linarith))
  let N : ↥(M : Set F) → ((F →+* ℝ) → ℤ) := fun a τ => ⌊τ (a : F) / s⌋
  have hN : Function.Injective N := by
    intro a b hab
    by_contra hne
    have hne' : (a : F) - b ≠ 0 := sub_ne_zero.2 (fun h => hne (Subtype.ext h))
    have hmem : (a : F) - b ∈ M := (M : Submodule (𝓞 F) F).sub_mem a.2 b.2
    have h1 := hν _ hmem hne'
    have h2 : |∏ τ : F →+* ℝ, τ ((a : F) - b)| ≤ s ^ Fintype.card (F →+* ℝ) := by
      rw [Finset.abs_prod, ← Finset.card_univ, ← Finset.prod_const]
      refine Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun τ _ => ?_)
      have hf := Int.abs_sub_lt_one_of_floor_eq_floor (congrFun hab τ)
      rw [← sub_div, abs_div, abs_of_pos hs0, div_lt_one hs0] at hf
      rw [map_sub]; exact hf.le
    linarith
  have hc : ∀ τ : F →+* ℝ, ∃ c : ℝ, 0 < c ∧ ∀ t : ℝ, c * (1 + |t|) ≤ ‖z τ + (t : ℂ)‖ :=
    fun τ => exists_lower_one_add (z τ) (hz τ)
  choose c hc0 hc using hc
  set C : ℝ := ∏ τ : F →+* ℝ, ((c τ * (s / 2)) ^ k)⁻¹ with hC
  refine Summable.of_norm_bounded (g := fun a => C * ∏ τ, wt (N a τ))
    (((summable_prod_wt (F →+* ℝ)).comp_injective hN).mul_left C) (fun a => ?_)
  simp only [lhsTerm, zpow_neg, zpow_natCast, ← Finset.prod_pow, ← Finset.prod_inv_distrib, norm_prod, norm_inv, norm_pow]
  rw [hC, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun τ _ => ?_)
  have hD : 0 < c τ * (s / 2) := by have := hc0 τ; positivity
  have hfl := floor_bound hs0 hs1 (τ (a : F))
  have he : c τ * (s / 2) * (1 + |((N a τ : ℤ) : ℝ)|) ≤ ‖z τ + ((τ (a : F) : ℝ) : ℂ)‖ := by
    calc c τ * (s / 2) * (1 + |((N a τ : ℤ) : ℝ)|) = c τ * (s / 2 * (1 + |((N a τ : ℤ) : ℝ)|)) := by ring
      _ ≤ c τ * (1 + |τ (a : F)|) := mul_le_mul_of_nonneg_left hfl (hc0 τ).le
      _ ≤ _ := hc τ _
  have hone : (1 : ℝ) ≤ 1 + |((N a τ : ℤ) : ℝ)| := by linarith [abs_nonneg ((N a τ : ℤ) : ℝ)]
  rw [wt, ← mul_inv]
  apply inv_anti₀ (by positivity)
  calc (c τ * (s / 2)) ^ k * (1 + |((N a τ : ℤ) : ℝ)|) ^ 2
      ≤ (c τ * (s / 2)) ^ k * (1 + |((N a τ : ℤ) : ℝ)|) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hone hk) (by positivity)
    _ = (c τ * (s / 2) * (1 + |((N a τ : ℤ) : ℝ)|)) ^ k := by rw [mul_pow (c τ * (s / 2))]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) he k
end
end

section

open scoped NNReal

namespace GlobalTheory.DetRelCompare

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

section Core

variable {C : Type} [Field C]

theorem eq_sum_rows {n : ℕ} (U : Fin n → Fin n → C) (h : (Matrix.of U).det ≠ 0)
    (f : Fin n → C) : ∃ γ : Fin n → C, f = ∑ s, γ s • U s := by
  refine ⟨Matrix.vecMul f (Matrix.of U)⁻¹, ?_⟩
  have hu : IsUnit (Matrix.of U).det := isUnit_iff_ne_zero.mpr h
  have key : Matrix.vecMul (Matrix.vecMul f (Matrix.of U)⁻¹) (Matrix.of U) = f := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hu, Matrix.vecMul_one]
  funext j
  conv_lhs => rw [← key]
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

theorem exists_eq_sum_of_mem {p q : ℕ} (F : Submodule C (Fin (p + q) → C))
    (u0 : Fin p → Fin (p + q) → C) (m0 : Fin q → Fin (p + q) → C)
    (hli : LinearIndependent C fun i => F.mkQ (u0 i)) (hm0 : ∀ k, m0 k ∈ F)
    (hN : (Matrix.of (Fin.append u0 m0)).det ≠ 0) (f : Fin (p + q) → C) (hf : f ∈ F) :
    ∃ β : Fin q → C, f = ∑ k, β k • m0 k := by
  obtain ⟨γ, hγ⟩ := eq_sum_rows _ hN f
  rw [Fin.sum_univ_add] at hγ
  simp only [Fin.append_left, Fin.append_right] at hγ
  have hz : ∑ i, γ (Fin.castAdd q i) • F.mkQ (u0 i) = 0 := by
    have h1 := congrArg F.mkQ hγ
    have hf0 : F.mkQ f = 0 := by simpa using hf
    have hm : ∑ k, γ (Fin.natAdd p k) • F.mkQ (m0 k) = 0 :=
      Finset.sum_eq_zero fun k _ => by simp [hm0 k]

    rw [hf0, map_add (f := _), map_sum, map_sum] at h1
    simp only [map_smul] at h1
    rw [hm, add_zero] at h1
    exact h1.symm
  have h0 := Fintype.linearIndependent_iff.1 hli _ hz
  exact ⟨fun k => γ (Fin.natAdd p k), by rw [hγ]; simp [h0]⟩

theorem det_append_eq {p q : ℕ} (F : Submodule C (Fin (p + q) → C))
    (u u0 : Fin p → Fin (p + q) → C) (m m0 : Fin q → Fin (p + q) → C)
    (A : Matrix (Fin p) (Fin p) C) (B : Matrix (Fin q) (Fin q) C)
    (hu : ∀ i, F.mkQ (u i) = ∑ j, A i j • F.mkQ (u0 j))
    (hm : ∀ i, m i = ∑ j, B i j • m0 j)
    (hli : LinearIndependent C fun i => F.mkQ (u0 i))
    (hm0 : ∀ k, m0 k ∈ F) (hN : (Matrix.of (Fin.append u0 m0)).det ≠ 0) :
    (Matrix.of (Fin.append u m)).det = A.det * B.det * (Matrix.of (Fin.append u0 m0)).det := by
  have hmem : ∀ i, u i - ∑ j, A i j • u0 j ∈ F := by
    intro i
    have : F.mkQ (u i - ∑ j, A i j • u0 j) = 0 := by

      rw [map_sub, map_sum, hu i]; simp only [map_smul]; exact sub_self _
    rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
  choose β hβ using fun i => exists_eq_sum_of_mem F u0 m0 hli hm0 hN _ (hmem i)
  have key : (Matrix.of (Fin.append u m)).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks A (Matrix.of β) 0 B *
        (Matrix.of (Fin.append u0 m0)).submatrix finSumFinEquiv finSumFinEquiv := by
    ext r c
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    rcases r with i | k
    · have hi : u i = ∑ j, A i j • u0 j + ∑ k, β i k • m0 k := by rw [← hβ i]; abel
      simp [Matrix.fromBlocks, hi, Finset.sum_apply]
    · simp [Matrix.fromBlocks, hm k, Finset.sum_apply]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, key, Matrix.det_mul,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_submatrix_equiv_self]

theorem comp_sum {W : Type} [AddCommGroup W] [Module C W] {n k l : ℕ} (a : Fin n → W)
    (b : Fin k → W) (c : Fin l → W) (P : Matrix (Fin k) (Fin n) C)
    (Q : Matrix (Fin l) (Fin k) C) (hb : ∀ i, b i = ∑ j, P i j • a j)
    (hc : ∀ i, c i = ∑ j, Q i j • b j) : ∀ i, c i = ∑ j, (Q * P) i j • a j := by
  intro i
  simp only [hc i, hb, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
  exact Finset.sum_comm

end Core

section Lattice

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

theorem coeffs {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] {n k : ℕ} (a : Fin n → W) (b : Fin k → W)
    (h : ∀ i, b i ∈ Submodule.span w.valuationSubring (Set.range a)) :
    ∃ P : Matrix (Fin k) (Fin n) w.valuationSubring,
      ∀ i, b i = ∑ j, algebraMap w.valuationSubring C (P i j) • a j := by
  choose P hP using fun i =>
    (Submodule.mem_span_range_iff_exists_fun w.valuationSubring).1 (h i)
  exact ⟨Matrix.of P, fun i => by
    rw [← hP i]; exact Finset.sum_congr rfl fun j _ => (algebraMap_smul C (P i j) (a j)).symm⟩

theorem mem_span_of_isLatticeBasis {W : Type} [AddCommGroup W] [Module C W]
    [Module w.valuationSubring W] [IsScalarTower w.valuationSubring C W] {n k : ℕ}
    {a : Fin n → W} {b : Fin k → W} {Y : Submodule w.valuationSubring W}
    (ha : IsLatticeBasis w a Y) (hb : IsLatticeBasis w b Y) (i : Fin k) :
    b i ∈ Submodule.span w.valuationSubring (Set.range a) := by
  rw [ha.2, ← hb.2]; exact Submodule.subset_span ⟨i, rfl⟩

theorem transition {W : Type} [AddCommGroup W] [Module C W] [Module w.valuationSubring W]
    [IsScalarTower w.valuationSubring C W] {n : ℕ} (a b : Fin n → W)
    (Y : Submodule w.valuationSubring W) (ha : IsLatticeBasis w a Y)
    (hb : IsLatticeBasis w b Y) :
    ∃ P : Matrix (Fin n) (Fin n) C, (∀ i, b i = ∑ j, P i j • a j) ∧ w P.det = 1 := by
  obtain ⟨P, hP⟩ := coeffs a b (mem_span_of_isLatticeBasis ha hb)
  obtain ⟨Q, hQ⟩ := coeffs b a (mem_span_of_isLatticeBasis hb ha)
  have hQP := comp_sum a b a (P.map (algebraMap w.valuationSubring C))
    (Q.map (algebraMap w.valuationSubring C)) hP hQ
  have hone : (Q.map (algebraMap w.valuationSubring C)) * (P.map (algebraMap w.valuationSubring C))
      = 1 := by
    ext i j
    have h := Fintype.linearIndependent_iff.1 ha.1
      (fun j => ((Q.map (algebraMap w.valuationSubring C)) *
        (P.map (algebraMap w.valuationSubring C))) i j - (1 : Matrix (Fin n) (Fin n) C) i j)
      (by
        simp only [sub_smul, Finset.sum_sub_distrib]
        rw [← hQP i]
        simp [Matrix.one_apply])
      j
    exact sub_eq_zero.1 h
  have hdet := congrArg Matrix.det hone
  rw [Matrix.det_mul, Matrix.det_one] at hdet
  have hle : ∀ R : Matrix (Fin n) (Fin n) w.valuationSubring,
      w (R.map (algebraMap w.valuationSubring C)).det ≤ 1 := by
    intro R
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ValuationSubring.algebraMap_apply]
    exact (w.mem_valuationSubring_iff _).1 R.det.2
  refine ⟨P.map (algebraMap w.valuationSubring C), fun i => hP i, le_antisymm (hle P) ?_⟩
  calc (1 : ℝ≥0) = w (Q.map (algebraMap w.valuationSubring C)).det *
        w (P.map (algebraMap w.valuationSubring C)).det := by rw [← map_mul, hdet, map_one]
    _ ≤ w (P.map (algebraMap w.valuationSubring C)).det :=
        mul_le_of_le_one_left (by positivity) (hle Q)

end Lattice

end GlobalTheory.DetRelCompare

namespace GlobalTheory.DetRelCompare

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

end GlobalTheory.DetRelCompare
end

section

open scoped NNReal

namespace GlobalTheory.Div.KerFil
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

theorem smul_vec_apply {r : ℕ} (b : w.valuationSubring) (v : Fin r → C) (i : Fin r) :
    (b • v) i = (b : C) * v i := rfl

theorem smul_C (b : w.valuationSubring) (z : C) : b • z = (b : C) * z := rfl

theorem smul_pi_apply {S : Type} {r : ℕ} (b : w.valuationSubring) (x : S → Fin r → C) (s : S)
    (i : Fin r) : (b • x) s i = (b : C) * x s i := rfl

theorem exists_prod_apply {S : Type} [DecidableEq S] {r : ℕ} (a : S → w.valuationSubring)
    (Fil : Submodule w.valuationSubring (S → Fin r → C))
    (hst : ∀ x ∈ Fil, unif a x ∈ Fil) (x : S → Fin r → C) (hx : x ∈ Fil) (T : Finset S) :
    ∃ y ∈ Fil, ∀ s' i, y s' i = (∏ s ∈ T, ((a s' : C) - a s)) * x s' i := by
  induction T using Finset.induction_on with
  | empty => exact ⟨x, hx, fun _ _ => by simp⟩
  | insert s0 T hs0 ih =>
    obtain ⟨y, hy, hyv⟩ := ih
    refine ⟨unif a y - a s0 • y, sub_mem (hst y hy) (Fil.smul_mem _ hy), fun s' i => ?_⟩
    rw [Finset.prod_insert hs0]
    simp only [Pi.sub_apply, unif, Pi.smul_apply, smul_eq_mul]
    rw [smul_C, hyv]
    ring

theorem single_mem_of_mem {S : Type} [Fintype S] [DecidableEq S] {r : ℕ}
    (a : S → w.valuationSubring) (Fil : Submodule w.valuationSubring (S → Fin r → C))
    (hst : ∀ x ∈ Fil, unif a x ∈ Fil) (τ : S) (x : S → Fin r → C) (hx : x ∈ Fil) :
    (Pi.single τ (diffGen a τ • x τ) : S → Fin r → C) ∈ Fil := by
  obtain ⟨y, hy, hyv⟩ := exists_prod_apply a Fil hst x hx (Finset.univ.erase τ)
  convert hy using 1
  funext s' i
  rw [hyv]
  by_cases e : s' = τ
  · subst e
    simp only [Pi.single_eq_same, smul_vec_apply, diffGen]
    push_cast
    rfl
  · rw [Finset.prod_eq_zero (i := s') (Finset.mem_erase.2 ⟨e, Finset.mem_univ _⟩) (sub_self _)]
    simp [e]

theorem diffGen_ne_zero {S : Type} [Fintype S] [DecidableEq S] (a : S → w.valuationSubring)
    (ha : Function.Injective a) (τ : S) : diffGen a τ ≠ 0 := by
  rw [diffGen, Finset.prod_ne_zero_iff]
  intro s hs e
  exact (Finset.mem_erase.1 hs).1 (ha (sub_eq_zero.1 e)).symm

end GlobalTheory.Div.KerFil

namespace GlobalTheory.Div.KerFil
open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

variable {C : Type} [Field C] {w : Valuation C ℝ≥0}

def clearDen {S : Type} [DecidableEq S] {r : ℕ}
    (Fil : Submodule w.valuationSubring (S → Fin r → C)) (τ : S) : Submodule C (Fin r → C) where
  carrier := {v | ∃ b : w.valuationSubring, b ≠ 0 ∧ (Pi.single τ (b • v) : S → Fin r → C) ∈ Fil}
  zero_mem' := ⟨1, one_ne_zero, by simp⟩
  add_mem' := by
    rintro v v' ⟨b, hb, h⟩ ⟨b', hb', h'⟩
    refine ⟨b * b', mul_ne_zero hb hb', ?_⟩
    have : (Pi.single τ ((b * b') • (v + v')) : S → Fin r → C) =
        b' • (Pi.single τ (b • v) : S → Fin r → C) + b • (Pi.single τ (b' • v') : S → Fin r → C) := by
      funext s i
      by_cases e : s = τ
      · subst e; simp only [Pi.single_eq_same, Pi.add_apply, smul_pi_apply, smul_vec_apply]
        push_cast; ring
      · simp [e]
    rw [this]
    exact add_mem (Fil.smul_mem _ h) (Fil.smul_mem _ h')
  smul_mem' := by
    rintro c v ⟨b, hb, h⟩
    by_cases hc0 : c = 0
    · exact ⟨1, one_ne_zero, by simp [hc0]⟩
    rcases w.valuationSubring.mem_or_inv_mem c with hc | hc
    · refine ⟨b, hb, ?_⟩
      have : (Pi.single τ (b • c • v) : S → Fin r → C) =
          (⟨c, hc⟩ : w.valuationSubring) • (Pi.single τ (b • v) : S → Fin r → C) := by
        funext s i
        by_cases e : s = τ
        · subst e; simp only [Pi.single_eq_same, smul_pi_apply, smul_vec_apply, Pi.smul_apply,
            smul_eq_mul, smul_C]
          ring
        · simp [e]
      rw [this]
      exact Fil.smul_mem _ h
    · have hne : (⟨c⁻¹, hc⟩ : w.valuationSubring) ≠ 0 := by
        intro e
        exact hc0 (inv_eq_zero.1 (congrArg Subtype.val e))
      refine ⟨b * ⟨c⁻¹, hc⟩, mul_ne_zero hb hne, ?_⟩
      have : (b * ⟨c⁻¹, hc⟩ : w.valuationSubring) • c • v = b • v := by
        funext i
        simp only [smul_vec_apply, Pi.smul_apply, smul_eq_mul, smul_C]
        push_cast
        field_simp
      rw [this]
      exact h

end GlobalTheory.Div.KerFil
end
