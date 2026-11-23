module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsLinearIndependentNormLeSuccMin
public import Mathlib.Analysis.Matrix.Order
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle005
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField

@[expose] public section

section

noncomputable section

open Module Submodule
open scoped InnerProductSpace

namespace GlobalTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_add_orthogonal_norm_sq_le (W : Submodule ℝ E) (u : E) :
    ∃ p ∈ W, ∃ q ∈ Wᗮ, u = p + q ∧ ‖q‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  obtain ⟨p, hp, q, hq, h⟩ := W.exists_add_mem_mem_orthogonal u
  refine ⟨p, hp, q, hq, h, ?_⟩
  rw [h, norm_add_sq_real, Submodule.inner_right_of_mem_orthogonal hp hq]
  nlinarith [sq_nonneg ‖p‖]

theorem exists_mem_span_int_norm_sub_sq_le_sum {ι : Type*} (v : ι → E) (s : Finset ι) {x : E}
    (hx : x ∈ span ℝ (v '' s)) :
    ∃ w ∈ span ℤ (v '' s), ‖x - w‖ ^ 2 ≤ (1 / 4) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty =>
    refine ⟨0, zero_mem _, ?_⟩
    have : x = 0 := by simpa using hx
    simp [this]
  | insert a s ha ih =>
    rw [Finset.coe_insert, Set.image_insert_eq] at hx ⊢
    obtain ⟨t, y, hy, rfl⟩ := mem_span_insert.1 hx
    obtain ⟨p, hp, q, hq, hv, hle⟩ := exists_add_orthogonal_norm_sq_le (span ℝ (v '' s)) (v a)
    have hy' : y + (t - round t) • p ∈ span ℝ (v '' s) := add_mem hy (smul_mem _ _ hp)
    obtain ⟨w, hw, hwle⟩ := ih hy'
    have hwR : w ∈ span ℝ (v '' s) := span_subset_span ℤ ℝ _ hw
    refine ⟨round t • v a + w, mem_span_insert.2 ⟨_, _, hw, rfl⟩, ?_⟩
    have he : t • v a + y - (round t • v a + w) =
        (y + (t - round t) • p - w) + (t - round t) • q := by
      rw [← Int.cast_smul_eq_zsmul ℝ, hv]; module
    rw [he, norm_add_sq_real,
      Submodule.inner_right_of_mem_orthogonal (sub_mem hy' hwR) (smul_mem _ _ hq),
      Finset.sum_insert ha, norm_smul, mul_pow, Real.norm_eq_abs]
    have h1 : |t - round t| ^ 2 ≤ 1 / 4 := by
      have := pow_le_pow_left₀ (abs_nonneg _) (abs_sub_round t) 2
      linarith
    nlinarith [mul_le_mul h1 hle (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 4)]

theorem exists_short_generator_inf_span_insert (L : Submodule ℤ E) [DiscreteTopology L]
    {ι : Type*} (v : ι → E) (s : Finset ι) (hv : ∀ i ∈ s, v i ∈ L) {u : E} (huL : u ∈ L)
    (hu : u ∉ span ℝ (v '' s)) :
    ∃ b : E, L ⊓ (span ℝ (insert u (v '' s))).restrictScalars ℤ =
        span ℤ {b} ⊔ L ⊓ (span ℝ (v '' s)).restrictScalars ℤ ∧
      ‖b‖ ^ 2 ≤ ‖u‖ ^ 2 + (1 / 4) * ∑ i ∈ s, ‖v i‖ ^ 2 := by
  set W := span ℝ (v '' s) with hW
  set C := ‖u‖ ^ 2 + (1 / 4) * ∑ i ∈ s, ‖v i‖ ^ 2 with hC
  obtain ⟨p, hp, q, hq, hupq, hle⟩ := exists_add_orthogonal_norm_sq_le W u
  have hZ : span ℤ (v '' s) ≤ L := span_le.2 (by rintro _ ⟨i, hi, rfl⟩; exact hv i hi)

  have red : ∀ (t : ℝ) (y : E), y ∈ W → t • u + y ∈ L → 0 < t → t ≤ 1 →
      ∃ y' ∈ W, t • u + y' ∈ L ∧ ‖t • u + y'‖ ^ 2 ≤ C := by
    intro t y hy hL h0 h1
    have hy' : y + t • p ∈ W := add_mem hy (smul_mem _ _ hp)
    obtain ⟨w, hw, hwle⟩ := exists_mem_span_int_norm_sub_sq_le_sum v s hy'
    have hwR : w ∈ W := span_subset_span ℤ ℝ _ hw
    refine ⟨y - w, sub_mem hy hwR, by rw [← add_sub_assoc]; exact sub_mem hL (hZ hw), ?_⟩
    have he : t • u + (y - w) = (y + t • p - w) + t • q := by rw [hupq]; module
    rw [he, norm_add_sq_real,
      Submodule.inner_right_of_mem_orthogonal (sub_mem hy' hwR) (smul_mem _ _ hq),
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h2 : t ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul h2 hle (sq_nonneg _) zero_le_one]

  have uniq : ∀ (t t' : ℝ) (y y' : E), y ∈ W → y' ∈ W → t • u + y = t' • u + y' → t = t' := by
    intro t t' y y' hy hy' h
    by_contra hne
    apply hu
    have : u = (t - t')⁻¹ • (y' - y) := by
      rw [eq_inv_smul_iff₀ (sub_ne_zero.2 hne), sub_smul, sub_eq_sub_iff_add_eq_add, h, add_comm]
    rw [this]; exact smul_mem _ _ (sub_mem hy' hy)
  let T : Set ℝ := {t | 0 < t ∧ t ≤ 1 ∧ ∃ y ∈ W, t • u + y ∈ L ∧ ‖t • u + y‖ ^ 2 ≤ C}
  have hT : T.Finite := by
    choose! f hfW hfL hfC using fun (t : ℝ) (ht : t ∈ T) => ht.2.2
    refine Set.Finite.of_injOn (f := fun t => t • u + f t) ?_ ?_ (finite_mem_and_norm_le L √C)
    · exact fun t ht => ⟨hfL t ht, Real.le_sqrt_of_sq_le (hfC t ht)⟩
    · exact fun t ht t' ht' h => uniq _ _ _ _ (hfW t ht) (hfW t' ht') h
  have hT1 : (1 : ℝ) ∈ T :=
    ⟨one_pos, le_rfl, red 1 0 (zero_mem _) (by simpa using huL) one_pos le_rfl⟩
  obtain ⟨t₀, ⟨h0, h1, y₀, hy₀, hbL, hbC⟩, hmin⟩ := Set.exists_min_image T id hT ⟨1, hT1⟩
  refine ⟨t₀ • u + y₀, le_antisymm ?_ (sup_le ?_ ?_), hbC⟩
  · rintro x ⟨hxL, hx⟩
    obtain ⟨t, y, hy, rfl⟩ := mem_span_insert.1 hx
    set k : ℤ := ⌊t / t₀⌋ with hk
    have hk1 : k * t₀ ≤ t := (le_div_iff₀ h0).1 (Int.floor_le _)
    have hk2 : t < (k + 1) * t₀ := (div_lt_iff₀ h0).1 (Int.lt_floor_add_one _)
    have he : t • u + y - k • (t₀ • u + y₀) = (t - k * t₀) • u + (y - (k : ℝ) • y₀) := by
      rw [← Int.cast_smul_eq_zsmul ℝ]; module
    have hyW : y - (k : ℝ) • y₀ ∈ W := sub_mem hy (smul_mem _ _ hy₀)
    have hL' : (t - k * t₀) • u + (y - (k : ℝ) • y₀) ∈ L := he ▸ sub_mem hxL (smul_mem _ _ hbL)
    have hz : t - k * t₀ = 0 := by
      by_contra hne
      have hpos : 0 < t - k * t₀ := lt_of_le_of_ne (by linarith) (Ne.symm hne)
      have hlt : t - k * t₀ < t₀ := by linarith
      exact absurd (hmin _ ⟨hpos, by linarith, red _ _ hyW hL' hpos (by linarith)⟩) (not_le.2 hlt)
    rw [hz, zero_smul, zero_add] at he hL'
    rw [eq_add_of_sub_eq' he]
    exact add_mem (mem_sup_left (smul_mem _ _ (mem_span_singleton_self _)))
      (mem_sup_right ⟨hL', hyW⟩)
  · rw [span_singleton_le_iff_mem]
    exact ⟨hbL, mem_span_insert.2 ⟨_, _, hy₀, rfl⟩⟩
  · exact inf_le_inf_left _ fun x hx => span_mono (Set.subset_insert _ _) hx

theorem exists_short_family_adapted (L : Submodule ℤ E) [DiscreteTopology L] {n : ℕ}
    {v : Fin n → E} (hv : LinearIndependent ℝ v) (hL : ∀ i, v i ∈ L) :
    ∃ b : Fin n → E, LinearIndependent ℝ b ∧
      (∀ s : ℕ, span ℤ (b '' {i : Fin n | (i : ℕ) < s}) =
        L ⊓ (span ℝ (v '' {i : Fin n | (i : ℕ) < s})).restrictScalars ℤ) ∧
      ∀ i, ‖b i‖ ^ 2 ≤ ‖v i‖ ^ 2 + (1 / 4) * ∑ j ∈ Finset.Iio i, ‖v j‖ ^ 2 := by
  choose b hb hbn using fun i : Fin n => exists_short_generator_inf_span_insert L v
    (Finset.Iio i) (fun j _ => hL j) (hL i) (hv.notMem_span_image (by simp))
  have key : ∀ s : ℕ, span ℤ (b '' {i : Fin n | (i : ℕ) < s}) =
      L ⊓ (span ℝ (v '' {i : Fin n | (i : ℕ) < s})).restrictScalars ℤ := by
    intro s
    induction s with
    | zero => simp
    | succ s ih =>
      by_cases hs : s < n
      · have h1 : {i : Fin n | (i : ℕ) < s + 1} = insert ⟨s, hs⟩ {i : Fin n | (i : ℕ) < s} := by
          ext i; simp [Fin.ext_iff]; omega
        have h2 : ((Finset.Iio (⟨s, hs⟩ : Fin n) : Finset (Fin n)) : Set (Fin n)) =
            {i : Fin n | (i : ℕ) < s} := by
          ext i; simp [Fin.lt_def]
        have h3 := hb ⟨s, hs⟩
        rw [h2] at h3
        rw [h1, Set.image_insert_eq, Set.image_insert_eq, h3, span_insert, ih]
      · have h1 : {i : Fin n | (i : ℕ) < s + 1} = {i : Fin n | (i : ℕ) < s} := by
          ext i; have := i.2; simp; omega
        rw [h1, ih]
  refine ⟨b, ?_, key, hbn⟩
  have hu : {i : Fin n | (i : ℕ) < n} = Set.univ := by ext i; simp
  have h := key n
  rw [hu, Set.image_univ, Set.image_univ] at h
  have hsp : span ℝ (Set.range b) = span ℝ (Set.range v) := by
    refine le_antisymm (span_le.2 fun x hx => ?_) (span_le.2 ?_)
    · exact (h.le (subset_span hx)).2
    · rintro _ ⟨i, rfl⟩
      exact span_subset_span ℤ ℝ _ (h.ge ⟨hL i, subset_span ⟨i, rfl⟩⟩)
  rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hsp, finrank_span_eq_card hv]

theorem exists_short_basis_adapted_of_subset_span (L : Submodule ℤ E) [DiscreteTopology L] {n : ℕ}
    {v : Fin n → E} (hv : LinearIndependent ℝ v) (hL : ∀ i, v i ∈ L)
    (hspan : (L : Set E) ⊆ span ℝ (Set.range v)) :
    ∃ b : Basis (Fin n) ℤ L,
      (∀ s : ℕ, span ℤ ((fun i => (b i : E)) '' {i : Fin n | (i : ℕ) < s}) =
        L ⊓ (span ℝ (v '' {i : Fin n | (i : ℕ) < s})).restrictScalars ℤ) ∧
      ∀ i, ‖(b i : E)‖ ^ 2 ≤ ‖v i‖ ^ 2 + (1 / 4) * ∑ j ∈ Finset.Iio i, ‖v j‖ ^ 2 := by
  obtain ⟨b, hb, hflag, hn⟩ := exists_short_family_adapted L hv hL
  have hu : {i : Fin n | (i : ℕ) < n} = Set.univ := by ext i; simp
  have h := hflag n
  rw [hu, Set.image_univ, Set.image_univ, inf_eq_left.2 (show L ≤ _ from hspan)] at h
  have hbZ : LinearIndependent ℤ b := hb.restrict_scalars' ℤ
  have hc : ∀ i, (((Basis.span hbZ).map (LinearEquiv.ofEq _ _ h) i : L) : E) = b i := by
    intro i; simp
  refine ⟨(Basis.span hbZ).map (LinearEquiv.ofEq _ _ h), ?_, ?_⟩
  · simpa only [hc] using hflag
  · simpa only [hc] using hn


omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem norm_sq_add_sum_Iio_le {n : ℕ} {v : Fin n → E} {i : Fin n} {r : ℝ}
    (h : ∀ j ≤ i, ‖v j‖ ≤ r) :
    ‖v i‖ ^ 2 + (1 / 4) * ∑ j ∈ Finset.Iio i, ‖v j‖ ^ 2 ≤ (((i : ℕ) + 1 + 3 : ℝ) / 4) * r ^ 2 := by
  have h1 : ∑ j ∈ Finset.Iio i, ‖v j‖ ^ 2 ≤ (Finset.Iio i).card • r ^ 2 :=
    Finset.sum_le_card_nsmul _ _ _ fun j hj =>
      pow_le_pow_left₀ (norm_nonneg _) (h j (Finset.mem_Iio.1 hj).le) 2
  rw [Fin.card_Iio, nsmul_eq_mul] at h1
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (h i le_rfl) 2
  linarith

end GlobalTheory
end
end

section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory

section RCLike

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n]

theorem trace_mul_nonneg_of_posSemidef {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  classical
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  have h := (hB.mul_mul_conjTranspose_same C).trace_nonneg
  rwa [trace_mul_cycle, ← star_eq_conjTranspose] at h

theorem re_trace_mul_nonneg_of_posSemidef {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ RCLike.re (A * B).trace :=
  (RCLike.nonneg_iff.mp (trace_mul_nonneg_of_posSemidef hA hB)).1

omit [Fintype n] in
theorem posSemidef_of_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (h : A ≤ B) : B.PosSemidef :=
  (hA.nonneg.trans h).posSemidef

omit [Fintype n] in
theorem posDef_of_le {A B : Matrix n n 𝕜} (hA : A.PosDef) (h : A ≤ B) : B.PosDef := by
  have := hA.add_posSemidef (le_iff.mp h)
  rwa [add_sub_cancel] at this

theorem conjTranspose_mul_mul_le_of_le {m : Type*} [Finite m] {A B : Matrix n n 𝕜} (h : A ≤ B)
    (C : Matrix n m 𝕜) : Cᴴ * A * C ≤ Cᴴ * B * C := by
  have := (le_iff.mp h).conjTranspose_mul_mul_same C
  rwa [Matrix.mul_sub, Matrix.sub_mul] at this

omit [Fintype n] in
theorem transpose_le_transpose_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) : Aᵀ ≤ Bᵀ := by
  have := (le_iff.mp h).transpose
  rwa [transpose_sub] at this

omit [Fintype n] in
theorem real_smul_le_real_smul_of_le {A B : Matrix n n 𝕜} (h : A ≤ B) {c : ℝ} (hc : 0 ≤ c) :
    c • A ≤ c • B := by
  have := (le_iff.mp h).smul hc
  rwa [smul_sub] at this

variable [DecidableEq n]

theorem inv_le_inv_of_posDef_of_le {A B : Matrix n n 𝕜} (hA : A.PosDef) (h : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  have hB := posDef_of_le hA h
  have hAi := hA.inv
  let _ := hB.isUnit.invertible
  let _ := hA.isUnit.invertible
  let _ := hAi.isUnit.invertible
  have h1 := PosDef.fromBlocks₁₁ (1 : Matrix n n 𝕜) B hAi
  have h2 := PosDef.fromBlocks₂₂ A⁻¹ (1 : Matrix n n 𝕜) hB
  simp only [conjTranspose_one, Matrix.mul_one, Matrix.one_mul, inv_inv_of_invertible] at h1 h2
  exact h2.mp (h1.mpr h)

theorem one_le_det_one_add_of_posSemidef {D : Matrix n n 𝕜} (hD : D.PosSemidef) :
    1 ≤ (1 + D).det := by
  first
  | exact @_root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add
  | exact _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add
  | (apply _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add <;> assumption)
  | (intros; apply _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add <;> assumption)
  | (intros; apply @_root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.OneLeDetOneAdd.one_le_det_one_add ..)

theorem det_le_det_of_posSemidef_of_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (h : A ≤ B) :
    A.det ≤ B.det := by
  by_cases h0 : A.det = 0
  · rw [h0]; exact (posSemidef_of_le hA h).det_nonneg
  have hA' := hA.posDef_iff_det_ne_zero.mpr h0
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp
    hA'.isStrictlyPositive
  let _ := hC.invertible
  have hD := (le_iff.mp h).conjTranspose_mul_mul_same C⁻¹
  have hB : B = star C * (1 + C⁻¹ᴴ * (B - star C * C) * C⁻¹) * C := by
    have e1 : star C * C⁻¹ᴴ = 1 := by
      rw [star_eq_conjTranspose, ← conjTranspose_mul, inv_mul_of_invertible, conjTranspose_one]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, e1,
      Matrix.one_mul, Matrix.mul_assoc, inv_mul_of_invertible, Matrix.mul_one, add_sub_cancel]
  have h1 := one_le_det_one_add_of_posSemidef hD
  rw [hB, det_mul_right_comm, det_mul (star C * C)]
  exact le_mul_of_one_le_right hA.det_nonneg h1

theorem re_det_le_re_det_of_posSemidef_of_le {A B : Matrix n n 𝕜} (hA : A.PosSemidef)
    (h : A ≤ B) : RCLike.re A.det ≤ RCLike.re B.det :=
  (RCLike.le_iff_re_im.mp (det_le_det_of_posSemidef_of_le hA h)).1

theorem re_det_pos_of_posDef {A : Matrix n n 𝕜} (hA : A.PosDef) : 0 < RCLike.re A.det :=
  (RCLike.pos_iff.mp hA.det_pos).1

theorem pow_mul_re_det_le_of_smul_le {B B' : Matrix n n 𝕜} (hB : B.PosSemidef) {c : ℝ}
    (hc : 0 ≤ c) (h : c • B ≤ B') :
    c ^ Fintype.card n * RCLike.re B.det ≤ RCLike.re B'.det := by
  have := re_det_le_re_det_of_posSemidef_of_le (hB.smul hc) h
  rwa [RCLike.real_smul_eq_coe_smul (K := 𝕜), det_smul, ← RCLike.ofReal_pow,
    RCLike.re_ofReal_mul] at this

theorem inv_real_smul_of_posDef {B : Matrix n n 𝕜} (hB : B.PosDef) {c : ℝ} (hc : c ≠ 0) :
    (c • B)⁻¹ = c⁻¹ • B⁻¹ := by
  let _ := hB.isUnit.invertible
  apply inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul,
    inv_mul_of_invertible]

theorem le_trace_smul_one_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A ≤ A.trace • (1 : Matrix n n 𝕜) := by
  have hU : (hA.1.eigenvectorUnitary : Matrix n n 𝕜) * star (hA.1.eigenvectorUnitary : Matrix n n 𝕜)
      = 1 := Unitary.coe_mul_star_self _
  have h1 : A.trace • (1 : Matrix n n 𝕜) - A = (hA.1.eigenvectorUnitary : Matrix n n 𝕜) *
      diagonal (fun i => A.trace - (hA.1.eigenvalues i : 𝕜)) *
        star (hA.1.eigenvectorUnitary : Matrix n n 𝕜) := by
    rw [← diagonal_sub, ← smul_one_eq_diagonal, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hU]
    congr 1
    conv_lhs => rw [hA.1.spectral_theorem]
    rfl
  rw [le_iff, h1]
  refine PosSemidef.mul_mul_conjTranspose_same (PosSemidef.diagonal fun i => ?_) _
  have : hA.1.eigenvalues i ≤ ∑ j, hA.1.eigenvalues j :=
    Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  simp only [Pi.zero_apply, sub_nonneg]
  rw [hA.1.trace_eq_sum_eigenvalues]
  exact_mod_cast this

omit [Fintype n] [DecidableEq n] in
theorem smul_eq_re_smul_of_nonneg {c : 𝕜} (hc : 0 ≤ c) (A : Matrix n n 𝕜) :
    c • A = RCLike.re c • A := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  congr 1
  exact (RCLike.conj_eq_iff_re.mp (RCLike.conj_eq_iff_im.mpr (RCLike.nonneg_iff.mp hc).2)).symm

theorem le_re_trace_smul_one_of_posSemidef {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    A ≤ RCLike.re A.trace • (1 : Matrix n n 𝕜) := by
  rw [← smul_eq_re_smul_of_nonneg hA.trace_nonneg]
  exact le_trace_smul_one_of_posSemidef hA


section Gram

variable {E : Type*} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

end Gram

theorem inv_smul_one_le_inv_of_le_smul_one {A : Matrix n n 𝕜} (hA : A.PosDef) {c : ℝ}
    (hc : 0 < c) (h : A ≤ c • (1 : Matrix n n 𝕜)) : c⁻¹ • (1 : Matrix n n 𝕜) ≤ A⁻¹ := by
  have := inv_le_inv_of_posDef_of_le hA h
  rwa [inv_real_smul_of_posDef PosDef.one hc.ne', inv_one] at this

end RCLike

section Rational

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

open NumberField IsCMField

variable [NumberField K] [IsCMField K]

end Rational

end GlobalTheory
end
