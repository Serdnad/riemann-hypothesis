module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.LinearAlgebra.Matrix.Adjugate

@[expose] public section

section

open Polynomial Matrix

namespace GlobalTheory.GoodTop

theorem sum_det_submatrix_image_eq {A : Type} [CommRing A] {r : Type} [Fintype r] [DecidableEq r]
    (M : Matrix r r A) (n : ℕ) (s : Finset r) (hs : s.card = n) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin n → r => Finset.univ.image p = s),
      (M.submatrix p p).det =
    (n.factorial : A) * (M.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det := by
  classical
  have hc : Fintype.card (Fin n) = Fintype.card s := by simp [hs]
  have h1 : ∑ e : Fin n ≃ s, (M.submatrix (Subtype.val ∘ e) (Subtype.val ∘ e)).det =
      (n.factorial : A) * (M.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det := by
    have : ∀ e : Fin n ≃ s, (M.submatrix (Subtype.val ∘ e) (Subtype.val ∘ e)).det =
        (M.submatrix (Subtype.val : s → r) (Subtype.val : s → r)).det := by
      intro e
      rw [← Matrix.submatrix_submatrix, Matrix.det_submatrix_equiv_self]
    simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Fintype.card_equiv (Fintype.equivOfCardEq hc), Fintype.card_fin]
  rw [← h1]
  symm
  refine Finset.sum_bij (fun e _ => Subtype.val ∘ e) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro e _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp]
    constructor
    · rintro ⟨a, rfl⟩
      exact (e a).2
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, by simp⟩
  · intro e _ e' _ h
    ext i
    exact congrFun h i
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    let f : Fin n → s := fun i => ⟨p i, hp ▸ Finset.mem_image_of_mem p (Finset.mem_univ i)⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      rw [← hp] at hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨a, rfl⟩
    have hb : Function.Bijective f :=
      (Fintype.bijective_iff_surjective_and_card f).mpr ⟨hf, hc⟩
    exact ⟨Equiv.ofBijective f hb, Finset.mem_univ _, rfl⟩

theorem factorial_mul_coeff_charpolyRev_neg {A : Type} [CommRing A] {r : Type} [Fintype r]
    [DecidableEq r] (M : Matrix r r A) (n : ℕ) :
    (n.factorial : A) * (Matrix.charpolyRev (-M)).coeff n =
      ∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign π : ℤ) : A) * ∏ i, M (p i) (p (π i)) := by
  classical
  have hrev : (-M).charpolyRev = det (1 + (X : A[X]) • M.map C) := by
    simp only [charpolyRev, sub_eq_add_neg]
    congr 2
    rw [Matrix.map_neg C (map_neg C) M, smul_neg, neg_neg]
  have hdet : ∀ p : Fin n → r, ∑ π : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign π : ℤ) : A) * ∏ i, M (p i) (p (π i)) = (M.submatrix p p).det := by
    intro p
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  rw [hrev, coeff_det_one_add_X_smul_eq_sum_minors, Finset.mul_sum]
  simp only [hdet]
  rw [← Finset.sum_filter_of_ne (s := Finset.univ)
    (p := fun p : Fin n → r => Finset.univ.image p ∈ (Finset.univ : Finset r).powersetCard n)]
  · rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset r).powersetCard n)
      (g := fun p : Fin n → r => Finset.univ.image p) (fun p hp => (Finset.mem_filter.mp hp).2)]
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [← sum_det_submatrix_image_eq M n s (Finset.mem_powersetCard.mp hs).2]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h ▸ hs, h⟩, fun h => h.2⟩
  · intro p _ hp
    have hinj : Function.Injective p := by
      intro i j hij
      by_contra hne
      exact hp (Matrix.det_zero_of_row_eq hne (by ext k; simp [hij]))
    rw [Finset.mem_powersetCard, Finset.card_image_of_injective _ hinj]
    simp

end GlobalTheory.GoodTop
end

section

namespace GlobalTheory.NonzeroDeterminantIntegrality

open Matrix

theorem exists_det_ne_zero {K I Λ : Type} [Field K] [Fintype Λ] [DecidableEq Λ] (v : I → Λ → K)
    (h : ∀ c : Λ → K, (∀ i, ∑ l, c l * v i l = 0) → c = 0) :
    ∃ f : Λ → I, (Matrix.of fun a l => v (f a) l).det ≠ 0 := by
  have hspan : Submodule.span K (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    have hexp : ∀ x : Λ → K, φ x = ∑ l, φ (Pi.single l 1) * x l := by
      intro x
      conv_lhs => rw [pi_eq_sum_univ' x]

      rw [map_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    have hc := h (fun l => φ (Pi.single l 1)) (fun i => by
      rw [← hexp]
      exact hle (Submodule.subset_span ⟨i, rfl⟩))
    apply hφ
    refine LinearMap.ext fun x => ?_
    rw [hexp]
    refine Finset.sum_eq_zero fun l _ => ?_
    have := congrFun hc l
    simp only [Pi.zero_apply] at this
    rw [this, zero_mul]
  obtain ⟨κ, a, -, hsp, hli⟩ := exists_linearIndependent' K v
  let b : Module.Basis κ K (Λ → K) := Module.Basis.mk hli (by rw [hsp, hspan])
  let e : Λ ≃ κ := (Pi.basisFun K Λ).indexEquiv b
  refine ⟨fun l => a (e l), ?_⟩
  have hli' : LinearIndependent K (Matrix.of fun x l => v (a (e x)) l).row :=
    hli.comp e e.injective
  have := Matrix.linearIndependent_rows_iff_isUnit.mp hli'
  exact ((Matrix.isUnit_iff_isUnit_det _).mp this).ne_zero

theorem integral_coefficients : ∀ (W : Type) [CommRing W] [IsDomain W] (K₀ K₁ : Type) [Field K₀] [Field K₁]
    (i₀ : W →+* K₀) (i₁ : W →+* K₁), Function.Injective i₀ → (∀ a : W, i₁ a ≠ 0 → IsUnit a) →
    ∀ (I Λ : Type) [Fintype Λ] (u : I → Λ → W),
    (∀ c : Λ → K₁, (∀ i : I, ∑ l : Λ, c l * i₁ (u i l) = 0) → c = 0) →
    ∀ (w : I → W) (z : Λ → K₀), (∀ i : I, i₀ (w i) = ∑ l : Λ, z l * i₀ (u i l)) →
    ∃ z₀ : Λ → W, (∀ l : Λ, i₀ (z₀ l) = z l) ∧ ∀ i : I, w i = ∑ l : Λ, z₀ l * u i l := by
  intro W _ _ K₀ K₁ _ _ i₀ i₁ hinj hunit I Λ _ u hu w z hz
  classical
  obtain ⟨f, hf⟩ := exists_det_ne_zero (fun i l => i₁ (u i l)) hu
  let M : Matrix Λ Λ W := Matrix.of fun a l => u (f a) l
  have hdet : IsUnit M.det := by
    apply hunit
    rw [RingHom.map_det]
    exact hf
  let z₀ : Λ → W := M⁻¹ *ᵥ (fun a => w (f a))
  have hM : M *ᵥ z₀ = fun a => w (f a) := by
    simp only [z₀]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hdet₀ : IsUnit (i₀.mapMatrix M).det := by
    rw [← RingHom.map_det]
    exact hdet.map i₀
  have key : (fun l => i₀ (z₀ l)) = z := by
    apply Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).mpr hdet₀)
    funext a
    have h1 := congrArg i₀ (congrFun hM a)
    rw [hz] at h1

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul] at h1 ⊢
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [h1]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
    rfl
  refine ⟨z₀, fun l => congrFun key l, fun i => hinj ?_⟩

  rw [hz, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, ← congrFun key l]

end GlobalTheory.NonzeroDeterminantIntegrality
end

section

open scoped Matrix

namespace GlobalTheory

theorem skewHermitian_perturb_idempotent_det_ne_zero :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (E D : Matrix (Fin n) (Fin n) k), E * E = E → (E.map σ)ᵀ = E → E * (D.map σ)ᵀ + D * E = 0 →
    (∀ a : Fin n → k, a ᵥ* E = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (E * V + D).det ≠ 0 := by
  intro k _ σ hσ ε hε hσε n E D hEE hEh hED hrank
  have h1 : E * (D.map σ)ᵀ = -(D * E) := eq_neg_of_add_eq_zero_left hED
  have h2 : E * (D.map σ)ᵀ = -(E * D * E) := by
    calc E * (D.map σ)ᵀ = E * (E * (D.map σ)ᵀ) := by rw [← Matrix.mul_assoc, hEE]
      _ = E * (-(D * E)) := by rw [h1]
      _ = -(E * D * E) := by rw [Matrix.mul_neg, Matrix.mul_assoc]
  have hDE : D * E = E * D * E := by
    have := h1.symm.trans h2
    exact neg_inj.mp this
  have h3 : E * (D.map σ)ᵀ * E = -(E * D * E) := by
    rw [h2, Matrix.neg_mul, Matrix.mul_assoc (E * D) E E, hEE]
  have hV : E * (ε • (1 : Matrix (Fin n) (Fin n) k) - D) * E = ε • E - E * D * E := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hEE]
  refine ⟨E * (ε • 1 - D) * E, ?_, ?_⟩
  · rw [hV]
    have hm : ((ε • E - E * D * E).map σ)ᵀ = (σ ε) • (E.map σ)ᵀ - (E.map σ)ᵀ * (D.map σ)ᵀ * (E.map σ)ᵀ := by
      ext i j
      have hs : ((ε • E).map σ)ᵀ = σ ε • (E.map σ)ᵀ := by
        ext i j
        simp
      rw [Matrix.map_sub _ (map_sub σ), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_sub, Matrix.transpose_mul,
        Matrix.transpose_mul, ← Matrix.mul_assoc, hs]
    rw [hm, hEh, h3, hσε, neg_smul, sub_neg_eq_add, neg_sub]
    abel
  · have hM : E * (E * (ε • 1 - D) * E) + D = ε • E - E * D * E + D := by
      rw [hV, Matrix.mul_sub, Matrix.mul_smul, hEE, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hEE]
    rw [hM]
    have hME : (ε • E - E * D * E + D) * E = ε • E := by
      rw [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, hEE, Matrix.mul_assoc (E * D) E E, hEE, hDE]
      abel
    intro hdet
    obtain ⟨a, ha0, ha⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
    have haE : a ᵥ* E = 0 := by
      have : a ᵥ* ((ε • E - E * D * E + D) * E) = 0 := by rw [← Matrix.vecMul_vecMul, ha, Matrix.zero_vecMul]
      rw [hME, Matrix.vecMul_smul] at this
      exact (smul_eq_zero.mp this).resolve_left hε
    have haD : a ᵥ* D = 0 := by
      have hx : a ᵥ* (E * D * E) = 0 := by
        rw [Matrix.mul_assoc, ← Matrix.vecMul_vecMul, haE, Matrix.zero_vecMul]
      rw [Matrix.vecMul_add, Matrix.vecMul_sub, Matrix.vecMul_smul, haE, hx] at ha
      simpa using ha
    exact ha0 (hrank a haE haD)

end GlobalTheory
end

section

open scoped Matrix

namespace GlobalTheory

theorem rank_normal_form_field : ∀ (k : Type) [Field k] (n : ℕ) (C : Matrix (Fin n) (Fin n) k),
    ∃ (U P : Matrix (Fin n) (Fin n) k) (e : Fin n → k), U.det ≠ 0 ∧ P.det ≠ 0 ∧ (∀ i, e i = 0 ∨ e i = 1) ∧
      U * C * P = Matrix.diagonal e := by
  intro k _ n C
  classical
  obtain ⟨L, L', d, hd⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal C
  refine ⟨Matrix.diagonal (fun i => if d i = 0 then 1 else (d i)⁻¹) * (L.map Matrix.TransvectionStruct.toMatrix).prod,
    (L'.map Matrix.TransvectionStruct.toMatrix).prod, fun i => if d i = 0 then 0 else 1, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.TransvectionStruct.det_toMatrix_prod, mul_one, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    by_cases h : d i = 0 <;> simp [h]
  · rw [Matrix.TransvectionStruct.det_toMatrix_prod]; exact one_ne_zero
  · intro i; by_cases h : d i = 0 <;> simp [h]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc _ C, hd, Matrix.diagonal_mul_diagonal]
    congr 1; funext i; by_cases h : d i = 0 <;> simp [h]

end GlobalTheory
end

section

open Matrix Polynomial

namespace GlobalTheory

theorem gramChange_gram_eq_mul {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {ι : Type} [Fintype ι]
    (u : ι → Fin n → K) :
    (Matrix.of fun i j => ∑ k, σ (u i k) * u j k) = (Matrix.of u).map σ * (Matrix.of u)ᵀ := by
  ext i j
  simp [Matrix.mul_apply]

theorem gramChange_square {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {ι : Type}
    [Fintype ι] [DecidableEq ι] (u v : ι → Fin n → K) (hu : LinearIndependent K u)
    (hv : LinearIndependent K v) (hvu : ∀ i, v i ∈ Submodule.span K (Set.range u)) :
    ∃ d : K, d ≠ 0 ∧ (Matrix.of fun i j => ∑ k, σ (v i k) * v j k).det
      = σ d * d * (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det := by
  classical
  let b := Module.Basis.span hu
  let P : Matrix ι ι K := Matrix.of fun i a => b.repr ⟨v i, hvu i⟩ a
  have hV : ∀ i, v i = ∑ a, P i a • u a := by
    intro i
    have h := congrArg Subtype.val (b.sum_repr ⟨v i, hvu i⟩)
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul, b, Module.Basis.span_apply] at h
    exact h.symm
  have hVm : Matrix.of v = P * Matrix.of u := by
    ext i k
    rw [Matrix.mul_apply, Matrix.of_apply,
      show v i k = (∑ a, P i a • u a) k from congrFun (hV i) k]
    simp [Finset.sum_apply]
  refine ⟨P.det, ?_, ?_⟩
  · intro hd
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
    have h1 : w ᵥ* Matrix.of v = 0 := by
      rw [hVm, ← Matrix.vecMul_vecMul, hw, Matrix.zero_vecMul]
    have h2 : ∑ i, w i • v i = 0 := by
      rw [← h1]
      ext k
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    exact hw0 (funext fun i => Fintype.linearIndependent_iff.mp hv w h2 i)
  · rw [gramChange_gram_eq_mul, gramChange_gram_eq_mul, hVm, Matrix.map_mul, transpose_mul,
      show P.map σ * (Matrix.of u).map σ * ((Matrix.of u)ᵀ * Pᵀ)
        = P.map σ * ((Matrix.of u).map σ * (Matrix.of u)ᵀ) * Pᵀ by
          simp only [Matrix.mul_assoc],
      det_mul, det_mul, det_transpose, RingHom.map_det,
      RingHom.mapMatrix_apply]
    ring

theorem gram_det_change_of_bases {K : Type} [Field K] (σ : K →+* K) {n : ℕ}
    (W : Submodule K (Fin n → K)) {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    [DecidableEq ι'] (u : ι → Fin n → K) (u' : ι' → Fin n → K) :
    LinearIndependent K u → Submodule.span K (Set.range u) = W → LinearIndependent K u' →
      Submodule.span K (Set.range u') = W → ∃ d : K, d ≠ 0 ∧
        (Matrix.of fun i j => ∑ k, σ (u' i k) * u' j k).det
          = σ d * d * (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det := by
  intro hu hsu hu' hsu'
  have hc : Fintype.card ι' = Fintype.card ι := by
    rw [← finrank_span_eq_card hu', ← finrank_span_eq_card hu, hsu', hsu]
  let e : ι' ≃ ι := Fintype.equivOfCardEq hc
  have hvu : ∀ i, (u' ∘ e.symm) i ∈ Submodule.span K (Set.range u) := by
    intro i
    rw [hsu, ← hsu']
    exact Submodule.subset_span ⟨e.symm i, rfl⟩
  obtain ⟨d, hd, hdet⟩ := gramChange_square σ u (u' ∘ e.symm) hu
    (hu'.comp e.symm e.symm.injective) hvu
  refine ⟨d, hd, ?_⟩
  rw [← hdet, ← det_submatrix_equiv_self e.symm]
  rfl

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory

theorem det_mul_det_toBlocks₂₂_of_mul_eq_one {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X Y : Matrix (m ⊕ n) (m ⊕ n) K) (h : X * Y = 1) :
    X.det * Y.toBlocks₂₂.det = X.toBlocks₁₁.det := by
  obtain ⟨A, B, C, D, rfl⟩ : ∃ A B C D, X = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks X).symm⟩
  obtain ⟨A', B', C', D', rfl⟩ : ∃ A B C D, Y = fromBlocks A B C D :=
    ⟨_, _, _, _, (fromBlocks_toBlocks Y).symm⟩
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at h
  obtain ⟨-, h12, -, h22⟩ := h
  have key : fromBlocks A B C D * fromBlocks (1 : Matrix m m K) B' 0 D' = fromBlocks A 0 C 1 := by
    rw [fromBlocks_multiply, h12, h22]
    simp
  have := congrArg Matrix.det key
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] at this
  simpa using this

end GlobalTheory
end

section

namespace GlobalTheory.DeterminantProductExpansion

theorem det_mul_expand {R : Type} [CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R) (B : Matrix (Fin N) (Fin i) R) :
    Matrix.det (A * B) = ∑ f : Fin i → Fin N, (∏ a : Fin i, A a (f a)) * Matrix.det (Matrix.submatrix B f id) := by
  let g : Fin i → Fin N → (Fin i → R) := fun a k => A a k • (fun j => B k j)
  have hrow : (A * B : Matrix (Fin i) (Fin i) R) = Matrix.of (fun a => ∑ k : Fin N, g a k) := by
    ext a j
    simp [g, Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : Matrix.det (A * B) =
      (Matrix.detRowAlternating : (Fin i → R) [⋀^Fin i]→ₗ[R] R).toMultilinearMap (fun a => ∑ k : Fin N, g a k) := by
    rw [hrow]; rfl

  rw [h1, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  simp only [g]
  rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  rfl

theorem main : ∀ {R : Type} [inst : CommRing R] {i N : ℕ} (A : Matrix (Fin i) (Fin N) R) (B : Matrix (Fin N) (Fin i) R), Matrix.det (A * B) = ∑ f : Fin i → Fin N, (∏ a : Fin i, A a (f a)) * Matrix.det (Matrix.submatrix B f id) :=
  fun A B => det_mul_expand A B

end GlobalTheory.DeterminantProductExpansion
end

section

open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

theorem mulVec_eq_zero_of_det_nonZeroDivisor {n R : Type} [Fintype n] [DecidableEq n]
    [CommRing R] (A : Matrix n n R) (hA : A.det ∈ nonZeroDivisors R) (v : n → R)
    (hv : A *ᵥ v = 0) : v = 0 := by
  have h : A.det • v = 0 := by
    have := congrArg (fun w => A.adjugate *ᵥ w) hv
    simpa [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec] using this
  funext i
  have hi := congrFun h i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
  exact (mul_left_mem_nonZeroDivisors_eq_zero_iff hA).1 hi

theorem twistedTrace_equivariant_and_injective_of_groupDet :
    ∀ (H K R : Type) [Group H] [Fintype H] [DecidableEq H] [Field K] [CommRing R] [Algebra K R] (st : H → R →ₐ[K] R), (∀ x, st 1 x = x) → (∀ h h' x, st (h * h') x = st h' (st h x)) → ∀ (χ : H →* Kˣ) (u : R), (Matrix.of fun h g : H => st (h * g) u).det ∈ nonZeroDivisors R → (∀ (F : R) (g : H), st g (∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h F) = ((χ g : Kˣ) : K) • ∑ h, (((χ h)⁻¹ : Kˣ) : K) • st h F) ∧ (∀ f : R, (∀ h, ∑ g, (((χ g)⁻¹ : Kˣ) : K) • st g (f * st h u) = 0) → f = 0) ∧ (∀ F : H → R, (∀ h g, st g (F h) = ((χ g : Kˣ) : K) • F h) → ∑ h, F h * st h u = 0 → F = 0) := by
  intro H K R _ _ _ _ _ _ st h1 hmul χ u hdet
  refine ⟨?_, ?_, ?_⟩
  · intro F g

    rw [map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.mulRight g) _ _ fun h => ?_
    rw [map_smul, ← hmul, Equiv.coe_mulRight, smul_smul, ← Units.val_mul]
    congr 2
    rw [map_mul, mul_inv_rev, mul_inv_cancel_left]
  · intro f hf
    have h := mulVec_eq_zero_of_det_nonZeroDivisor _ hdet
      (fun g => (((χ g)⁻¹ : Kˣ) : K) • st g f) (by
        funext h
        rw [Pi.zero_apply, ← hf h]
        simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [map_mul, ← hmul, mul_smul_comm, mul_comm])
    simpa [h1] using congrFun h 1
  · intro F hF h0
    refine mulVec_eq_zero_of_det_nonZeroDivisor (Matrix.of fun h g : H => st (h * g) u)ᵀ
      (by rwa [Matrix.det_transpose]) F ?_
    funext g
    have h2 := congrArg (st g) h0

    rw [map_sum, map_zero] at h2
    have h3 : ((χ g : Kˣ) : K) • ∑ h, st (h * g) u * F h = 0 := by
      rw [← h2, Finset.smul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [map_mul, hF, ← hmul, smul_mul_assoc, mul_comm]
    have h4 := congrArg (fun x => (((χ g)⁻¹ : Kˣ) : K) • x) h3
    simp only [smul_smul, Units.inv_mul, one_smul, smul_zero] at h4
    simpa [Matrix.mulVec, dotProduct] using h4

end GlobalTheory
end
