module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle156
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle065
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ScNorm
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.Integral
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall

@[expose] public section

section

open Polynomial Matrix

namespace UpperTheory.V.Sd.S2.symmetric_square_mixed_charpoly

variable {k : Type} [Field k]

private def blk (A B : Matrix (Fin 2) (Fin 2) k) : Matrix (Fin 4) (Fin 4) k :=
  !![A 0 0, A 0 1, 0, 0; A 1 0, A 1 1, 0, 0; 0, 0, B 0 0, B 0 1; 0, 0, B 1 0, B 1 1]

private def ant (A B : Matrix (Fin 2) (Fin 2) k) : Matrix (Fin 4) (Fin 4) k :=
  !![0, 0, A 0 0, A 0 1; 0, 0, A 1 0, A 1 1; B 0 0, B 0 1, 0, 0; B 1 0, B 1 1, 0, 0]

private def Pm (α β : k) : Matrix (Fin 4) (Fin 4) k :=
  !![0, α, 0, α; β, 0, -β, 0; 0, -1, 0, 1; 1, 0, 1, 0]

private def Qm (α β : k) : Matrix (Fin 4) (Fin 4) k :=
  (2 : k)⁻¹ • !![0, β⁻¹, 0, 1; α⁻¹, 0, -1, 0; 0, -β⁻¹, 0, 1; α⁻¹, 0, 1, 0]

private lemma PQ (h2 : (2 : k) ≠ 0) {α β : k} (ha : α ≠ 0) (hb : β ≠ 0) : Pm α β * Qm α β = 1 := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp [Pm, Qm, Matrix.mul_apply, Fin.sum_univ_four] <;>
    field_simp [h2, ha, hb] <;> ring

private lemma cp_conj (h2 : (2 : k) ≠ 0) {α β : k} (ha : α ≠ 0) (hb : β ≠ 0) (M N : Matrix (Fin 4) (Fin 4) k)
    (h : Pm α β * M = N * Pm α β) : M.charpoly = N.charpoly := by
  have h1 := PQ h2 ha hb
  have h3 : Qm α β * Pm α β = 1 := mul_eq_one_comm.mp h1
  have : M = Qm α β * (N * Pm α β) := by rw [← h, ← Matrix.mul_assoc, h3, Matrix.one_mul]
  rw [this, Matrix.charpoly_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one]

private lemma P_mix (h2 : (2 : k) ≠ 0) (α β : kˣ) (A B : Matrix (Fin 2) (Fin 2) k) :
    Pm (α : k) β * mix (β / α) A B = blk A B * Pm (α : k) β := by
  have ha := α.ne_zero
  have hb := β.ne_zero
  ext i j : 1
  fin_cases i <;> fin_cases j <;>
    simp [Pm, mix, blk, Matrix.mul_apply, Fin.sum_univ_four, Units.val_div_eq_div_val] <;>
    field_simp [h2, ha, hb] <;> ring

private lemma blk_P (α β : k) (A B : Matrix (Fin 2) (Fin 2) k) :
    blk A B * Pm α β * Matrix.diagonal ![β, -α, -β, α] =
      ant (A * Matrix.diagonal ![α ^ 2, β ^ 2]) B * Pm α β := by
  ext i j : 1
  rw [Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [Pm, ant, blk, Matrix.mul_apply, Fin.sum_univ_four] <;> ring

private lemma cp_blk (A B : Matrix (Fin 2) (Fin 2) k) : (blk A B).charpoly = A.charpoly * B.charpoly := by
  simp only [Matrix.charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_zero, Matrix.submatrix_apply, Matrix.charmatrix_apply]
  norm_num [blk, Fin.succAbove, Fin.lt_def, Fin.ext_iff, Matrix.diagonal_apply]
  ring

private lemma cp_ant (A B : Matrix (Fin 2) (Fin 2) k) : (ant A B).charpoly = (A * B).charpoly.comp (X ^ 2) := by
  simp only [Matrix.charpoly, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_zero,
    Matrix.det_fin_zero, Matrix.submatrix_apply, Matrix.charmatrix_apply]
  norm_num [ant, Fin.succAbove, Fin.lt_def, Fin.ext_iff, Matrix.diagonal_apply, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

end UpperTheory.V.Sd.S2.symmetric_square_mixed_charpoly

open UpperTheory.V.Sd.S2 UpperTheory.V.Sd.S2.symmetric_square_mixed_charpoly in
theorem UpperTheory.symmetric_square_mixed_charpoly :
    UpperTheory.V.Sd.S2.MixCp := by
  intro k Γ₀ Γ _ _ _ j t α β ρ R H s hs
  have hN : j.range.Normal := Subgroup.normal_of_index_eq_two H.index
  have hc : ∀ h : Γ₀, ∃ h', j h' = t⁻¹ * j h * t := fun h => by
    have := hN.conj_mem' (j h) ⟨h, rfl⟩ t
    exact this
  have hm : ∀ a b : Γ, a ∉ j.range → b ∉ j.range → a * b ∈ j.range := fun a b ha hb =>
    (Subgroup.mul_mem_iff_of_index_two H.index).mpr (by simp [ha, hb])
  have ht' : t⁻¹ ∉ j.range := fun h => H.nmem (inv_mem_iff.mp h)
  refine ⟨fun g g' hg => ?_, fun g hg => ?_⟩
  · obtain ⟨h, hh⟩ := hm _ _ ht' hs
    obtain ⟨g'', hg''⟩ := hc g
    have e : g' = h⁻¹ * g'' * h := H.inj (by
      rw [map_mul, map_mul, map_inv, hh, hg'', hg]; group)
    rw [H.on g g'' hg'', cp_conj H.two α.ne_zero β.ne_zero _ _ (P_mix H.two α β _ _), cp_blk, e]
    congr 1
    rw [map_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  · obtain ⟨h, hh⟩ := hm _ _ hs ht'
    obtain ⟨h', hh'⟩ := hc h
    obtain ⟨u, hu⟩ := hm _ _ H.nmem H.nmem
    have e : g = h * u * h' := H.inj (by
      rw [map_mul, map_mul, hh', hu, hh, hg]; group)
    have es : s = j h * t := by rw [hh]; group
    have key : Pm (α : k) β * (R s : Matrix (Fin 4) (Fin 4) k) =
        ant ((ρ h : Matrix (Fin 2) (Fin 2) k) * Matrix.diagonal ![(α : k) ^ 2, (β : k) ^ 2]) (ρ h') * Pm (α : k) β := by
      rw [es, map_mul, Units.val_mul, H.on h h' hh', H.off, ← Matrix.mul_assoc, P_mix H.two, blk_P]
    rw [cp_conj H.two α.ne_zero β.ne_zero _ _ key, cp_ant, e, map_mul, map_mul, Units.val_mul, Units.val_mul, H.sq u hu]
end

section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Sd

namespace UpperTheory

section

variable {k : Type} [NormedField k] [IsUltrametricDist k] {K : Type} [Field K]

private theorem norm_ringHom_integer_le_one (σ : K →+* k) (x : 𝓞 K) : ‖σ (x : K)‖ ≤ 1 := by
  have hy : IsIntegral ℤ (σ (x : K)) := map_isIntegral_int σ (RingOfIntegers.isIntegral_coe x)
  have h : IsIntegral (NormedField.valuation (K := k)).integer (σ (x : K)) := hy.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := k))).mem_of_integral h
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h2
  exact_mod_cast h2

private def embeddingPrimeIdeal (σ : K →+* k) : Ideal (𝓞 K) where
  carrier := {x | ‖σ (x : K)‖ < 1}
  add_mem' := by
    intro x y hx hy
    change ‖σ (algebraMap (𝓞 K) K (x + y))‖ < 1
    rw [map_add (f := _), map_add (f := _)]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt hx hy)
  zero_mem' := by
    change ‖σ (algebraMap (𝓞 K) K 0)‖ < 1
    simp
  smul_mem' := by
    intro c x hx
    change ‖σ (algebraMap (𝓞 K) K (c * x))‖ < 1
    rw [map_mul, map_mul, norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (norm_ringHom_integer_le_one σ c)) hx

private theorem norm_embedding_eq_one_of_not_mem (σ : K →+* k) (x : 𝓞 K) (hx : x ∉ embeddingPrimeIdeal σ) :
    ‖σ (algebraMap (𝓞 K) K x)‖ = 1 :=
  le_antisymm (norm_ringHom_integer_le_one σ x) (not_lt.1 hx)

private theorem embedding_ideal_prime (σ : K →+* k) : (embeddingPrimeIdeal σ).IsPrime := by
  refine ⟨?_, ?_⟩
  · intro h
    have h1 : ‖σ (algebraMap (𝓞 K) K 1)‖ < 1 := (Ideal.eq_top_iff_one _).1 h
    simp at h1
  · intro x y hxy
    by_contra hc
    push Not at hc
    change ‖σ (algebraMap (𝓞 K) K (x * y))‖ < 1 at hxy
    rw [map_mul, map_mul, norm_mul, norm_embedding_eq_one_of_not_mem σ x hc.1, norm_embedding_eq_one_of_not_mem σ y hc.2, one_mul] at hxy
    exact lt_irrefl _ hxy

private theorem exists_embedding_prime_above [NumberField K] [CharZero k] [IsAlgClosed k] {l : ℕ} (hp : l.Prime) (hk : ‖(l : k)‖ < 1)
    (w : HeightOneSpectrum (𝓞 K)) (hl : (l : 𝓞 K) ∈ w.asIdeal) :
    ∃ σ : K →+* k, embeddingPrimeIdeal σ = w.asIdeal := by
  classical
  by_contra hne
  push Not at hne
  have σ0 : K →ₐ[ℚ] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hnot : ¬ ((w.asIdeal : Set (𝓞 K)) ⊆ ⋃ σ ∈ ((Finset.univ : Finset (K →ₐ[ℚ] k)) : Set (K →ₐ[ℚ] k)),
      (embeddingPrimeIdeal (σ : K →+* k) : Set (𝓞 K))) := by
    rw [Ideal.subset_union_prime σ0 σ0 (fun σ _ _ _ => embedding_ideal_prime _)]
    rintro ⟨σ, -, hle⟩
    exact hne σ (((w.isPrime.isMaximal w.ne_bot).eq_of_le (embedding_ideal_prime _).ne_top hle).symm)
  obtain ⟨a, haw, ha⟩ := Set.not_subset.1 hnot
  have h1 : ∀ σ : K →ₐ[ℚ] k, ‖σ (a : K)‖ = 1 := by
    intro σ
    refine norm_embedding_eq_one_of_not_mem (σ : K →+* k) a fun h => ha ?_
    simp only [Set.mem_iUnion]
    exact ⟨σ, by simp, h⟩
  have hprod : ‖algebraMap ℚ k (Algebra.norm ℚ (a : K))‖ = 1 := by
    rw [Algebra.norm_eq_prod_embeddings, norm_prod]
    exact Finset.prod_eq_one (fun σ _ => h1 σ)
  have hmem : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : 𝓞 K) ∈ w.asIdeal :=
    (Ideal.span_le.2 (Set.singleton_subset_iff.2 haw)) (Ideal.absNorm_mem _)
  have hdvd : l ∣ Ideal.absNorm (Ideal.span {a}) := by
    by_contra hnd
    have hc : IsCoprime (l : 𝓞 K) ((Ideal.absNorm (Ideal.span {a}) : ℕ) : 𝓞 K) :=
      Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
    obtain ⟨u, v, huv⟩ := hc
    refine w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← huv]
    exact add_mem (Ideal.mul_mem_left _ _ hl) (Ideal.mul_mem_left _ _ hmem)
  have hn : ‖((Ideal.absNorm (Ideal.span {a}) : ℕ) : k)‖ = 1 := by
    rw [Ideal.absNorm_span_singleton, ← hprod, ← Algebra.coe_norm_int, eq_ratCast, Rat.cast_intCast,
      Nat.cast_natAbs]
    rcases abs_choice (Algebra.norm ℤ a) with h | h
    · rw [h]
    · rw [h, Int.cast_neg, norm_neg]
  obtain ⟨m, hm⟩ := hdvd
  rw [hm, Nat.cast_mul, norm_mul] at hn
  have hk1 : ‖(m : k)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one _ m
  have h2 : ‖(l : k)‖ * ‖(m : k)‖ ≤ ‖(l : k)‖ * 1 := mul_le_mul_of_nonneg_left hk1 (norm_nonneg _)
  linarith

end

theorem exists_ringHom_to_localField_inducing_place : UpperTheory.V.Sd.S2.EmbEx := by
  intro F _ _ _ l hl ι
  refine ⟨fun w hw => ?_, fun w w' τ τ' h h' e => ?_⟩
  · have hk : ‖(l : Qbar l)‖ < 1 := by
      have : (l : Qbar l) = algebraMap ℚ_[l] (Qbar l) (l : ℚ_[l]) := (map_natCast _ l).symm
      rw [this, norm_algebraMap']
      exact Padic.norm_p_lt_one
    obtain ⟨σ, hσ⟩ := exists_embedding_prime_above hl.out hk w hw
    exact ⟨σ, fun x => by rw [← hσ]; rfl⟩
  · have e2 : ι.toRingHom.comp τ = ι.toRingHom.comp τ' := by
      rcases InfinitePlace.mk_eq_iff.1 e with e | e
      · exact e
      · rw [← e]
        exact (ComplexEmbedding.isReal_iff.1 (IsTotallyReal.complexEmbedding_isReal _)).symm
    have e3 : τ = τ' := RingHom.ext fun x => ι.injective (RingHom.congr_fun e2 x)
    subst e3
    exact HeightOneSpectrum.ext (Ideal.ext fun x => (h x).trans (h' x).symm)

end UpperTheory
end
end

section

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2
open scoped Matrix

private theorem col_eq {k : Type} [Field k] (g r : GL (Fin 2) k) (a b : kˣ) (h10 : (g * r * g⁻¹ : GL (Fin 2) k) 1 0 = 0)
    (h00 : (g * r * g⁻¹ : GL (Fin 2) k) 0 0 = a) (h11 : (g * r * g⁻¹ : GL (Fin 2) k) 1 1 = b) :
    r 0 0 * g⁻¹ 0 0 + r 0 1 * g⁻¹ 1 0 = a * g⁻¹ 0 0 ∧ r 1 0 * g⁻¹ 0 0 + r 1 1 * g⁻¹ 1 0 = a * g⁻¹ 1 0 ∧
      Matrix.GeneralLinearGroup.det r = a * b := by
  have e : ((r : Matrix (Fin 2) (Fin 2) k) * (g⁻¹ : GL (Fin 2) k)) =
      ((g⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (g * r * g⁻¹ : GL (Fin 2) k) := by
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    group
  have e0 := congrFun (congrFun e 0) 0
  have e1 := congrFun (congrFun e 1) 0
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two] at e0 e1
  have t : Matrix.GeneralLinearGroup.det (g * r * g⁻¹) = Matrix.GeneralLinearGroup.det r := by
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  rw [h10, h00] at e0 e1
  refine ⟨?_, ?_, ?_⟩
  · rw [e0]; ring
  · rw [e1]; ring
  · rw [← t]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h10, h00, h11, mul_zero, sub_zero]
    rfl

private theorem one_le_norm {K : Type} [NormedField K] [IsUltrametricDist K] {x y a b : K} (h : ¬ ‖x - y‖ < 1)
    (ha : ‖a - x‖ < 1) (hb : ‖b - y‖ < 1) : 1 ≤ ‖a - b‖ ∧ 1 ≤ ‖b - a‖ := by
  have : 1 ≤ ‖a - b‖ := by
    by_contra hlt
    apply h
    rw [norm_sub_rev] at ha
    have e : x - y = (x - a) + ((a - b) + (b - y)) := by ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha ?_)
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (not_le.mp hlt) hb)
  exact ⟨this, by rwa [norm_sub_rev]⟩

private theorem norm_le_of {K : Type} [NormedField K] {c d p q : K} (hc : 1 ≤ ‖c‖) (e : c * q = d * p) :
    ‖q‖ ≤ ‖d‖ * ‖p‖ :=
  calc ‖q‖ ≤ ‖c‖ * ‖q‖ := le_mul_of_one_le_left (norm_nonneg _) hc
    _ = ‖d‖ * ‖p‖ := by rw [← norm_mul, e, norm_mul]

theorem UpperTheory.mix_stable_line_local :
    UpperTheory.V.Sd.S2.LocLine := by
  intro l _ S A x κ ⟨s₀, hne⟩ hA ⟨g, hg⟩
  have key := fun s => col_eq g (A s) _ _ (hg s).1 ((hg s).2 0) ((hg s).2 1)
  have hdet : (g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 * (g⁻¹ : GL (Fin 2) (Qbar l)) 1 1 -
      (g⁻¹ : GL (Fin 2) (Qbar l)) 0 1 * (g⁻¹ : GL (Fin 2) (Qbar l)) 1 0 ≠ 0 := by
    have := (g⁻¹).det_ne_zero
    rwa [Matrix.det_fin_two] at this
  generalize (g⁻¹ : GL (Fin 2) (Qbar l)) 0 0 = p at key hdet
  generalize (g⁻¹ : GL (Fin 2) (Qbar l)) 1 0 = q at key hdet
  have hne' : ¬ ‖(x s₀ : Qbar l) - 1‖ < 1 := hne
  obtain ⟨a00, a11, a10, a01⟩ := hA s₀
  refine ⟨fun s => (key s).2.2, fun hκ => ?_, fun hκ => ?_⟩
  · have h1 : ‖(κ 0 s₀ : Qbar l) - (x s₀ : Qbar l)‖ < 1 := hκ s₀
    have hge := (one_le_norm hne' h1 a00).1
    have hpq : ‖p‖ ≤ ‖A s₀ 0 1‖ * ‖q‖ := norm_le_of hge (by linear_combination -(key s₀).1)
    have hq : q ≠ 0 := by
      rintro rfl
      rw [norm_zero, mul_zero, norm_le_zero_iff] at hpq
      simp [hpq] at hdet
    refine ⟨p / q, ?_, fun s => ?_⟩
    · rw [norm_div, div_le_one (norm_pos_iff.mpr hq)]
      exact hpq.trans (mul_le_of_le_one_left (norm_nonneg _) a01)
    · obtain ⟨k1, k2, -⟩ := key s
      ext i
      fin_cases i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
        linear_combination k1
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
        linear_combination k2
  · have h1 : ‖(κ 0 s₀ : Qbar l) - 1‖ < 1 := hκ s₀
    have hge := (one_le_norm hne' a11 h1).2
    have hpq : ‖q‖ ≤ ‖A s₀ 1 0‖ * ‖p‖ := norm_le_of hge (by linear_combination -(key s₀).2.1)
    have hp : p ≠ 0 := by
      rintro rfl
      rw [norm_zero, mul_zero, norm_le_zero_iff] at hpq
      simp [hpq] at hdet
    refine ⟨q / p, ?_, fun s => ?_⟩
    · rw [norm_div, div_lt_one (norm_pos_iff.mpr hp)]
      exact hpq.trans_lt (mul_lt_of_lt_one_left (norm_pos_iff.mpr hp) a10)
    · obtain ⟨k1, k2, -⟩ := key s
      ext i
      fin_cases i
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
        linear_combination k1
      · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        field_simp
        linear_combination k2
end

section

section
variable {K : Type} [NormedField K] [IsUltrametricDist K]

private theorem add_lt {a b : K} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max a b) (max_lt ha hb)

private theorem sub_eq (h2 : ‖(2 : K)‖ = 1) {a b : K} (ha : ‖a - 1‖ < 1) (hb : ‖b - 1‖ < 1) :
    ‖a - b‖ = ‖a ^ 2 - b ^ 2‖ := by
  have h := add_lt ha hb
  have h1 : ‖a + b‖ = 1 := by
    have e : a + b = 2 + ((a - 1) + (b - 1)) := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h2]; exact h.ne'), h2]
    exact max_eq_left h.le
  have e : a ^ 2 - b ^ 2 = (a + b) * (a - b) := by ring
  rw [e, norm_mul, h1, one_mul]

private theorem mul_lt {a b : K} (ha : ‖a - 1‖ < 1) (hb : ‖b - 1‖ < 1) : ‖a * b - 1‖ < 1 := by
  have e : a * b - 1 = (a - 1) * (b - 1) + ((a - 1) + (b - 1)) := by ring
  rw [e]
  refine add_lt ?_ (add_lt ha hb)
  rw [norm_mul]
  nlinarith [norm_nonneg (a - 1), norm_nonneg (b - 1)]

omit [IsUltrametricDist K] in
private theorem ex_root [IsAlgClosed K] (y : Kˣ) (hy : ‖(y : K) - 1‖ < 1) :
    ∃ x : Kˣ, x ^ 2 = y ∧ ‖(x : K) - 1‖ < 1 := by
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (y : K) (n := 2) (by norm_num)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact y.ne_zero (by rw [← hx]; ring)
  by_cases h : ‖x - 1‖ < 1
  · exact ⟨Units.mk0 x hx0, Units.ext (by simpa using hx), h⟩
  · refine ⟨Units.mk0 (-x) (neg_ne_zero.mpr hx0), Units.ext (by simpa using hx), ?_⟩
    have e : (y : K) - 1 = -((x - 1) * (-x - 1)) := by rw [← hx]; ring
    rw [e, norm_neg, norm_mul] at hy
    simp only [Units.val_mk0]
    by_contra h'
    push Not at h h'
    nlinarith

end

theorem UpperTheory.exists_square_root_of_character_near_one :
    UpperTheory.V.Sd.S2.SqrtChar := by
  intro l _ hl Γ _ _ η hη hc
  have h2 : ‖(2 : PadicAlgCl l)‖ = 1 := by
    have e : (2 : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) ((2 : ℕ) : ℚ_[l]) := by
      rw [map_natCast]; norm_num
    rw [e]
    erw [PadicAlgCl.norm_extends]
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes Fact.out Nat.prime_two).mpr hl
  have hc' : ∀ g, ‖((η g : (PadicAlgCl l)ˣ) : PadicAlgCl l) - 1‖ < 1 := fun g => by
    simpa [UpperTheory.V.Sd.Cong] using hc g
  choose d hd hd1 using fun g => ex_root (η g) (hc' g)
  have hv : ∀ g, ((d g : (PadicAlgCl l)ˣ) : PadicAlgCl l) ^ 2 = η g := fun g => by
    rw [← hd g]; simp
  have hmul : ∀ g h, d (g * h) = d g * d h := fun g h => by
    apply Units.ext
    have := sub_eq h2 (hd1 (g * h)) (mul_lt (hd1 g) (hd1 h))
    rw [mul_pow, hv, hv, hv, map_mul, Units.val_mul, sub_self, norm_zero, norm_eq_zero, sub_eq_zero] at this
    simpa using this
  refine ⟨MonoidHom.mk' d hmul, ?_, hd, fun g => ?_⟩
  · rw [Units.isEmbedding_val₀.continuous_iff]
    have hη' : Continuous fun g => ((η g : (PadicAlgCl l)ˣ) : PadicAlgCl l) := Units.continuous_val.comp hη
    rw [continuous_iff_continuousAt]
    intro g
    have h1 := (hη'.continuousAt (x := g))
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero] at h1 ⊢
    refine h1.congr fun x => ?_
    simp only [Function.comp, MonoidHom.mk'_apply]
    rw [sub_eq h2 (hd1 x) (hd1 g), hv, hv]
  · simpa [UpperTheory.V.Sd.Cong] using hd1 g
end

section

open Formalism.ConjugateSelfDual IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.automorphic_forms_descent_to_smaller_level :
    UpperTheory.V.Sd.S2.Descend := by
  intro l _ c
  refine ⟨UpperTheory.V.Fr.sc_norm l c, ?_⟩
  intro ι Γ _ _ _ _ _ _ P hc hr hn
  obtain ⟨E, hE, hEr⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l Γ 4 P.r.toHomUnits
    fun i j => hc.matrix_elem i j
  let s : Set (PadicAlgCl l) := Set.range fun p : ι × Fin 4 × Fin 4 => P.n p.1 p.2.1 p.2.2
  haveI : Finite s := (Set.finite_range _).to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] s) :=
    IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral
  obtain ⟨c₁, hcc, h₁⟩ := (UpperTheory.integrality_of_norm_coefficients l).1 c (IntermediateField.adjoin ℚ_[l] s ⊔ E) inferInstance
  have hr₁ : ∀ g i j, P.r g i j ∈ c₁.O := fun g i j =>
    h₁ _ ((le_sup_right : E ≤ _) (hEr g i j)) (hr g i j)
  have hn₁ : ∀ v i j, P.n v i j ∈ c₁.O := fun v i j =>
    h₁ _ ((le_sup_left : IntermediateField.adjoin ℚ_[l] s ≤ _)
      (IntermediateField.subset_adjoin _ _ ⟨(v, i, j), rfl⟩)) (hn v i j)
  let ρ : Γ →* M4 c₁.O :=
    { toFun := fun g => Matrix.of fun i j => ⟨P.r g i j, hr₁ g i j⟩
      map_one' := by
        ext i j
        simp only [map_one, Matrix.of_apply, Matrix.one_apply]
        split_ifs <;> rfl
      map_mul' := fun g h => by
        ext i j
        simp only [map_mul, Matrix.of_apply, Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul] }
  refine ⟨c₁, hcc, ⟨ρ, fun v => Matrix.of fun i j => ⟨P.n v i j, hn₁ v i j⟩⟩, ?_, fun i j => ?_⟩
  · exact PD.ext (MonoidHom.ext fun g => Matrix.ext fun i j => rfl) (funext fun v => Matrix.ext fun i j => rfl)
  · exact ((UpperTheory.integrality_of_norm_coefficients l).2 c₁ Γ _).2 (hc.matrix_elem i j)
end
