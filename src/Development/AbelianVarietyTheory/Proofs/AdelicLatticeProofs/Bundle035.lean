module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseOneAddPreservingAdelicCompletion
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index
public import Mathlib.FieldTheory.Galois.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle029
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.TensorProduct.Maps
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle030
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle020
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
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.adelic_unitary_scaling_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), Module.finrank F E = 2 → (∀ x, c (c x) = x) → c ≠ 1 → ∀ (n : ℕ) (g : Matrix (Fin n) (Fin n) (RA F E)) (e : FiniteAdeleRing (𝓞 F) F), e * e = e → {v | e v ≠ 0}.Finite → ∃ lam : E, lam * c lam = 1 ∧ IsUnit (1 + ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] lam) • ((e ⊗ₜ[F] (1 : E)) • g + ((1 - e) ⊗ₜ[F] (1 : E)) • (1 : Matrix (Fin n) (Fin n) (RA F E)))).det := by
  first | exact @GlobalTheory.UnRep.exists_norm_one_isUnit_det | exact GlobalTheory.UnRep.exists_norm_one_isUnit_det | (intros; apply GlobalTheory.UnRep.exists_norm_one_isUnit_det <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_inverse_one_add_preserving_adelicCompletion : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (N : ℕ) (e : FiniteAdeleRing (𝓞 F) F), (∀ v, e v ∈ v.adicCompletionIntegers F) → (∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∉ v.asIdeal → e v = 0) → ∀ X : Matrix (Fin n) (Fin n) (RA F E), (∀ z ∈ hat F (L : Set (Fin n → E)), X *ᵥ z ∈ hat F (L : Set (Fin n → E))) → ∃ W : Matrix (Fin n) (Fin n) (RA F E), (1 + (e ⊗ₜ[F] (1 : E) : RA F E) • (N • X)) * W = 1 ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), W *ᵥ z ∈ hat F (L : Set (Fin n → E)) := by
  first | exact @GlobalTheory.UnRep.exists_inverse_one_add_preserving_hat | exact GlobalTheory.UnRep.exists_inverse_one_add_preserving_hat | (intros; apply GlobalTheory.UnRep.exists_inverse_one_add_preserving_hat <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.HermiteReduction

theorem exists_lt_two_mul {S : Type} [Nonempty S] (f : S → ℝ) (c : ℝ) (hc : 0 < c) (hf : ∀ s, c ≤ f s) :
    ∃ s, ∀ t, f s < 2 * f t := by
  have hbdd : BddBelow (Set.range f) := ⟨c, by rintro _ ⟨s, rfl⟩; exact hf s⟩
  have hm : c ≤ ⨅ s, f s := le_ciInf hf
  have hlt : ⨅ s, f s < 2 * ⨅ s, f s := by linarith
  obtain ⟨s, hs⟩ := exists_lt_of_ciInf_lt hlt
  exact ⟨s, fun t => hs.trans_le (by linarith [ciInf_le hbdd t])⟩

noncomputable def gramMinor {N : ℕ} (x : Matrix (Fin N) (Fin N) ℝ) (j : Fin (N + 1)) : ℝ :=
  ((xᵀ * x).submatrix (Fin.castLE (Nat.lt_succ_iff.mp j.2)) (Fin.castLE (Nat.lt_succ_iff.mp j.2))).det

theorem prod_castLE_succ {N : ℕ} (f : Fin N → ℝ) (p q : Fin N) (hq : (q : ℕ) = p + 1) (h : (q : ℕ) ≤ N) :
    ∏ i : Fin q, f (Fin.castLE h i) = (∏ l ∈ Finset.univ.filter (· < p), f l) * f p := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq'⟩ := q
  simp only at hq h ⊢
  subst hq
  rw [Fin.prod_univ_castSucc]
  congr 1
  refine Finset.prod_bij (fun i _ => Fin.castLE h i.castSucc) ?_ ?_ ?_ ?_
  · intro i _
    simp [Fin.lt_def]
  · intro i _ j _ hij
    exact Fin.ext (by simpa using congrArg Fin.val hij)
  · intro l hl
    have hl' : (l : ℕ) < p := by simpa [Fin.lt_def] using hl
    exact ⟨⟨l, hl'⟩, Finset.mem_univ _, Fin.ext rfl⟩
  · intro i _
    rfl

theorem mul_upper {N : ℕ} (n m : Matrix (Fin N) (Fin N) ℝ) (hn1 : ∀ i, n i i = 1) (hn0 : ∀ i j, j < i → n i j = 0)
    (hm1 : ∀ i, m i i = 1) (hm0 : ∀ i j, j < i → m i j = 0) :
    (∀ i, (n * m) i i = 1) ∧ ∀ i j, j < i → (n * m) i j = 0 := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hn1, hm1, one_mul]
    · intro l _ hl
      rcases lt_or_gt_of_ne hl with h | h
      · rw [hn0 i l h, zero_mul]
      · rw [hm0 l i h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l i with h | h
    · rw [hn0 i l h, zero_mul]
    · rw [hm0 l j (lt_of_lt_of_le hij h), mul_zero]

theorem le_of_swap {N : ℕ} (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ)
    (hk : kᵀ * k = 1) (ha : ∀ i, 0 < a i) (hn1 : ∀ i, n i i = 1) (hn0 : ∀ i j, j < i → n i j = 0)
    (hν : ∀ i j, i < j → |n i j| ≤ 1 / 2) (p q : Fin N) (hq : (q : ℕ) = p + 1)
    (hlt : ∏ j, gramMinor (k * diagonal a * n) j <
      2 * ∏ j, gramMinor ((k * diagonal a * n).submatrix id (Equiv.swap p q)) j) : a p ≤ 2 * a q := by
  set g := k * diagonal a * n with hg
  have hpq : p < q := by rw [Fin.lt_def]; omega
  have hqN : (q : ℕ) ≤ N := q.2.le
  obtain ⟨h1, h2⟩ := GlobalTheory.T.gram_minor_swap_adjacent_columns N k a n g (g.submatrix id (Equiv.swap p q)) p q hk hn1 hn0 hq rfl rfl
  have hG : ∀ j : Fin (N + 1),
      gramMinor g j = ∏ i : Fin j, a (Fin.castLE (Nat.lt_succ_iff.mp j.2) i) ^ 2 :=
    fun j => GlobalTheory.T.det_leading_minor_gram_iwasawa N k a n hk hn1 hn0 j _
  let qq : Fin (N + 1) := ⟨q, Nat.lt_succ_of_le hqN⟩
  have hpos : ∀ j, 0 < gramMinor g j := fun j => by
    rw [hG]
    exact Finset.prod_pos fun i _ => pow_pos (ha _) 2
  have hrest : ∏ j ∈ Finset.univ.erase qq, gramMinor (g.submatrix id (Equiv.swap p q)) j =
      ∏ j ∈ Finset.univ.erase qq, gramMinor g j := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hne : (j : ℕ) ≠ q := fun h => (Finset.mem_erase.mp hj).1 (Fin.ext h)
    exact h1 j (Nat.lt_succ_iff.mp j.2) hne
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ qq),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ qq), hrest] at hlt
  have hR : 0 < ∏ j ∈ Finset.univ.erase qq, gramMinor g j := Finset.prod_pos fun j _ => hpos j
  have hlt' : gramMinor g qq < 2 * gramMinor (g.submatrix id (Equiv.swap p q)) qq := by
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith [mul_le_mul_of_nonneg_right hc' hR.le]
  have eG : gramMinor g qq = (∏ l ∈ Finset.univ.filter (· < p), a l ^ 2) * a p ^ 2 := by
    rw [hG]
    exact prod_castLE_succ (fun i => a i ^ 2) p q hq _
  have eG' : gramMinor (g.submatrix id (Equiv.swap p q)) qq =
      (∏ l ∈ Finset.univ.filter (· < p), a l ^ 2) * (a q ^ 2 + n p q ^ 2 * a p ^ 2) := h2 hqN
  rw [eG, eG'] at hlt'
  have hP : 0 < ∏ l ∈ Finset.univ.filter (· < p), a l ^ 2 :=
    Finset.prod_pos fun l _ => pow_pos (ha l) 2
  have hn : n p q ^ 2 ≤ 1 / 4 := by
    have h3 := abs_le.mp (hν p q hpq)
    nlinarith [h3.1, h3.2]
  have key : a p ^ 2 < 2 * (a q ^ 2 + n p q ^ 2 * a p ^ 2) := by
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith [mul_le_mul_of_nonneg_left hc' hP.le]
  have hap := ha p
  have haq := ha q
  by_contra hc
  have hc' := not_le.mp hc
  nlinarith [mul_lt_mul'' hc' hc' (by positivity) (by positivity),
    mul_le_mul_of_nonneg_right hn (sq_nonneg (a p))]

theorem exists_reduced : ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ (γ : Matrix (Fin N) (Fin N) ℤ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), (γ.det = 1 ∨ γ.det = -1) ∧ kᵀ * k = 1 ∧ (∀ i, 0 < a i) ∧ (∀ i, n i i = 1) ∧ (∀ i j, j < i → n i j = 0) ∧ (∀ i j, i < j → |n i j| ≤ 1 / 2) ∧ (∀ p q : Fin N, (q : ℕ) = p + 1 → a p ≤ 2 * a q) ∧ g * γ.map (Int.cast : ℤ → ℝ) = k * diagonal a * n := by
  intro N g hg
  obtain ⟨c, hc, hcb⟩ := GlobalTheory.T.gram_leading_minor_lower_bound_integral N g hg
  let S := {γ : Matrix (Fin N) (Fin N) ℤ // γ.det = 1 ∨ γ.det = -1}
  have : Nonempty S := ⟨⟨1, Or.inl Matrix.det_one⟩⟩
  have hdet0 : ∀ γ : S, γ.1.det ≠ 0 := fun γ => by
    rcases γ.2 with h | h <;> rw [h] <;> norm_num
  have hbound : ∀ γ : S, c ^ (N + 1) ≤ ∏ j, gramMinor (g * γ.1.map (Int.cast : ℤ → ℝ)) j := by
    intro γ
    calc c ^ (N + 1) = ∏ _j : Fin (N + 1), c := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hc.le)
          (fun j _ => hcb γ.1 (hdet0 γ) j (Nat.lt_succ_iff.mp j.2))
  obtain ⟨γ0, hγ0⟩ := exists_lt_two_mul
    (fun γ : S => ∏ j, gramMinor (g * γ.1.map (Int.cast : ℤ → ℝ)) j) (c ^ (N + 1)) (pow_pos hc _) hbound
  have hgd : (g * γ0.1.map (Int.cast : ℤ → ℝ)).det ≠ 0 := by
    rw [Matrix.det_mul]
    refine mul_ne_zero hg ?_
    rw [← Int.cast_det]
    exact_mod_cast hdet0 γ0
  obtain ⟨k, a, n, hk, ha, hn1, hn0, hgk⟩ := GlobalTheory.T.iwasawa_decomposition_real_matrix N _ hgd
  obtain ⟨ν, hν1, hν0, hνb⟩ := GlobalTheory.T.unipotent_upper_size_reduction N n hn1 hn0
  have hνR1 : ∀ i, ν.map (Int.cast : ℤ → ℝ) i i = 1 := fun i => by simp [hν1]
  have hνR0 : ∀ i j, j < i → ν.map (Int.cast : ℤ → ℝ) i j = 0 := fun i j h => by simp [hν0 i j h]
  obtain ⟨hn'1, hn'0⟩ := mul_upper n _ hn1 hn0 hνR1 hνR0
  have hνdet : ν.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j h => hν0 i j h)]
    simp [hν1]
  have hγdet : (γ0.1 * ν).det = 1 ∨ (γ0.1 * ν).det = -1 := by
    rw [Matrix.det_mul, hνdet, mul_one]
    exact γ0.2
  have hmap : (γ0.1 * ν).map (Int.cast : ℤ → ℝ) =
      γ0.1.map (Int.cast : ℤ → ℝ) * ν.map (Int.cast : ℤ → ℝ) :=
    Matrix.map_mul (f := Int.castRingHom ℝ)
  have heq : g * (γ0.1 * ν).map (Int.cast : ℤ → ℝ) =
      k * diagonal a * (n * ν.map (Int.cast : ℤ → ℝ)) := by
    rw [hmap, ← Matrix.mul_assoc, hgk, Matrix.mul_assoc (k * diagonal a)]
  have hΦ : ∏ j, gramMinor (k * diagonal a * (n * ν.map (Int.cast : ℤ → ℝ))) j =
      ∏ j, gramMinor (g * γ0.1.map (Int.cast : ℤ → ℝ)) j := by
    rw [hgk]
    refine Finset.prod_congr rfl fun j _ => ?_
    unfold gramMinor
    rw [GlobalTheory.T.det_leading_minor_gram_iwasawa N k a _ hk hn'1 hn'0 j _, GlobalTheory.T.det_leading_minor_gram_iwasawa N k a n hk hn1 hn0 j _]
  refine ⟨γ0.1 * ν, k, a, n * ν.map (Int.cast : ℤ → ℝ), hγdet, hk, ha, hn'1, hn'0, hνb,
    fun p q hq => ?_, heq⟩
  have hpq : p ≠ q := fun h => by rw [h] at hq; omega
  let γ' : S := ⟨(γ0.1 * ν).submatrix id (Equiv.swap p q), by
    rw [Matrix.det_permute', Equiv.Perm.sign_swap hpq]
    rcases hγdet with h | h <;> simp [h]⟩
  have hsw : g * γ'.1.map (Int.cast : ℤ → ℝ) =
      (k * diagonal a * (n * ν.map (Int.cast : ℤ → ℝ))).submatrix id (Equiv.swap p q) := by
    rw [← heq]
    ext i j
    rfl
  refine le_of_swap k a _ hk ha hn'1 hn'0 hνb p q hq ?_
  rw [hΦ, ← hsw]
  exact hγ0 γ'

end GlobalTheory.ClassFin.HermiteReduction
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.pow_card_le_index_iInf_of_prime' : ∀ (p : ℕ) (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G), p.Prime → (∀ (i : ι) (x : G), x ^ p ∈ K i) → (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) → (⨅ i, K i).index ≠ 0 → p ^ Fintype.card ι ≤ (⨅ i, K i).index := by
  first | exact @GlobalTheory.CNorm.pow_card_le_index_iInf_of_prime | exact GlobalTheory.CNorm.pow_card_le_index_iInf_of_prime | (intros; apply GlobalTheory.CNorm.pow_card_le_index_iInf_of_prime <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.algebraMap_norm_tensor_eq_prod_galois_conjugates : ∀ (F E K : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] [IsGalois F E] [CommRing K] [Algebra F K] (y : K ⊗[F] E), algebraMap K (K ⊗[F] E) (Algebra.norm K y) = ∏ g : E ≃ₐ[F] E, Algebra.TensorProduct.map (AlgHom.id K K) (g : E →ₐ[F] E) y := by
  first | exact @GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates | exact GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates | (intros; apply GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.exists_tensor_eq_of_fixed_by_algEquiv : ∀ (F M E K : Type) [Field F] [CharZero F] [Field M] [Field E] [Algebra F M] [Algebra M E] [Algebra F E] [IsScalarTower F M E] [FiniteDimensional M E] [IsGalois M E] [CommRing K] [Algebra F K] (y : K ⊗[F] E), (∀ h : E ≃ₐ[M] E, Algebra.TensorProduct.map (AlgHom.id K K) ((h.restrictScalars F : E ≃ₐ[F] E) : E →ₐ[F] E) y = y) → ∃ z : K ⊗[F] M, Algebra.TensorProduct.map (AlgHom.id K K) (IsScalarTower.toAlgHom F M E) z = y := by
  first | exact @GlobalTheory.CNorm.tensor_exists_of_galois_fixed | exact GlobalTheory.CNorm.tensor_exists_of_galois_fixed | (intros; apply GlobalTheory.CNorm.tensor_exists_of_galois_fixed <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.index_range_ker_iterate_endomorphism : ∀ (M : Type) [CommGroup M] (f : Monoid.End M) (k : ℕ), (MonoidHom.range (f ^ (k + 1) : Monoid.End M)).index ≠ 0 → Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) ≠ 0 → (MonoidHom.range f).index ≠ 0 ∧ Nat.card (MonoidHom.ker f) ≠ 0 ∧ (MonoidHom.range (f ^ (k + 1) : Monoid.End M)).index * Nat.card (MonoidHom.ker f) ^ (k + 1) = (MonoidHom.range f).index ^ (k + 1) * Nat.card (MonoidHom.ker (f ^ (k + 1) : Monoid.End M)) := by
  first | exact @GlobalTheory.CNorm.index_ker_iterate | exact GlobalTheory.CNorm.index_ker_iterate | (intros; apply GlobalTheory.CNorm.index_ker_iterate <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.hilbert90_baseChange' : ∀ (F E K : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [FiniteDimensional F E] [Field K] [Algebra F K] (τ : E ≃ₐ[F] E) (m : ℕ), orderOf τ = m → ∀ x : K ⊗[F] E, ∏ i ∈ Finset.range m, (Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E))^[i] x = 1 → ∃ z : (K ⊗[F] E)ˣ, x * Algebra.TensorProduct.map (AlgHom.id K K) (τ : E →ₐ[F] E) z = z := by
  first | exact @GlobalTheory.CNorm.hilbert90_baseChange | exact GlobalTheory.CNorm.hilbert90_baseChange | (intros; apply GlobalTheory.CNorm.hilbert90_baseChange <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem two_places_of_embeddings : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (ψ ψ' : E →ₐ[F] v.adicCompletion F), ψ ≠ ψ' → ∃ w w' : HeightOneSpectrum (𝓞 E), w ≠ w' ∧ w.under (𝓞 F) = v ∧ w'.under (𝓞 F) = v := by
  intro F E _ _ _ _ _ v ψ ψ' hne
  let V : Valuation (v.adicCompletion F) ℤᵐ⁰ := Valued.v
  let u : Valuation E ℤᵐ⁰ := V.comap (ψ : E →+* v.adicCompletion F)
  let u' : Valuation E ℤᵐ⁰ := V.comap (ψ' : E →+* v.adicCompletion F)
  have hu : ∀ a : F, u (algebraMap F E a) = v.valuation F a := by
    intro a
    change Valued.v (ψ _) = _
    rw [AlgHom.commutes]
    exact v.valuedAdicCompletion_eq_valuation' a
  have hu' : ∀ a : F, u' (algebraMap F E a) = v.valuation F a := by
    intro a
    change Valued.v (ψ' _) = _
    rw [AlgHom.commutes]
    exact v.valuedAdicCompletion_eq_valuation' a
  obtain ⟨w, hw, hwm⟩ := exists_centre_over v u hu
  obtain ⟨w', hw', hwm'⟩ := exists_centre_over v u' hu'
  refine ⟨w, w', ?_, hw, hw'⟩
  rintro rfl
  obtain ⟨z, hz⟩ : ∃ z, ψ z ≠ ψ' z := by
    by_contra hc
    push Not at hc
    exact hne (AlgHom.ext hc)
  obtain ⟨d, hd⟩ : ∃ d, d = ψ z - ψ' z := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := by rw [hd]; exact sub_ne_zero.2 hz
  have hVd : V d ≠ 0 := (Valuation.ne_zero_iff _).2 hd0
  obtain ⟨ρ, hρ⟩ := exists_val_sub_mul_lt_one _ (HeightOneSpectrum.denseRange_algebraMap F v)
    (ψ z) d⁻¹
  obtain ⟨c, hc⟩ := exists_val_sub_mul_lt_one _ (HeightOneSpectrum.denseRange_algebraMap F v)
    d d⁻¹
  set t := (ψ z - algebraMap F (v.adicCompletion F) ρ) * d⁻¹ with ht
  set s := (d - algebraMap F (v.adicCompletion F) c) * d⁻¹ with hs
  have e1 : ψ z - algebraMap F (v.adicCompletion F) ρ = d * t := by
    rw [ht]; field_simp
  have e2 : ψ' z - algebraMap F (v.adicCompletion F) ρ = -(d * (1 - t)) := by
    linear_combination e1 + hd
  have e3 : algebraMap F (v.adicCompletion F) c = d * (1 - s) := by
    rw [hs]; field_simp; ring
  obtain ⟨y, hy⟩ : ∃ y, y = (z - algebraMap F E ρ) / algebraMap F E c := ⟨_, rfl⟩
  have huy : u y < 1 := by
    change V (ψ y) < 1
    rw [hy, map_div₀, map_sub, AlgHom.commutes, AlgHom.commutes, e1, e3, map_div₀,
      map_mul _ _ t, map_mul _ _ (1 - s), Valuation.map_one_sub_of_lt _ hc, mul_one,
      mul_div_cancel_left₀ _ hVd]
    exact hρ
  have huy' : u' y = 1 := by
    change V (ψ' y) = 1
    rw [hy, map_div₀, map_sub, AlgHom.commutes, AlgHom.commutes, e2, e3, map_div₀,
      Valuation.map_neg, map_mul _ _ (1 - t), map_mul _ _ (1 - s),
      Valuation.map_one_sub_of_lt _ hc, Valuation.map_one_sub_of_lt _ hρ, div_self]
    rwa [mul_one]
  obtain ⟨n, ⟨m, hm⟩, hnd | hnd⟩ := w.exists_primeCompl_mul_eq_or_mul_eq (K := E) y
  · have hd1 : 1 ≤ u' (algebraMap (𝓞 E) E m) := not_lt.1 fun a => hm ((hwm' m).2 a)
    have h1 : u (algebraMap (𝓞 E) E n) < 1 := by
      rw [← hnd, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right' (val_integer_le_one u m)) huy
    have h2 := (hwm' n).1 ((hwm n).2 h1)
    rw [← hnd, map_mul, huy', one_mul] at h2
    exact absurd h2 (not_lt.2 hd1)
  · have hd1 : 1 ≤ u (algebraMap (𝓞 E) E m) := not_lt.1 fun a => hm ((hwm m).2 a)
    rw [← hnd, map_mul] at hd1
    exact absurd (lt_of_le_of_lt (mul_le_of_le_one_right' (val_integer_le_one u n)) huy)
      (not_lt.2 hd1)

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.exists_approx_mod_powers' : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F), 0 < p → (∀ v, y v ≠ 0) → ∃ x : F, x ≠ 0 ∧ ∀ v ∈ S, ∃ r : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = y v * r ^ p := by
  first | exact @GlobalTheory.CNorm.exists_approx_mod_powers | exact GlobalTheory.CNorm.exists_approx_mod_powers | (intros; apply GlobalTheory.CNorm.exists_approx_mod_powers <;> assumption)
end
