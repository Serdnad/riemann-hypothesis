module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Data.Matrix.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle040
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156
import Development.AbelianVarietyTheory.Definitions.Divisors.HasBoundedPolesGlobalData
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle031
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle001
public import Mathlib.Data.Fintype.Sum
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001
import ReciprocityTheory.SemistableReduction.Bundle002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112

@[expose] public section

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Northcott

theorem isIntegral_eig {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : IsIntegral ℤ M) {w : ℂ}
    {x : Fin n → ℂ} (hx : x ≠ 0) (hMx : M *ᵥ x = w • x) : IsIntegral ℤ w := by
  obtain ⟨q, hq, hqM⟩ := hM
  refine ⟨q, hq, ?_⟩
  have hv : Module.End.HasEigenvector (Matrix.toLin' M) w x :=
    ⟨Module.End.mem_eigenspace_iff.2 (by simpa [Matrix.toLin'_apply] using hMx), hx⟩
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := q.map (algebraMap ℤ ℂ)) hv
  have h2 : Polynomial.aeval (Matrix.toLin' M) (q.map (algebraMap ℤ ℂ)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    have e := Polynomial.aeval_algHom_apply
      ((Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) ℂ ≃ₐ[ℂ] _).toAlgHom.restrictScalars ℤ) M q
    have e2 : Polynomial.aeval M q = 0 := hqM
    rw [e2, map_zero] at e
    exact e
  rw [h2, LinearMap.zero_apply] at h1
  have h3 := (smul_eq_zero.1 h1.symm).resolve_right hx
  rwa [Polynomial.eval_map] at h3

theorem norm_le_of_isIntegral_inv (w : ℂ) (c : ℚ) (N : ℕ) (hN : 0 < N) (hw : ‖w‖ ^ 2 = (c : ℝ))
    (hc : (c : ℝ) ≠ 0) (hI : IsIntegral ℤ ((N : ℂ) * w⁻¹)) : ‖w‖ ≤ N := by
  have hcpos : (0 : ℝ) < c := lt_of_le_of_ne (hw ▸ sq_nonneg _) (Ne.symm hc)
  have hconj : IsIntegral ℤ (starRingEnd ℂ ((N : ℂ) * w⁻¹)) := hI.map (starRingEnd ℂ).toIntAlgHom
  have hprod := hI.mul hconj
  have e : (N : ℂ) * w⁻¹ * starRingEnd ℂ ((N : ℂ) * w⁻¹) = (((N : ℚ) ^ 2 / c : ℚ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_mul, norm_inv, mul_pow, inv_pow, hw,
      Complex.norm_natCast]
    push_cast
    ring
  rw [e] at hprod
  have hq : IsIntegral ℤ ((N : ℚ) ^ 2 / c) := by
    refine (isIntegral_algHom_iff ((algebraMap ℚ ℂ).toIntAlgHom) (algebraMap ℚ ℂ).injective
      (x := (N : ℚ) ^ 2 / c)).1 ?_
    simpa using hprod
  obtain ⟨k, hk⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).1 hq
  have hcq : (0 : ℚ) < c := by exact_mod_cast hcpos
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hpos : (0 : ℚ) < (N : ℚ) ^ 2 / c := by positivity
  have hk1 : (1 : ℚ) ≤ (N : ℚ) ^ 2 / c := by
    rw [← hk] at hpos ⊢
    rw [algebraMap_int_eq, eq_intCast] at hpos ⊢
    have : (0 : ℤ) < k := by exact_mod_cast hpos
    have : (1 : ℤ) ≤ k := this
    exact_mod_cast this
  have hcN : (c : ℚ) ≤ (N : ℚ) ^ 2 := by rwa [le_div_iff₀ hcq, one_mul] at hk1
  have hcN' : (c : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hcN
  rw [← hw] at hcN'
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Nat.cast_nonneg _) two_ne_zero).1 hcN'

end GlobalTheory.LKMid.Northcott
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory

theorem similitude_eigvec_orthogonal : ∀ {n : ℕ} (h g : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) (Z : GL (Fin n) ℂ) (lam : Fin n → ℂ), h.IsHermitian → h.det ≠ 0 → c ≠ 0 → gᴴ * h * g = (c : ℂ) • h → Function.Injective lam → (∀ i, ‖lam i‖ ^ 2 = c) → g * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * Matrix.diagonal lam → ∃ d : Fin n → ℝ, (∀ i, d i ≠ 0) ∧ (Z : Matrix (Fin n) (Fin n) ℂ)ᴴ * h * (Z : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal (fun i => (d i : ℂ)) := by
  intro n h g c Z lam hh hdet hc hg hinj hnorm hgZ
  set M : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ) with hM
  set H : Matrix (Fin n) (Fin n) ℂ := Mᴴ * h * M with hH
  have hHherm : H.IsHermitian := by
    simp only [hH, IsHermitian, conjTranspose_mul, conjTranspose_conjTranspose, hh.eq, Matrix.mul_assoc]
  have key : (Matrix.diagonal lam)ᴴ * H * Matrix.diagonal lam = (c : ℂ) • H := by
    have e1 : (M * Matrix.diagonal lam)ᴴ * h * (M * Matrix.diagonal lam) = (Matrix.diagonal lam)ᴴ * H * Matrix.diagonal lam := by
      simp only [hH, conjTranspose_mul, Matrix.mul_assoc]
    rw [← e1, ← hgZ]
    simp only [hH, conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc gᴴ, ← Matrix.mul_assoc (gᴴ * h), hg]
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hc' : ∀ i, (starRingEnd ℂ) (lam i) * lam i = (c : ℂ) := by
    intro i
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast hnorm i
  have hlam0 : ∀ i, lam i ≠ 0 := by
    intro i h0
    have := hnorm i
    rw [h0, norm_zero] at this
    exact hc (by simpa using this.symm)
  have hoff : ∀ i j, i ≠ j → H i j = 0 := by
    intro i j hij
    have e := congrFun (congrFun key i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul] at e
    simp only [Matrix.smul_apply, smul_eq_mul] at e
    have hne : lam j - lam i ≠ 0 := sub_ne_zero.mpr (fun h => hij (hinj h).symm)
    have hstar : (starRingEnd ℂ) (lam i) ≠ 0 := by simpa using hlam0 i
    have e2 : (starRingEnd ℂ) (lam i) * (lam j - lam i) * H i j = 0 := by
      rw [← hc' i] at e
      simp only [Pi.star_apply] at e
      have : star (lam i) = (starRingEnd ℂ) (lam i) := rfl
      rw [this] at e
      linear_combination e
    rcases mul_eq_zero.mp e2 with h1 | h1
    · exact absurd h1 (mul_ne_zero hstar hne)
    · exact h1
  have hdiag : H = Matrix.diagonal (fun i => (((H i i).re : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      exact (hHherm.coe_re_apply_self i).symm
    · rw [Matrix.diagonal_apply_ne _ hij, hoff i j hij]
  refine ⟨fun i => (H i i).re, ?_, hdiag⟩
  have hdetH : H.det ≠ 0 := by
    have hMdet : M.det ≠ 0 := by
      rw [hM]; exact (Matrix.isUnit_iff_isUnit_det _).mp Z.isUnit |>.ne_zero
    simp only [hH, Matrix.det_mul, Matrix.det_conjTranspose]
    exact mul_ne_zero (mul_ne_zero (by simpa using hMdet) hdet) hMdet
  intro i hi
  rw [hdiag, Matrix.det_diagonal] at hdetH
  apply hdetH
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

end GlobalTheory
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.MatUnitIso

variable {k K B : Type} [Field k] [CommRing K] [Ring B] [Algebra k K] [Algebra k B]

def phiL {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B) :
    Matrix (Fin n) (Fin n) K →ₗ[k] B where
  toFun M := ∑ a, ∑ b, ι (M a b) * E a b
  map_add' M N := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c M := by simp [Finset.smul_sum, smul_mul_assoc]

theorem phiL_apply {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B) (M) :
    phiL ι E M = ∑ a, ∑ b, ι (M a b) * E a b := rfl

theorem core {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B)
    (hc : ∀ z x, Commute (ι z) x)
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    (M : Matrix (Fin n) (Fin n) K) (c a d e : Fin n) :
    E c a * phiL ι E M * E d e = ι (M a d) * E c e := by
  have h : ∀ a' b', E c a * (ι (M a' b') * E a' b') * E d e
      = if a = a' then (if b' = d then ι (M a d) * E c e else 0) else 0 := by
    intro a' b'
    rw [← mul_assoc, ← (hc (M a' b') (E c a)).eq]
    simp only [mul_assoc, hE, mul_ite, mul_zero]
    split_ifs with h1 h2
    · subst h1 h2; rw [mul_assoc, hE, if_pos rfl]
    · rw [mul_assoc, hE, if_neg h2, mul_zero]
    · rw [zero_mul]
  simp only [phiL_apply, Finset.mul_sum, Finset.sum_mul, h]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem extract {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B)
    (hc : ∀ z x, Commute (ι z) x)
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    (h1 : ∑ a, E a a = 1) (M : Matrix (Fin n) (Fin n) K) (a b : Fin n) :
    ∑ c, E c a * phiL ι E M * E b c = ι (M a b) := by
  simp only [core ι E hc hE, ← Finset.mul_sum, h1, mul_one]

theorem phiL_injective {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B)
    (hi : Function.Injective ι) (hc : ∀ z x, Commute (ι z) x)
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    (h1 : ∑ a, E a a = 1) : Function.Injective (phiL ι E) := by
  intro M N h
  ext a b
  apply hi
  rw [← extract ι E hc hE h1 M a b, ← extract ι E hc hE h1 N a b, h]

theorem phiL_one {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B)
    (h1 : ∑ a, E a a = 1) : phiL ι E 1 = 1 := by
  simp [phiL_apply, Matrix.one_apply, h1]

theorem phiL_mul {n : ℕ} (ι : K →ₐ[k] B) (E : Fin n → Fin n → B)
    (hc : ∀ z x, Commute (ι z) x)
    (hE : ∀ a b c d, E a b * E c d = if b = c then E a d else 0)
    (M N : Matrix (Fin n) (Fin n) K) :
    phiL ι E (M * N) = phiL ι E M * phiL ι E N := by
  have h : ∀ a b c d, ι (M a b) * E a b * (ι (N c d) * E c d)
      = if b = c then ι (M a b * N b d) * E a d else 0 := by
    intro a b c d
    rw [mul_assoc, ← mul_assoc (E a b), ← (hc (N c d) (E a b)).eq, mul_assoc, hE,
      ← mul_assoc, ← map_mul]
    split_ifs with hbc
    · subst hbc; rfl
    · rw [mul_zero]

  simp only [phiL_apply, Finset.sum_mul, Finset.mul_sum, h, Matrix.mul_apply, map_sum]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]

theorem matrixRingEquiv_of_matrixUnits : ∀ (k K B : Type) [Field k] [CommRing K] [Ring B] [Algebra k K] [Algebra k B] [FiniteDimensional k B] (n : ℕ) (ι : K →ₐ[k] B), Function.Injective ι → (∀ z x, Commute (ι z) x) → Module.finrank k B = n ^ 2 * Module.finrank k K → ∀ E : Fin n → Fin n → B, (∀ a b c d, E a b * E c d = if b = c then E a d else 0) → ∑ a, E a a = 1 → ∃ Φ : Matrix (Fin n) (Fin n) K ≃+* B, (∀ M, Φ M = ∑ a, ∑ b, ι (M a b) * E a b) ∧ ∀ x a b, ι (Φ.symm x a b) = ∑ c, E c a * x * E b c := by
  intro k K B _ _ _ _ _ _ n ι hi hc hdim E hE h1
  haveI : FiniteDimensional k K := FiniteDimensional.of_injective (ι : K →ₐ[k] B).toLinearMap hi
  have hinj := phiL_injective ι E hi hc hE h1
  have hrank : Module.finrank k (Matrix (Fin n) (Fin n) K) = Module.finrank k B := by
    rw [Module.finrank_matrix, hdim]; simp [Fintype.card_fin, sq]
  have hsurj : Function.Surjective (phiL ι E) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj
  let f : Matrix (Fin n) (Fin n) K →+* B :=
    { toFun := phiL ι E
      map_one' := phiL_one ι E h1
      map_mul' := phiL_mul ι E hc hE
      map_zero' := map_zero _
      map_add' := map_add _ }
  let Φ : Matrix (Fin n) (Fin n) K ≃+* B := RingEquiv.ofBijective f ⟨hinj, hsurj⟩
  refine ⟨Φ, fun M => rfl, fun x a b => ?_⟩
  obtain ⟨M, rfl⟩ := hsurj x
  have hx : Φ.symm (phiL ι E M) = M := Φ.symm_apply_apply M
  rw [hx]
  exact (extract ι E hc hE h1 M a b).symm

end GlobalTheory.MatUnitIso
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem exchange_independent_completion (E M : Type) [Field E] [AddCommGroup M] [Module E M]
    (n d : ℕ) (v : Fin n → M) (w : Fin d → M) (hv : LinearIndependent E v)
    (hw : LinearIndependent E w) (hvw : ∀ k, v k ∈ Submodule.span E (Set.range w)) :
    ∃ K : Finset (Fin d), n + K.card = d ∧ LinearIndependent E (Sum.elim v fun k : K => w k) := by
  classical
  obtain ⟨b, hbt, hsb, htb, hb⟩ := exists_linearIndepOn_id_extension
    (s := Set.range v) (t := Set.range v ∪ Set.range w) (K := E)
    hv.linearIndepOn_id Set.subset_union_left
  let K : Finset (Fin d) := Finset.univ.filter (fun k => w k ∈ b ∧ w k ∉ Set.range v)
  let u : Fin n ⊕ K → M := Sum.elim v fun k : K => w k
  have hK : ∀ k : K, w k ∈ b ∧ w k ∉ Set.range v := fun k => (Finset.mem_filter.1 k.2).2
  have hu_inj : Function.Injective u := by
    rintro (i | i) (j | j) h
    · simp only [u, Sum.elim_inl] at h; rw [hv.injective h]
    · simp only [u, Sum.elim_inl, Sum.elim_inr] at h; exact absurd ⟨i, h⟩ (hK j).2
    · simp only [u, Sum.elim_inl, Sum.elim_inr] at h; exact absurd ⟨j, h.symm⟩ (hK i).2
    · simp only [u, Sum.elim_inr] at h; rw [Subtype.ext (hw.injective h)]
  have hu_mem : ∀ x, u x ∈ b := by
    rintro (i | i)
    · exact hsb ⟨i, rfl⟩
    · exact (hK i).1
  have hu_range : Set.range u = b := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact hu_mem x
    · intro x hx
      by_cases hxv : x ∈ Set.range v
      · obtain ⟨i, rfl⟩ := hxv; exact ⟨Sum.inl i, rfl⟩
      · rcases hbt hx with ⟨i, rfl⟩ | ⟨k, rfl⟩
        · exact absurd ⟨i, rfl⟩ hxv
        · have hk : k ∈ K := Finset.mem_filter.2 ⟨Finset.mem_univ _, hx, hxv⟩
          exact ⟨Sum.inr ⟨k, hk⟩, rfl⟩
  have hli : LinearIndependent E u :=
    LinearIndependent.comp (show LinearIndependent E (fun x : b => (x : M)) from hb) (fun x => (⟨u x, hu_mem x⟩ : b)) (fun x y h => hu_inj (congrArg Subtype.val h))
  refine ⟨K, ?_, hli⟩
  have hspan : Submodule.span E (Set.range u) = Submodule.span E (Set.range w) := by
    apply le_antisymm
    · rw [Submodule.span_le, hu_range]
      intro x hx
      rcases hbt hx with ⟨i, rfl⟩ | ⟨k, rfl⟩
      · exact hvw i
      · exact Submodule.subset_span ⟨k, rfl⟩
    · rw [Submodule.span_le, hu_range]; exact Set.subset_union_right.trans htb
  have h1 := finrank_span_eq_card hli
  have h2 := finrank_span_eq_card hw
  rw [hspan, h2] at h1
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe] at h1
  omega

end GlobalTheory
end

section

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory

theorem charpoly_eq_of_monic_aeval_linearIndependent :
    ∀ (K : Type) [CommRing K] (n : ℕ) (X : Matrix (Fin n) (Fin n) K) (P : Polynomial K),
      P.Monic → P.natDegree = n → Polynomial.aeval X P = 0 →
      LinearIndependent K (fun i : Fin n => X ^ (i : ℕ)) → X.charpoly = P := by
  intro K _ n X P hP hdeg hX hli
  rcases subsingleton_or_nontrivial K with hK | hK
  · exact Subsingleton.elim _ _
  have hc : X.charpoly.Monic := Matrix.charpoly_monic X
  have hcd : X.charpoly.natDegree = n := by
    simpa using Matrix.charpoly_natDegree_eq_dim X
  have hcdeg : X.charpoly.degree = n := by
    rw [Polynomial.degree_eq_natDegree hc.ne_zero, hcd]
  have hPdeg : P.degree = n := by
    rw [Polynomial.degree_eq_natDegree hP.ne_zero, hdeg]
  have hDdeg : (X.charpoly - P).degree < n := by
    have h := Polynomial.degree_sub_lt (p := X.charpoly) (q := P)
      (by rw [hcdeg, hPdeg]) hc.ne_zero (by rw [hc.leadingCoeff, hP.leadingCoeff])
    rwa [hcdeg] at h
  have hDaeval : Polynomial.aeval X (X.charpoly - P) = 0 := by
    rw [map_sub, Matrix.aeval_self_charpoly, hX, sub_zero]
  rw [← sub_eq_zero]
  by_contra hD0
  have hnat : (X.charpoly - P).natDegree < n :=
    (Polynomial.natDegree_lt_iff_degree_lt hD0).mpr hDdeg
  have hsum : ∑ i : Fin n, (X.charpoly - P).coeff (i : ℕ) • X ^ (i : ℕ) = 0 := by
    have h := Polynomial.aeval_eq_sum_range' hnat X
    rw [hDaeval, Finset.sum_range (fun i => (X.charpoly - P).coeff i • X ^ i)] at h
    exact h.symm
  have hcoeff := Fintype.linearIndependent_iff.mp hli
    (fun i : Fin n => (X.charpoly - P).coeff (i : ℕ)) hsum
  apply hD0
  ext k
  rw [Polynomial.coeff_zero]
  by_cases hk : k < n
  · exact hcoeff ⟨k, hk⟩
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hnat (not_lt.mp hk))

end GlobalTheory
end

section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSChoice GlobalTheory.HSShort

namespace GlobalTheory

theorem exists_basis_choice_det_ne_zero : ∀ (F E A A' : Type) [Field F] [Field E] [Algebra F E] [AddCommGroup A] [Module F A] [AddCommGroup A'] [Module E A'] (ι : A →ₛₗ[algebraMap F E] A') (V : Submodule F A) (r δ : ℕ) (bb : Module.Basis (Fin r) F V) (res : A' →ₗ[E] (Fin δ → E)), (Submodule.span E (ι '' (V : Set A))).map res = ⊤ → ∃ σ : Fin δ → Fin r, (Matrix.of fun p' p => res (ι (bb (σ p))) p').det ≠ 0 := by
  intro F E A A' _ _ _ _ _ _ _ ι V r δ bb res h
  have hsub : ι '' (V : Set A) ⊆ Submodule.span E (Set.range fun i => ι (bb i)) := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x = ∑ i, bb.repr ⟨x, hx⟩ i • ((bb i : V) : A) := by
      have := congrArg Subtype.val (bb.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at this
      exact this.symm

    rw [hx', map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span E (Set.range fun i => res (ι (bb i))) = ⊤ := by
    have h1 := Submodule.map_mono (f := res) (Submodule.span_le.mpr hsub)
    rw [h, Submodule.map_span, ← Set.range_comp] at h1
    exact eq_top_iff.mpr h1
  obtain ⟨b, hb, hbspan, hli⟩ := exists_linearIndependent E (Set.range fun i => res (ι (bb i)))
  let bs := Module.Basis.mk hli (by rw [Subtype.range_coe, hbspan, hspan])
  let e := bs.indexEquiv (Pi.basisFun E (Fin δ))
  have hmem : ∀ p, ((e.symm p : b) : Fin δ → E) ∈ Set.range fun i => res (ι (bb i)) :=
    fun p => hb (e.symm p).2
  choose σ hσ using hmem
  refine ⟨σ, ?_⟩
  have hli2 : LinearIndependent E (fun p => res (ι (bb (σ p)))) := by
    have : (fun p => res (ι (bb (σ p)))) = ((↑) : b → Fin δ → E) ∘ e.symm := funext fun p => hσ p
    rw [this]
    exact hli.comp _ e.symm.injective
  have hunit : IsUnit (Matrix.of fun p' p => res (ι (bb (σ p))) p') := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli2
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

end GlobalTheory
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

namespace GlobalTheory

theorem exists_left_basis_through_algHom : ∀ (L : Type) [Field L] [NumberField L] (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C]
    (ι : L →ₐ[ℚ] C), ∃ (r : ℕ) (e : Fin r → C), ∀ x : C, ∃! c : Fin r → L, x = ∑ i, ι (c i) * e i := by
  intro L _ _ C _ _ _ ι
  letI : Module L C := Module.compHom C ι.toRingHom
  have hsmul : ∀ (l : L) (x : C), l • x = ι l * x := fun _ _ => rfl
  haveI : IsScalarTower ℚ L C := ⟨fun q l x => by
    rw [hsmul, hsmul, map_smul, smul_mul_assoc]⟩
  haveI : Module.Finite L C := Module.Finite.of_restrictScalars_finite ℚ L C
  let b := Module.finBasis L C
  refine ⟨Module.finrank L C, b, fun x => ⟨b.repr x, ?_, ?_⟩⟩
  · simp only [← hsmul]
    exact (b.sum_repr x).symm
  · intro c hc
    simp only [← hsmul] at hc
    rw [hc, b.repr_sum_self]

end GlobalTheory
end
