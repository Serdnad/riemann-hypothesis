module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.NumberTheory.NumberField.Basic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Algebra.Order.Archimedean

@[expose] public section

section

open IsDedekindDomain NumberField

namespace GlobalTheory.SmithBetween

open Matrix


open IsDedekindDomain NumberField in
open Matrix in
theorem _root_.GlobalTheory.SmithBetween.exists_mul_eq_mul_diagonal {R : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n R) (hM : M.det ≠ 0) :
    ∃ P Q : Matrix n n R, IsUnit P.det ∧ IsUnit Q.det ∧ ∃ c : n → R,
      M * Q = P * Matrix.diagonal c := by
  have hinj : Function.Injective M.mulVecLin := Matrix.mulVec_injective_of_det_ne_zero hM
  obtain ⟨m, snf⟩ := Submodule.smithNormalForm (Pi.basisFun R n) (LinearMap.range M.mulVecLin)
  have hm : m = Fintype.card n := by
    have h1 := Module.finrank_eq_card_basis snf.bN
    rw [LinearMap.finrank_range_of_inj hinj] at h1
    simpa using h1.symm
  have hf : Function.Bijective snf.f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨snf.f.injective, by simp [hm]⟩
  let g : Fin m ≃ n := Equiv.ofBijective snf.f hf
  let eN := LinearEquiv.ofInjective M.mulVecLin hinj
  let bQ : Module.Basis n R (n → R) := (snf.bN.map eN.symm).reindex g
  letI := (Pi.basisFun R n).invertibleToMatrix snf.bM
  letI := (Pi.basisFun R n).invertibleToMatrix bQ
  refine ⟨(Pi.basisFun R n).toMatrix snf.bM, (Pi.basisFun R n).toMatrix bQ, ?_, ?_,
    fun j => snf.a (g.symm j), ?_⟩
  · exact isUnit_det_of_invertible _
  · exact isUnit_det_of_invertible _
  · ext i j
    have key : M *ᵥ bQ j = snf.a (g.symm j) • snf.bM j := by
      have h2 := snf.snf (g.symm j)
      have h3 : snf.f (g.symm j) = j := g.apply_symm_apply j
      rw [h3] at h2
      rw [← h2]
      simp only [bQ, Module.Basis.reindex_apply, Module.Basis.map_apply]
      have h4 : ((eN (eN.symm (snf.bN (g.symm j)))) : n → R) =
          M.mulVecLin (eN.symm (snf.bN (g.symm j))) := rfl
      rw [LinearEquiv.apply_symm_apply] at h4
      rw [← Matrix.mulVecLin_apply, ← h4]
    have := congrFun key i
    simp only [Matrix.mul_diagonal, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [Matrix.mul_apply]
    simp [Matrix.mulVec, dotProduct] at this
    simpa [mul_comm, Module.Basis.toMatrix_apply] using this

open IsDedekindDomain NumberField in
open Matrix in
theorem _root_.GlobalTheory.SmithBetween.smith_between (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (ϖ : R)
    (hϖ : Irreducible ϖ) (n k : ℕ) (hk : k ≤ n) (M M' : Matrix (Fin n) (Fin n) R)
    (hMM : M * M' = ϖ • (1 : Matrix (Fin n) (Fin n) R)) (hdet : Associated M.det (ϖ ^ k)) :
    ∃ P Q : Matrix (Fin n) (Fin n) R, IsUnit P.det ∧ IsUnit Q.det ∧
      M * Q = P * Matrix.diagonal (fun i : Fin n => if i.1 < n - k then (1 : R) else ϖ) := by
  classical
  have hM0 : M.det ≠ 0 := by
    rw [hdet.ne_zero_iff]; exact pow_ne_zero _ hϖ.ne_zero
  obtain ⟨P, Q, hP, hQ, c, hMQ⟩ := _root_.GlobalTheory.SmithBetween.exists_mul_eq_mul_diagonal M hM0
  have hdvd : ∀ j, c j ∣ ϖ := by
    intro j
    have hD : Matrix.diagonal c = P⁻¹ * M * Q := by
      rw [Matrix.mul_assoc, hMQ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul]
    have hX : Matrix.diagonal c * (Q⁻¹ * M' * P) = ϖ • (1 : Matrix (Fin n) (Fin n) R) := by
      rw [hD]
      calc P⁻¹ * M * Q * (Q⁻¹ * M' * P) = P⁻¹ * (M * (Q * Q⁻¹) * M') * P := by
            simp only [Matrix.mul_assoc]
        _ = ϖ • (1 : Matrix (Fin n) (Fin n) R) := by
            rw [Matrix.mul_nonsing_inv _ hQ, Matrix.mul_one, hMM, Matrix.mul_smul, Matrix.mul_one,
              Matrix.smul_mul, Matrix.nonsing_inv_mul _ hP]
    have := congrFun (congrFun hX j) j
    simp only [Matrix.diagonal_mul, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul,
      mul_one] at this
    exact ⟨_, this.symm⟩
  let d : Fin n → R := fun j => if IsUnit (c j) then 1 else ϖ
  have hu : ∀ j, ∃ u : Rˣ, c j = d j * u := by
    intro j
    by_cases h : IsUnit (c j)
    · exact ⟨h.unit, by simp [d, h]⟩
    · obtain ⟨b, hb⟩ := hdvd j
      rcases hϖ.isUnit_or_isUnit hb with h' | h'
      · exact absurd h' h
      · refine ⟨h'.unit⁻¹, ?_⟩
        simp only [d, h, if_false, hb]
        rw [mul_assoc, IsUnit.mul_val_inv, mul_one]
  choose u hu using hu

  set s := (Finset.univ.filter fun j => ¬IsUnit (c j)).card with hs
  have hprod : ∏ j, d j = ϖ ^ s := by
    simp only [d]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
  have hsk : s = k := by
    have h1 : M.det * Q.det = P.det * ∏ j, c j := by
      rw [← Matrix.det_mul, hMQ, Matrix.det_mul, Matrix.det_diagonal]
    have h2 : ∏ j, c j = ϖ ^ s * ∏ j, (u j : R) := by
      rw [← hprod, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ => hu j
    have h3 : Associated (ϖ ^ s) M.det := by
      have hA : Associated (M.det * Q.det) M.det := (associated_mul_isUnit_left_iff hQ).2 (Associated.refl _)
      have hv : IsUnit (P.det * ∏ j, (u j : R)) :=
        hP.mul (by rw [← Units.coe_prod]; exact Units.isUnit _)
      have hB : Associated (ϖ ^ s) (P.det * ∏ j, c j) := by
        rw [h2, mul_left_comm]
        exact associated_mul_unit_right _ _ hv
      rw [← h1] at hB
      exact hB.trans hA
    have h4 : Associated (ϖ ^ s) (ϖ ^ k) := h3.trans hdet
    exact le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h4.dvd)
      ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h4.symm.dvd)
  let P' := P * Matrix.diagonal fun j => (u j : R)
  have hP' : IsUnit P'.det := by
    simp only [P', Matrix.det_mul, Matrix.det_diagonal]
    exact hP.mul (by rw [← Units.coe_prod]; exact Units.isUnit _)
  have hMQ' : M * Q = P' * Matrix.diagonal d := by
    rw [hMQ, Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
    congr 2
    funext j
    rw [hu j, mul_comm]

  have hcard1 : Fintype.card {j // ¬IsUnit (c j)} = Fintype.card {i : Fin n // ¬i.1 < n - k} := by
    rw [Fintype.card_subtype, ← hs, hsk, Fintype.card_subtype_compl, Fintype.card_subtype,
      Fin.card_filter_val_lt, Fintype.card_fin]
    omega
  have hcard0 : Fintype.card {j // IsUnit (c j)} = Fintype.card {i : Fin n // i.1 < n - k} := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun j => IsUnit (c j))
    rw [Fintype.card_subtype, Fintype.card_subtype, Fin.card_filter_val_lt]
    rw [← hs, hsk, Finset.card_univ, Fintype.card_fin] at h
    omega
  let τ : Equiv.Perm (Fin n) :=
    Equiv.subtypeCongr (Fintype.equivOfCardEq hcard0) (Fintype.equivOfCardEq hcard1)
  have hτ : ∀ j, (τ j).1 < n - k ↔ IsUnit (c j) := by
    intro j
    by_cases h : IsUnit (c j)
    · have e1 : (Equiv.sumCompl fun x => IsUnit (c x)).symm j = Sum.inl ⟨j, h⟩ :=
        Equiv.sumCompl_symm_apply_of_pos (p := fun x => IsUnit (c x)) (a := j) h
      simp only [τ, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply, e1, Sum.map_inl,
        Equiv.sumCompl_apply_inl, h, iff_true]
      exact (Fintype.equivOfCardEq hcard0 ⟨j, h⟩).2
    · have e1 : (Equiv.sumCompl fun x => IsUnit (c x)).symm j = Sum.inr ⟨j, h⟩ :=
        Equiv.sumCompl_symm_apply_of_neg (p := fun x => IsUnit (c x)) (a := j) h
      simp only [τ, Equiv.subtypeCongr, Equiv.trans_apply, Equiv.sumCongr_apply, e1, Sum.map_inr,
        Equiv.sumCompl_apply_inr, h, iff_false]
      exact (Fintype.equivOfCardEq hcard1 ⟨j, h⟩).2
  have hsign : ∀ A : Matrix (Fin n) (Fin n) R, IsUnit A.det → IsUnit (A.submatrix id τ.symm).det := by
    intro A hA
    rw [Matrix.det_permute']
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ.symm) with h | h <;> simp [h, hA]
  refine ⟨P'.submatrix id τ.symm, Q.submatrix id τ.symm, hsign P' hP', hsign Q hQ, ?_⟩
  have h1 : M * Q.submatrix id τ.symm = (M * Q).submatrix id τ.symm := by
    ext i j; simp [Matrix.mul_apply]
  rw [h1, hMQ', ← Matrix.submatrix_mul_equiv P' (Matrix.diagonal d) id τ.symm τ.symm,
    Matrix.submatrix_diagonal_equiv]
  congr 2
  funext i
  have := hτ (τ.symm i)
  rw [Equiv.apply_symm_apply] at this
  simp only [Function.comp_apply, d]
  by_cases hi : i.1 < n - k
  · simp [hi, this.1 hi]
  · simp [hi, mt this.2 hi]

end GlobalTheory.SmithBetween
end

section

namespace GlobalTheory
namespace GenericCharBlock

open Matrix

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mul_rankOne (Q : Matrix ι ι K) (q a b : K) (hQ : Q * Q = q • Q) :
    (1 + a • Q) * (1 + b • Q) = 1 + (a + b + a * b * q) • Q := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, hQ, smul_smul, add_smul, smul_add]
  module

noncomputable def rankOneUnit (Q : Matrix ι ι K) (q μ : K) (hQ : Q * Q = q • Q)
    (hμ : 1 + μ * q ≠ 0) : GL ι K where
  val := 1 + μ • Q
  inv := 1 + (-μ / (1 + μ * q)) • Q
  val_inv := by
    rw [mul_rankOne Q q _ _ hQ]
    have : μ + -μ / (1 + μ * q) + μ * (-μ / (1 + μ * q)) * q = 0 := by
      field_simp; ring
    rw [this, zero_smul, add_zero]
  inv_val := by
    rw [mul_rankOne Q q _ _ hQ]
    have : -μ / (1 + μ * q) + μ + -μ / (1 + μ * q) * μ * q = 0 := by
      field_simp; ring
    rw [this, zero_smul, add_zero]

theorem rankOneUnit_val (Q : Matrix ι ι K) (q μ : K) (hQ : Q * Q = q • Q)
    (hμ : 1 + μ * q ≠ 0) : (rankOneUnit Q q μ hQ hμ).val = 1 + μ • Q := rfl

noncomputable def unip (Q : Matrix ι ι K) (h : Q * Q = 0) (y : K) : GL ι K :=
  rankOneUnit Q 0 y (by rw [h, zero_smul]) (by simp)

theorem unip_val (Q : Matrix ι ι K) (h : Q * Q = 0) (y : K) :
    (unip Q h y).val = 1 + y • Q := rfl

noncomputable def diagUnit (f : ι → K) (hf : ∀ a, f a ≠ 0) : GL ι K where
  val := diagonal f
  inv := diagonal fun a => (f a)⁻¹
  val_inv := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext a; exact mul_inv_cancel₀ (hf a)
  inv_val := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext a; exact inv_mul_cancel₀ (hf a)

theorem diagUnit_val (f : ι → K) (hf : ∀ a, f a ≠ 0) : (diagUnit f hf).val = diagonal f := rfl

theorem conj_one_add (B Bi X : Matrix ι ι K) (h : B * Bi = 1) (y : K) :
    B * (1 + y • X) * Bi = 1 + y • (B * X * Bi) := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, h, Matrix.mul_smul, Matrix.smul_mul]

theorem conj_mul_conj (B Bi X Y : Matrix ι ι K) (h : Bi * B = 1) :
    (B * X * Bi) * (B * Y * Bi) = B * (X * Y) * Bi := by
  calc (B * X * Bi) * (B * Y * Bi) = B * X * (Bi * B) * Y * Bi := by simp only [Matrix.mul_assoc]
    _ = B * (X * Y) * Bi := by rw [h, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem single_eq_smul (i j : ι) (x : K) : single i j x = x • single i j (1 : K) := by
  rw [smul_single, smul_eq_mul, mul_one]

theorem chi_trivial_of_scaled {A : Type} [CommGroup A] (H : Subgroup (GL ι K)) (χ : H →* A)
    (P : Matrix ι ι K) (hP : P * P = 0)
    (hmem : ∀ y : K, ∃ g : GL ι K, g ∈ H ∧ g.val = 1 + y • P)
    (s : GL ι K) (hs : s ∈ H) (l : K) (hl : l ≠ 1) (hsc : s.val * P = l • (P * s.val))
    (g : GL ι K) (hg : g ∈ H) (y : K) (hgy : g.val = 1 + y • P) : χ ⟨g, hg⟩ = 1 := by
  have hl' : l - 1 ≠ 0 := sub_ne_zero.mpr hl
  obtain ⟨g1, hg1, hv1⟩ := hmem (y / (l - 1))
  have hinv : s.val * (s⁻¹ : GL ι K).val = 1 := s.mul_inv
  have key : s * g1 * s⁻¹ = g1 * g := by
    ext1
    simp only [Units.val_mul]
    rw [hv1, hgy]
    have e1 : s.val * (1 + (y / (l - 1)) • P) * (s⁻¹ : GL ι K).val
        = 1 + (y / (l - 1) * l) • P := by
      rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hinv, Matrix.mul_smul, hsc,
        Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc, hinv, Matrix.mul_one, smul_smul]
    rw [e1, mul_rankOne P 0 _ _ (by rw [hP, zero_smul])]
    congr 2
    field_simp
    ring
  have e : (⟨s, hs⟩ * ⟨g1, hg1⟩ * (⟨s, hs⟩ : H)⁻¹ : H) = ⟨g1, hg1⟩ * ⟨g, hg⟩ := Subtype.ext key
  have h1 : χ ⟨g1, hg1⟩ = χ ⟨g1, hg1⟩ * χ ⟨g, hg⟩ := by
    calc χ ⟨g1, hg1⟩ = χ ⟨s, hs⟩ * χ ⟨g1, hg1⟩ * (χ ⟨s, hs⟩)⁻¹ := by
          rw [mul_comm (χ ⟨s, hs⟩), mul_inv_cancel_right]
      _ = χ (⟨s, hs⟩ * ⟨g1, hg1⟩ * (⟨s, hs⟩ : H)⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = χ (⟨g1, hg1⟩ * ⟨g, hg⟩) := by rw [e]
      _ = χ ⟨g1, hg1⟩ * χ ⟨g, hg⟩ := map_mul _ _ _
  exact (mul_eq_left.mp h1.symm)

end GenericCharBlock
end GlobalTheory
end

section

namespace GlobalTheory

open Matrix

theorem intSymm_posSemidef_real :
    ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℤ), B.IsSymm →
      (∀ v : Fin g → ℤ, 0 ≤ dotProduct v (B.mulVec v)) →
      (B.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  intro g B hB hQ
  set M : Matrix (Fin g) (Fin g) ℝ := B.map (Int.cast : ℤ → ℝ) with hM

  set f : (Fin g → ℝ) → ℝ := fun x => dotProduct x (M.mulVec x) with hf
  have hcont : Continuous f := by
    simp only [hf, dotProduct, mulVec]
    fun_prop
  have hscale : ∀ (c : ℝ) (x : Fin g → ℝ), f (c • x) = c ^ 2 * f x := by
    intro c x
    simp only [hf, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  have hint : ∀ v : Fin g → ℤ, f (fun i => (v i : ℝ)) = ((dotProduct v (B.mulVec v) : ℤ) : ℝ) := by
    intro v
    simp only [hf, hM, dotProduct, mulVec, Matrix.map_apply]
    push_cast
    rfl
  have hrat : ∀ q : Fin g → ℚ, 0 ≤ f (fun i => (q i : ℝ)) := by
    intro q
    set N : ℕ := ∏ i, (q i).den with hN
    have hNpos : 0 < N := Finset.prod_pos (fun i _ => (q i).den_pos)
    have hdvd : ∀ i, (q i).den ∣ N := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    let v : Fin g → ℤ := fun i => (q i).num * ((N / (q i).den : ℕ) : ℤ)
    have hv : (N : ℝ) • (fun i => (q i : ℝ)) = fun i => (v i : ℝ) := by
      funext i
      have hd : ((q i).den : ℝ) ≠ 0 := by exact_mod_cast (q i).den_nz
      simp only [Pi.smul_apply, smul_eq_mul, v, Int.cast_mul, Int.cast_natCast]
      rw [Nat.cast_div (hdvd i) hd, Rat.cast_def]
      field_simp
    have h1 := hscale (N : ℝ) (fun i => (q i : ℝ))
    rw [hv, hint] at h1
    have h2 : (0 : ℝ) ≤ ((dotProduct v (B.mulVec v) : ℤ) : ℝ) := by exact_mod_cast hQ v
    have h3 : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
    nlinarith
  have hdense : DenseRange (fun q : Fin g → ℚ => fun i => (q i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hall : ∀ x : Fin g → ℝ, 0 ≤ f x := by
    intro x
    have hclosed : IsClosed {x : Fin g → ℝ | 0 ≤ f x} := isClosed_le continuous_const hcont
    have hsub : Set.range (fun q : Fin g → ℚ => fun i => (q i : ℝ)) ⊆ {x | 0 ≤ f x} := by
      rintro _ ⟨q, rfl⟩
      exact hrat q
    have := hdense.closure_range ▸ (closure_minimal hsub hclosed)
    exact this (Set.mem_univ x)
  refine posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun x => ?_⟩
  · ext i j
    simp [hM, conjTranspose_apply, hB.apply i j]
  · simpa [hf] using hall x

end GlobalTheory
end

section

namespace GlobalTheory.SpanQuotientTensor

theorem span_mkQ_one_tmul {K D : Type} [Field K] [AddCommGroup D] [Module K D]
    (F : Type) [Field F] [Algebra K F] (N : Submodule F (TensorProduct K F D)) :
    Submodule.span F (Set.range (fun x : D => N.mkQ ((1 : F) ⊗ₜ[K] x))) = ⊤ := by
  rw [eq_top_iff]
  rintro q -
  obtain ⟨y, rfl⟩ := N.mkQ_surjective q
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    have h : (a ⊗ₜ[K] x : TensorProduct K F D) = a • ((1 : F) ⊗ₜ[K] x) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  | add y z hy hz =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hy hz

theorem main : (let d1 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [inst_5 : Algebra LL F] → (U →+* F) → Submodule F (TensorProduct LL F D) := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) ↦ ⨆ (c : U), LinearMap.range (LinearMap.baseChange F ((m : U → Module.End LL D) c) - (τ : U → F) c • LinearMap.id)); let d2 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [Algebra LL F] → (U →+* F) → Type := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) ↦ TensorProduct LL F D ⧸ d1 m F τ); let d3 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (m : U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [inst_5 : Algebra LL F] → (τ : U →+* F) → TensorProduct LL F D →ₗ[F] d2 m F τ := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) ↦ Submodule.mkQ (d1 m F τ)); let d4 : {LL U D : Type} → [inst : Field LL] → [inst_1 : Field U] → [inst_2 : AddCommGroup D] → [inst_3 : Module LL D] → (m : U →+* Module.End LL D) → (F : Type) → [inst_4 : Field F] → [inst_5 : Algebra LL F] → (τ : U →+* F) → D → d2 m F τ := @(fun {LL U D : Type} [Field LL] [Field U] [AddCommGroup D] [Module LL D] (m : U →+* Module.End LL D) (F : Type) [Field F] [Algebra LL F] (τ : U →+* F) (x : D) ↦ (d3 m F τ : TensorProduct LL F D → d2 m F τ) ((1 : F) ⊗ₜ[LL] x)); ∀ {LL U D : Type} [inst : Field LL] [inst_1 : Field U] [inst_2 : AddCommGroup D] [inst_3 : Module LL D] (m : U →+* Module.End LL D) (F : Type) [inst_4 : Field F] [inst_5 : Algebra LL F] (τ : U →+* F), Submodule.span F (Set.range (d4 m F τ)) = ⊤) := by
  intro d1 d2 d3 d4 LL U D _ _ _ _ m F _ _ τ
  exact span_mkQ_one_tmul F (d1 m F τ)

end GlobalTheory.SpanQuotientTensor
end

section

universe u_1 u_2

namespace GlobalTheory.NatMulIntegerMultiple

open NumberField

theorem exists_nat_mul_eq_integer {K : Type*} [Field K] [NumberField K] (k : K) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ a : 𝓞 K, (n : K) * k = algebraMap (𝓞 K) K a := by
  have halg : IsAlgebraic ℤ k :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic k)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg y
  · refine ⟨n, by rintro rfl; exact hy rfl, ⟨(n : K) * k, ?_⟩, rfl⟩
    have : (n : K) * k = (n : ℤ) • k := by rw [zsmul_eq_mul]; push_cast; rfl
    rw [this]; exact hint
  · refine ⟨n, by rintro rfl; exact hy rfl, ⟨(n : K) * k, ?_⟩, rfl⟩
    have : (n : K) * k = -((-(n : ℤ)) • k) := by rw [zsmul_eq_mul]; push_cast; ring
    rw [this]; exact hint.neg

theorem exists_nsmul_mem {K : Type*} {V : Type*} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (L : Submodule (𝓞 K) V) :
    ∀ x ∈ Submodule.span K (L : Set V), ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ L := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x h => exact ⟨1, one_ne_zero, by simpa using h⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨n, hn, hny⟩ := hy
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    rw [smul_add]
    have e1 : (m * n) • x = n • (m • x) := by rw [mul_nsmul]
    have e2 : (m * n) • y = m • (n • y) := by rw [mul_comm, mul_nsmul]
    rw [e1, e2]
    exact L.add_mem (L.nsmul_mem hmx n) (L.nsmul_mem hny m)
  | smul c x _ hx =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, a, ha⟩ := exists_nat_mul_eq_integer c
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    have : (m * n) • (c • x) = a • (n • x) := by
      calc (m * n) • (c • x) = ((m : K) * c) • (n • x) := by
            rw [← Nat.cast_smul_eq_nsmul K (m * n), ← Nat.cast_smul_eq_nsmul K n, smul_smul, smul_smul]
            push_cast; ring_nf
        _ = algebraMap (𝓞 K) K a • (n • x) := by rw [ha]
        _ = a • (n • x) := algebraMap_smul K a (n • x)
    rw [this]; exact L.smul_mem a hnx

theorem main : ∀ {K : Type u_1} {V : Type u_2} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
    [inst_3 : Module K V] [inst_4 : Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V] (L : Submodule (NumberField.RingOfIntegers K) V),
    ∀ x ∈ Submodule.span K (↑L : Set V), ∃ (n : ℕ), n ≠ (0 : ℕ) ∧ n • x ∈ L :=
  fun L => exists_nsmul_mem L

end GlobalTheory.NatMulIntegerMultiple
end
