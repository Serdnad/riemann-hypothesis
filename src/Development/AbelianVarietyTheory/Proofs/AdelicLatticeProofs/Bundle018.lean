module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle003
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_orthogonal_mul_upper (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ) :
    ∃ (k r : Matrix (Fin N) (Fin N) ℝ), kᵀ * k = 1 ∧ (∀ i j, j < i → r i j = 0) ∧ g = k * r := by
  classical
  let f : Fin N → EuclideanSpace ℝ (Fin N) := fun j => WithLp.toLp 2 (fun i => g i j)
  have h : Module.finrank ℝ (EuclideanSpace ℝ (Fin N)) = Fintype.card (Fin N) := by simp
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis h f
  refine ⟨Matrix.of fun i j => b j i, Matrix.of fun i j => inner ℝ (b i) (f j), ?_, ?_, ?_⟩
  · ext i j
    have := orthonormal_iff_ite.mp b.orthonormal i j
    rw [Matrix.mul_apply, Matrix.one_apply, ← this, PiLp.inner_apply]
    simp [mul_comm]
  · intro i j hij
    exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular h f hij
  · ext i j
    have := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v i) (b.sum_repr' (f j))
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    calc g i j = f j i := rfl
      _ = _ := this.symm
      _ = _ := Finset.sum_congr rfl fun x _ => mul_comm _ _

theorem iwasawa_real : ∀ (N : ℕ) (g : Matrix (Fin N) (Fin N) ℝ), g.det ≠ 0 → ∃ (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), kᵀ * k = 1 ∧ (∀ i, 0 < a i) ∧ (∀ i, n i i = 1) ∧ (∀ i j, j < i → n i j = 0) ∧ g = k * diagonal a * n := by
  intro N g hg
  obtain ⟨k, r, hk, hr, rfl⟩ := exists_orthogonal_mul_upper N g
  have hbt : r.BlockTriangular id := fun i j hij => hr i j hij
  have hdet : r.det ≠ 0 := by
    intro h0
    apply hg
    rw [Matrix.det_mul, h0, mul_zero]
  rw [Matrix.det_of_isUpperTriangular hbt, Finset.prod_ne_zero_iff] at hdet
  have hne : ∀ i, r i i ≠ 0 := fun i => hdet i (Finset.mem_univ i)
  have habs : ∀ i, |r i i| ≠ 0 := fun i => abs_ne_zero.mpr (hne i)
  refine ⟨k * diagonal (fun i => r i i / |r i i|), fun i => |r i i|,
    Matrix.of fun i j => r i j / r i i, ?_, fun i => abs_pos.mpr (hne i), ?_, ?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc kᵀ, hk,
      Matrix.one_mul, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [div_mul_div_comm, abs_mul_abs_self, div_self (mul_ne_zero (hne i) (hne i))]
  · intro i
    exact div_self (hne i)
  · intro i j hij
    simp [hr i j hij]
  · rw [Matrix.mul_assoc, Matrix.mul_assoc]
    congr 1
    ext i j
    rw [Matrix.diagonal_mul, Matrix.diagonal_mul, Matrix.of_apply]
    have h1 := hne i
    have h2 := habs i
    field_simp

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem det_leading_gram_iwasawa : ∀ (N : ℕ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), kᵀ * k = 1 → (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → ∀ (j : ℕ) (h : j ≤ N), (((k * diagonal a * n)ᵀ * (k * diagonal a * n)).submatrix (Fin.castLE h) (Fin.castLE h)).det = ∏ i : Fin j, a (Fin.castLE h i) ^ 2 := by
  intro N k a n hk hd hn j h
  have h1 : (k * diagonal a * n)ᵀ * (k * diagonal a * n)
      = nᵀ * diagonal (fun i => a i ^ 2) * n := by
    have : diagonal (fun i => a i ^ 2) = diagonal a * diagonal a := by
      rw [diagonal_mul_diagonal]; simp [sq]
    rw [this, transpose_mul, transpose_mul, diagonal_transpose]
    calc nᵀ * (diagonal a * kᵀ) * (k * diagonal a * n)
        = nᵀ * (diagonal a * (kᵀ * k) * diagonal a) * n := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hk, Matrix.mul_one]
  have h2 : (nᵀ * diagonal (fun i => a i ^ 2) * n).submatrix (Fin.castLE h) (Fin.castLE h)
      = (n.submatrix (Fin.castLE h) (Fin.castLE h))ᵀ
        * diagonal (fun i : Fin j => a (Fin.castLE h i) ^ 2)
        * n.submatrix (Fin.castLE h) (Fin.castLE h) := by
    ext p q
    rw [submatrix_apply, Matrix.mul_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ ?_
    · intro r hr
      have hr' : j ≤ r.val := by
        by_contra hlt
        exact hr ⟨⟨r.val, not_le.mp hlt⟩, Fin.ext rfl⟩
      have : n r (Fin.castLE h q) = 0 := hn _ _ (by
        rw [Fin.lt_def]; have := q.2; simp; omega)
      rw [this, mul_zero]
    · intro r
      simp [Matrix.mul_diagonal]
  have h3 : (n.submatrix (Fin.castLE h) (Fin.castLE h)).det = 1 := by
    rw [det_of_isUpperTriangular]
    · simp [hd]
    · intro p q hpq
      exact hn _ _ (by
        have h' : q < p := hpq
        exact h')
  rw [h1, h2, det_mul, det_mul, det_transpose, h3, det_diagonal]
  simp

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_algHom_algebraicClosure_ker_le (K A : Type) [Field K] [CommRing A] [Algebra K A]
    [Algebra.FiniteType K A] (m : Ideal A) [m.IsMaximal] :
    ∃ φ : A →ₐ[K] AlgebraicClosure K, ∀ x, φ x = 0 → x ∈ m := by
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite K (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ m)
  let ι : (A ⧸ m) →ₐ[K] AlgebraicClosure K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨ι.comp (Ideal.Quotient.mkₐ K m), fun x hx => ?_⟩
  have h : ι (Ideal.Quotient.mk m x) = 0 := hx
  have h2 : Ideal.Quotient.mk m x = 0 := ι.toRingHom.injective (by simpa using h)
  exact Ideal.Quotient.eq_zero_iff_mem.mp h2

theorem mem_range_algebraMap_of_isNilpotent_tmul_sub (K A : Type) [Field K] [CharZero K]
    [CommRing A] [Algebra K A] [Algebra.FiniteType K A] [IsReduced A] (f : A)
    (hf : IsNilpotent (f ⊗ₜ[K] (1 : A) - (1 : A) ⊗ₜ[K] f)) : f ∈ (algebraMap K A).range := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, Subsingleton.elim _ _⟩
  have h1 : ∀ φ ψ : A →ₐ[K] AlgebraicClosure K, φ f = ψ f := by
    intro φ ψ
    have h := (hf.map (Algebra.TensorProduct.productMap φ ψ)).eq_zero
    simpa [sub_eq_zero] using h
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal A
  obtain ⟨φ₀, -⟩ := exists_algHom_algebraicClosure_ker_le K A m₀
  have h2 : φ₀ f ∈ Set.range (algebraMap K (AlgebraicClosure K)) := by
    rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
    intro σ
    exact h1 (σ.toAlgHom.comp φ₀) φ₀
  obtain ⟨c, hc⟩ := h2
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := K)
  refine ⟨c, ?_⟩
  have h3 : f - algebraMap K A c ∈ (⊥ : Ideal A).jacobson := by
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro m ⟨-, hm⟩
    obtain ⟨φ, hφ⟩ := exists_algHom_algebraicClosure_ker_le K A m
    apply hφ
    rw [map_sub, AlgHom.commutes, hc, h1 φ φ₀, sub_self]
  have h4 : (⊥ : Ideal A).jacobson = ⊥ :=
    IsJacobsonRing.out inferInstance (Ideal.isRadical_bot)
  rw [h4, Ideal.mem_bot, sub_eq_zero] at h3
  exact h3.symm

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem two_pow_card_le_index_iInf :
    ∀ (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G),
      (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) → (⨅ i, K i).index ≠ 0 →
        2 ^ Fintype.card ι ≤ (⨅ i, K i).index := by
  intro G ι _ _ K h hidx
  classical
  choose x hx hx' using h
  have key : ∀ (A : Finset ι) (j : ι), (∏ i ∈ A, x i) ∈ K j ↔ j ∉ A := by
    intro A j
    constructor
    · intro hm hj
      rw [← Finset.mul_prod_erase A x hj] at hm
      have h2 : (∏ i ∈ A.erase j, x i) ∈ K j :=
        Subgroup.prod_mem _ fun i hi => hx' i j (Finset.ne_of_mem_erase hi).symm
      exact hx j ((Subgroup.mul_mem_cancel_right _ h2).1 hm)
    · intro hj
      exact Subgroup.prod_mem _ fun i hi => hx' i j (fun e => hj (e ▸ hi))
  haveI : Finite (G ⧸ ⨅ i, K i) := Nat.finite_of_card_ne_zero hidx
  have inj : Function.Injective
      (fun A : Finset ι => ((∏ i ∈ A, x i : G) : G ⧸ ⨅ i, K i)) := by
    intro A B hAB
    have hm : (∏ i ∈ A, x i)⁻¹ * (∏ i ∈ B, x i) ∈ ⨅ i, K i := QuotientGroup.eq.1 hAB
    ext j
    have hj : (∏ i ∈ A, x i)⁻¹ * (∏ i ∈ B, x i) ∈ K j := (Subgroup.mem_iInf.1 hm) j
    have hiff : (∏ i ∈ A, x i) ∈ K j ↔ (∏ i ∈ B, x i) ∈ K j := by
      constructor
      · intro ha
        exact (Subgroup.mul_mem_cancel_left _ (inv_mem ha)).1 hj
      · intro hb
        exact inv_mem_iff.1 ((Subgroup.mul_mem_cancel_right _ hb).1 hj)
    rw [key, key] at hiff
    exact not_iff_not.1 hiff
  have := Nat.card_le_card_of_injective _ inj
  rwa [Nat.card_eq_fintype_card, Fintype.card_finset] at this

end GlobalTheory.QNorm
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem repr_algebraMap_of_basis_image (F β : Type) [Field F] [Algebra ℚ F] [Fintype β]
    (ω : Module.Basis β ℚ F) (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A]
    [Algebra F A] (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (x : F) (k : β) :
    b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k) := by
  have hq : ∀ q : ℚ, algebraMap F A (algebraMap ℚ F q) = algebraMap R A (algebraMap ℚ R q) := by
    intro q
    have h : (algebraMap F A).comp (algebraMap ℚ F) = (algebraMap R A).comp (algebraMap ℚ R) :=
      RingHom.ext_rat _ _
    exact RingHom.congr_fun h q
  have hx : algebraMap F A x = ∑ j, algebraMap ℚ R (ω.repr x j) • b j := by
    conv_lhs => rw [← ω.sum_repr x]

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_mul, hq, hb, Algebra.smul_def]
  rw [hx, b.repr_sum_self]

theorem coords_const_baseChange : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ x : F, (∀ k, b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k)) ∧ Algebra.leftMulMatrix b (algebraMap F A x) = (Algebra.leftMulMatrix ω x).map (algebraMap ℚ R) := by
  intro F β _ _ _ _ ω R A _ _ _ _ _ b hb x
  refine ⟨repr_algebraMap_of_basis_image F β ω R A b hb x, ?_⟩
  ext i j
  rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    hb j, ← map_mul, repr_algebraMap_of_basis_image F β ω R A b hb]

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.finite_places_over (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) = v}.Finite := by
  refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 E)).preimage
    (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
  rintro w rfl
  exact ⟨w.isPrime, ⟨rfl⟩⟩


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.places_over : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], (∀ S : Finset (HeightOneSpectrum (𝓞 F)), ∃ SE : Finset (HeightOneSpectrum (𝓞 E)), ∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) ∧ (∀ v : HeightOneSpectrum (𝓞 F), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v) ∧ ∀ (w : HeightOneSpectrum (𝓞 E)), ∃ e : ℕ, 0 < e ∧ ∀ x : F, w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x ^ e := by
  intro F E _ _ _ _ _
  refine ⟨fun S => ?_, fun v => ?_, fun w => ?_⟩
  · have hfin : {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ S}.Finite := by
      have hU : {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) ∈ S} =
          ⋃ v ∈ S, {w : HeightOneSpectrum (𝓞 E) | w.under (𝓞 F) = v} := by
        ext w; simp
      rw [hU]
      exact S.finite_toSet.biUnion fun v _ => _root_.GlobalTheory.QNorm.finite_places_over F E v
    exact ⟨hfin.toFinset, fun w => by simp⟩
  · obtain ⟨P, hmax, hover⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral v.asIdeal (S := 𝓞 E)
    have hne : P ≠ ⊥ := by
      rintro rfl
      apply v.ne_bot
      rw [hover.over]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
    exact ⟨⟨P, hmax.isPrime, hne⟩, HeightOneSpectrum.ext hover.over.symm⟩
  · haveI : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
    refine ⟨(w.under (𝓞 F)).asIdeal.ramificationIdx' w.asIdeal, Nat.pos_of_ne_zero ?_,
      fun x => ?_⟩
    · refine Ideal.IsDedekindDomain.ramificationIdx'_ne_zero ?_ w.isPrime Ideal.map_comap_le
      rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))]
      exact (w.under (𝓞 F)).ne_bot
    · rw [Ideal.ramificationIdx'_eq_ramificationIdx
        (w.under (𝓞 F)).asIdeal w.asIdeal (w.under (𝓞 F)).ne_bot]
      exact (HeightOneSpectrum.valuation_liesOver E (w.under (𝓞 F)) w x).symm

end GlobalTheory.QNorm
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem prod_absNorm_pow_le_two_pow :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (e : HeightOneSpectrum (𝓞 F) → ℕ), (∀ v ∈ S, v.valuation F 2 = WithZero.exp (-(e v : ℤ))) → ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v ≤ 2 ^ Module.finrank ℚ F := by
  intro F _ _ S e h
  have hdvd : ∀ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(2 : 𝓞 F)} := by
    intro v hv
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_dvd]
    have h2 : v.valuation F (algebraMap (𝓞 F) F 2) = v.intValuation 2 :=
      HeightOneSpectrum.valuation_of_algebraMap v 2
    rw [map_ofNat, h v hv] at h2
    exact h2.ge
  have hprod : ∏ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(2 : 𝓞 F)} := by
    refine Finset.prod_dvd_of_coprime ?_ hdvd
    intro v _ w _ hvw
    refine IsCoprime.pow ?_
    rw [Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal
      (fun hh => hvw (HeightOneSpectrum.ext hh))
  have hn : Ideal.absNorm (Ideal.span {(2 : 𝓞 F)}) = 2 ^ Module.finrank ℚ F := by
    rw [Ideal.absNorm_span_singleton]
    have : (2 : 𝓞 F) = algebraMap ℤ (𝓞 F) 2 := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp [Int.natAbs_pow]
  have h3 := map_dvd Ideal.absNorm hprod
  rw [hn, map_prod] at h3
  simp only [map_pow] at h3
  exact Nat.le_of_dvd (by positivity) h3

end GlobalTheory.QNorm
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem card_ringHom_real_eq_nrRealPlaces :
    ∀ (F : Type) [Field F] [NumberField F], Nat.card (F →+* ℝ) = InfinitePlace.nrRealPlaces F := by
  intro F _ _
  let e : (F →+* ℝ) ≃ {φ : F →+* ℂ // ComplexEmbedding.IsReal φ} :=
    { toFun := fun ψ => ⟨Complex.ofRealHom.comp ψ, by
        rw [ComplexEmbedding.isReal_iff]
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq]⟩
      invFun := fun φ => φ.2.embedding
      left_inv := fun ψ => by
        ext x
        simp [ComplexEmbedding.IsReal.embedding]
      right_inv := fun φ => by
        apply Subtype.ext
        ext x
        simp }
  classical
  rw [Nat.card_congr (e.trans InfinitePlace.mkReal), Nat.card_eq_fintype_card]

end GlobalTheory.QNorm
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.exists_approx_mod_squares :
    ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) (z : (F →+* ℝ) → ℝ), (∀ v, y v ≠ 0) → (∀ σ, z σ ≠ 0) → ∃ x : F, x ≠ 0 ∧ (∀ v ∈ S, IsSquare (algebraMap F (v.adicCompletion F) x * y v)) ∧ ∀ σ : F →+* ℝ, 0 < σ x * z σ := by
  intro F _ _ S y z hy hz
  set U : Set ((∀ v : S, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) × ((F →+* ℝ) → ℝ)) :=
    (⋂ v : S, {p | ‖p.1 v * y v - 1‖ < min ‖(4 : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)‖ 1}) ∩
      ⋂ σ, {p | 0 < p.2 σ * z σ} with hUdef
  have hU : IsOpen U := by
    refine IsOpen.inter (isOpen_iInter_of_finite fun v => ?_) (isOpen_iInter_of_finite fun σ => ?_)
    · exact isOpen_lt
        ((((continuous_apply v).comp continuous_fst).mul continuous_const).sub continuous_const).norm
        continuous_const
    · exact isOpen_lt continuous_const (((continuous_apply σ).comp continuous_snd).mul continuous_const)
  have hne : U.Nonempty := by
    refine ⟨(fun v => (y v)⁻¹, z), ?_⟩
    simp only [hUdef, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    refine ⟨fun v => ?_, fun σ => mul_self_pos.2 (hz σ)⟩
    rw [inv_mul_cancel₀ (hy v), sub_self, norm_zero, lt_min_iff]
    have h4 := (map_ne_zero (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))).2
      (by norm_num : (4 : F) ≠ 0)
    rw [map_ofNat] at h4
    exact ⟨norm_pos_iff.2 h4, one_pos⟩
  obtain ⟨x, hx⟩ := (_root_.GlobalTheory.LocalQuad.denseRange_finite_real F S).exists_mem_open hU hne
  simp only [hUdef, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq] at hx
  obtain ⟨hxS, hxR⟩ := hx
  by_cases hx0 : x = 0
  · subst hx0
    refine ⟨1, one_ne_zero, fun v hv => ?_, fun σ => ?_⟩
    · have h := hxS ⟨v, hv⟩
      simp at h
    · have h := hxR σ
      simp at h
  refine ⟨x, hx0, fun v hv => ?_, hxR⟩
  have h := (hxS ⟨v, hv⟩).trans_le (min_le_left _ _)
  exact _root_.GlobalTheory.LocalQuad.isSquare_of_valued_sub_one_lt F v _ (Valued.toNormedField.norm_lt_iff.1 h)

end GlobalTheory.QNorm
end
