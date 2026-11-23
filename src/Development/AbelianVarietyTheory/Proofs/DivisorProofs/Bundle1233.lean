module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle156

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory
namespace IdempotentUnimodular

theorem exists_factor {O : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {n : ℕ}
    (e : Matrix (Fin n) (Fin n) O) (he : e * e = e) :
    ∃ (s : ℕ) (F : Matrix (Fin n) (Fin s) O) (C : Matrix (Fin s) (Fin n) O),
      F * C = e ∧ C * F = 1 := by
  obtain ⟨s, b⟩ := Submodule.basisOfPid (Pi.basisFun O (Fin n)) (LinearMap.range (Matrix.toLin' e))
  refine ⟨s, LinearMap.toMatrix b (Pi.basisFun O (Fin n)) (LinearMap.range (Matrix.toLin' e)).subtype,
    LinearMap.toMatrix (Pi.basisFun O (Fin n)) b (Matrix.toLin' e).rangeRestrict, ?_, ?_⟩
  · rw [← LinearMap.toMatrix_comp]
    have : (LinearMap.range (Matrix.toLin' e)).subtype ∘ₗ (Matrix.toLin' e).rangeRestrict
        = Matrix.toLin' e := by
      ext x; simp
    rw [this, LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  · rw [← LinearMap.toMatrix_comp]
    have : (Matrix.toLin' e).rangeRestrict ∘ₗ (LinearMap.range (Matrix.toLin' e)).subtype
        = LinearMap.id := by
      apply LinearMap.ext
      rintro ⟨_, x, rfl⟩
      apply Subtype.ext
      simp [Matrix.mulVec_mulVec, he]
    rw [this, LinearMap.toMatrix_id]

theorem exists_basis {K : Type*} [Field K] (O : Subring K) [IsPrincipalIdealRing O]
    (σ : K →+* K) (hσ : ∀ x ∈ O, σ x ∈ O) {n : ℕ} (V : Submodule K (Fin n → K))
    (e : Matrix (Fin n) (Fin n) K) (hint : ∀ i j, e i j ∈ O) (h1 : ∀ x, e *ᵥ x ∈ V)
    (h2 : ∀ x ∈ V, e *ᵥ x = x) (h3 : ∀ x ∈ V, ∀ y, ∑ k, σ (x k) * (y - e *ᵥ y) k = 0) :
    ∃ (s : ℕ) (f : Module.Basis (Fin s) K V),
      (Matrix.of fun i j => ∑ k, σ ((f i : Fin n → K) k) * (f j : Fin n → K) k).det ∈ O ∧
      ∃ d ∈ O,
        (Matrix.of fun i j => ∑ k, σ ((f i : Fin n → K) k) * (f j : Fin n → K) k).det * d = 1 := by
  have hee : e * e = e := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
    exact h2 _ (h1 x)
  let e₀ : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨e i j, hint i j⟩
  have he₀ : e₀.map O.subtype = e := by ext i j; rfl
  have hee₀ : e₀ * e₀ = e₀ := by
    apply Matrix.map_injective (f := O.subtype) Subtype.val_injective
    show (e₀ * e₀).map O.subtype = e₀.map O.subtype
    rw [Matrix.map_mul, he₀, hee]
  obtain ⟨s, F₀, C₀, hFC₀, hCF₀⟩ := exists_factor e₀ hee₀
  let σ₀ : O →+* O := (σ.comp O.subtype).codRestrict O (fun x => hσ x x.2)
  set F := F₀.map O.subtype with hF
  set C := C₀.map O.subtype with hC
  have hFC : F * C = e := by rw [hF, hC, ← Matrix.map_mul, hFC₀, he₀]
  have hCF : C * F = 1 := by
    rw [hF, hC, ← Matrix.map_mul, hCF₀]; simp
  have heF : e * F = F := by rw [← hFC, Matrix.mul_assoc, hCF, Matrix.mul_one]
  have hmem : ∀ j, (fun k => F k j) ∈ V := by
    intro j
    have : (fun k => F k j) = e *ᵥ (fun k => F k j) := by
      funext k
      conv_lhs => rw [← heF]
      rfl
    rw [this]; exact h1 _
  have hmem' : ∀ y, F *ᵥ y ∈ V := by
    intro y
    rw [← heF, ← Matrix.mulVec_mulVec]; exact h1 _
  let φ : V ≃ₗ[K] (Fin s → K) := LinearEquiv.ofLinear (Matrix.toLin' C ∘ₗ V.subtype)
    ((Matrix.toLin' F).codRestrict V (fun y => hmem' y))
    (by
      apply LinearMap.ext
      intro y
      show C *ᵥ (F *ᵥ y) = y
      rw [Matrix.mulVec_mulVec, hCF, Matrix.one_mulVec])
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      show F *ᵥ (C *ᵥ (x : Fin n → K)) = x
      rw [Matrix.mulVec_mulVec, hFC, h2 _ x.2])
  have hb : ∀ i k, ((Module.Basis.ofEquivFun φ i : V) : Fin n → K) k = F k i := by
    intro i k
    rw [Module.Basis.coe_ofEquivFun]
    show (F *ᵥ (Pi.single i 1)) k = F k i
    simp
  refine ⟨s, Module.Basis.ofEquivFun φ, ?_⟩
  have hG : (Matrix.of fun i j => ∑ k, σ (((Module.Basis.ofEquivFun φ i : V) : Fin n → K) k) *
      ((Module.Basis.ofEquivFun φ j : V) : Fin n → K) k) = (F.map σ)ᵀ * F := by
    ext i j
    simp only [hb, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [hG]
  have hFe : (F.map σ)ᵀ * e = (F.map σ)ᵀ := by
    ext i j
    have := h3 _ (hmem i) (Pi.single j 1)
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, Matrix.mulVec_single_one,
      sub_eq_zero] at this
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    rw [Finset.sum_eq_single j (by intro b _ hb; simp [hb]) (by simp)] at this
    simpa using this.symm
  have hinv : ((F.map σ)ᵀ * F) * (C * (C.map σ)ᵀ) = 1 := by
    rw [← Matrix.mul_assoc, Matrix.mul_assoc _ F, hFC, hFe, ← Matrix.transpose_mul,
      ← Matrix.map_mul, hCF]
    simp
  have hA : (F.map σ)ᵀ * F = ((F₀.map σ₀)ᵀ * F₀).map O.subtype := by
    rw [Matrix.map_mul]; rfl
  have hB : C * (C.map σ)ᵀ = (C₀ * (C₀.map σ₀)ᵀ).map O.subtype := by
    rw [Matrix.map_mul]; rfl
  refine ⟨?_, (C * (C.map σ)ᵀ).det, ?_, ?_⟩
  · rw [hA, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact Subtype.property _
  · rw [hB, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact Subtype.property _
  · rw [← Matrix.det_mul, hinv, Matrix.det_one]

theorem main : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (σ : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (V : Submodule (w.adicCompletion E) (Fin n → w.adicCompletion E))
    (e : Matrix (Fin n) (Fin n) (w.adicCompletion E)), (∀ i j, Valued.v (e i j) ≤ 1) → (∀ x, e *ᵥ x ∈ V) →
    (∀ x ∈ V, e *ᵥ x = x) → (∀ x ∈ V, ∀ y, ∑ k, σ (x k) * (y - e *ᵥ y) k = 0) →
    ∃ (s : ℕ) (f : Module.Basis (Fin s) (w.adicCompletion E) V),
      Valued.v (Matrix.of fun i j => ∑ k, σ ((f i : Fin n → w.adicCompletion E) k) * (f j : Fin n → w.adicCompletion E) k).det = 1 := by
  intro E _ _ w σ _ hv n V e hint h1 h2 h3
  haveI : IsPrincipalIdealRing (w.adicCompletionIntegers E).toSubring :=
    inferInstanceAs (IsPrincipalIdealRing (w.adicCompletionIntegers E))
  have hO : ∀ x, x ∈ (w.adicCompletionIntegers E).toSubring ↔ Valued.v x ≤ 1 := fun x => Iff.rfl
  obtain ⟨s, f, hd, d, hd', hdd⟩ := exists_basis (w.adicCompletionIntegers E).toSubring σ
    (fun x hx => by rw [hO] at hx ⊢; rwa [hv]) V e (fun i j => (hO _).2 (hint i j)) h1 h2 h3
  refine ⟨s, f, ?_⟩
  rw [hO] at hd hd'
  have h := congrArg Valued.v hdd
  rw [map_mul, map_one] at h
  refine le_antisymm hd ?_
  rw [← h]
  exact mul_le_of_le_one_right' hd'

end IdempotentUnimodular
end GlobalTheory
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.GlobHerm

theorem vandermonde_diag_herm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (l : Fin n → ℂ) (hl : Function.Injective l)
    (h1 : ∀ k, ‖l k‖ = 1) (hVA : vandermonde l * A = diagonal l * vandermonde l) :
    A.det ≠ 0 ∧ (Matrix.of fun i j : Fin n => trace (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ))) = (vandermonde l)ᴴ * vandermonde l ∧
      ((vandermonde l)ᴴ * vandermonde l).det ≠ 0 ∧
      Aᴴ * ((vandermonde l)ᴴ * vandermonde l) * A = (vandermonde l)ᴴ * vandermonde l := by
  set V := vandermonde l with hV
  have hl0 : ∀ k, l k ≠ 0 := fun k h => by simpa [h] using h1 k
  have hVd : V.det ≠ 0 := det_vandermonde_ne_zero_iff.2 hl
  have hconj : ∀ k, starRingEnd ℂ (l k) = (l k)⁻¹ := by
    intro k
    rw [Complex.inv_def, Complex.normSq_eq_norm_sq, h1 k]; simp
  have hAd : A.det ≠ 0 := by
    have := congrArg Matrix.det hVA
    rw [det_mul, det_mul, det_diagonal, mul_comm] at this
    have h2 : A.det = ∏ k, l k := mul_right_cancel₀ hVd this
    rw [h2]; exact Finset.prod_ne_zero_iff.2 fun k _ => hl0 k
  set D' := diagonal fun k => (l k)⁻¹
  have hDD : D' * diagonal l = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext k; exact inv_mul_cancel₀ (hl0 k)
  have hAinv : A * A⁻¹ = 1 := mul_nonsing_inv A (isUnit_iff_ne_zero.2 hAd)
  have hVAi : V * A⁻¹ = D' * V := by
    calc V * A⁻¹ = D' * diagonal l * V * A⁻¹ := by rw [hDD, one_mul]
      _ = D' * (V * A) * A⁻¹ := by rw [hVA, mul_assoc D']
      _ = D' * V := by rw [mul_assoc, mul_assoc, hAinv, mul_one]
  have hpow : ∀ j : ℕ, V * A ^ j = diagonal l ^ j * V := by
    intro j; induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hVA, ← mul_assoc, ← pow_succ]
  have hpowi : ∀ j : ℕ, V * A⁻¹ ^ j = D' ^ j * V := by
    intro j; induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, hVAi, ← mul_assoc, ← pow_succ]
  have hVinv : V⁻¹ * V = 1 := nonsing_inv_mul V (isUnit_iff_ne_zero.2 hVd)
  have hVinv' : V * V⁻¹ = 1 := mul_nonsing_inv V (isUnit_iff_ne_zero.2 hVd)
  refine ⟨hAd, ?_, ?_, ?_⟩
  · ext i j
    have hM : V * (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)) = (D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) * V := by
      rw [← mul_assoc, hpowi, mul_assoc, hpow, ← mul_assoc]
    have htr : trace (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)) = trace (D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) := by
      calc trace (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)) = trace (V⁻¹ * (V * (A⁻¹ ^ (i : ℕ) * A ^ (j : ℕ)))) := by
            rw [← mul_assoc, hVinv, one_mul]
        _ = trace (V⁻¹ * ((D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) * V)) := by rw [hM]
        _ = trace (D' ^ (i : ℕ) * diagonal l ^ (j : ℕ)) := by
            rw [trace_mul_comm, mul_assoc, hVinv', mul_one]
    rw [of_apply, htr, diagonal_pow, diagonal_pow, diagonal_mul_diagonal, trace_diagonal, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [V, D', vandermonde_apply, conjTranspose_apply, hconj, inv_pow]
  · rw [det_mul, det_conjTranspose]
    exact mul_ne_zero (by simpa using hVd) hVd
  · calc Aᴴ * (Vᴴ * V) * A = (V * A)ᴴ * (V * A) := by
          rw [conjTranspose_mul]; simp only [mul_assoc]
      _ = Vᴴ * ((diagonal l)ᴴ * diagonal l) * V := by
          rw [hVA, conjTranspose_mul]; simp only [mul_assoc]
      _ = Vᴴ * V := by
          rw [diagonal_conjTranspose, diagonal_mul_diagonal]
          have : (diagonal fun k => star (l k) * l k) = 1 := by
            rw [← diagonal_one]; congr 1; funext k
            show starRingEnd ℂ (l k) * l k = 1
            rw [hconj, inv_mul_cancel₀ (hl0 k)]
          simp only [Pi.star_apply] at this ⊢
          rw [this, mul_one]

end GlobalTheory.GlobHerm

namespace GlobalTheory.GlobHerm

theorem exists_mat_herm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n →
    ∃ C H : Matrix (Fin n) (Fin n) E, C.charpoly = P ∧ C.det ≠ 0 ∧ H.det ≠ 0 ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H ∧
      cT (IsCMField.complexConj E).toRingEquiv.toRingHom C * H * C = H := by
  intro E _ _ _ n P hP
  obtain ⟨hmon, hdeg, hsep, hroot⟩ := hP
  subst hdeg
  have hP0 : P ≠ 0 := hmon.ne_zero
  let pb := AdjoinRoot.powerBasis hP0
  let Cm : Matrix (Fin P.natDegree) (Fin P.natDegree) E := Algebra.leftMulMatrix pb.basis pb.gen
  let H : Matrix (Fin P.natDegree) (Fin P.natDegree) E :=
    Matrix.of fun i j => trace (Cm⁻¹ ^ (i : ℕ) * Cm ^ (j : ℕ))
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hτc : ∀ x, τ ((IsCMField.complexConj E).toRingEquiv.toRingHom x) = starRingEnd ℂ (τ x) :=
    fun x => IsCMField.complexEmbedding_complexConj E τ x
  have hQsep : (P.map τ).Separable := hsep.map
  have hQcard : (P.map τ).roots.card = P.natDegree := by
    rw [splits_iff_card_roots.1 (IsAlgClosed.splits _), natDegree_map]
  have hs : (P.map τ).roots.toFinset.card = P.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hQsep), hQcard]
  let e : (P.map τ).roots.toFinset ≃ Fin P.natDegree := Fintype.equivFinOfCardEq (by simp [hs])
  let l : Fin P.natDegree → ℂ := fun k => (e.symm k : ℂ)
  have hl : Function.Injective l := Subtype.val_injective.comp e.symm.injective
  have hlr : ∀ k, eval₂ τ (l k) P = 0 := by
    intro k
    have := (e.symm k).2
    rw [Multiset.mem_toFinset, mem_roots hQsep.ne_zero, IsRoot, eval_map] at this
    exact this
  have h1 : ∀ k, ‖l k‖ = 1 := fun k => hroot τ _ (Multiset.mem_toFinset.1 (e.symm k).2)
  have hrep : ∀ k (x : AdjoinRoot P),
      ∑ i : Fin pb.dim, l k ^ (i : ℕ) * τ (pb.basis.repr x i) = AdjoinRoot.lift τ (l k) (hlr k) x := by
    intro k x
    conv_rhs => rw [← pb.basis.sum_repr x]

    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, PowerBasis.coe_basis]
    simp only [pb, AdjoinRoot.powerBasis_gen, map_pow, AdjoinRoot.lift_root, AdjoinRoot.algebraMap_eq,
      AdjoinRoot.lift_of]
    ring
  have hVA : vandermonde l * Cm.map τ = diagonal l * vandermonde l := by
    ext k j
    rw [Matrix.mul_apply, diagonal_mul, vandermonde_apply]
    show ∑ i : Fin pb.dim, l k ^ (i : ℕ) * τ (Algebra.leftMulMatrix pb.basis pb.gen i j) = l k * l k ^ (j : ℕ)
    have hC : ∀ i : Fin pb.dim, Algebra.leftMulMatrix pb.basis pb.gen i j = pb.basis.repr (pb.gen * pb.basis j) i :=
      fun i => Algebra.leftMulMatrix_eq_repr_mul _ _ _ _
    rw [Finset.sum_congr rfl fun i _ => by rw [hC i], hrep k]
    simp only [pb, PowerBasis.coe_basis, AdjoinRoot.powerBasis_gen]
    rw [← pow_succ', map_pow, AdjoinRoot.lift_root, pow_succ']
  obtain ⟨hAd, hH, hHd, hpres⟩ := GlobalTheory.GlobHerm.vandermonde_diag_herm (Cm.map τ) l hl h1 hVA
  have hinv : (Cm.map τ)⁻¹ = Cm⁻¹.map τ := by
    apply inv_eq_left_inv
    have hCd : Cm.det ≠ 0 := by
      intro h; apply hAd
      have := RingHom.map_det τ Cm
      rw [h, map_zero] at this
      exact this.symm
    rw [← Matrix.map_mul, nonsing_inv_mul Cm (isUnit_iff_ne_zero.2 hCd), Matrix.map_one _ (map_zero τ) (map_one τ)]
  have hHm : H.map τ = (vandermonde l)ᴴ * vandermonde l := by
    rw [← hH]
    ext i j
    simp only [map_apply, of_apply, H]
    rw [AddMonoidHom.map_trace τ, hinv]
    congr 1
    change τ.mapMatrix _ = _
    rw [map_mul, map_pow, map_pow]
    rfl
  have hinj : Function.Injective (fun M : Matrix (Fin P.natDegree) (Fin P.natDegree) E => M.map τ) :=
    Matrix.map_injective τ.injective
  have hcT : ∀ M : Matrix (Fin P.natDegree) (Fin P.natDegree) E,
      (cT (IsCMField.complexConj E).toRingEquiv.toRingHom M).map τ = (M.map τ)ᴴ := by
    intro M; ext i j
    simp only [cT, map_apply, transpose_apply, conjTranspose_apply, hτc]
    rfl
  refine ⟨Cm, H, ?_, ?_, ?_, ?_, ?_⟩
  · refine (charpoly_leftMulMatrix pb).trans ?_
    rw [AdjoinRoot.powerBasis_gen, AdjoinRoot.minpoly_root hP0, hmon.leadingCoeff, inv_one,
      Polynomial.C_1, mul_one]
  · intro h; apply hAd
    have := RingHom.map_det τ Cm
    rw [h, map_zero] at this
    exact this.symm
  · intro h; apply hHd
    have := RingHom.map_det τ H
    rw [h, map_zero] at this
    rw [← hHm]; exact this.symm
  · apply hinj
    simp only
    rw [hcT, hHm, conjTranspose_mul, conjTranspose_conjTranspose]
  · apply hinj
    simp only
    rw [Matrix.map_mul, Matrix.map_mul, hcT, hHm, hpres]
end GlobalTheory.GlobHerm
end

section

open GlobalTheory.BCT

namespace GlobalTheory.ConjRegroup

theorem finsum_fibres {H C : Type} (p : H → C) (a : H → ℂ) (ha : (Function.support a).Finite) :
    ∑ᶠ γ, a γ = ∑ᶠ c : C, ∑ᶠ x, Set.indicator {x | p x = c} a x := by
  classical
  have h1 : ∀ c : C, ∑ᶠ x, Set.indicator {x | p x = c} a x
      = ∑ x ∈ ha.toFinset, if c = p x then a x else 0 := by
    intro c
    rw [finsum_eq_sum_of_support_subset (s := ha.toFinset)]
    · refine Finset.sum_congr rfl fun x _ => ?_
      simp [Set.indicator_apply, eq_comm]
    · intro x hx
      have : a x ≠ 0 := fun h => hx (by simp [Set.indicator_apply, h])
      simpa using this
  simp_rw [h1]
  rw [finsum_sum_comm]
  · rw [finsum_eq_sum a ha]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [finsum_eq_single _ (p x)]
    · simp
    · intro c hc
      simp [hc]
  · intro x _
    refine (Set.finite_singleton (p x)).subset ?_
    intro c hc
    by_contra h
    exact hc (if_neg h)

theorem mk_eq_iff {H : Type} [Group H] (x y : H) :
    (Quot.mk _ x : TwCl (MonoidHom.id H)) = Quot.mk _ y ↔ ∃ g, y = g⁻¹ * x * g := by
  have he : Equivalence fun x y : H => ∃ g, y = g⁻¹ * x * (MonoidHom.id H) g := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp [mul_assoc]⟩
    · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
      exact ⟨g * h, by simp [mul_assoc]⟩
  exact Quot.eq.trans he.eqvGen_iff

theorem conj_injective {H : Type} [Group H] (r : H) :
    Function.Injective fun δ : H ⧸ twCent (MonoidHom.id H) r =>
      Quotient.out δ * r * (Quotient.out δ)⁻¹ := by
  intro δ ε h
  rw [← QuotientGroup.out_eq' δ, ← QuotientGroup.out_eq' ε, QuotientGroup.eq]
  change (Quotient.out δ)⁻¹ * Quotient.out ε * r = r * ((Quotient.out δ)⁻¹ * Quotient.out ε)
  simp only at h
  calc (Quotient.out δ)⁻¹ * Quotient.out ε * r
      = (Quotient.out δ)⁻¹ * (Quotient.out ε * r * (Quotient.out ε)⁻¹) * Quotient.out ε := by group
    _ = r * ((Quotient.out δ)⁻¹ * Quotient.out ε) := by rw [← h]; group

theorem range_conj {H : Type} [Group H] (c : TwCl (MonoidHom.id H)) :
    Set.range (fun δ : H ⧸ twCent (MonoidHom.id H) c.rep =>
      Quotient.out δ * c.rep * (Quotient.out δ)⁻¹)
      = {x | (Quot.mk _ x : TwCl (MonoidHom.id H)) = c} := by
  have hc : (Quot.mk _ c.rep : TwCl (MonoidHom.id H)) = c := Quot.out_eq c
  ext x
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨δ, rfl⟩
    refine Eq.trans ?_ hc
    rw [mk_eq_iff]
    exact ⟨Quotient.out δ, by group⟩
  · intro h
    obtain ⟨g, hg⟩ := (mk_eq_iff x c.rep).1 (h.trans hc.symm)
    refine ⟨QuotientGroup.mk g, ?_⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (twCent (MonoidHom.id H) c.rep) g
    have hk2 : (k : H) * c.rep = c.rep * k := k.2
    rw [hk]
    calc g * k * c.rep * (g * k)⁻¹ = g * (k * c.rep) * (g * k)⁻¹ := by group
      _ = g * c.rep * g⁻¹ := by rw [hk2]; group
      _ = x := by rw [hg]; group

theorem finsum_eq_finsum_classes {H : Type} [Group H] (a : H → ℂ) (ha : (Function.support a).Finite) :
    ∑ᶠ γ, a γ = ∑ᶠ c : TwCl (MonoidHom.id H), ∑ᶠ δ : H ⧸ twCent (MonoidHom.id H) c.rep,
      a (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) := by
  rw [finsum_fibres (fun x => (Quot.mk _ x : TwCl (MonoidHom.id H))) a ha]
  refine finsum_congr fun c => ?_
  rw [← finsum_mem_def, ← range_conj c, finsum_mem_range (conj_injective (TwCl.rep c))]

end GlobalTheory.ConjRegroup
end

section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

namespace GlobalTheory.OrbIndUnit

theorem avg_const_fun {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hs : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [rStab]
  unfold avg
  rw [hs, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := uniqueOfSubsingleton (1 : H ⧸ (⊤ : Subgroup H))
  rw [finsum_unique]
  simp

theorem twOrb_id_indicator (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (γ : G) :
    twOrb (MonoidHom.id G) K γ ((K : Set G).indicator 1) = ∑ᶠ q : DoubleCoset.Quotient (twCent (MonoidHom.id G) γ : Set G) (K : Set G), if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then (((twCent (MonoidHom.id G) γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) γ)) : ℕ) : ℂ) else 0 := by
  unfold twOrb
  apply finsum_congr
  intro q
  set Q : G := Quotient.out q with hQ
  have hfun : (fun k : K => (K : Set G).indicator 1 ((Q * k)⁻¹ * γ * (MonoidHom.id G) (Q * k)))
      = fun _ => (K : Set G).indicator (1 : G → ℂ) (Q⁻¹ * γ * Q) := by
    funext k
    have he : (Q * k)⁻¹ * γ * (MonoidHom.id G) (Q * k) = (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k := by
      simp only [MonoidHom.id_apply]; group
    rw [he]
    by_cases h : Q⁻¹ * γ * Q ∈ K
    · have h' : (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k ∈ K := K.mul_mem (K.mul_mem (K.inv_mem k.2) h) k.2
      simp [Set.indicator_apply, h, h']
    · have h' : (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k ∉ K := by
        intro h'
        apply h
        have := K.mul_mem (K.mul_mem k.2 h') (K.inv_mem k.2)
        simpa [mul_assoc] using this
      simp [Set.indicator_apply, h, h']
  rw [hfun, avg_const_fun]
  by_cases h : Q⁻¹ * γ * Q ∈ K
  · simp [Set.indicator_apply, h]
  · simp [Set.indicator_apply, h]

end GlobalTheory.OrbIndUnit
end

end

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter Formalism.UG GlobalTheory.BCT
open scoped Classical

theorem _root_.GlobalTheory.T.exists_matrix_charpoly_preserving_hermitian_form_CM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : E[X]), P ∈ Ell E n → ∃ C H : Matrix (Fin n) (Fin n) E, C.charpoly = P ∧ C.det ≠ 0 ∧ H.det ≠ 0 ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom H = H ∧ cT (IsCMField.complexConj E).toRingEquiv.toRingHom C * H * C = H := by
  first | exact @GlobalTheory.GlobHerm.exists_mat_herm | exact GlobalTheory.GlobHerm.exists_mat_herm | (intros; apply GlobalTheory.GlobHerm.exists_mat_herm <;> assumption)

end
end

section

@[expose] public section

open GlobalTheory.BCT

theorem _root_.GlobalTheory.T.finsum_eq_finsum_conjugacyClasses_centraliserCosets : ∀ {H : Type} [Group H] (a : H → ℂ), (Function.support a).Finite → ∑ᶠ γ, a γ = ∑ᶠ c : TwCl (MonoidHom.id H), ∑ᶠ δ : H ⧸ twCent (MonoidHom.id H) c.rep, a (Quotient.out δ * c.rep * (Quotient.out δ)⁻¹) := by
  first | exact @GlobalTheory.ConjRegroup.finsum_eq_finsum_classes | exact GlobalTheory.ConjRegroup.finsum_eq_finsum_classes | (intros; apply GlobalTheory.ConjRegroup.finsum_eq_finsum_classes <;> assumption)

end
end

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.GlobalTheory.T.orthogonal_projection_integral_adic : ∀ (E : Type) [Field E] [NumberField E] (w : Pl E) (σ : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (V : Submodule (w.adicCompletion E) (Fin n → w.adicCompletion E))
    (e : Matrix (Fin n) (Fin n) (w.adicCompletion E)), (∀ i j, Valued.v (e i j) ≤ 1) → (∀ x, e *ᵥ x ∈ V) →
    (∀ x ∈ V, e *ᵥ x = x) → (∀ x ∈ V, ∀ y, ∑ k, σ (x k) * (y - e *ᵥ y) k = 0) →
    ∃ (s : ℕ) (f : Module.Basis (Fin s) (w.adicCompletion E) V),
      Valued.v (Matrix.of fun i j => ∑ k, σ ((f i : Fin n → w.adicCompletion E) k) * (f j : Fin n → w.adicCompletion E) k).det = 1 := by
  first | exact @GlobalTheory.IdempotentUnimodular.main | exact GlobalTheory.IdempotentUnimodular.main | (intros; apply GlobalTheory.IdempotentUnimodular.main <;> assumption)

end
end

section

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

theorem _root_.GlobalTheory.T.orbitalIntegral_indicator_eq_finsum_relIndex : ∀ (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (γ : G), twOrb (MonoidHom.id G) K γ ((K : Set G).indicator 1) = ∑ᶠ q : DoubleCoset.Quotient (twCent (MonoidHom.id G) γ : Set G) (K : Set G), if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then (((twCent (MonoidHom.id G) γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) γ)) : ℕ) : ℂ) else 0 := by
  first | exact @GlobalTheory.OrbIndUnit.twOrb_id_indicator | exact GlobalTheory.OrbIndUnit.twOrb_id_indicator | (intros; apply GlobalTheory.OrbIndUnit.twOrb_id_indicator <;> assumption)

end
end
