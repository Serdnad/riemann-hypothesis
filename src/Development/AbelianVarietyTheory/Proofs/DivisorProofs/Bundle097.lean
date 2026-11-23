module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Prime
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
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

section

open Module Submodule

namespace GlobalTheory

theorem extend_linearIndependent_rows_by_standard_basis
    {K : Type} [Field K] {J : Type} [Fintype J] {n : ℕ} (v : J → Fin n → K) :
    LinearIndependent K v → ∃ e : J → Fin n, Function.Injective e ∧
      (Matrix.of (Function.extend e v (fun i => Pi.single i (1 : K)))).det ≠ 0 := by
  intro hv
  set std : Fin n → (Fin n → K) := fun i => Pi.single i (1 : K) with hstd
  set W : Submodule K (Fin n → K) := span K (Set.range v) with hWdef
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K (W.mkQ ∘ std)
  classical
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hW : finrank K W = Fintype.card J := finrank_span_eq_card hv
  have hQ := Submodule.finrank_quotient_add_finrank W
  have hfin : finrank K (Fin n → K) = n := Module.finrank_fin_fun K
  have hκ : Fintype.card κ ≤ finrank K ((Fin n → K) ⧸ W) := hli.fintype_card_le_finrank

  let C := {i : Fin n // i ∉ Set.range a}
  have hC : Fintype.card C = n - Fintype.card κ := by
    have h1 : Fintype.card C = Fintype.card (Fin n) - Fintype.card (Set.range a) := by
      simp only [C]
      rw [Fintype.card_subtype_compl]
    rw [h1, Fintype.card_fin, Set.card_range_of_injective ha]
  have hJC : Fintype.card J ≤ Fintype.card C := by omega
  obtain ⟨φ⟩ := Function.Embedding.nonempty_of_card_le hJC
  let e : J → Fin n := fun j => (φ j).1
  have he : Function.Injective e := fun x y h => φ.injective (Subtype.ext h)
  have heC : ∀ j, e j ∉ Set.range a := fun j => (φ j).2
  refine ⟨e, he, ?_⟩
  set f := Function.extend e v std with hf
  have hfe : ∀ j, f (e j) = v j := fun j => he.extend_apply v std j
  have hfa : ∀ k, f (a k) = std (a k) := by
    intro k
    apply Function.extend_apply'
    rintro ⟨j, hj⟩
    exact heC j ⟨k, hj.symm⟩

  have hstdspan : span K (Set.range std) = ⊤ := by
    have := (Pi.basisFun K (Fin n)).span_eq
    convert this using 2
    ext i
    simp [std, Pi.basisFun_apply]
  have hspanf : span K (Set.range f) = ⊤ := by
    have hWle : W ≤ span K (Set.range f) := by
      apply span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact subset_span ⟨e j, hfe j⟩
    have hAle : span K (Set.range (std ∘ a)) ≤ span K (Set.range f) := by
      apply span_le.mpr
      rintro _ ⟨k, rfl⟩
      exact subset_span ⟨a k, hfa k⟩
    have htop : W ⊔ span K (Set.range (std ∘ a)) = ⊤ := by
      rw [← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
      have : (W.mkQ ∘ std ∘ a) = (W.mkQ ∘ std) ∘ a := rfl
      rw [← Function.comp_assoc] at *
      rw [hspan, Set.range_comp, ← Submodule.map_span, hstdspan, Submodule.map_top, LinearMap.range_eq_top]
      exact W.mkQ_surjective
    exact eq_top_iff.mpr (htop ▸ sup_le hWle hAle)
  have hlin : LinearIndependent K f := by
    rw [linearIndependent_iff_card_eq_finrank_span, Set.finrank, hspanf, finrank_top, hfin,
      Fintype.card_fin]
  have hunit : IsUnit (Matrix.of f) := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    exact hlin
  exact (Matrix.isUnit_iff_isUnit_det _).mp hunit |>.ne_zero

end GlobalTheory
end

section

namespace GlobalTheory.Div.BlockChangeDet

open Matrix

theorem det_blockDiagonal'_eq_prod {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R]
    {κ : ι → Type} [∀ c, Fintype (κ c)] [∀ c, DecidableEq (κ c)]
    (M : ∀ c, Matrix (κ c) (κ c) R) :
    (Matrix.blockDiagonal' M).det = ∏ c, (M c).det := by
  classical
  set f := Fintype.equivFin ι
  let b : (Σ c, κ c) → Fin (Fintype.card ι) := fun p => f p.1
  have hb : (Matrix.blockDiagonal' M).BlockTriangular b := by
    rintro ⟨c, i⟩ ⟨c', j⟩ h
    exact Matrix.blockDiagonal'_apply_ne M i j (fun hc => by subst hc; exact lt_irrefl _ h)
  rw [hb.det_fintype]
  symm
  refine Fintype.prod_equiv f _ _ (fun c => ?_)
  let e : κ c ≃ {p : (Σ c, κ c) // b p = f c} :=
    { toFun := fun i => ⟨⟨c, i⟩, rfl⟩
      invFun := fun p => cast (congrArg κ (f.injective p.2)) p.1.2
      left_inv := fun i => rfl
      right_inv := by
        rintro ⟨⟨c', i⟩, h⟩
        have hc : c' = c := f.injective h
        subst hc
        rfl }
  rw [← Matrix.det_submatrix_equiv_self e]
  congr 1
  ext i j
  exact (Matrix.blockDiagonal'_apply_eq M c i j).symm

theorem det_block_change (F : Type) [Field F] {N : Type} [AddCommGroup N] [Module F N]
    {κ : Type} [Fintype κ]
    (m : κ → ℕ) {n : ℕ} (e : (Σ b, Fin (m b)) ≃ Fin n) (ℓ : (Σ b, Fin (m b)) → N)
    (hℓ : ∀ x : N, ∃! a : (Σ b, Fin (m b)) → F, x = ∑ k, a k • ℓ k) (nu mu : Fin n → N)
    (U A : Matrix (Fin n) (Fin n) F) (C : (Σ b, Fin (m b)) → Fin n → F)
    (g : ∀ b, Matrix (Fin (m b)) (Fin (m b)) F)
    (hU : ∀ σ, ℓ σ = ∑ k, U (e σ) k • nu k) (hA : ∀ k, mu k = ∑ l, A k l • nu l)
    (hg : ∀ b i, ∑ j, g b i j • ℓ ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k) :
    U.det ≠ 0 ∧ (∏ b, (g b).det) * U.det = (Matrix.of fun i k => C (e.symm i) k).det * A.det := by
  classical

  have hli : LinearIndependent F ℓ := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have h0 : (0 : N) = ∑ k, (0 : (Σ b, Fin (m b)) → F) k • ℓ k := by simp
    have := (hℓ 0).unique ha.symm h0
    intro i
    exact congrFun this i
  have hsp : ⊤ ≤ Submodule.span F (Set.range ℓ) := by
    intro x _
    obtain ⟨a, ha, -⟩ := hℓ x
    rw [ha]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  have hfr : Module.finrank F N = n := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp), Fintype.card_congr e, Fintype.card_fin]
  have hspnu : ⊤ ≤ Submodule.span F (Set.range nu) := by
    refine le_trans hsp (Submodule.span_le.mpr ?_)
    rintro _ ⟨σ, rfl⟩
    rw [hU σ]
    exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))
  have hlinu : LinearIndependent F nu :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspnu (by simp [hfr])
  have uniq : ∀ a c : Fin n → F, ∑ k, a k • nu k = ∑ k, c k • nu k → a = c := by
    intro a c h
    have := Fintype.linearIndependent_iff.mp hlinu (a - c)
      (by simp [sub_smul, Finset.sum_sub_distrib, h])
    funext k
    exact sub_eq_zero.mp (this k)

  have hdet : U.det ≠ 0 := by
    have hrows : LinearIndependent F (fun i => U i) := by
      rw [Fintype.linearIndependent_iff]
      intro a ha
      have hli' : LinearIndependent F (ℓ ∘ e.symm) := hli.comp e.symm e.symm.injective
      refine Fintype.linearIndependent_iff.mp hli' a ?_
      have hcol : ∀ k, ∑ i, a i * U i k = 0 := by
        intro k
        have := congrFun ha k
        simpa [Finset.sum_apply] using this
      calc ∑ i, a i • (ℓ ∘ e.symm) i
          = ∑ i, a i • ∑ k, U i k • nu k := by
            refine Finset.sum_congr rfl (fun i _ => ?_)
            simp [Function.comp, hU]
        _ = ∑ k, (∑ i, a i * U i k) • nu k := by
            simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
            exact Finset.sum_comm
        _ = 0 := by simp [hcol]
    have hu := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
    exact (Matrix.isUnit_iff_isUnit_det U |>.mp hu).ne_zero
  refine ⟨hdet, ?_⟩

  have hent : ∀ σ k, ∑ τ, blockDiagonal' g σ τ * U (e τ) k = ∑ l, C σ l * A l k := by
    rintro ⟨b, i⟩
    have h1 : ∑ τ, blockDiagonal' g ⟨b, i⟩ τ • ℓ τ = ∑ j, g b i j • ℓ ⟨b, j⟩ := by
      rw [Fintype.sum_sigma]
      rw [Finset.sum_eq_single b]
      · refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [blockDiagonal'_apply_eq]
      · intro b' _ hb'
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [blockDiagonal'_apply_ne g i j (Ne.symm hb'), zero_smul]
      · intro h; exact absurd (Finset.mem_univ b) h
    have h2 : ∑ k, (∑ τ, blockDiagonal' g ⟨b, i⟩ τ * U (e τ) k) • nu k
        = ∑ τ, blockDiagonal' g ⟨b, i⟩ τ • ℓ τ := by
      simp only [hU, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have h3 : ∑ k, (∑ l, C ⟨b, i⟩ l * A l k) • nu k = ∑ l, C ⟨b, i⟩ l • mu l := by
      simp only [hA, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have := uniq (fun k => ∑ τ, blockDiagonal' g ⟨b, i⟩ τ * U (e τ) k)
      (fun k => ∑ l, C ⟨b, i⟩ l * A l k) (by rw [h2, h1, hg b i, ← h3])
    intro k
    exact congrFun this k
  have key : Matrix.reindex e e (blockDiagonal' g) * U
      = (Matrix.of fun i k => C (e.symm i) k) * A := by
    ext i k
    simp only [Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.of_apply]
    rw [← hent (e.symm i) k]
    exact Fintype.sum_equiv e.symm _ _ (fun x => by simp)
  have := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self, det_blockDiagonal'_eq_prod] at this
  exact this

theorem det_block_change' : ∀ {F : Type} [Field F] {N : Type} [AddCommGroup N] [Module F N] {κ : Type} [Fintype κ]
    (m : κ → ℕ) {n : ℕ} (e : (Σ b, Fin (m b)) ≃ Fin n) (ℓ : (Σ b, Fin (m b)) → N),
    (∀ x : N, ∃! a : (Σ b, Fin (m b)) → F, x = ∑ k, a k • ℓ k) → ∀ (nu mu : Fin n → N)
    (U A : Matrix (Fin n) (Fin n) F) (C : (Σ b, Fin (m b)) → Fin n → F)
    (g : ∀ b, Matrix (Fin (m b)) (Fin (m b)) F),
    (∀ σ, ℓ σ = ∑ k, U (e σ) k • nu k) → (∀ k, mu k = ∑ l, A k l • nu l) →
    (∀ b i, ∑ j, g b i j • ℓ ⟨b, j⟩ = ∑ k, C ⟨b, i⟩ k • mu k) →
    U.det ≠ 0 ∧ (∏ b, (g b).det) * U.det = (Matrix.of fun i k => C (e.symm i) k).det * A.det := by
  intro F _ N _ _ κ _ m n e ℓ hℓ nu mu U A C g hU hA hg
  exact det_block_change F m e ℓ hℓ nu mu U A C g hU hA hg

end GlobalTheory.Div.BlockChangeDet
end

section

open Matrix Polynomial

theorem GlobalTheory.gram_det_ne_zero_of_ker_orth {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {ι : Type} [Fintype ι] [DecidableEq ι] (u : ι → Fin n → K) (hli : LinearIndependent K u) (hsp : Submodule.span K (Set.range u) = LinearMap.ker (Matrix.toLin' A)) (horth : ∀ x z, A *ᵥ x = 0 → ∑ k, σ ((A *ᵥ z) k) * x k = 0) (hdec : ∀ v, ∃ z y, A *ᵥ y = 0 ∧ v = A *ᵥ z + y) : (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det ≠ 0 := by
  intro hdet
  obtain ⟨c, hc0, hGc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set x : Fin n → K := ∑ j, c j • u j with hxdef
  have hx0 : x ≠ 0 := by
    intro hx
    apply hc0
    funext j
    exact Fintype.linearIndependent_iff.mp hli c hx j
  have hxspan : x ∈ Submodule.span K (Set.range u) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hAx : A *ᵥ x = 0 := by
    rw [hsp, LinearMap.mem_ker, Matrix.toLin'_apply] at hxspan
    exact hxspan
  have hu : ∀ i, ∑ k, σ (u i k) * x k = 0 := by
    intro i
    have := congrFun hGc i
    rw [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.of_apply, Pi.zero_apply] at this
    rw [← this]
    simp only [hxdef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hy : ∀ y ∈ LinearMap.ker (Matrix.toLin' A), ∑ k, σ (y k) * x k = 0 := by
    intro y hy
    rw [← hsp] at hy
    obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy

    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ i, ∑ k, σ (d i) * σ (u i k) * x k = σ (d i) * ∑ k, σ (u i k) * x k := by
      intro i; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    simp [this, hu]
  have hall : ∀ v : Fin n → K, ∑ k, σ (v k) * x k = 0 := by
    intro v
    obtain ⟨z, y, hAy, rfl⟩ := hdec v
    have h1 := horth x z hAx
    have h2 := hy y (by rw [LinearMap.mem_ker, Matrix.toLin'_apply]; exact hAy)
    simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib, h1, h2, add_zero]
  apply hx0
  funext k
  have := hall (Pi.single k 1)
  simpa [Pi.single_apply] using this
end

section

namespace GlobalTheory.MatrixRangeExistence

theorem exists_matrix_range_eq {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (n : ℕ) (ϖ : O) (N : Submodule O (Fin n → O)) (hϖ : ϖ ≠ 0)
    (hN : ∀ y : Fin n → O, (fun a : Fin n => ϖ * y a) ∈ N) :
    ∃ A : Matrix (Fin n) (Fin n) O,
      (∀ x : Fin n → O, x ∈ N ↔ ∃ u : Fin n → O, Matrix.mulVec A u = x) ∧ Matrix.det A ≠ 0 := by
  classical
  let f : (Fin n → O) →ₗ[O] N :=
    LinearMap.codRestrict N (ϖ • LinearMap.id) (fun y => hN y)
  have hf : Function.Injective f := by
    intro y z h
    have h' : ϖ • y = ϖ • z := congrArg Subtype.val h
    funext a
    exact mul_left_cancel₀ hϖ (congrFun h' a)
  have h1 : n ≤ Module.finrank O N := by
    have := LinearMap.finrank_le_finrank_of_injective hf
    simpa using this
  have h2 : Module.finrank O N ≤ n := by
    have := Submodule.finrank_le N
    simpa using this
  let b : Module.Basis (Fin n) O N := Module.finBasisOfFinrankEq O N (le_antisymm h2 h1)
  let A : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => (b j : Fin n → O) i
  have hA : ∀ u : Fin n → O, Matrix.mulVec A u = ((∑ j, u j • b j : N) : Fin n → O) := by
    intro u
    funext i
    simp [A, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have key : ∀ x : Fin n → O, x ∈ N ↔ ∃ u : Fin n → O, Matrix.mulVec A u = x := by
    intro x
    constructor
    · intro hx
      refine ⟨fun j => b.repr ⟨x, hx⟩ j, ?_⟩
      rw [hA, b.sum_repr ⟨x, hx⟩]
    · rintro ⟨u, rfl⟩
      rw [hA]
      exact Subtype.property _
  refine ⟨A, key, ?_⟩
  have hcol : ∀ j : Fin n, ∃ u : Fin n → O,
      Matrix.mulVec A u = fun a => ϖ * (Pi.single j (1 : O) : Fin n → O) a :=
    fun j => (key _).1 (hN _)
  choose U hU using hcol
  have hmul : A * (Matrix.of fun i j => U j i) = ϖ • (1 : Matrix (Fin n) (Fin n) O) := by
    ext i j
    have := congrFun (hU j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp [Matrix.mul_apply, this, Matrix.one_apply, Pi.single_apply]
  intro h0
  have := congrArg Matrix.det hmul
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ hϖ this.symm

end GlobalTheory.MatrixRangeExistence
end

section

namespace GlobalTheory

theorem exists_injective_rows_leadingMinors_not_mem (R : Type) [CommRing R] (p : Ideal R) :
    ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) R), T.det ∉ p →
    ∃ f : Fin n → Fin n, Function.Injective f ∧ ∀ (k : ℕ) (hk : k ≤ n),
      (Matrix.of fun a b : Fin k => T (f (Fin.castLE hk a)) (Fin.castLE hk b)).det ∉ p := by
  intro n
  induction n with
  | zero =>
    intro T hT
    refine ⟨id, Function.injective_id, fun k hk => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.mp hk
    have h1 : T.det = 1 := Matrix.det_isEmpty
    rw [Matrix.det_isEmpty]
    rwa [h1] at hT
  | succ n ih =>
    intro T hT
    have hsum := T.det_succ_column (Fin.last n)
    obtain ⟨i, hi⟩ : ∃ i : Fin (n+1), (-1) ^ ((i : ℕ) + (Fin.last n : ℕ)) * T i (Fin.last n) *
        (T.submatrix i.succAbove (Fin.last n).succAbove).det ∉ p := by
      by_contra h
      push_neg at h
      exact hT (hsum ▸ p.sum_mem fun i _ => h i)
    have hM : (T.submatrix i.succAbove Fin.castSucc).det ∉ p := by
      intro hm
      apply hi
      rw [Fin.succAbove_last]
      exact p.mul_mem_left _ hm
    obtain ⟨g, hg, hmin⟩ := ih _ hM
    set f : Fin (n+1) → Fin (n+1) := Fin.lastCases i (fun j => i.succAbove (g j))
    have hf : Function.Injective f := by
      intro a b hab
      induction a using Fin.lastCases with
      | last =>
        induction b using Fin.lastCases with
        | last => rfl
        | cast b =>
          simp only [f, Fin.lastCases_last, Fin.lastCases_castSucc] at hab
          exact absurd hab.symm (Fin.succAbove_ne i _)
      | cast a =>
        induction b using Fin.lastCases with
        | last =>
          simp only [f, Fin.lastCases_last, Fin.lastCases_castSucc] at hab
          exact absurd hab (Fin.succAbove_ne i _)
        | cast b =>
          simp only [f, Fin.lastCases_castSucc] at hab
          rw [hg (Fin.succAbove_right_injective hab)]
    refine ⟨f, hf, ?_⟩
    intro k hk
    rcases Nat.lt_or_ge k (n+1) with hlt | hge
    · have hk' : k ≤ n := Nat.lt_succ_iff.mp hlt
      have hmat : (Matrix.of fun a b : Fin k => T (f (Fin.castLE hk a)) (Fin.castLE hk b)) =
          Matrix.of fun a b : Fin k => (T.submatrix i.succAbove Fin.castSucc)
            (g (Fin.castLE hk' a)) (Fin.castLE hk' b) := by
        ext a b
        have e1 : (Fin.castLE hk a : Fin (n+1)) = Fin.castSucc (Fin.castLE hk' a) := Fin.ext rfl
        have e2 : (Fin.castLE hk b : Fin (n+1)) = Fin.castSucc (Fin.castLE hk' b) := Fin.ext rfl
        rw [Matrix.of_apply, Matrix.of_apply, e1, e2]
        simp only [f, Fin.lastCases_castSucc, Matrix.submatrix_apply]
      rw [hmat]
      exact hmin k hk'
    · obtain rfl : k = n + 1 := le_antisymm hk hge
      let σ : Equiv.Perm (Fin (n+1)) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
      have hmat : (Matrix.of fun a b : Fin (n+1) => T (f (Fin.castLE hk a)) (Fin.castLE hk b)) =
          T.submatrix σ id := by
        ext a b
        have e1 : Fin.castLE hk a = a := Fin.ext rfl
        have e2 : Fin.castLE hk b = b := Fin.ext rfl
        simp [σ, e1, e2]
      rw [hmat, Matrix.det_permute]
      intro hm
      apply hT
      have hs : T.det = ((Equiv.Perm.sign σ : ℤ) : R) * (((Equiv.Perm.sign σ : ℤ) : R) * T.det) := by
        rw [← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
        simp
      rw [hs]
      exact p.mul_mem_left _ hm

theorem exists_rowPerm_leadingMinors_not_mem : ∀ (R : Type) [CommRing R] (n : ℕ)
    (T : Matrix (Fin n) (Fin n) R) (p : Ideal R), p.IsPrime → T.det ∉ p →
    ∃ w : Equiv.Perm (Fin n), ∀ (k : ℕ) (hk : k ≤ n),
      ((T.submatrix w id).submatrix (Fin.castLE hk) (Fin.castLE hk)).det ∉ p := by
  intro R _ n T p _ hT
  obtain ⟨f, hf, h⟩ := exists_injective_rows_leadingMinors_not_mem R p n T hT
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), fun k hk => h k hk⟩

end GlobalTheory
end
