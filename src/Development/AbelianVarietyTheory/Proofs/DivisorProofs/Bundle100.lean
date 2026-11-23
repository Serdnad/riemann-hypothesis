module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.MeasureTheory.Group.Defs
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section

section

open ValuativeRel Matrix

namespace GlobalTheory

theorem rank_frame_exists :
    ∀ (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
      (X : Matrix A D K), ∃ (H : Matrix (Fin X.rank) A K) (Q : Matrix D (Fin X.rank) K),
        H * X * Q = 1 := by
  intro K _ A D _ _ _ _ X
  classical
  let V := LinearMap.range X.mulVecLin
  let b : Module.Basis (Fin X.rank) K V := by
    simpa only [V, Matrix.finrank_range_mulVecLin] using (Module.finBasis K V)
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := V) b.equivFun.toLinearMap
  have hpre : ∀ i, ∃ v : D → K, X *ᵥ v = ((b i : V) : A → K) := fun i => by
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (b i).2
    exact ⟨v, hv⟩
  choose q hq using hpre
  refine ⟨LinearMap.toMatrix' g, Matrix.of fun d i => q i d, ?_⟩
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one,
    Matrix.one_mulVec]
  have hcol : (Matrix.of fun d i => q i d).col j = q j := by
    ext d; simp [Matrix.col]
  rw [hcol, hq j, LinearMap.toMatrix'_mulVec]
  have := congrArg (fun f => f (b j)) hg
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    LinearEquiv.coe_coe] at this
  rw [this]
  ext k
  rw [Module.Basis.equivFun_self]
  simp [Pi.single_apply, Finsupp.single_apply, eq_comm]

end GlobalTheory
end

section

open Matrix

namespace GlobalTheory.IdemRankLocal

theorem exists_conj_diag (W : Type) [CommRing W] [IsLocalRing W] (n : ℕ)
    (p : Matrix (Fin n) (Fin n) W) (hp : p * p = p) :
    ∃ (r : ℕ) (P P' : Matrix (Fin n) (Fin n) W), P * P' = 1 ∧
    p = P * Matrix.diagonal (fun i : Fin n => if i.val < r then (1 : W) else 0) * P' := by
  classical
  set f : (Fin n → W) →ₗ[W] (Fin n → W) := Matrix.toLin' p with hfdef
  have hf : IsIdempotentElem f := by
    show f * f = f
    rw [Module.End.mul_eq_comp, hfdef, ← Matrix.toLin'_mul, hp]
  have hc := LinearMap.IsIdempotentElem.isCompl hf
  haveI : Module.Projective W (LinearMap.range f) :=
    Module.Projective.of_split (LinearMap.range f).subtype
      (Submodule.linearProjOfIsCompl _ _ hc)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left hc x)
  haveI : Module.Projective W (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype
      (Submodule.linearProjOfIsCompl _ _ hc.symm)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left hc.symm x)
  haveI : Module.Finite W (LinearMap.range f) :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl _ _ hc)
      (Submodule.linearProjOfIsCompl_surjective hc)
  haveI : Module.Finite W (LinearMap.ker f) :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl _ _ hc.symm)
      (Submodule.linearProjOfIsCompl_surjective hc.symm)
  haveI : Module.Free W (LinearMap.range f) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Free W (LinearMap.ker f) := Module.free_of_flat_of_isLocalRing
  set r := Module.finrank W (LinearMap.range f)
  set s := Module.finrank W (LinearMap.ker f)
  let b1 := Module.finBasis W (LinearMap.range f)
  let b2 := Module.finBasis W (LinearMap.ker f)
  let bs : Module.Basis (Fin r ⊕ Fin s) W (Fin n → W) :=
    (b1.prod b2).map (Submodule.prodEquivOfIsCompl _ _ hc)
  have hrs : r + s = n := by
    have := Module.finrank_eq_card_basis bs
    simpa [Fintype.card_sum] using this.symm
  have hbs1 : ∀ i, f (bs (Sum.inl i)) = bs (Sum.inl i) := by
    intro i
    simp only [bs, Module.Basis.map_apply, Module.Basis.prod_apply]
    simp
    obtain ⟨y, hy⟩ := (b1 i).2
    rw [← hy]
    exact LinearMap.congr_fun hf y
  have hbs2 : ∀ i, f (bs (Sum.inr i)) = 0 := by
    intro i
    simp only [bs, Module.Basis.map_apply, Module.Basis.prod_apply]
    simp
  let b : Module.Basis (Fin n) W (Fin n → W) := bs.reindex (finSumFinEquiv.trans (finCongr hrs))
  have hb : ∀ j : Fin n, f (b j) = (if j.val < r then (1 : W) else 0) • b j := by
    intro j
    have hj : b j = bs ((finSumFinEquiv.trans (finCongr hrs)).symm j) := Module.Basis.reindex_apply _ _ _
    rw [hj]
    by_cases h : j.val < r
    · have : (finSumFinEquiv.trans (finCongr hrs)).symm j = Sum.inl ⟨j, h⟩ := by
        apply (finSumFinEquiv.trans (finCongr hrs)).injective
        ext; simp
      rw [this, if_pos h, one_smul, hbs1]
    · have : (finSumFinEquiv.trans (finCongr hrs)).symm j = Sum.inr ⟨j.val - r, by omega⟩ := by
        apply (finSumFinEquiv.trans (finCongr hrs)).injective
        ext; simp; omega
      rw [this, if_neg h, zero_smul, hbs2]
  have hdiag : LinearMap.toMatrix b b f = Matrix.diagonal (fun i : Fin n => if i.val < r then (1 : W) else 0) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb j, map_smul, b.repr_self]
    by_cases hij : i = j
    · subst hij; simp; split_ifs <;> simp
    · simp [Matrix.diagonal_apply_ne _ hij, Finsupp.single_apply, Ne.symm hij]
      split_ifs <;> simp [Finsupp.single_apply, Ne.symm hij]
  let e := Pi.basisFun W (Fin n)
  refine ⟨r, e.toMatrix b, b.toMatrix e, ?_, ?_⟩
  · exact Module.Basis.toMatrix_mul_toMatrix_flip e b
  · have := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix e b e b f
    rw [← hdiag, this, LinearMap.toMatrix_eq_toMatrix', hfdef, LinearMap.toMatrix'_toLin']

theorem rank_map_const : ∀ (W : Type) [CommRing W] [IsLocalRing W] (n : ℕ) (Q : Matrix (Fin n) (Fin n) W),
    Q * Q = Q → ∃ r : ℕ, ∀ (k : Type) [Field k] (β : W →+* k), (Q.map β).rank = r := by
  intro W _ _ n Q hQ
  classical
  obtain ⟨r, P, P', hPP', hQeq⟩ := exists_conj_diag W n Q hQ
  refine ⟨Fintype.card {i : Fin n // i.val < r}, fun k _ β => ?_⟩
  have hm : P.map β * P'.map β = 1 := by
    rw [← Matrix.map_mul, hPP', Matrix.map_one _ β.map_zero β.map_one]
  have hP : IsUnit (P.map β).det := Matrix.isUnit_det_of_right_inverse hm
  have hP' : IsUnit (P'.map β).det := Matrix.isUnit_det_of_left_inverse hm
  rw [hQeq, Matrix.map_mul, Matrix.map_mul, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hP',
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP, Matrix.diagonal_map β.map_zero,
    Matrix.rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun i => by split_ifs with h <;> simp [h]))

end GlobalTheory.IdemRankLocal
end

section

open Matrix

namespace GlobalTheory

theorem exists_rows_linearIndependent_of_le_rank {K m n : Type} [Field K] [Fintype m] [Fintype n]
    (ρ : ℕ) (M : Matrix m n K) (h : ρ ≤ M.rank) :
    ∃ S : Fin ρ → m, LinearIndependent K (M.submatrix S id).row := by
  classical
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K M.row
  haveI : Finite κ := Finite.of_injective a ha
  letI : Fintype κ := Fintype.ofFinite κ
  have hκ : Fintype.card κ = M.rank := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_row]
  have hle : Fintype.card (Fin ρ) ≤ Fintype.card κ := by rw [hκ, Fintype.card_fin]; exact h
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hle
  exact ⟨a ∘ f, hli.comp f f.injective⟩

theorem exists_submatrix_det_ne_zero_of_le_rank :
    ∀ (k : Type) [Field k] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
      (ρ : ℕ) (Y : Matrix A D k), ρ ≤ Y.rank → ∃ S : Fin ρ → A, ∃ τ : Fin ρ → D,
        (Y.submatrix S τ).det ≠ 0 := by
  intro k _ A D _ _ _ _ ρ Y h
  obtain ⟨S, hS⟩ := exists_rows_linearIndependent_of_le_rank ρ Y h
  have hZ : (Y.submatrix S id).rank = ρ := by
    rw [Matrix.rank_eq_finrank_span_row, finrank_span_eq_card hS, Fintype.card_fin]
  have hZt : ρ ≤ (Y.submatrix S id)ᵀ.rank := by rw [Matrix.rank_transpose, hZ]
  obtain ⟨τ, hτ⟩ := exists_rows_linearIndependent_of_le_rank ρ (Y.submatrix S id)ᵀ hZt
  refine ⟨S, τ, ?_⟩
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_rows_iff_isUnit.1 hτ)
  have e : (Y.submatrix S id)ᵀ.submatrix τ id = (Y.submatrix S τ)ᵀ := by ext i j; rfl
  rw [e, Matrix.det_transpose] at hu
  exact hu.ne_zero

end GlobalTheory
end

section

open ValuativeRel Matrix

namespace GlobalTheory

theorem rows_mem_span_of_isUnit_mul (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A]
    [Fintype D] [DecidableEq D] (r : ℕ) (X : Matrix A D K) (H : Matrix (Fin r) A K)
    (Q : Matrix D (Fin r) K) (hX : X.rank ≤ r) (hU : IsUnit (H * X * Q)) :
    ∀ i, ∃ s : Fin r → K, X i = s ᵥ* (H * X) := by
  intro i
  have hle : Submodule.span K (Set.range (H * X)) ≤ Submodule.span K (Set.range X) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have : (H * X) j = ∑ a, H j a • X a := by
      ext d; simp [Matrix.mul_apply, Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  have h1 : r ≤ (H * X).rank := by
    have := Matrix.rank_mul_le_left (H * X) Q
    rw [Matrix.rank_of_isUnit _ hU] at this
    simpa using this
  have heq : Submodule.span K (Set.range (H * X)) = Submodule.span K (Set.range X) := by
    apply Submodule.eq_of_le_of_finrank_le hle
    have e1 : X.rank = Module.finrank K (Submodule.span K (Set.range X)) :=
      Matrix.rank_eq_finrank_span_row X
    have e2 : (H * X).rank = Module.finrank K (Submodule.span K (Set.range (H * X))) :=
      Matrix.rank_eq_finrank_span_row (H * X)
    omega
  have hi : X i ∈ Submodule.span K (Set.range (H * X)) := heq ▸ Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hi
  refine ⟨c, ?_⟩
  rw [← hc]
  ext d
  simp [Matrix.vecMul, dotProduct, Finset.sum_apply, mul_comm]

end GlobalTheory
end

section

open NumberField

namespace GlobalTheory.RationalSpan


open Classical in
theorem expand {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ} {s : Type}
    (b : Module.Basis s K L) (v : Fin n → L) :
    v = ∑ j ∈ Finset.univ.biUnion (fun i => (b.repr (v i)).support),
      b j • (fun i => algebraMap K L (b.repr (v i) j)) := by
  funext i
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  conv_lhs => rw [← b.linearCombination_repr (v i)]
  rw [Finsupp.linearCombination_apply]
  rw [Finsupp.sum_of_support_subset _ (s := Finset.univ.biUnion (fun i => (b.repr (v i)).support))]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Algebra.smul_def, mul_comm]
  · intro j hj
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hj⟩
  · intro j _
    simp

theorem repr_coord {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ} {s : Type}
    (b : Module.Basis s K L) (a : Fin n → K) (y : Fin n → L) (j : s) :
    b.repr (∑ k, algebraMap K L (a k) * y k) j = ∑ k, a k * b.repr (y k) j := by

  simp [← Algebra.smul_def, map_sum, Finsupp.finsetSum_apply]

theorem map_mulVec_comp {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (x : Fin n → K) :
    (M.map (algebraMap K L)).mulVec (fun i => algebraMap K L (x i)) =
      fun i => algebraMap K L (M.mulVec x i) := by
  funext i
  exact (RingHom.map_mulVec (algebraMap K L) M x i).symm

end GlobalTheory.RationalSpan

theorem GlobalTheory.rational_eigen_image_span : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ) (ι : Type) (A : ι → Matrix (Fin n) (Fin n) K) (lam : ι → K) (e : Matrix (Fin n) (Fin n) K), (∀ y : Fin n → L, (∀ p, ((A p).map (algebraMap K L)).mulVec y = algebraMap K L (lam p) • y) ↔ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' {x : Fin n → K | ∀ p, (A p).mulVec x = lam p • x})) ∧ ∀ y : Fin n → L, y ∈ LinearMap.range (e.map (algebraMap K L)).mulVecLin ↔ y ∈ Submodule.span L ((fun x i => algebraMap K L (x i)) '' (LinearMap.range e.mulVecLin : Set (Fin n → K))) := by
  intro K L _ _ _ n ι A lam e
  classical
  let b := Module.Basis.ofVectorSpace K L
  let f := algebraMap K L
  refine ⟨fun y => ⟨fun h => ?_, fun h => ?_⟩, fun y => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [GlobalTheory.RationalSpan.expand b y]
    refine Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩))
    intro p
    funext i
    have h1 := congrArg (fun z => b.repr z j) (congrFun (h p) i)
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [GlobalTheory.RationalSpan.repr_coord] at h1
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
    rw [h1, ← Algebra.smul_def]
    simp
  · let W : Submodule L (Fin n → L) :=
      { carrier := {y | ∀ p, ((A p).map f).mulVec y = f (lam p) • y}
        add_mem' := by
          intro a c ha hc p
          simp only [Set.mem_setOf_eq] at *
          rw [Matrix.mulVec_add, ha p, hc p, smul_add]
        zero_mem' := by
          intro p
          simp
        smul_mem' := by
          intro c a ha p
          simp only [Set.mem_setOf_eq] at *
          rw [Matrix.mulVec_smul, ha p, smul_comm] }
    have hle : Submodule.span L ((fun x i => f (x i)) '' {x : Fin n → K | ∀ p, (A p).mulVec x = lam p • x}) ≤ W := by
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩ p
      rw [GlobalTheory.RationalSpan.map_mulVec_comp, hx p]
      funext i
      simp [f, Algebra.smul_def]
    exact hle h
  · obtain ⟨z, rfl⟩ := h

    rw [GlobalTheory.RationalSpan.expand b z, map_sum]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    rw [map_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨e.mulVec (fun i => b.repr (z i) j), ⟨_, rfl⟩, ?_⟩)
    rw [Matrix.mulVecLin_apply, GlobalTheory.RationalSpan.map_mulVec_comp]
  · have hle : Submodule.span L ((fun x i => f (x i)) '' (LinearMap.range e.mulVecLin : Set (Fin n → K))) ≤ LinearMap.range (e.map f).mulVecLin := by
      rw [Submodule.span_le]
      rintro _ ⟨x, ⟨w, rfl⟩, rfl⟩
      exact ⟨fun i => f (w i), by rw [Matrix.mulVecLin_apply, GlobalTheory.RationalSpan.map_mulVec_comp]; rfl⟩
    exact hle h
end

section

noncomputable section

namespace GlobalTheory.LatOrb

open Polynomial Matrix

variable (O : Type) {K : Type} [CommRing O] [Field K] [Algebra O K]

def stdLat (n : ℕ) : Submodule O (Fin n → K) where
  carrier := {v | ∀ i, v i ∈ (algebraMap O K).range}
  add_mem' := by
    intro a b ha hb i
    exact Subring.add_mem _ (ha i) (hb i)
  zero_mem' := fun i => Subring.zero_mem _
  smul_mem' := by
    intro c v hv i
    obtain ⟨a, ha⟩ := hv i
    exact ⟨c * a, by simp [Algebra.smul_def, ha]⟩

def matLat {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K)) :
    Submodule O (Fin n → K) :=
  M.map ((Matrix.mulVecLin g).restrictScalars O)

def IsLatV {n : ℕ} (M : Submodule O (Fin n → K)) : Prop :=
  M.FG ∧ Submodule.span K (M : Set (Fin n → K)) = ⊤

def herm {n : ℕ} (σ : K →+* K) (x y : Fin n → K) : K := ∑ k, x k * σ (y k)

def SelfDual {n : ℕ} (σ : K →+* K) (M : Submodule O (Fin n → K)) : Prop :=
  ∀ y, y ∈ M ↔ ∀ x ∈ M, herm σ y x ∈ (algebraMap O K).range

variable {O}

theorem mem_stdLat {n : ℕ} (v : Fin n → K) : v ∈ stdLat O n ↔ ∀ i, v i ∈ (algebraMap O K).range :=
  Iff.rfl

theorem mem_matLat {n : ℕ} (g : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K))
    (v : Fin n → K) : v ∈ matLat O g M ↔ ∃ u ∈ M, g *ᵥ u = v := by
  simp [matLat]

theorem matLat_mul {n : ℕ} (a b : Matrix (Fin n) (Fin n) K) (M : Submodule O (Fin n → K)) :
    matLat O (a * b) M = matLat O a (matLat O b M) := by
  ext v
  simp only [mem_matLat]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨b *ᵥ u, ⟨u, hu, rfl⟩, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨u, hu, by rw [Matrix.mulVec_mulVec]⟩

theorem matLat_one {n : ℕ} (M : Submodule O (Fin n → K)) : matLat O 1 M = M := by
  ext v
  simp [mem_matLat]

end GlobalTheory.LatOrb
end
end

section

open MeasureTheory

namespace GlobalTheory

theorem card_leftCosets_doubleCoset_inv_eq : ∀ {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (ν : Measure G) [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] (J : Subgroup G) (α : G) (R R' : Finset G), MeasurableSet (J : Set G) → ν J ≠ 0 → ν J ≠ ⊤ → (∀ γ ∈ R, ∃ k₁ ∈ J, ∃ k₂ ∈ J, γ = k₁ * α * k₂) → (∀ x : G, (∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ J) → (∀ γ ∈ R', ∃ k₁ ∈ J, ∃ k₂ ∈ J, γ = k₁ * α⁻¹ * k₂) → (∀ x : G, (∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * α⁻¹ * k₂) → ∃! γ, γ ∈ R' ∧ γ⁻¹ * x ∈ J) → R.card = R'.card := by
  intro G _ _ _ ν _ _ J α R R' hJ h0 htop hR hRu hR' hR'u
  set S : Set G := {x | ∃ k₁ ∈ J, ∃ k₂ ∈ J, x = k₁ * α * k₂} with hS
  have hA : ∀ γ ∈ R, ∀ x, γ⁻¹ * x ∈ J → x ∈ S := by
    intro γ hγ x hx
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := hR γ hγ
    exact ⟨k₁, h₁, k₂ * ((k₁ * α * k₂)⁻¹ * x), J.mul_mem h₂ hx, by group⟩
  have hB : ∀ γ ∈ R', ∀ x, x * γ ∈ J → x ∈ S := by
    intro γ hγ x hx
    obtain ⟨k₁, h₁, k₂, h₂, rfl⟩ := hR' γ hγ
    exact ⟨x * (k₁ * α⁻¹ * k₂) * k₂⁻¹, J.mul_mem hx (J.inv_mem h₂), k₁⁻¹, J.inv_mem h₁, by group⟩
  have hBu : ∀ x ∈ S, ∃! γ, γ ∈ R' ∧ x * γ ∈ J := by
    rintro x ⟨k₁, h₁, k₂, h₂, hx⟩
    have := hR'u x⁻¹ ⟨k₂⁻¹, J.inv_mem h₂, k₁⁻¹, J.inv_mem h₁, by rw [hx]; group⟩
    simpa only [← mul_inv_rev, J.inv_mem_iff] using this
  have e1 : S = ⋃ γ ∈ R, (fun x => γ⁻¹ * x) ⁻¹' (J : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
    exact ⟨fun hx => (hRu x hx).exists, fun ⟨γ, h, h'⟩ => hA γ h x h'⟩
  have e2 : S = ⋃ γ ∈ R', (fun x => x * γ) ⁻¹' (J : Set G) := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe, exists_prop]
    exact ⟨fun hx => (hBu x hx).exists, fun ⟨γ, h, h'⟩ => hB γ h x h'⟩
  have m1 : ν S = R.card * ν J := by
    rw [e1, measure_biUnion_finset]
    · simp only [measure_preimage_mul, Finset.sum_const, nsmul_eq_mul]
    · intro a ha b hb hab
      rw [Function.onFun, Set.disjoint_left]
      intro x hxa hxb
      exact hab ((hRu x (hA a ha x hxa)).unique ⟨ha, hxa⟩ ⟨hb, hxb⟩)
    · intro b _
      exact measurable_const_mul _ hJ
  have m2 : ν S = R'.card * ν J := by
    rw [e2, measure_biUnion_finset]
    · simp only [measure_preimage_mul_right, Finset.sum_const, nsmul_eq_mul]
    · intro a ha b hb hab
      rw [Function.onFun, Set.disjoint_left]
      intro x hxa hxb
      exact hab ((hBu x (hB a ha x hxa)).unique ⟨ha, hxa⟩ ⟨hb, hxb⟩)
    · intro b _
      exact measurable_mul_const _ hJ
  have := (ENNReal.mul_left_inj h0 htop).1 (m1.symm.trans m2)
  exact_mod_cast this

end GlobalTheory
end
