module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import ReciprocityTheory.DualLattices.Bundle007
public import ReciprocityTheory.DualLattices.Bundle004
public import ReciprocityTheory.DualLattices.Bundle006
public import Mathlib.FieldTheory.IsAlgClosed.Basic
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Lemma
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
public import ReciprocityTheory.DualLattices.ProdEraseUpdate
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Ideal.Quotient.Basic

@[expose] public section

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

variable {R : Type} [CommRing R] {g : ℕ}

private lemma smulMV {κ μ : Type} [Fintype μ] (c : R) (M : Matrix κ μ R) (v : μ → R) :
    (c • M) *ᵥ v = c • (M *ᵥ v) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
    Finset.mul_sum, mul_assoc]

private theorem matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero {n : Type} [Fintype n] [DecidableEq n] {S : Type} [CommRing S]
    [IsDomain S] {A B : Matrix n n S} {c : S} (hc : c ≠ 0) (h : A * B = c • (1 : Matrix n n S)) :
    B * A = c • (1 : Matrix n n S) := by
  have hdet : A.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hc h1.symm
  have key : A.det • (B * A) = A.det • (c • (1 : Matrix n n S)) := by
    calc A.det • (B * A) = (A.adjugate * A) * (B * A) := by
          rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = A.adjugate * ((A * B) * A) := by simp only [Matrix.mul_assoc]
      _ = A.adjugate * (c • A) := by rw [h, Matrix.smul_mul, Matrix.one_mul]
      _ = c • (A.adjugate * A) := by rw [Matrix.mul_smul]
      _ = A.det • (c • (1 : Matrix n n S)) := by rw [Matrix.adjugate_mul]; exact smul_comm _ _ _
  ext i j
  have h2 := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h2
  simpa only [Matrix.smul_apply, smul_eq_mul] using mul_left_cancel₀ hdet h2

private theorem block_products_of_transpose_form_eq_smul [IsDomain R] {Ht Bt : Matrix (Fin g) (Ix g) R}
    {E : Matrix (Ix g) (Ix g) R} {cp : R} (hcp : cp ≠ 0) (hE : IsUnit E.det)
    (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E) :
    Bt * (Eᵀ)⁻¹ * Htᵀ = cp • 1 ∧ Bt * (Eᵀ)⁻¹ * Btᵀ = 0 ∧ -(Ht * (Eᵀ)⁻¹) * Htᵀ = 0 ∧
      -(Ht * (Eᵀ)⁻¹) * Btᵀ = cp • 1 := by
  have hT1 : Htᵀ * Bt - Btᵀ * Ht = cp • Eᵀ := by
    simpa only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_smul] using congrArg Matrix.transpose hform
  have hEF : Eᵀ * (Eᵀ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (by rwa [Matrix.det_transpose])
  have hP : Matrix.fromCols Htᵀ Btᵀ * Matrix.fromRows (Bt * (Eᵀ)⁻¹) (-(Ht * (Eᵀ)⁻¹)) =
      cp • (1 : Matrix (Ix g) (Ix g) R) := by
    rw [Matrix.fromCols_mul_fromRows, Matrix.mul_neg, ← sub_eq_add_neg, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← Matrix.sub_mul, hT1, Matrix.smul_mul, hEF]
  have hQ := matrix_mul_comm_of_mul_eq_smul_one_of_ne_zero hcp hP
  rw [Matrix.fromRows_mul_fromCols] at hQ
  have h1 : (cp • (1 : Matrix (Ix g) (Ix g) R)) = Matrix.fromBlocks (cp • 1) 0 0 (cp • 1) := by
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]
  rw [h1, Matrix.fromBlocks_inj] at hQ
  exact hQ

lemma hb_facts [IsDomain R] {Ht Bt : Matrix (Fin g) (Ix g) R} {E : Matrix (Ix g) (Ix g) R} {cp : R}
    (hcp : cp ≠ 0) (hE : IsUnit E.det) (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E) :
    Ht * ((Eᵀ)⁻¹ * Htᵀ) = 0 ∧ Bt * ((Eᵀ)⁻¹ * Htᵀ) = cp • (1 : Matrix (Fin g) (Fin g) R) := by
  obtain ⟨h11, -, h21, -⟩ := block_products_of_transpose_form_eq_smul hcp hE hform
  refine ⟨?_, ?_⟩
  · rw [Matrix.neg_mul, neg_eq_zero, Matrix.mul_assoc] at h21
    exact h21
  · rw [Matrix.mul_assoc] at h11
    exact h11

variable {m : ℕ}

lemma exists_fromRows_mulVec_iff [IsDomain R] {Ht Bt : Matrix (Fin g) (Ix g) R} {E : Matrix (Ix g) (Ix g) R} {cp : R}
    (hcp : cp ≠ 0) (hE : IsUnit E.det) (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)) (i : Fin m) (hHt : Ht * εT i = (εL (π i))ᵀ * Ht)
    (hBt : Bt * εT i = εL i * Bt) (x : Fin g → R) (hx : εL i *ᵥ x = x) :
    (∃ t, fromRows Ht Bt *ᵥ (εT i *ᵥ t) = Sum.elim (0 : Fin g → R) x) ↔
      ∃ z, Htᵀ *ᵥ x = cp • z := by
  have hT1 : Htᵀ * Bt - Btᵀ * Ht = cp • Eᵀ := by
    simpa only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_smul] using congrArg Matrix.transpose hform
  constructor
  · rintro ⟨t, ht⟩
    rw [Matrix.fromRows_mulVec] at ht
    have h1 : Ht *ᵥ (εT i *ᵥ t) = 0 := funext fun k => by simpa using congrFun ht (Sum.inl k)
    have h2 : Bt *ᵥ (εT i *ᵥ t) = x := funext fun k => by simpa using congrFun ht (Sum.inr k)
    refine ⟨Eᵀ *ᵥ (εT i *ᵥ t), ?_⟩
    rw [← smulMV, ← hT1, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1,
      h2, Matrix.mulVec_zero, sub_zero]
  · rintro ⟨z, hz⟩
    obtain ⟨hHF, hBF⟩ := hb_facts hcp hE hform
    have hs1 : Ht *ᵥ ((Eᵀ)⁻¹ *ᵥ z) = 0 := by
      have h : cp • (Ht *ᵥ ((Eᵀ)⁻¹ *ᵥ z)) = 0 := by
        rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← hz]
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        rw [hHF, Matrix.zero_mulVec]
      exact (smul_eq_zero.mp h).resolve_left hcp
    have hs2 : Bt *ᵥ ((Eᵀ)⁻¹ *ᵥ z) = x := by
      have h : cp • (Bt *ᵥ ((Eᵀ)⁻¹ *ᵥ z)) = cp • x := by
        rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← hz]
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        rw [hBF, smulMV, Matrix.one_mulVec]
      exact smul_right_injective _ hcp h
    generalize (Eᵀ)⁻¹ *ᵥ z = s at hs1 hs2
    have e1 : Ht *ᵥ (εT i *ᵥ s) = 0 := by
      rw [Matrix.mulVec_mulVec, hHt, ← Matrix.mulVec_mulVec, hs1, Matrix.mulVec_zero]
    have e2 : Bt *ᵥ (εT i *ᵥ s) = x := by
      rw [Matrix.mulVec_mulVec, hBt, ← Matrix.mulVec_mulVec, hs2, hx]
    exact ⟨s, by rw [Matrix.fromRows_mulVec, e1, e2]⟩

lemma cok_kill [IsDomain R] {Ht Bt : Matrix (Fin g) (Ix g) R} {E : Matrix (Ix g) (Ix g) R} {cp : R}
    (hcp : cp ≠ 0) (hE : IsUnit E.det) (hform : Btᵀ * Ht - Htᵀ * Bt = cp • E)
    (εT : Fin m → Matrix (Ix g) (Ix g) R) (εL : Fin m → Matrix (Fin g) (Fin g) R)
    (π : Equiv.Perm (Fin m)) (i : Fin m) (hπi : π (π i) = i)
    (hHt : ∀ j, Ht * εT j = (εL (π j))ᵀ * Ht) :
    ∀ f ∈ LinearMap.range (Matrix.mulVecLin (εL i)ᵀ), ∃ t, Ht *ᵥ (εT (π i) *ᵥ t) = cp • f := by
  intro f hf
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hf
  obtain ⟨-, -, -, h22⟩ := block_products_of_transpose_form_eq_smul hcp hE hform
  rw [Matrix.neg_mul, Matrix.mul_assoc] at h22
  have hHt' : Ht *ᵥ (-((Eᵀ)⁻¹ *ᵥ (Btᵀ *ᵥ y))) = cp • y := by
    rw [Matrix.mulVec_neg]
    simp only [Matrix.mulVec_mulVec]
    rw [← Matrix.neg_mulVec, h22, smulMV, Matrix.one_mulVec]
  generalize -((Eᵀ)⁻¹ *ᵥ (Btᵀ *ᵥ y)) = t at hHt'
  refine ⟨t, ?_⟩
  simp only [Matrix.mulVecLin_apply]
  rw [Matrix.mulVec_mulVec, hHt, hπi, ← Matrix.mulVec_mulVec, hHt', Matrix.mulVec_smul]

end ReciprocityTheory.PGsh.Up
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.PGsh.Up

theorem sum_val_zmod (p : ℕ) [Fact p.Prime] : ∑ a : ZMod p, a.val = p * (p - 1) / 2 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hinj : Set.InjOn (fun a : ZMod p => a.val) (univ : Finset (ZMod p)) :=
    fun a _ b _ h => ZMod.val_injective p h
  have himg : (univ : Finset (ZMod p)).image (fun a => a.val) = range p := by
    ext i
    simp only [mem_image, mem_univ, true_and, mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      exact ZMod.val_lt a
    · intro hi
      exact ⟨(i : ZMod p), ZMod.val_cast_of_lt hi⟩
  rw [← Finset.sum_range_id, ← himg]
  exact (Finset.sum_image (f := fun i : ℕ => i) hinj).symm

theorem sum_val_coord (p : ℕ) [Fact p.Prime] {ι : Type} [Fintype ι] [DecidableEq ι] (j : ι) :
    ∑ α : ι → ZMod p, (α j).val = p ^ (Fintype.card ι - 1) * (p * (p - 1) / 2) := by
  have h := (Equiv.funSplitAt j (ZMod p)).sum_comp (fun q => q.1.val)
  simp only [Equiv.funSplitAt_apply] at h
  rw [h, Fintype.sum_prod_type]
  simp only [sum_const, card_univ, smul_eq_mul]
  rw [← Finset.mul_sum, sum_val_zmod]
  congr 1
  rw [Fintype.card_fun, ZMod.card, Fintype.card_subtype_compl, Fintype.card_subtype_eq]

theorem u5 : MonomialDeterminantStatement := by
  intro p _ C _ v R _ _ hR hp ι _ _ Λ u hΛ hu hc
  have hpne : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  obtain ⟨I, hmem⟩ : ∃ I : Ideal R, ∀ r, r ∈ I ↔ v (algebraMap R C r) < 1 :=
    ⟨{ carrier := {r | v (algebraMap R C r) < 1}
       add_mem' := by
         intro a b ha hb
         show v (algebraMap R C (a + b)) < 1
         rw [map_add (f := _)]
         exact lt_of_le_of_lt (v.map_add _ _) (max_lt ha hb)
       zero_mem' := by
         show v (algebraMap R C 0) < 1
         simp
       smul_mem' := by
         intro c a ha
         show v (algebraMap R C (c * a)) < 1
         rw [map_mul, map_mul]
         exact lt_of_le_of_lt (mul_le_of_le_one_left (by positivity) (hR.map_le_one c)) ha },
     fun r => Iff.rfl⟩
  have hmax : I.IsMaximal := by
    rw [Ideal.isMaximal_iff]
    refine ⟨?_, ?_⟩
    · rw [hmem]
      simp
    · intro J x hIJ hxI hxJ
      have hv1 : v (algebraMap R C x) = 1 :=
        le_antisymm (hR.map_le_one x) (not_lt.mp fun h => hxI ((hmem x).mpr h))
      obtain ⟨y, hy⟩ := (hR.isUnit_of_one' hv1).exists_right_inv
      rw [← hy]
      exact J.mul_mem_right y hxJ
  letI : Field (R ⧸ I) := Ideal.Quotient.field I
  have hpk : ((p : ℕ) : R ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem, hmem, map_natCast]
    exact hp
  haveI : CharP (R ⧸ I) p := by
    have hdvd := (ringChar.spec (R ⧸ I) p).mp hpk
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact absurd h1 CharP.ringChar_ne_one
    · exact ringChar.eq_iff.mp h1
  have hC : IsUnit (Λ.map (Ideal.Quotient.mk I)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hΛ.map _
  have hN := det_monF_ne_zero (p := p) (Λ.map (Ideal.Quotient.mk I)) hC
  choose w hw using fun j x => hR.exists_of_le_one (hu j x)
  have hent : ∀ j x, Ideal.Quotient.mk I (w j x) = lam (Λ.map (Ideal.Quotient.mk I)) j x := by
    intro j x
    rw [show Ideal.Quotient.mk I (w j x) = Ideal.Quotient.mk I (∑ i, Λ j i * ((x i).val : R)) from
      Ideal.Quotient.eq.mpr ((hmem _).mpr (by rw [map_sub, hw]; exact hc j x))]

    simp only [map_sum, map_mul, map_natCast]
    simp only [lam, xc, Matrix.map_apply, ZMod.castHom_apply, ZMod.natCast_val]
  have hWN : Ideal.Quotient.mk I (Matrix.of fun (x α : ι → ZMod p) => ∏ j, w j x ^ (α j).val).det =
      (Matrix.of fun (x α : ι → ZMod p) => monF (Λ.map (Ideal.Quotient.mk I)) α x).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    ext x α
    simp only [Matrix.map_apply, Matrix.of_apply, map_prod, map_pow, monF, hent]
  have hWv : v (algebraMap R C (Matrix.of fun (x α : ι → ZMod p) => ∏ j, w j x ^ (α j).val).det) = 1 := by
    refine le_antisymm (hR.map_le_one _) (not_lt.mp fun h => hN ?_)
    rw [← hWN]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hmem _).mpr h)
  have hdetM : (Matrix.of fun (x α : ι → ZMod p) => ∏ j, u j x ^ (α j).val).det =
      algebraMap R C (Matrix.of fun (x α : ι → ZMod p) => ∏ j, w j x ^ (α j).val).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    congr 1
    ext x α
    simp only [Matrix.map_apply, Matrix.of_apply, map_prod, map_pow, hw]
  have h1 : v (Matrix.of fun (x α : ι → ZMod p) => ∏ j, u j x ^ (α j).val).det = 1 := by
    rw [hdetM]
    exact hWv
  refine ⟨h1, fun ε => ?_⟩
  have hscale : (Matrix.of fun (x α : ι → ZMod p) => ∏ j, (ε j * u j x) ^ (α j).val) =
      Matrix.of fun (x α : ι → ZMod p) =>
        (∏ j, ε j ^ (α j).val) * (Matrix.of fun (x α : ι → ZMod p) => ∏ j, u j x ^ (α j).val) x α := by
    ext x α
    simp only [Matrix.of_apply, mul_pow, Finset.prod_mul_distrib]
  rw [hscale, Matrix.det_mul_row, map_mul, h1, mul_one, Finset.prod_comm, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_pow_eq_pow_sum, map_pow, sum_val_coord p j]

end ReciprocityTheory.PGsh.Up
end
end

section

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

structure OEnd (B : BX R₀) (O : LAlg R₀) where
  f : ∀ {R : LAlg R₀}, LHom O R → B.G R →+ B.G R
  nat : ∀ {R S : LAlg R₀} (s : LHom O R) (g : LHom R S) (x : B.G R),
    f (g.comp s) (B.map g x) = B.map g (f s x)

structure OAdj (B : BX R₀) (O : LAlg R₀) where
  a : OEnd B O
  ab : OEnd B O
  e : ∀ {R : LAlg R₀} (s : LHom O R) (x z : B.G R), B.P R (a.f s x) z ≃ B.P R x (ab.f s z)
  e_smul : ∀ {R : LAlg R₀} (s : LHom O R) (x z : B.G R) (l : (R : Type u)ˣ) (u : B.P R (a.f s x) z),
    e s x z (B.smul l u) = B.smul l (e s x z u)
  equiv_addFst : ∀ {R : LAlg R₀} (s : LHom O R) (x x' z : B.G R) (u : B.P R (a.f s x) z)
    (u' : B.P R (a.f s x') z),
    e s (x + x') z (B.tr1 (map_add (a.f s) x x').symm (B.add1 u u')) =
      B.add1 (e s x z u) (e s x' z u')
  equiv_addSnd : ∀ {R : LAlg R₀} (s : LHom O R) (x z z' : B.G R) (u : B.P R (a.f s x) z)
    (w : B.P R (a.f s x) z'),
    e s x (z + z') (B.add2 u w) =
      B.tr2 (map_add (ab.f s) z z').symm (B.add2 (e s x z u) (e s x z' w))

namespace DualPair

variable {R : LAlg R₀} (Dp : DualPair R)

lemma ση_mem (r : (R : Type u)) : Dp.σ.1 r * Dp.η ∈ Dp.π.ker := by
  rw [LHom.ker, Submodule.restrictScalars_mem, Dp.ker_eq]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

def ηmap : (R : Type u) →ₗ[R₀] Dp.π.ker where
  toFun r := ⟨Dp.σ.1 r * Dp.η, Dp.ση_mem r⟩
  map_add' r r' := Subtype.ext (by simp [add_mul])
  map_smul' c r := Subtype.ext (by simp [Algebra.smul_def, mul_assoc])

end DualPair

def hext (B : BX R₀) {R : LAlg R₀} (h : B.gg →ₗ[R₀] (R : Type u)) : B.gg ⊗[R₀] (R : Type u) →ₗ[R₀] (R : Type u) :=
  LinearMap.mul' R₀ (R : Type u) ∘ₗ TensorProduct.map h LinearMap.id

def LinHtStatement (B : BX R₀) (O : LAlg R₀) : Prop :=
  ∀ (A : OAdj B O) (R : LAlg R₀) (s : LHom O R) (Dp : DualPair R) (N : ℕ) (y : B.G R)
    (h : B.gg →ₗ[R₀] (R : Type u)) (δ : B.gg →ₗ[R₀] B.gg ⊗[R₀] (R : Type u)),
    N • y = 0 → B.IsHeight Dp N y h →
    (∀ v, A.ab.f (Dp.σ.comp s) (B.tg Dp.π Dp.sqZero (v ⊗ₜ Dp.ηk)) =
      B.tg Dp.π Dp.sqZero (LinearMap.lTensor B.gg Dp.ηmap (δ v))) →
    B.IsHeight Dp N (A.a.f s y) (hext B h ∘ₗ δ)

end ReciprocityTheory.PGsh
end
end

section

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

structure ATower (R₀ : Type u) [CommRing R₀] (p : ℕ) where
  O : LAlg R₀
  R' : ℕ → LAlg R₀
  R : ℕ → LAlg R₀
  π : ∀ n, LHom (R' n) (R n)
  q : ∀ n, LHom O (R n)
  ξ : ∀ n, (R' n : Type u)
  surj : ∀ n, Function.Surjective (π n).1
  ker_eq : ∀ n, RingHom.ker (π n).1 = Ideal.span {ξ n}
  ξ_sq : ∀ n, ξ n * ξ n = 0
  ann : ∀ n (a : (R' n : Type u)), a * ξ n = 0 → a ∈ Ideal.span {ξ n}
  char : ∀ n, ((p ^ (n + 1) : ℕ) : (R' n : Type u)) = 0
  sep : ∀ a : (O : Type u), (∀ n, (q n).1 a = 0) → a = 0
  c : (O : Type u)
  cp : ∀ n, (R' n : Type u)
  cp_spec : ∀ n, (π n).1 (cp n) = (q n).1 c
  zh : ∀ n, (R' n : Type u)ˣ
  zh_pow : ∀ n, (zh n : (R' n : Type u)) ^ (p ^ (n + 1)) = 1 + cp n * ξ n
  ζ : ∀ n, (O : Type u)ˣ
  ζ_spec : ∀ n, (q n).1 (ζ n : (O : Type u)) = (π n).1 (zh n : (R' n : Type u))

variable {R₀ : Type u} [CommRing R₀]

lemma ATower.ξ_mem {p : ℕ} (Tw : ATower R₀ p) (n : ℕ) : Tw.ξ n ∈ (Tw.π n).ker := by
  rw [LHom.ker, Submodule.restrictScalars_mem, Tw.ker_eq]
  exact Ideal.subset_span (Set.mem_singleton _)

lemma ATower.sqZero {p : ℕ} (Tw : ATower R₀ p) (n : ℕ) : (Tw.π n).SqZero := ⟨Tw.surj n, by
    rw [Tw.ker_eq, sq, Ideal.span_singleton_mul_span_singleton, Tw.ξ_sq, Ideal.span_singleton_eq_bot]⟩

def NsetExpInjectiveSurjective (B : BX R₀) {p : ℕ} (Tw : ATower R₀ p) : Prop :=
  ∀ (Dp : ∀ n, DualPair (Tw.R n)) (ι : Type) (τ : ι → ℕ → B.G Tw.O)
    (E : ι → ι → (Tw.O : Type u)) (ht : ι → B.gg →ₗ[R₀] (Tw.O : Type u))
    (bt : ι → B.gg ⊗[R₀] (Tw.O : Type u)),
    (∀ i j n, ∃ k : ℕ, (Tw.q n).1 (E i j) = k ∧
      B.IsPairing (p ^ (n + 1)) (τ i n) (τ j n) (Tw.ζ n ^ k)) →
    (∀ i n, B.IsHeight (Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
      ((Tw.q n).1.toLinearMap ∘ₗ ht i)) →
    (∀ i n, ∃ (th : B.G (Tw.R' n)) (w : B.gg ⊗[R₀] (Tw.R' n : Type u)),
      B.map (Tw.π n) th = B.map (Tw.q n) (τ i n) ∧
      (p ^ (n + 1)) • th = B.tg (Tw.π n) (Tw.sqZero n)
        (TensorProduct.map LinearMap.id (ξmul (Tw.π n) (Tw.ξ n) (Tw.ξ_mem n)) w) ∧
      LinearMap.lTensor B.gg (Tw.π n).1.toLinearMap w =
        LinearMap.lTensor B.gg (Tw.q n).1.toLinearMap (bt i)) →
    ∀ i j, Tw.c * E i j = B.ev (ht j) (bt i) - B.ev (ht i) (bt j)

end ReciprocityTheory.PGsh
end
end

section

noncomputable section

open TensorProduct

namespace ReciprocityTheory.PGsh

universe u

variable {R₀ : Type u} [CommRing R₀]

namespace BX

variable (B : BX R₀)

def evK {R' R : LAlg R₀} (π : LHom R' R) (h : B.gg →ₗ[R₀] R') (V : B.gg ⊗[R₀] π.ker) : R' :=
  LinearMap.mul' R₀ R' (TensorProduct.map h π.ker.subtype V)

end BX

def TangentPairingStatement (B : BX R₀) : Prop :=
  ∀ (R' R : LAlg R₀) (π : LHom R' R) (ξ : (R' : Type u)) (Dp : DualPair R) (N : ℕ)
    (hsurj : Function.Surjective π.1) (hker : RingHom.ker π.1 = Ideal.span {ξ}) (hsq : ξ * ξ = 0),
    (∀ a, a * ξ = 0 → a ∈ Ideal.span {ξ}) → (N : (R' : Type u)) = 0 →
    ∀ (sh th : B.G R') (Vs Vt : B.gg ⊗[R₀] π.ker) (hs ht : B.gg →ₗ[R₀] R')
      (zh : (R' : Type u)ˣ) (z : (R : Type u)ˣ),
      N • sh = B.tg π (π.sqZero_of_span ξ hsurj hker hsq) Vs → N • th = B.tg π (π.sqZero_of_span ξ hsurj hker hsq) Vt →
      B.IsHeight Dp N (B.map π sh) (π.1.toLinearMap ∘ₗ hs) →
      B.IsHeight Dp N (B.map π th) (π.1.toLinearMap ∘ₗ ht) →
      B.IsPairing N (B.map π sh) (B.map π th) z → Units.map (π.1 : R' →* R) zh = z →
      (zh : (R' : Type u)) ^ N = 1 + (B.evK π ht Vs - B.evK π hs Vt)

end ReciprocityTheory.PGsh
end
end

section

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

def ColengthCotangentBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → v (p : C) < 1 →
    ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N], (∀ x : N, p • x = 0) →
    ∀ (AA : HopfOrder (C := C) R N) (lenN lenOm : NNReal),
      HasColen R v AA.carrier lenN → HasLen v R (OmAA AA.carrier) lenOm →
      lenN ^ 2 ≤ lenOm ^ Fintype.card N

end ReciprocityTheory.PGsh.Up
end
end
