module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Topology.Algebra.Valued.ValuationTopology
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.TensorProduct.Free

@[expose] public section

section

open Pointwise

namespace GlobalTheory

theorem length_quotient_span_pow_le (O : Type) [CommRing O] (p : O) (n : ℕ) :
    Module.length O (O ⧸ Ideal.span {p ^ n}) ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) := by
  induction n with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one]
    haveI : Subsingleton (O ⧸ (⊤ : Ideal O)) := Ideal.Quotient.subsingleton_iff.mpr rfl
    rw [Module.length_eq_zero]
    exact bot_le
  | succ n ih =>
    set S : Submodule O O := Ideal.span {p ^ (n + 1)} with hS
    set T : Submodule O O := Ideal.span {p ^ n} with hT
    have hST : S ≤ T := Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow p n.le_succ)
    let v : O ⧸ S := S.mkQ (p ^ n)
    have hker : (Ideal.span {p} : Submodule O O) ≤ LinearMap.ker (LinearMap.toSpanSingleton O (O ⧸ S) v) := by
      intro x hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      simp only [v, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul]
      rw [Submodule.Quotient.mk_eq_zero, hS, Ideal.mem_span_singleton']
      exact ⟨c, by ring⟩
    let ψ : (O ⧸ (Ideal.span {p} : Submodule O O)) →ₗ[O] O ⧸ S :=
      (Ideal.span {p} : Submodule O O).liftQ (LinearMap.toSpanSingleton O (O ⧸ S) v) hker
    let N : Submodule O (O ⧸ S) := LinearMap.range ψ
    have hN : N = T.map S.mkQ := by
      simp only [N, ψ, Submodule.range_liftQ, hT, Ideal.span, Submodule.map_span, Set.image_singleton]
      rw [← LinearMap.span_singleton_eq_range]
    have h1 := Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
      (LinearMap.exact_subtype_mkQ N)
    have hle : Module.length O N ≤ Module.length O (O ⧸ Ideal.span {p}) :=
      Module.length_le_of_surjective ψ.rangeRestrict ψ.surjective_rangeRestrict
    have heq : Module.length O ((O ⧸ S) ⧸ N) = Module.length O (O ⧸ Ideal.span {p ^ n}) := by
      rw [hN]
      exact (Submodule.quotientQuotientEquivQuotient S T hST).length_eq
    change Module.length O (O ⧸ S) ≤ _
    rw [h1, heq]
    calc Module.length O N + Module.length O (O ⧸ Ideal.span {p ^ n})
        ≤ Module.length O (O ⧸ Ideal.span {p}) + (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) :=
          add_le_add hle ih
      _ = ((n + 1 : ℕ) : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) := by
          push_cast; ring

theorem main : ∀ (O : Type) [CommRing O] (p : O) (n : ℕ),
    Module.length O (O ⧸ Ideal.span {p ^ n}) ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) :=
  fun O _ p n => length_quotient_span_pow_le O p n

end GlobalTheory
end

section

open Pointwise

namespace GlobalTheory

theorem length_quotient_tower_of_le {R : Type} [CommRing R] {X : Type} [AddCommGroup X] [Module R X]
    (Y W : Submodule R X) (hYW : Y ≤ W) :
    Module.length R (X ⧸ Y) =
      Module.length R (W ⧸ Y.comap W.subtype) + Module.length R (X ⧸ W) := by
  have hf : Function.Injective ((Y.comap W.subtype).mapQ Y W.subtype le_rfl) := by
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
    simp
  refine Module.length_eq_add_of_exact ((Y.comap W.subtype).mapQ Y W.subtype le_rfl)
    (Submodule.factor hYW) hf (Submodule.factor_surjective hYW) ?_
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H x =>
    constructor
    · intro h
      have hx : x ∈ W := by
        simpa [Submodule.Quotient.mk_eq_zero] using h
      exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩
    · rintro ⟨w, hw⟩
      rw [← hw]
      induction w using Submodule.Quotient.induction_on with
      | H z => simp [Submodule.Quotient.mk_eq_zero]

theorem length_quotient_smul_sup_le : ∀ (O A : Type) [CommRing O] [AddCommGroup A] [Module O A]
    (Z B B' : Submodule O A) (a : O), B ≤ B' →
    Module.length O (↥Z ⧸ (Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B).comap Z.subtype) ≤
      Module.length O ((↥Z ⧸ B'.comap Z.subtype) ⧸ LinearMap.range (a • (LinearMap.id :
        (↥Z ⧸ B'.comap Z.subtype) →ₗ[O] (↥Z ⧸ B'.comap Z.subtype)))) +
      Module.length O (↥(Z ⊓ B') ⧸ B.comap (Z ⊓ B').subtype) := by
  intro O A _ _ _ Z B B' a hBB'
  set N : Submodule O Z := (Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B).comap Z.subtype with hN
  set C : Submodule O Z := B'.comap Z.subtype with hC
  set K : Submodule O Z := N ⊔ C with hK
  rw [length_quotient_tower_of_le N K le_sup_left, add_comm]
  refine add_le_add ?_ ?_
  ·
    let f : (↥Z ⧸ C) →ₗ[O] (↥Z ⧸ K) := Submodule.factor (le_sup_right : C ≤ K)
    have hf : LinearMap.range (a • (LinearMap.id : (↥Z ⧸ C) →ₗ[O] (↥Z ⧸ C))) ≤ LinearMap.ker f := by
      rintro y ⟨q, rfl⟩
      induction q using Submodule.Quotient.induction_on with
      | H z =>
        rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, map_smul]
        change a • (Submodule.Quotient.mk z : ↥Z ⧸ K) = 0
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        refine Submodule.mem_sup_left ?_
        show ((a • z : Z) : A) ∈ Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B
        exact Submodule.mem_sup_left ⟨z, z.2, by simp⟩
    refine Module.length_le_of_surjective (Submodule.liftQ _ f hf) ?_
    intro w
    induction w using Submodule.Quotient.induction_on with
    | H z =>
      exact ⟨Submodule.Quotient.mk (Submodule.Quotient.mk z), rfl⟩
  ·
    let ι : ↥(Z ⊓ B') →ₗ[O] K :=
      LinearMap.codRestrict K (LinearMap.codRestrict Z (Z ⊓ B').subtype (fun x => x.2.1))
        (fun x => Submodule.mem_sup_right (show _ ∈ C from x.2.2))
    let φ : ↥(Z ⊓ B') →ₗ[O] (↥K ⧸ N.comap K.subtype) := (N.comap K.subtype).mkQ ∘ₗ ι
    have hφ : B.comap (Z ⊓ B').subtype ≤ LinearMap.ker φ := by
      intro x hx
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      show ((x : A)) ∈ Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B
      exact Submodule.mem_sup_right hx
    refine Module.length_le_of_surjective (Submodule.liftQ _ φ hφ) ?_
    intro w
    induction w using Submodule.Quotient.induction_on with
    | H k =>
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp k.2
      refine ⟨Submodule.Quotient.mk ⟨(z : A), z.2, hz⟩, ?_⟩
      rw [Submodule.liftQ_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.eq]
      have : ((ι ⟨(z : A), z.2, hz⟩ - k : K) : Z) = -y := by
        ext
        simp only [ι, ← hyz, Submodule.coe_sub, Submodule.coe_neg, Submodule.coe_add]
        change (z : A) - ((y : A) + (z : A)) = -(y : A)
        abel
      show ((ι ⟨(z : A), z.2, hz⟩ - k : K) : Z) ∈ N
      rw [this]
      exact N.neg_mem hy

end GlobalTheory
end

section

open Pointwise

namespace GlobalTheory

theorem length_le_of_forall_fg_length_le (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (b : ℕ∞)
    (h : ∀ N : Submodule O M, N.FG → Module.length O N ≤ b) : Module.length O M ≤ b := by
  rw [Module.length_eq_height]
  refine Order.height_le_iff'.2 fun p _ => ?_
  have hx : ∀ i : Fin p.length, ∃ x ∈ p i.succ, x ∉ p i.castSucc :=
    fun i => SetLike.exists_of_lt (p.step i)
  choose x hx1 hx2 using hx
  set N : Submodule O M := Submodule.span O (Set.range x) with hN
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range x)
  have hxN : ∀ i, x i ∈ N := fun i => Submodule.subset_span ⟨i, rfl⟩
  let q : LTSeries (Submodule O N) :=
    { length := p.length
      toFun := fun i => (p i).comap N.subtype
      step := fun i => by
        refine lt_of_le_of_ne (Submodule.comap_mono (p.step i).le) ?_
        intro heq
        have h1 : (⟨x i, hxN i⟩ : N) ∈ (p i.succ).comap N.subtype := hx1 i
        rw [← heq] at h1
        exact hx2 i h1 }
  have h2 : (q.length : ℕ∞) ≤ Order.height (⊤ : Submodule O N) :=
    Order.length_le_height le_top
  calc (p.length : ℕ∞) = q.length := rfl
    _ ≤ Order.height (⊤ : Submodule O N) := h2
    _ = Module.length O N := (Module.length_eq_height (R := O) (M := N)).symm
    _ ≤ b := h N hNfg

end GlobalTheory
end

section

open scoped TensorProduct
open Matrix

namespace GlobalTheory

theorem exists_combination_norm_ne_zero_of_linearIndependent
    {B A : Type} [CommRing B] [IsDomain B] [CommRing A] [Algebra B A]
    [Module.Free B A] [Module.Finite B A] {d : ℕ} (hd : Module.finrank B A = d)
    (y : Fin d → A) (hy : LinearIndependent B y) :
    ∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0 := by
  classical
  let e := Module.finBasisOfFinrankEq B A hd
  let Y : Matrix (Fin d) (Fin d) B := fun i j => e.equivFun (y j) i
  have key : ∀ v : Fin d → B, e.equivFun (∑ j, v j • y j) = Y *ᵥ v := by
    intro v
    ext i
    simp [Y, Matrix.mulVec, dotProduct, mul_comm]
  have hdet : Y.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    have h1 : ∑ j, v j • y j = 0 := by
      apply e.equivFun.injective
      rw [key, hv, map_zero]
    exact hv0 (funext fun j => Fintype.linearIndependent_iff.mp hy v h1 j)
  refine ⟨Y.adjugate *ᵥ e.equivFun 1, ?_⟩
  have hsum : ∑ j, (Y.adjugate *ᵥ e.equivFun 1) j • y j = algebraMap B A Y.det := by
    apply e.equivFun.injective
    rw [key, Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec,
      Matrix.one_mulVec, Algebra.algebraMap_eq_smul_one, map_smul]
  rw [hsum, Algebra.norm_algebraMap]
  exact pow_ne_zero _ hdet

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory


open MvPolynomial in
theorem exists_field_combination_norm_ne_zero {k B A : Type} [Field k] [Infinite k] [CommRing B]
    [IsDomain B] [Algebra k B] [CommRing A] [Algebra B A] [Module.Free B A] [Module.Finite B A]
    {d : ℕ} (y : Fin d → A) (hx : ∃ x : Fin d → B, Algebra.norm B (∑ i, x i • y i) ≠ 0) :
    ∃ a : Fin d → k, Algebra.norm B (∑ i, algebraMap k B (a i) • y i) ≠ 0 := by
  classical
  obtain ⟨x₀, hx₀⟩ := hx
  let b := Module.Free.chooseBasis B A
  let M : Matrix (Module.Free.ChooseBasisIndex B A) (Module.Free.ChooseBasisIndex B A)
      (MvPolynomial (Fin d) B) :=
    Matrix.of fun j l => ∑ i, X i * C (Algebra.leftMulMatrix b (y i) j l)
  have heval : ∀ x : Fin d → B, eval x M.det = Algebra.norm B (∑ i, x i • y i) := by
    intro x
    rw [Algebra.norm_eq_matrix_det b, RingHom.map_det]
    congr 1
    ext j l

    simp [M, map_sum, Matrix.sum_apply, mul_comm]
  by_contra hcon
  push_neg at hcon
  have hinf : ∀ _ : Fin d, (Set.range (algebraMap k B)).Infinite := fun _ =>
    Set.infinite_range_of_injective (algebraMap k B).injective
  have hQ : M.det = 0 := by
    refine funext_set (fun _ => Set.range (algebraMap k B)) hinf fun x hx => ?_
    choose a ha using fun i => hx i (Set.mem_univ i)
    rw [heval, map_zero, ← hcon a]
    simp [ha]
  exact hx₀ (by rw [← heval, hQ, map_zero])

end GlobalTheory
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem norm_tensorProduct_map_left {R B L : Type} [Field R] [CommRing B] [Algebra R B] [Field L]
    [Algebra R L] [FiniteDimensional R L] (f : B →ₐ[R] B) (w : B ⊗[R] L) :
    Algebra.norm B (Algebra.TensorProduct.map f (AlgHom.id R L) w) = f (Algebra.norm B w) := by
  classical
  let e := Module.finBasis R L
  let b := Algebra.TensorProduct.basis B e
  let σ := Algebra.TensorProduct.map f (AlgHom.id R L)
  have hrepr : ∀ z : B ⊗[R] L, ∀ i, b.repr (σ z) i = f (b.repr z i) := by
    intro z i
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x y =>
      simp only [σ, b, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
        smul_eq_mul, map_mul, AlgHom.commutes]
    | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy]
  have hb : ∀ j, σ (b j) = b j := by
    intro j
    simp [σ, b, Algebra.TensorProduct.basis_apply]
  have hmat : Algebra.leftMulMatrix b (σ w) = (Algebra.leftMulMatrix b w).map f := by
    ext i j
    rw [Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
      ← hb j, ← map_mul, hb j, hrepr]
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b, hmat]
  exact (AlgHom.map_det f _).symm

end GlobalTheory
end

section

noncomputable section

namespace GlobalTheory.Hk3.GramSep

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def gam (σ : L →+* L) (ϖ : L) {r : ℕ} (e : Fin r → ℕ) : AddSubgroup (Matrix (Fin r) (Fin r) L) where
  carrier := {Γ | (∀ k j, σ (Γ k j) = - Γ j k) ∧ ∀ k j, Valued.v (Γ k j) ≤ Valued.v ϖ ^ max (e k) (e j)}
  zero_mem' := ⟨fun k j => by simp, fun k j => by simp⟩
  add_mem' := by
    intro a b ha hb
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.add_apply, map_add (f := _), ha.1 k j, hb.1 k j]; ring
    · exact (Valuation.map_add _ _ _).trans (max_le (ha.2 k j) (hb.2 k j))
  neg_mem' := by
    intro a ha
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.neg_apply, map_neg, ha.1 k j]
    · simpa only [Matrix.neg_apply, Valuation.map_neg] using ha.2 k j

def gam0 (σ : L →+* L) (ϖ : L) {r : ℕ} (e : Fin r → ℕ) : AddSubgroup (Matrix (Fin r) (Fin r) L) where
  carrier := {Γ | (∀ k j, σ (Γ k j) = - Γ j k) ∧ ∀ k j, Valued.v (Γ k j) ≤ Valued.v ϖ ^ (e k + e j)}
  zero_mem' := ⟨fun k j => by simp, fun k j => by simp⟩
  add_mem' := by
    intro a b ha hb
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.add_apply, map_add (f := _), ha.1 k j, hb.1 k j]; ring
    · exact (Valuation.map_add _ _ _).trans (max_le (ha.2 k j) (hb.2 k j))
  neg_mem' := by
    intro a ha
    refine ⟨fun k j => ?_, fun k j => ?_⟩
    · simp only [Matrix.neg_apply, map_neg, ha.1 k j]
    · simpa only [Matrix.neg_apply, Valuation.map_neg] using ha.2 k j

end GlobalTheory.Hk3.GramSep

end
end
