module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle101
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.TensorProduct.Maps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle105
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.SymplecticGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle108
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open scoped TensorProduct
universe u

theorem _root_.GlobalTheory.T.characterAugmentationSubspace_top_eq_ker_smul :
    ∀ (k : Type) [Field k] (C : Type) [CommRing C] (H : Type u) [AddCommGroup H]
      [Module k H] (σ : C →+* Module.End k H) (χ : C →+* k),
      letI : Module (k ⊗[ℤ] C) H := Module.compHom H
        (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
          (fun _ _ => Algebra.commutes _ _)).toRingHom;
      ∀ x : H, x ∈ GlobalTheory.HTRho.mSub σ χ ⊤ ↔
        x ∈ (RingHom.ker (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom
          (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) • ⊤ : Submodule (k ⊗[ℤ] C) H) := by
  intro k _ C _ H _ _ σ χ
  let L := Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
    (fun _ _ => Algebra.commutes _ _)
  let φ := Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom
    (fun _ _ => Commute.all _ _)
  let : Module (k ⊗[ℤ] C) H := Module.compHom H L.toRingHom
  let X := GlobalTheory.HTRho.mSub σ χ ⊤
  let Y : Submodule (k ⊗[ℤ] C) H := RingHom.ker φ • ⊤
  change ∀ x : H, x ∈ X ↔ x ∈ Y
  have hsmul (a : k ⊗[ℤ] C) (y : H) : a • y = L a y := rfl
  have hL (l : k) (c : C) (y : H) : L (l ⊗ₜ c) y = l • σ c y := by
    exact congrArg (fun f : Module.End k H => f y)
      (Algebra.TensorProduct.lift_tmul (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
        (fun _ _ => Algebra.commutes _ _) l c)
  have hφ (l : k) (c : C) : φ (l ⊗ₜ c) = l * χ c := by
    simp [φ]
  have hSub (a : k ⊗[ℤ] C) (y : H) : L a y - φ a • y ∈ X := by
    induction a using TensorProduct.inductionOn with
    | tmul l c =>
      rw [hL, hφ, mul_smul, ← smul_sub]
      exact Submodule.smul_mem X l (Submodule.subset_span ⟨c, y, trivial, by simp⟩)
    | add a b ha hb =>
      rw [map_add L, map_add φ, LinearMap.add_apply, add_smul, add_sub_add_comm]
      exact add_mem ha hb
  intro x
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, y, -, rfl⟩ := hz
      let a : k ⊗[ℤ] C := 1 ⊗ₜ c - χ c ⊗ₜ (1 : C)
      have ha : a ∈ RingHom.ker φ := by
        change φ a = 0
        simp [a, hφ]
      have hy : a • y ∈ Y := Submodule.smul_mem_smul ha (Submodule.mem_top (x := y))
      have hay : a • y = σ (algebraMap C C c) y - χ c • y := by
        rw [hsmul]
        simp [a, hL]
      exact hay ▸ hy
    | zero => exact Y.zero_mem
    | add a b _ _ ha hb => exact Y.add_mem ha hb
    | smul l z _ hz =>
      have hl : (l ⊗ₜ (1 : C) : k ⊗[ℤ] C) • z = l • z := by
        rw [hsmul, hL, map_one, one_apply_eq_self]
      exact hl ▸ Y.smul_mem _ hz
  · intro hx
    refine Submodule.smul_induction_on (show x ∈ RingHom.ker φ • ⊤ from hx) ?_ ?_
    · intro a ha y _
      rw [hsmul]
      simpa only [RingHom.mem_ker.mp ha, zero_smul, sub_zero] using hSub a y
    · intro a b ha hb
      exact X.add_mem ha hb
end

section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.UnitaryStd

variable {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ) (g : ℕ)

theorem form_cx_coord (S : Matrix (Fin r) (Fin r) ℤ) (y z : Lat ρ g) :
    form ρ g S (cx ρ g y) z = ∑ i, ∑ j, S i j *
      ∑ α : Fin g ⊕ Fin g, (basis ρ g).repr y (i, α) * (basis ρ g).repr z (j, α) := by
  rw [form_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [cx_apply, basis_repr, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, dotProduct,
    Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add]
  ring

theorem form_cx_basis (S : Matrix (Fin r) (Fin r) ℤ) (p q : Fin r × (Fin g ⊕ Fin g)) :
    form ρ g S (cx ρ g (basis ρ g p)) (basis ρ g q) = if p.2 = q.2 then S p.1 q.1 else 0 := by
  rw [form_cx_coord]
  obtain ⟨i0, a⟩ := p
  obtain ⟨j0, b⟩ := q
  simp only [Module.Basis.repr_self, Finsupp.single_apply, Prod.mk.injEq]
  simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]

theorem form_cx_baseChange_pos (S : Matrix (Fin r) (Fin r) ℤ) (hS : (S.map (Int.cast : ℤ → ℝ)).PosDef)
    (x : ℝ ⊗[ℤ] Lat ρ g) (hx : x ≠ 0) :
    0 < (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x := by
  set b := Algebra.TensorProduct.basis ℝ (basis ρ g) with hb
  set c := b.repr x with hc
  have hx' : x = ∑ p, c p • b p := (b.sum_repr x).symm
  have key : (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x =
      ∑ q, ∑ p, c p * c q * (((if p.2 = q.2 then S p.1 q.1 else 0 : ℤ)) : ℝ) := by
    conv_lhs => rw [hx']

    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hb,
    Algebra.TensorProduct.basis_apply, LinearMap.baseChange_tmul, LinearMap.BilinForm.baseChange_tmul,
    form_cx_basis, mul_one, zsmul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  set v : (Fin g ⊕ Fin g) → Fin r → ℝ := fun α i => c (i, α) with hv
  have key2 : (form ρ g S).baseChange ℝ ((cx ρ g).baseChange ℝ x) x =
      ∑ α, v α ⬝ᵥ ((S.map (Int.cast : ℤ → ℝ)).mulVec (v α)) := by
    rw [key, Finset.sum_comm]
    simp only [Fintype.sum_prod_type, Int.cast_ite, Int.cast_zero, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, dotProduct, Matrix.mulVec,
      Matrix.map_apply, Finset.mul_sum, hv]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key2]
  have hnn : ∀ α, 0 ≤ v α ⬝ᵥ ((S.map (Int.cast : ℤ → ℝ)).mulVec (v α)) := by
    intro α
    by_cases h0 : v α = 0
    · simp [h0]
    · simpa using (hS.dotProduct_mulVec_pos h0).le
  have hne : c ≠ 0 := by
    intro h; apply hx; rw [hx']; simp [h]
  obtain ⟨⟨i, α⟩, hp⟩ : ∃ p, c p ≠ 0 := by
    by_contra h; push_neg at h; exact hne (Finsupp.ext h)
  have hα : v α ≠ 0 := fun h => hp (by simpa [hv] using congrFun h i)
  have hpos : 0 < v α ⬝ᵥ ((S.map (Int.cast : ℤ → ℝ)).mulVec (v α)) := by
    simpa using hS.dotProduct_mulVec_pos hα
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (fun β _ => hnn β) (Finset.mem_univ α))

end GlobalTheory.UnitaryStd
end

section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.UnitaryStd

theorem form_basis_basis {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ)
    (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) (a c : Fin g ⊕ Fin g) :
    form ρ g S (basis ρ g (j, c)) (basis ρ g (i, a)) =
      S j i * (Matrix.J (Fin g) ℤ) a c := by
  rw [form_apply, Matrix.J]
  simp only [basis_apply, dotProduct]
  rcases a with k | k <;> rcases c with l | l <;>
    simp [Pi.single_apply, Prod.ext_iff, Matrix.one_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm]
  all_goals simp [ite_and, Finset.mul_sum, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.sum_ite_irrel, mul_ite]
  all_goals (split_ifs <;> simp_all)

theorem toMatrix_basis_dualBasis_form {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ)
    (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ) :
    LinearMap.toMatrix (basis ρ g) (basis ρ g).dualBasis (form ρ g S) =
      Matrix.kroneckerMap (· * ·) S.transpose (Matrix.J (Fin g) ℤ) := by
  ext ⟨i, a⟩ ⟨j, c⟩
  rw [LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr, form_basis_basis]
  rfl

theorem form_bijective_of_unimodular : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ)
    (g : ℕ) (S : Matrix (Fin r) (Fin r) ℤ), IsUnit S.det → Function.Bijective (GlobalTheory.UnitaryStd.form ρ g S) := by
  intro E _ _ r ρ g S hS
  set b := basis ρ g
  set M := LinearMap.toMatrix b b.dualBasis (form ρ g S) with hMdef
  have hM : IsUnit M.det := by
    rw [hMdef, toMatrix_basis_dualBasis_form, Matrix.det_kronecker, Matrix.det_transpose]
    exact (hS.pow _).mul ((Matrix.isUnit_det_J (Fin g) ℤ).pow _)
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hM
  have hf : form ρ g S = Matrix.toLin b b.dualBasis M := by rw [hMdef, Matrix.toLin_toMatrix]
  set Ψ := Matrix.toLin b.dualBasis b M⁻¹
  have hl : ∀ x, Ψ (form ρ g S x) = x := fun x => by
    rw [hf, ← LinearMap.comp_apply, ← Matrix.toLin_mul, h2, Matrix.toLin_one, LinearMap.id_apply]
  have hr : ∀ f, form ρ g S (Ψ f) = f := fun f => by
    rw [hf, ← LinearMap.comp_apply, ← Matrix.toLin_mul, h1, Matrix.toLin_one, LinearMap.id_apply]
  exact ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩

end GlobalTheory.UnitaryStd
end

section

open NumberField

open Pointwise
namespace GlobalTheory

theorem twistDet_rows {E K : Type} [Field E] [Field K] (τE : E →+* K) {p : ℕ}
    (β : Fin p → K) (c : Fin p → Fin p → E) :
    (Matrix.of fun i => β i • fun a => τE (c i a)).det = (∏ i, β i) * τE (Matrix.of c).det := by
  have h : (Matrix.of fun i => β i • fun a => τE (c i a)) =
      Matrix.diagonal β * (Matrix.of c).map τE := by
    ext i j
    simp [Matrix.diagonal_mul]
  rw [h, Matrix.det_mul, Matrix.det_diagonal, RingHom.map_det]
  rfl

theorem pow_eq_span_prod_set {K : Type} [Field K] [NumberField K] (p : ℕ) (𝔟 : Submodule (𝓞 K) K) :
    𝔟 ^ p = Submodule.span (𝓞 K) (∏ _i ∈ (Finset.univ : Finset (Fin p)), (𝔟 : Set K)) := by
  rw [← Submodule.prod_span]
  simp [Finset.prod_const]

theorem span_twistDets_eq {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K]
    (τ : 𝓞 E →+* 𝓞 K) (τE : E →+* K) (hτ : ∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) (p : ℕ)
    (𝔟 : Submodule (𝓞 K) K) (Λ : Submodule (𝓞 E) (Fin p → E)) :
    Submodule.span (𝓞 K) {d | ∃ y : Fin p → Fin p → K,
        (∀ i, y i ∈ {x : Fin p → K | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) ∧ d = (Matrix.of y).det} =
      𝔟 ^ p * Submodule.span (𝓞 K) (τE '' GlobalTheory.IdxTensor.dets E p Λ) := by
  set S : Set K := {d | ∃ y : Fin p → Fin p → K,
        (∀ i, y i ∈ {x : Fin p → K | ∃ β ∈ 𝔟, ∃ c ∈ Λ, x = β • fun a => τE (c a)}) ∧ d = (Matrix.of y).det}
    with hS
  have hpow := pow_eq_span_prod_set p 𝔟
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro d ⟨y, hy, rfl⟩
    choose β hβ c hc hyc using hy
    have hy' : y = fun i => β i • fun a => τE (c i a) := funext hyc
    subst hy'
    rw [twistDet_rows]
    refine Submodule.mul_mem_mul ?_ ?_
    · rw [hpow]
      refine Submodule.subset_span ?_
      rw [Set.mem_finsetProd]
      exact ⟨β, fun {i} _ => hβ i, rfl⟩
    · exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨c, hc, rfl⟩, rfl⟩
  · rw [Submodule.mul_le]

    have key : ∀ c : Fin p → Fin p → E, (∀ i, c i ∈ Λ) →
        ∀ m ∈ 𝔟 ^ p, m * τE (Matrix.of c).det ∈ Submodule.span (𝓞 K) S := by
      intro c hc m hm
      rw [hpow] at hm
      induction hm using Submodule.span_induction with
      | mem x hx =>
        rw [Set.mem_finsetProd] at hx
        obtain ⟨β, hβ, rfl⟩ := hx
        refine Submodule.subset_span ⟨fun i => β i • fun a => τE (c i a), fun i => ?_, ?_⟩
        · exact ⟨β i, hβ (Finset.mem_univ i), c i, hc i, rfl⟩
        · rw [twistDet_rows]
      | zero => simp
      | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
      | smul r x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ r hx
    have key2 : ∀ e ∈ GlobalTheory.IdxTensor.dets E p Λ, ∀ m ∈ 𝔟 ^ p,
        m * τE e ∈ Submodule.span (𝓞 K) S := by
      intro e he
      induction he using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨c, hc, rfl⟩ := hx
        exact key c hc
      | zero => intro m _; simp
      | add x y _ _ hx hy =>
        intro m hm; rw [map_add (f := _), mul_add]; exact add_mem (hx m hm) (hy m hm)
      | smul a x _ hx =>
        intro m hm
        rw [Algebra.smul_def, map_mul]
        have : τE (algebraMap (𝓞 E) E a) = ((τ a : 𝓞 K) : K) := hτ a
        rw [this, mul_left_comm, ← Algebra.smul_def (τ a)]
        · exact Submodule.smul_mem _ (τ a) (hx m hm)
    intro m hm n hn
    induction hn using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨e, he, rfl⟩ := hx
      exact key2 e he m hm
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | smul r x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ r hx

end GlobalTheory
end

section

open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory

theorem one_tmul_mem_locOrder_of_nsmul_mem : ∀ {B : Type} [Ring B] [Algebra ℚ B] (OB : Subring B) (b : B) (m : ℕ),
    0 < m → (m : B) * b ∈ OB → ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ m →
    (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b ∈ locOrder ℓ OB := by
  intro B _ _ OB b m hm hmb ℓ _ hℓ
  have hunit : IsUnit (m : ℤ_[ℓ]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : ℓ.Prime)).mpr hℓ)
  obtain ⟨u, hu⟩ := hunit
  have hgen : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((m : B) * b) ∈ locOrder ℓ OB :=
    Algebra.subset_adjoin ⟨_, hmb, rfl⟩
  have key : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] b = ((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((m : B) * b)) := by
    rw [TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    have : ((m : B) * b) = (m : ℚ) • b := by rw [Algebra.smul_def]; simp
    rw [this, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    congr 1
    have h1 : ((u : ℤ_[ℓ]) : ℚ_[ℓ]) = (m : ℚ_[ℓ]) := by rw [hu]; simp
    have h2 : (((u⁻¹ : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) : ℚ_[ℓ]) * ((u : ℤ_[ℓ]) : ℚ_[ℓ]) = 1 := by
      rw [← PadicInt.coe_mul]; simp
    rw [h1] at h2
    rw [Algebra.smul_def]
    simp only [map_natCast]
    rw [PadicInt.algebraMap_apply]
    linear_combination h2.symm
  rw [key]
  exact Subalgebra.smul_mem _ hgen _

end GlobalTheory
end

section

open NumberField

namespace GlobalTheory.IdxTensor

theorem dets_span_eq {F : Type} [Field F] [NumberField F] (p : ℕ) (S : Set (Fin p → F)) :
    GlobalTheory.IdxTensor.dets F p (Submodule.span (𝓞 F) S) =
      Submodule.span (𝓞 F) {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ S) ∧ d = (Matrix.of y).det} := by
  set T : Set F := {d | ∃ y : Fin p → Fin p → F, (∀ i, y i ∈ S) ∧ d = (Matrix.of y).det} with hT
  apply le_antisymm
  · unfold dets
    rw [Submodule.span_le]
    rintro d ⟨y, hy, rfl⟩
    have key : ∀ s : Finset (Fin p), ∀ y : Fin p → Fin p → F,
        (∀ i, y i ∈ Submodule.span (𝓞 F) S) → (∀ i, i ∉ s → y i ∈ S) →
          (Matrix.of y).det ∈ Submodule.span (𝓞 F) T := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro y _ h
        exact Submodule.subset_span ⟨y, fun i => h i (Finset.notMem_empty i), rfl⟩
      | insert a s ha ih =>
        intro y hy hs
        have upd : ∀ v, Matrix.of (Function.update y a v) = Matrix.updateRow (Matrix.of y) a v := fun v => rfl
        have hv : ∀ v ∈ Submodule.span (𝓞 F) S,
            (Matrix.updateRow (Matrix.of y) a v).det ∈ Submodule.span (𝓞 F) T := by
          intro v hv
          induction hv using Submodule.span_induction with
          | mem x hx =>
            rw [← upd]
            apply ih
            · intro i
              by_cases h : i = a
              · subst h; simpa using Submodule.subset_span hx
              · simpa [Function.update_of_ne h] using hy i
            · intro i hi
              by_cases h : i = a
              · subst h; simpa using hx
              · simpa [Function.update_of_ne h] using hs i (by simp [h, hi])
          | zero =>
            rw [Matrix.det_eq_zero_of_row_eq_zero a (by intro j; simp)]
            exact Submodule.zero_mem _
          | add x z _ _ hx hz =>
            rw [Matrix.det_updateRow_add]
            exact Submodule.add_mem _ hx hz
          | smul r x _ hx =>
            rw [← algebraMap_smul F r x, Matrix.det_updateRow_smul, ← Algebra.smul_def]
            exact Submodule.smul_mem _ r hx
        have := hv (y a) (hy a)
        rwa [← upd, Function.update_eq_self] at this
    exact key Finset.univ y hy (by simp)
  · unfold dets
    apply Submodule.span_mono
    rintro d ⟨y, hy, rfl⟩
    exact ⟨y, fun i => Submodule.subset_span (hy i), rfl⟩

end GlobalTheory.IdxTensor
end

section

open scoped TensorProduct
open GlobalTheory.LKInvGood

namespace GlobalTheory

theorem cenOrder_finite : ∀ (F : Type) [Field F] [NumberField F] (ℓ : ℕ) [Fact ℓ.Prime],
    Module.Finite ℤ_[ℓ] (cenOrder ℓ F) := by
  intro F _ _ ℓ _
  classical
  let f : NumberField.RingOfIntegers F → ℚ_[ℓ] ⊗[ℚ] F := fun a => (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (a : F)
  obtain ⟨s, hs⟩ := (inferInstance : Module.Finite ℤ (NumberField.RingOfIntegers F)).fg_top
  have hint : ∀ x ∈ (f '' (s : Set (NumberField.RingOfIntegers F))), IsIntegral ℤ_[ℓ] x := by
    rintro _ ⟨a, -, rfl⟩
    have h1 : IsIntegral ℤ ((a : F)) := NumberField.RingOfIntegers.isIntegral_coe a
    have h2 : IsIntegral ℤ (f a) := by
      have := h1.map ((Algebra.TensorProduct.includeRight : F →ₐ[ℚ] ℚ_[ℓ] ⊗[ℚ] F).restrictScalars ℤ)
      simpa [f] using this
    exact h2.tower_top
  have hfin : Module.Finite ℤ_[ℓ] (Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F)))) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral ((s.finite_toSet).image f) hint
  have heq : cenOrder ℓ F = Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F))) := by
    apply le_antisymm
    · apply Algebra.adjoin_le
      rintro _ ⟨a, rfl⟩
      let A := Algebra.adjoin ℤ_[ℓ] (f '' (s : Set (NumberField.RingOfIntegers F)))
      let N : Submodule ℤ (NumberField.RingOfIntegers F) :=
        { carrier := {x | f x ∈ A}
          add_mem' := by
            intro x y hx hy
            simp only [Set.mem_setOf_eq, f, map_add (f := _), TensorProduct.tmul_add] at hx hy ⊢
            exact A.add_mem hx hy
          zero_mem' := by
            simp only [Set.mem_setOf_eq, f, map_zero, TensorProduct.tmul_zero]
            exact A.zero_mem
          smul_mem' := by
            intro c x hx
            simp only [Set.mem_setOf_eq, f, zsmul_eq_mul, map_mul, map_intCast] at hx ⊢
            have : (1 : ℚ_[ℓ]) ⊗ₜ[ℚ] ((c : F) * (x : F)) = c • ((1 : ℚ_[ℓ]) ⊗ₜ[ℚ] (x : F)) := by
              rw [← zsmul_eq_mul, TensorProduct.tmul_smul]
            rw [this]
            exact A.toSubring.zsmul_mem hx c }
      have hsN : (s : Set _) ⊆ N := fun x hx => show f x ∈ A from Algebra.subset_adjoin ⟨x, hx, rfl⟩
      have : a ∈ N := by
        have := Submodule.span_le.mpr hsN
        rw [hs] at this
        exact this Submodule.mem_top
      exact this
    · apply Algebra.adjoin_mono
      rintro _ ⟨a, -, rfl⟩
      exact ⟨a, rfl⟩
  rw [heq]
  exact hfin

end GlobalTheory
end
