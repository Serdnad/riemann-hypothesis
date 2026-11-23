module

public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.OreLocalization.Ring
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Ideal.IdempotentFG
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module

@[expose] public section

section

namespace GlobalTheory

open IsLocalization

theorem exists_basicOpen_isUnit_of_notMem_map :
    ∀ (S : Type) [CommRing S] (f₀ : S) (q : Ideal S), q.IsPrime → f₀ ∉ q →
      ∀ (J : Type) [Finite J] (m : J → Localization.Away f₀),
        (∀ i, m i ∉ Ideal.map (algebraMap S (Localization.Away f₀)) q) →
        ∃ f : S, f ∉ q ∧ ∃ φ : Localization.Away f₀ →ₐ[S] Localization.Away f,
          ∀ i, IsUnit (φ (m i)) := by
  intro S _ f₀ q hq hf₀ J _ m hm
  classical
  haveI := Fintype.ofFinite J
  have hdisj : Disjoint (↑(Submonoid.powers f₀) : Set S) ↑q :=
    (Ideal.disjoint_powers_iff_notMem f₀ hq.isRadical).2 hf₀
  haveI hq' : (Ideal.map (algebraMap S (Localization.Away f₀)) q).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f₀) (Localization.Away f₀) q hq hdisj
  set d : (Localization.Away f₀) := ∏ i, m i with hd
  have hdq : d ∉ Ideal.map (algebraMap S (Localization.Away f₀)) q := by
    intro h
    obtain ⟨i, -, hi⟩ := (Ideal.IsPrime.prod_mem_iff (p := Ideal.map (algebraMap S (Localization.Away f₀)) q)).1 h
    exact hm i hi
  obtain ⟨⟨a, y⟩, hay⟩ := IsLocalization.mk'_surjective (Submonoid.powers f₀) d
  simp only at hay
  have hspec : d * algebraMap S (Localization.Away f₀) y = algebraMap S (Localization.Away f₀) a := by
    rw [← hay]; exact IsLocalization.mk'_spec (Localization.Away f₀) a y
  have hyu : IsUnit (algebraMap S (Localization.Away f₀) y) := IsLocalization.map_units (Localization.Away f₀) y
  have ha : a ∉ q := by
    intro haq
    have h1 : algebraMap S (Localization.Away f₀) a ∈ Ideal.map (algebraMap S (Localization.Away f₀)) q := Ideal.mem_map_of_mem _ haq
    rw [← hspec] at h1
    rcases hq'.mem_or_mem h1 with h2 | h2
    · exact hdq h2
    · exact hq'.ne_top (Ideal.eq_top_of_isUnit_mem _ h2 hyu)
  refine ⟨f₀ * a, fun h => (hq.mem_or_mem h).elim hf₀ ha, ?_⟩
  let ψ : (Localization.Away f₀) →+* Localization.Away (f₀ * a) := IsLocalization.Away.awayToAwayRight f₀ a
  let φ : (Localization.Away f₀) →ₐ[S] Localization.Away (f₀ * a) :=
    { ψ with commutes' := fun r => IsLocalization.Away.awayToAwayRight_eq f₀ a r }
  refine ⟨φ, fun i => ?_⟩
  have hφ : ∀ x, φ x = ψ x := fun _ => rfl

  have hau : IsUnit (algebraMap S (Localization.Away (f₀ * a)) a) := by
    have hu : IsUnit (algebraMap S (Localization.Away (f₀ * a)) (f₀ * a)) :=
      IsLocalization.Away.algebraMap_isUnit (f₀ * a)
    rw [map_mul] at hu
    exact isUnit_of_mul_isUnit_right hu
  have hyu' : IsUnit (φ (algebraMap S (Localization.Away f₀) y)) := hyu.map φ
  have hdu : IsUnit (φ d) := by
    have h3 : φ d * φ (algebraMap S (Localization.Away f₀) y) = algebraMap S _ a := by
      rw [← map_mul, hspec, AlgHom.commutes]
    exact isUnit_of_mul_isUnit_left (h3 ▸ hau)
  have hdvd : m i ∣ d := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
  exact isUnit_of_dvd_unit (map_dvd φ hdvd) hdu

end GlobalTheory
end

section

namespace GlobalTheory.Morita

structure MatrixUnits (R : Type*) [CommRing R] (N : Type*) [AddCommGroup N] [Module R N]
    (ι : Type*) [Fintype ι] [DecidableEq ι] where

  E : ι → ι → Module.End R N
  mul_eq : ∀ i j k l, E i j * E k l = if j = k then E i l else 0
  sum_diag : ∑ i, E i i = 1

variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace MatrixUnits

variable (U : MatrixUnits R N ι)

theorem apply_apply (i j k l : ι) (x : N) : U.E i j (U.E k l x) = if j = k then U.E i l x else 0 := by
  have h := LinearMap.congr_fun (U.mul_eq i j k l) x
  rw [Module.End.mul_apply] at h
  rw [h]; split_ifs <;> simp

theorem sum_apply (x : N) : ∑ i, U.E i i x = x := by
  have h := LinearMap.congr_fun U.sum_diag x
  simpa [LinearMap.sum_apply] using h

def corner (a : ι) : Submodule R N := LinearMap.range (U.E a a)

theorem mem_corner_iff (a : ι) (x : N) : x ∈ U.corner a ↔ U.E a a x = x := by
  constructor
  · rintro ⟨y, rfl⟩; rw [U.apply_apply]; simp
  · intro h; exact ⟨x, h⟩

theorem apply_mem_corner (a i : ι) (x : N) : U.E a i x ∈ U.corner a := ⟨U.E a i x, by rw [U.apply_apply]; simp⟩

def toPi (a : ι) : N ≃ₗ[R] (ι → U.corner a) where
  toFun x i := ⟨U.E a i x, U.apply_mem_corner a i x⟩
  map_add' x y := by ext i; simp
  map_smul' r x := by ext i; simp
  invFun v := ∑ i, U.E i a (v i)
  left_inv x := by
    simp only
    conv_rhs => rw [← U.sum_apply x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [U.apply_apply]; simp
  right_inv v := by
    ext j

    simp only [map_sum, U.apply_apply]
    simp [(U.mem_corner_iff a _).1 (v j).2]

theorem toPi_apply (a : ι) (x : N) (i : ι) : ((U.toPi a x) i : N) = U.E a i x := rfl

theorem toPi_E (a i j : ι) (x : N) : U.toPi a (U.E i j x) = Pi.single i (U.toPi a x j) := by
  ext k
  rw [toPi_apply, U.apply_apply]
  by_cases h : k = i
  · subst h; simp [toPi_apply]
  · simp [h, Pi.single_apply]

end MatrixUnits

def stdUnits (M : Type*) [AddCommGroup M] [Module R M] : MatrixUnits R (ι → M) ι where
  E i j := LinearMap.single R (fun _ => M) i ∘ₗ LinearMap.proj j
  mul_eq i j k l := by
    ext x m
    by_cases h : j = k
    · subst h; simp [Pi.single_apply]
    · simp [h, Pi.single_apply]
  sum_diag := by
    ext x m
    simp [LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply]

end GlobalTheory.Morita

namespace GlobalTheory.Morita
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

end GlobalTheory.Morita

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

section semilinear

variable {σ : R →+* R} (F : N →ₛₗ[σ] N)

end semilinear

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita.MatrixUnits
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι] (U : MatrixUnits R N ι)

section extend

variable {σ : R →+* R}

def extend (a : ι) (F₀ : U.corner a →ₛₗ[σ] U.corner a) : N →ₛₗ[σ] N where
  toFun x := ∑ i, U.E i a (F₀ (U.toPi a x i))
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.smul_sum]

end extend

end GlobalTheory.Morita.MatrixUnits

namespace GlobalTheory.Morita
variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

end GlobalTheory.Morita

namespace GlobalTheory.Morita
variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]

end GlobalTheory.Morita

universe w

namespace GlobalTheory.Morita

variable {R : Type*} [CommRing R] {N : Type*} [AddCommGroup N] [Module R N]
  {ι : Type*} [Fintype ι] [DecidableEq ι]


end GlobalTheory.Morita
end

section

open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.IdemNewton

variable {A : Type} [CommRing A] {Λ : Type} [Ring Λ] [Algebra A Λ]

theorem mem_smul_top_iff_repr {ι : Type} [Fintype ι] (b : Module.Basis ι A Λ) (J : Ideal A) (z : Λ) :
    z ∈ J • (⊤ : Submodule A Λ) ↔ ∀ i, b.repr z i ∈ J := by
  constructor
  · intro hz i
    refine Submodule.smul_induction_on hz (fun r hr y _ => ?_) (fun y w hy hw => ?_)
    · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact J.mul_mem_right _ hr
    · rw [map_add (f := _), Finsupp.add_apply]
      exact add_mem hy hw
  · intro h
    rw [← b.sum_repr z]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (h i) Submodule.mem_top

theorem mul_mem_right {J : Ideal A} {z : Λ} (y : Λ) (hz : z ∈ J • (⊤ : Submodule A Λ)) :
    z * y ∈ J • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun r hr w _ => ?_) (fun u w hu hw => ?_)
  · rw [smul_mul_assoc]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [add_mul]
    exact add_mem hu hw

theorem mul_mem_left {J : Ideal A} {z : Λ} (y : Λ) (hz : z ∈ J • (⊤ : Submodule A Λ)) :
    y * z ∈ J • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun r hr w _ => ?_) (fun u w hu hw => ?_)
  · rw [mul_smul_comm]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · rw [mul_add]
    exact add_mem hu hw

theorem mul_mem {J K : Ideal A} {z y : Λ} (hz : z ∈ J • (⊤ : Submodule A Λ))
    (hy : y ∈ K • (⊤ : Submodule A Λ)) : z * y ∈ (J * K) • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun r hr w _ => ?_) (fun u w hu hw => ?_)
  · rw [smul_mul_assoc, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hr (mul_mem_left w hy)
  · rw [add_mul]
    exact add_mem hu hw

theorem exists_idem : ∀ (A : Type) [CommRing A] (I : Ideal A) [IsAdicComplete I A] (Λ : Type) [Ring Λ]
    [Algebra A Λ] [Module.Free A Λ] [Module.Finite A Λ] (x : Λ),
    x * x - x ∈ I • (⊤ : Submodule A Λ) →
      ∃ e : Λ, IsIdempotentElem e ∧ e - x ∈ I • (⊤ : Submodule A Λ) := by
  intro A _ I _ Λ _ _ _ _ x hx
  let b := Module.Free.chooseBasis A Λ
  have mono : ∀ {k m : ℕ}, k ≤ m → ∀ {z : Λ}, z ∈ (I ^ m) • (⊤ : Submodule A Λ) →
      z ∈ (I ^ k) • (⊤ : Submodule A Λ) := fun hkm _ hz =>
    Submodule.smul_mono_left (Ideal.pow_le_pow_right hkm) hz
  let f : ℕ → Λ := fun k => Nat.rec x (fun _ y => 3 * (y * y) - 2 * (y * y * y)) k
  have f0 : f 0 = x := rfl
  have fs : ∀ k, f (k + 1) = 3 * (f k * f k) - 2 * (f k * f k * f k) := fun k => rfl
  have h1 : ∀ k, (f k * f k - f k) ∈ (I ^ (k + 1)) • (⊤ : Submodule A Λ) := by
    intro k
    induction k with
    | zero => simpa [f0] using hx
    | succ k ih =>
      have e : f (k + 1) * f (k + 1) - f (k + 1) =
          ((f k * f k - f k) * (f k * f k - f k)) * (4 * (f k * f k) - 4 * f k - 3) := by
        rw [fs]; noncomm_ring
      rw [e]
      refine mul_mem_right _ ?_
      have := mul_mem ih ih
      rw [← pow_add] at this
      exact mono (by omega) this
  have h2 : ∀ k, (f (k + 1) - f k) ∈ (I ^ (k + 1)) • (⊤ : Submodule A Λ) := by
    intro k
    have e : f (k + 1) - f k = (f k * f k - f k) * (1 - 2 * f k) := by
      rw [fs]; noncomm_ring
    rw [e]
    exact mul_mem_right _ (h1 k)
  have h3 : ∀ k m, k ≤ m → (f m - f k) ∈ (I ^ (k + 1)) • (⊤ : Submodule A Λ) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => simp
    | succ m hkm ih =>
      have e : f (m + 1) - f k = (f (m + 1) - f m) + (f m - f k) := by abel
      rw [e]
      exact add_mem (mono (by omega) (h2 m)) ih
  have h4 : ∀ i, ∃ L : A, ∀ k, b.repr (f k) i - L ∈ I ^ k := by
    intro i
    obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) (fun k => b.repr (f k) i) (fun {k m} hkm => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_mem_iff, neg_sub]
      have := (mem_smul_top_iff_repr b _ _).1 (mono (Nat.le_succ k) (h3 k m hkm)) i
      rwa [map_sub, Finsupp.sub_apply] at this)
    refine ⟨L, fun k => ?_⟩
    have := hL k
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  choose L hL using h4
  let e : Λ := b.equivFun.symm L
  have he : ∀ i, b.repr e i = L i := fun i => by
    have := congrFun (b.equivFun.apply_symm_apply L) i
    rwa [Module.Basis.equivFun_apply] at this
  have hL' : ∀ k, (f k - e) ∈ (I ^ k) • (⊤ : Submodule A Λ) := fun k =>
    (mem_smul_top_iff_repr b _ _).2 fun i => by
      rw [map_sub, Finsupp.sub_apply, he]
      exact hL i k
  refine ⟨e, ?_, ?_⟩
  · change e * e = e
    rw [← sub_eq_zero]
    refine b.ext_elem fun i => ?_
    rw [map_zero, Finsupp.zero_apply]
    refine IsHausdorff.haus' (I := I) _ fun k => ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    refine (mem_smul_top_iff_repr b _ _).1 ?_ i
    have e1 : e * e - e = (f k * f k - f k) - ((f k - e) * (f k - 1) + e * (f k - e)) := by
      noncomm_ring
    rw [e1]
    exact sub_mem (mono (Nat.le_succ k) (h1 k))
      (add_mem (mul_mem_right _ (hL' k)) (mul_mem_left _ (hL' k)))
  · have e1 : e - x = (f 1 - f 0) - (f 1 - e) := by rw [f0]; abel
    rw [e1]
    have a := h2 0
    have c := hL' 1
    rw [zero_add, pow_one] at a
    rw [pow_one] at c
    exact sub_mem a c

end GlobalTheory.IdemNewton
end

section

open scoped TensorProduct

namespace GlobalTheory

theorem invariant_derivation_exists :
    ∀ (k A : Type) [CommRing k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → ∀ l : A →ₗ[k] k, (∀ a b, l (a * b) = ε a * l b + ε b * l a) → ∃ D : Derivation k A A, ∀ a, ε (D a) = l a := by
  intro k A _ _ _ ε Δ hε l hl
  obtain ⟨h1, h2⟩ := hε
  let F : A ⊗[k] A →ₗ[k] A := (TensorProduct.rid k A).toLinearMap ∘ₗ LinearMap.lTensor A l
  let E : A ⊗[k] A →ₗ[k] A :=
    (TensorProduct.rid k A).toLinearMap ∘ₗ LinearMap.lTensor A ε.toLinearMap
  have hF : ∀ a b : A, F (a ⊗ₜ b) = l b • a := fun a b => by simp [F]
  have hE : ∀ a b : A, E (a ⊗ₜ b) = ε b • a := fun a b => by simp [E]
  have key : ∀ x y : A ⊗[k] A, F (x * y) = E x * F y + E y * F x := by
    intro x y
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul c d =>
        rw [Algebra.TensorProduct.tmul_mul_tmul, hF, hF, hF, hE, hE, hl]
        simp only [Algebra.smul_def, map_add (f := _), map_mul]
        ring
      | add y₁ y₂ ih₁ ih₂ =>
        rw [mul_add, map_add (f := _), ih₁, ih₂, map_add (f := _), map_add (f := _)]
        ring
    | add x₁ x₂ ih₁ ih₂ =>
      rw [add_mul, map_add (f := _), ih₁, ih₂, map_add (f := _), map_add (f := _)]
      ring
  have hEΔ : ∀ a, E (Δ a) = a := fun a => h2 a
  have hεF : ∀ x : A ⊗[k] A,
      ε (F x) = l (TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap x)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rw [hF]
      simp [mul_comm]
    | add x₁ x₂ ih₁ ih₂ => rw [map_add (f := _), map_add (f := _), ih₁, ih₂, map_add (f := _), map_add (f := _), map_add (f := _)]
  refine ⟨Derivation.mk' (F ∘ₗ Δ.toLinearMap) (fun a b => ?_), fun a => ?_⟩
  · simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, map_mul,
      key, hEΔ, smul_eq_mul]
  · show ε (F (Δ a)) = l a
    rw [hεF, h1]

end GlobalTheory
end

section

open scoped TensorProduct
universe u

namespace GlobalTheory

theorem exists_idem_local_of_character :
    ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A]
      (φ : A →ₐ[k] k), ∃ e : A, IsIdempotentElem e ∧ φ e = 1 ∧
        ∀ a, φ a = 0 → IsNilpotent (e * a) := by
  intro k _ A _ _ _ φ
  haveI : IsArtinianRing A := IsArtinianRing.of_finite k A
  set m : Ideal A := RingHom.ker φ with hm
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := A) (M := A)
    ⟨fun n => OrderDual.toDual (m ^ n), fun _ _ h => Ideal.pow_le_pow_right h⟩
  have hst : ∀ j, n ≤ j → m ^ n = m ^ j := fun j hj => hn j hj
  set N := n + 1 with hN
  have hI : IsIdempotentElem (m ^ N) := by
    show m ^ N * m ^ N = m ^ N
    rw [← pow_add, ← hst (N + N) (by omega), hst N (by omega)]
  have hfg : (m ^ N).FG := IsNoetherian.noetherian _
  obtain ⟨f, hf, hIf⟩ := (Ideal.isIdempotentElem_iff_of_fg _ hfg).1 hI
  refine ⟨1 - f, hf.one_sub, ?_, ?_⟩
  · have hfm : f ∈ m := by
      have : f ∈ m ^ N := by rw [hIf]; exact Ideal.subset_span rfl
      exact Ideal.pow_le_self (by omega) this
    have : φ f = 0 := hfm
    simp [this]
  · intro a ha
    have ham : a ∈ m := ha
    have haN : a ^ N ∈ m ^ N := Ideal.pow_mem_pow ham N
    rw [hIf, Ideal.mem_span_singleton'] at haN
    obtain ⟨y, hy⟩ := haN
    refine ⟨N, ?_⟩
    rw [mul_pow, hf.one_sub.pow_succ_eq n, ← hy]
    have : (1 - f) * f = 0 := by rw [sub_mul, one_mul, hf.eq, sub_self]
    calc (1 - f) * (y * f) = y * ((1 - f) * f) := by ring
      _ = 0 := by rw [this, mul_zero]

end GlobalTheory
end
