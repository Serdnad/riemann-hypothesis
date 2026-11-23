module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.ToDual
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle005
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Algebra.Module.Projective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle006
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Order.SupIndep
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle007
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle009
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle010
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle012
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.PowerSeries.Basic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle001
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.LinearAlgebra.Isomorphisms

@[expose] public section

section

open Polynomial

theorem _root_.GlobalTheory.T.exists_separable_generator_card_eq_pow_natDegree : ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] [Algebra (ZMod l) K], ∃ (a : K) (p : (ZMod l)[X]), p.Monic ∧ Irreducible p ∧ aeval a p = 0 ∧ aeval a (derivative p) ≠ 0 ∧ (∀ y : K, ∃ q : (ZMod l)[X], aeval a q = y) ∧ Nat.card K = l ^ p.natDegree := by
  first | exact @GlobalTheory.finiteField_exists_generator_minpoly | exact GlobalTheory.finiteField_exists_generator_minpoly | (intros; apply GlobalTheory.finiteField_exists_generator_minpoly <;> assumption)
end

section

open scoped PowerSeries Pointwise

theorem _root_.GlobalTheory.T.numerical_conditions_theorem_T_large_prime : ∀ (l H N η r : ℕ), 2 ≤ N → 1 ≤ η → η < H → 4 * r ≤ N ^ 2 → 40 * (H * N ^ 2 + N ^ 3) < l → 2 * (H + η + 2 * (N - 1) * r + 1) + 2 < l ∧ 10 * H + 2 ≤ l ∧ 14 * H + (N + 2) * η < l ∧ 8 * H + 1 < l ∧ 4 * η * r + 4 < l ∧ (r + 2) * η < l + 1 := by
  first | exact @GlobalTheory.numerical_bounds_of_forty_mul_lt | exact GlobalTheory.numerical_bounds_of_forty_mul_lt | (intros; apply GlobalTheory.numerical_bounds_of_forty_mul_lt <;> assumption)
end

section

open scoped NNReal

theorem _root_.GlobalTheory.T.frobeniusPowEquation_dvd_all_pow : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (u : R), ((l : ℕ) : R) = 0 → u ∈ nonZeroDivisors R → ∀ (κ : Type) [Fintype κ] (D : κ → R) (c : κ → κ → R) (h : ℕ), (∀ j, u ^ h * D j = ∑ i, D i ^ l * c i j) → (∀ j (M : ℕ), ∃ c : ℕ, ∀ n : ℕ, u ^ (M * n) ∣ u ^ c * D j ^ n) → ∀ (m : ℕ) j, u ^ m ∣ D j := by
  first | exact @GlobalTheory.phiEq_dvd_all_pow | exact GlobalTheory.phiEq_dvd_all_pow | (intros; apply GlobalTheory.phiEq_dvd_all_pow <;> assumption)
end

section


theorem _root_.GlobalTheory.T.card_le_of_double_annihilator_pairing : ∀ (O : Type) [CommRing O] (X Y E : Type) [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module O Y] [AddCommGroup E] [Module O E] [Finite X] (β : Y →ₗ[O] X →ₗ[O] E) (S : Submodule O X) (F : Finset Y) (Es : Finset E) (a : O), (∀ c, (∀ y, (∀ s ∈ S, β y s = 0) → β y c = 0) → c ∈ S) → (∀ y, (∀ s ∈ S, β y s = 0) → y ∈ F ∧ a • y = 0) → (∀ e : E, a • e = 0 → e ∈ Es) → Nat.card X ≤ Es.card ^ F.card * Nat.card S := by
  first | exact @GlobalTheory.card_le_of_double_annihilator | exact GlobalTheory.card_le_of_double_annihilator | (intros; apply GlobalTheory.card_le_of_double_annihilator <;> assumption)
end

section


theorem _root_.GlobalTheory.T.projective_of_free_lattice_over_finite_free_ring : ∀ (Z S A D : Type) [CommRing Z] [CommRing S] [CommRing A] [AddCommGroup D] [Module A D] (z : Z →+* S) (a : S →+* A) (N : Submodule A D) (q : ℕ) (x : Fin q → D), (∀ y, y ∈ N ↔ ∃ s : Fin q → S, y = ∑ i, a (s i) • x i) → (∀ s : Fin q → S, ∑ i, a (s i) • x i = 0 → s = 0) → (∃ (d : ℕ) (w : Fin d → S), ∀ y : S, ∃! c : Fin d → Z, y = ∑ i, z (c i) * w i) → @Module.Projective Z _ ↥N _ (Module.compHom _ (a.comp z)) := by
  first | exact @GlobalTheory.projective_compHom_of_free_of_finite_free | exact GlobalTheory.projective_compHom_of_free_of_finite_free | (intros; apply GlobalTheory.projective_compHom_of_free_of_finite_free <;> assumption)
end

section


theorem _root_.GlobalTheory.T.filter_weight_mem_of_tate_graded_stable : ∀ {C σ Γ : Type} [Field C] [Group Γ] [MulSemiringAction Γ C] (χ : Γ →* Cˣ), (∀ m : ℤ, m ≠ 0 → ∀ a : C, (∀ g : Γ, g • a = ((χ g ^ m : Cˣ) : C) * a) → a = 0) → ∀ (w : σ → ℤ) (J : Submodule C (σ →₀ C)), (∀ g : Γ, ∀ φ ∈ J, ∃ ψ ∈ J, ∀ m, ψ m = ((χ g ^ w m : Cˣ) : C) * (g • φ m)) → ∀ φ ∈ J, ∀ d : ℤ, φ.filter (fun m => w m = d) ∈ J := by
  first | exact @GlobalTheory.tate_weight_graded | exact GlobalTheory.tate_weight_graded | (intros; apply GlobalTheory.tate_weight_graded <;> assumption)
end

section


theorem _root_.GlobalTheory.T.disjoint_finset_sup_of_supIndep_sup' : ∀ (R V ι : Type) [Ring R] [AddCommGroup V] [Module R V] (F : Finset ι) (G B : ι → Submodule R V), F.SupIndep (fun i => G i ⊔ B i) → (∀ i ∈ F, Disjoint (G i) (B i)) → Disjoint (F.sup G) (F.sup B) := by
  first | exact @GlobalTheory.disjoint_finset_sup_of_supIndep_sup | exact GlobalTheory.disjoint_finset_sup_of_supIndep_sup | (intros; apply GlobalTheory.disjoint_finset_sup_of_supIndep_sup <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.StableLatCount Polynomial

namespace GlobalTheory

theorem card_kernel_quot_of_bijective (O : Type) [CommRing O] (P : Type) [AddCommGroup P]
    [Module O P] (N : Submodule O P) (T : P →ₗ[O] P) (hT : Function.Bijective T)
    (hN : ∀ x ∈ N, T x ∈ N) :
    Nat.card {z : P ⧸ N // ∀ x : P, Submodule.Quotient.mk x = z → T x ∈ N} =
      Nat.card (↥N ⧸ (N.map T).comap N.subtype) := by
  let e : P ≃ₗ[O] P := LinearEquiv.ofBijective T hT
  have he1 : ∀ y, T (e.symm y) = y := fun y => e.apply_symm_apply y
  have he2 : ∀ x, e.symm (T x) = x := fun x => e.symm_apply_apply x
  let g : N →ₗ[O] P ⧸ N := N.mkQ ∘ₗ (e.symm : P →ₗ[O] P) ∘ₗ N.subtype
  have hg : ∀ y : N, g y = Submodule.Quotient.mk (e.symm (y : P)) := fun y => rfl
  have hker : LinearMap.ker g = (N.map T).comap N.subtype := by
    ext ⟨y, hy⟩
    rw [LinearMap.mem_ker, hg, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.mem_map]
    constructor
    · intro h
      exact ⟨e.symm y, h, he1 y⟩
    · rintro ⟨x, hx, hxy⟩
      simp only at hxy
      subst hxy
      show e.symm (T x) ∈ N
      rw [he2]
      exact hx
  have hrange : ∀ z : P ⧸ N,
      z ∈ LinearMap.range g ↔ ∀ x : P, Submodule.Quotient.mk x = z → T x ∈ N := by
    intro z
    constructor
    · rintro ⟨⟨y, hy⟩, rfl⟩ x hx
      rw [hg] at hx
      have h1 : x - e.symm y ∈ N := (Submodule.Quotient.eq N).mp hx
      have h2 : T (x - e.symm y) ∈ N := hN _ h1
      rw [map_sub, he1] at h2
      simpa using N.add_mem h2 hy
    · intro h
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N z
      refine ⟨⟨T x, h x rfl⟩, ?_⟩
      rw [hg]
      simp only
      rw [he2]
  calc Nat.card {z : P ⧸ N // ∀ x : P, Submodule.Quotient.mk x = z → T x ∈ N}
      = Nat.card (LinearMap.range g) :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun z => (hrange z).symm))
    _ = Nat.card (↥N ⧸ LinearMap.ker g) := Nat.card_congr g.quotKerEquivRange.toEquiv.symm
    _ = Nat.card (↥N ⧸ (N.map T).comap N.subtype) :=
        Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.monoidAlgebra_exists_right_inv_of_map_field : ∀ {E L G : Type} [Field E] [Field L] [Group G] [Fintype G] (j : E →+* L) (x : MonoidAlgebra E G), (∃ v : MonoidAlgebra L G, MonoidAlgebra.mapRingHom G j x * v = 1) → ∃ v : MonoidAlgebra E G, x * v = 1 := by
  first | exact @GlobalTheory.groupAlgebra_exists_right_inv_of_map | exact GlobalTheory.groupAlgebra_exists_right_inv_of_map | (intros; apply GlobalTheory.groupAlgebra_exists_right_inv_of_map <;> assumption)
end

section

open scoped BigOperators

namespace GlobalTheory.BlockDetPoly

def coeffSub {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (m : ℕ) :
    Subalgebra (MvPolynomial (Fin m) O) (X → MvPolynomial (Fin m) O) where
  carrier := {f | ∀ d, (fun x => AddMonoidAlgebra.coeff (f x) d) ∈ T}
  mul_mem' := by
    intro f g hf hg d
    have : (fun x => AddMonoidAlgebra.coeff ((f * g) x) d) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal d,
        (fun x => AddMonoidAlgebra.coeff (f x) p.1) * (fun x => AddMonoidAlgebra.coeff (g x) p.2) := by
      funext x
      simp [MvPolynomial.coeff_mul, Finset.sum_apply]
    rw [this]
    exact T.sum_mem fun p _ => T.mul_mem (hf _) (hg _)
  add_mem' := by
    intro f g hf hg d
    have : (fun x => AddMonoidAlgebra.coeff ((f + g) x) d) =
        (fun x => AddMonoidAlgebra.coeff (f x) d) + (fun x => AddMonoidAlgebra.coeff (g x) d) := by
      funext x
      simp
    rw [this]
    exact T.add_mem (hf _) (hg _)
  algebraMap_mem' := fun p d => T.algebraMap_mem (AddMonoidAlgebra.coeff p d)

theorem C_mem_coeffSub {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (m : ℕ)
    (t : X → O) (ht : t ∈ T) : (fun x => MvPolynomial.C (t x)) ∈ coeffSub T m := by
  show ∀ d : Fin m →₀ ℕ,
    (fun x => AddMonoidAlgebra.coeff (MvPolynomial.C (t x) : MvPolynomial (Fin m) O) d) ∈ T
  intro d
  rcases eq_or_ne d 0 with rfl | hd
  · simpa using ht
  · have h0 : (fun x => AddMonoidAlgebra.coeff (MvPolynomial.C (t x) : MvPolynomial (Fin m) O) d) = 0 := by
      funext x
      simp [MvPolynomial.coeff_C, Ne.symm hd]
    rw [h0]
    exact T.zero_mem

theorem det_comb_mem {O X Q : Type} [CommRing O] [CommRing Q] (T : Subalgebra O (X → O)) {n : ℕ}
    (R : Subalgebra O (X → Matrix (Fin n) (Fin n) O))
    (hR : ∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, a k ∈ R) →
      ∀ d : Fin m →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det
        (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) ∈ T)
    (φ : O →+* Q) (S : Subalgebra Q (X → Q)) (hS : ∀ t ∈ T, (fun x => φ (t x)) ∈ S)
    {J : Type} [Fintype J] (b : J → X → Matrix (Fin n) (Fin n) O) (hb : ∀ j, b j ∈ R)
    (c : J → Q) : (fun x => Matrix.det (∑ j, c j • (b j x).map φ)) ∈ S := by
  classical

  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let a : Fin (Fintype.card J) → X → Matrix (Fin n) (Fin n) O := fun k => b (e k)

  let A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (Fintype.card J)) (X → O)) :=
    Matrix.of fun i j => ∑ k, MvPolynomial.X k * MvPolynomial.C (fun x => a k x i j)
  have hcoef : ∀ d, AddMonoidAlgebra.coeff A.det d ∈ T := by
    intro d
    have h1 : AddMonoidAlgebra.coeff A.det d = fun x => AddMonoidAlgebra.coeff (Matrix.det
        (∑ k, (MvPolynomial.X k : MvPolynomial (Fin (Fintype.card J)) O) •
          (a k x).map MvPolynomial.C)) d := by
      funext x
      have h2 : MvPolynomial.map (Pi.evalRingHom (fun _ : X => O) x) A.det =
          Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin (Fintype.card J)) O) •
            (a k x).map MvPolynomial.C) := by
        rw [RingHom.map_det]
        congr 1
        ext i j
        simp [A, Matrix.sum_apply]
      rw [← h2, MvPolynomial.coeff_map]
      rfl
    rw [h1]
    exact hR _ a (fun k => hb (e k)) d

  have h3 : ∀ x, Matrix.det (∑ j, c j • (b j x).map φ) =
      MvPolynomial.eval₂ (φ.comp (Pi.evalRingHom (fun _ : X => O) x)) (fun k => c (e k)) A.det := by
    intro x
    rw [← MvPolynomial.coe_eval₂Hom, RingHom.map_det]
    congr 1
    ext i j
    simp only [A, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
      MvPolynomial.eval₂_C, RingHom.comp_apply, Pi.evalRingHom_apply, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    exact (e.sum_comp (fun j' => c j' * φ (b j' x i j))).symm
  have key : (fun x => Matrix.det (∑ j, c j • (b j x).map φ)) =
      ∑ d ∈ A.det.support, (fun x => φ (AddMonoidAlgebra.coeff A.det d x)) *
        algebraMap Q (X → Q) (∏ k, c (e k) ^ d k) := by
    funext x
    rw [h3, MvPolynomial.eval₂_eq', Finset.sum_apply]
    simp
  rw [key]
  exact S.sum_mem fun d _ => S.mul_mem (hS _ (hcoef d)) (S.algebraMap_mem _)

private theorem mem_coeffSub_iff_forall_coeff_mem {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (m : ℕ)
    (f : X → MvPolynomial (Fin m) O) :
    f ∈ coeffSub T m ↔ ∀ d, (fun x => AddMonoidAlgebra.coeff (f x) d) ∈ T := Iff.rfl

theorem main : ∀ {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (n : ℕ) (R : Subalgebra O (X → Matrix (Fin n) (Fin n) O)), (∀ (m : ℕ) (a : Fin m → X → Matrix (Fin n) (Fin n) O), (∀ k, a k ∈ R) → ∀ d : Fin m →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • (a k x).map MvPolynomial.C)) d) ∈ T) → ∀ (m g : ℕ) (Θ : Fin m → Fin g → Fin g → X → Matrix (Fin n) (Fin n) O), (∀ k p q, Θ k p q ∈ R) → ∀ d : Fin m →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det (Matrix.of fun (pa qb : Fin g × Fin n) => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) * MvPolynomial.C (Θ k pa.1 qb.1 x pa.2 qb.2))) d) ∈ T := by
  intro O X _ T n R hR m g Θ hΘ d
  classical

  let ψ : (X → Matrix (Fin n) (Fin n) O) →+* (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)) :=
    RingHom.compLeft (MvPolynomial.C : O →+* MvPolynomial (Fin m) O).mapMatrix X
  have hψ : ∀ (a : X → Matrix (Fin n) (Fin n) O) x, ψ a x = (a x).map MvPolynomial.C :=
    fun _ _ => rfl
  let s : Submonoid (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)) := R.toSubmonoid.map ψ
  let R' : Subalgebra (MvPolynomial (Fin m) O) (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)) :=
    Algebra.adjoin (MvPolynomial (Fin m) O) (s : Set _)

  have hrep : ∀ F ∈ R', ∃ (N : ℕ) (c : Fin N → MvPolynomial (Fin m) O)
      (b : Fin N → X → Matrix (Fin n) (Fin n) O), (∀ j, b j ∈ R) ∧ F = ∑ j, c j • ψ (b j) := by
    intro F hF
    have hF' : F ∈ Submodule.span (MvPolynomial (Fin m) O) (s : Set _) := by
      have h := Algebra.adjoin_eq_span (R := MvPolynomial (Fin m) O)
        (s : Set (X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)))
      rw [Submonoid.closure_eq] at h
      rw [← h]
      exact hF
    obtain ⟨N, c, b, hsum⟩ := Submodule.mem_span_set'.mp hF'
    choose b' hb' hbe using fun j => Submonoid.mem_map.mp (b j).2
    refine ⟨N, c, b', fun j => hb' j, ?_⟩
    rw [← hsum]
    simp [hbe]

  have hR' : ∀ (m' : ℕ) (a : Fin m' → X → Matrix (Fin n) (Fin n) (MvPolynomial (Fin m) O)),
      (∀ k, a k ∈ R') → ∀ d' : Fin m' →₀ ℕ, (fun x => AddMonoidAlgebra.coeff (Matrix.det
        (∑ k, (MvPolynomial.X k : MvPolynomial (Fin m') (MvPolynomial (Fin m) O)) •
          (a k x).map MvPolynomial.C)) d') ∈ coeffSub T m := by
    intro m' a ha d'
    choose N c b hb hab using fun k => hrep (a k) (ha k)
    have hS : ∀ t ∈ T, (fun x => ((MvPolynomial.C : MvPolynomial (Fin m) O →+* MvPolynomial (Fin m')
        (MvPolynomial (Fin m) O)).comp MvPolynomial.C) (t x)) ∈ coeffSub (coeffSub T m) m' :=
      fun t ht => C_mem_coeffSub (coeffSub T m) m' _ (C_mem_coeffSub T m t ht)
    have h := det_comb_mem T R hR ((MvPolynomial.C : MvPolynomial (Fin m) O →+* MvPolynomial (Fin m')
        (MvPolynomial (Fin m) O)).comp MvPolynomial.C) (coeffSub (coeffSub T m) m') hS
      (J := Σ k, Fin (N k)) (fun kj => b kj.1 kj.2) (fun kj => hb kj.1 kj.2)
      (fun kj => MvPolynomial.X kj.1 * MvPolynomial.C (c kj.1 kj.2))
    have heq : ∀ x, (∑ kj : (Σ k, Fin (N k)), (MvPolynomial.X kj.1 * MvPolynomial.C (c kj.1 kj.2) :
          MvPolynomial (Fin m') (MvPolynomial (Fin m) O)) • (b kj.1 kj.2 x).map
          ((MvPolynomial.C : MvPolynomial (Fin m) O →+* MvPolynomial (Fin m')
            (MvPolynomial (Fin m) O)).comp MvPolynomial.C)) =
        ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m') (MvPolynomial (Fin m) O)) •
          (a k x).map MvPolynomial.C := by
      intro x
      ext i j
      simp [hab, hψ, Matrix.sum_apply, Fintype.sum_sigma, Finset.mul_sum, mul_assoc, Finset.sum_apply]
    simp only [heq] at h
    exact (mem_coeffSub_iff_forall_coeff_mem _ _ _).mp h d'

  have hblk : ∀ p q, (fun x => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) •
      (Θ k p q x).map MvPolynomial.C) ∈ R' := by
    intro p q
    have h4 : (fun x => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) •
        (Θ k p q x).map MvPolynomial.C) = ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) • ψ (Θ k p q) := by
      funext x
      simp [Finset.sum_apply, hψ]
    rw [h4]
    exact R'.sum_mem fun k _ =>
      R'.smul_mem (Algebra.subset_adjoin (Submonoid.mem_map.mpr ⟨Θ k p q, hΘ k p q, rfl⟩)) _
  have h5 := (mem_coeffSub_iff_forall_coeff_mem _ _ _).mp (GlobalTheory.BlockDet.main (coeffSub T m) n R' hR' g _ hblk) d
  have h6 : ∀ x, (Matrix.of fun (pa qb : Fin g × Fin n) => (∑ k, (MvPolynomial.X k :
        MvPolynomial (Fin m) O) • (Θ k pa.1 qb.1 x).map MvPolynomial.C) pa.2 qb.2) =
      Matrix.of fun (pa qb : Fin g × Fin n) => ∑ k, (MvPolynomial.X k : MvPolynomial (Fin m) O) *
        MvPolynomial.C (Θ k pa.1 qb.1 x pa.2 qb.2) := by
    intro x
    ext pa qb
    simp [Matrix.sum_apply]
  simp only [h6] at h5
  exact h5

end GlobalTheory.BlockDetPoly
end

section

open scoped BigOperators

theorem _root_.GlobalTheory.T.not_dvd_coeff_aeval_one_add_X_pow_sub_one : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (σ : Type) [Fintype σ] (l μ : ℕ), l.Prime → ϖ ∣ (l : O) → ∀ (F : MvPolynomial σ O) (e : σ → ℕ) (m₀ : σ →₀ ℕ), (∀ m : σ →₀ ℕ, m.degree ≤ ∑ q, m₀ q * l ^ e q → ϖ ^ μ ∣ F.coeff m) → ¬ ϖ ^ (μ + 1) ∣ F.coeff m₀ → (∀ m : σ →₀ ℕ, m ≠ m₀ → ∑ q, m q * l ^ e q ≤ ∑ q, m₀ q * l ^ e q → ϖ ^ (μ + 1) ∣ F.coeff m) → ¬ ϖ ^ (μ + 1) ∣ (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial O) ^ (l ^ e q) - 1) F).coeff (∑ q, m₀ q * l ^ e q) := by
  first | exact @GlobalTheory.not_dvd_coeff_aeval_oneAddX_pow_sub_one | exact GlobalTheory.not_dvd_coeff_aeval_oneAddX_pow_sub_one | (intros; apply GlobalTheory.not_dvd_coeff_aeval_oneAddX_pow_sub_one <;> assumption)
end

section

open scoped PowerSeries Pointwise
namespace GlobalTheory

theorem coeff_zero_smul_mem_map_of_aeval_mul_eq_zero : ∀ {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (T : Module.End O V) (Rp : Polynomial O), Polynomial.aeval T Rp * T = 0 → ∀ (Z : Submodule O V), (∀ z ∈ Z, T z ∈ Z) → ∀ w ∈ Z, w ∈ LinearMap.range T → Rp.coeff 0 • w ∈ Z.map T := by
  first
  | exact @_root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map
  | exact _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map
  | (apply _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map <;> assumption)
  | (intros; apply _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CoefficientMembership.coeff_zero_smul_mem_map ..)

end GlobalTheory
end
