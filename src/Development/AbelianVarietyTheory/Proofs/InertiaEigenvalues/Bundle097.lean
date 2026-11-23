module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisBorderedMatrixNormalFormInvariants
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle063
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle064
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle066
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle067
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle065

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallis_borderedMatrix_normalForm_invariants : ∀ (k : Type) [Field k] (r : ℕ), (∀ (g : GL (Fin r) k) (Y : Gl r k), inv (act g Y) = inv Y) ∧ (∀ a : Inv r k, inv (sec a) = a) ∧ (∀ Y : Gl r k, Cm Y * Bm Y = hankel (inv Y)) ∧ (∀ (g h : GL (Fin r) k) (Y : Gl r k), act (g * h) Y = act g (act h Y)) ∧ ∀ Y Y₁ : Gl r k, Delta (inv Y) ≠ 0 → inv Y₁ = inv Y → ∃! g : GL (Fin r) k, act g Y = Y₁ ∧ (g : Matrix (Fin r) (Fin r) k) * Bm Y = Bm Y₁ := by
  first | exact @GlobalTheory.JR.normalForm_invariants | exact GlobalTheory.JR.normalForm_invariants | (intros; apply GlobalTheory.JR.normalForm_invariants <;> assumption)
end

section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial

theorem _root_.GlobalTheory.T.isUnit_det_conjugationMatrix_integralBasis :
    ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), (∀ x, φ (K.c x) = K'.c (φ x)) →
      (letI : Algebra K.E K'.E := φ.toAlgebra
       ∀ w : Module.Basis (Fin d) K.E K'.E,
         (∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔
           ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k) →
         ∃ u : K.O, IsUnit u ∧
           algebraMap K.O K.E u = (Matrix.of fun m l => w.repr (K'.c (w l)) m).det) := by
  intro K K' d φ hφ
  let : Algebra K.E K'.E := φ.toAlgebra
  intro w hw
  have hunit : ∃ u : K.O, IsUnit u ∧
      algebraMap K.O K.E u = (Matrix.of fun m l => w.repr (K'.c (w l)) m).det := by
    set C : Matrix (Fin d) (Fin d) K.E := Matrix.of fun m l => w.repr (K'.c (w l)) m with hC
    have hsm : ∀ (e : K.E) (x : K'.E), e • x = φ e * x := fun e x => rfl
    have hint : ∀ m l, ∃ a : K.O, algebraMap K.O K.E a = C m l := by
      intro m l
      have h1 : ∃ y : K'.O, algebraMap K'.O K'.E y = w l := by
        rw [hw]
        intro k
        rw [w.repr_self]
        by_cases h : l = k
        · subst h; exact ⟨1, by simp⟩
        · exact ⟨0, by simp [h]⟩
      obtain ⟨y, hy⟩ := h1
      obtain ⟨y', hy'⟩ := K'.c_int y
      have h2 : ∃ y : K'.O, algebraMap K'.O K'.E y = K'.c (w l) := ⟨y', by rw [← hy', hy]⟩
      exact (hw _).1 h2 m
    choose A hA using hint
    have hrep : ∀ (x : K'.E) (n : Fin d), w.repr (K'.c x) n = ∑ m, K.c (w.repr x m) * C n m := by
      intro x n
      have hx : K'.c x = ∑ m, K.c (w.repr x m) • K'.c (w m) := by
        conv_lhs => rw [← w.sum_repr x]

        rw [map_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hsm, hsm, map_mul, ← hφ]

      rw [hx, map_sum, Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      rfl
    have hCC : C * (K.c : K.E →+* K.E).mapMatrix C = 1 := by
      ext n l
      have h := hrep (K'.c (w l)) n
      rw [K'.c_c, w.repr_self, Finsupp.single_apply] at h
      rw [Matrix.mul_apply, Matrix.one_apply]
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.coe_coe]
      rw [eq_comm]
      convert h using 1
      · exact if_congr eq_comm rfl rfl
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [mul_comm]
      rfl
    have hdet : C.det * K.c C.det = 1 := by
      have h := congrArg Matrix.det hCC
      rw [Matrix.det_mul, Matrix.det_one, ← RingHom.map_det] at h
      exact h
    have hdetA : algebraMap K.O K.E (Matrix.of A).det = C.det := by
      rw [RingHom.map_det]
      congr 1
      ext m l
      simp [hA]
    refine ⟨(Matrix.of A).det, ?_, hdetA⟩
    obtain ⟨β, hβ⟩ := K.c_int (Matrix.of A).det
    apply IsUnit.of_mul_eq_one β
    apply IsFractionRing.injective K.O K.E
    rw [map_mul, ← hβ, hdetA, hdet, map_one]
  exact hunit
end

section

open GlobalTheory.UnitLemma Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.UnitLemma.BaseChange

variable {K : UQ} (B : InvAlg K)

theorem herm_sum_left {ι : Type} (s : Finset ι) (x : B.A) (f : ι → B.A) (z : B.A) :
    B.herm x (∑ k ∈ s, f k) z = ∑ k ∈ s, B.herm x (f k) z := by
  unfold InvAlg.herm

  rw [Finset.mul_sum, Finset.sum_mul, map_sum]

theorem herm_sum_right {ι : Type} (s : Finset ι) (x y : B.A) (f : ι → B.A) :
    B.herm x y (∑ k ∈ s, f k) = ∑ k ∈ s, B.herm x y (f k) := by
  unfold InvAlg.herm

  rw [map_sum, Finset.mul_sum, map_sum]

theorem herm_basis_change (x : B.A) {n : ℕ} (e e' : Module.Basis (Fin n) K.E B.A)
    (he : ∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0) (i j : Fin n) :
    B.herm x (e' i) (e' j) = ∑ k, e.toMatrix e' k i * K.c (e.toMatrix e' k j) := by
  have hi := e.sum_toMatrix_smul_self e' i
  have hj := e.sum_toMatrix_smul_self e' j
  rw [← hi, ← hj, herm_sum_left]
  simp_rw [herm_sum_right, GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, he]
  simp [mul_ite, Finset.sum_ite_eq]

theorem orthonormal_iff_unitary : ∀ (K : UQ) (B : InvAlg K) (x : B.A) (n : ℕ) (e e' : Module.Basis (Fin n) K.E B.A),
    (∀ i j, B.herm x (e i) (e j) = if i = j then 1 else 0) →
    ((∀ i j, B.herm x (e' i) (e' j) = if i = j then 1 else 0) ↔ ((e.toMatrix e').map K.c)ᵀ * e.toMatrix e' = 1) := by
  intro K B x n e e' he
  have key := herm_basis_change B x e e' he
  have hm : ∀ i j, (((e.toMatrix e').map K.c)ᵀ * e.toMatrix e') j i = B.herm x (e' i) (e' j) := by
    intro i j
    rw [key, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by simp [mul_comm]
  constructor
  · intro h'
    ext j i
    rw [hm, h', Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  · intro hu i j
    rw [← hm, hu, Matrix.one_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij, Ne.symm hij]

end GlobalTheory.UnitLemma.BaseChange
end
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.exists_unit_sigma_eq_mul_invAlg : ∀ (K : UQ) (B : InvAlg K) (u : B.A), u * B.σ u = 1 → ∃ β : B.Aˣ, B.σ (β : B.A) = β * u := by
  first | exact @GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma | exact GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma | (intros; apply GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.fg_units_quot_integralUnits_reduced_finite_algebra : ∀ (K : UQ), (∀ (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L)) → ∀ (A : Type) [CommRing A] [Algebra K.O A] [Algebra K.E A] [IsScalarTower K.O K.E A] [Module.Finite K.E A], IsReduced A → Group.FG (Aˣ ⧸ intUnits K.O A) := by
  first | exact @GlobalTheory.UnitLemma.NormUnits.units_quot_intUnits_fg | exact GlobalTheory.UnitLemma.NormUnits.units_quot_intUnits_fg | (intros; apply GlobalTheory.UnitLemma.NormUnits.units_quot_intUnits_fg <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.isIntegral_iff_forall_maximalSpectrum_residue : ∀ (K : UQ) (B : InvAlg K), IsReduced B.A → ∀ x : B.A, IsIntegral K.O x ↔ ∀ m : MaximalSpectrum B.A, IsIntegral K.O (Ideal.Quotient.mk m.asIdeal x) := by
  first | exact @GlobalTheory.UnitLemma.isIntegral_iff_forall_maximalSpectrum | exact GlobalTheory.UnitLemma.isIntegral_iff_forall_maximalSpectrum | (intros; apply GlobalTheory.UnitLemma.isIntegral_iff_forall_maximalSpectrum <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.unit_prescribed_residue_reduced_finite_algebra : ∀ (K : UQ) (B : InvAlg K), IsReduced B.A → ∀ (m : MaximalSpectrum B.A) (z : B.A ⧸ m.asIdeal), z ≠ 0 → ∃ y : B.Aˣ, Ideal.Quotient.mk m.asIdeal (y : B.A) = z ∧ ∀ m' : MaximalSpectrum B.A, m' ≠ m → Ideal.Quotient.mk m'.asIdeal (y : B.A) = 1 := by
  first | exact @GlobalTheory.UnitLemma.unit_prescribed_residue | exact GlobalTheory.UnitLemma.unit_prescribed_residue | (intros; apply GlobalTheory.UnitLemma.unit_prescribed_residue <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.fg_units_quot_integralUnits_finite_field_ext : ∀ (K : UQ) (L : Type) [Field L] [Algebra K.O L] [Algebra K.E L] [IsScalarTower K.O K.E L] [FiniteDimensional K.E L], Group.FG (Lˣ ⧸ intUnits K.O L) := by
  first | exact @GlobalTheory.FieldUnitsQuotFG.fg_units_quot | exact GlobalTheory.FieldUnitsQuotFG.fg_units_quot | (intros; apply GlobalTheory.FieldUnitsQuotFG.fg_units_quot <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.isFullLattice_prod_of_comap_inl_map_snd : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)), IsLat K.O K.E (M.comap (LinearMap.inl K.O B₁.A B₂.A)) → IsLat K.O K.E (M.map (LinearMap.snd K.O B₁.A B₂.A)) → IsLat K.O K.E M := by
  first | exact @GlobalTheory.UnitLemma.isLat_of_comap_inl_of_map_snd | exact GlobalTheory.UnitLemma.isLat_of_comap_inl_of_map_snd | (intros; apply GlobalTheory.UnitLemma.isLat_of_comap_inl_of_map_snd <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.kappaSum_zero_and_stableSum_mul_zero_of_not_integral : ∀ (K : UQ) (B₁ B₂ : InvAlg K), ¬ (IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g) → InvAlg.kapSum B₁ B₂ = 0 ∧ B₁.stSum * B₂.stSum = 0 := by
  first | exact @GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral | exact GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral | (intros; apply GlobalTheory.UnitLemma.kapSum_eq_zero_and_stSum_mul_eq_zero_of_not_isIntegral <;> assumption)
end

section

open GlobalTheory.UnitLemma Polynomial

theorem _root_.GlobalTheory.T.finite_submodules_between_mulLeftImage_lattice : ∀ (K : UQ) (B : InvAlg K) (L : Submodule K.O B.A), IsLat K.O K.E L → ∀ c : K.O, c ≠ 0 → {M : Submodule K.O B.A | mulLat K.O (algebraMap K.O B.A c) L ≤ M ∧ M ≤ L}.Finite := by
  first | exact @GlobalTheory.UnitLemma.finite_between_mulLat | exact GlobalTheory.UnitLemma.finite_between_mulLat | (intros; apply GlobalTheory.UnitLemma.finite_between_mulLat <;> assumption)
end

section

namespace GlobalTheory.UnitLemma

open Polynomial

theorem InvAlg.isReduced_of_separable_P : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → IsReduced B.A := by
  intro K B h
  obtain ⟨e, he⟩ := exists_basis_pow_of_separable K B h
  have h2 : minpoly K.E (LinearMap.mulLeft K.E B.g) = minpoly K.E B.g :=
    minpoly.algHom_eq (Algebra.lmul K.E B.A) (Algebra.lmul_injective) B.g
  have hms : (minpoly K.E B.g).Separable :=
    h.of_dvd (h2 ▸ LinearMap.minpoly_dvd_charpoly (LinearMap.mulLeft K.E B.g))
  have hsurj : ∀ a : B.A, ∃ q : K.E[X], aeval B.g q = a := by
    intro a
    have hle : Submodule.span K.E (Set.range e) ≤
        Subalgebra.toSubmodule (Algebra.adjoin K.E ({B.g} : Set B.A)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      rw [he]
      exact Subalgebra.pow_mem (Algebra.adjoin K.E ({B.g} : Set B.A))
        (Algebra.subset_adjoin (Set.mem_singleton B.g)) _
    have ha : a ∈ Algebra.adjoin K.E ({B.g} : Set B.A) := hle (e.span_eq ▸ Submodule.mem_top)
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨q, hq⟩ := ha
    exact ⟨q, hq⟩
  refine ⟨fun n hn => ?_⟩
  obtain ⟨k, hk⟩ := hn
  obtain ⟨q, rfl⟩ := hsurj n
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · subst h0
    rw [pow_zero] at hk
    haveI := subsingleton_of_zero_eq_one hk.symm
    exact Subsingleton.elim _ _
  have hdk : minpoly K.E B.g ∣ q ^ k := minpoly.dvd _ _ (by rw [map_pow, hk])
  obtain ⟨r, hr⟩ := (hms.squarefree.dvd_pow_iff_dvd h0.ne').1 hdk
  rw [hr, map_mul, minpoly.aeval, zero_mul]

end GlobalTheory.UnitLemma
end
