module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
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
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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

@[expose] public section

section

open Polynomial UpperTheory.V.W

private theorem UpperTheory.V.AlgebraTools.Det.map_D_mapRingHom_eq {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G)
    {A' : Type} [CommRing A'] (f : A →+* A') (B₀ : Type) [CommRing B₀] [Algebra A B₀]
    (B : Type) [CommRing B] [Algebra A' B] (φ : B₀ →+* B)
    (hφ : ∀ a, φ (algebraMap A B₀ a) = algebraMap A' B (f a)) (x : MonoidAlgebra B₀ G) :
    (D.map f).D B (MonoidAlgebra.mapRingHom G φ x) = φ (D.D B₀ x) := by
  let : Algebra A B := ((algebraMap A' B).comp f).toAlgebra
  exact D.nat B₀ B { φ with commutes' := hφ } x

theorem UpperTheory.V.AlgebraTools.Det.mapApi :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) {A' : Type} [CommRing A'] (f : A →+* A'),
    (∀ y, (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f) ∧
    (∀ i y, (D.map f).lam i (MonoidAlgebra.mapRingHom G f y) = f (D.lam i y)) ∧
    (∀ i g, (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1))) ∧
    (∀ (σ : Type) (x : MonoidAlgebra (MvPolynomial σ A) G), (D.map f).D (MvPolynomial σ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map f) x) =
      MvPolynomial.map f (D.D (MvPolynomial σ A) x)) ∧
    (∀ (m : ℕ) (y : Fin m → MonoidAlgebra A G), (D.map f).D (MvPolynomial (Fin m) A') (GDet.gen fun j => MonoidAlgebra.mapRingHom G f (y j)) =
      MvPolynomial.map f (D.D (MvPolynomial (Fin m) A) (GDet.gen y))) ∧
    (∀ y, D.Kills y → (D.map f).Kills (MonoidAlgebra.mapRingHom G f y)) ∧
    (∀ {A'' : Type} [CommRing A''] (f' : A' →+* A''), (D.map f).map f' = D.map (f'.comp f)) ∧ D.map (RingHom.id A) = D := by
  intro n A G _ _ D A' _ f
  have h1 : ∀ y, (D.map f).chi (MonoidAlgebra.mapRingHom G f y) = (D.chi y).map f := by
    intro y
    have e : MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C (MonoidAlgebra.mapRingHom G f y) =
        MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y) := by
      rw [map_sub, MonoidAlgebra.mapRingHom_single, Polynomial.coe_mapRingHom, Polynomial.map_X,
        ← RingHom.comp_apply, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp,
        ← MonoidAlgebra.mapRingHom_comp, Polynomial.mapRingHom_comp_C]
    show (D.map f).D A'[X] _ = _
    rw [e, UpperTheory.V.AlgebraTools.Det.map_D_mapRingHom_eq D f A[X] A'[X] (Polynomial.mapRingHom f) (fun a => by simp)]
    rfl
  have h2 : ∀ i y, (D.map f).lam i (MonoidAlgebra.mapRingHom G f y) = f (D.lam i y) := by
    intro i y
    simp only [GDet.lam, h1, Polynomial.coeff_map, map_mul, map_pow, map_neg, map_one]
  have h4 : ∀ (σ : Type) (x : MonoidAlgebra (MvPolynomial σ A) G), (D.map f).D (MvPolynomial σ A') (MonoidAlgebra.mapRingHom G (MvPolynomial.map f) x) =
      MvPolynomial.map f (D.D (MvPolynomial σ A) x) := fun σ x =>
    UpperTheory.V.AlgebraTools.Det.map_D_mapRingHom_eq D f _ _ (MvPolynomial.map f) (fun a => MvPolynomial.map_C f a) x
  refine ⟨h1, h2, ?_, h4, ?_, ?_, ?_, ?_⟩
  · intro i g
    simpa using h2 i (MonoidAlgebra.single g 1)
  · intro m y
    rw [← h4]
    congr 1
    ext g
    simp [GDet.gen]
  · intro y hy B _ _ h
    let : Algebra A B := ((algebraMap A' B).comp f).toAlgebra
    have := hy B h
    rw [show MonoidAlgebra.mapRingHom G (algebraMap A B) y = MonoidAlgebra.mapRingHom G (algebraMap A' B) (MonoidAlgebra.mapRingHom G f y) from by
      rw [← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp]; rfl] at this
    exact this
  · intro A'' _ f'
    rfl
  · cases D
    simp only [GDet.map]
    congr 1
    funext B _ i
    congr 1
    exact Algebra.algebra_ext _ _ (fun r => rfl)
end

section

open Polynomial UpperTheory.V.W

private theorem coeff_scale {A : Type} [CommRing A] {m : ℕ} (P : MvPolynomial (Fin m) A) (s : Fin m →₀ ℕ) :
    AddMonoidAlgebra.coeff ((MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X])) P).coeff s.degree)
      s
      = AddMonoidAlgebra.coeff P s := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have h : MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))
        (MvPolynomial.monomial u a) = C (MvPolynomial.monomial u a) * X ^ u.degree := by
      rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq, Finsupp.prod, Finsupp.prod,
        show u.degree = ∑ i ∈ u.support, u i from rfl]
      simp only [mul_pow, Finset.prod_mul_distrib, ← C_pow, ← map_prod, Finset.prod_pow_eq_pow_sum,
        Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq, map_mul]
      ring
    rw [h, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial_apply, MvPolynomial.coeff_monomial]
    split_ifs with h1 h2 h2
    · rw [MvPolynomial.coeff_monomial, if_pos h2]
    · rw [MvPolynomial.coeff_monomial, if_neg h2]
    · exact absurd (congrArg Finsupp.degree h2) h1
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), Polynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, MvPolynomial.coeff_add]

theorem UpperTheory.V.AlgebraTools.Det.genHomog :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (m : ℕ) (y : Fin m → MonoidAlgebra A G),
    (D.D (MvPolynomial (Fin m) A) (GDet.gen y)).IsHomogeneous n := by
  intro n A G _ _ D m y
  have hφ : (MvPolynomial.aeval (fun j => (C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))) =
      (Polynomial.CAlgHom : MvPolynomial (Fin m) A →ₐ[A] (MvPolynomial (Fin m) A)[X]) :=
    MvPolynomial.algHom_ext fun i => by
      change _ = Polynomial.C (MvPolynomial.X i)
      simp
  have hC : MvPolynomial.aeval (fun j => (C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))
      (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) = C (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
    rw [hφ]
    rfl
  have hgen (B : Type) [CommRing B] [Algebra A B] (b : Fin m → B) :
      D.D B (∑ j, b j • MonoidAlgebra.mapRingHom G (algebraMap A B) (y j)) =
        MvPolynomial.aeval b (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
    rw [← D.nat (MvPolynomial (Fin m) A) B (MvPolynomial.aeval b)]
    congr 1

    simp only [GDet.gen, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext g
    simp [MonoidAlgebra.mapRingHom]
  have key : MvPolynomial.aeval (fun j => (X * C (MvPolynomial.X j) : (MvPolynomial (Fin m) A)[X]))
      (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) = X ^ n * C (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) := by
    rw [← hgen _, ← hC, ← hgen _, ← D.homog,
      Finset.smul_sum]
    simp only [mul_smul]
  intro d hd
  have h1 := coeff_scale (D.D (MvPolynomial (Fin m) A) (GDet.gen y)) d
  rw [key, mul_comm, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial] at h1
  have hw : Finsupp.weight 1 d = d.degree := by
    simp only [Finsupp.weight_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rfl
  rw [hw]
  by_contra hne
  simp [hne] at h1
  exact hd h1.symm
end
