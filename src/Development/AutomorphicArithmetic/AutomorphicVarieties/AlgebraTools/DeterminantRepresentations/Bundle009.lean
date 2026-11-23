module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.RepAlg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle015
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DCoefMem
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.Bundle009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Gcomm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.Bundle007
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

@[expose] public section

section

open Polynomial TensorProduct UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.extDense :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [TopologicalSpace A] [T2Space A] [TopologicalSpace G] (D D' : GDet n A G) (S : Set G), Dense S →
    (∀ i ≤ n, Continuous fun g : G => D.lam i (MonoidAlgebra.single g 1)) →
    (∀ i ≤ n, Continuous fun g : G => D'.lam i (MonoidAlgebra.single g 1)) →
    (∀ g ∈ S, D.chi (MonoidAlgebra.single g 1) = D'.chi (MonoidAlgebra.single g 1)) → D = D' := by
  intro n A G _ _ _ _ _ D D' S hS hc hc' hchi
  have hlam (g : G) (i : ℕ) (hi : i ≤ n) :
      D.lam i (MonoidAlgebra.single g 1) = D'.lam i (MonoidAlgebra.single g 1) := by
    have h := Continuous.ext_on hS (hc i hi) (hc' i hi) (fun x hx => by
      show (-1) ^ i * (D.chi _).coeff (n - i) = (-1) ^ i * (D'.chi _).coeff (n - i)
      rw [hchi x hx])
    exact congrFun h g
  have htoDet (F : GDet n A G) (y : MonoidAlgebra A G) (i : ℕ) :
      F.toDet.lam i y = F.lam i y := by
    have h : F.toDet.chi y = F.chi y := by
      change F.D A[X] (ofT A G A[X] (X ⊗ₜ 1 - 1 ⊗ₜ y)) =
        F.D A[X] (MonoidAlgebra.single 1 X - MonoidAlgebra.mapRingHom G C y)
      congr 1
      rw [map_sub, ofT_tmul, ofT_tmul, map_one, one_smul, MonoidAlgebra.one_def,
        MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rfl
    unfold Det.lam GDet.lam
    rw [h]
  have hdet : D.toDet = D'.toDet := by
    refine UpperTheory.V.CA.d_ext D.toDet D'.toDet (MonoidHom.mrange (MonoidAlgebra.of A G)) ?_ ?_
    · rw [Submodule.eq_top_iff']
      intro x
      induction x using MonoidAlgebra.induction_linear with
      | zero => exact zero_mem _
      | add a b ha hb => exact add_mem ha hb
      | single g r =>
        have h : MonoidAlgebra.single g r = r • MonoidAlgebra.single g (1 : A) := by simp
        rw [h]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
    · rintro x ⟨g, rfl⟩ i _ hi
      rw [htoDet, htoDet]
      exact hlam g i hi
  rw [← GDet.ofDet_toDet D, hdet, GDet.ofDet_toDet]
end

section

open Polynomial UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.amitsurSub :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] (D : GDet n A G) (m : ℕ) (g : Fin m → G) (β : Fin m →₀ ℕ),
    AddMonoidAlgebra.coeff (D.D (MvPolynomial (Fin m) A) (GDet.gen fun j => MonoidAlgebra.single (g j) 1)) β ∈
      Subring.closure {a | ∃ i ≤ n, ∃ s : G, a = D.lam i (MonoidAlgebra.single s 1)} := by
  intro n A G _ _ D m g β
  have h := UpperTheory.V.CA.d_coef_mem D.toDet (MonoidHom.mrange (MonoidAlgebra.of A G))
    (Subring.closure {a | ∃ i ≤ n, ∃ s : G, a = D.lam i (MonoidAlgebra.single s 1)})
    (by
      rintro x ⟨s, rfl⟩ i - h2
      rw [(UpperTheory.V.CA.d_toDet D _).2.1]
      exact Subring.subset_closure ⟨i, h2, s, rfl⟩)
    (fun j => MonoidAlgebra.single (g j) 1) (fun j => ⟨g j, rfl⟩) β
  have e : D.toDet.poly (fun j => MonoidAlgebra.single (g j) (1 : A)) =
      D.D (MvPolynomial (Fin m) A) (GDet.gen fun j => MonoidAlgebra.single (g j) 1) := by
    change D.D _ (ofT A G _ (Det.gen _)) = _
    congr 1

    simp only [Det.gen, GDet.gen, map_sum, ofT_tmul, MvPolynomial.algebraMap_eq]
  rwa [e] at h
end

section

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

theorem UpperTheory.V.AlgebraTools.Det.killsStar :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) (D : GDet n R F.G₀), F.IsPolar O D → ∀ y, D.Kills y → D.Kills (F.star O R n y) := by
  intro l _ F O _ _ R _ _ n D hP y hy B _ _ h
  letI : Algebra O B := ((algebraMap R B).comp (algebraMap O R)).toAlgebra
  haveI : IsScalarTower O R B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨-, -, -, -, -, snat⟩ := AlgebraTools.Det.starApi F O R n
  obtain ⟨bmul, b1, badd, -, binv, -⟩ := AlgebraTools.Det.starApi F O B n
  have hm : MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B) (F.star O R n y)
      = F.star O B n (MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B) y) :=
    (snat B (IsScalarTower.toAlgHom O R B) y).symm
  rw [hm]
  have key : 1 + h * F.star O B n (MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B) y)
      = F.star O B n (1 + MonoidAlgebra.mapRingHom F.G₀ (algebraMap R B) y * F.star O B n h) := by
    rw [badd, bmul, b1, binv]
  rw [key, hP B, (AlgebraTools.Det.gcomm D).1 B]
  exact hy B (F.star O B n h)
end
