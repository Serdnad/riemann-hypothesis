module

public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
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
public import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IncIdealPrime.proof (h₁ : IncidenceGeneric.Statement) : IncIdealPrime.Statement := by
  intro F _ n k P hP hrel
  have := hP
  obtain ⟨j, hj⟩ := hrel
  have hξ : genPt P j ≠ 0 := by
    unfold genPt
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hj
  set c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P) := Pi.single j (genPt P j)⁻¹ with hc
  have hsum : ∑ l, c l * genPt P l = 1 := by
    rw [Finset.sum_eq_single j]
    · simp [hc, inv_mul_cancel₀ hξ]
    · intro b _ hb
      simp [hc, Pi.single_eq_of_ne hb]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hker : incIdeal P k =
      RingHom.ker (aeval (genSubst (k := k) (genPt P) c) :
        MvPolynomial (Fin k × Fin n) F →ₐ[F]
          MvPolynomial (Fin k × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ P))) := by
    ext g
    rw [RingHom.mem_ker]
    exact h₁ F n k P c hsum g
  rw [hker]
  exact RingHom.ker_isPrime _

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial IsLocalRing

theorem OrdPolynomialLocalization.comap_C_map_C {R : Type*} [CommRing R] (σ : Type*) (p : Ideal R) :
    Ideal.comap (C : R →+* MvPolynomial σ R) (Ideal.map (C : R →+* MvPolynomial σ R) p) = p := by
  classical
  ext r
  rw [Ideal.mem_comap, MvPolynomial.mem_map_C_iff]
  constructor
  · intro h
    simpa using h 0
  · intro h m
    rw [coeff_C]
    split_ifs
    · exact h
    · exact p.zero_mem

theorem OrdPolynomialLocalization.proof : OrdPolynomialLocalization.Statement := by
  intro R _ σ p _ _ x
  set P := Ideal.map (C : R →+* MvPolynomial σ R) p with hPdef
  have : P.LiesOver p := ⟨by
    rw [Ideal.under, MvPolynomial.algebraMap_eq, hPdef]
    exact (OrdPolynomialLocalization.comap_C_map_C σ p).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p P
  set A := Localization.AtPrime p
  set B := Localization.AtPrime P
  have : IsLocalHom (algebraMap A B) :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom p P (algebraMap R (MvPolynomial σ R))
      Ideal.LiesOver.over))
  have hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      IsScalarTower.algebraMap_eq R (MvPolynomial σ R) B, ← Ideal.map_map, MvPolynomial.algebraMap_eq,
      ← hPdef, Localization.AtPrime.map_eq_maximalIdeal]
  have h1 : Module.length B (B ⧸ maximalIdeal B) = 1 := by
    have : IsSimpleModule B (B ⧸ maximalIdeal B) :=
      isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal B, ⟨LinearEquiv.refl _ _⟩⟩
    exact Module.length_eq_one _ _
  have key := IsLocalRing.length_baseChange A B (A ⧸ Ideal.span {algebraMap R A x})
  rw [hm, h1, mul_one, ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
    (Ideal.span {algebraMap R A x})).toLinearEquiv.length_eq, Ideal.map_span,
    Set.image_singleton, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R (MvPolynomial σ R) B, MvPolynomial.algebraMap_eq] at key
  exact key

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def GenericLinearTrdeg.Statement : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (N k d : ℕ) (η : Fin N → E),
    Algebra.trdeg F (Algebra.adjoin F (Set.range η)) = d →
      Algebra.trdeg F (Algebra.adjoin F
        (Set.range (fun ij : Fin k × Fin N => (X ij : MvPolynomial (Fin k × Fin N) E)) ∪
          Set.range (fun i : Fin k => ∑ m, X (i, m) * C (η m)))) = ((k * N + min k d : ℕ) : Cardinal)

def IncIdealDim.Statement : Prop :=
  ∀ (F : Type) [Field F] (n k d : ℕ) (P : Ideal (MvPolynomial (Fin n) F)), IsProjPrime P →
    ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞) →
      ringKrullDim (MvPolynomial (Fin k × Fin n) F ⧸ incIdeal P k) =
        ((k * n - k + min k d : ℕ) : WithBot ℕ∞)

def ChowFormBirational.Statement : Prop :=
  ∀ (F : Type) [Field F] [CharZero F] (n k : ℕ) (P : Ideal (MvPolynomial (Fin n) F))
    (g : MvPolynomial (Fin (k + 1) × Fin n) F) (c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ P)),
    IsProjPrime P → IsChowForm P (k + 1) g → ∑ j, c j * genPt P j = 1 →
      ∃ t : Fin n → F, (∑ l, C (t l) * pderiv (0, l) g) ∉ incIdeal P (k + 1) ∧
        ∀ m, aeval (genSubst (genPt P) c) (pderiv (0, m) g) *
              C (∑ l, algebraMap F (FractionRing (MvPolynomial (Fin n) F ⧸ P)) (t l) * genPt P l) =
            aeval (genSubst (genPt P) c) (∑ l, C (t l) * pderiv (0, l) g) * C (genPt P m)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def AffineChartTrdeg.Statement : Prop :=
  ∀ (F : Type) [Field F] (n d : ℕ) (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]
    (j : Fin n), IsProjPrime P →
    ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ((d + 1 : ℕ) : WithBot ℕ∞) → X j ∉ P →
      Algebra.trdeg F (Algebra.adjoin F (Set.range fun m => genPt P m * (genPt P j)⁻¹)) =
        ((d : ℕ) : Cardinal)

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartHomogenise.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (Q : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F),
    Q.IsPrime → linForm t - 1 ∈ Q →
      ∃ W : Ideal (MvPolynomial (Fin n) F), IsProjPrime W ∧ linForm t ∉ W ∧
        W ⊔ Ideal.span {linForm t - 1} = Q ∧
        ∀ J : Ideal (MvPolynomial (Fin n) F), IsHomogIdeal J → J ≤ Q → J ≤ W

def ChartDehomog.Statement : Prop :=
  ∀ (F : Type) [Field F] (n : ℕ) (W : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
    (G : MvPolynomial (Fin n) F) (d : ℕ),
    W.IsPrime → IsHomogIdeal W → linForm t ∉ W → G.IsHomogeneous d →
      G ∈ W ⊔ Ideal.span {linForm t - 1} → G ∈ W

def ComponentOfIncIdeal.Statement : Prop :=
  ∀ (F : Type) [Field F] (n e : ℕ) (I W : Ideal (MvPolynomial (Fin n) F)) (u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F),
    IsProjPrime I → ringKrullDim (MvPolynomial (Fin n) F ⧸ I) = ((e + 1 : ℕ) : WithBot ℕ∞) →
      linForm u ∉ I → IsProjPrime W → I ⊔ Ideal.span {linForm u} ≤ W → Prime q →
        incIdeal W e ≤ Ideal.span {q} →
          W ∈ relComps (I ⊔ Ideal.span {linForm u}) ∧ incIdeal W e = Ideal.span {q}

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem isHomogIdeal_iff_isHomogeneous_degree {R : Type*} [CommRing R] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) R)) :
    IsHomogIdeal I ↔ I.IsHomogeneous (homogeneousSubmodule (Fin n) R) := by
  constructor
  · intro h i r hr
    convert h r hr i using 1
    exact decomposition.decompose'_apply r i
  · intro h f hf d
    exact homogeneousComponent_mem_of_mem h hf d

theorem MinimalPrimeHomog.proof : MinimalPrimeHomog.Statement := by
  intro F _ n J W hJ hW
  rw [isHomogIdeal_iff_isHomogeneous_degree] at hJ ⊢
  have hWp : W.IsPrime := hW.1.1
  have hcore : (W.homogeneousCore (homogeneousSubmodule (Fin n) F)).toIdeal = W := by
    apply le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _)
    refine hW.2 ⟨hWp.homogeneousCore, ?_⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
    exact hJ.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hW.1.2)
  rw [← hcore]
  exact (W.homogeneousCore _).isHomogeneous

end GroundTheory.Heights₂.Heights
end
