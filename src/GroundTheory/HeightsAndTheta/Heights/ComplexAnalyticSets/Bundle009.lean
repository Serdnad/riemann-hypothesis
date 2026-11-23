module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Kaehler.Basic
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
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.Height

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

noncomputable section

def DiscrAdjoin.Statement : Prop :=
  ∀ (R K L : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (ℓ : L), IsIntegral R ℓ →
    IntermediateField.adjoin K {ℓ} = ⊤ →
      (minpoly R ℓ).natDegree = Module.finrank K L ∧ (minpoly R ℓ).discr ≠ 0 ∧
      ∀ z : L, IsIntegral R z → (minpoly R ℓ).discr • z ∈ Algebra.adjoin R {ℓ}

end

end GroundTheory.Heights₂.Heights.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

noncomputable section

def poincareDeepWeight (z : ℂ) : ℝ :=
  if Real.log (‖z‖ ^ 2) < -Real.exp 1 then (‖z‖ ^ 2 * Real.log (‖z‖ ^ 2) ^ 2)⁻¹ else 0

def TubeDeepWeightMass.Statement : Prop :=
  ∀ (d : ℕ) (R : ℝ),
    ∫⁻ z in {z : Fin (d + 1) → ℂ | ∀ i : Fin d, ‖z i.succ‖ ≤ R}, ENNReal.ofReal (poincareDeepWeight (z 0)) < ⊤

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

def DerivationCotangentIndependent.Statement : Prop :=
  ∀ (T : Type) [CommRing T] (P : Ideal T) [P.IsPrime] (h : ℕ) (D : Fin h → Derivation ℤ T T)
    (f : Fin h → T), (∀ i, f i ∈ P) → (Matrix.of fun i j => D j (f i)).det ∉ P →
      ∀ a : Fin h → Localization.AtPrime P,
        ∑ i, a i * algebraMap T (Localization.AtPrime P) (f i) ∈
            maximalIdeal (Localization.AtPrime P) ^ 2 →
          ∀ i, a i ∈ maximalIdeal (Localization.AtPrime P)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Metric MeasureTheory

def HausdorffNullComplementConnected.Statement : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] (D C : Set E),
    IsOpen D → IsPreconnected D → μH[(Module.finrank ℝ E : ℝ) - 1] C = 0 → IsPreconnected (D \ C)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def DerivationAdicCompletion.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (I : Ideal R) (D : Derivation ℤ R R),
    ∃ D' : Derivation ℤ (AdicCompletion I R) (AdicCompletion I R),
      ∀ r : R, D' (algebraMap R (AdicCompletion I R) r) = algebraMap R (AdicCompletion I R) (D r)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def CompletionNormalDescent.Statement : Prop :=
  ∀ (R : Type) [CommRing R] (J : Ideal R), IsNoetherianRing R → J ≤ (⊥ : Ideal R).jacobson →
    IsDomain (AdicCompletion J R) → IsIntegrallyClosed (AdicCompletion J R) →
      IsDomain R ∧ IsIntegrallyClosed R

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def AdicCompletionRegular.Statement : Prop :=
  ∀ (R : Type) [CommRing R], IsNoetherianRing R → ∀ (M : Ideal R) [M.IsMaximal],
    IsRegularLocalRing (Localization.AtPrime M) → IsRegularLocalRing (AdicCompletion M R)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

abbrev primeFibreLocalRing (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : Ideal S)
    [P.IsPrime] : Type _ :=
  Localization.AtPrime P ⧸
    Ideal.map (algebraMap S (Localization.AtPrime P)) (Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) P))

def FlatNormalFibres.Statement : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S],
    IsNoetherianRing R → IsNoetherianRing S → IsLocalRing S → Module.Flat R S →
      IsDomain R → IsIntegrallyClosed R →
      (∀ (P : Ideal S) [P.IsPrime],
        IsDomain (primeFibreLocalRing R P) ∧ IsIntegrallyClosed (primeFibreLocalRing R P)) →
        IsDomain S ∧ IsIntegrallyClosed S

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

def FlatDimFormula.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B],
    IsNoetherianRing A → IsNoetherianRing B → IsLocalHom (algebraMap A B) → Module.Flat A B →
      ringKrullDim B = ringKrullDim A + ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

def FlatLocalRegularElement.Statement : Prop :=
  ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B],
    IsNoetherianRing A → IsNoetherianRing B → IsLocalHom (algebraMap A B) →
    ∀ (M : Type) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M],
      Module.Finite B M → Module.Flat A M →
      ∀ y ∈ maximalIdeal B,
        IsSMulRegular (M ⧸ ((maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B M))) y →
        IsSMulRegular M y ∧ Module.Flat A (QuotSMulTop y M)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open IsLocalRing

section FlatLocal

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R] [IsLocalRing S]
  [IsLocalHom (algebraMap R S)]

theorem isLocalRing_closedFibre :
    IsLocalRing (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  have : Nontrivial (S ⧸ (maximalIdeal R).map (algebraMap R S)) :=
    Ideal.Quotient.nontrivial_iff.mpr (map_maximalIdeal_lt_top (algebraMap R S)).ne
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem ringKrullDim_eq_add_ringKrullDim_closedFibre [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Flat R S] :
    ringKrullDim S = ringKrullDim R + ringKrullDim (S ⧸ (maximalIdeal R).map (algebraMap R S)) := by
  have := isLocalRing_closedFibre (R := R) (S := S)
  have : (maximalIdeal S).LiesOver (maximalIdeal R) := ⟨(maximalIdeal_comap (algebraMap R S)).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R) (maximalIdeal S)
  rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at h
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim,
    ← maximalIdeal_height_eq_ringKrullDim, h, WithBot.coe_add]

theorem isRegularLocalRing_of_flat_of_closedFibre [IsNoetherianRing S] [Module.Flat R S]
    (hR : IsRegularLocalRing R) (hF : IsRegularLocalRing (S ⧸ (maximalIdeal R).map (algebraMap R S))) :
    IsRegularLocalRing S := by
  have : IsNoetherianRing R := by have := hR; infer_instance
  have := isLocalRing_closedFibre (R := R) (S := S)
  set J := (maximalIdeal R).map (algebraMap R S)
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [ringKrullDim_eq_add_ringKrullDim_closedFibre (R := R), ← (isRegularLocalRing_iff R).mp hR,
    ← (isRegularLocalRing_iff (S ⧸ J)).mp hF]
  suffices h : (maximalIdeal S).spanFinrank ≤
      (maximalIdeal R).spanFinrank + (maximalIdeal (S ⧸ J)).spanFinrank by
    exact_mod_cast h
  have fgR := (maximalIdeal R).fg_of_isNoetherianRing
  have fgF := (maximalIdeal (S ⧸ J)).fg_of_isNoetherianRing
  set s := (maximalIdeal R).generators
  set t := (maximalIdeal (S ⧸ J)).generators
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  let lift : S ⧸ J → S := Function.surjInv hsurj
  set t' := lift '' t
  have ht' : Ideal.Quotient.mk J '' t' = t := by
    rw [Set.image_image]
    simp [lift, Function.surjInv_eq hsurj]
  have : IsLocalHom (Ideal.Quotient.mk J) := IsLocalHom.of_surjective _ hsurj
  have hcomap : (maximalIdeal (S ⧸ J)).comap (Ideal.Quotient.mk J) = maximalIdeal S :=
    maximalIdeal_comap _
  have heq : maximalIdeal S = Ideal.span (algebraMap R S '' s ∪ t') := by
    apply le_antisymm
    · intro x hx
      have hx' : Ideal.Quotient.mk J x ∈ Ideal.map (Ideal.Quotient.mk J) (Ideal.span t') := by
        rw [Ideal.map_span, ht']
        change Ideal.Quotient.mk J x ∈ Submodule.span (S ⧸ J) t
        rw [Submodule.span_generators, ← Ideal.mem_comap, hcomap]
        exact hx
      rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker] at hx'
      rw [Ideal.span_union, sup_comm, ← Ideal.map_span]
      change x ∈ Submodule.span S t' ⊔ Ideal.map (algebraMap R S) (Submodule.span R s)
      rw [Submodule.span_generators]
      exact hx'
    · rw [Ideal.span_le, Set.union_subset_iff]
      constructor
      · rintro _ ⟨y, hy, rfl⟩
        exact map_maximalIdeal_le (algebraMap R S) (Ideal.mem_map_of_mem _ (Submodule.FG.generators_mem _ hy))
      · rintro _ ⟨y, hy, rfl⟩
        rw [SetLike.mem_coe, ← hcomap, Ideal.mem_comap, Function.surjInv_eq hsurj]
        exact Submodule.FG.generators_mem _ hy
  have fins := Submodule.FG.finite_generators fgR
  have fint := Submodule.FG.finite_generators fgF
  rw [heq, ← Submodule.FG.generators_ncard fgR, ← Submodule.FG.generators_ncard fgF]
  refine (Submodule.spanFinrank_span_le_ncard_of_finite ((fins.image _).union (fint.image _))).trans ?_
  exact (Set.ncard_union_le _ _).trans (add_le_add (Set.ncard_image_le fins) (Set.ncard_image_le fint))

end FlatLocal

section Localized

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (P : Ideal B) [P.IsPrime]

theorem map_maximalIdeal_localization_eq :
    letI := Localization.AtPrime.algebraOfLiesOver (P.under A) P
    (maximalIdeal (Localization.AtPrime (P.under A))).map
        (algebraMap (Localization.AtPrime (P.under A)) (Localization.AtPrime P)) =
      Ideal.map (algebraMap B (Localization.AtPrime P))
        (Ideal.map (algebraMap A B) (Ideal.comap (algebraMap A B) P)) := by
  let := Localization.AtPrime.algebraOfLiesOver (P.under A) P
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map]
  congr 1
  ext x
  simp only [RingHom.comp_apply]
  exact Localization.localRingHom_to_map _ _ _ Ideal.LiesOver.over x

end Localized

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def PolyKaehlerFree.Statement : Prop :=
  ∀ (R k : Type) [Field R] [Field k] [Algebra R k] (n : ℕ),
    Module.Free (MvPolynomial (Fin n) k) Ω[MvPolynomial (Fin n) k⁄R]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
