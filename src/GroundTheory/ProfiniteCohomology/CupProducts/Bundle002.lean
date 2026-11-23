module

public import GroundTheory.ProfiniteCohomology.CupProducts.Bundle001
public import GroundTheory.ProfiniteCohomology.Bundle006
public import GroundTheory.TateCohomology.CupProduct
public import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality.Naturality
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory TensorProduct

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Comparison

variable {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] {p q n : ℕ}

end Comparison

section Levels

variable (U : OpenNormalSubgroup G) {p q n : ℕ}

theorem inflation_π (A : Rep.{u} k G) [IsDiscreteRep A]
    (z : groupCohomology.cocycles (A.quotientToInvariants (U : Subgroup G)) p) :
    inflation A U p (groupCohomology.π _ p z) =
      cohomologyπ A p (HomologicalComplex.cyclesMap (inflationCochains A U) p z) :=
  ConcreteCategory.congr_hom (HomologicalComplex.homologyπ_naturality (inflationCochains A U) p) z

theorem cochainOf_cocycleι_cyclesMap_inflationCochains (A : Rep.{u} k G) [IsDiscreteRep A]
    (z : groupCohomology.cocycles (A.quotientToInvariants (U : Subgroup G)) p) :
    cochainOf (A := A) (cocycleι (A := A) (p := p)
      (HomologicalComplex.cyclesMap (inflationCochains A U) p z)) =
      fun g => (groupCohomology.iCocycles (A.quotientToInvariants (U : Subgroup G)) p z
        (fun i => (g i : G ⧸ (U : Subgroup G))) : A) :=
  congrArg (fun ψ => cochainOf (A := A) (ψ.hom z))
    (HomologicalComplex.cyclesMap_i (inflationCochains A U) p)

theorem inflationCochains_comp_cochainsMap {A A' : Rep.{u} k G} [IsDiscreteRep A]
    [IsDiscreteRep A'] (f : A ⟶ A') :
    inflationCochains A U ≫ cochainsMap f =
      groupCohomology.cochainsMap (MonoidHom.id _)
        ((Rep.quotientToInvariantsFunctor k (U : Subgroup G)).map f) ≫ inflationCochains A' U := by
  ext n x : 3
  rfl

theorem inflation_comp_cohomologyMap {A A' : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep A']
    (f : A ⟶ A') (n : ℕ) :
    inflation A U n ≫ cohomologyMap f n =
      groupCohomology.map (MonoidHom.id _)
        ((Rep.quotientToInvariantsFunctor k (U : Subgroup G)).map f) n ≫ inflation A' U n := by
  have h := congrArg (fun φ => HomologicalComplex.homologyMap φ n)
    (inflationCochains_comp_cochainsMap U f)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact h

theorem cohomologyMap_inflation {A A' : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep A']
    (f : A ⟶ A') (x : groupCohomology (A.quotientToInvariants (U : Subgroup G)) n) :
    cohomologyMap f n (inflation A U n x) =
      inflation A' U n (groupCohomology.map (MonoidHom.id _)
        ((Rep.quotientToInvariantsFunctor k (U : Subgroup G)).map f) n x) :=
  ConcreteCategory.congr_hom (inflation_comp_cohomologyMap U f n) x

variable (A B : Rep.{u} k G) [IsDiscreteRep A] [IsDiscreteRep B]

theorem cup_inflation (h : p + q = n)
    (x : groupCohomology (A.quotientToInvariants (U : Subgroup G)) p)
    (y : groupCohomology (B.quotientToInvariants (U : Subgroup G)) q) :
    GroundTheory.ProfCoh.cup h (inflation A U p x) (inflation B U q y) =
      inflation (A ⊗ B) U n (groupCohomology.map (MonoidHom.id _)
        (invariantsTensorHom A B (U : Subgroup G)) n (GroundTheory.GroupCoh.cupH h x y)) := by
  refine groupCohomology_induction_on x fun x => ?_
  refine groupCohomology_induction_on y fun y => ?_
  rw [inflation_π, inflation_π, cup_cohomologyπ, GroundTheory.GroupCoh.cupH_π,
    GroundTheory.GroupCoh.map_π_apply, inflation_π]
  congr 1
  apply cocycles_ext
  rw [cocycleι_cupCocycles, cochainOf_cupLocallyConstant,
    cochainOf_cocycleι_cyclesMap_inflationCochains, cochainOf_cocycleι_cyclesMap_inflationCochains,
    cochainOf_cocycleι_cyclesMap_inflationCochains, GroundTheory.GroupCoh.iCocycles_cocyclesMap,
    GroundTheory.GroupCoh.iCocycles_cupCocycles]
  funext g
  simp only [GroundTheory.GroupCoh.cupCochain_apply]
  have hP : Fin.partialProd (fun i => (g i : G ⧸ (U : Subgroup G))) ⟨p, by omega⟩ =
      ((Fin.partialProd g ⟨p, by omega⟩ : G) : G ⧸ (U : Subgroup G)) :=
    partialProd_comp_monoidHom (QuotientGroup.mk' (U : Subgroup G)) g _
  rw [hP]
  rfl

end Levels

end GroundTheory.ProfCoh
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory TensorProduct groupCohomology GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G]

section PairingHom

variable {A B C : Rep.{u} k G}

def pairingHom (β : A →ₗ[k] B →ₗ[k] C)
    (hβ : ∀ (g : G) (a : A) (b : B), β (A.ρ g a) (B.ρ g b) = C.ρ g (β a b)) : A ⊗ B ⟶ C :=
  Rep.ofHom ⟨TensorProduct.lift β, fun g => TensorProduct.ext' fun a b => by
    simpa using hβ g a b⟩

@[simp]
theorem pairingHom_tmul (β : A →ₗ[k] B →ₗ[k] C)
    (hβ : ∀ (g : G) (a : A) (b : B), β (A.ρ g a) (B.ρ g b) = C.ρ g (β a b)) (a : A) (b : B) :
    (pairingHom β hβ).hom (a ⊗ₜ[k] b : (A ⊗ B : Rep k G)) = β a b :=
  TensorProduct.lift.tmul a b

end PairingHom

variable [TopologicalSpace G] [IsTopologicalGroup G]

section CupPairing

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C] {p q n : ℕ}

def cupPairing (μ : A ⊗ B ⟶ C) (h : p + q = n) :
    cohomology A p →ₗ[k] cohomology B q →ₗ[k] cohomology C n :=
  (cup h).compr₂ (cohomologyMap μ n).hom

theorem cupPairing_apply (μ : A ⊗ B ⟶ C) (h : p + q = n) (x : cohomology A p)
    (y : cohomology B q) : cupPairing μ h x y = cohomologyMap μ n (cup h x y) :=
  rfl

theorem cupPairing_cohomologyπ (μ : A ⊗ B ⟶ C) (h : p + q = n) (x : cocycles A p)
    (y : cocycles B q) :
    cupPairing μ h (cohomologyπ A p x) (cohomologyπ B q y) =
      cohomologyπ C n (HomologicalComplex.cyclesMap (cochainsMap μ) n (cupCocycles h x y)) := by
  rw [cupPairing_apply, cup_cohomologyπ, cohomologyMap_cohomologyπ]

theorem cochainOf_cocycleι_cyclesMap_cupCocycles (μ : A ⊗ B ⟶ C) (h : p + q = n)
    (x : cocycles A p) (y : cocycles B q) (s : Fin n → G) :
    cochainOf (A := C) (cocycleι (A := C) (p := n)
        (HomologicalComplex.cyclesMap (cochainsMap μ) n (cupCocycles h x y))) s =
      μ.hom (cochainOf (A := A) (cocycleι (A := A) (p := p) x)
          (fun i : Fin p => s ⟨i, by omega⟩) ⊗ₜ[k]
        B.ρ (Fin.partialProd s ⟨p, by omega⟩)
          (cochainOf (A := B) (cocycleι (A := B) (p := q) y)
            fun j : Fin q => s ⟨p + j, by omega⟩)) := by
  rw [cochainOf_cocycleι_cyclesMap, cocycleι_cupCocycles, cochainOf_cupLocallyConstant]
  rfl

variable {A' B' C' : Rep.{u} k G} [IsDiscreteRep A'] [IsDiscreteRep B'] [IsDiscreteRep C']

theorem cupPairing_cohomologyMap (μ : A ⊗ B ⟶ C) (f : A' ⟶ A) (g : B' ⟶ B) (h : p + q = n)
    (x : cohomology A' p) (y : cohomology B' q) :
    cupPairing μ h (cohomologyMap f p x) (cohomologyMap g q y) =
      cupPairing ((f ⊗ₘ g) ≫ μ) h x y := by
  rw [cupPairing_apply, cupPairing_apply, ← cohomologyMap_tensorHom_cup, cohomologyMap_comp]
  rfl

theorem cohomologyMap_cupPairing (μ : A ⊗ B ⟶ C) (ν : C ⟶ C') (h : p + q = n)
    (x : cohomology A p) (y : cohomology B q) :
    cohomologyMap ν n (cupPairing μ h x y) = cupPairing (μ ≫ ν) h x y := by
  rw [cupPairing_apply, cupPairing_apply, cohomologyMap_comp]
  rfl

theorem cohomologyRes_cupPairing (μ : A ⊗ B ⟶ C) (S : Subgroup G) (h : p + q = n)
    (x : cohomology A p) (y : cohomology B q) :
    cohomologyRes C S n (cupPairing μ h x y) =
      cupPairing ((resTensorIso S.subtype A B).inv ≫ (Rep.resFunctor S.subtype).map μ) h
        (cohomologyRes A S p x) (cohomologyRes B S q y) := by
  rw [cupPairing_apply, cupPairing_apply, ← cohomologyMap_resTensorIso_cohomologyRes_cup,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, cohomologyMap_comp_cohomologyRes,
    ← cohomologyMap_comp, Iso.hom_inv_id_assoc]
  rfl

end CupPairing

end GroundTheory.ProfCoh
end
end
