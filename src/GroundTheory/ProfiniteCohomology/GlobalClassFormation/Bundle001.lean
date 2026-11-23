module

public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Places
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.IdeleLimits.Bundle001
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.InfDefs
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.IsScalarTowerFiniteSubfieldAlgebraicClosure
import GroundTheory.GlobalFields.CyclotomicCharacters.Character
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.Colimit
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LocalLimits.InfColimit
public import GroundTheory.ProfiniteCohomology.GlobalClassFormation.LevelDefs
public import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
public import GroundTheory.GlobalFields.SecondInequality.Cyclic
public import GroundTheory.TateCohomology.Bundle005
public import GroundTheory.TateCohomology.Bundle004
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IntermediateField IsDedekindDomain GroundTheory.Global FiniteSubfield
  IdeleLimit DirectSum

open scoped Pointwise NumberField.LiesOver

noncomputable section

variable (K : FiniteSubfield)

structure LocalEmbeddings where

  fin : ∀ v : HeightOneSpectrum (𝓞 K.1), AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure (v.adicCompletion K.1)

  inf : ∀ v : InfinitePlace K.1, AlgebraicClosure ℚ →ₐ[K.1] AlgebraicClosure v.Completion

theorem nonempty_localEmbeddings : Nonempty (LocalEmbeddings K) :=
  ⟨⟨fun _ => Classical.choice nonempty_algHom_of_isSepClosed,
    fun _ => Classical.choice nonempty_algHom_of_isSepClosed⟩⟩

variable {K}

namespace LocalEmbeddings

variable (ι : LocalEmbeddings K)

def places : CompatiblePlaces K where
  fin v p := placeOfEmbedding (ι.fin v) p.1
  fin_liesOver v {p q} h := by
    haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
    exact liesOver_placeOfEmbedding (ι.fin v)
  inf v p := infPlaceOfEmbedding (ι.inf v) p.1
  inf_liesOver v {p q} h := by
    haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
    exact liesOver_infPlaceOfEmbedding (ι.inf v)

end LocalEmbeddings


variable (K) in
def localGaloisCohomology (n : ℕ) : Place K.1 → Type
  | .inl v => cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) n
  | .inr v => cohomology (galUnitsZ (v.adicCompletion K.1) (AlgebraicClosure (v.adicCompletion K.1))) n

instance (n : ℕ) (v : Place K.1) : AddCommGroup (localGaloisCohomology K n v) := by
  rcases v with v | v <;> exact inferInstanceAs (AddCommGroup (cohomology _ n))

namespace LocalEmbeddings

variable (ι : LocalEmbeddings K) (n : ℕ)

def localInflHom : ∀ (v : Place K.1) (p : GLevel K),
    (ι.places.levelDecomposition n).L v p →+ localGaloisCohomology K n v
  | .inl v, p => (infLocalInfl (ι.inf v) p.1 n).hom.toAddMonoidHom
  | .inr v, p => (localInfl (ι.fin v) p.1 n).hom.toAddMonoidHom



def localLimit : LocalLimit (ι.places.levelDecomposition n) where
  T := localGaloisCohomology K n
  infl := ι.localInflHom n
  infl_compat v p q h z := by
    rcases v with v | v
    · haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
      exact congrArg (fun φ => φ.hom z) (infLocalTransition_comp_infLocalInfl (ι.inf v) (F := p.1) (E := q.1) n)
    · haveI : Fact (p.1 ≤ q.1) := ⟨h⟩
      exact congrArg (fun φ => φ.hom z) (localTransition_comp_localInfl (ι.fin v) (F := p.1) (E := q.1) n)
  exists_infl v t := by
    rcases v with v | v
    · have h := exists_infLocalInfl_eq (ι.inf v) n t
      obtain ⟨p, y, hy⟩ := h
      exact ⟨p, y, hy⟩
    · have h := exists_localInfl_eq (ι.fin v) n t
      obtain ⟨p, y, hy⟩ := h
      exact ⟨p, y, hy⟩
  exists_lt_eq_zero v p z hz := by
    rcases v with v | v
    · have h := exists_infLocalTransition_eq_zero (ι.inf v) n p z hz
      obtain ⟨q, hpq, hq⟩ := h
      exact ⟨q, hpq, hq⟩
    · have h := exists_localTransition_eq_zero (ι.fin v) n p z hz
      obtain ⟨q, hpq, hq⟩ := h
      exact ⟨q, hpq, hq⟩

end LocalEmbeddings

def idelesLimitCohomologyEquiv (ι : LocalEmbeddings K) {n : ℕ} (hn : 1 ≤ n) :
    cohomology (limitRep K) n ≃+ ⨁ v : Place K.1, localGaloisCohomology K n v :=
  limitCohomologyEquiv (ι.places.levelDecomposition n) (ι.localLimit n) hn

theorem idelesLimitCohomologyEquiv_levelInfl (ι : LocalEmbeddings K) {n : ℕ} (hn : 1 ≤ n) (p : GLevel K)
    (y : cohomology (ideleRep K.1 p.1.1) n) (v : Place K.1) :
    idelesLimitCohomologyEquiv ι hn ((levelInfl K p.1 n).hom y) v =
      ι.localInflHom n v p (ι.places.shapiro n v p ((cohomologyMap (placeProj v) n).hom y)) :=
  limitCohomologyEquiv_levelInfl _ _ hn p y v

end

end GroundTheory.ProfCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory CategoryTheory.Limits GroundTheory.Global NumberField Module

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem natCard_tateCohomology_zero_ideleClassRep (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology (ideleClassRep K L) 0) = finrank K L := by
  rw [GroundTheory.GroupCoh.natCard_tateCohomology_zero _ hσ]
  exact (classFieldAxiom_ideleClassGroup σ hσ).1

theorem natCard_tateCohomology_neg_one_ideleClassRep (σ : Gal(L/K))
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) :
    Nat.card (tateCohomology (ideleClassRep K L) (-1)) = 1 := by
  rw [GroundTheory.GroupCoh.natCard_tateCohomology_neg_one _ hσ]
  exact (classFieldAxiom_ideleClassGroup σ hσ).2

variable [IsCyclic Gal(L/K)]

theorem isZero_groupCohomology_one_ideleClassRep_of_isCyclic :
    IsZero (groupCohomology (ideleClassRep K L) 1) := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  have e2 : (-1 + 2 : ℤ) = ((1 : ℕ) : ℤ) := by norm_num
  have h0 : Nat.card (groupCohomology (ideleClassRep K L) 1) =
      Nat.card (tateCohomology (ideleClassRep K L) ((1 : ℕ) : ℤ)) :=
    (Nat.card_congr
      ((TateCohomology.isoGroupCohomology 1).app (ideleClassRep K L)).toLinearEquiv.toEquiv).symm
  have h1 : Nat.card (tateCohomology (ideleClassRep K L) (-1 + 2)) =
      Nat.card (tateCohomology (ideleClassRep K L) (-1)) :=
    Nat.card_congr
      (GroundTheory.GroupCoh.tateCohomologyPeriodicIso (ideleClassRep K L) hσ (-1)).toLinearEquiv.toEquiv
  have h : Nat.card (groupCohomology (ideleClassRep K L) 1) = 1 := by
    rw [h0, ← e2, h1]
    exact natCard_tateCohomology_neg_one_ideleClassRep σ hσ
  have : Subsingleton (groupCohomology (ideleClassRep K L) 1) :=
    (Nat.card_eq_one_iff_unique.1 h).1
  exact ModuleCat.isZero_of_subsingleton _

theorem natCard_groupCohomology_two_ideleClassRep_of_isCyclic :
    Nat.card (groupCohomology (ideleClassRep K L) 2) = finrank K L := by
  obtain ⟨σ, hσ⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  let e : groupCohomology (ideleClassRep K L) 2 ≅ tateCohomology (ideleClassRep K L) 0 :=
    ((TateCohomology.isoGroupCohomology 2).app (ideleClassRep K L)).symm ≪≫
      GroundTheory.GroupCoh.tateCohomologyPeriodicIso (ideleClassRep K L) hσ 0
  rw [Nat.card_congr e.toLinearEquiv.toEquiv]
  exact natCard_tateCohomology_zero_ideleClassRep σ hσ

end GroundTheory.ProfCoh
end
