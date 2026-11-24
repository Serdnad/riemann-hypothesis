module

public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.LocalFieldAutomorphisms.Kloc
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar
import Formalism.ConjugateSelfDual.Statement
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicAutomorphismUnique

@[expose] public section

noncomputable section

namespace ReciprocityTheory.Neutral.Cmp

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

theorem mem_range_of_aeval_rat_eq_zero (ι : Ω →+* PadicAlgCl p) [IsAlgClosed Ω] {g : Polynomial ℚ} (hg : g ≠ 0)
    {b : PadicAlgCl p} (hb : Polynomial.aeval b g = 0) : b ∈ ι.range := by
  classical
  haveI : CharZero Ω := RingHom.charZero ι
  have hmap : (g.map (algebraMap ℚ Ω)).map ι = g.map (algebraMap ℚ (PadicAlgCl p)) := by
    rw [Polynomial.map_map]
    congr 1
    exact RingHom.ext_rat _ _
  have hroot : ((g.map (algebraMap ℚ Ω)).map ι).IsRoot b := by
    rw [hmap, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hb
  exact Polynomial.Splits.mem_range_of_isRoot (IsAlgClosed.splits _) (Polynomial.map_ne_zero hg) hroot

theorem denseRange_of_isAlgClosed (ι : Ω →+* PadicAlgCl p) [IsAlgClosed Ω] : DenseRange ι := by
  apply _root_.GlobalTheory.denseRange_of_isAlgClosed_padicAlgCl <;> assumption

theorem finiteDimensional_Kloc (ι : Ω →+* PadicAlgCl p) : FiniteDimensional ℚ_[p] (Kloc F ι) := by
  classical
  let b := Module.finBasis ℚ F
  let f := ι.comp (algebraMap F Ω)
  have hle : Kloc F ι ≤ IntermediateField.adjoin ℚ_[p] (Set.range fun i => f (b i)) := by
    apply IntermediateField.adjoin_le_iff.2
    rintro _ ⟨y, rfl⟩

    rw [← b.sum_repr y, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul, Rat.smul_def, ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p))]
    exact mul_mem (IntermediateField.algebraMap_mem _ _) (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (Set.range fun i => f (b i))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion_injective hle)

theorem isAlgClosure_Kloc (ι : Ω →+* PadicAlgCl p) : IsAlgClosure (Kloc F ι) (PadicAlgCl p) := by
  exact ⟨inferInstance, inferInstance⟩


variable (F) in
include F in
theorem denseRange (ι : Ω →+* PadicAlgCl p) : DenseRange ι := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  exact denseRange_of_isAlgClosed ι

theorem norm_map (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ := by
  exact (spectralNorm_eq_of_equiv σ x).symm

theorem norm_map_GK (ι : Ω →+* PadicAlgCl p) (σ : GK F ι) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ := by
  exact norm_map (σ.restrictScalars ℚ_[p]) x

end ReciprocityTheory.Neutral.Cmp
