import GroundTheory.ProfiniteCohomology.ContinuousCochains.LongExactSequence
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclicTrivialInductionRing

open CategoryTheory GroundTheory.ProfCoh

attribute [local instance 2000] Rep.hV2

namespace UpperTheory.Reformulated.B.Gua5

private theorem isDiscreteRep_of_forall_eq {k G : Type} [CommRing k] [Group G]
    [TopologicalSpace G] (A : Rep.{0, 0, 0} k G) (h : ∀ (g : G) (a : A.V), A.ρ g a = a) :
    GroundTheory.ProfCoh.IsDiscreteRep A := by
  haveI : A.ρ.IsTrivial := ⟨fun g => LinearMap.ext fun a => h g a⟩
  infer_instance

theorem finite_cohomology_of_trivial_of_cyclic {H : Type} [inst : Group H] [inst_1 : TopologicalSpace H]
    [inst_2 : IsTopologicalGroup H] (n r : ℕ)
    (hcyc : ∀ (C : Rep.{0} (ULift.{0} ℤ) H) [inst_3 : IsDiscreteRep C] [Finite C] [IsAddCyclic C],
      (∀ (g : H) (c : C), C.ρ g c = c) → (∀ c : C, n • c = 0) → Finite (cohomology C r))
    (A : Rep.{0} (ULift.{0} ℤ) H) [inst_3 : IsDiscreteRep A] [Finite A]
    (htriv : ∀ (g : H) (a : A), A.ρ g a = a) (hA : ∀ a : A, n • a = 0) :
    Finite (cohomology A r) := by
  refine UpperTheory.cyclic_trivial_induction n
    (fun B => ∀ [IsDiscreteRep B], Finite (cohomology B r)) ?_ ?_ A inferInstance htriv hA
  · intro C _ _ ht hn _
    exact hcyc C ht hn
  · intro A B C f g hA hC hf hfg hg PA PC _
    haveI := isDiscreteRep_of_forall_eq A hA
    haveI := isDiscreteRep_of_forall_eq C hC
    let S := ShortComplex.mk f g (by
      exact Rep.hom_ext (DFunLike.ext _ _ fun a => (hfg (f.hom a)).2 ⟨a, rfl⟩))
    have he : S.ShortExact := {
      mono_f := (Rep.mono_iff_injective f).2 hf
      epi_g := (Rep.epi_iff_surjective g).2 hg
      exact := by
        rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep.{0} (ULift.{0} ℤ) H) (ModuleCat.{0} (ULift.{0} ℤ)))]
        exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2 hfg }
    exact AddCommGrpCat.isFinite.prop_X₂_of_exact
      ((cohomology_exact₂ he r).map (forget₂ (ModuleCat _) AddCommGrpCat)) PA PC

end UpperTheory.Reformulated.B.Gua5
