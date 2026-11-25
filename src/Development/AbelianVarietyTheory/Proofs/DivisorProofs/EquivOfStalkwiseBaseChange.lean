module

import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EquivOfStalkwiseBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringsRefineOfCechConerveProperty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceOfStrictlyHenselianSta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceDescentLocalEquivalenceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallEtaleCechNerveResolutionOfSurjectiveStatement
import Mathlib.Tactic.Linter.HaveILetI

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LocGlobSp

def covSurj (S : Scheme.{0}) : MorphismProperty (S.Etale)ᵒᵖ := fun _ _ g => Surjective g.unop.left

instance (S : Scheme.{0}) : (covSurj S).IsStableUnderComposition := by
  constructor
  intro X Y Z f g hf hg
  have : Surjective f.unop.left := hf
  have : Surjective g.unop.left := hg
  exact (inferInstance : Surjective (g.unop.left ≫ f.unop.left))

theorem fst_isIso {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso g] [HasPullback f g] :
    IsIso (pullback.fst f g) := by
  have w : 𝟙 X ≫ f = (f ≫ inv g) ≫ g := by
    rw [Category.id_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  refine ⟨⟨pullback.lift (𝟙 _) (f ≫ inv g) w, ?_, pullback.lift_fst _ _ _⟩⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.condition, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id, Category.id_comp]

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E E' : Spc) (α : E ⟶ E') (p : E' ⟶ sch.obj S), Finitary F → QcqsOver (α ≫ p) → QcqsOver p → (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R ((bcMap α p).app (Over.mk s)) F) → Eqv R α F :=
  _root_.UpperTheory.Cb.equiv_of_stalkwise_base_change

end GlobalTheory.EtC.LocGlobSp

end
