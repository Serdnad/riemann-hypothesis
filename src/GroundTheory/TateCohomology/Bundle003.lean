module

public import GroundTheory.TateCohomology.Bundle002
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import GroundTheory.TateCohomology.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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

namespace GroundTheory.GroupCoh

open CategoryTheory Limits Rep

universe u

section ConnectingIso

variable {k G : Type u} [CommRing k] [Group G] [Fintype G]

theorem isIso_δ_of_tateAcyclic {S : ShortComplex (Rep.{u} k G)} (hS : S.ShortExact)
    (h : TateAcyclic S.X₂) (n : ℤ) : IsIso (TateCohomology.δ hS n) := by
  have : Mono (TateCohomology.δ hS n) :=
    (TateCohomology.exact₃ hS n).mono_g ((h n).eq_of_src _ _)
  have : Epi (TateCohomology.δ hS n) :=
    (TateCohomology.exact₁ hS n).epi_f ((h (n + 1)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

end ConnectingIso

variable {k G : Type u} [CommRing k] [Group G]

section Coind

noncomputable abbrev toCoind (A : Rep.{u} k G) :
    A ⟶ coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A) :=
  (resCoindAdjunction k (⊥ : Subgroup G).subtype).unit.app A

theorem toCoind_hom_apply (A : Rep.{u} k G) (a : A) (x : G) :
    ((toCoind A).hom a).1 x = A.ρ x a := rfl

theorem toCoind_injective (A : Rep.{u} k G) : Function.Injective (toCoind A).hom := by
  intro a b hab
  have h : ((toCoind A).hom a).1 1 = ((toCoind A).hom b).1 1 := by rw [hab]
  rwa [toCoind_hom_apply, toCoind_hom_apply, map_one, one_apply_eq_self,
    one_apply_eq_self] at h

instance (A : Rep.{u} k G) : Mono (toCoind A) :=
  (Rep.mono_iff_injective _).2 (toCoind_injective A)

noncomputable def coindSES : Rep.{u} k G ⥤ ShortComplex (Rep.{u} k G) where
  obj A := ShortComplex.mk (toCoind A) (cokernel.π (toCoind A)) (cokernel.condition _)
  map {A B} f :=
    { τ₁ := f
      τ₂ := (resFunctor (⊥ : Subgroup G).subtype ⋙ coindFunctor k (⊥ : Subgroup G).subtype).map f
      τ₃ := cokernel.map (toCoind A) (toCoind B) f _
        ((resCoindAdjunction k (⊥ : Subgroup G).subtype).unit.naturality f)
      comm₁₂ := (resCoindAdjunction k (⊥ : Subgroup G).subtype).unit.naturality f
      comm₂₃ := by simp }
  map_id A := by
    refine ShortComplex.hom_ext _ _ rfl ?_ ?_
    · exact (resFunctor (⊥ : Subgroup G).subtype ⋙ coindFunctor k (⊥ : Subgroup G).subtype).map_id A
    · have h : coindMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype (𝟙 A)) = 𝟙 _ :=
        (resFunctor (⊥ : Subgroup G).subtype ⋙ coindFunctor k (⊥ : Subgroup G).subtype).map_id A
      exact coequalizer.hom_ext (by simp [h])
  map_comp f g := by
    refine ShortComplex.hom_ext _ _ rfl ?_ ?_
    · exact (resFunctor (⊥ : Subgroup G).subtype ⋙ coindFunctor k (⊥ : Subgroup G).subtype).map_comp f g
    · have h : coindMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype (f ≫ g)) =
          coindMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype f) ≫
            coindMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype g) :=
        (resFunctor (⊥ : Subgroup G).subtype ⋙ coindFunctor k (⊥ : Subgroup G).subtype).map_comp f g
      exact coequalizer.hom_ext (by simp [h])

@[simp] theorem coindSES_obj_X₁ (A : Rep.{u} k G) : (coindSES.obj A).X₁ = A := rfl

@[simp] theorem coindSES_obj_X₂ (A : Rep.{u} k G) :
    (coindSES.obj A).X₂ = coind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A) := rfl

theorem coindSES_shortExact (A : Rep.{u} k G) : (coindSES.obj A).ShortExact := by
  change (ShortComplex.cokernelSequence (toCoind A)).ShortExact
  refine ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact _) ?_ inferInstance
  change Mono (toCoind A)
  infer_instance

noncomputable abbrev coindShift (A : Rep.{u} k G) : Rep.{u} k G := (coindSES.obj A).X₃

variable [Fintype G]

theorem tateAcyclic_coindSES_X₂ (A : Rep.{u} k G) : TateAcyclic (coindSES.obj A).X₂ :=
  tateAcyclic_coind_bot _

noncomputable def coindShiftIso (A : Rep.{u} k G) (n : ℤ) :
    tateCohomology (coindShift A) n ≅ tateCohomology A (n + 1) :=
  @asIso _ _ _ _ (TateCohomology.δ (coindSES_shortExact A) n)
    (isIso_δ_of_tateAcyclic (coindSES_shortExact A) (tateAcyclic_coindSES_X₂ A) n)

theorem isIso_δ_coindSES (A : Rep.{u} k G) (n : ℤ) :
    IsIso (TateCohomology.δ (coindSES_shortExact A) n) :=
  isIso_δ_of_tateAcyclic _ (tateAcyclic_coindSES_X₂ A) n

end Coind

section Ind

noncomputable abbrev fromInd (A : Rep.{u} k G) :
    ind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A) ⟶ A :=
  (indResAdjunction k (⊥ : Subgroup G).subtype).counit.app A

theorem fromInd_surjective (A : Rep.{u} k G) : Function.Surjective (fromInd A).hom := by
  intro a
  refine ⟨Representation.IndV.mk _ _ 1 a, ?_⟩
  change ((indResHomEquiv _ _ _).symm (𝟙 _)).hom _ = a
  simp

instance (A : Rep.{u} k G) : Epi (fromInd A) :=
  (Rep.epi_iff_surjective _).2 (fromInd_surjective A)

noncomputable def indSES : Rep.{u} k G ⥤ ShortComplex (Rep.{u} k G) where
  obj A := ShortComplex.mk (kernel.ι (fromInd A)) (fromInd A) (kernel.condition _)
  map {A B} f :=
    { τ₁ := kernel.map (fromInd A) (fromInd B)
        ((resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor k (⊥ : Subgroup G).subtype).map f) f
        ((indResAdjunction k (⊥ : Subgroup G).subtype).counit.naturality f).symm
      τ₂ := (resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor k (⊥ : Subgroup G).subtype).map f
      τ₃ := f
      comm₁₂ := by simp
      comm₂₃ := (indResAdjunction k (⊥ : Subgroup G).subtype).counit.naturality f }
  map_id A := by
    refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
    · have h : indMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype (𝟙 A)) = 𝟙 _ :=
        (resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor k (⊥ : Subgroup G).subtype).map_id A
      exact equalizer.hom_ext (by simp [h])
    · exact (resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor k (⊥ : Subgroup G).subtype).map_id A
  map_comp f g := by
    refine ShortComplex.hom_ext _ _ ?_ ?_ rfl
    · have h : indMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype (f ≫ g)) =
          indMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype f) ≫
            indMap (⊥ : Subgroup G).subtype (resMap (⊥ : Subgroup G).subtype g) :=
        (resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor k (⊥ : Subgroup G).subtype).map_comp f g
      exact equalizer.hom_ext (by simp [h])
    · exact (resFunctor (⊥ : Subgroup G).subtype ⋙ indFunctor k (⊥ : Subgroup G).subtype).map_comp f g

@[simp] theorem indSES_obj_X₂ (A : Rep.{u} k G) :
    (indSES.obj A).X₂ = ind (⊥ : Subgroup G).subtype (res (⊥ : Subgroup G).subtype A) := rfl

@[simp] theorem indSES_obj_X₃ (A : Rep.{u} k G) : (indSES.obj A).X₃ = A := rfl

theorem indSES_shortExact (A : Rep.{u} k G) : (indSES.obj A).ShortExact := by
  change (ShortComplex.kernelSequence (fromInd A)).ShortExact
  refine ShortComplex.ShortExact.mk' (ShortComplex.kernelSequence_exact _) inferInstance ?_
  change Epi (fromInd A)
  infer_instance

noncomputable abbrev indShift (A : Rep.{u} k G) : Rep.{u} k G := (indSES.obj A).X₁

variable [Fintype G]

theorem tateAcyclic_indSES_X₂ (A : Rep.{u} k G) : TateAcyclic (indSES.obj A).X₂ :=
  tateAcyclic_ind_bot _

noncomputable def indShiftIso (A : Rep.{u} k G) (n : ℤ) :
    tateCohomology A n ≅ tateCohomology (indShift A) (n + 1) :=
  @asIso _ _ _ _ (TateCohomology.δ (indSES_shortExact A) n)
    (isIso_δ_of_tateAcyclic (indSES_shortExact A) (tateAcyclic_indSES_X₂ A) n)

end Ind

end GroundTheory.GroupCoh
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits groupCohomology Rep

universe u

variable {k G : Type u} [CommRing k] [Group G]

theorem map_one_succ {H : Type u} [Group H] {A : Rep k H} {B : Rep k G}
    (φ : res (1 : G →* H) A ⟶ B) (n : ℕ) : map 1 φ (n + 1) = 0 := by
  let f : PUnit.{u + 1} →* H := 1
  let g : G →* PUnit.{u + 1} := 1
  let ψ : res g (res f A) ⟶ B := ofHom ⟨φ.hom.toLinearMap, fun x => φ.hom.isIntertwining' x⟩
  have h : map 1 φ (n + 1) = map (f.comp g) ((resFunctor g).map (𝟙 (res f A)) ≫ ψ) (n + 1) :=
    map_congr (by ext; rfl) rfl (n + 1)
  rw [h, map_comp, (isZero_groupCohomology_succ_of_subsingleton (res f A) n).eq_zero_of_src
    (map g ψ (n + 1)), Limits.comp_zero]

variable (A : Rep k G) (S : Subgroup G) [S.Normal]

noncomputable abbrev inflation (n : ℕ) :
    groupCohomology (A.quotientToInvariants S) n ⟶ groupCohomology A n :=
  map (QuotientGroup.mk' S) (ofHom (A.ρ.quotientToInvariants_lift S)) n

noncomputable abbrev restriction (n : ℕ) :
    groupCohomology A n ⟶ groupCohomology (res S.subtype A) n :=
  map S.subtype (𝟙 _) n

theorem inflation_comp_restriction (n : ℕ) :
    inflation A S (n + 1) ≫ restriction A S (n + 1) = 0 := by
  rw [← map_comp, Category.comp_id, groupCohomology.congr (QuotientGroup.mk'_comp_subtype S)
    (fun f φ => map f φ (n + 1)), map_one_succ]

noncomputable def infResShortComplex (n : ℕ) : ShortComplex (ModuleCat k) where
  X₁ := groupCohomology (A.quotientToInvariants S) (n + 1)
  X₂ := groupCohomology A (n + 1)
  X₃ := groupCohomology (res S.subtype A) (n + 1)
  f := inflation A S (n + 1)
  g := restriction A S (n + 1)
  zero := inflation_comp_restriction A S n

lemma invariants_map_surjective {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    (h1 : IsZero (groupCohomology X.X₁ 1)) :
    Function.Surjective ((invariantsFunctor k G).map X.g).hom := by
  have ex := (map_cochainsFunctor_shortExact hX).homology_exact₃ 0 1 rfl
  have e : Epi (map (MonoidHom.id G) X.g 0) := ex.epi_f (h1.eq_of_tgt _ _)
  have hc := map_id_comp_H0Iso_hom X.g
  have e2 : Epi ((H0Iso X.X₂).hom ≫ (invariantsFunctor k G).map X.g) := by
    rw [← hc]; infer_instance
  have e3 := epi_of_epi (H0Iso X.X₂).hom ((invariantsFunctor k G).map X.g)
  exact (ModuleCat.epi_iff_surjective _).1 e3

noncomputable def toCoindOne : A ⟶ coindOne k G A :=
  ofHom ⟨LinearMap.pi fun x => A.ρ x, fun g => by
    ext a x
    change A.ρ x (A.ρ g a) = A.ρ (x * g) a
    rw [map_mul, mul_apply_eq_comp]⟩

lemma toCoindOne_injective : Function.Injective (toCoindOne A).hom := fun a b h => by
  have h' : A.ρ 1 a = A.ρ 1 b := congrFun h 1
  simpa using h'

instance : Mono (toCoindOne A) := (Rep.mono_iff_injective _).2 (toCoindOne_injective A)

noncomputable abbrev shiftSC : ShortComplex (Rep k G) :=
  ShortComplex.mk (toCoindOne A) (cokernel.π (toCoindOne A)) (cokernel.condition _)

lemma shiftSC_shortExact : (shiftSC A).ShortExact where
  exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
  mono_f := inferInstanceAs (Mono (toCoindOne A))
  epi_g := inferInstanceAs (Epi (cokernel.π _))

instance : (quotientToInvariantsFunctor k S).PreservesZeroMorphisms where
  map_zero _ _ := by ext; rfl

noncomputable abbrev shiftSCQ : ShortComplex (Rep k (G ⧸ S)) :=
  (shiftSC A).map (quotientToInvariantsFunctor k S)

lemma shiftSCQ_shortExact (h1 : IsZero (groupCohomology (res S.subtype A) 1)) :
    (shiftSCQ A S).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [← ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k (G ⧸ S)) (ModuleCat k)),
      ShortComplex.moduleCat_exact_iff_ker_sub_range]
    intro x hx
    have hrk := ((shiftSC_shortExact A).exact.map
      (forget₂ (Rep k G) (ModuleCat k))).moduleCat_range_eq_ker
    have hx' : x.1 ∈ LinearMap.ker ((shiftSC A).map (forget₂ (Rep k G) (ModuleCat k))).g.hom :=
      congrArg Subtype.val hx
    rw [← hrk] at hx'
    obtain ⟨a, ha⟩ := hx'
    have ha' : (toCoindOne A).hom a = x.1 := ha
    refine ⟨⟨a, fun s => toCoindOne_injective A ?_⟩, Subtype.ext ha'⟩
    refine (hom_comm_apply (toCoindOne A) (s : G) a).trans ?_
    rw [ha']
    exact x.2 s
  · exact (Rep.mono_iff_injective _).2 fun x y h =>
      Subtype.ext (toCoindOne_injective A (congrArg Subtype.val h))
  · exact (Rep.epi_iff_surjective (shiftSCQ A S).g).2
      (invariants_map_surjective (X := (shiftSC A).map (resFunctor S.subtype))
        ((shortExact_res S.subtype).2 (shiftSC_shortExact A)) h1)

theorem infRes_step (n : ℕ)
    (ih : ∀ B : Rep k G, (∀ i, 0 < i → i < n + 1 → IsZero (groupCohomology (res S.subtype B) i)) →
      Mono (infResShortComplex B S n).f ∧ (infResShortComplex B S n).Exact)
    (hA : ∀ i, 0 < i → i < n + 2 → IsZero (groupCohomology (res S.subtype A) i)) :
    Mono (infResShortComplex A S (n + 1)).f ∧ (infResShortComplex A S (n + 1)).Exact := by
  have hX := shiftSC_shortExact A
  have hS := (shortExact_res S.subtype).2 hX
  have hQ := shiftSCQ_shortExact A S (hA 1 one_pos (by omega))
  have hC : ∀ i, 0 < i → i < n + 1 →
      IsZero (groupCohomology (res S.subtype (shiftSC A).X₃) i) := by
    intro i hi hin
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have hδ := isIso_δ_of_isZero hS (m + 1) (isZero_res_coindOne k A S m)
      (isZero_res_coindOne k A S (m + 1))
    exact (hA (m + 1 + 1) (by omega) (by omega)).of_iso (@asIso _ _ _ _ _ hδ)
  obtain ⟨ihm, ihe⟩ := ih (shiftSC A).X₃ hC
  have hδQ := isIso_δ_of_isZero hQ (n + 1) (isZero_quotientToInvariants_coindOne k A S n)
    (isZero_quotientToInvariants_coindOne k A S (n + 1))
  have hδX := isIso_δ_of_isZero hX (n + 1) (isZero_coindOne k G A n)
    (isZero_coindOne k G A (n + 1))
  have hδS := isIso_δ_of_isZero hS (n + 1) (isZero_res_coindOne k A S n)
    (isZero_res_coindOne k A S (n + 1))
  let F : (shiftSCQ A S).map (resFunctor (QuotientGroup.mk' S)) ⟶ shiftSC A :=
    { τ₁ := ofHom (A.ρ.quotientToInvariants_lift S)
      τ₂ := ofHom ((coindOne k G A).ρ.quotientToInvariants_lift S)
      τ₃ := ofHom ((shiftSC A).X₃.ρ.quotientToInvariants_lift S)
      comm₁₂ := by ext; rfl
      comm₂₃ := by ext; rfl }
  have h1 : δ hQ (n + 1) (n + 1 + 1) rfl ≫ inflation A S (n + 1 + 1) =
      inflation (shiftSC A).X₃ S (n + 1) ≫ δ hX (n + 1) (n + 1 + 1) rfl :=
    δ_comp_map (QuotientGroup.mk' S) hQ hX F (n + 1) (n + 1 + 1) rfl
  have h2 : δ hX (n + 1) (n + 1 + 1) rfl ≫ restriction A S (n + 1 + 1) =
      restriction (shiftSC A).X₃ S (n + 1) ≫ δ hS (n + 1) (n + 1 + 1) rfl :=
    δ_comp_map_res S.subtype hX (n + 1) (n + 1 + 1) rfl
  let e : infResShortComplex (shiftSC A).X₃ S n ≅ infResShortComplex A S (n + 1) :=
    ShortComplex.isoMk (@asIso _ _ _ _ _ hδQ) (@asIso _ _ _ _ _ hδX) (@asIso _ _ _ _ _ hδS) h1 h2
  refine ⟨?_, (ShortComplex.exact_iff_of_iso e).1 ihe⟩
  have hf : e.inv.τ₁ ≫ (infResShortComplex (shiftSC A).X₃ S n).f ≫ e.hom.τ₂ =
      (infResShortComplex A S (n + 1)).f := by
    rw [← Category.assoc, e.inv.comm₁₂, Category.assoc, ← ShortComplex.comp_τ₂, e.inv_hom_id,
      ShortComplex.id_τ₂, Category.comp_id]
  rw [← hf]
  infer_instance

theorem infResShortComplex_mono_exact (n : ℕ) :
    ∀ A : Rep k G, (∀ i, 0 < i → i < n + 1 → IsZero (groupCohomology (res S.subtype A) i)) →
      Mono (infResShortComplex A S n).f ∧ (infResShortComplex A S n).Exact := by
  induction n with
  | zero => exact fun A _ => ⟨inferInstanceAs (Mono (H1InfRes A S).f), H1InfRes_exact A S⟩
  | succ n ih => exact fun A hA => infRes_step A S n ih hA

variable {A S}

theorem inflation_injective {q : ℕ} (hq : q ≠ 0)
    (hA : ∀ i, 0 < i → i < q → IsZero (groupCohomology (res S.subtype A) i)) :
    Function.Injective (inflation A S q).hom := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  exact (ModuleCat.mono_iff_injective _).1 (infResShortComplex_mono_exact S n A hA).1

theorem range_inflation_eq_ker_restriction {q : ℕ} (hq : q ≠ 0)
    (hA : ∀ i, 0 < i → i < q → IsZero (groupCohomology (res S.subtype A) i)) :
    LinearMap.range (inflation A S q).hom = LinearMap.ker (restriction A S q).hom := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
  exact (infResShortComplex_mono_exact S n A hA).2.moduleCat_range_eq_ker

theorem inflation_two_injective (h1 : IsZero (groupCohomology (res S.subtype A) 1)) :
    Function.Injective (inflation A S 2).hom :=
  inflation_injective two_ne_zero fun i hi hi2 => by
    obtain rfl : i = 1 := by omega
    exact h1

theorem range_inflation_two_eq_ker_restriction
    (h1 : IsZero (groupCohomology (res S.subtype A) 1)) :
    LinearMap.range (inflation A S 2).hom = LinearMap.ker (restriction A S 2).hom :=
  range_inflation_eq_ker_restriction two_ne_zero fun i hi hi2 => by
    obtain rfl : i = 1 := by omega
    exact h1

end GroundTheory.GroupCoh
end
