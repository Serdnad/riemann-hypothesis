module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle001
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.RingTheory.Henselian
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory

theorem isOpen_singleton_of_isClosed_of_generization {X : Scheme.{0}} [IsLocallyNoetherian X] (x : X)
    (hx : IsClosed ({x} : Set X)) (h : ∀ y, y ⤳ x → y = x) : IsOpen ({x} : Set X) := by
  obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
  have hemb := (X.affineCover.f i).isOpenEmbedding
  rw [← Set.image_singleton, ← hemb.isOpen_iff_image_isOpen]
  have hN : IsLocallyNoetherian (X.affineCover.X i) := isLocallyNoetherian_of_isOpenImmersion (X.affineCover.f i)
  have hA : IsAffine (X.affineCover.X i) := inferInstance
  have : IsNoetherian (X.affineCover.X i) := {}
  have hcl : IsClosed ({y} : Set (X.affineCover.X i)) := by
    have := hx.preimage hemb.continuous
    rwa [← Set.image_singleton, Set.preimage_image_eq _ hemb.injective] at this
  have hgen : ∀ z, z ⤳ y → z = y := fun z hz => hemb.injective (h _ (hz.map hemb.continuous))
  clear hx h hemb
  generalize X.affineCover.X i = Y at *
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := Y)
  have hc : IsClosed (⋃ Z ∈ {Z ∈ irreducibleComponents Y | y ∉ Z}, Z) :=
    (hfin.subset (Set.sep_subset _ _)).isClosed_biUnion
      fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  convert hc.isOpen_compl using 1
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, not_exists]
  constructor
  · rintro rfl Z hZ hz
    exact hZ.2 hz
  · intro H
    have hm := irreducibleComponent_mem_irreducibleComponents z
    have hy : y ∈ irreducibleComponent z := by
      by_contra hy
      exact H _ ⟨hm, hy⟩ mem_irreducibleComponent
    have hg := (isIrreducible_irreducibleComponent (x := z)).isGenericPoint_genericPoint
      isClosed_irreducibleComponent
    have e := hgen _ (hg.specializes hy)
    rw [e] at hg
    have : z ∈ closure {y} := by
      rw [hg.def]; exact mem_irreducibleComponent
    rwa [hcl.closure_eq] at this

theorem quasiFiniteAt_of_isClosed_of_generization {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) (h : ∀ y, y ⤳ x → f y = f x → y = x) : f.QuasiFiniteAt x := by
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber]
  have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  have : IsLocallyNoetherian (f.fiber (f x)) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x))
  have hemb := (f.fiberι (f x)).isEmbedding
  have hx' : f.fiberι (f x) (f.asFiber x) = x := by simp
  apply isOpen_singleton_of_isClosed_of_generization
  · have := hx.preimage hemb.continuous
    convert this using 1
    ext z
    exact ⟨fun hz => by rw [hz]; exact hx', fun hz => hemb.injective (hz.trans hx'.symm)⟩
  · intro y hy
    apply hemb.injective
    rw [hx']
    apply h
    · have := hy.map hemb.continuous
      rwa [hx'] at this
    · have : f.fiberι (f x) y ∈ f ⁻¹' {f x} := by
        rw [← f.range_fiberι]; exact ⟨y, rfl⟩
      exact this

theorem eq_of_specializes_of_basicOpen {X : Scheme.{0}} {y x : X} (h : y ⤳ x)
    (H : ∀ (U : X.Opens) (_ : x ∈ U) (s : Γ(X, U)), y ∈ X.basicOpen s → x ∈ X.basicOpen s) : y = x := by
  refine (h.antisymm ?_).eq
  rw [specializes_iff_forall_open]
  intro V hV hy
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  have hyU : y ∈ U := h.mem_open U.2 hxU
  obtain ⟨s, hs, hys⟩ := IsAffineOpen.exists_basicOpen_le hU (V := ⟨V, hV⟩) ⟨y, hy⟩ hyU
  exact hs (H U hxU s hys)

theorem quasiFiniteAt_homOfVector_of_coord : ∀ (C : Core) (w : C.G.toScheme) (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), IsClosed ({w} : Set C.G.toScheme) → C.Coord w W hw u → (AffineSpace.homOfVector (W.ι ≫ C.GG.hom) (fun i => W.topIso.inv.hom (u i))).QuasiFiniteAt ⟨w, hw⟩ := by
  intro C w W hw u hcl hco
  have := C.proper
  have hlft : LocallyOfFiniteType C.GG.hom := inferInstanceAs (LocallyOfFiniteType (C.G.ι ≫ C.P.hom))
  unfold Core.Coord at hco
  change IsLocalRing.maximalIdeal (C.GG.left.presheaf.stalk w) = _ at hco
  set f := AffineSpace.homOfVector (W.ι ≫ C.GG.hom) (fun i => W.topIso.inv.hom (u i)) with hf
  have hover : f ≫ (𝔸(Fin C.g; C.Z) ↘ C.Z) = W.ι ≫ C.GG.hom := AffineSpace.homOfVector_over _ _
  have : LocallyOfFiniteType (f ≫ (𝔸(Fin C.g; C.Z) ↘ C.Z)) := by
    rw [hover]; infer_instance
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_comp f (𝔸(Fin C.g; C.Z) ↘ C.Z)
  have hemb := W.ι.isOpenEmbedding
  apply quasiFiniteAt_of_isClosed_of_generization
  · have := hcl.preimage hemb.continuous
    convert this using 1
    ext z
    exact Subtype.ext_iff
  intro y hy hfy
  have hy' : y.1 ⤳ w := hy.map hemb.continuous
  have hg : C.GG.hom y.1 = C.GG.hom w := by
    have e : ∀ t : W.toScheme, C.GG.hom t.1 = (𝔸(Fin C.g; C.Z) ↘ C.Z) (f t) := by
      intro t
      rw [← Scheme.Hom.comp_apply, hover]; rfl
    rw [e y, hfy, ← e ⟨w, hw⟩]
  apply Subtype.ext
  let P : Ideal (C.G.toScheme.presheaf.stalk w) :=
    (IsLocalRing.maximalIdeal _).comap (C.G.toScheme.presheaf.stalkSpecializes hy').hom
  have hP : ∀ (U : C.G.toScheme.Opens) (hU : w ∈ U) (s : Γ(C.G.toScheme, U)),
      (C.G.toScheme.presheaf.germ U w hU).hom s ∈ P ↔ y.1 ∉ C.G.toScheme.basicOpen s := by
    intro U hU s
    rw [C.G.toScheme.mem_basicOpen s y.1 (hy'.mem_open U.2 hU), Ideal.mem_comap,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← CommRingCat.comp_apply,
      TopCat.Presheaf.germ_stalkSpecializes]
  have hm : ∀ (U : C.G.toScheme.Opens) (hU : w ∈ U) (s : Γ(C.G.toScheme, U)),
      (C.G.toScheme.presheaf.germ U w hU).hom s ∈ IsLocalRing.maximalIdeal _ ↔
        w ∉ C.G.toScheme.basicOpen s := by
    intro U hU s
    rw [C.G.toScheme.mem_basicOpen s w hU, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hle : IsLocalRing.maximalIdeal (C.G.toScheme.presheaf.stalk w) ≤ P := by
    refine hco.le.trans (sup_le ?_ ?_)
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      have h1 : w ∉ C.G.toScheme.basicOpen (u i) := by
        rw [← hm W hw]
        exact hco.ge (Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩))
      have e : ∀ t : W.toScheme, t.1 ∈ C.G.toScheme.basicOpen (u i) ↔
          f t ∈ Scheme.basicOpen _ (AffineSpace.coord C.Z i) := by
        intro t
        have e1 : f ⁻¹ᵁ Scheme.basicOpen _ (AffineSpace.coord C.Z i) =
            W.toScheme.basicOpen (W.topIso.inv.hom (u i)) := by
          rw [Scheme.preimage_basicOpen_top, hf, AffineSpace.homOfVector_appTop_coord]
        have e2 := W.ι_image_basicOpen_topIso_inv (u i)
        rw [← e2, ← e1]
        exact Scheme.Hom.apply_mem_image_iff W.ι (x := t)
      refine (hP W hw (u i)).2 ?_
      rw [e y, hfy, ← e ⟨w, hw⟩]
      exact h1
    · refine (Ideal.IsPrime.radical_le_iff inferInstance).2 ?_
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      obtain ⟨V, hV, s, rfl⟩ := C.Z.presheaf.exists_germ_eq a
      rw [Ideal.mem_comap, Scheme.Hom.germ_stalkMap_apply]
      refine (hP _ _ _).2 ?_
      have h1 : C.GG.hom w ∉ C.Z.basicOpen s := by
        rw [C.Z.mem_basicOpen s _ hV]
        exact ha
      rw [← hg] at h1
      intro h2
      apply h1
      have e := Scheme.preimage_basicOpen C.GG.hom s
      exact e.ge h2
  apply eq_of_specializes_of_basicOpen hy'
  intro U hU s hs
  by_contra hn
  exact (hP U hU s).1 (hle ((hm U hU s).2 hn)) hs

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

noncomputable section
namespace GlobalTheory.SS.GenProj

theorem ext_of_dense {W X T Z : Scheme.{0}} (j : W ⟶ X)
    [IsSchemeTheoreticallyDominant j] {m m' : X ⟶ T} (g : T ⟶ Z) [IsSeparated g]
    (h₁ : j ≫ m = j ≫ m') (h₂ : m ≫ g = m' ≫ g) : m = m' := by
  let a : Over.mk (m ≫ g) ⟶ Over.mk g := Over.homMk m
  let b : Over.mk (m ≫ g) ⟶ Over.mk g := Over.homMk m' h₂.symm
  have : IsSeparated (Over.mk g).hom := ‹_›
  let c : Over.mk (j ≫ m ≫ g) ⟶ Over.mk (m ≫ g) := Over.homMk j
  have hc : c ≫ a = c ≫ b := by ext1; exact h₁
  have hk : (equalizer.ι a b).left.ker = ⊥ := by
    have e : (equalizer.lift c hc).left ≫ (equalizer.ι a b).left = j := by
      rw [← Over.comp_left, equalizer.lift_ι]; rfl
    have := (equalizer.lift c hc).left.le_ker_comp (equalizer.ι a b).left
    rw [e] at this
    exact le_bot_iff.mp (this.trans j.ker_eq_bot.le)
  have : IsIso (equalizer.ι a b).left := IsClosedImmersion.isIso_iff_ker_eq_bot.mpr hk
  rw [← cancel_epi (equalizer.ι a b).left]
  exact congr($(equalizer.condition a b).left)

theorem eq_of_generic {S E U X X' A : Scheme.{0}} (i : E ⟶ S) [IsSchemeTheoreticallyDominant i] [QuasiCompact i]
    (s : X ⟶ S) (s' : X' ⟶ S) [Flat s] [IsSeparated s'] (p : U ⟶ X) (q : U ⟶ X') [Flat p]
    (hs : p ≫ s = q ≫ s') (j : A ⟶ X) [Mono j] (j' : A ⟶ X')
    (H : ∀ (Z : Scheme.{0}) (a : Z ⟶ U) (t : Z ⟶ E), a ≫ p ≫ s = t ≫ i → ∃ c : Z ⟶ A, c ≫ j = a ≫ p ∧ c ≫ j' = a ≫ q)
    {Z : Scheme.{0}} (a b : Z ⟶ U) (hab : a ≫ p = b ≫ p) : a ≫ q = b ≫ q := by
  have key : pullback.fst p p ≫ q = pullback.snd p p ≫ q := by
    let w := pullback.fst p p ≫ p ≫ s
    have : Flat w := by dsimp only [w]; infer_instance
    refine ext_of_dense (pullback.fst w i) s' ?_ ?_
    · obtain ⟨c₁, h₁, h₁'⟩ := H _ (pullback.fst w i ≫ pullback.fst p p) (pullback.snd w i)
        (by rw [← pullback.condition]; simp [w])
      obtain ⟨c₂, h₂, h₂'⟩ := H _ (pullback.fst w i ≫ pullback.snd p p) (pullback.snd w i)
        (by rw [← pullback.condition, Category.assoc, ← pullback.condition_assoc])
      have e : c₁ = c₂ := by
        rw [← cancel_mono j, h₁, h₂, Category.assoc, Category.assoc, pullback.condition]
      rw [← Category.assoc, ← Category.assoc, ← h₁', ← h₂', e]
    · rw [Category.assoc, Category.assoc, ← hs, pullback.condition_assoc]
  have := congrArg (fun x => pullback.lift a b hab ≫ x) key
  simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this

theorem exists_image {U X : Scheme.{0}} (p : U ⟶ X) [Flat p] [LocallyOfFinitePresentation p] :
    ∃ (V : X.Opens) (p' : U ⟶ V.toScheme), p' ≫ V.ι = p ∧ Flat p' ∧ LocallyOfFinitePresentation p' ∧ Surjective p' := by
  let V : X.Opens := ⟨Set.range p, p.isOpenMap.isOpen_range⟩
  have hr : Set.range p ⊆ Set.range V.ι := by rw [Scheme.Opens.range_ι]; exact subset_rfl
  have e : IsOpenImmersion.lift V.ι p hr ≫ V.ι = p := IsOpenImmersion.lift_fac _ _ _
  have hP : IsPullback (IsOpenImmersion.lift V.ι p hr) (𝟙 U) V.ι p :=
    IsPullback.of_vert_isIso_mono ⟨by rw [e, Category.id_comp]⟩
  refine ⟨V, IsOpenImmersion.lift V.ι p hr, e, ?_, ?_, ⟨?_⟩⟩
  · exact MorphismProperty.of_isPullback (P := @Flat) hP.flip ‹_›
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hP.flip ‹_›
  · rintro ⟨_, u, rfl⟩
    refine ⟨u, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, e]; rfl

theorem exists_openImmersion {U X X' : Scheme.{0}} (p : U ⟶ X) (q : U ⟶ X') [Flat p] [LocallyOfFinitePresentation p]
    [Flat q] [LocallyOfFinitePresentation q]
    (H : ∀ (Z : Scheme.{0}) (a b : Z ⟶ U), a ≫ p = b ≫ p ↔ a ≫ q = b ≫ q) :
    ∃ (V : X.Opens) (p' : U ⟶ V.toScheme) (h : V.toScheme ⟶ X'), p' ≫ V.ι = p ∧ Flat p' ∧ Surjective p' ∧
      p' ≫ h = q ∧ IsOpenImmersion h := by
  obtain ⟨V, p', hp, _, _, _⟩ := exists_image p
  obtain ⟨V', q', hq, _, _, _⟩ := exists_image q
  have H' : ∀ (Z : Scheme.{0}) (a b : Z ⟶ U), a ≫ p' = b ≫ p' ↔ a ≫ q' = b ≫ q' := by
    intro Z a b
    rw [← cancel_mono V.ι, ← cancel_mono V'.ι]
    simpa [hp, hq] using H Z a b
  let u := EffectiveEpi.desc p' q' (fun a b h => (H' _ a b).1 h)
  let v := EffectiveEpi.desc q' p' (fun a b h => (H' _ a b).2 h)
  have hu : p' ≫ u = q' := EffectiveEpi.fac _ _ _
  have hv : q' ≫ v = p' := EffectiveEpi.fac _ _ _
  have : IsIso u := ⟨v, by rw [← cancel_epi p', ← Category.assoc, hu, hv, Category.comp_id],
    by rw [← cancel_epi q', ← Category.assoc, hv, hu, Category.comp_id]⟩
  exact ⟨V, p', u ≫ V'.ι, hp, ‹_›, ‹_›, by rw [← Category.assoc, hu, hq], inferInstance⟩

variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}

theorem prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j := by
  have h : (M.prod N).e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y) = fst A A' ≫ M.e.inv := by
    simp [Model.prod]
  have h2 := congrArg (fun q => q.left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))) h
  have h4 : ((Over.pullback (spMap (algebraMap R K))).map (fst M.Y N.Y)).left ≫ pullback.fst M.Y.hom (spMap (algebraMap R K))
      = pullback.fst (M.prod N).Y.hom (spMap (algebraMap R K)) ≫ (fst M.Y N.Y).left := pullback.lift_fst _ _ _
  simp only [Over.comp_left, Category.assoc] at h2
  exact (Category.assoc _ _ _).trans ((congrArg (fun q => (M.prod N).e.inv.left ≫ q) h4).symm.trans h2)

theorem exists_lift_j (M : Model R A) {Z : Scheme.{0}} (a : Z ⟶ M.Y.left) (t : Z ⟶ Sp K)
    (h : a ≫ M.Y.hom = t ≫ spMap (algebraMap R K)) : ∃ d : Z ⟶ A.left, d ≫ M.j = a := by
  refine ⟨pullback.lift a t h ≫ M.e.hom.left, ?_⟩
  have e : M.e.hom.left ≫ M.e.inv.left = 𝟙 _ := by rw [← Over.comp_left, Iso.hom_inv_id]; rfl
  unfold Model.j
  rw [Category.assoc, ← Category.assoc M.e.hom.left, e]
  exact (congrArg _ (Category.id_comp _)).trans (pullback.lift_fst _ _ _)

theorem mono_j [IsFractionRing R K] (M : Model R A) : Mono M.j := by
  have : IsPreimmersion (spMap (algebraMap R K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have : Mono (pullback.fst M.Y.hom (spMap (algebraMap R K))) := inferInstance
  exact mono_comp' inferInstance this

theorem genIso_of_prod : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A A' B B' : Over (Sp K)) [IsIntegral A.left] [IsIntegral (A ⊗ B).left] (M : Model R A) (M' : Model R A') (N : Model R B) (N' : Model R B') (f : A ≅ A') (Θ : A ⊗ B ⟶ A' ⊗ B'), M.Irr → M'.Irr → N.Irr → N'.Irr → Θ ≫ fst A' B' = fst A B ≫ f.hom → GenIso (M.prod N) (M'.prod N') Θ → GenIso M M' f.hom := by
  intro R K _ _ _ _ _ hSH A A' B B' _ _ M M' N N' f Θ _ _ _ _ hΘ ⟨z, hz, U, g, hzU, ⟨hg₁, hg₂⟩, hgo⟩
  have := hSH.2.2.2
  have := M.smooth; have := M'.smooth; have := N.smooth; have := N'.smooth
  have := M.sep; have := M'.sep
  have := mono_j M; have := mono_j M'
  have : IsDominant (spMap (algebraMap R K)) := by
    refine ⟨?_⟩
    show DenseRange (PrimeSpectrum.comap (algebraMap R K))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap R K))
  have : IsIso f.hom.left := inferInstanceAs (IsIso ((Over.forget _).map f.hom))
  let π : (M.prod N).Y.left ⟶ M.Y.left := (fst M.Y N.Y).left
  let π' : (M'.prod N').Y.left ⟶ M'.Y.left := (fst M'.Y N'.Y).left
  have : Smooth π := inferInstanceAs (Smooth (pullback.fst M.Y.hom N.Y.hom))
  have : Smooth π' := inferInstanceAs (Smooth (pullback.fst M'.Y.hom N'.Y.hom))
  have hπ : π ≫ M.Y.hom = (M.prod N).Y.hom := Over.w (fst M.Y N.Y)
  have hπ' : π' ≫ M'.Y.hom = (M'.prod N').Y.hom := Over.w (fst M'.Y N'.Y)
  have hj : (M.prod N).j ≫ π = (fst A B).left ≫ M.j := prod_j_fst M N
  have hj' : (M'.prod N').j ≫ π' = (fst A' B').left ≫ M'.j := prod_j_fst M' N'
  have hs : (U.ι ≫ π) ≫ M.Y.hom = (g ≫ π') ≫ M'.Y.hom := by
    rw [Category.assoc, Category.assoc, hπ, hπ', hg₁]
  have H : ∀ (Z : Scheme.{0}) (a : Z ⟶ U.toScheme) (t : Z ⟶ Sp K),
      a ≫ (U.ι ≫ π) ≫ M.Y.hom = t ≫ spMap (algebraMap R K) →
      ∃ c : Z ⟶ A.left, c ≫ M.j = a ≫ U.ι ≫ π ∧ c ≫ f.hom.left ≫ M'.j = a ≫ g ≫ π' := by
    intro Z a t h
    obtain ⟨d, hd⟩ := exists_lift_j (M.prod N) (a ≫ U.ι) t (by rw [← h, ← hπ]; simp only [Category.assoc])
    obtain ⟨d', h₁, h₂⟩ := (isPullback_morphismRestrict (M.prod N).j U).exists_lift a d hd.symm
    refine ⟨d ≫ (fst A B).left, ?_, ?_⟩
    · rw [Category.assoc, ← hj, ← Category.assoc, hd, Category.assoc]
    · have e : Θ.left ≫ (fst A' B').left = (fst A B).left ≫ f.hom.left := by
        rw [← Over.comp_left, hΘ, Over.comp_left]
      rw [← h₁, ← h₂]
      simp only [Category.assoc]
      rw [reassoc_of% hg₂, hj', reassoc_of% e]
  obtain ⟨V, p', h, hp, _, _, hq, hh⟩ := exists_openImmersion (U.ι ≫ π) (g ≫ π') (fun Z a b =>
    ⟨eq_of_generic (spMap (algebraMap R K)) M.Y.hom M'.Y.hom _ _ hs M.j (f.hom.left ≫ M'.j) H a b,
     eq_of_generic (spMap (algebraMap R K)) M'.Y.hom M.Y.hom _ _ hs.symm (f.hom.left ≫ M'.j) M.j
      (fun Z a t h => (H Z a t (by rw [hs, h])).imp fun _ h => h.symm) a b⟩)
  have : Epi p' := Flat.epi_of_flat_of_surjective _
  refine ⟨π z, ?_, V, h, ?_, ⟨?_, ?_⟩, hh⟩
  · show M.Y.hom (π z) = _
    rw [← Scheme.Hom.comp_apply, hπ]; exact hz
  · have : V.ι (p' ⟨z, hzU⟩) = π z := congrArg (fun q : U.toScheme ⟶ M.Y.left => q ⟨z, hzU⟩) hp
    rw [← this]; exact (p' ⟨z, hzU⟩).2
  · rw [← cancel_epi p', reassoc_of% hq, reassoc_of% hp]
    simpa only [Category.assoc] using hs.symm
  · have : Epi (pullback.snd p' (M.j ∣_ V)) := Flat.epi_of_flat_of_surjective _
    have e : pullback.fst p' (M.j ∣_ V) ≫ U.ι ≫ π = (pullback.snd p' (M.j ∣_ V) ≫ (M.j ⁻¹ᵁ V).ι) ≫ M.j := by
      rw [← hp, pullback.condition_assoc, morphismRestrict_ι, Category.assoc]
    obtain ⟨c, hc₁, hc₂⟩ := H _ (pullback.fst p' (M.j ∣_ V)) (pullback.snd p' (M.j ∣_ V) ≫ (M.j ⁻¹ᵁ V).ι ≫ A.hom)
      (by rw [← Category.assoc, e, Category.assoc, M.j_hom]; simp only [Category.assoc])
    rw [e, cancel_mono] at hc₁
    rw [← cancel_epi (pullback.snd p' (M.j ∣_ V)), ← pullback.condition_assoc, hq, ← hc₂, hc₁, Category.assoc]

end GlobalTheory.SS.GenProj
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory

theorem henselianLocalRing_valuationSubring_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K]
    (V : ValuationSubring K) : HenselianLocalRing V where
  is_henselian f hf a₀ h₁ _ := by
    classical
    have hg : (f.map (algebraMap V K)).Monic := hf.map _
    have hsplit : (f.map (algebraMap V K)).Splits := IsAlgClosed.splits _

    have hev : ((f.eval a₀ : V) : K) =
        ((f.map (algebraMap V K)).roots.map fun r => (a₀ : K) - r).prod := by
      have h1 : ((f.eval a₀ : V) : K) = (f.map (algebraMap V K)).eval (a₀ : K) := by
        rw [Polynomial.eval_map]
        exact (Polynomial.eval₂_at_apply (algebraMap V K) a₀).symm
      rw [h1]
      exact hsplit.eval_eq_prod_roots_of_monic hg _
    have hlt : V.valuation (((f.map (algebraMap V K)).roots.map fun r => (a₀ : K) - r).prod) < 1 := by
      rw [← hev]
      exact (ValuationSubring.valuation_lt_one_iff V _).mp h₁
    rw [map_multiset_prod, Multiset.map_map] at hlt

    obtain ⟨r, hr, hrlt⟩ : ∃ r ∈ (f.map (algebraMap V K)).roots, V.valuation ((a₀ : K) - r) < 1 := by
      by_contra hcon
      push Not at hcon
      refine absurd hlt (not_lt.mpr (Multiset.one_le_prod_of_one_le ?_))
      simp only [Multiset.mem_map, Function.comp_apply]
      rintro _ ⟨s, hs, rfl⟩
      exact hcon s hs
    have hrV : r ∈ V := by
      rw [← V.valuation_le_one_iff]
      have h2 : r = (a₀ : K) - ((a₀ : K) - r) := by ring
      rw [h2]
      exact (Valuation.map_sub _ _ _).trans (max_le (V.valuation_le_one a₀) hrlt.le)
    refine ⟨⟨r, hrV⟩, ?_, ?_⟩
    · have hroot := (Polynomial.mem_roots hg.ne_zero).mp hr
      show Polynomial.eval _ f = 0
      apply Subtype.ext
      have h3 := Polynomial.eval₂_at_apply (p := f) (algebraMap V K) (⟨r, hrV⟩ : V)
      rw [← Polynomial.eval_map] at h3
      simpa using h3.symm.trans hroot
    · rw [ValuationSubring.valuation_lt_one_iff]
      have h4 : ((((⟨r, hrV⟩ : V) - a₀ : V)) : K) = r - a₀ := rfl
      rw [h4, Valuation.map_sub_swap]
      exact hrlt

theorem ZJ.exists_classical_lift_of_smooth :
    ∀ (p : ℕ) [Fact p.Prime] (X S : Scheme.{0}) (f : X ⟶ S) [Smooth f] (y : Sp (OO p) ⟶ S) (x : Sp (kb p) ⟶ X), x ≫ f = rPt p ≫ y → ∃ b : Sp (OO p) ⟶ X, b ≫ f = y ∧ rPt p ≫ b = x := by
  intro p _ X S f _ y x hx
  have : HenselianLocalRing (OO p) := henselianLocalRing_valuationSubring_of_isAlgClosed _
  obtain ⟨⟨b, hb⟩, hb'⟩ := reducePoint_residue_surjective f (OO p) y ⟨x, hx⟩
  exact ⟨b, hb, congrArg Subtype.val hb'⟩

end GlobalTheory
end
