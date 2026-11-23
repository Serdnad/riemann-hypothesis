module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Order.CompletePartialOrder
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Limits.Shapes.Connected
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Std.Tactic.BVDecide.Normalize.Prop
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle026
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.StTransl

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

namespace GlobalTheory.CompanionTheory.PointSurjectivity


open GlobalTheory.Cube in
private noncomputable def suppHom {ν κ : Type} [LinearOrder ν] [LinearOrder κ] {R : Type} [CommRing R]
    (A : GlobalTheory.Cube.{0} (ν ⊕ₗ κ) R) (P P' : Set (Finset (ν ⊕ₗ κ)))
    (hP : P.OrdConnected) (hP' : P'.OrdConnected)
    (h : ∀ ⦃s t⦄, s ⊆ t → s ∈ P → t ∈ P' → (t ∈ P ↔ s ∈ P')) :
    supp A P hP ⟶ supp A P' hP' := by
  classical
  refine Cube.homMk _ _ (suppMapApp (𝟙 A) hP hP') ?_
  intro s t hst x
  by_cases hs : s ∈ P
  · refine supp_ext fun ht' => ?_
    by_cases ht : t ∈ P
    · have hs' := (h hst hs ht').1 ht
      rw [suppEquiv_suppMapApp (𝟙 A) ht, suppEquiv_res hst hs, suppEquiv_res hst hs',
        suppEquiv_suppMapApp (𝟙 A) hs, app_res]
    · have hs' := mt (h hst hs ht').2 ht
      have := subsingleton_supp A hP ht
      have := subsingleton_supp A hP' hs'
      rw [Subsingleton.elim (res _ hst x) 0, Subsingleton.elim (suppMapApp (𝟙 A) hP hP' s x) 0]
      simp only [map_zero]
  · have := subsingleton_supp A hP hs
    rw [Subsingleton.elim x 0]
    simp only [map_zero]

open GlobalTheory.Cube in
theorem isZero_homology_supp_singleton {ν κ : Type} [LinearOrder ν] [LinearOrder κ] {R : Type}
    [CommRing R] (A : GlobalTheory.Cube.{0} (ν ⊕ₗ κ) R) {Q : Set (Finset ν)} (hQ : Q.OrdConnected)
    (hT₁ : Set.OrdConnected {t : Finset κ | t.card = 1}) (j : κ) (n : ℕ)
    (h : Limits.IsZero ((GlobalTheory.cubeComplex (supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q
      {t : Finset κ | t.card = 1}) (ordConnected_partsIn _ _ hQ hT₁))).homology n)) :
    Limits.IsZero ((GlobalTheory.cubeComplex (supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {{j}})
      (ordConnected_partsIn _ _ hQ Set.ordConnected_singleton))).homology n) := by
  have hsub : ∀ u, u ∈ partsIn (inlEmb ν κ) (inrEmb ν κ) Q {{j}} →
      u ∈ partsIn (inlEmb ν κ) (inrEmb ν κ) Q {t : Finset κ | t.card = 1} := by
    intro u hu
    refine ⟨hu.1, ?_⟩
    have : part (inrEmb ν κ) u = {j} := hu.2
    simp [this]
  have heq : ∀ {a b : Finset κ}, a ⊆ b → a = {j} → b.card = 1 → b = {j} := by
    rintro a b hab rfl hb
    obtain ⟨c, rfl⟩ := Finset.card_eq_one.1 hb
    rw [Finset.singleton_subset_singleton.1 hab]
  have heq' : ∀ {a b : Finset κ}, a ⊆ b → a.card = 1 → b = {j} → a = {j} := by
    rintro a b hab ha rfl
    obtain ⟨c, rfl⟩ := Finset.card_eq_one.1 ha
    rw [Finset.singleton_subset_singleton.1 hab]
  let i : supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {{j}})
        (ordConnected_partsIn _ _ hQ Set.ordConnected_singleton) ⟶
      supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {t : Finset κ | t.card = 1})
        (ordConnected_partsIn _ _ hQ hT₁) :=
    suppHom A _ _ _ _ fun s t hst hs ht => iff_of_true
      ⟨ht.1, heq (monotone_part _ hst) hs.2 ht.2⟩ (hsub s hs)
  let r : supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {t : Finset κ | t.card = 1})
        (ordConnected_partsIn _ _ hQ hT₁) ⟶
      supp A (partsIn (inlEmb ν κ) (inrEmb ν κ) Q {{j}})
        (ordConnected_partsIn _ _ hQ Set.ordConnected_singleton) :=
    suppHom A _ _ _ _ fun s t hst hs ht => iff_of_true (hsub t ht)
      ⟨hs.1, heq' (monotone_part _ hst) hs.2 ht.2⟩
  have hir : i ≫ r = 𝟙 _ := by
    ext s x
    refine supp_ext fun hs => ?_
    change suppEquiv A _ hs (suppMapApp (𝟙 A) _ _ s (suppMapApp (𝟙 A) _ _ s x)) =
      suppEquiv A _ hs x
    rw [suppEquiv_suppMapApp _ (hsub s hs) hs, suppEquiv_suppMapApp _ hs (hsub s hs)]
    rfl
  rw [Limits.IsZero.iff_id_eq_zero]
  have hc : HomologicalComplex.homologyMap ((GlobalTheory.cubeFunctor (ν ⊕ₗ κ) R).map i) n ≫
      HomologicalComplex.homologyMap ((GlobalTheory.cubeFunctor (ν ⊕ₗ κ) R).map r) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp, ← CategoryTheory.Functor.map_comp, hir,
      CategoryTheory.Functor.map_id, HomologicalComplex.homologyMap_id]
  have hz : HomologicalComplex.homologyMap ((GlobalTheory.cubeFunctor (ν ⊕ₗ κ) R).map i) n = 0 :=
    h.eq_of_tgt _ _
  rw [hz, Limits.zero_comp] at hc
  exact hc.symm


open GlobalTheory.Cube in
theorem cechComplex_sliceFst_singleton_acyclic_of_trunc₂ : ∀ {ν κ : Type} [LinearOrder ν] [LinearOrder κ] [Finite ν] [Finite κ] {R : Type} [CommRing R]
    (A : GlobalTheory.Cube.{0} (ν ⊕ₗ κ) R)
    (hA : ∀ t : Finset κ, 2 ≤ t.card → (GlobalTheory.cechComplex (GlobalTheory.Cube.sliceFst A t)).Acyclic)
    (hT : ∀ n, Limits.IsZero ((GlobalTheory.cubeComplex (GlobalTheory.Cube.trunc₂ A)).homology (n + 2))) (j : κ), (GlobalTheory.cechComplex (GlobalTheory.Cube.sliceFst A {j})).Acyclic := by
  intro ν κ _ _ _ _ R _ A hA hT j
  have hcompl := isCompl_range_inlEmb_inrEmb ν κ
  have hQ : Set.OrdConnected {s : Finset ν | s.Nonempty} := ordConnected_nonempty
  have hU₂ : IsUpperSet {t : Finset κ | 2 ≤ t.card} :=
    fun _ _ hst ht => le_trans ht (Finset.card_le_card hst)
  have hT₂ := hU₂.ordConnected
  have hT₁ : Set.OrdConnected {t : Finset κ | t.card = 1} := by
    refine ⟨fun a ha b hb c hc => ?_⟩
    have h1 := Finset.card_le_card hc.1
    have h2 := Finset.card_le_card hc.2
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    omega
  let P₁ := partsIn (inlEmb ν κ) (inrEmb ν κ) {s : Finset ν | s.Nonempty} {t : Finset κ | 2 ≤ t.card}
  let P := partsIn (inlEmb ν κ) (inrEmb ν κ) {s : Finset ν | s.Nonempty} {t : Finset κ | t.Nonempty}
  let P₂ := partsIn (inlEmb ν κ) (inrEmb ν κ) {s : Finset ν | s.Nonempty} {t : Finset κ | t.card = 1}
  let hp₁ := ordConnected_partsIn (inlEmb ν κ) (inrEmb ν κ) hQ hT₂
  let hp := ordConnected_partsIn (inlEmb ν κ) (inrEmb ν κ) hQ ordConnected_nonempty
  let hp₂ := ordConnected_partsIn (inlEmb ν κ) (inrEmb ν κ) hQ hT₁
  have h : ∀ s, s ∈ P ↔ s ∈ P₁ ∨ s ∈ P₂ := by
    intro u
    have hc : (part (inrEmb ν κ) u).Nonempty ↔
        2 ≤ (part (inrEmb ν κ) u).card ∨ (part (inrEmb ν κ) u).card = 1 := by
      rw [← Finset.card_pos]
      omega
    simp only [P, P₁, P₂, mem_partsIn, Set.mem_setOf_eq]
    tauto
  have hd : ∀ s ∈ P₁, s ∉ P₂ := by
    intro u hu hu'
    have h1 : 2 ≤ (part (inrEmb ν κ) u).card := hu.2
    have h2 : (part (inrEmb ν κ) u).card = 1 := hu'.2
    omega
  have hu : ∀ ⦃s t⦄, s ⊆ t → s ∈ P₁ → t ∈ P → t ∈ P₁ :=
    fun _ _ hst hs ht => ⟨ht.1, hU₂ (monotone_part _ hst) hs.2⟩
  let f := suppHom A P₁ P hp₁ hp fun s _ hst hs ht => iff_of_true (hu hst hs ht) ((h s).2 (Or.inl hs))
  let g := suppHom A P P₂ hp hp₂ fun s t hst hs ht => iff_of_true ((h t).2 (Or.inr ht))
    (((h s).1 hs).resolve_left fun hs₁ => hd t (hu hst hs₁ ((h t).2 (Or.inr ht))) ht)
  have hfg : f ≫ g = 0 := by
    ext s x
    by_cases hs : s ∈ P₁
    · exact (subsingleton_supp A hp₂ (hd s hs)).elim _ _
    · rw [(subsingleton_supp A hp₁ hs).elim x 0]
      simp only [map_zero]
  let S := ShortComplex.mk f g hfg
  have hS := GlobalTheory.cubeFunctor_shortExact S (fun s => by
    have key : Function.Exact (suppMapApp (𝟙 A) hp₁ hp s) (suppMapApp (𝟙 A) hp hp₂ s) ∧
        Function.Injective (suppMapApp (𝟙 A) hp₁ hp s) ∧
        Function.Surjective (suppMapApp (𝟙 A) hp hp₂ s) := by
      by_cases hs : s ∈ P₁
      · have := subsingleton_supp A hp₂ (hd s hs)
        have hb : Function.Bijective (suppMapApp (𝟙 A) hp₁ hp s) :=
          suppMapApp_bijective _ (iff_of_true hs ((h s).2 (Or.inl hs))) fun _ => Function.bijective_id
        exact ⟨fun y => iff_of_true (Subsingleton.elim _ _) (hb.2 y), hb.1, Function.surjective_to_subsingleton _⟩
      · have := subsingleton_supp A hp₁ hs
        have hb : Function.Bijective (suppMapApp (𝟙 A) hp hp₂ s) :=
          suppMapApp_bijective _ (by change s ∈ P ↔ s ∈ P₂; rw [h s]; simp only [hs, false_or]) fun _ => Function.bijective_id
        refine ⟨fun y => ?_, Function.injective_of_subsingleton _, hb.2⟩
        rw [map_eq_zero_iff _ hb.1]
        exact ⟨fun hy => ⟨0, by rw [map_zero, hy]⟩, by
          rintro ⟨x, rfl⟩; rw [Subsingleton.elim x 0, map_zero]⟩
    exact ModuleCat.shortComplex_shortExact _ key.1 key.2.1 key.2.2)
  have h₁ : (GlobalTheory.cubeComplex (supp A _ (ordConnected_partsIn (inlEmb ν κ) (inrEmb ν κ) hQ hT₂))).Acyclic := by
    rw [supp_partsIn_comm hQ hT₂ A]
    refine GlobalTheory.cubeComplex_supp_partsIn_acyclic hcompl.symm hT₂ hQ A fun t ht => ?_
    refine (GlobalTheory.cubeComplex_trunc₁_acyclic_iff _).2 ?_
    rw [← sliceFst_eq_slice]
    exact hA t ht
  have hzero : ∀ n, Limits.IsZero ((GlobalTheory.cubeComplex (supp A (partsIn (inlEmb ν κ) (inrEmb ν κ)
      {s : Finset ν | s.Nonempty} {{j}})
      (ordConnected_partsIn _ _ hQ Set.ordConnected_singleton))).homology (n + 2)) := fun n => by
    refine isZero_homology_supp_singleton A hQ hT₁ j (n + 2) ?_
    have := GlobalTheory.isIso_homologyMap_g_of_acyclic hS h₁ (n + 2)
    exact (hT n).of_iso (@asIso _ _ _ _ _ this).symm
  let truncIso (B : Cube ν R) (n : ℕ) :
      (GlobalTheory.cubeComplex (trunc₁ B)).homology (n + 1) ≅
        (GlobalTheory.cechComplex B).homology n := by
    classical
    let incl : supp B {s | s.Nonempty} ordConnected_nonempty ⟶ B := Cube.homMk _ _
      (fun s => if hs : s.Nonempty then (suppEquiv B ordConnected_nonempty hs).toLinearMap else 0) (by
        intro s t hst x
        by_cases hs : s.Nonempty
        · have ht : t.Nonempty := isUpperSet_nonempty hst hs
          simp only [dif_pos hs, dif_pos ht, LinearEquiv.coe_coe]
          exact suppEquiv_res hst hs ht x
        · have := subsingleton_supp B ordConnected_nonempty hs
          rw [Subsingleton.elim x 0]
          simp only [map_zero])
    have hi : IsIso (GlobalTheory.cechComplexMap incl) :=
      GlobalTheory.isIso_cechComplexMap _ fun s hs => by
        change Function.Bijective ⇑(if h : s.Nonempty then (suppEquiv B ordConnected_nonempty h).toLinearMap else 0)
        rw [dif_pos hs]
        exact (suppEquiv B ordConnected_nonempty hs).bijective
    exact GlobalTheory.cubeHomologySuccIsoCech _ (subsingleton_trunc₁_empty B) n ≪≫
      HomologicalComplex.homologyMapIso (@asIso _ _ _ _ _ hi) n
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine ((hzero n).of_iso
    (GlobalTheory.suppSingletonHomologyIso hcompl hQ j A (n + 1)).symm).of_iso
    (GlobalTheory.cechHomologyMapIso (eqToIso (sliceFst_eq_slice A {j})) n ≪≫
      (truncIso _ n).symm)

end GlobalTheory.CompanionTheory.PointSurjectivity
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity

noncomputable section

namespace GlobalTheory.CompanionTheory.CoverPoints

theorem exists_affine_cover_finite_closed_points : ∀ (X : Scheme.{0}) [CompactSpace X] (F : Set X) (hF : F.Finite) (hc : ∀ x ∈ F, IsClosed ({x} : Set X)), ∃ (r : ℕ) (V : Fin (r + 1) → X.Opens), (∀ j, IsAffineOpen (V j)) ∧ ⨆ j, V j = ⊤ ∧
      ∀ x ∈ F, ∀ i j, x ∈ V i → x ∈ V j → i = j := by
  intro X _ F hF hc
  have hcl : ∀ G : Set X, G ⊆ F → IsClosed G := fun G hG => by
    have h := (hF.subset hG).isClosed_biUnion (fun x hx => hc x (hG hx))
    simpa using h

  have hW : ∀ x : F, ∃ W : X.Opens, IsAffineOpen W ∧ x.1 ∈ W ∧ ∀ y ∈ F, y ∈ W → y = x.1 := by
    intro x
    have hx : x.1 ∈ (F \ {x.1})ᶜ := fun h => h.2 rfl
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWo⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx
      (hcl _ Set.diff_subset).isOpen_compl
    refine ⟨W, hW, hxW, fun y hy hyW => ?_⟩
    by_contra hne
    exact hWo hyW ⟨hy, hne⟩
  choose W hWa hWx hWF using hW

  have hC : IsCompact ((⨆ x, W x : X.Opens) : Set X)ᶜ :=
    (⨆ x, W x : X.Opens).isOpen.isClosed_compl.isCompact
  obtain ⟨s, hs⟩ := hC.elim_finite_subcover
    (fun U : {U : X.Opens // IsAffineOpen U ∧ ∀ x ∈ F, x ∉ U} => (U.1 : Set X))
    (fun U => U.1.isOpen) (by
      intro y hy
      have hy' : y ∈ Fᶜ := fun h => hy (by
        exact (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨y, h⟩, hWx ⟨y, h⟩⟩ : y ∈ (⨆ x, W x : X.Opens)))
      obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hUo⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hy'
        (hcl F subset_rfl).isOpen_compl
      exact Set.mem_iUnion.2 ⟨⟨U, hU, fun x hx hxU => hUo hxU hx⟩, hyU⟩)
  haveI : Fintype F := hF.fintype

  let V' : Option (F ⊕ s) → X.Opens := fun a => match a with
    | none => ⊥
    | some (Sum.inl x) => W x
    | some (Sum.inr U) => U.1.1
  have hV'a : ∀ a, IsAffineOpen (V' a) := by
    rintro (_ | x | U)
    · exact isAffineOpen_bot X
    · exact hWa x
    · exact U.1.2.1
  have hV'F : ∀ x (hx : x ∈ F) a, x ∈ V' a → a = some (Sum.inl ⟨x, hx⟩) := by
    rintro x hx (_ | y | U) h
    · exact absurd h (by simp [V'])
    · have : x = y.1 := hWF y x hx h
      subst this
      rfl
    · exact absurd h (U.1.2.2 x hx)
  let e : Option (F ⊕ s) ≃ Fin (Fintype.card (F ⊕ s) + 1) :=
    Fintype.equivFinOfCardEq Fintype.card_option
  refine ⟨Fintype.card (F ⊕ s), fun j => V' (e.symm j), fun j => hV'a _, ?_, ?_⟩
  · refine top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ?_
    by_cases hy : y ∈ (⨆ x, W x : X.Opens)
    · obtain ⟨x, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
      exact ⟨e (some (Sum.inl x)), by simpa [V'] using hx⟩
    · obtain ⟨U, hU, hyU⟩ := Set.mem_iUnion₂.1 (hs hy)
      exact ⟨e (some (Sum.inr ⟨U, hU⟩)), by simpa [V'] using hyU⟩
  · intro x hx i j hi hj
    exact e.symm.injective ((hV'F x hx _ hi).trans (hV'F x hx _ hj).symm)

end GlobalTheory.CompanionTheory.CoverPoints
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.KerPull.Kernel

section General

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] {A A' H : C} [GrpObj A] [GrpObj A']
  {q : A ⟶ A'} [IsMonHom q] {i : H ⟶ A}

theorem mono_of_isKernel (hp : IsPullback i (toUnit H) q η[A']) : Mono i :=
  ⟨fun _ _ e => hp.hom_ext e (toUnit_unique _ _)⟩

def kerLift (hp : IsPullback i (toUnit H) q η[A']) {W : C} (f : W ⟶ A) (hf : f ≫ q = 1) : W ⟶ H :=
  hp.lift f (toUnit W) (by rw [hf, Hom.one_def])

theorem kerLift_comp (hp : IsPullback i (toUnit H) q η[A']) {W : C} (f : W ⟶ A) (hf : f ≫ q = 1) :
    kerLift hp f hf ≫ i = f :=
  hp.lift_fst ..

theorem comp_kills (hp : IsPullback i (toUnit H) q η[A']) {W : C} (x : W ⟶ H) : (x ≫ i) ≫ q = 1 := by
  rw [Category.assoc, hp.w, ← Category.assoc, toUnit_unique (x ≫ toUnit H) (toUnit W), Hom.one_def]

@[instance_reducible]
def grpObjOfIsKernel (hp : IsPullback i (toUnit H) q η[A']) : GrpObj H :=
  have := mono_of_isKernel hp
  { one := kerLift hp η[A] (by rw [IsMonHom.one_hom, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp])
    mul := kerLift hp (fst H H ≫ i * snd H H ≫ i) (by
      rw [MonObj.mul_comp, comp_kills hp, comp_kills hp, _root_.mul_one])
    inv := kerLift hp (i ≫ ι[A]) (by
      have e : i ≫ q = 1 := by simpa using comp_kills hp (𝟙 H)
      have h : (i⁻¹ * i) ≫ q = 1 := by rw [inv_mul_cancel, MonObj.one_comp]
      rw [MonObj.mul_comp, e, _root_.mul_one] at h
      exact h)
    one_mul := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [toUnit_unique (fst (𝟙_ C) H) (toUnit _), ← Hom.one_def, _root_.one_mul, leftUnitor_hom]
    mul_one := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [toUnit_unique (snd H (𝟙_ C)) (toUnit _), ← Hom.one_def, _root_.mul_one, rightUnitor_hom]
    mul_assoc := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      exact _root_.mul_assoc _ _ _
    left_inv := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [← Hom.one_def]
      exact inv_mul_cancel i
    right_inv := by
      rw [← cancel_mono i]
      simp [kerLift_comp, MonObj.comp_mul]
      rw [← Hom.one_def]
      exact mul_inv_cancel i }

theorem isMonHom_of_isKernel (hp : IsPullback i (toUnit H) q η[A']) :
    letI := grpObjOfIsKernel hp
    IsMonHom i := by
  letI := grpObjOfIsKernel hp
  refine { one_hom := kerLift_comp hp _ _, mul_hom := ?_ }
  refine (kerLift_comp hp _ _).trans ?_
  rw [Hom.mul_def]
  simp

theorem isCommMonObj_of_isKernel [BraidedCategory C] [IsCommMonObj A]
    (hp : IsPullback i (toUnit H) q η[A']) :
    letI := grpObjOfIsKernel hp
    IsCommMonObj H := by
  letI := grpObjOfIsKernel hp
  have := mono_of_isKernel hp
  have := isMonHom_of_isKernel hp
  refine (isCommMonObj_iff_isMulCommutative _).mpr fun T => ⟨⟨fun x y => ?_⟩⟩
  rw [← cancel_mono i, MonObj.mul_comp, MonObj.mul_comp, mul_comm]

end General

theorem exists_finite_kernel : ∀ (k : Type) [Field k] (A A' : Over (Sp k)) [GrpObj A] [GrpObj A'], IsAbelianScheme A → ∀ (q : A ⟶ A'), IsMonHom q → IsFinite q.left →
    ∃ (H : Over (Sp k)) (_ : GrpObj H) (_ : IsCommMonObj H) (i : H ⟶ A), IsMonHom i ∧ IsFinite H.hom ∧
      IsPullback i (toUnit _) q η[A'] := by
  intro k _ A A' _ _ hA q hq hf
  have := hA.comm
  have hp : IsPullback (pullback.fst q η[A']) (toUnit (pullback q η[A'])) q η[A'] := by
    rw [toUnit_unique (toUnit _) (pullback.snd q η[A'])]
    exact IsPullback.of_hasPullback _ _
  refine ⟨pullback q η[A'], grpObjOfIsKernel hp, isCommMonObj_of_isKernel hp, pullback.fst _ _,
    isMonHom_of_isKernel hp, ?_, hp⟩
  have hl := hp.map (Over.forget _)
  have h1 : IsFinite (toUnit (pullback q η[A'])).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) hl hf
  have h2 : (pullback q η[A']).hom = (toUnit (pullback q η[A'])).left ≫ (𝟙_ (Over (Sp k))).hom :=
    (Over.w _).symm
  rw [h2]
  exact inferInstanceAs (IsFinite (_ ≫ 𝟙 _))
end GlobalTheory.CompanionTheory.KerPull.Kernel
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.FnDesc

theorem exists_app_eq_of_lfp {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π]
    [LocallyOfFinitePresentation π] (U : Y.Opens) (f : Γ(X, π ⁻¹ᵁ U))
    (hf : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ X) (h₁ : ⊤ ≤ g₁ ⁻¹ᵁ (π ⁻¹ᵁ U))
      (h₂ : ⊤ ≤ g₂ ⁻¹ᵁ (π ⁻¹ᵁ U)), g₁ ≫ π = g₂ ≫ π →
      (g₁.appLE _ ⊤ h₁).hom f = (g₂.appLE _ ⊤ h₂).hom f) :
    ∃ a, (π.app U).hom a = f := by
  have : Surjective (π ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› U
  have p := isPullback_morphismRestrict π U
  have : Flat (π ∣_ U) := MorphismProperty.of_isPullback (P := @Flat) p.flip ‹_›
  have : LocallyOfFinitePresentation (π ∣_ U) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) p.flip ‹_›
  obtain ⟨b, hb⟩ := GlobalTheory.FunDescent.exists_appTop_eq (π ∣_ U) ((GlobalTheory.FunDescent.res (π ⁻¹ᵁ U)).hom f) (by
    intro Z g₁ g₂ e
    have k : ∀ g : Z ⟶ (π ⁻¹ᵁ U).toScheme, ⊤ ≤ (g ≫ (π ⁻¹ᵁ U).ι) ⁻¹ᵁ (π ⁻¹ᵁ U) := by
      intro g; simp
    have := hf Z (g₁ ≫ (π ⁻¹ᵁ U).ι) (g₂ ≫ (π ⁻¹ᵁ U).ι) (k _) (k _) (by
      rw [Category.assoc, Category.assoc, ← morphismRestrict_ι, reassoc_of% e])
    rw [← GlobalTheory.FunDescent.res_comp_appTop _ g₁ _ rfl, ← GlobalTheory.FunDescent.res_comp_appTop _ g₂ _ rfl] at this
    exact this)
  obtain ⟨a, rfl⟩ := (GlobalTheory.FunDescent.res_bijective U).2 b
  refine ⟨a, (GlobalTheory.FunDescent.res_bijective _).1 ?_⟩
  rw [← GlobalTheory.FunDescent.res_square_apply, hb]

theorem units_descend :
    ∀ {P Q : Scheme.{0}} (f : P ⟶ Q), Flat f → LocallyOfFinitePresentation f → Surjective f → ∀ V : Q.Opens,
    Function.Injective (pullU f V) ∧ ∀ a : Γ(P, f ⁻¹ᵁ V)ˣ,
      (∀ (W : Scheme.{0}) (b c : W ⟶ P), b ≫ f = c ≫ f → ∀ w : W, f (b w) ∈ V →
        gm b w (f ⁻¹ᵁ V) a = gm c w (f ⁻¹ᵁ V) a) → ∃ s : Γ(Q, V)ˣ, pullU f V s = a := by
  intro P Q f _ _ _ V
  refine ⟨fun a b h => Units.ext (GlobalTheory.FunDescent.app_injective f V (congrArg Units.val h)), fun a ha => ?_⟩
  obtain ⟨t, ht⟩ := exists_app_eq_of_lfp f V a.val (fun Z g₁ g₂ h₁ h₂ e => by
    have k : ∀ (g : Z ⟶ P) (h : ⊤ ≤ g ⁻¹ᵁ (f ⁻¹ᵁ V)) (z : Z),
        gm (𝟙 Z) z ⊤ (res h (pullU g _ a)) = gm g z (f ⁻¹ᵁ V) a := fun g h z =>
      (gm_res (𝟙 Z) z h trivial _).trans ((gm_pull (𝟙 Z) g z _ (h trivial) _).trans (by
        rw [Category.id_comp]))
    have : res h₁ (pullU g₁ _ a) = res h₂ (pullU g₂ _ a) := unit_ext fun z _ =>
      (k g₁ h₁ z).trans ((ha Z g₁ g₂ e z (h₁ trivial)).trans (k g₂ h₂ z).symm)
    exact congrArg Units.val this)
  obtain ⟨s, rfl⟩ := GlobalTheory.FunDescent.isUnit_of_isUnit_app f V t (ht ▸ a.isUnit)
  exact ⟨s, Units.ext ht⟩

end GlobalTheory.CompanionTheory.FnDesc
end
