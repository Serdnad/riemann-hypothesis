module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem exists_geomPt_range_eq (X : Scheme.{0}) (g : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (z : Sp k ⟶ X), Set.range z = {g} := by
  let κ := X.residueField g
  let k := AlgebraicClosure κ
  refine ⟨k, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ X.fromSpecResidueField g, ?_⟩
  have hsub : Set.range (Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ X.fromSpecResidueField g) ⊆ {g} := by
    rw [← X.range_fromSpecResidueField g]
    rintro _ ⟨p, rfl⟩
    exact ⟨_, rfl⟩
  have hne : (Set.range (Spec.map (CommRingCat.ofHom (algebraMap κ k)) ≫ X.fromSpecResidueField g)).Nonempty :=
    Set.range_nonempty _
  exact (Set.Nonempty.subset_singleton_iff hne).mp hsub

private lemma exists_factor_of_range_subset_closedImmersion {T N B : Scheme.{0}} [IsReduced T] (x : T ⟶ B) (ν : N ⟶ B)
    [IsClosedImmersion ν] (h : Set.range x ⊆ Set.range ν) : ∃ l : T ⟶ N, l ≫ ν = x := by
  have : Surjective (pullback.snd ν x) := ⟨fun t => by
    have ht : t ∈ Set.range (pullback.snd ν x) := by
      rw [Scheme.Pullback.range_snd]
      exact h ⟨t, rfl⟩
    exact ht⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd ν x)
  exact ⟨inv (pullback.snd ν x) ≫ pullback.fst ν x, by
    rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]⟩

theorem etSet_of_kerSet :
    ∀ (S : Scheme.{0}) (G G' : Over S) [GrpObj G] [GrpObj G'] (ψ : G ⟶ G') (K : Set G.left), IsSeparated G'.hom → IsFinite ψ.left → Etale ψ.left → KerSet ψ K → EtSet G K ∧ (IsReduced S → ∀ (C : Over S) (j : C ⟶ G), Etale C.hom → IsClosedImmersion j.left → Set.range j.left = K → IsPullback j (toUnit C) ψ η[G']) := by
  intro S G G' _ _ ψ K hsep hfin het hK
  have hew : (η[G'] : 𝟙_ (Over S) ⟶ G').left ≫ G'.hom = 𝟙 S := Over.w _
  have : IsClosedImmersion ((η[G'] : 𝟙_ (Over S) ⟶ G').left ≫ G'.hom) := by
    rw [hew]
    have : IsIso (𝟙 S) := inferInstance
    infer_instance
  have he : IsClosedImmersion (η[G'] : 𝟙_ (Over S) ⟶ G').left := IsClosedImmersion.of_comp _ G'.hom
  have htu : ∀ Y : Over S, (toUnit Y).left = Y.hom := fun Y =>
    (Category.comp_id _).symm.trans (Over.w (toUnit Y))
  have hfac : ∀ {T : Scheme.{0}} [IsReduced T] (w : T ⟶ G.left),
      Set.range (w ≫ ψ.left) ⊆ Set.range (η[G'] : 𝟙_ (Over S) ⟶ G').left →
      w ≫ ψ.left = (w ≫ G.hom) ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    intro T _ w hw
    obtain ⟨l, hl⟩ := exists_factor_of_range_subset_closedImmersion (w ≫ ψ.left) _ hw
    have hl' : l = w ≫ G.hom := by
      have := congrArg (· ≫ G'.hom) hl
      simp only [Category.assoc, hew, Over.w] at this
      exact this
    rw [← hl, hl']
  have hKeq : K = ψ.left ⁻¹' Set.range (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    ext q
    obtain ⟨k, _, _, w, hw⟩ := exists_geomPt_range_eq G.left q
    have key := hK k (w ≫ G.hom) (Over.homMk w rfl)
    have hr : Set.range (Over.homMk (U := Over.mk (w ≫ G.hom)) w rfl).left = {q} := hw
    rw [hr, Set.singleton_subset_iff] at key
    rw [← key, Set.mem_preimage]
    obtain ⟨p, rfl⟩ : q ∈ Set.range w := hw ▸ rfl
    constructor
    · intro h
      have h2 : w ≫ ψ.left = (toUnit (Over.mk (w ≫ G.hom))).left ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left :=
        congrArg (fun f => f.left) h
      refine ⟨(toUnit (Over.mk (w ≫ G.hom))).left p, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← h2, Scheme.Hom.comp_apply]
    · intro h
      have hw2 := hfac w (by
        rintro _ ⟨p', rfl⟩
        have h3 : w p' ∈ ({w p} : Set G.left) := hw ▸ Set.mem_range_self p'
        rw [Set.mem_singleton_iff] at h3
        rw [Scheme.Hom.comp_apply, h3]
        exact h)
      ext1
      change w ≫ ψ.left = (toUnit (Over.mk (w ≫ G.hom))).left ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left
      rw [htu]
      exact hw2
  have hsqS : ∀ (C : Over S) (j : C ⟶ G), IsReduced C.left → Set.range j.left = K →
      j.left ≫ ψ.left = C.hom ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    intro C j _ hjr
    have := hfac j.left (by
      rintro _ ⟨p, rfl⟩
      have hp : j.left p ∈ K := hjr ▸ Set.mem_range_self p
      rw [hKeq] at hp
      rw [Scheme.Hom.comp_apply]
      exact hp)
    rw [this, Over.w j]
  have hPfst : Set.range (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) = K := by
    rw [Scheme.Pullback.range_fst, hKeq]
  have hfin' : IsFinite (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) :=
    inferInstance
  have het' : Etale (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) :=
    inferInstance
  have hci : IsClosedImmersion (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) :=
    inferInstance
  refine ⟨⟨Over.mk (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left : _ ⟶ S),
    Over.homMk (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) (by
      change _ = pullback.snd _ _
      rw [← Over.w ψ, ← Category.assoc, pullback.condition, Category.assoc, hew]
      exact Category.comp_id _),
    hfin', het', hci, hPfst⟩, ?_⟩
  intro hred C j hCet hj hjr
  have hCred : IsReduced C.left := GlobalTheory.isReduced_of_smooth_of_isReduced C.hom
  have hsq := hsqS C j hCred hjr
  have hred' : IsReduced (𝟙_ (Over S)).left := hred
  have hPred : IsReduced (pullback ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) :=
    GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.snd ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left)
  let φ : C.left ⟶ pullback ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left := pullback.lift j.left C.hom hsq
  have hφ1 : φ ≫ pullback.fst _ _ = j.left := pullback.lift_fst _ _ _
  have hφci : IsClosedImmersion φ := by
    have : IsClosedImmersion (φ ≫ pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left) := by
      rw [hφ1]; exact hj
    exact IsClosedImmersion.of_comp φ (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left)
  have hφs : Surjective φ := ⟨fun r => by
    have hr : pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left r ∈ Set.range j.left := by
      rw [hjr, ← hPfst]; exact Set.mem_range_self r
    obtain ⟨c, hc⟩ := hr
    refine ⟨c, (pullback.fst ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left).isClosedEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hφ1, hc]⟩
  have hφi : IsIso φ := isIso_of_isClosedImmersion_of_surjective φ
  have HS : IsPullback j.left (toUnit C).left ψ.left (η[G'] : 𝟙_ (Over S) ⟶ G').left := by
    rw [htu C]
    exact IsPullback.of_iso_pullback ⟨hsq⟩ (asIso φ) hφ1 (pullback.lift_snd _ _ _)
  have hw : j ≫ ψ = toUnit C ≫ η[G'] := by
    ext1
    change j.left ≫ ψ.left = (toUnit C).left ≫ (η[G'] : 𝟙_ (Over S) ⟶ G').left
    rw [htu C]; exact hsq
  exact IsPullback.of_map (Over.forget S) hw HS

end GlobalTheory.HkFam
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.GlueFn

end GlobalTheory.GlueFn

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct ContDiff in
private lemma exists_complex_section_through_closed_point (X : Scheme) (p : X ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType p] (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ q : Spec (CommRingCat.of ℂ) ⟶ X, q ≫ p = 𝟙 _ ∧ ∀ s, q.base s = x := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  have h1 : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    isClosed_singleton_iff_locallyOfFiniteType.mp hx
  have h2 : LocallyOfFiniteType (X.fromSpecResidueField x ≫ p) := inferInstance
  obtain ⟨φ, hφ⟩ : ∃ φ, Spec.map φ = X.fromSpecResidueField x ≫ p :=
    ⟨Spec.preimage _, Spec.map_preimage _⟩
  rw [← hφ] at h2
  have hft : φ.hom.FiniteType := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h2
  letI := φ.hom.toAlgebra
  haveI : Algebra.FiniteType ℂ (X.residueField x) := hft
  haveI : Module.Finite ℂ (X.residueField x) := finite_of_finite_type_of_isJacobsonRing ℂ _
  have hsurj : Function.Surjective (algebraMap ℂ (X.residueField x)) := by
    apply IsSepClosed.algebraMap_surjective
  let e := RingEquiv.ofBijective (algebraMap ℂ (X.residueField x))
    ⟨(algebraMap ℂ _).injective, hsurj⟩
  refine ⟨Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ X.fromSpecResidueField x, ?_, ?_⟩
  · rw [Category.assoc, ← hφ, ← Spec.map_comp]
    convert Spec.map_id (CommRingCat.of ℂ)
    ext a
    exact e.symm_apply_apply a
  · intro s
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct ContDiff in
private lemma valAt'_sub_of_top_le {X : Scheme} (q : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X) (U : X.Opens) (hU : ⊤ ≤ q ⁻¹ᵁ U)
    (a b : Γ(X, U)) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U (a - b) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U a - _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U b := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt'
  rw [dite_eq_left hU, dite_eq_left hU, dite_eq_left hU]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
  simp only [map_sub]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct ContDiff in
private lemma not_mem_basicOpen_of_valAt'_eq_zero {X : Scheme} (q : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X)
    (U : X.Opens) (hU : ⊤ ≤ q ⁻¹ᵁ U) (f : Γ(X, U)) (hf : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U f = 0)
    (s : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ) : q.base s ∉ X.basicOpen f := by
  intro hs
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' at hf
  rw [dite_eq_left hU] at hf
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt at hf
  have h0 : q.appLE U ⊤ hU f = 0 := by
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom hf
    simpa using this
  have hmem : s ∈ q ⁻¹ᵁ X.basicOpen f := hs
  rw [Scheme.Hom.preimage_basicOpen] at hmem
  have hres : (Spec (CommRingCat.of ℂ)).basicOpen (q.appLE U ⊤ hU f) =
      ⊤ ⊓ (Spec (CommRingCat.of ℂ)).basicOpen (q.app U f) := by
    rw [← Scheme.basicOpen_res]
    rfl
  rw [h0, Scheme.basicOpen_zero] at hres
  have : s ∈ (⊤ ⊓ (Spec (CommRingCat.of ℂ)).basicOpen (q.app U f) :
      (Spec (CommRingCat.of ℂ)).Opens) := ⟨trivial, hmem⟩
  rw [← hres] at this
  exact this

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct ContDiff in
private lemma valAt'_presheaf_map {X : Scheme} (q : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ X) {U V : X.Opens} (i : V ⟶ U)
    (hV : ⊤ ≤ q ⁻¹ᵁ V) (a : Γ(X, U)) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q V (X.presheaf.map i.op a) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' q U a := by
  have hU : ⊤ ≤ q ⁻¹ᵁ U := fun s hs => i.le (hV hs)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt'
  rw [dite_eq_left hU, dite_eq_left hV]
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
  rw [← Scheme.Hom.map_appLE q hV i.op]
  rfl


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct ContDiff in
theorem _root_.GlobalTheory.existsUnique_section_of_locally_regular :
    ∀ (P₀ : _root_.ReciprocityTheory.ChartRestriction.G.Out.PolAV (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) (u : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), _root_.GlobalTheory.KS.GoodU u Hm χ → ∀ (O : P₀.A.left.Opens) (h : (Fin P₀.g → ℂ) → ℂ), (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → ∃ (O' : P₀.A.left.Opens) (a : Γ(P₀.A.left, O')), O' ≤ O ∧ ⊤ ≤ (u.ex z).left ⁻¹ᵁ O' ∧ ∀ z', ⊤ ≤ (u.ex z').left ⁻¹ᵁ O' → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z').left O' a = h z') → ∃! a : Γ(P₀.A.left, O), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left O a = h z := by
  intro P₀ u Hm χ _ O h H
  haveI := P₀.smoothDim
  have hsm : Smooth P₀.A.hom := SmoothOfRelativeDimension.smooth P₀.g P₀.A.hom
  haveI := hsm
  haveI : IsReduced P₀.A.left := _root_.GlobalTheory.isReduced_of_smooth_complex _ _ hsm
  haveI : JacobsonSpace P₀.A.left := LocallyOfFiniteType.jacobsonSpace P₀.A.hom
  have hpt : ∀ y : P₀.A.left, IsClosed ({y} : Set P₀.A.left) →
      ∃ z, ∀ s, (u.ex z).left.base s = y := by
    intro y hy
    obtain ⟨q, hq, hqy⟩ := exists_complex_section_through_closed_point P₀.A.left P₀.A.hom y hy
    obtain ⟨z, hz⟩ := u.ex_onto (Over.homMk q hq : 𝟙_ (Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)) ⟶ P₀.A)
    exact ⟨z, fun s => by rw [hz]; exact hqy s⟩
  have hs₀ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ := IsLocalRing.closedPoint ℂ
  have huniq : ∀ (V : P₀.A.left.Opens) (a b : Γ(P₀.A.left, V)), (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ V →
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left V a = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left V b) → a = b := by
    intro V a b hab
    rw [← sub_eq_zero, ← basicOpen_eq_bot_iff]
    by_contra hne
    obtain ⟨y, hyB, hyc⟩ := nonempty_inter_closedPoints
      ((TopologicalSpace.Opens.ne_bot_iff_nonempty _).mp hne)
      (P₀.A.left.basicOpen (a - b)).isOpen.isLocallyClosed
    obtain ⟨z, hz⟩ := hpt y (mem_closedPoints_iff.mp hyc)
    have hzV : ⊤ ≤ (u.ex z).left ⁻¹ᵁ V := fun s _ => by
      show (u.ex z).left.base s ∈ V
      rw [hz]
      exact P₀.A.left.basicOpen_le _ hyB
    have h0 : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left V (a - b) = 0 := by
      rw [valAt'_sub_of_top_le _ _ hzV, hab z hzV, sub_self]
    exact not_mem_basicOpen_of_valAt'_eq_zero _ _ hzV _ h0 hs₀ (by rw [hz]; exact hyB)
  have hloc : ∀ w : {z // ⊤ ≤ (u.ex z).left ⁻¹ᵁ O}, ∃ (O' : P₀.A.left.Opens)
      (a : Γ(P₀.A.left, O')), O' ≤ O ∧ ⊤ ≤ (u.ex w.1).left ⁻¹ᵁ O' ∧ ∀ z', ⊤ ≤ (u.ex z').left ⁻¹ᵁ O' →
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z').left O' a = h z' := fun w => H w.1 w.2
  choose W aW hWO hWz hWv using hloc
  have hcover : O ≤ iSup W := by
    by_contra hle
    have hZ : ((O : Set P₀.A.left) ∩ ((iSup W : P₀.A.left.Opens) : Set P₀.A.left)ᶜ).Nonempty := by
      rw [← Set.diff_eq, Set.diff_nonempty]
      exact hle
    have hZlc : IsLocallyClosed ((O : Set P₀.A.left) ∩ ((iSup W : P₀.A.left.Opens) : Set P₀.A.left)ᶜ) :=
      ⟨O, ((iSup W : P₀.A.left.Opens) : Set P₀.A.left)ᶜ, O.isOpen, (iSup W).isOpen.isClosed_compl, rfl⟩
    obtain ⟨y, ⟨hyO, hyW⟩, hyc⟩ := nonempty_inter_closedPoints hZ hZlc
    obtain ⟨z, hz⟩ := hpt y (mem_closedPoints_iff.mp hyc)
    have hzO : ⊤ ≤ (u.ex z).left ⁻¹ᵁ O := fun s _ => by
      show (u.ex z).left.base s ∈ O
      rw [hz]
      exact hyO
    have hyz : y ∈ W ⟨z, hzO⟩ := by
      rw [← hz hs₀]
      exact hWz ⟨z, hzO⟩ (show hs₀ ∈ (⊤ : (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ).Opens) from trivial)
    exact hyW (TopologicalSpace.Opens.mem_iSup.mpr ⟨_, hyz⟩)
  have hcompat : TopCat.Presheaf.IsCompatible P₀.A.left.sheaf.obj W aW := by
    intro i j
    apply huniq
    intro z hz
    have hi : ⊤ ≤ (u.ex z).left ⁻¹ᵁ W i := fun s hs => (inf_le_left : W i ⊓ W j ≤ W i) (hz hs)
    have hj : ⊤ ≤ (u.ex z).left ⁻¹ᵁ W j := fun s hs => (inf_le_right : W i ⊓ W j ≤ W j) (hz hs)
    erw [valAt'_presheaf_map _ _ hz, valAt'_presheaf_map _ _ hz]
    rw [hWv i z hi, hWv j z hj]
  obtain ⟨a, ha, -⟩ := P₀.A.left.sheaf.existsUnique_gluing' W O (fun i => homOfLE (hWO i))
    hcover aW hcompat
  have hval : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' (u.ex z).left O a = h z := by
    intro z hz
    rw [← valAt'_presheaf_map (u.ex z).left (homOfLE (hWO ⟨z, hz⟩)) (hWz ⟨z, hz⟩) a]
    erw [ha ⟨z, hz⟩]
    exact hWv ⟨z, hz⟩ z (hWz ⟨z, hz⟩)
  refine ⟨a, hval, fun b hb => huniq O b a fun z hz => ?_⟩
  rw [hb z hz, hval z hz]

end GlobalTheory
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.ConstEndo

theorem unit_comp {S S₀ : Scheme.{0}} {f : S ⟶ S₀} {X : Over S} {X₀ : Over S₀} [GrpObj X] [GrpObj X₀]
    {φ : X.left ⟶ X₀.left} (h : IsGrpPullback X X₀ f φ) :
    (η[X]).left ≫ φ = f ≫ (η[X₀]).left := by
  obtain ⟨hpb, hmul⟩ := h

  have hw : ((η[X]).left ≫ φ) ≫ X₀.hom = (𝟙_ (Over S)).hom ≫ f := by
    rw [Category.assoc, hpb.w, ← Category.assoc, Over.w]
  let x₀ : Over.mk ((𝟙_ (Over S)).hom ≫ f) ⟶ X₀ := Over.homMk ((η[X]).left ≫ φ) hw

  have hηη : (η[X] : 𝟙_ (Over S) ⟶ X) * η[X] = η[X] := by
    rw [MonObj.one_eq_one, _root_.one_mul]
  have hx : x₀ * x₀ = x₀ := by
    ext1
    rw [hmul (𝟙_ (Over S)) η[X] η[X] x₀ x₀ rfl rfl, hηη]
    rfl
  have h1 : x₀ = 1 := by
    simpa using hx
  have h2 := congrArg CommaMorphism.left h1
  simp only [x₀, Over.homMk_left, Hom.one_def, Over.comp_left, Over.toUnit_left, Over.mk_hom,
    Over.tensorUnit_hom] at h2
  exact h2

private theorem surjective_of_isPullback_dualNumber_fst {A₀ : Over (Sp ℂ)} {A' : Over (Sp (DualNumber ℂ))} (j : A₀.left ⟶ A'.left)
    (h : IsPullback j A₀.hom A'.hom (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) :
    Function.Surjective j := by

  have hc : Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
    intro p
    have hp : p ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := by
      rw [range_comap_of_surjective _ _ (fun x => ⟨TrivSqZeroExt.inl x, rfl⟩)]
      intro x hx
      have hx0 : x.fst = 0 := hx
      apply p.isPrime.mem_of_pow_mem 2
      have hx' : x = TrivSqZeroExt.inr x.snd := TrivSqZeroExt.ext hx0 rfl
      rw [hx', pow_two, TrivSqZeroExt.inr_mul_inr]
      exact p.asIdeal.zero_mem
    exact hp
  have hs : Surjective (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) := ⟨hc⟩
  exact (MorphismProperty.of_isPullback h.flip hs).surj

private theorem exists_unit_mul_eq_mul_uniformizer_pow {X S Y : Scheme.{0}} [IsAffine Y] (π : X ⟶ S)
    (hπ : Function.Bijective (π.appTop).hom) (g : X ⟶ Y) : ∃ c : S ⟶ Y, g = π ≫ c := by

  have : IsIso π.appTop := (ConcreteCategory.isIso_iff_bijective _).mpr hπ
  refine ⟨S.toSpecΓ ≫ Spec.map (inv π.appTop) ≫ Spec.map g.appTop ≫ inv Y.toSpecΓ, ?_⟩
  rw [← cancel_mono Y.toSpecΓ]
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [Scheme.toSpecΓ_naturality, Scheme.toSpecΓ_naturality_assoc, ← Spec.map_comp_assoc,
    IsIso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem endo_comp_proj : Out.Laws → Out.Laws2 → ∀ (P₀ : Out.PolAV (Sp ℂ)), ∀ (A' : Over (Sp (DualNumber ℂ))) [GrpObj A'] (ρ : A'.left ⟶ P₀.A.left) (j : P₀.A.left ⟶ A'.left), IsConst A' P₀.A ρ j → ∀ (f' : A' ⟶ A') (f₀ : P₀.A ⟶ P₀.A), IsAbelianScheme A' → IsMonHom f' → IsMonHom f₀ → j ≫ f'.left = f₀.left ≫ j → f'.left ≫ ρ = ρ ≫ f₀.left := by
  intro hL _ P₀ A' _ ρ j hc f' f₀ hab hf' hf₀ hj
  obtain ⟨hρ, hjp, hjρ⟩ := hc
  set ic : Sp (DualNumber ℂ) ⟶ Sp ℂ := spMap (algebraMap ℂ (DualNumber ℂ)) with hic
  have hwρ : ρ ≫ P₀.A.hom = A'.hom ≫ ic := hρ.1.w

  let T : Over (Sp ℂ) := Over.mk (A'.hom ≫ ic)
  let D : T ⟶ P₀.A := Over.homMk (f'.left ≫ ρ) (by
    simp only [T, Over.mk_hom, Category.assoc, hwρ]
    rw [← Category.assoc, Over.w])
  let E : T ⟶ P₀.A := Over.homMk (ρ ≫ f₀.left) (by
    simp only [T, Over.mk_hom, Category.assoc, Over.w, hwρ])
  suffices hDE : D = E from congrArg CommaMorphism.left hDE
  rw [← _root_.mul_inv_eq_one]
  set δ := D * E⁻¹ with hδ

  have hjT : j ≫ T.hom = P₀.A.hom := by
    simp only [T, Over.mk_hom]
    rw [← hwρ, ← Category.assoc, hjρ, Category.id_comp]
  let jT : P₀.A ⟶ T := Over.homMk j hjT
  have h1 : jT ≫ δ = 1 := by
    have hh : jT ≫ D = jT ≫ E := by
      ext1
      simp only [jT, D, E, Over.comp_left, Over.homMk_left]
      rw [← Category.assoc, hj, Category.assoc, hjρ, Category.comp_id, ← Category.assoc, hjρ,
        Category.id_comp]
    rw [hδ, MonObj.comp_mul, GrpObj.comp_inv, hh, _root_.mul_inv_cancel]

  have hη : (η[A']).left ≫ ρ = ic ≫ (η[P₀.A]).left := unit_comp hρ
  have hηA : (η[A']).left ≫ A'.hom = 𝟙 _ := by
    rw [Over.w]; rfl
  let eT : Over.mk ic ⟶ T := Over.homMk (η[A']).left (by
    simp only [T, Over.mk_hom]
    rw [← Category.assoc, hηA]
    exact Category.id_comp _)
  have h2 : (eT ≫ δ).left = ic ≫ (η[P₀.A]).left := by
    have hh : eT ≫ D = eT ≫ E := by
      ext1
      simp only [eT, D, E, Over.comp_left, Over.homMk_left]
      have e1 : (η[A']).left ≫ f'.left = (η[A']).left := by
        rw [← Over.comp_left, IsMonHom.one_hom]
      have e2 : (η[P₀.A]).left ≫ f₀.left = (η[P₀.A]).left := by
        rw [← Over.comp_left, IsMonHom.one_hom]
      rw [← Category.assoc, e1, hη, ← Category.assoc, hη, Category.assoc, e2]
    rw [hδ, MonObj.comp_mul, GrpObj.comp_inv, hh, _root_.mul_inv_cancel]
    simp [Hom.one_def]

  have hsurj := surjective_of_isPullback_dualNumber_fst j hjp.1
  obtain ⟨p₀⟩ : Nonempty (Sp ℂ) := inferInstance
  obtain ⟨_, ⟨V₀, hV, rfl⟩, hxV, -⟩ :=
    P₀.A.left.isBasis_affineOpens.exists_subset_of_mem_open
      (show (η[P₀.A]).left p₀ ∈ (⊤ : P₀.A.left.Opens) from trivial) (⊤ : P₀.A.left.Opens).2
  let V : P₀.A.left.Opens := V₀
  have hrange : Set.range δ.left ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := hsurj x
    have e1 : (jT ≫ δ).left = (1 : P₀.A ⟶ P₀.A).left := by rw [h1]
    have e2 : δ.left (j y) = (η[P₀.A]).left (P₀.A.hom y) := by
      have := congrArg (fun m => m y) e1
      simpa [jT, Hom.one_def] using this
    rw [e2, Subsingleton.elim (P₀.A.hom y) p₀]
    exact hxV
  have : IsAffine V := hV
  have hG : Function.Bijective (A'.hom.appTop).hom := by
    have hgl := hL.globalFns
    unfold Out.GlobalFnsSt at hgl
    exact hgl _ A' hab
  obtain ⟨c, hc⟩ := exists_unit_mul_eq_mul_uniformizer_pow A'.hom hG (IsOpenImmersion.lift V.ι δ.left hrange)
  have hδc : δ.left = A'.hom ≫ c ≫ V.ι := by
    rw [← Category.assoc, ← hc, IsOpenImmersion.lift_fac]

  have h3 : c ≫ V.ι = ic ≫ (η[P₀.A]).left := by
    rw [← h2]
    simp only [eT, Over.comp_left, Over.homMk_left, hδc]
    rw [← Category.assoc, hηA]
    exact (Category.id_comp (c ≫ V.ι)).symm
  ext1
  rw [hδc, h3]
  simp [T, Hom.one_def]

end GlobalTheory.ConstEndo
end
