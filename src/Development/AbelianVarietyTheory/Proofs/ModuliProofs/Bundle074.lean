module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle780
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle004
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle064
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle069
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.DenseOfDenseP
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle063
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle068
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Etale
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle002
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

noncomputable section

namespace GlobalTheory.ConstThickening

theorem existsUnique_of_isPushout {K : Type} [Field K] {A A' : CommRingCat.{0}} (c : K →+* A) (p : A ⟶ A')
    (s : DualNumber K →+* A')
    (H : IsPushout (CommRingCat.ofHom c) (CommRingCat.ofHom (algebraMap K (DualNumber K))) p (CommRingCat.ofHom s))
    (F : A') : ∃! ab : A × A, F = p.hom ab.1 + s DualNumber.eps * p.hom ab.2 := by
  apply GlobalTheory.RelConstThickening.existsUnique_of_isPushout <;> assumption

variable {K : Type} [Field K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K} {π : Y' ⟶ Sp (DualNumber K)} {ρ : Y' ⟶ Y}

def constHom {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) (U : X.Opens) : R →+* Γ(X, U) :=
  (f.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem res_constFn {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) {U V : X.Opens} (h : V ≤ U) (a : R) :
    (X.presheaf.map (homOfLE h).op).hom (constFn f U a) = constFn f V a := by
  exact congrArg (fun g => g.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
    (f.appLE_map (U := ⊤) (fun _ _ => trivial) (homOfLE h).op)

theorem res_app {X X' : Scheme.{0}} (f : X' ⟶ X) {U V : X.Opens} (h : V ≤ U) (h' : f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    (X'.presheaf.map (homOfLE h').op).hom ((f.app U).hom a) = (f.app V).hom ((X.presheaf.map (homOfLE h).op).hom a) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)) :
    (X.presheaf.map (homOfLE h').op).hom ((X.presheaf.map (homOfLE h).op).hom a) =
      (X.presheaf.map (homOfLE (h'.trans h)).op).hom a := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem existsUnique_affine (H : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) {U : Y.Opens}
    (hU : IsAffineOpen U) (F : Γ(Y', ρ ⁻¹ᵁ U)) : ∃! ab : Γ(Y, U) × Γ(Y, U),
      F = (ρ.app U).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app U).hom ab.2 := by
  refine existsUnique_of_isPushout (constHom q U) (ρ.app U) (constHom π (ρ ⁻¹ᵁ U)) ?_ F
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := ρ ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  refine po.of_iso (Scheme.ΓSpecIso (.of K)) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber K))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · ext x; simp [constHom]
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [constHom]

theorem res_comb {U V : Y.Opens} (h : V ≤ U) (h' : ρ ⁻¹ᵁ V ≤ ρ ⁻¹ᵁ U) (a b : Γ(Y, U)) :
    (Y'.presheaf.map (homOfLE h').op).hom ((ρ.app U).hom a + constFn π _ DualNumber.eps * (ρ.app U).hom b) =
      (ρ.app V).hom ((Y.presheaf.map (homOfLE h).op).hom a) +
        constFn π _ DualNumber.eps * (ρ.app V).hom ((Y.presheaf.map (homOfLE h).op).hom b) := by
  rw [map_add (f := _), map_mul, res_app ρ h, res_app ρ h, res_constFn]

theorem le_iSup_affine (O : Y.Opens) : O ≤ ⨆ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, U.1 := fun x hx => by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUO⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx O.isOpen
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hUO⟩, hxU⟩

theorem unique_comb (H : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) {O : Y.Opens} {a b a' b' : Γ(Y, O)}
    (h : (ρ.app O).hom a + constFn π _ DualNumber.eps * (ρ.app O).hom b =
      (ρ.app O).hom a' + constFn π _ DualNumber.eps * (ρ.app O).hom b') : a = a' ∧ b = b' := by
  have loc : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      ((Y.presheaf.map (homOfLE U.2.2).op).hom a, (Y.presheaf.map (homOfLE U.2.2).op).hom b) =
      ((Y.presheaf.map (homOfLE U.2.2).op).hom a', (Y.presheaf.map (homOfLE U.2.2).op).hom b') := fun U => by
    have h' : ρ ⁻¹ᵁ U.1 ≤ ρ ⁻¹ᵁ O := fun x hx => U.2.2 hx
    have e := congrArg (Y'.presheaf.map (homOfLE h').op).hom h
    rw [res_comb U.2.2, res_comb U.2.2] at e
    exact (existsUnique_affine H U.2.1 _).unique rfl e
  exact ⟨Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) a a'
      fun U => congrArg Prod.fst (loc U),
    Y.sheaf.eq_of_locally_eq' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O) b b'
      fun U => congrArg Prod.snd (loc U)⟩

theorem existsUnique_comb (H : IsPullback ρ π q (spMap (algebraMap K (DualNumber K)))) (O : Y.Opens)
    (F : Γ(Y', ρ ⁻¹ᵁ O)) : ∃! ab : Γ(Y, O) × Γ(Y, O),
      F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  have hle : ∀ U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O}, ρ ⁻¹ᵁ U.1 ≤ ρ ⁻¹ᵁ O := fun U x hx => U.2.2 hx
  choose ab hab using fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} =>
    (existsUnique_affine H U.2.1 ((Y'.presheaf.map (homOfLE (hle U)).op).hom F)).exists
  have comp : ∀ U V : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O},
      (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (ab U).1 =
        (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (ab V).1 ∧
      (Y.presheaf.map (homOfLE (inf_le_left : U.1 ⊓ V.1 ≤ U.1)).op).hom (ab U).2 =
        (Y.presheaf.map (homOfLE (inf_le_right : U.1 ⊓ V.1 ≤ V.1)).op).hom (ab V).2 := fun U V => by
    apply unique_comb H
    rw [← res_comb inf_le_left (fun x hx => hx.1), ← res_comb inf_le_right (fun x hx => hx.2), ← hab, ← hab]
    exact (res_res _ _ F).trans (res_res _ _ F).symm
  obtain ⟨a, ha, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (ab U).1) (fun U V => (comp U V).1)
  obtain ⟨b, hb, -⟩ := Y.sheaf.existsUnique_gluing' _ O (fun U => homOfLE U.2.2) (le_iSup_affine O)
    (fun U => (ab U).2) (fun U V => (comp U V).2)
  have hF : F = (ρ.app O).hom a + constFn π _ DualNumber.eps * (ρ.app O).hom b := by
    refine Y'.sheaf.eq_of_locally_eq' (fun U : {U : Y.Opens // IsAffineOpen U ∧ U ≤ O} => ρ ⁻¹ᵁ U.1) _
      (fun U => homOfLE (hle U)) (fun x hx => ?_) _ _ fun U => ?_
    · obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 (le_iSup_affine O hx)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩
    · refine (hab U).trans (Eq.trans ?_ (res_comb U.2.2 (hle U) a b).symm)
      rw [← ha U, ← hb U]
      rfl
  refine ⟨(a, b), hF, fun c hc => ?_⟩
  have := unique_comb H (hc.symm.trans hF)
  exact Prod.ext this.1 this.2

theorem surjective_spMap_fst : Surjective (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
  have hs : Function.Surjective (TrivSqZeroExt.fstHom K K K).toRingHom := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  refine ⟨fun P => ?_⟩
  have : P ∈ Set.range (PrimeSpectrum.comap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    rw [range_comap_of_surjective _ _ hs]
    intro x hx
    refine (P : PrimeSpectrum (DualNumber K)).2.mem_of_pow_mem 2 ?_
    have hx' : x.fst = 0 := hx
    have : x ^ 2 = 0 := by ext <;> simp [sq, hx']
    rw [this]; exact zero_mem _
  exact this

theorem structure_dualNumber : ∀ (K : Type) [Field K] (Y Y' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap K (DualNumber K))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → (∀ O : Y'.Opens, ρ ⁻¹ᵁ (j ⁻¹ᵁ O) = O) ∧ IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ∧ ∀ (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)), ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  intro K _ Y Y' q π ρ j H hj hq
  have e : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  have hp : IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    refine IsPullback.of_right ?_ hq H
    rw [hj, e]
    exact IsPullback.id_horiz q
  refine ⟨fun O => ?_, hp, existsUnique_comb H⟩
  have hs : Surjective j := MorphismProperty.of_isPullback (P := @Surjective) hp.flip surjective_spMap_fst
  ext x
  obtain ⟨y, rfl⟩ := hs.surj x
  change j (ρ (j y)) ∈ O ↔ j y ∈ O
  rw [← Scheme.Hom.comp_apply j ρ, hj]
  rfl

end GlobalTheory.ConstThickening
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.ProperFlatNearFibre

theorem exists_opens_smoothOfRelativeDimension_of_flat {R : CommRingCat.{0}} {Z T : Scheme.{0}}
    (s : Z ⟶ Spec R) [LocallyOfFinitePresentation s] [Flat s] (t : T ⟶ Spec R) (g : ℕ)
    (h : SmoothOfRelativeDimension g (pullback.snd s t)) (z : Z) (w : T) (hw : s z = t w) :
    ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s) := by
  apply GlobalTheory.SmoothNearFibre.exists_opens_of_flat <;> assumption

theorem smoothOfRelativeDimension_pullback_snd {Z T S : Scheme.{0}} (s : Z ⟶ S) (t : T ⟶ S)
    (g : ℕ) (h : ∀ (z : Z) (w : T), s z = t w →
      ∃ W : Z.Opens, z ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ s)) :
    SmoothOfRelativeDimension g (pullback.snd s t) := by
  let V : {W : Z.Opens // SmoothOfRelativeDimension g (W.ι ≫ s)} → (pullback s t).Opens :=
    fun W => pullback.fst s t ⁻¹ᵁ W.1
  have htop : iSup V = ⊤ := by
    rw [← top_le_iff]
    intro y _
    obtain ⟨W, hW, hW'⟩ := h (pullback.fst s t y) (pullback.snd s t y) (by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition])
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} g) V htop
    fun W => ?_
  exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension.{0} g)
    ((isPullback_morphismRestrict (pullback.fst s t) W.1).paste_vert
      (IsPullback.of_hasPullback s t)) W.2

theorem exists_away_smoothOfRelativeDimension :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (g : ℕ) (K : Type) [Field K] (x : R →+* K), IsProper s → Flat s → SmoothOfRelativeDimension g (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ SmoothOfRelativeDimension g (pullback.snd s (spMap (algebraMap R (Localization.Away f)))) := by
  intro R _ _ Z s g K _ x hs hf h
  have : LocallyOfFinitePresentation s := inferInstance
  let U : Z.Opens := ⨆ W : {W : Z.Opens // SmoothOfRelativeDimension g (W.ι ≫ s)}, W.1
  have hc : IsClosed (s '' (U : Set Z)ᶜ) := s.isClosedMap _ U.2.isClosed_compl
  let w : Sp K := (default : PrimeSpectrum K)
  have hp : spMap x w ∈ (s '' (U : Set Z)ᶜ)ᶜ := by
    rintro ⟨z, hz, e⟩
    obtain ⟨W, hW, hW'⟩ := exists_opens_smoothOfRelativeDimension_of_flat s (spMap x) g h z w e
    exact hz (TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW'⟩, hW⟩)
  obtain ⟨_, ⟨f, rfl⟩, hf1, hf2⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hp
      hc.isOpen_compl
  refine ⟨f, ?_, smoothOfRelativeDimension_pullback_snd _ _ g fun z y e => ?_⟩
  · have h1 : f ∉ (spMap x w).asIdeal := hf1
    rwa [GlobalTheory.VeryDenseFibres.spMap_apply_asIdeal, RingHom.mem_ker] at h1
  · have h1 : s z ∈ (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) := by
      rw [← PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]
      exact ⟨y, e.symm⟩
    have h2 : z ∈ U := by
      by_contra hz
      exact hf2 h1 ⟨z, hz, rfl⟩
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.1 h2
    exact ⟨W.1, hW, W.2⟩

end GlobalTheory.ProperFlatNearFibre
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
open Classical

namespace GlobalTheory

theorem isOpen_setOf_TT_eq_bot : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (M : GlobalTheory.ZH.RatModel o Ω) (I : Type) (d : I → Ω) (e : ℕ), M.HasDiv S.th → (∀ z : M.Z, ∀ x₀ ∈ S.supI M z, (S.TT M z = ⊥ ↔ ∃ k, d k ≠ 0 ∧ S.th x₀ ^ e / d k ∈ M.O z)) → IsOpen {z : M.Z | S.TT M z = ⊥} := by
  intro o Ω _ _ _ S M I d e hdiv h
  haveI : NeZero (S.r * S.N) :=
    ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega)⟩
  refine isOpen_iff_forall_mem_open.2 fun z hz => ?_
  obtain ⟨x₀, hx₀⟩ := hdiv z
  obtain ⟨k, hk, hreg⟩ := (h z x₀ hx₀).1 hz
  refine ⟨{w | M.Div S.th x₀ w} ∩ {w | S.th x₀ ^ e / d k ∈ M.O w}, ?_,
    (M.isOpen_setOf_div S.th x₀).inter (M.isOpen_setOf_mem_O _), hx₀, hreg⟩
  rintro w ⟨hw1, hw2⟩
  exact (h w x₀ hw1).2 ⟨k, hk, hw2⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem exists_det_ne_zero_of_common_ker {K J : Type} [Field K] {g : ℕ} (φ : J → (Fin g → K) →ₗ[K] K)
    (h : ∀ w, (∀ i, φ i w = 0) → w = 0) :
    ∃ c : Fin g → J, (Matrix.of fun a b => φ (c b) (Pi.single a 1)).det ≠ 0 := by
  classical
  let ψ : J → Module.Dual K (Fin g → K) := φ
  have hspan : Submodule.span K (Set.range ψ) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hco : (Submodule.span K (Set.range ψ)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro w hw
      rw [Submodule.mem_dualCoannihilator] at hw
      exact (Submodule.mem_bot K).2 (h w fun i => hw _ (Submodule.subset_span ⟨i, rfl⟩))
    have hdim := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span K (Set.range ψ))
    rw [hco, finrank_bot, add_zero] at hdim
    rw [hdim, Subspace.dual_finrank_eq]
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent K (Set.range ψ)
  let B : Module.Basis b K (Module.Dual K (Fin g → K)) :=
    Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan, hspan]))
  let D : Module.Basis (Fin g) K (Module.Dual K (Fin g → K)) := (Pi.basisFun K (Fin g)).dualBasis
  let e : b ≃ Fin g := B.indexEquiv D
  have hex : ∀ k : Fin g, ∃ j, ψ j = ((e.symm k : b) : Module.Dual K (Fin g → K)) := fun k => hbsub (e.symm k).2
  choose c hc using hex
  refine ⟨c, ?_⟩
  have hM : (Matrix.of fun a k => φ (c k) (Pi.single a 1)) = D.toMatrix (B.reindex e) := by
    ext a k
    rw [Matrix.of_apply]
    change ψ (c k) (Pi.single a 1) = _
    rw [hc k]
    simp only [Module.Basis.toMatrix_apply, D, Module.Basis.dualBasis_repr,
      Module.Basis.reindex_apply, B, Module.Basis.mk_apply, Pi.basisFun_apply]
  rw [hM]
  intro h0
  have hone := congrArg Matrix.det (D.toMatrix_mul_toMatrix_flip (B.reindex e))
  rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at hone
  exact zero_ne_one hone

theorem top_le_preimage_finset_inf {X : Scheme.{0}} (x : Sp ℂ ⟶ X) {κ : Type} (s : Finset κ) (W : κ → X.Opens)
    (h : ∀ i ∈ s, ⊤ ≤ x ⁻¹ᵁ W i) : ⊤ ≤ x ⁻¹ᵁ (s.inf W) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
    intro _ p _
    simp
  | @insert a s ha ih =>
    intro h p hp
    rw [Finset.inf_insert]
    exact ⟨h a (Finset.mem_insert_self a s) hp, ih (fun i hi => h i (Finset.mem_insert_of_mem hi)) hp⟩

theorem fderiv_fn_resG {g : ℕ} {A₀ : Over (Sp ℂ)} [GrpObj A₀] {L₀ : LB A₀.left} (u : HolUnif A₀ L₀ g)
    {X : Scheme.{0}} (m : A₀.left ⟶ X) {W W' : X.Opens} (h : W' ≤ W) (f : Γ(X, W)) {z : Fin g → ℂ}
    (hz : z ∈ dom u m W') : fderiv ℂ (fn u m W' (resG X h f)) z = fderiv ℂ (fn u m W f) z := by
  have key : ∀ (y : Sp ℂ ⟶ X), ⊤ ≤ y ⁻¹ᵁ W' → valAt' y W' (resG X h f) = valAt' y W f := by
    intro y hy
    have hy2 : ⊤ ≤ y ⁻¹ᵁ W := hy.trans (fun q hq => h hq)
    unfold valAt'
    rw [dite_eq_left hy, dite_eq_left hy2]
    unfold valAt
    congr 1
    rw [← Scheme.Hom.map_appLE y hy (homOfLE h).op]
    rfl
  have hopen : IsOpen (dom u m W') := by
    exact (u.hol (m ⁻¹ᵁ W') 0).1
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [hopen.mem_nhds hz] with z' hz'
  exact key _ hz'

theorem exists_fibre_coords : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (R : Type) [CommRing R] (x₀ : R →+* ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : P₀.A.left ⟶ X), Smooth p → IsPullback m P₀.A.hom p (spMap x₀) → ∀ z, ∃ (W : X.Opens) (t : Fin P₀.g → Γ(X, W)), z ∈ dom u m W ∧ (Matrix.of fun a b => fderiv ℂ (fn u m W (t b)) z (Pi.single a 1)).det ≠ 0 := by
  intro P₀ u Hm χ hG R _ x₀ X p m hsm hpb z
  let J : Type := {Wf : (W : X.Opens) × Γ(X, W) // z ∈ dom u m Wf.1}
  let φ : J → (Fin P₀.g → ℂ) →ₗ[ℂ] ℂ := fun j => (fderiv ℂ (fn u m j.1.1 j.1.2) z).toLinearMap
  have hker : ∀ w, (∀ j, φ j w = 0) → w = 0 := by
    intro w hw
    have hδ : PtDer ((u.ex z).left ≫ m) (fun _ _ => (0 : ℂ)) :=
      ⟨fun _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ _ => rfl⟩
    obtain ⟨w₀, _, huniq⟩ := GlobalTheory.T.existsUnique_uniformising_vector_vertical_tangent P₀ u Hm χ hG R x₀ X p m hsm hpb z (fun _ _ => 0) hδ (fun _ => rfl)
    have e1 : w = w₀ := huniq w (fun W f hzW => (hw ⟨⟨W, f⟩, hzW⟩).symm)
    have e2 : (0 : Fin P₀.g → ℂ) = w₀ := huniq 0 (fun W f _ => (ContinuousLinearMap.map_zero _).symm)
    exact e1.trans e2.symm
  obtain ⟨c, hc⟩ := exists_det_ne_zero_of_common_ker φ hker
  have hzW : z ∈ dom u m (Finset.univ.inf fun b => (c b).1.1) :=
    top_le_preimage_finset_inf ((u.ex z).left ≫ m) Finset.univ (fun b => (c b).1.1) (fun b _ => (c b).2)
  refine ⟨Finset.univ.inf fun b => (c b).1.1,
    fun b => resG X (Finset.inf_le (Finset.mem_univ b)) (c b).1.2, hzW, ?_⟩
  have hE : (Matrix.of fun a b => fderiv ℂ (fn u m (Finset.univ.inf fun b => (c b).1.1)
      (resG X (Finset.inf_le (Finset.mem_univ b)) (c b).1.2)) z (Pi.single a 1)) =
      Matrix.of fun a b => φ (c b) (Pi.single a 1) := by
    ext a b
    simp only [Matrix.of_apply]
    rw [fderiv_fn_resG u m (Finset.inf_le (Finset.mem_univ b)) (c b).1.2 hzW]
    rfl
  rw [hE]
  exact hc

end GlobalTheory.KS
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_abelianScheme_descent_of_galoisCover : ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp K) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (G : Over X) [GrpObj G] (ν : Ga → (G.left ⟶ G.left)), IsGaloisCover Ga ρ π → IsQProjOver (G.hom ≫ π ≫ sY) → IsAbelianScheme G → (∀ a, IsGrpPullback G G (ρ a) (ν a)) → ν 1 = 𝟙 _ → (∀ a c, ν (a * c) = ν a ≫ ν c) → ∃ (G' : Over Y) (_ : GrpObj G') (φ : G.left ⟶ G'.left), IsAbelianScheme G' ∧ IsGrpPullback G G' π φ ∧ IsGaloisCover Ga ν φ := by
  first | exact @GlobalTheory.abelianScheme_descends_galoisCover | exact GlobalTheory.abelianScheme_descends_galoisCover | (intros; apply GlobalTheory.abelianScheme_descends_galoisCover <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

def chartPullCompOfPullPull {X Y Z : Scheme.{0}} (M : LB X) (π : Y ⟶ X) (φ : Z ⟶ Y) :
    ChartPull (M.pull (φ ≫ π)) ((M.pull π).pull φ) (𝟙 Z) where
  idx j := fun _ => j
  le j := RepBC.le₂ M π φ j
  g y j j' hj hj' := by
    have h := RepBC.le₂ M π φ j hj
    have h' := RepBC.le₂ M π φ j' hj'
    refine (gm_pull_g M (φ ≫ π) (𝟙 Z) y j j' hj hj').trans (Eq.symm ?_)
    refine (gm_pull_g (M.pull π) φ (𝟙 Z) y (fun _ => j) (fun _ => j') h h').trans ?_
    exact gm_pull_g M π (𝟙 Z ≫ φ) y j j' (mem_pull.1 h) (mem_pull.1 h')

theorem lbIso_pullPull_iff {X Y Z : Scheme.{0}} (A : LB Z) (M : LB X) (π : Y ⟶ X) (φ : Z ⟶ Y) :
    LBIso A ((M.pull π).pull φ) ↔ LBIso A (M.pull (φ ≫ π)) :=
  ⟨LBIso.chartPull (chartPullId A) (chartPullCompOfPullPull M π φ),
    LBIso.chartPull (chartPullId A) (chartPullLinComb M π (fun _ : PUnit => φ) (fun _ => φ ≫ π) (fun _ => 1) (𝟙 Z)
      fun _ => (Category.id_comp _).symm)⟩

theorem fam_baseChange : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec) (sc : Ix g (N' ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (R' : Type) [CommRing R'] (ρ : R →+* R') (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → Fam b Mat κ β v m M th sc → ∃ (th' : Ix g (N' ^ 2) → (M.pull π).Sec) (sc' : Ix g (N' ^ 2) → (Out.baseOver (Sp R') ⟶ Z')), Fam b Mat κ (ρ.comp β) (fun a => ρ (v a)) m (M.pull π) th' sc' ∧ ∀ (K : Type) [Field K] (x : R' →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (φ : t.A.left ⟶ Z'.left), Fib m (M.pull π) th' sc' x t φ → Fib m M th sc (x.comp ρ) t (φ ≫ π) := by
  intro o _ g N' J b Mat κ R _ β v m Z M th sc R' _ ρ Z' π hp ⟨⟨I, p, hrep, hco⟩, hflat, hfib⟩
  obtain ⟨th', hrep', hc⟩ := RepBC.projRep_baseChange R R' _ ρ I _ _ _ _ π M th hrep hp
  have hw : ∀ h, (spMap ρ ≫ (sc h).left) ≫ Z.hom = 𝟙 _ ≫ spMap ρ := fun h => by
    rw [Category.assoc, Over.w (sc h), Category.id_comp]
    exact Category.comp_id _
  let sc' : Ix g (N' ^ 2) → (Out.baseOver (Sp R') ⟶ Z') := fun h =>
    Over.homMk (hp.lift (spMap ρ ≫ (sc h).left) (𝟙 _) (hw h)) (hp.lift_snd _ _ _)
  have hsc : ∀ h, (sc' h).left ≫ π = spMap ρ ≫ (sc h).left := fun h => hp.lift_fst _ _ _
  have hsc' : ∀ h, (sc' h).left ≫ Z'.hom = 𝟙 _ := fun h => hp.lift_snd _ _ _
  refine ⟨th', sc', ⟨⟨_, fun h a => ρ (p h a), hrep', fun h => (hc _ _ _).2 ?_⟩,
    MorphismProperty.of_isPullback (P := @Flat) hp hflat, ?_⟩, ?_⟩
  · rw [hsc]
    exact Coord.baseChange (hco h) ρ
  · intro K _ _ x s t ht
    obtain ⟨φ, h1, ⟨σ, hσ, h2⟩, h3, h4⟩ := hfib K (x.comp ρ) s t ((good_comp _ _ _).1 ht)
    have hw' : φ ≫ Z.hom = (t.A.hom ≫ spMap x) ≫ spMap ρ := by
      rw [h1.w, NearBuild.spMap_comp, Category.assoc]
    have e1 : hp.lift φ _ hw' ≫ π = φ := hp.lift_fst _ _ _
    have e2 : hp.lift φ _ hw' ≫ Z'.hom = t.A.hom ≫ spMap x := hp.lift_snd _ _ _
    generalize hp.lift φ _ hw' = φ' at e1 e2
    subst e1
    refine ⟨φ', IsPullback.of_right (by rw [← NearBuild.spMap_comp]; exact h1) e2 hp, ⟨σ, hσ, fun T _ y w => ?_⟩,
      (lbIso_pullPull_iff _ _ _ _).2 h3, fun h => ?_⟩
    · rw [h2 T y w, hc, Category.assoc, Category.assoc]
    · apply hp.hom_ext
      · rw [Category.assoc, h4, NearBuild.spMap_comp]
        erw [Category.assoc, Category.assoc, hsc]
      · rw [Category.assoc, e2, ← Category.assoc, Over.w (t.lab h ^ N')]
        erw [Category.assoc, hsc', Category.id_comp]
  · rintro K _ x s t φ ⟨h1, ⟨σ, hσ, h2⟩, h3, h4⟩
    refine ⟨by rw [NearBuild.spMap_comp]; exact h1.paste_horiz hp, ⟨σ, hσ, fun T _ y w => ?_⟩,
      (lbIso_pullPull_iff _ _ _ _).1 h3, fun h => ?_⟩
    · rw [h2 T y w, hc, Category.assoc, Category.assoc]
    · rw [← Category.assoc, h4, NearBuild.spMap_comp]
      erw [Category.assoc, Category.assoc, hsc]

end GlobalTheory.ZM.NearBuild
end
end
