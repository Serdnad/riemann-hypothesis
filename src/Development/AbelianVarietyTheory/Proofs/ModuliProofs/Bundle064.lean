module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoNormalizationPullbackOfToIntegralClosure
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulApplyEqOfEqOnInvariants
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteSeparableOfSumMem
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartFiniteType
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle046
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
public import Mathlib.CategoryTheory.MorphismProperty.Descent

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_eq_evaluation_div {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (z : X.residueField x) : ∃ a b : Γ(X, U), z = X.evaluation U x hx a / X.evaluation U x hx b := by
  classical
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  haveI : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  have he : ∀ c, X.evaluation U x hx c =
      (X.residue x).hom (algebraMap Γ(X, U) (X.presheaf.stalk x) c) := fun c => rfl
  obtain ⟨s, rfl⟩ : ∃ s, (X.residue x).hom s = z := IsLocalRing.residue_surjective z
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl s
  change s * algebraMap Γ(X, U) (X.presheaf.stalk x) (b : Γ(X, U)) =
    algebraMap Γ(X, U) (X.presheaf.stalk x) a at hab
  have hb0 : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) (b : Γ(X, U))) :=
    IsLocalization.map_units _ b
  have hb := hb0.map (X.residue x).hom
  refine ⟨a, b, ?_⟩
  rw [he, he, eq_div_iff hb.ne_zero, ← map_mul (X.residue x).hom, hab]

theorem isFractionRing_residueField {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (q : Ideal Γ(X, U)) (hq : ∀ a, a ∈ q ↔ X.evaluation U x hx a = 0) :
    letI := (Ideal.Quotient.lift q (X.evaluation U x hx).hom fun a ha ↦ (hq a).1 ha).toAlgebra
    IsFractionRing (Γ(X, U) ⧸ q) (X.residueField x) := by
  letI : Algebra (Γ(X, U) ⧸ q) (X.residueField x) :=
    (Ideal.Quotient.lift q (X.evaluation U x hx).hom fun a ha ↦ (hq a).1 ha).toAlgebra
  have hmk : ∀ a, algebraMap (Γ(X, U) ⧸ q) (X.residueField x) (Ideal.Quotient.mk q a) =
      X.evaluation U x hx a := fun a => Ideal.Quotient.lift_mk _ _ _
  have hinj : Function.Injective (algebraMap (Γ(X, U) ⧸ q) (X.residueField x)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [hmk] at hc
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ((hq a).2 hc)
  haveI : NoZeroDivisors (Γ(X, U) ⧸ q) :=
    hinj.noZeroDivisors _ (map_zero _) (map_mul _)
  refine ⟨?_, ?_, ?_⟩
  · intro y
    refine isUnit_iff_ne_zero.mpr fun h => ?_
    haveI : Nontrivial (Γ(X, U) ⧸ q) :=
      ⟨⟨0, 1, fun h => by simpa using congrArg (algebraMap (Γ(X, U) ⧸ q) (X.residueField x)) h⟩⟩
    exact nonZeroDivisors.ne_zero y.2 (hinj (h.trans (map_zero _).symm))
  · intro z
    obtain ⟨a, b, hz⟩ := exists_eq_evaluation_div hU x hx z
    by_cases hb : X.evaluation U x hx b = 0
    · refine ⟨(0, 1), ?_⟩
      show z * algebraMap (Γ(X, U) ⧸ q) (X.residueField x) 1 =
        algebraMap (Γ(X, U) ⧸ q) (X.residueField x) 0
      rw [hz, hb, div_zero, zero_mul, map_zero]
    · have hb' : Ideal.Quotient.mk q b ≠ 0 := by
        intro h
        apply hb
        rw [← hmk, h, map_zero]
      refine ⟨(Ideal.Quotient.mk q a, ⟨Ideal.Quotient.mk q b, mem_nonZeroDivisors_of_ne_zero hb'⟩), ?_⟩
      show z * algebraMap (Γ(X, U) ⧸ q) (X.residueField x) (Ideal.Quotient.mk q b) =
        algebraMap (Γ(X, U) ⧸ q) (X.residueField x) (Ideal.Quotient.mk q a)
      rw [hz, hmk, hmk, div_mul_cancel₀ _ hb]
  · intro c d h
    exact ⟨1, by rw [hinj h]⟩

theorem residueFieldMap_finite_separable_of_tame {Γ : Type} [Group Γ] [Finite Γ] {X X' : Scheme.{0}}
    (ρ : Γ →* Aut X) (π : X ⟶ X') [IsAffineHom π] (hπ : ∀ g, (ρ g).asIso.hom ≫ π = π)
    (hinv : ∀ W : X'.Opens, IsAffineOpen W → ∀ s : Γ(X, π ⁻¹ᵁ W),
      IsInvariantSection ρ _ s → s ∈ Set.range (π.app W))
    (ht : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0)
    (x : X) :
    letI := (π.residueFieldMap x).hom.toAlgebra
    FiniteDimensional (X'.residueField (π x)) (X.residueField x) ∧
      Algebra.IsSeparable (X'.residueField (π x)) (X.residueField x) := by
  let := (π.residueFieldMap x).hom.toAlgebra
  obtain ⟨_, ⟨(W : X'.Opens), hW, rfl⟩, hx, -⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (π x)) isOpen_univ
  have hx : π x ∈ W := hx
  have hW : IsAffineOpen W := hW
  have hU : IsAffineOpen (π ⁻¹ᵁ W) := hW.preimage π
  have hst := preimage_le_of_invariant ρ π hπ W
  let := sectionsAction ρ _ hst
  let := (π.app W).hom.toAlgebra
  have hfix (g : Γ) (a : Γ(X', W)) : g • algebraMap Γ(X', W) Γ(X, π ⁻¹ᵁ W) a = algebraMap _ _ a :=
    (isInvariantSection_app ρ π hπ W a g⁻¹).2
  have : SMulCommClass Γ Γ(X', W) Γ(X, π ⁻¹ᵁ W) := ⟨fun g a s ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hfix]⟩
  have : Algebra.IsInvariant Γ(X', W) Γ(X, π ⁻¹ᵁ W) Γ := ⟨fun s hs ↦
    hinv W hW s fun g ↦ ⟨hst g, by simpa only [inv_inv] using
      (show (ρ g⁻¹⁻¹).asIso.hom.appLE _ _ (hst _) s = s from hs g⁻¹)⟩⟩
  let ev := X.evaluation (π ⁻¹ᵁ W) x hx
  let q : Ideal Γ(X, π ⁻¹ᵁ W) := RingHom.ker ev.hom
  have : q.IsPrime := RingHom.ker_isPrime _
  have hq : ∀ a, a ∈ q ↔ ev a = 0 := fun a ↦ Iff.rfl
  have hnat (a : Γ(X', W)) : π.residueFieldMap x (X'.evaluation W (π x) hx a) = ev (π.app W a) :=
    Scheme.evaluation_naturality_apply π x hx a
  have hp : ∀ a, a ∈ q.under Γ(X', W) ↔ X'.evaluation W (π x) hx a = 0 := fun a ↦ by
    rw [← map_eq_zero_iff _ (π.residueFieldMap x).hom.injective, hnat]
    rfl
  let := (Ideal.Quotient.lift q ev.hom fun a ha ↦ (hq a).1 ha).toAlgebra
  let := (Ideal.Quotient.lift _ (X'.evaluation W (π x) hx).hom fun a ha ↦ (hp a).1 ha).toAlgebra
  have := isFractionRing_residueField hU x hx q hq
  have := isFractionRing_residueField hW (π x) hx _ hp
  refine TameResidue.residue_finite_separable Γ Γ(X', W) Γ(X, π ⁻¹ᵁ W) q _ _ hnat fun hc ↦ ?_
  let Ω := AlgebraicClosure (X.residueField x)
  let jΩ : X.residueField x ⟶ CommRingCat.of Ω := CommRingCat.ofHom (algebraMap (X.residueField x) Ω)
  let y : Sp Ω ⟶ X := Spec.map (ev ≫ jΩ) ≫ hU.fromSpec
  have key (g : Γ) : g⁻¹ ∈ q.inertia Γ ↔ y ≫ (ρ g).asIso.hom = y := by
    have e : y ≫ (ρ g).asIso.hom = Spec.map ((ρ g).asIso.hom.appLE _ _ (hst g) ≫ ev ≫ jΩ) ≫ hU.fromSpec := by
      rw [Spec.map_comp, Category.assoc, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec _ hU hU]
    have : Mono jΩ := ConcreteCategory.mono_of_injective _ jΩ.hom.injective
    rw [e, cancel_mono, Spec.map_inj, ← Category.assoc, cancel_mono]
    have e₂ (s) : g⁻¹ • s = (ρ g).asIso.hom.appLE _ _ (hst g) s := by
      change (ρ g⁻¹⁻¹).asIso.hom.appLE _ _ (hst _) s = _
      simp only [inv_inv]
    refine Iff.trans AddSubgroup.mem_inertia ⟨fun h ↦ ?_, fun h s ↦ ?_⟩
    · ext s
      have := (hq _).1 (h s)
      rw [map_sub, sub_eq_zero, e₂] at this
      exact this
    · refine (hq _).2 ?_
      rw [map_sub, sub_eq_zero, e₂]
      exact congr($h s)
  have hcard : Nat.card {g // y ≫ (ρ g).asIso.hom = y} = Nat.card (q.inertia Γ) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun g ↦ (key g).symm.trans (inv_mem_iff (H := q.inertia Γ)))
  apply ht Ω y
  rw [hcard]
  have := congrArg jΩ.hom ((hq _).1 hc)
  simpa using this

theorem splitFibres_descend_of_tame_quotient : ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (G : Over X) [GrpObj G] (G' : Over X') [GrpObj G'] (φ : G.left ⟶ G'.left), (IsAffineHom π ∧ (∀ g, (ρ g).asIso.hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).asIso.hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).asIso.hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X), (Nat.card {g // x ≫ (ρ g).asIso.hom = x} : k) ≠ 0) → IsGrpPullback G G' π φ → (∀ x : X, ∃ (k : Type) (_ : Field k) (_ : Algebra (X.residueField x) k), FiniteDimensional (X.residueField x) k ∧ Algebra.IsSeparable (X.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x)).obj G)) → (∀ x : X', ∃ (k : Type) (_ : Field k) (_ : Algebra (X'.residueField x) k), FiniteDimensional (X'.residueField x) k ∧ Algebra.IsSeparable (X'.residueField x) k ∧ ∃ S : SplitExt (Sp k), S.IsGt ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField x) k)) ≫ X'.fromSpecResidueField x)).obj G')) := by
  intro Γ _ _ X X' ρ π G _ G' _ φ hq ht hφ hS x'
  obtain ⟨-, hsurj, -⟩ := quotient_isIntegral_surjective_orbits Γ X X' ρ π hq
  obtain ⟨_, hπ, hV⟩ := hq
  obtain ⟨x, rfl⟩ := π.surjective x'
  let := (π.residueFieldMap x).hom.toAlgebra
  obtain ⟨h₁, h₂⟩ := residueFieldMap_finite_separable_of_tame ρ π hπ
    (fun W _ s hs ↦ (hV W).2 s fun g _ ↦ (hs g).2) ht x
  obtain ⟨k, _, _, hfin, hsep, S, hGt⟩ := hS x
  let : Algebra (X'.residueField (π x)) k :=
    ((algebraMap (X.residueField x) k).comp (π.residueFieldMap x).hom).toAlgebra
  have : IsScalarTower (X'.residueField (π x)) (X.residueField x) k := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  refine ⟨k, inferInstance, inferInstance, Module.Finite.trans (X.residueField x) k,
    Algebra.IsSeparable.trans _ (X.residueField x) k, S, ?_⟩
  have key : (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x) ≫ π =
      Spec.map (CommRingCat.ofHom (algebraMap (X'.residueField (π x)) k)) ≫ X'.fromSpecResidueField (π x) := by
    rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Spec.map_comp_assoc]
    rfl
  rw [← key]
  generalize Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) k)) ≫ X.fromSpecResidueField x = t at hGt
  obtain ⟨e, he, -⟩ := grpPullback_iso hφ (isGrpPullback_pullback G' π)
  have : IsMonHom ((Over.pullback t).mapIso e).hom := by
    rw [Functor.mapIso_hom]
    infer_instance
  have h₃ := isGt_of_iso ((Over.pullback t).mapIso e) hGt
  have : IsMonHom (pullCompIso t π G').symm.hom := inferInstanceAs (IsMonHom (pullCompIso t π G').inv)
  exact isGt_of_iso (pullCompIso t π G').symm h₃

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.VeryDenseFibres

theorem smooth_fiber_of_smooth_fiber {X T S : Scheme.{0}} (f : X ⟶ S) (t : T ⟶ S) (y : T)
    (h : Smooth ((pullback.snd f t).fiberToSpecResidueField y)) :
    Smooth (f.fiberToSpecResidueField (t y)) := by
  have hp := isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f t) y
  refine MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp.flip ⟨⟨?_, ?_⟩, ?_⟩ h
  · exact ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  · infer_instance
  · infer_instance

theorem mem_smoothLocus_of_smooth_fiber {R : CommRingCat.{0}} {X : Scheme.{0}} (f : X ⟶ Spec R)
    [LocallyOfFinitePresentation f] [Flat f] (x : X)
    (h : Smooth (f.fiberToSpecResidueField (f x))) : x ∈ f.smoothLocus := by
  wlog hX : ∃ S, X = Spec S generalizing f X
  · obtain ⟨i, y, rfl⟩ := X.affineCover.exists_eq x
    have _ : Smooth (pullback.snd f ((Spec R).fromSpecResidueField
        ((X.affineCover.f i ≫ f) y))) := h
    have H := this (X.affineCover.f i ≫ f) y (by
      rw [Scheme.Hom.fiberToSpecResidueField, ← pullbackRightPullbackFstIso_inv_snd_snd]
      infer_instance) ⟨_, rfl⟩
    rwa [← Scheme.Hom.preimage_smoothLocus_eq] at H
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  letI := φ.hom.toAlgebra
  haveI : Algebra.FinitePresentation R S :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation) (φ := φ)).mp ‹_›
  haveI : Module.Flat R S :=
    (HasRingHomProperty.Spec_iff (P := @Flat) (φ := φ)).mp ‹_›
  haveI : x.asIdeal.IsPrime := PrimeSpectrum.isPrime x
  let p : PrimeSpectrum R := Spec.map φ x
  haveI : x.asIdeal.LiesOver p.asIdeal := ⟨rfl⟩
  haveI : Algebra.FormallySmooth p.asIdeal.ResidueField (p.asIdeal.Fiber S) := by
    rw [← RingHom.formallySmooth_algebraMap]
    refine RingHom.Smooth.formallySmooth ?_
    rw [← CommRingCat.hom_ofHom (algebraMap p.asIdeal.ResidueField (p.asIdeal.Fiber ↑S)),
      ← HasRingHomProperty.Spec_iff (P := @Smooth),
      ← MorphismProperty.arrow_mk_iso_iff (P := @Smooth) (Spec.fiberToSpecResidueFieldIso R S p)]
    exact h
  haveI := Algebra.IsSmoothAt.of_formallySmooth_fiber (R := R) p.asIdeal x.asIdeal
  obtain ⟨g, hg, hsm⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R x.asIdeal
  let j : Spec (CommRingCat.of (Localization.Away g)) ⟶ Spec S :=
    Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g)))
  haveI : IsOpenImmersion j := IsOpenImmersion.of_isLocalization g
  haveI : Smooth (j ≫ Spec.map φ) := by
    rw [← Spec.map_comp, HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hsm
  obtain ⟨y, rfl⟩ : x ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
    rw [PrimeSpectrum.localization_away_comap_range _ g]
    exact hg
  have := (j ≫ Spec.map φ).smoothLocus_eq_top.ge (Set.mem_univ y)
  rwa [← Scheme.Hom.preimage_smoothLocus_eq] at this

theorem exists_opens_smoothOfRelativeDimension {X T S : Scheme.{0}} (f : X ⟶ S) [Smooth f]
    (t : T ⟶ S) (g : ℕ) (h : SmoothOfRelativeDimension g (pullback.snd f t)) (x : X) (y : T)
    (hxy : f x = t y) : ∃ W : X.Opens, x ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ f) := by
  obtain ⟨n, W, hW, hd⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim f x
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} n
  have h1 : SmoothOfRelativeDimension n (pullback.snd (W.ι ≫ f) t) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) _ _ hd
  have h2 : SmoothOfRelativeDimension (0 + (0 + g)) (pullback.snd (W.ι ≫ f) t) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback (W.ι ≫ f) t)
    ⟨x, hW⟩ y hxy
  have e : n = g := by simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2 z
  exact ⟨W, hW, e ▸ hd⟩

theorem eq_top_of_forall_mem {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R)
    [UniversallyClosed s] (P : Set (Ideal R))
    (hP : ∀ q : Ideal R, q.IsPrime → ∃ p ∈ P, p.IsPrime ∧ q ≤ p) (U : Z.Opens)
    (hU : ∀ z : Z, (s z).asIdeal ∈ P → z ∈ U) : U = ⊤ := by
  rw [← top_le_iff]
  intro x _
  by_contra hx
  have hc : IsClosed (s '' (U : Set Z)ᶜ) := s.isClosedMap _ U.2.isClosed_compl
  obtain ⟨p, hp, hp', hle⟩ := hP (s x).asIdeal (PrimeSpectrum.isPrime _)
  have hs : s x ⤳ (⟨p, hp'⟩ : PrimeSpectrum R) := (PrimeSpectrum.le_iff_specializes _ _).1 hle
  obtain ⟨y, hy, hy'⟩ := hs.mem_closed hc ⟨x, hx, rfl⟩
  exact hy (hU y (by rw [hy']; exact hp))

theorem spMap_apply_asIdeal {R K : Type} [CommRing R] [Field K] (x : R →+* K) (y : Sp K) :
    (spMap x y).asIdeal = RingHom.ker x := by
  have : y.asIdeal = ⊥ := by
    have := PrimeSpectrum.isPrime y
    exact Ideal.eq_bot_of_prime _
  change Ideal.comap x y.asIdeal = _
  rw [this]
  rfl

end GlobalTheory.VeryDenseFibres
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FieldBaseChange

theorem flat_spMap {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) : Flat (spMap i) := by
  rw [Flat.SpecMap_iff]
  letI := i.toAlgebra
  exact (inferInstance : Module.Flat K₀ K)

theorem surjective_spMap {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) : Surjective (spMap i) := by
  have : Subsingleton (Sp K₀) := inferInstanceAs (Subsingleton (PrimeSpectrum K₀))
  have : Nonempty (Sp K) := inferInstanceAs (Nonempty (PrimeSpectrum K))
  exact ⟨fun y => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩

section General

variable {U S : Scheme.{0}} (j : U ⟶ S)

theorem pullback_map_left_fst {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback j).map a).left ≫ pullback.fst Y.hom j = pullback.fst X.hom j ≫ a.left :=
  pullback.lift_fst _ _ _

theorem pullback_map_injective [Flat j] [Surjective j] (X Y : Over S) :
    Function.Injective ((Over.pullback j).map : (X ⟶ Y) → _) := fun f g h => by
  have : Epi (pullback.fst X.hom j) := Flat.epi_of_flat_of_surjective _
  apply Over.OverMorphism.ext
  rw [← cancel_epi (pullback.fst X.hom j), ← pullback_map_left_fst, ← pullback_map_left_fst, h]

theorem isMonHom_of_pullback [Flat j] [Surjective j] {G H : Over S} [MonObj G] [MonObj H] (f : G ⟶ H)
    (hf : IsMonHom ((Over.pullback j).map f)) : IsMonHom f := by
  constructor
  · apply pullback_map_injective j
    have h := hf.one_hom
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi] at h
    rw [Functor.map_comp, h]
  · apply pullback_map_injective j
    have h := hf.mul_hom
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Functor.LaxMonoidal.μ_natural_assoc, Category.assoc,
      cancel_epi] at h
    rw [Functor.map_comp, Functor.map_comp, h]


variable {j} in
theorem isMonHom_iff_of_isGrpPullback [Flat j] [Surjective j] {G H : Over S} [GrpObj G] [GrpObj H]
    {G' H' : Over U} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hG : IsGrpPullback G' G j φ) (hH : IsGrpPullback H' H j ψ) (f' : G' ⟶ H') (f : G ⟶ H)
    (hf : φ ≫ f.left = f'.left ≫ ψ) : IsMonHom f' ↔ IsMonHom f := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso (isGrpPullback_pullback G j) hG
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hH (isGrpPullback_pullback H j)
  have e : (Over.pullback j).map f = a.hom ≫ f' ≫ b.hom := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [pullback_map_left_fst, Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hb', ← hf,
        ← Category.assoc, ha']
    · exact (Over.w _).trans (Over.w _).symm
  constructor
  · intro h
    exact isMonHom_of_pullback j f (by rw [e]; infer_instance)
  · intro h
    have e' : f' = a.inv ≫ (Over.pullback j).map f ≫ b.inv := by simp [e]
    rw [e']
    infer_instance

end General

theorem epi_and_isMonHom_iff : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K), (∀ (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀), IsPullback φ p p₀ (spMap i) → Epi φ ∧ Flat φ ∧ Surjective φ ∧ IsAffineHom φ ∧ ∀ U : X₀.Opens, Function.Injective (φ.app U).hom) ∧ ∀ (A₀ B₀ : Over (Sp K₀)) (A B : Over (Sp K)) [GrpObj A₀] [GrpObj B₀] [GrpObj A] [GrpObj B] (φ : A.left ⟶ A₀.left) (ψ : B.left ⟶ B₀.left) (f₀ : A₀ ⟶ B₀) (f : A ⟶ B), IsGrpPullback A A₀ (spMap i) φ → IsGrpPullback B B₀ (spMap i) ψ → φ ≫ f₀.left = f.left ≫ ψ → (IsMonHom f ↔ IsMonHom f₀) := by
  intro K₀ K _ _ i
  have := flat_spMap i
  have := surjective_spMap i
  refine ⟨fun X₀ X p₀ p φ h => ?_, fun A₀ B₀ A B _ _ _ _ φ ψ f₀ f hA hB hf =>
    isMonHom_iff_of_isGrpPullback hA hB f f₀ hf⟩
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) h.flip ‹_›
  have : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) h.flip ‹_›
  have : IsAffineHom φ := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  exact ⟨Flat.epi_of_flat_of_surjective φ, ‹_›, ‹_›, ‹_›, fun U => GlobalTheory.FunDescent.app_injective φ U⟩

end GlobalTheory.FieldBaseChange
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TraitDataIntrinsic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)

theorem j_s : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

theorem exists_generic {S T : Scheme.{0}} {i : T ⟶ S} {χ : S ⟶ Y.X} {t : SAB H S} (m : SABMap t Y.t χ) {v : T ⟶ Xo.XF c}
    (hv : v ≫ Y.j = i ≫ χ) : ∃ (t' : SAB H T) (m₁ : SABMap t' t i) (n : SABMap t' Y.oF.t v)
      (m₂ : SABMap t' Xo.univ.t (v ≫ pullback.fst _ _)), m₁.φ ≫ m.φ = n.φ ≫ Y.m.φ ∧ m₂.φ = n.φ ≫ Y.m0.toSABMap.φ := by
  obtain ⟨t', ⟨p⟩⟩ := (GlobalTheory.ModelPoints.model_points_charts E H D l Xo c O β Y).2.1 _ (i ≫ χ)
  obtain ⟨m₁, h₁⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m p
  have key : ∀ u : T ⟶ Y.X, v ≫ Y.j = u → ∀ p : SABMap t' Y.t u, ∃ n : SABMap t' Y.oF.t v, p.φ = n.φ ≫ Y.m.φ := by
    rintro _ rfl p
    exact GlobalTheory.ObjMaps.exists_sab_cancel Y.m p
  obtain ⟨n, hn⟩ := key _ hv p
  obtain ⟨m₂, h₂⟩ := GlobalTheory.ObjMaps.exists_sab_comp Y.m0.toSABMap n
  exact ⟨t', m₁, n, m₂, h₁.symm.trans hn, h₂⟩

end GlobalTheory.TraitDataIntrinsic
end
