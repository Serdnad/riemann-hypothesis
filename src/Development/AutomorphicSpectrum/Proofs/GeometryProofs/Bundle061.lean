module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatingModelChartCompat
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Mathlib.Basic.Complex.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle049
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalExtensionProjectiveModule
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSchemeMapFromSpecialFibre
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle002
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle011

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChartSmooth

open GlobalTheory.CompanionTheory.Ar.ChartFin

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem mem_adjoin_iff {o : Type} [CommRing o] [Algebra o Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type}
    {x : κ → Ω} (hall : ∀ q : X, genPt ξ ⤳ q) (T : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) {U : X.Opens}
    (hU : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩) (h : genPt ξ ∈ U) (a : Ω) :
    a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔ ∃ s : Γ(X, U), secVal ξ U h s = a := by
  rw [T.ring c hc a]
  constructor
  · intro H
    refine exists_secVal hall T.gen.inj U h a fun q hq => ?_
    obtain ⟨h', hi⟩ := (hU q).1 hq
    exact H _ hi
  · rintro ⟨s, rfl⟩ p hp
    have hq : p.1 ∈ U := (hU p.1).2 ⟨p.2, hp⟩
    exact ⟨_, _root_.GlobalTheory.CompanionTheory.Ar.ChartFin.genMap_germ ξ h hq p.2 s⟩

theorem exists_secEquiv {o : Type} [CommRing o] [Algebra o Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {κ : Type}
    {x : κ → Ω} (hall : ∀ q : X, genPt ξ ⤳ q) (T : CoordTie o ξ x) {c : κ} (hc : x c ≠ 0) {U : X.Opens}
    (hU : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩) (h : genPt ξ ∈ U) :
    ∃ E : Γ(X, U) ≃+* Algebra.adjoin o (Set.range fun j => x j / x c),
      ∀ s, ((E s : Algebra.adjoin o (Set.range fun j => x j / x c)) : Ω) = secVal ξ U h s := by
  have hm : ∀ s, secVal ξ U h s ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := fun s =>
    (mem_adjoin_iff hall T hc hU h _).2 ⟨s, rfl⟩
  refine ⟨RingEquiv.ofBijective ((secVal ξ U h).codRestrict _ hm) ⟨fun a b e => ?_, fun r => ?_⟩, fun _ => rfl⟩
  · exact secVal_injective hall T.gen.inj U h (congrArg Subtype.val e)
  · obtain ⟨s, hs⟩ := (mem_adjoin_iff hall T hc hU h r).1 r.2
    exact ⟨s, Subtype.ext hs⟩

variable {X' : Scheme.{0}} {Ω' : Type} [Field Ω']

theorem inChart_map {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {f : X' ⟶ X}
    {i : Ω →+* Ω'} {κ κ' : Type} {x : κ → Ω} {x' : κ' → Ω'} (hall : ∀ q : X, genPt ξ ⤳ q)
    (T : CoordTie ℤ ξ x) (T' : CoordTie ℤ ξ' x') (hd : Dominates ξ' ξ f i) {c : κ} {c' : κ'} (hc : x c ≠ 0)
    (hc' : x' c' ≠ 0) (hi : ∀ j, i (x j / x c) ∈ Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c'))
    (p' : Cpt ξ') (hp' : InChart ξ' x' c' p') : InChart ξ x c ⟨f p'.1, hall _⟩ := by
  obtain ⟨h, hreg, hunit⟩ := RegAtDom.regAt_dominates X Ω ξ X' Ω' ξ' f i hd p'
  obtain ⟨d, hd0, hdr⟩ := T.cover ⟨f p'.1, h⟩
  have ha0 : x c / x d ≠ 0 := div_ne_zero hc hd0
  have hinv : (i (x c / x d))⁻¹ ∈ regAt ξ' p' := by
    rw [← map_inv₀, inv_div]
    exact (T'.ring c' hc' _).1 (hi d) p' hp'
  have hu := hunit T'.gen _ (hdr c) ⟨(map_ne_zero i).2 ha0, hreg _ (hdr c), hinv⟩
  refine ⟨hc, fun j => ?_⟩
  have e : x j / x c = x j / x d * (x c / x d)⁻¹ := by
    field_simp
  rw [e]
  exact mul_mem (hdr j) hu.2.2

theorem smooth_chartRing (X X' : Scheme.{0}) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω]
    (ξ : Spec (CommRingCat.of Ω₀) ⟶ X)
    (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (f : X' ⟶ X) (i : Ω₀ →+* Ω) (κ κ' : Type) (x : κ → Ω₀) (x' : κ' → Ω) :
    (∀ q : X, genPt ξ ⤳ q) → (∀ q : X', genPt ξ' ⤳ q) → CoordTie ℤ ξ x → CoordTie ℤ ξ' x' →
    GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → Smooth f → ∀ (c : κ) (c' : κ'), x c ≠ 0 → x' c' ≠ 0 →
    (∀ j, i (x j / x c) ∈ Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c')) →
    ∃ φ : Algebra.adjoin ℤ (Set.range fun j => x j / x c) →+* Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c'),
      (∀ a, ((φ a : Algebra.adjoin ℤ (Set.range fun j' => x' j' / x' c')) : Ω) = i a) ∧ φ.Smooth := by
  intro hall hall' T T' hd hsm c c' hc hc' hi
  obtain ⟨U, hUa, hUm⟩ := T.affine c hc
  obtain ⟨U', hU'a, hU'm⟩ := T'.affine c' hc'
  have hg : genPt ξ ∈ U := (hUm _).2 ⟨specializes_rfl, inChart_genPt T.gen hc⟩
  have hg' : genPt ξ' ∈ U' := (hU'm _).2 ⟨specializes_rfl, inChart_genPt T'.gen hc'⟩
  have hle : U' ≤ f ⁻¹ᵁ U := by
    intro q hq
    obtain ⟨h, hin⟩ := (hU'm q).1 hq
    exact (hUm (f q)).2 ⟨hall _, inChart_map hall T T' hd hc hc' hi ⟨q, h⟩ hin⟩
  obtain ⟨E, hE⟩ := exists_secEquiv hall T hc hUm hg
  obtain ⟨E', hE'⟩ := exists_secEquiv hall' T' hc' hU'm hg'
  have hs : (f.appLE U U' hle).hom.Smooth := Smooth.smooth_appLE (f := f) hUa hU'a hle
  have hval : ∀ s, secVal ξ' U' hg' ((f.appLE U U' hle).hom s) = i (secVal ξ U hg s) := by
    intro s
    have h2 : genPt ξ' ∈ f ⁻¹ᵁ U := hle hg'
    rw [← secVal_app hd U hg h2 s, ← secVal_res ξ' (homOfLE hle) hg' h2 ((f.app U).hom s)]
    rfl
  refine ⟨(E'.toRingHom.comp (f.appLE U U' hle).hom).comp E.symm.toRingHom, fun a => ?_, ?_⟩
  · obtain ⟨s, rfl⟩ := E.surjective a
    simp only [RingHom.comp_apply]
    have : E.symm.toRingHom (E s) = s := E.symm_apply_apply s
    rw [this]
    exact (hE' _).trans ((hval s).trans (congrArg i (hE s).symm))
  · have hr := RingHom.Smooth.propertyIsLocal.respectsIso
    exact hr.2 _ E.symm (hr.1 _ E' hs)

end GlobalTheory.CompanionTheory.Ar.ChartSmooth
end
end

section

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.LieTangent

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    dualMap (g.comp f) = (dualMap g).comp (dualMap f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp

theorem centre_field_base {K K' : Type} [Field K] [Field K'] {X : Scheme.{0}} (φ : K →+* K')
    (z : Sp K ⟶ X) : centre (Spec.map (CommRingCat.ofHom φ) ≫ z) = centre z := by
  have : Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint K') = IsLocalRing.closedPoint K :=
    Subsingleton.elim _ _
  change (Spec.map (CommRingCat.ofHom φ) ≫ z) _ = z _
  rw [Scheme.Hom.comp_apply, this]

section
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
  {E : Type} [AddCommGroup E] [Module Ω E]

theorem extends_generise (M : LieModel G ξ E) (p : Cpt ξ) {y : X} (hy : genPt ξ ⤳ y) (c : y ⤳ p.1) {e : E}
    {v : epsAt (R := X.presheaf.stalk p.1) (X.fromSpecStalk p.1) ⟶ G} (h : M.Extends p e v) :
    M.Extends ⟨y, hy⟩ e (epsBase (R := X.presheaf.stalk p.1) (R' := X.presheaf.stalk y)
      (X.presheaf.stalkSpecializes c).hom (Scheme.SpecMap_stalkSpecializes_fromSpecStalk c) ≫ v) := by
  rw [LieModel.extends_iff] at *
  refine ⟨isTanAt_base _ _ h.1, ?_⟩
  rw [h.2, ← Category.assoc]
  congr 1
  refine Over.OverMorphism.ext ?_
  change Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [spec_comp, ← dualMap_comp]
  congr 3
  exact RingHom.ext fun s => (genMap_specializes p hy c s).symm

theorem valAt_lie_base {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (φ : R →+* R')
    (M : LieModel G ξ E) {z : Sp R ⟶ X} {z' : Sp R' ⟶ X} (hz : Spec.map (CommRingCat.ofHom φ) ≫ z = z')
    (hg : genPt ξ ⤳ centre z') {e : E} {w : epsAt z ⟶ G} (h : M.ValAt z e w) :
    M.ValAt z' e (epsBase φ hz ≫ w) := by
  subst hz
  rw [LieModel.valAt_iff] at *
  obtain ⟨h1, v, hv, rfl⟩ := h
  refine ⟨hg, _, extends_generise M ⟨centre z, h1⟩ hg (centre_specializes φ z) hv, ?_⟩
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  refine Over.OverMorphism.ext ?_
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [spec_comp, spec_comp, ← dualMap_comp, ← dualMap_comp]
  congr 3
  exact congrArg (fun g => g.hom) (stalk_base φ z).symm

end

theorem pull_lie_value : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : Type) [Field L] [NumberField L]
    (z : Sp (𝓞 L) ⟶ X) (σ : L →+* ℂ) (Bc : Type) [AddCommGroup Bc] [Module (𝓞 L) Bc] (MB : LieModel G z Bc) (x : Bc) (e : Li)
    (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
    M.ValAt _ e v → (v.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (MB.pt x).left) →
    ∃ v' : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ G, M.ValAt _ e v' ∧
      (v'.left ≫ (𝟙 G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (MB.pt x).left) := by
  intro X Ω _ ξ G _ Li _ _ M L _ _ z σ Bc _ _ MB x e v hv hl
  have hz : Spec.map (CommRingCat.ofHom σ) ≫ (spMap (algebraMap (𝓞 L) L) ≫ z) =
      spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z := by
    rw [← Category.assoc, spec_comp]
  have hg : genPt ξ ⤳ centre (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) := by
    obtain ⟨h1, -⟩ := hv
    rw [← hz, centre_field_base]
    exact h1
  refine ⟨epsBase σ hz ≫ v, valAt_lie_base σ M hz hg hv, ?_⟩
  unfold LieModel.Lifts at *
  change (Spec.map _ ≫ v.left) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rw [Category.comp_id] at hl
  rw [hl, ← Category.assoc, spec_comp, ← dualMap_comp]

end GlobalTheory.CompanionTheory.Ar.RootHt
end
end

section

open MvPolynomial

theorem _root_.GlobalTheory.T.multihomog_covering_forms : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a b : K → ℕ) (n : ℕ) (u v : Fin n → MvPolynomial (Σ k, ι k) ℤ), (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (u j) a) → (∀ j, GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (v j) b) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j)) ≠ 0) → (∀ z : ((Σ k, ι k) → ℂ), (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∃ j, eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j)) ≠ 0) → ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A → ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A → ∃ A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, A'.a = (fun k => A.a k + (a k : ℤ) - (b k : ℤ)) ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A' ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsConjInvariantH A' ∧ ∀ z : ((Σ k, ι k) → ℂ), A'.h z = A.h z * Real.sqrt ((∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (u j))‖ ^ 2) / (∑ j, ‖eval z (MvPolynomial.map (Int.castRingHom ℂ) (v j))‖ ^ 2)) := by
  first | exact @GlobalTheory.CompanionTheory.TwistLine.twisted_hermitian_line | exact GlobalTheory.CompanionTheory.TwistLine.twisted_hermitian_line | (intros; apply GlobalTheory.CompanionTheory.TwistLine.twisted_hermitian_line <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

theorem _root_.GlobalTheory.T.flat_local_extension_exists : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (j : X ⟶ Y) (q : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation j], (∀ (P : Ideal R) [P.IsPrime], ∃ (R' : Type) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R') (X' Y' : Scheme.{0}) (j' : X' ⟶ Y') (q' : Y' ⟶ Spec (CommRingCat.of R')) (a : X' ⟶ X) (b : Y' ⟶ Y) (U : X'.Opens), Module.Flat R R' ∧ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P ∧ IsPullback b q' q (Spec.map (CommRingCat.ofHom (algebraMap R R'))) ∧ IsPullback a j' j b ∧ IsOpenImmersion (U.ι ≫ j') ∧ ∀ x : X', q' (j' x) = IsLocalRing.closedPoint R' → x ∈ U) → IsOpenImmersion j := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flat_local_extension_exists | exact GlobalTheory.CompanionTheory.Relay.flat_local_extension_exists | (intros; apply GlobalTheory.CompanionTheory.Relay.flat_local_extension_exists <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

theorem _root_.GlobalTheory.T.stalk_surjective_open_immersion : ∀ (S X₀ Xg X' : Scheme.{0}) (e : Xg ⟶ X₀) (f : X' ⟶ Xg) (W' : X'.Opens) (jW : W'.toScheme ⟶ S) (jQ : S ⟶ Xg), IsPreimmersion e → IsOpenImmersion jQ → IsIso jW → jW ≫ jQ = W'.ι ≫ f → ∀ x ∈ W', Function.Surjective ((f ≫ e).stalkMap x).hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.stalkMap_comp_surjective_of_open_part | exact GlobalTheory.CompanionTheory.Ar.Flat.stalkMap_comp_surjective_of_open_part | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.stalkMap_comp_surjective_of_open_part <;> assumption)
end

section

open NumberField


theorem _root_.GlobalTheory.T.principal_extension_projective_module : ∀ (L : Type) [Field L] [NumberField L] (B : Type) [AddCommGroup B] [Module (𝓞 L) B] [Module.Finite (𝓞 L) B] [Module.Projective (𝓞 L) B] (I : Ideal (𝓞 L)), I ≠ ⊥ → ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (y : 𝓞 L'), I.map (algebraMap (𝓞 L) (𝓞 L')) = Ideal.span {y} ∧ ∀ (B' : Type) [AddCommGroup B'] [Module (𝓞 L') B'] [Module.Finite (𝓞 L') B'] [Module.Projective (𝓞 L') B'] (io : B →ₛₗ[algebraMap (𝓞 L) (𝓞 L')] B'), Submodule.span (𝓞 L') (Set.range io) = ⊤ → Module.finrank (𝓞 L') B' = Module.finrank (𝓞 L) B → ∃ e : Fin (Module.finrank (𝓞 L') B') → B', LinearIndependent (𝓞 L') e ∧ Submodule.span (𝓞 L') (Set.range e) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Basis.exists_basis_after_extension | exact GlobalTheory.CompanionTheory.Ar.Basis.exists_basis_after_extension | (intros; apply GlobalTheory.CompanionTheory.Ar.Basis.exists_basis_after_extension <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem movePositionToLast : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ), IsIntersectionFamily I → ∀ (P : Ideal (MRing ι)) (e : ℕ) (L : Fin (e + 1) → HermLine ι) (i : Fin (e + 1)), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → I P (e + 1) L = I P (e + 1) (Fin.snoc (fun j : Fin e => L (i.succAbove j)) (L i)) := by
  intro K _ ι _ I hI P e L i hP hL
  let σ : Equiv.Perm (Fin (e + 1)) := (finSuccEquivLast (n := e)).trans (finSuccEquiv' i).symm
  have h : (Fin.snoc (fun j : Fin e => L (i.succAbove j)) (L i) : Fin (e + 1) → HermLine ι) = L ∘ σ := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [σ]
    · simp [σ]
  rw [h]
  exact (hI.1 P (e + 1) L σ hP hL).symm

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem goodProjExistsStatement_holds : ReciprocityTheory.ChartRestriction.G.Geo.GoodProjExistsStatement :=
  ReciprocityTheory.ChartRestriction.G.Geo.goodProjExists

end GlobalTheory.CompanionTheory.Ar.Link
end

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

theorem _root_.GlobalTheory.T.finite_scheme_map_from_special_fibre : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X Y : Over (Spec (CommRingCat.of R))) [IsFinite X.hom] [IsFinite Y.hom] (f : X ⟶ Y), ∃ (P Q : Type) (_ : CommRing P) (_ : CommRing Q) (_ : Algebra R P) (_ : Algebra R Q) (φ : Q →ₐ[R] P) (i : X.left ≅ Spec (CommRingCat.of P)) (j : Y.left ≅ Spec (CommRingCat.of Q)) (i₀ : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).obj X).left ≅ Spec (CommRingCat.of (IsLocalRing.ResidueField R ⊗[R] P))) (j₀ : ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).obj Y).left ≅ Spec (CommRingCat.of (IsLocalRing.ResidueField R ⊗[R] Q))), Module.Finite R P ∧ Module.Finite R Q ∧ (Flat X.hom → Module.Flat R P) ∧ f.left = i.hom ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j.inv ∧ ((Over.pullback (thick R (IsLocalRing.maximalIdeal R) 0)).map f).left = i₀.hom ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) φ).toRingHom) ≫ j₀.inv := by
  first | exact @GlobalTheory.CompanionTheory.FinFlatModel.exists_algHom_model | exact GlobalTheory.CompanionTheory.FinFlatModel.exists_algHom_model | (intros; apply GlobalTheory.CompanionTheory.FinFlatModel.exists_algHom_model <;> assumption)
end
