module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle002
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Tactic.ENatToNat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FourierExtractionTsumClass
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle003
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.QuasiAffine
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GenSpread.ClosedFac

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R]

def str {H : Scheme.{0}} (q : H ⟶ Sp R) (U : H.Opens) : CommRingCat.of R ⟶ Γ(H, U) :=
  CommRingCat.ofHom (GlobalTheory.SectionsCommRing.structureHom q U)

theorem fromSpec_comp {H : Scheme.{0}} (q : H ⟶ Sp R) {U : H.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ q = Spec.map (str q U) := by
  rw [← IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top _) hU (fun _ _ => trivial),
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]; rfl

theorem str_res {H : Scheme.{0}} (q : H ⟶ Sp R) (U : H.Opens) (a : R) :
    str q U a = H.presheaf.map (homOfLE le_top).op (str q ⊤ a) :=
  (GlobalTheory.SectionsCommRing.map_structureHom q le_top a).symm

theorem appTop_str {H T : Scheme.{0}} (q : H ⟶ Sp R) {R' : Type} [CommRing R'] (g : R →+* R') (x : T ⟶ H)
    (t : T ⟶ Sp R') (w : x ≫ q = t ≫ spMap g) (a : R) : x.appTop (str q ⊤ a) = str t ⊤ (g a) := by
  have e {Y : Scheme.{0}} {S : Type} [CommRing S] (p : Y ⟶ Sp S) :
      str p ⊤ = (Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ p.appTop :=
    congrArg ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ≫ ·) (Scheme.Hom.appLE_eq_app (f := p) (U := ⊤))
  have : str q ⊤ ≫ x.appTop = CommRingCat.ofHom g ≫ str t ⊤ := by
    rw [e, e, Category.assoc, ← Scheme.Hom.comp_appTop, w, Scheme.Hom.comp_appTop,
      Scheme.ΓSpecIso_inv_naturality_assoc]
  exact congrArg (fun φ => φ.hom a) this

theorem eq_zero_of_app_eq_zero {H : Scheme.{0}} {U : H.Opens} (hU : IsAffineOpen U) {B : CommRingCat.{0}}
    (f : Γ(H, U) ⟶ B) (s : Γ(H, U)) (hs : (Spec.map f ≫ hU.fromSpec).app U s = 0) : f s = 0 := by
  have hz : ⊤ ≤ (Spec.map f ≫ hU.fromSpec) ⁻¹ᵁ U := fun _ _ => hU.range_fromSpec.subset ⟨_, rfl⟩
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have h1 : hU.fromSpec.appLE U ⊤ hfs = (Scheme.ΓSpecIso Γ(H, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(H, U)).presheaf.map_id _
  have h2 : (Spec.map f ≫ hU.fromSpec).appLE U ⊤ hz = hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map f).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  rw [h1, ← Scheme.ΓSpecIso_inv_naturality] at h2
  have h3 : (Spec.map f ≫ hU.fromSpec).appLE U ⊤ hz s = 0 := by
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply, hs, map_zero]
  rw [h2, CommRingCat.comp_apply] at h3
  exact (map_eq_zero_iff _ (Scheme.ΓSpecIso B).symm.commRingCatIsoToRingEquiv.injective).1 h3

theorem exists_mul_eq_zero [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
    {Z H : Scheme.{0}} (i : Z ⟶ H) (q : H ⟶ Sp R) [IsLocallyNoetherian H]
    (h : ∀ (B : Type) [CommRing B] (x : Sp B ⟶ H) (t : Sp B ⟶ Sp K), x ≫ q = t ≫ spMap (algebraMap R K) →
      ∃ y : Sp B ⟶ Z, y ≫ i = x) (U : H.affineOpens) :
    ∃ a : R, a ≠ 0 ∧ ∀ s ∈ i.ker.ideal U, str q U.1 a * s = 0 := by
  classical
  let M : Submonoid Γ(H, U.1) := (nonZeroDivisors R).map (str q U.1).hom
  let B := Localization M
  let φ : R →+* B := (algebraMap Γ(H, U.1) B).comp (str q U.1).hom
  have hφ (y : nonZeroDivisors R) : IsUnit (φ y) := IsLocalization.map_units B (⟨_, y, y.2, rfl⟩ : M)
  let ψ : K →+* B := IsLocalization.lift (M := nonZeroDivisors R) hφ
  obtain ⟨y, hy⟩ := h B (spMap (algebraMap Γ(H, U.1) B) ≫ U.2.fromSpec) (spMap ψ) (by
    rw [Category.assoc, fromSpec_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext1
    exact (IsLocalization.lift_comp (M := nonZeroDivisors R) hφ).symm)
  have key (s : Γ(H, U.1)) (hs : s ∈ i.ker.ideal U) : ∃ a : R, a ≠ 0 ∧ str q U.1 a * s = 0 := by
    have h1 := (y ≫ i).ideal_ker_le U (y.le_ker_comp i U hs)
    rw [hy] at h1
    have h2 : algebraMap Γ(H, U.1) B s = 0 :=
      eq_zero_of_app_eq_zero U.2 (CommRingCat.ofHom (algebraMap Γ(H, U.1) B)) s h1
    obtain ⟨⟨_, a, ha, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff M B s).1 h2
    exact ⟨a, nonZeroDivisors.ne_zero ha, hm⟩
  have := IsLocallyNoetherian.component_noetherian U
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian (i.ker.ideal U)
  have hS' (s : S) : s.1 ∈ i.ker.ideal U := hS ▸ Ideal.subset_span s.2
  choose a ha ha' using fun s : S => key s (hS' s)
  refine ⟨∏ s, a s, Finset.prod_ne_zero_iff.2 fun s _ => ha s, fun s hs => ?_⟩
  rw [← hS] at hs
  refine Submodule.span_induction (fun s hs => ?_) (mul_zero _) (fun u v _ _ hu hv => ?_)
    (fun c u _ hu => ?_) hs
  · rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨s, hs⟩ : S)), map_mul, mul_assoc, ha' ⟨s, hs⟩, mul_zero]
  · rw [mul_add, hu, hv, add_zero]
  · rw [smul_eq_mul, mul_left_comm, hu, mul_zero]

theorem exists_lift (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (Z H : Scheme.{0}) (i : Z ⟶ H) (q : H ⟶ Sp R) (hi : IsClosedImmersion i)
    (hq : LocallyOfFiniteType q) (hq' : QuasiCompact q)
    (h : ∀ (B : Type) [CommRing B] (x : Sp B ⟶ H) (t : Sp B ⟶ Sp K), x ≫ q = t ≫ spMap (algebraMap R K) →
      ∃ y : Sp B ⟶ Z, y ≫ i = x) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (T : Scheme.{0}) (x : T ⟶ H) (t : T ⟶ Sp R'), x ≫ q = t ≫ spMap g → ∃ y : T ⟶ Z, y ≫ i = x := by
  classical
  have : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace H := QuasiCompact.compactSpace_of_compactSpace q
  obtain ⟨S, hS, hSU⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : H.Opens))).1
    isCompact_univ
  have : Fintype S := hS.fintype
  choose a ha ha' using exists_mul_eq_zero i q h
  refine ⟨∏ U : S, a U, Finset.prod_ne_zero_iff.2 fun U _ => ha U, fun R' _ g hg T x t w => ?_⟩
  set s := str q ⊤ (∏ U : S, a U) with hs
  have hx : IsUnit (x.appTop s) := by
    rw [hs, appTop_str q g x t w]
    exact hg.map _
  have hle : i.ker ≤ (H.basicOpen s).ι.ker := by
    refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun U : S => U.1) ?_ fun U u hu => ?_
    · rw [hSU, iSup_subtype]
    · rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
      have h0 : str q U.1.1 (∏ U : S, a U) * u = 0 := by
        rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ U), map_mul, mul_assoc, ha' _ u hu, mul_zero]
      have h1 : IsUnit ((H.basicOpen s).ι.app U.1.1 (str q U.1.1 (∏ U : S, a U))) := by
        rw [str_res, ← hs, ← CommRingCat.comp_apply, Scheme.Hom.naturality, CommRingCat.comp_apply]
        refine IsUnit.map _ ?_
        refine (H.basicOpen s).toScheme.toRingedSpace.isUnit_of_isUnit_germ _ _ fun z _ => ?_
        refine (Scheme.mem_basicOpen _ _ z _).1 ?_
        rw [← Scheme.preimage_basicOpen]
        exact z.2
      exact h1.mul_right_eq_zero.1 (by rw [← map_mul, h0, map_zero])
  have hr : Set.range x ⊆ Set.range (H.basicOpen s).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change z ∈ x ⁻¹ᵁ H.basicOpen s
    rw [Scheme.preimage_basicOpen_top, Scheme.basicOpen_of_isUnit _ hx]
    trivial
  refine ⟨IsOpenImmersion.lift _ x hr ≫ IsClosedImmersion.lift i _ hle, ?_⟩
  rw [Category.assoc, IsClosedImmersion.lift_fac, IsOpenImmersion.lift_fac]

end GlobalTheory.GenSpread.ClosedFac
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem hom_ext_of_geometricPoints_dense {X Y S : Scheme.{0}} [IsReduced X] (t : Y ⟶ S)
    [IsSeparated t] (f g : X ⟶ Y) (h : f ≫ t = g ≫ t) (D : Set X) (hD : Dense D)
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), Set.range x ⊆ D →
      x ≫ f = x ≫ g) : f = g := by
  suffices IsDominant (equalizer.ι f g) from
    ext_of_isDominant_of_isSeparated t h (equalizer.ι f g) (equalizer.condition _ _)
  refine ⟨Dense.mono (fun x hx ↦ ?_) hD⟩
  let K := AlgebraicClosure (X.residueField x)
  let y : Sp K ⟶ X :=
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) K)) ≫ X.fromSpecResidueField x
  have hy : ∀ p, y p = x := fun p ↦ Scheme.fromSpecResidueField_apply x _
  have hxy : y ≫ f = y ≫ g := H K y (by rintro _ ⟨p, rfl⟩; rwa [hy])
  have p : Sp K := IsLocalRing.closedPoint K
  refine ⟨equalizer.lift y hxy p, ?_⟩
  rw [← Scheme.Hom.comp_apply, equalizer.lift_ι, hy]

theorem exists_lift_closedImmersion_of_dense {X Y Z : Scheme.{0}} [IsReduced X] (i : Z ⟶ Y)
    [IsClosedImmersion i] (f : X ⟶ Y) (D : Set X) (hD : Dense D)
    (H : ∀ x ∈ D, f x ∈ Set.range i) : ∃ f' : X ⟶ Z, f' ≫ i = f := by
  have : IsDominant (pullback.snd i f) := ⟨Dense.mono (fun x hx ↦ by
    rw [Scheme.Pullback.range_snd]; exact H x hx) hD⟩
  have : Surjective (pullback.snd i f) :=
    surjective_of_isDominant_of_isClosed_range _ (Scheme.Hom.isClosedEmbedding _).isClosed_range
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd i f)
  refine ⟨inv (pullback.snd i f) ≫ pullback.fst i f, ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

theorem dense_fibres_ext :
    ∀ (X S : Scheme.{0}) [IsReduced X] (s : X ⟶ S) [Flat s] [LocallyOfFinitePresentation s]
      (Sg : Set S), Dense Sg → Dense (s ⁻¹' Sg) ∧
      (∀ (Y : Scheme.{0}) (t : Y ⟶ S) [IsSeparated t] (f g : X ⟶ Y), f ≫ t = s → g ≫ t = s →
        (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X),
          Set.range (x ≫ s) ⊆ Sg → x ≫ f = x ≫ g) → f = g) ∧
      (∀ (Y Z : Scheme.{0}) (i : Z ⟶ Y) [IsClosedImmersion i] (f : X ⟶ Y),
        (∀ x : X, s x ∈ Sg → f x ∈ Set.range i) → ∃ f' : X ⟶ Z, f' ≫ i = f) := by
  intro X S _ s _ _ Sg hSg
  have hD : Dense (s ⁻¹' Sg) := hSg.preimage s.isOpenMap
  refine ⟨hD, fun Y t _ f g hf hg H ↦ ?_, fun Y Z i _ f H ↦ ?_⟩
  · refine hom_ext_of_geometricPoints_dense t f g (hf.trans hg.symm) _ hD fun K _ _ x hx ↦ ?_
    refine H K x ?_
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact hx ⟨p, rfl⟩
  · exact exists_lift_closedImmersion_of_dense i f _ hD H

end GlobalTheory
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma exists_retraction_of_flat_quasiFinite (V K : Type) [CommRing V] [IsDomain V]
    [ValuationRing V] [Field K] [IsAlgClosed K] [Algebra V K] [IsFractionRing V K] {B : Type}
    [CommRing B] (φ : V →+* B) (hflat : φ.Flat) (hqf : φ.QuasiFinite) (q : Ideal B) [q.IsPrime]
    (hq : q.comap φ = IsLocalRing.maximalIdeal V) :
    ∃ ψ : B →+* V, ψ.comp φ = RingHom.id V ∧ (IsLocalRing.maximalIdeal V).comap ψ = q := by
  letI : Algebra V B := φ.toAlgebra
  haveI : Module.Flat V B := hflat
  haveI : Algebra.QuasiFinite V B := hqf.toAlgebra
  haveI : q.LiesOver (IsLocalRing.maximalIdeal V) := ⟨hq.symm⟩
  obtain ⟨P, hPq, hP, hPl⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal V))
    (q := IsLocalRing.maximalIdeal V) q bot_le
  have hPV : P.comap φ = ⊥ := hPl.over.symm
  set κ := P.ResidueField
  have hinj : Function.Injective (algebraMap V κ) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    rw [IsScalarTower.algebraMap_apply V B κ, Ideal.algebraMap_residueField_eq_zero] at hv
    have : v ∈ P.comap φ := hv
    rwa [hPV, Ideal.mem_bot] at this
  letI : Algebra K κ := (IsFractionRing.lift (K := K) hinj).toAlgebra
  haveI : IsScalarTower V K κ := IsScalarTower.of_algebraMap_eq
    (fun v => (IsFractionRing.lift_algebraMap (K := K) hinj v).symm)
  haveI : Algebra.QuasiFinite K κ := Algebra.QuasiFinite.of_restrictScalars V K κ
  haveI : Module.Finite K κ := Module.Finite.of_quasiFinite
  let e : K ≃+* κ := RingEquiv.ofBijective (algebraMap K κ)
    ⟨(algebraMap K κ).injective, IsSepClosed.algebraMap_surjective K κ⟩
  let χ : B →+* K := e.symm.toRingHom.comp (algebraMap B κ)
  have hχφ : ∀ v, χ (φ v) = algebraMap V K v := by
    intro v
    apply e.injective
    simp only [χ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.apply_symm_apply]
    change algebraMap B κ (algebraMap V B v) = algebraMap K κ (algebraMap V K v)
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hχ0 : ∀ b, χ b = 0 → b ∈ q := by
    intro b hb
    apply hPq
    rw [← Ideal.algebraMap_residueField_eq_zero]
    have : e (χ b) = algebraMap B κ b := by simp [χ]
    rw [← this, hb, map_zero]
  have hφq : ∀ v ∈ IsLocalRing.maximalIdeal V, φ v ∈ q := by
    intro v hv
    rw [← hq] at hv
    exact hv
  have hmem : ∀ b, χ b ∈ (algebraMap V K).range := by
    intro b
    rcases ValuationRing.isInteger_or_isInteger V (χ b) with ⟨v, hv⟩ | ⟨v, hv⟩
    · exact ⟨v, hv⟩
    by_cases hb0 : χ b = 0
    · exact ⟨0, by rw [hb0, map_zero]⟩
    by_cases hvu : IsUnit v
    · obtain ⟨u, rfl⟩ := hvu
      refine ⟨↑u⁻¹, ?_⟩
      rw [← inv_inv (χ b), ← hv]
      exact map_units_inv (algebraMap V K : V →* K) u
    · exfalso
      have hvm : v ∈ IsLocalRing.maximalIdeal V := hvu
      have h1 : χ (b * φ v - 1) = 0 := by
        rw [map_sub, map_mul, map_one, hχφ, hv, mul_inv_cancel₀ hb0, sub_self]
      have h2 := hχ0 _ h1
      have h3 : b * φ v ∈ q := q.mul_mem_left b (hφq v hvm)
      have h4 := q.sub_mem h3 h2
      rw [sub_sub_cancel] at h4
      exact ‹q.IsPrime›.ne_top ((Ideal.eq_top_iff_one q).mpr h4)
  let j := algebraMap V K
  have hj : Function.Injective j := IsFractionRing.injective V K
  let e₂ : V ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun a b h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  let ψ : B →+* V := e₂.symm.toRingHom.comp (χ.codRestrict j.range hmem)
  have hψ : ∀ b, j (ψ b) = χ b := by
    intro b
    have : e₂ (ψ b) = χ.codRestrict j.range hmem b := by simp [ψ]
    exact congrArg Subtype.val this
  refine ⟨ψ, ?_, ?_⟩
  · ext v
    apply hj
    simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [hψ, hχφ]
  · ext b
    rw [Ideal.mem_comap]
    constructor
    · intro hb
      have h1 : χ (b - φ (ψ b)) = 0 := by rw [map_sub, hχφ, hψ, sub_self]
      have h2 := hχ0 _ h1
      have h3 := hφq _ hb
      simpa using q.add_mem h2 h3
    · intro hb
      by_contra hn
      have hu : IsUnit (ψ b) := by
        by_contra h
        exact hn h
      obtain ⟨u, hu⟩ := hu
      have h1 : χ (b * φ ↑u⁻¹ - 1) = 0 := by
        rw [map_sub, map_mul, map_one, hχφ, ← hψ, ← hu, ← map_mul, Units.mul_inv, map_one, sub_self]
      have h2 := hχ0 _ h1
      have h3 : b * φ ↑u⁻¹ ∈ q := q.mul_mem_right _ hb
      have h4 := q.sub_mem h3 h2
      rw [sub_sub_cancel] at h4
      exact ‹q.IsPrime›.ne_top ((Ideal.eq_top_iff_one q).mpr h4)

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
private lemma exists_section_through_closed_fiber_point (V K : Type) [CommRing V] [IsDomain V]
    [ValuationRing V] [Field K] [IsAlgClosed K] [Algebra V K] [IsFractionRing V K]
    (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of V)) [LocallyQuasiFinite f] [Flat f] (x : X)
    (hx : f x = IsLocalRing.closedPoint V) :
    ∃ s : Spec (CommRingCat.of V) ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint V) = x := by
  obtain ⟨_, ⟨U, hU₀, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU₀
  have hg : Spec.map (Spec.preimage (hU.fromSpec ≫ f)) = hU.fromSpec ≫ f := Spec.map_preimage _
  set φ := Spec.preimage (hU.fromSpec ≫ f)
  haveI : Flat hU.fromSpec := inferInstance
  haveI : LocallyQuasiFinite hU.fromSpec := inferInstance
  haveI : Flat (hU.fromSpec ≫ f) := MorphismProperty.comp_mem _ _ _ ‹_› ‹_›
  haveI : LocallyQuasiFinite (hU.fromSpec ≫ f) := MorphismProperty.comp_mem _ _ _ ‹_› ‹_›
  have hflat : φ.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).mp (hg ▸ inferInstance)
  have hqf : φ.hom.QuasiFinite :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp (hg ▸ inferInstance)
  have hqx : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) = x := hU.fromSpec_primeIdealOf _
  set q := hU.primeIdealOf ⟨x, hxU⟩
  have hq : q.asIdeal.comap φ.hom = IsLocalRing.maximalIdeal V := by
    have h1 : (Spec.map φ) q = IsLocalRing.closedPoint V := by
      rw [hg]
      exact (congrArg f hqx).trans hx
    exact congrArg PrimeSpectrum.asIdeal h1
  obtain ⟨ψ, hψ, hψq⟩ := exists_retraction_of_flat_quasiFinite V K φ.hom hflat hqf q.asIdeal hq
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, ?_, ?_⟩
  · rw [Category.assoc, ← hg, ← Spec.map_comp]
    have : φ ≫ CommRingCat.ofHom ψ = 𝟙 _ := by ext1; exact hψ
    rw [this, Spec.map_id]
  · have : (Spec.map (CommRingCat.ofHom ψ)) (IsLocalRing.closedPoint V) = q :=
      PrimeSpectrum.ext hψq
    exact (congrArg hU.fromSpec this).trans hqx


open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
theorem _root_.GlobalTheory.exists_section_of_quasiFinite_flat :
    ∀ (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K] [IsAlgClosed K]
      [Algebra V K] [IsFractionRing V K] (X : Scheme.{0}) (f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V) [IsSeparated f]
      [QuasiCompact f] [LocallyOfFiniteType f] [LocallyQuasiFinite f] [Flat f] (x : X),
      f x = IsLocalRing.closedPoint V →
        ∃ s : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V ⟶ X, s ≫ f = 𝟙 _ ∧ s (IsLocalRing.closedPoint V) = x := by
  intro V K _ _ _ _ _ _ _ X f _ _ _ _ _ x hx
  exact exists_section_through_closed_fiber_point V K X f x hx

end GlobalTheory
end

section

open scoped BigOperators

theorem _root_.GlobalTheory.T.hasSum_graded_of_mul_degree' : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] (X : Type) [AddCommGroup X] (Rel : ℕ → (X → C) → C → Prop) (n k : ℕ), 1 ≤ n → 1 ≤ k → (∀ (l l' : ℕ) (a a' : X → C) (c c' : C), 1 ≤ l → 1 ≤ l' → Rel l a c → Rel l' a' c' → ∃ a'', Rel (l + l') a'' (c * c') ∧ ∀ α, HasSum (fun χ => a χ * a' (α - χ)) (a'' α)) → (∃ κ : C, κ ≠ 0 ∧ ∀ a c, Rel (n * k) a c → HasSum a (κ * c)) → ∃ u : C, u ≠ 0 ∧ ∀ a c, Rel k a c → Summable a → HasSum a (u * c) := by
  first | exact @GlobalTheory.hasSum_graded_of_mul_degree | exact GlobalTheory.hasSum_graded_of_mul_degree | (intros; apply GlobalTheory.hasSum_graded_of_mul_degree <;> assumption)
end

section

open Module

namespace GlobalTheory

theorem exists_torsion_twist_tsum_norm_ge :
    ∀ (K X : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (ζ : K), 0 < N → ‖(N : K)‖ = 1 → IsPrimitiveRoot ζ N → ∀ (σ : X → K) (q : X → ℝ) (r : ℝ), 0 < r → r < 1 → Filter.Tendsto q Filter.cofinite Filter.atTop → (∀ z, ‖σ z‖ ≤ r ^ q z) → ∀ z₀ : X, ‖σ z₀‖ = r ^ q z₀ → (∀ μ, μ ≠ 0 → q z₀ < q (z₀ + N • μ)) → ∃ t : Multiplicative X →* Kˣ, t ^ N = 1 ∧ r ^ q z₀ ≤ ‖∑' z, σ z * (t (Multiplicative.ofAdd z) : K)‖ := by
  classical
  intro K X _ _ _ _ _ _ N ζ hN hN1 hζ σ q r hr0 hr1 hq hσ z₀ hz₀ hlead
  have hσ0 : Filter.Tendsto σ Filter.cofinite (nhds 0) :=
    squeeze_zero_norm hσ ((tendsto_rpow_atTop_of_base_lt_one r (by linarith) hr1).comp hq)
  obtain ⟨hfin, hsum, hnorm⟩ :=
    fourier_extraction_tsum_class K X N ζ hN hN1 hζ σ hσ0 z₀
  have hclass : ‖∑' μ, σ (z₀ + N • μ)‖ = r ^ q z₀ := by
    rw [← hz₀]
    refine hnorm fun μ hμ => (hσ _).trans_lt ?_
    rw [hz₀]
    exact Real.rpow_lt_rpow_of_exponent_gt hr0 hr1 (hlead μ hμ)
  have hone : ∀ (t : {t : Multiplicative X →* Kˣ // t ^ N = 1}) (x : Multiplicative X),
      ‖(t.1 x : K)‖ = 1 := by
    intro t x
    have h1 : ‖(t.1 x : K)‖ ^ N = 1 := by
      rw [← norm_pow, ← Units.val_pow_eq_pow_val, TorsionFourier.apply_pow_eq_one t.2,
        Units.val_one, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h1
  haveI := Fintype.ofFinite {t : Multiplicative X →* Kˣ // t ^ N = 1}
  rw [finsum_eq_sum_of_fintype] at hsum
  obtain ⟨t, -, ht⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
    (t := (Finset.univ : Finset {t : Multiplicative X →* Kˣ // t ^ N = 1}))
    ⟨⟨1, one_pow N⟩, Finset.mem_univ _⟩
    (fun t => (((t.1 (Multiplicative.ofAdd z₀))⁻¹ : Kˣ) : K) *
      ∑' β, σ β * (t.1 (Multiplicative.ofAdd β) : K))
  refine ⟨t.1, t.2, ?_⟩
  rw [hsum, norm_mul, norm_pow, hN1, one_pow, one_mul, hclass, norm_mul,
    Units.val_inv_eq_inv_val, norm_inv, hone, inv_one, one_mul] at ht
  exact ht

end GlobalTheory
end

section

open scoped BigOperators

theorem _root_.GlobalTheory.T.cone_closure_arc_of_integral_image_reduction_alt : (∀ (F K J ι : Type) [Field F] [Field K] [Algebra F K] [Fintype J] [Finite ι] (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra F (A i)], (∀ i, Algebra.FiniteType F (A i)) → ∀ (w : ∀ i, J → A i) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J F) (d : ℕ), G.IsHomogeneous d → (∀ i, MvPolynomial.aeval (w i) G = 0) → MvPolynomial.aeval v G = 0) → ∃ (i : ι) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A i →+* FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ (∀ x : F, f (algebraMap F (A i) x) = algebraMap W (FractionRing W) (algebraMap K W (algebraMap F K x))) ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w i j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W) → (∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∃ (F : Type) (_ : Field F) (_ : CharZero F) (φ' : R →+* F), (∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ' r = n * x) ∧ ∀ (A : Type) [CommRing A] [Algebra ℚ A] (χ : R →+* A), (∀ r, φ r = 0 → χ r = 0) → ∃ χ' : F →+* A, χ'.comp φ' = χ) → ∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∀ (K J ι : Type) [Field K] [CharZero K] [Fintype J] [Finite ι] (ψ : R →+* K), (∀ r, φ r = 0 → ψ r = 0) → ∀ (A : ι → Type) [∀ i, CommRing (A i)] [∀ i, Algebra ℚ (A i)], (∀ i, Algebra.FiniteType ℚ (A i)) → ∀ (χ : ∀ i, R →+* A i), (∀ i r, φ r = 0 → χ i r = 0) → ∀ (w : ∀ i, J → A i) (v : J → K), v ≠ 0 → (∀ (G : MvPolynomial J R) (d : ℕ), G.IsHomogeneous d → (∀ i, MvPolynomial.eval₂ (χ i) (w i) G = 0) → MvPolynomial.eval₂ ψ v G = 0) → ∃ (i : ι) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Algebra K W) (f : A i →+* FractionRing W) (s : FractionRing W) (w' : J → W), IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ s ≠ 0 ∧ (∀ r : R, f (χ i r) = algebraMap W (FractionRing W) (algebraMap K W (ψ r))) ∧ ∀ j, algebraMap W (FractionRing W) (w' j) = s * f (w i j) ∧ w' j - algebraMap K W (v j) ∈ IsLocalRing.maximalIdeal W := by
  first | exact @GlobalTheory.cone_closure_arc_of_integral_image_reduction | exact GlobalTheory.cone_closure_arc_of_integral_image_reduction | (intros; apply GlobalTheory.cone_closure_arc_of_integral_image_reduction <;> assumption)
end

section

open scoped BigOperators

theorem _root_.GlobalTheory.T.exists_field_of_isIntegral_image' : ∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∃ (F : Type) (_ : Field F) (_ : CharZero F) (φ' : R →+* F), (∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ' r = n * x) ∧ ∀ (A : Type) [CommRing A] [Algebra ℚ A] (χ : R →+* A), (∀ r, φ r = 0 → χ r = 0) → ∃ χ' : F →+* A, χ'.comp φ' = χ := by
  first | exact @GlobalTheory.exists_field_of_isIntegral_image | exact GlobalTheory.exists_field_of_isIntegral_image | (intros; apply GlobalTheory.exists_field_of_isIntegral_image <;> assumption)
end
