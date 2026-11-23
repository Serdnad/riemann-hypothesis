module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2675
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenOfLocal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValuesDetOmegaDeltaUnitAffineOpens
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle644
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsPolarizationDescentOfQuasiIsogeny
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle851
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle854
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3390
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle013
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem HasExt.of_comp {W V T : Scheme.{0}} (g : W ⟶ V) (e : V ⟶ T) (B : Over W) [GrpObj B] (h : HasExt (g ≫ e) B) :
    HasExt g B := by
  obtain ⟨G, _, φ, hG, hφ⟩ := h
  exact ⟨(Over.pullback e).obj G, inferInstance, _, IsSemiAbelian.pullback _ _ hG,
    ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor e g hφ⟩

theorem HasExt.of_dense {W V U : Scheme.{0}} [AlgebraicGeometry.IsNoetherian V]
    (hV : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme V) (l : W ⟶ V) [IsOpenImmersion l] [IsDominant l] (j : V ⟶ U)
    (A : Over V) [GrpObj A] (hA : IsSemiAbelian A) (B : Over W) [GrpObj B] (κ : B.left ⟶ A.left)
    (hκ : IsGrpPullback B A l κ) (h : HasExt (l ≫ j) B) : HasExt j A := by
  obtain ⟨G, _, φ, hG, hφ⟩ := h
  letI : (Over.pullback j).Monoidal :=
    (Over.instBraidedPullback (f := j)).toMonoidal
  letI : GrpObj ((Over.pullback j).obj G) :=
    Functor.grpObjObj (F := Over.pullback j)
  have h2 := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor j l hφ
  obtain ⟨e, ⟨he, -⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.existsUnique_iso_of_extensions hV hA
    (IsSemiAbelian.pullback j G hG) hκ h2
  exact ⟨G, inferInstance, e.hom.left ≫ pullback.fst _ _, hG,
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G j)).congr (Category.id_comp _) rfl⟩

theorem etale_of_comp_bijective {B A R : Type} [CommRing B] [IsLocalRing B] [CommRing A] [IsLocalRing A]
    [CommRing R] [IsLocalRing R] (e : B →+* A) (he : Function.Bijective e) (φ : A →+* R)
    (h : IsEtaleCompletion (φ.comp e)) (h' : ((residue R).comp (φ.comp e)).FormallyUnramified) :
    IsEtaleCompletion φ ∧ ((residue R).comp φ).FormallyUnramified := by
  obtain ⟨h1, h2, h3⟩ := h
  let E := RingEquiv.ofBijective e he
  have hφ : φ = (φ.comp e).comp E.symm.toRingHom := by
    ext a
    exact congrArg φ (E.apply_symm_apply a).symm
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [hφ]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective E.symm.bijective) h1
  · rw [← h2, ← Ideal.map_map, IsLocalRing.map_maximalIdeal_of_surjective e he.2]
  · exact RingHom.Finite.of_comp_finite (f := e) h3
  · exact RingHom.FormallyUnramified.of_comp (f := e) h'

theorem etale_of_comp_openImmersion {S S' : Scheme.{0}} (i : S' ⟶ S) [IsOpenImmersion i] {R : Type} [CommRing R]
    [IsLocalRing R] (ξ' : Sp R ⟶ S') (ξ : Sp R ⟶ S) (hξ : ξ' ≫ i = ξ)
    (h : IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom)
    (h' : ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified) :
    IsEtaleCompletion (Scheme.stalkClosedPointTo ξ').hom ∧
      ((residue R).comp (Scheme.stalkClosedPointTo ξ').hom).FormallyUnramified := by
  subst hξ
  have hiso : IsIso (i.stalkMap (ξ' (IsLocalRing.closedPoint (CommRingCat.of R)))) :=
    (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
  have hb : Function.Bijective (i.stalkMap (ξ' (IsLocalRing.closedPoint (CommRingCat.of R)))).hom :=
    ConcreteCategory.bijective_of_isIso _
  rw [Scheme.stalkClosedPointTo_comp] at h h'
  exact etale_of_comp_bijective _ hb _ h h'

theorem generic_mem_of_flat {S : Scheme.{0}} {R : Type} [CommRing R] [IsLocalRing R] [IsDomain R] (ξ : Sp R ⟶ S)
    (h : (Scheme.stalkClosedPointTo ξ).hom.Flat) (U : S.Opens) (t : S) (ht : t ∈ U) (hs : t ⤳ ξ (closedPoint R))
    (z : Sp (FractionRing R)) : (jK R ≫ ξ) z ∈ U := by
  have hfl : Flat ξ := by
    rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of R) ξ]
    have : Flat (Spec.map (Scheme.stalkClosedPointTo ξ)) := (HasRingHomProperty.Spec_iff (P := @Flat)).2 h
    exact MorphismProperty.comp_mem @Flat _ _ this (GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk _ _)
  obtain ⟨p, -, hp⟩ := Flat.generalizingMap ξ hs
  have hz : jK R z ⤳ p := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun a ha => ?_
    have ha' : algebraMap R (FractionRing R) a ∈ z.asIdeal := ha
    have := z.isPrime
    rw [Ideal.eq_bot_of_prime z.asIdeal, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective R _)] at ha'
    rw [ha']
    exact zero_mem _
  exact (hz.map ξ.continuous).mem_open U.isOpen (by rw [hp]; exact ht)

theorem Chart.nonempty_restrict {X S X' S' : Scheme.{0}} [IrreducibleSpace S'] [Nonempty X'] (j : X ⟶ S) [Mono j]
    (j' : X' ⟶ S') [IsOpenImmersion j'] (i : S' ⟶ S) [IsOpenImmersion i] (k : X' ⟶ X) (w : k ≫ j = j' ≫ i)
    (A : Over X) [GrpObj A] (x : S') (C : Chart j A (i x)) : Nonempty (Chart j' ((Over.pullback k).obj A) x) := by
  have h1 : Set.range C.ξ ⊆ Set.range i := by
    rintro _ ⟨y, rfl⟩
    exact (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of C.R) C.ξ (U := i.opensRange)
      ⟨x, C.centre.symm⟩).ge (Set.mem_univ y)
  let ξ' : Sp C.R ⟶ S' := IsOpenImmersion.lift i C.ξ h1
  have hξ : ξ' ≫ i = C.ξ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨he, hu⟩ := etale_of_comp_openImmersion i ξ' C.ξ hξ C.etc C.unr
  have hg : genericPoint S' ∈ j'.opensRange :=
    ((genericPoint_spec S').mem_open_set_iff j'.opensRange.isOpen).2 (by
      rw [Set.univ_inter]; exact Set.range_nonempty _)
  have h2 : Set.range (jK C.R ≫ ξ') ⊆ Set.range j' := by
    rintro _ ⟨z, rfl⟩
    exact generic_mem_of_flat ξ' he.1 j'.opensRange _ hg (genericPoint_specializes _) z
  let y' : Sp (FractionRing C.R) ⟶ X' := IsOpenImmersion.lift j' (jK C.R ≫ ξ') h2
  have hy' : y' ≫ j' = jK C.R ≫ ξ' := IsOpenImmersion.lift_fac _ _ _
  have hk : C.y = y' ≫ k := by
    rw [← cancel_mono j, Category.assoc, w, ← Category.assoc, hy', Category.assoc, hξ, C.hy]
  refine ⟨{ R := C.R, complete := C.complete, charZero := C.charZero, ξ := ξ', centre := ?_, etc := he, unr := hu,
            G := C.G, semi := C.semi, y := y', hy := hy', α := _,
            gen := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor k y' (C.gen.congr hk rfl) }⟩
  apply i.isOpenEmbedding.injective
  exact (congrArg (fun q => q (closedPoint C.R)) hξ).trans C.centre

theorem hasExt_opensRange (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S]
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (j : X ⟶ S) [IsOpenImmersion j] [IsDominant j]
    (A : Over X) [GrpObj A] (hA : IsAbelianScheme A) (L : LB A.left) (hL : L.IsLB) (hamp : RelAmple A L)
    (hC : ∀ x : S, Nonempty (Chart j A x)) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] (i : Sp R ⟶ S) [IsOpenImmersion i] :
    letI : (Over.pullback (j ⁻¹ᵁ i.opensRange).ι).Monoidal :=
      (Over.instBraidedPullback (f := (j ⁻¹ᵁ i.opensRange).ι)).toMonoidal
    @GlobalTheory.Desc.HasExt _ _ (j ∣_ i.opensRange) ((Over.pullback (j ⁻¹ᵁ i.opensRange).ι).obj A)
      (Functor.grpObjObj (F := Over.pullback (j ⁻¹ᵁ i.opensRange).ι)) := by
  letI : (Over.pullback (j ⁻¹ᵁ i.opensRange).ι).Monoidal :=
    (Over.instBraidedPullback (f := (j ⁻¹ᵁ i.opensRange).ι)).toMonoidal
  letI : GrpObj ((Over.pullback (j ⁻¹ᵁ i.opensRange).ι).obj A) :=
    Functor.grpObjObj (F := Over.pullback (j ⁻¹ᵁ i.opensRange).ι)
  obtain ⟨x₀, p, hp⟩ := j.denseRange.exists_mem_open i.opensRange.isOpen (Set.range_nonempty i)
  obtain ⟨_, ⟨f : R, rfl⟩, hpf, hf⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := p) (u := (i ⁻¹ᵁ j.opensRange).1) ⟨x₀, hp.symm⟩ (i ⁻¹ᵁ j.opensRange).isOpen
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hpf (zero_mem _)
  have hrange : Set.range (awayMap f) = (PrimeSpectrum.basicOpen f).1 :=
    PrimeSpectrum.localization_away_comap_range (Localization.Away f) f
  have : IsOpenImmersion (awayMap f) := IsOpenImmersion.of_isLocalization f
  have hne : Nonempty (Sp (Localization.Away f)) := by
    obtain ⟨q, -⟩ : p ∈ Set.range (awayMap f) := hrange ▸ hpf
    exact ⟨q⟩
  have h1 : Set.range (awayMap f ≫ i) ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    exact hf (hrange.le (Set.mem_range_self z))
  let k : Sp (Localization.Away f) ⟶ X := IsOpenImmersion.lift j (awayMap f ≫ i) h1
  have hk : k ≫ j = awayMap f ≫ i := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (k ≫ j) := by rw [hk]; infer_instance
  have : IsOpenImmersion k := IsOpenImmersion.of_comp k j
  have hL' := pull_isLB hL (pullback.fst A.hom k)
  obtain ⟨u, hu⟩ := GlobalTheory.lbIso_refl hL'
  letI : (Over.pullback k).Monoidal :=
    (Over.instBraidedPullback (f := k)).toMonoidal
  letI : GrpObj ((Over.pullback k).obj A) :=
    Functor.grpObjObj (F := Over.pullback k)
  have hext : HasExt (awayMap f) ((Over.pullback k).obj A) :=
    GlobalTheory.T.extendsToSemiAbelian_away_of_charts R f hf0 _ (isAbelianScheme_pullback_obj k A hA) (L.pull (pullback.fst A.hom k)) hL'
      (relAmple_pull (isGrpPullback_pullback A k).1 hL hL' ((isGen_iff u).1 hu) k.opensRange
        (isAffineOpen_opensRange k) (fun y => ⟨y, rfl⟩) hamp)
      fun x => (hC (i x)).elim fun C => Chart.nonempty_restrict j (awayMap f) i k hk A x C
  have h2 : Set.range k ⊆ Set.range (j ⁻¹ᵁ i.opensRange).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact ⟨awayMap f z, (congrArg (fun q => q z) hk).symm⟩
  let l : Sp (Localization.Away f) ⟶ (j ⁻¹ᵁ i.opensRange).toScheme := IsOpenImmersion.lift _ k h2
  have hl : l ≫ (j ⁻¹ᵁ i.opensRange).ι = k := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (l ≫ (j ⁻¹ᵁ i.opensRange).ι) := by rw [hl]; infer_instance
  have : IsOpenImmersion l := IsOpenImmersion.of_comp l (j ⁻¹ᵁ i.opensRange).ι
  have hcomp : l ≫ (j ∣_ i.opensRange) ≫ i.isoOpensRange.inv = awayMap f := by
    rw [← cancel_mono i, Category.assoc, Category.assoc, i.isoOpensRange_inv_comp, morphismRestrict_ι, ← Category.assoc,
      hl, hk]
  have : IsDominant l := by
    have hd : Dense (Set.range (awayMap f)) :=
      (awayMap f).isOpenEmbedding.isOpen_range.dense (Set.range_nonempty _)
    have hg := ((j ∣_ i.opensRange) ≫ i.isoOpensRange.inv).isOpenEmbedding
    refine ⟨(hd.preimage hg.isOpenMap).mono ?_⟩
    rintro y ⟨z, hz⟩
    exact ⟨z, hg.injective ((congrArg (fun q => q z) hcomp).trans hz)⟩
  have := GlobalTheory.IsNormalScheme.of_pred hS
  have : IsLocallyNoetherian (j ⁻¹ᵁ i.opensRange).toScheme :=
    isLocallyNoetherian_of_isOpenImmersion ((j ⁻¹ᵁ i.opensRange).ι ≫ j)
  have : TopologicalSpace.NoetherianSpace (j ⁻¹ᵁ i.opensRange).toScheme :=
    ((j ⁻¹ᵁ i.opensRange).ι ≫ j).isOpenEmbedding.isInducing.noetherianSpace
  have : AlgebraicGeometry.IsNoetherian (j ⁻¹ᵁ i.opensRange).toScheme := {}
  have : GlobalTheory.IsNormalScheme (j ⁻¹ᵁ i.opensRange).toScheme :=
    GlobalTheory.IsNormalScheme.of_isOpenImmersion ((j ⁻¹ᵁ i.opensRange).ι ≫ j)
  refine HasExt.of_dense (GlobalTheory.IsNormalScheme.pred _) l _ _
    (isSemiAbelian_of_isAbelianScheme _ (isAbelianScheme_pullback_obj _ A hA)) ((Over.pullback k).obj A) _
    (ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor _ l ((isGrpPullback_pullback A k).congr hl.symm rfl))
    (HasExt.of_comp _ i.isoOpensRange.inv _ ?_)
  rw [Category.assoc, hcomp]
  exact hext

theorem exists_hasExt_near : ∀ (X S : Scheme.{0}) [AlgebraicGeometry.IsNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (j : X ⟶ S) [IsOpenImmersion j], IsDominant j → ∀ (A : Over X) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → (∀ x : S, Nonempty (Chart j A x)) →
    ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
      (letI : (Over.pullback (j ⁻¹ᵁ U).ι).Monoidal :=
        (Over.instBraidedPullback (f := (j ⁻¹ᵁ U).ι)).toMonoidal
      @GlobalTheory.Desc.HasExt _ _ (j ∣_ U) ((Over.pullback (j ⁻¹ᵁ U).ι).obj A)
        (Functor.grpObjObj (F := Over.pullback (j ⁻¹ᵁ U).ι))) := by
  intro X S _ hS j _ hj A _ hA L hL hamp hC s
  have := GlobalTheory.IsNormalScheme.of_pred hS
  let Z : S.Opens := GlobalTheory.IsNormalScheme.component ⟨_, irreducibleComponent_mem_irreducibleComponents s⟩
  obtain ⟨U, hU, hs, hle⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := Z) (x := s) mem_irreducibleComponent
  have : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace
    ⟨⟨s, hs⟩, isIrreducible_irreducibleComponent.2.open_subset U.isOpen hle⟩
  have : IsIntegral U.toScheme := GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace _
  have : IsIntegral (Spec Γ(S, U)) := IsIntegral.of_isIso hU.isoSpec.hom
  have : IsDomain Γ(S, U) := (affine_isIntegral_iff _).1 this
  have : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsIntegrallyClosed Γ(S, U) := GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hU
  let i : Sp Γ(S, U) ⟶ S := hU.fromSpec
  have : IsOpenImmersion i := inferInstanceAs (IsOpenImmersion hU.fromSpec)
  refine ⟨i.opensRange, ?_, hasExt_opensRange X S hS j A hA L hL hamp hC Γ(S, U) i⟩
  exact hU.range_fromSpec.ge hs

end GlobalTheory.Desc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.KerKilledFibreOpen

theorem eq_one_of_local {S' : Scheme.{0}} {G : Over S'} [GrpObj G] (T : Over S') (x : T ⟶ G)
    (h : ∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      (Over.homMk U.ι : Over.mk (U.ι ≫ T.hom) ⟶ T) ≫ x = 1) : x = 1 := by
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun p => ?_
  obtain ⟨U, hp, hx⟩ := h p
  refine ⟨U, hp, ?_⟩
  have h1 : (Over.homMk U.ι : Over.mk (U.ι ≫ T.hom) ⟶ T) ≫ (1 : T ⟶ G) = 1 := MonObj.comp_one _
  rw [← h1] at hx
  exact congrArg (fun q => q.left) hx

theorem unit_residue : ∀ (S' : Scheme.{0}) (W : S'.Opens) (s : S'), s ∈ W → ∀ d : ℕ, IsUnit ((d : ℕ) : Γ(W.toScheme, ⊤)) → IsUnit ((d : ℕ) : S'.residueField s) := by
  intro S' W s hs d hd
  let x : W.toScheme := ⟨s, hs⟩
  have h1 : IsUnit ((d : ℕ) : W.toScheme.residueField x) := by
    have := hd.map (W.toScheme.evaluation ⊤ x trivial).hom
    simpa using this
  have hx : W.ι.base x = s := rfl
  rw [isUnit_iff_ne_zero] at h1 ⊢
  intro h0
  apply h1
  have := congrArg (Scheme.Hom.residueFieldMap W.ι x).hom (hx ▸ h0 : ((d : ℕ) : S'.residueField (W.ι.base x)) = 0)
  simpa using this


open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison GlobalTheory.KerKilledLocal in
theorem kerKilledOn_of_global : ∀ (d : ℕ) (S' : Scheme.{0}) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (V : S'.Opens), (∀ (T : Over S') (x : T ⟶ G), Set.range T.hom.base ⊆ (V : Set S') → (∃ c : (P.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, c.IsGen) → x ^ d = 1) → GlobalTheory.KerKilledLocus.KerKilledOn d G P V := by
  intro d S' G _ _ P V h T x hs
  apply down_injective G V
  rw [down_pow, down_one]
  let T' : Over S' := Over.mk (T.hom ≫ V.ι)
  let GV := (Over.pullback V.ι).obj G
  have hr : Set.range T'.hom.base ⊆ (V : Set S') := by
    rintro _ ⟨t, rfl⟩
    have h' : T'.hom.base t ∈ Set.range V.ι.base := ⟨T.hom.base t, rfl⟩
    rwa [Scheme.Opens.range_ι] at h'
  refine h T' (down G V x) hr ?_
  let Y : Over V.toScheme := Over.mk ((snd G T').left ≫ T.hom)
  have w1 : (fst G T').left ≫ G.hom = (G ⊗ T').hom := Over.w (fst G T')
  have w2 : (snd G T').left ≫ (T.hom ≫ V.ι) = (G ⊗ T').hom := Over.w (snd G T')
  let u : Y ⟶ GV := Over.homMk (pullback.lift (fst G T').left ((snd G T').left ≫ T.hom) (by
      rw [w1, Category.assoc, w2])) (pullback.lift_snd _ _ _)
  let v : Y ⟶ T := Over.homMk (snd G T').left rfl
  have heq : (lift u v).left ≫ (lift (snd GV T ≫ x) (fst GV T)).left ≫ pφ₂ V.ι G =
      (lift (snd G T' ≫ down G V x) (fst G T')).left ≫ 𝟙 _ := by
    rw [Category.comp_id]
    apply adelic_GL2_ext_of_local_components G
    · simp only [Category.assoc, pφ₂_fst]
      rw [lift_left_fst'_assoc, lift_left_fst']
      simp only [Over.comp_left, Category.assoc]
      rw [lift_left_snd'_assoc]
      rfl
    · simp only [Category.assoc, pφ₂_snd]
      rw [lift_left_snd'_assoc, lift_left_snd', lift_left_fst'_assoc]
      change pullback.lift _ _ _ ≫ pullback.fst G.hom V.ι = _
      rw [pullback.lift_fst]
  obtain ⟨t, ht⟩ := gen_pull3 P (pφ₂ V.ι G) _ (lift u v).left _ (𝟙 _) heq hs
  exact gen_chartPull (chartPullUnpull _ _ rfl) t ht

theorem comp_pow_overScheme_grpObj {S' : Scheme.{0}} {G T T' : Over S'} [GrpObj G] (u : T' ⟶ T) (x : T ⟶ G) :
    ∀ n : ℕ, u ≫ x ^ n = (u ≫ x) ^ n
  | 0 => by rw [pow_zero, pow_zero, MonObj.comp_one]
  | n + 1 => by rw [pow_succ, pow_succ, MonObj.comp_mul, comp_pow_overScheme_grpObj u x n]

theorem kerKilledOn_near_of_fibre : ∀ (d : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → ∀ W : S'.Opens, (∀ V : S'.Opens, V ≤ W → Out.RelAmple ((Over.pullback V.ι).obj G) ((P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)).pull (lift (𝟙 ((Over.pullback V.ι).obj G)) (𝟙 ((Over.pullback V.ι).obj G))).left)) → IsUnit ((d : ℕ) : Γ(W.toScheme, ⊤)) → ∀ s ∈ W, GlobalTheory.KerKilledNear.FibreKilled d G P s → ∃ V : S'.Opens, s ∈ V ∧ GlobalTheory.KerKilledLocus.KerKilledOn d G P V := by
  intro d S' _ G _ _ P hA hP hg₁ hg₂ hsym W hamp hd s hs hfib
  obtain ⟨V₀, Z, i, hs₀, hmono, hfin, h1, hmul, hinv, hfac, hloc⟩ := GlobalTheory.T.exists_finite_kernel_near_diagonal_ample S' G P hA hP hg₁ hg₂ hsym W hamp s hs
  have hfibZ : ∀ (T : Over S') (z : T ⟶ Z), (∃ f : T.left ⟶ Spec (S'.residueField s),
      T.hom = f ≫ S'.fromSpecResidueField s) → (z ≫ i) ^ d = 1 := by
    rintro T z ⟨f, hf⟩
    have hT : Set.range T.hom.base ⊆ (V₀ : Set S') := by
      rintro _ ⟨p, rfl⟩
      have e : (f ≫ S'.fromSpecResidueField s).base p = s :=
        Set.mem_singleton_iff.mp (Scheme.range_fromSpecResidueField s ▸ Set.mem_range_self (f.base p))
      rw [hf, e]
      exact hs₀
    refine eq_one_of_local T _ fun p => ?_
    obtain ⟨U, hp, c, hc⟩ := hloc T z hT p
    refine ⟨U, hp, ?_⟩
    rw [comp_pow_overScheme_grpObj]
    exact hfib (Over.mk (U.ι ≫ T.hom)) _ ⟨U.ι ≫ f, by simp [hf]⟩ ⟨c, hc⟩
  obtain ⟨V, hsV, hVV₀, hV⟩ := GlobalTheory.T.finite_subgroup_killed_near_point_of_fibre S' G Z i V₀ d s hmono hs₀ hfin h1 hmul hinv (unit_residue S' W s hs d hd) hfibZ
  refine ⟨V, hsV, kerKilledOn_of_global d S' G P V fun T x hT hx => ?_⟩
  obtain ⟨z, rfl⟩ := hfac T x (hT.trans hVV₀) hx
  exact hV T z hT

end GlobalTheory.KerKilledFibreOpen
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.thetaKeyValues_detOmega_delta_local_units : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ → KeyLoc κ →
  ∀ (S : Scheme.{0}) [IsIntegral S] (s : S ⟶ Sp ℤ) (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → LocallyOfFiniteType s →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → UnifAlong G L.L → NzFib σ →
    ∃ f : (VB.det (LieVB.omega G) g).ι → δ.ι → S.presheaf.stalk (genericPoint S),
      (∀ c i, ∀ x ∈ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i, ∃ (V : S.Opens) (_ : V ≤ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i)
        (_ : x ∈ V) (u : Γ(S, V)ˣ), ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f c i) ∧
      (∀ c c' i i' (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
        (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i'),
        f c i * S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) ^ 8 =
          S.presheaf.germ _ (genericPoint S) h1
            ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) ^ 4 * f c' i') := by
  first | exact @GlobalTheory.KeyValsPf.keyVals | exact GlobalTheory.KeyValsPf.keyVals | (intros; apply GlobalTheory.KeyValsPf.keyVals <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.keyValues_detOmega_delta_unit_affineOpens : ∀ κ : Rule, Homog (fun _ => 1) κ → Funct κ →
  ∀ (S : Scheme.{0}) [IsIntegral S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec), 1 ≤ g → Geo.Tor.IsNormalScheme S → IsLocallyNoetherian S →
    CharZero Γ(S, ⊤) → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → (abLocus G).Nonempty → IsOpen (abLocus G) →
    L.IsSymmetric → δ.IsLB → PolOnAb G L.L → NzFib σ →
    (∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (ξ : Sp A ⟶ S),
      IsOpenImmersion ξ → ∀ [IsCommMonObj ((Over.pullback ξ).obj G)] (L' : RigLB ((Over.pullback ξ).obj G)) (σ' : L'.L.Sec)
      (x : KeyIn (FractionRing A)) (y : Fin x.P.g → (epsR A ⟶ (Over.pullback ξ).obj G)),
      LBIso (L.L.pull (pullback.fst G.hom ξ)) L'.L → SmoothOfRelativeDimension x.P.g ((Over.pullback ξ).obj G).hom →
      IsOpen (abLocus ((Over.pullback ξ).obj G)) → L'.IsSymmetric → PolOnAb ((Over.pullback ξ).obj G) L'.L →
      IsLieBasis y → NzFib σ' → KeyOn (algebraMap A (FractionRing A)) x ((Over.pullback ξ).obj G) L' σ' y →
      ∃ u : Aˣ, (κ (FractionRing A) x : FractionRing A) = algebraMap A (FractionRing A) u) →
    ∃ f : (VB.det (LieVB.omega G) g).ι → δ.ι → S.presheaf.stalk (genericPoint S),
      (∀ c i, ∀ x ∈ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i, ∃ (V : S.Opens) (_ : V ≤ (VB.det (LieVB.omega G) g).U c ⊓ δ.U i)
        (_ : x ∈ V) (u : Γ(S, V)ˣ), ∀ h : genericPoint S ∈ V, S.presheaf.germ V (genericPoint S) h (u : Γ(S, V)) = f c i) ∧
      (∀ c c' i i' (h1 : genericPoint S ∈ (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')
        (h2 : genericPoint S ∈ δ.U i ⊓ δ.U i'),
        f c i * S.presheaf.germ _ (genericPoint S) h2 (δ.g i i' : Γ(S, δ.U i ⊓ δ.U i')) ^ 8 =
          S.presheaf.germ _ (genericPoint S) h1
            ((VB.det (LieVB.omega G) g).g c c' : Γ(S, (VB.det (LieVB.omega G) g).U c ⊓ (VB.det (LieVB.omega G) g).U c')) ^ 4 * f c' i') := by
  first | exact @GlobalTheory.KeyValsGen.keyVals | exact GlobalTheory.KeyValsGen.keyVals | (intros; apply GlobalTheory.KeyValsGen.keyVals <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GSumInt

theorem mem_O_of_pow_eq_one {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z) (z : M.Z) {u : Ω} {k : ℕ} (hk : 0 < k) (hu : u ^ k = 1) :
    u ∈ M.O z := by
  haveI := RatModel.isIntegrallyClosed_O hn z
  have hint : IsIntegral (M.O z) u :=
    ⟨_, Polynomial.monic_X_pow_sub_C (1 : M.O z) hk.ne', by simp [hu]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [← hy]
  exact y.2


variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} in
theorem base_mem (X₁ : Setup F W i) (z₁ : X₁.M.Z) : GSum.base X₁ z₁ ∈ X₁.S.supI X₁.M z₁ := by
  have h : (X₁.S.supI X₁.M z₁).Nonempty := by
    obtain ⟨x, hx⟩ := X₁.div z₁
    exact ⟨x, hx⟩
  rw [GSum.base, dite_eq_left h]
  exact h.some_mem

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (z₁ : X₁.M.Z) (x : D.X.S.Gam) (j : D.X.S.J) (z' : D.X.M.Z), D.q z' = z₁ → D.X.S.ev x j / D.X.S.th (D.lab (GSum.base X₁ z₁)) ∈ D.X.M.O z' := by
  intro g n F W Z i X₁ hg hn ho himm he8 hth hproj ε₁ hε D z₁ x j z' hz'
  obtain ⟨y, u, k, hk, hu, he⟩ := GlobalTheory.T.theta_system_value_eq_root_mul_theta_constant _ _ D.X.S D.X.ρ x j
  have hd := GlobalTheory.T.thetaSetup_dividingLabel_persists_deeperLevel g n F W Z i X₁ hg hn ho himm he8 hth hproj ε₁ hε D z₁ _ (base_mem X₁ z₁) z' hz'
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme D.X.M.Z := fun z => by
    haveI := D.X.normal
    exact ⟨D.X.normal.isDomain_stalk z, GlobalTheory.IsNormalScheme.isIntegrallyClosed_stalk z⟩
  rw [he, mul_div_assoc]
  exact mul_mem (mem_O_of_pow_eq_one D.X.M hN z' hk hu) (hd.2 y)

end GlobalTheory.Poinc.GSumInt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_polarization_descent_of_quasi_isogeny : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → PolKerAt o ψ' c (𝟙 Y) → ∃ P' : LB (G2 B).left, IsAxesTriv B P' ∧ LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) ∧ LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) := by
  first | exact @UpperTheory.Cb.exists_polarization_descent_of_quasi_isogeny | exact UpperTheory.Cb.exists_polarization_descent_of_quasi_isogeny
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.harrisTaylor_crystal_action_adjoint : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (c : D.O) x y, φ (GlobalTheory.HTCount.crysAct o₀ c x) y = φ x (GlobalTheory.HTCount.crysAct o₀ (D.star c).unop y) := by
  first | (exact @GlobalTheory.HTCount.crysAct_adjoint) | (exact GlobalTheory.HTCount.crysAct_adjoint) | (intros; apply GlobalTheory.HTCount.crysAct_adjoint  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct

theorem _root_.GlobalTheory.T.harrisTaylor_lie_condition_mod_hodgeFiltration : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C₀ : Type) [CommRing C₀] [IsLocalRing C₀] (β : R →+* C₀) (s : Sp C₀ ⟶ Sp R), s = spMap β → ∀ (o₀ : GlobalTheory.UPel.HT.Obj b N s) (y : HdR o₀.A), GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O D.ω) y - β b.ρ • y ∈ Fil o₀.A → ∃ w : Fin D.a → HdR o₀.A, (∀ i (c : 𝓞 D.F), GlobalTheory.HTSummand.crysAct (dp0 C₀) (𝟙 _) o₀.act (algebraMap (𝓞 D.F) D.O c) (w i) - β (b.t i c) • w i ∈ Fil o₀.A) ∧ y - ∑ i, w i ∈ Fil o₀.A := by
  first | (exact @GlobalTheory.HTSummand.lie_mod_fil) | (exact GlobalTheory.HTSummand.lie_mod_fil) | (intros; apply GlobalTheory.HTSummand.lie_mod_fil  <;> assumption)
end
