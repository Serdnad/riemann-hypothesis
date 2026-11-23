module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle021
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivBasicOpenOfTrivFibre
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle102
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FlatKernelPolarisationCosetsOverDVR
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle048
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle057
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle034
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphism
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle106
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle015
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle100
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle093
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle088
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle006
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBundleIsoExtendingGeneric
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIntegralFamiliesSpanPullDegeneration
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.StabFlatLocal
open GlobalTheory.CechPic GlobalTheory.StabFlat

theorem exists_ideal (hG : GlobalFnsSt) {V : Type} [CommRing V] [IsNoetherianRing V] [IsLocalRing V]
    (B : Over (Spec (CommRingCat.of V))) [GrpObj B]
    [IsCommMonObj B] (hB : IsAbelianScheme B) (hp : IsProjBy B.hom) {g : ℕ} (hg : SmoothOfRelativeDimension g B.hom)
    {L O : LB B.left} (hL : L.IsLB) (hO : O.IsLB) (hΘ : ∃ t : LB.Gen (Theta B L), t.IsGen)
    (hu : ∃ u : LB.Gen (abelian₂ B O), u.IsGen) {H : Over (Spec (CommRingCat.of V))} (j : H ⟶ B)
    (hH : ∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ B), (∀ p : T.left, ∃ U : T.left.Opens, p ∈ U ∧
      Triv ((LB.div (translDiff B L x) (O.pull (snd T B).left)).pull ((fst T B).left ⁻¹ᵁ U).ι)) ↔
        ∃ y : T ⟶ H, y ≫ j = x)
    (A : Type) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (a : Spec (CommRingCat.of A) ⟶ B.left)
    (σ : V →+* A) (hσ : IsLocalHom σ) (h₁ : σ.Flat)
    (h₂ : IsRegularLocalRing (A ⧸ (IsLocalRing.maximalIdeal V).map σ))
    (h₃ : ringKrullDim (A ⧸ (IsLocalRing.maximalIdeal V).map σ) = g)
    (K₀ : Type) [Field K₀] (g₀ : A →+* K₀) (hg₀ : IsLocalHom g₀)
    (h₀ : ∃ y : Spec (CommRingCat.of K₀) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom g₀) ≫ a)
    (hE : ∀ (K : Type) [Field K] (φ : A →+* K), (IsLocalRing.maximalIdeal V).map σ ≤ RingHom.ker φ →
      (∃ y : Spec (CommRingCat.of K) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) →
      RingHom.ker φ = IsLocalRing.maximalIdeal A) :
    ∃ I : Ideal A, ((Ideal.Quotient.mk I).comp σ).Flat ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R),
      (∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) ↔
        I ≤ RingHom.ker φ := by
  let t := a ≫ B.hom
  obtain ⟨F, hF, hΛ, hcl⟩ := exists_family hL hO hΘ hu t (Over.homMk a rfl)
  let B' := (Over.pullback t).obj B
  have hB' : IsAbelianScheme B' := TLinPf.isAb_pullback t B hB
  have hpb : IsPullback (pullback.fst B.hom t) B'.hom B.hom t := IsPullback.of_hasPullback _ _
  have hp' : IsProjBy B'.hom := isProjBy_baseChange hp hpb
  have hg' : SmoothOfRelativeDimension g B'.hom := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange g
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) hpb hg
  have test : ∀ (R : Type) [CommRing R] [IsLocalRing R] (φ : A →+* R) (X' : Scheme.{0}) (π : X' ⟶ B'.left)
      (f' : X' ⟶ Spec (CommRingCat.of R)), IsPullback π f' B'.hom (Spec.map (CommRingCat.ofHom φ)) →
      (Triv (F.pull π) ↔
        ∃ y : Spec (CommRingCat.of R) ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom φ) ≫ a) := by
    intro R _ _ φ X' π f' h
    let T : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ t)
    let x : T ⟶ B := Over.homMk (Spec.map (CommRingCat.ofHom φ) ≫ a) (Category.assoc _ _ _)
    have hM : (LB.div (translDiff B L x) (O.pull (snd T B).left)).IsLB :=
      LB.isLB_div (LB.isLB_linComb hL _ _) (pull_isLB hO _)
    have q : IsPullback f' (π ≫ pullback.fst B.hom t) T.hom B.hom := (h.paste_horiz hpb).flip
    let W : Over (Spec (CommRingCat.of V)) := Over.mk (f' ≫ T.hom)
    let e : W ⟶ T ⊗ B := Over.homMk q.isoPullback.hom (by
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ T.hom = f' ≫ T.hom
      rw [IsPullback.isoPullback_hom_fst_assoc])
    have : IsIso e.left := inferInstanceAs (IsIso q.isoPullback.hom)
    have c₁ : CechPic.pull π (cls F hF) = CechPic.pull e.left (cls _ hM) := by
      rw [cls_eq_dcl hL hO, pull_dcl]
      refine hcl W π _ _ ?_ q.isoPullback_hom_snd
      show q.isoPullback.hom ≫ pullback.fst T.hom B.hom ≫ Spec.map (CommRingCat.ofHom φ) ≫ a =
        π ≫ B'.hom ≫ a
      rw [IsPullback.isoPullback_hom_fst_assoc, h.w_assoc]
    refine (cls_eq_zero_iff (pull_isLB hF π)).symm.trans ?_
    rw [cls_pull hF, c₁, pull_iso_eq_zero]
    refine ((loc_triv_iff (R := R) (fst T B).left hM).symm.trans (hH T x)).trans ⟨?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact ⟨y.left, congrArg (·.left) hy⟩
    · rintro ⟨y, hy⟩
      refine ⟨Over.homMk y ?_, Over.OverMorphism.ext hy⟩
      rw [← Over.w j, ← Category.assoc, hy]
      exact Category.assoc _ _ _
  obtain ⟨P⟩ := GlobalTheory.AbLaw.nonempty_perf_of_smooth_isProjBy A _ B'.hom hB'.smooth hp' F hF
  have := hB'.proper
  have := hB'.geomConnected
  have q₀ := IsPullback.of_hasPullback B'.hom (Spec.map (CommRingCat.ofHom g₀))
  obtain ⟨I, ⟨eI⟩, hI⟩ := GlobalTheory.UU.SecCyclic.cyclic_ideal A _ B'.hom F hF P inferInstance inferInstance K₀ g₀ hg₀ _ _ _
    q₀ (CubeOpen.bijective_appTop hG B' hB' q₀) ((test K₀ g₀ _ _ _ q₀).2 h₀)
  obtain ⟨C, c₁, c₂, ⟨eC⟩, c₃⟩ := GlobalTheory.T.exists_perfect_free_finite_complex A B' hB' hp' g hg' F hF hΛ P
  refine ⟨I, ?_, fun R _ _ φ => (test R φ _ _ _ (IsPullback.of_hasPullback _ _)).symm.trans
    (hI R φ _ _ _ (IsPullback.of_hasPullback _ _))⟩
  letI : Algebra V A := σ.toAlgebra
  haveI : IsLocalHom (algebraMap V A) := hσ
  haveI : Module.Flat V A := h₁
  have key : Module.Flat V (A ⧸ I) → ((Ideal.Quotient.mk I).comp σ).Flat := fun h =>
    RingHom.flat_algebraMap_iff.2 h
  refine key (GlobalTheory.T.flat_quotient_of_equiv_coker_dualMap_of_exact_fibres_alt V A g h₂ h₃ C c₁ c₂ (fun p hϖ => ?_) I ⟨eC.trans eI⟩)
  let K := AlgebraicClosure p.asIdeal.ResidueField
  let φ : A →+* K := (algebraMap p.asIdeal.ResidueField K).comp (algebraMap A p.asIdeal.ResidueField)
  have hk : RingHom.ker φ = p.asIdeal := by
    rw [RingHom.ker_comp_of_injective _ (algebraMap p.asIdeal.ResidueField K).injective,
      Ideal.ker_algebraMap_residueField]
  refine ⟨K, inferInstance, φ, hk, fun i hi => c₃ K φ _ _ _ (IsPullback.of_hasPullback _ _) i ?_⟩
  rcases hi with hi | hi
  · refine Or.inr fun ht => hi (hk.symm.trans (hE K φ ?_ ((test K φ _ _ _ (IsPullback.of_hasPullback _ _)).1 ht)))
    exact hϖ.trans hk.ge
  · exact Or.inl hi

theorem flat_of_isFinite : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsNoetherianRing V] [IsLocalRing V] (B : Over (Sp V)) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ L : LB B.left, L.IsLB → (∃ t : LB.Gen (Theta B L), t.IsGen) → ∀ (H : Over (Sp V)) (j : H ⟶ B), IsClosedImmersion j.left → (∀ (T : Over (Sp V)) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) → IsFinite H.hom → Flat H.hom := by
  intro hG V _ _ _ B _ _ hB hp L hL hΘ H j hj hH hf
  obtain ⟨hO, hu, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L hL
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim V B hB
  rw [← Over.w j]
  refine GlobalTheory.T.flat_closedSubscheme_finite_over_localRing V B.left H.left B.hom j.left hj (by rw [Over.w j]; exact hf) fun h σ hσ hn => ?_
  have cl : ∀ (z : H.left) (p : Spec (B.left.presheaf.stalk (j.left h))),
      (IsLocalRing.maximalIdeal V).map σ ≤ p.asIdeal →
      j.left z = B.left.fromSpecStalk (j.left h) p → IsClosed ({j.left z} : Set B.left) := by
    intro z p hp e
    have hz : H.hom z = IsLocalRing.closedPoint V := by
      rw [← Over.w j, Scheme.Hom.comp_apply, e, ← Scheme.Hom.comp_apply, hσ]
      refine PrimeSpectrum.ext (Eq.symm ((IsLocalRing.maximalIdeal.isMaximal V).eq_of_le
        (PrimeSpectrum.isPrime _).ne_top ?_))
      exact Ideal.map_le_iff_le_comap.1 hp
    have := j.left.isClosedEmbedding.isClosedMap _ (isClosed_of_isFinite H.hom z hz)
    rwa [Set.image_singleton] at this
  have hm : (IsLocalRing.maximalIdeal V).map σ ≤ IsLocalRing.maximalIdeal _ :=
    Ideal.map_le_iff_le_comap.2 fun v hv => map_nonunit σ v hv
  obtain ⟨h₀, h₁, h₂, h₃⟩ := GlobalTheory.T.stalk_regular_flat_of_smooth V B.left B.hom g hg (j.left h)
    (cl h (IsLocalRing.closedPoint _) hm Scheme.fromSpecStalk_closedPoint.symm) σ hσ hn
  refine @exists_ideal hG V _ _ _ B _ _ hB hp g hg L (pw L 0) hL hO hΘ hu H j
    (fun T x => (hK _ rfl T x).symm.trans (hH T x))
    (B.left.presheaf.stalk (j.left h)) _ h₀ _
    (B.left.fromSpecStalk (j.left h)) σ hn h₁ h₂ h₃ (H.left.residueField h) _
    (j.left.stalkMap h ≫ H.left.residue h).hom
    (RingHom.isLocalHom_comp (IsLocalRing.residue (H.left.presheaf.stalk h)) (j.left.stalkMap h).hom) ⟨H.left.fromSpecResidueField h, ?_⟩ ?_
  · rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc]
    rfl
  · rintro K _ φ hφ ⟨y, hy⟩
    let p := Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint K)
    have hk : p.asIdeal = RingHom.ker φ := by
      show Ideal.comap φ (IsLocalRing.maximalIdeal K) = _
      rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]
    have e : j.left (y (IsLocalRing.closedPoint K)) = B.left.fromSpecStalk (j.left h) p :=
      congrArg (fun q => q (IsLocalRing.closedPoint K)) hy
    have hc := cl _ p (hφ.trans hk.ge) e
    have hs : B.left.fromSpecStalk (j.left h) p ⤳ j.left h := by
      have : B.left.fromSpecStalk (j.left h) p ∈ Set.range (B.left.fromSpecStalk (j.left h)) := ⟨p, rfl⟩
      rwa [Scheme.range_fromSpecStalk] at this
    have e' : j.left h = B.left.fromSpecStalk (j.left h) p := (hs.mem_closed hc e.symm).trans e
    have hp' : p = IsLocalRing.closedPoint _ := (B.left.fromSpecStalk (j.left h)).isEmbedding.injective
      (e'.symm.trans Scheme.fromSpecStalk_closedPoint.symm)
    rw [← hk, hp']
    rfl

end GlobalTheory.StabFlatLocal
end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_compatible_generatingSections_all_thickenings : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (Y : Over (Spec (CommRingCat.of R))) (H : LB Y.left) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), Smooth Y.hom → H.IsLB → VeryAmpleBy Y.hom H s → ∀ f : ∀ e, (thickObj R I e Y).left ⟶ Y.left, (∀ e, thickMap R I e Y ≫ f (e + 1) = f e) → ∃ (t : ℤ) (m : ℕ) (u : ∀ e, Fin (m + 1) → LB.Sec (LB.LinComb H (Y := (thickObj R I e Y).left) (K := Fin 2) ![pullback.fst Y.hom (thick R I e), f e] ![t, -1])), (⨆ i, nonzeroLocus (u 0 i) = ⊤) ∧ ∀ e i z J, Good H z J → sval (u (e + 1) i) (thickMap R I e Y) z J = sval (u e i) (𝟙 _) z J := by
  first | exact @GlobalTheory.SecTower.exists_tower | exact GlobalTheory.SecTower.exists_tower | (intros; apply GlobalTheory.SecTower.exists_tower <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.flat_kernelPolarisation_cosets_over_DVR : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (B : Over (Spec (CommRingCat.of V))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∀ (L : RigLB B) (_ : CubicalStr B L) (O : LB B.left), O.IsLB → (∃ u : LB.Gen (abelian₂ B O), u.IsGen) → ∀ (H : Over (Spec (CommRingCat.of V))) (j : H ⟶ B), IsClosedImmersion j.left → (∀ (T : Over (Spec (CommRingCat.of V))) (x : T ⟶ B), (∀ p : (T).left, ∃ U : (T).left.Opens, p ∈ U ∧ Triv ((LB.div (translDiff B L.L x) (O.pull (snd (T) B).left)).pull ((fst (T) B).left ⁻¹ᵁ U).ι)) ↔ ∃ y : T ⟶ H, y ≫ j = x) → IsFinite H.hom → Flat H.hom := by
  first | exact @GlobalTheory.StabFlat.flat_of_isFinite | exact GlobalTheory.StabFlat.flat_of_isFinite | (intros; apply GlobalTheory.StabFlat.flat_of_isFinite <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.ExpOnto

theorem exists_sec_comb {X : Scheme.{0}} {L : LB X} {n : ℕ} (r : Fin n → Γ(X, ⊤)) (b : Fin n → LB.Sec L) :
    ∃ t : LB.Sec L, ∀ j, t.f j = ∑ i, resTop _ (r i) * (b i).f j := by
  induction n with
  | zero => exact ⟨DVR.SecOps.secZero, fun j => by simp [DVR.SecOps.secZero]⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih (fun i => r i.succ) (fun i => b i.succ)
    refine ⟨DVR.SecOps.secAdd (DVR.SecOps.secScale (r 0) (b 0)) t, fun j => ?_⟩
    rw [Fin.sum_univ_succ, ← ht j]
    rfl

theorem fam_sum_f {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {k : ℕ} {K : Type} (S : Finset K) (s : K → Fam D F k) (α : D.X) (j) :
    ((∑ i ∈ S, s i).s α).f j = ∑ i ∈ S, ((s i).s α).f j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, DVR.add_f, ih]

theorem exists_expF_of_fam : Laws → Laws2 → AllPre fun {V} _ _ _ {D} {_} {_} _ _ U => D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → U.FE F k → ∀ s : Fam D F k, ∃ t, U.ExpF F k t s.s := by
  intro hL hL2 V _ _ _ hV D A G _ _ U hB F _ _ k hk hFE s
  obtain ⟨b, hb⟩ := GlobalTheory.PowBasis.exists_basis_pow_field hL2.secTwist V A F k hk
  choose e he using fun i => GlobalTheory.T.exists_fourierJacobi_expansion_over_field hL hL2 V hV D A G U F k hk (b i)
  let f : Fin (k ^ A.g) → Fam D F k := fun i => ⟨e i, hFE _ _ (he i)⟩
  have comb : ∀ c : Fin (k ^ A.g) → F, ∃ t, (∀ j, t.f j = ∑ i,
      liftFun A.A _ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i)) * (b i).f j) ∧
      U.ExpF F k t (∑ i, c i • f i).s := fun c => by
    obtain ⟨t, ht⟩ := exists_sec_comb (fun i => (fst (TFK (R := V) F) A.A).left.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i))) b
    refine ⟨t, ht, ExpLinC.expF_lincomb V hV D A G U F k _ c b e t _ he ht fun α j => ?_⟩
    exact fam_sum_f _ _ α j
  have hli : LinearIndependent F f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    obtain ⟨t, ht, hE⟩ := comb c
    obtain ⟨t', ht', hE'⟩ := comb 0
    have h0 : (∑ i, (0 : Fin (k ^ A.g) → F) i • f i) = ∑ i, c i • f i := by
      rw [hc]; simp
    have htt : t = t' := (GlobalTheory.T.fourierJacobiExpansion_overField_injective V hV D A G U F k t t' _ _ hE hE').2 (by rw [h0])
    subst htt
    exact congrFun ((hb t).unique ht ht')
  obtain ⟨hfin, hdim⟩ := finrank_fam_of_laws hL hL2 V D hB F k hk
  have hg : A.g = D.P.g + D.rank := PreU.dim_eq V hV D A G U
  have hsp := hli.span_eq_top_of_card_eq_finrank' (by rw [hdim, Fintype.card_fin, hg])
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 (hsp ▸ Submodule.mem_top (x := s))
  obtain ⟨t, -, hE⟩ := comb c
  exact ⟨t, hc ▸ hE⟩

end GlobalTheory.UU.ExpOnto

end
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

theorem _root_.GlobalTheory.T.torusTorsion_to_abelianTorsion_theta_action : Laws → Laws2 → (AllPre fun {V} _ _ _ {D} {A} {_} _ _ U => ∀ N : ℕ, 1 ≤ N → ∃ m : {g : GtPtF D (Kbar V) // GtTors D N g} → (TFK (R := V) (Kbar V) ⟶ A.A), Function.Injective m ∧ (∀ g, U.Acts (Kbar V) N 0 g.1 (m g)) ∧ ∀ g g' g'', GtPtF.IsAdd g.1 g'.1 g''.1 → m g'' = m g * m g') := by
  first | exact @GlobalTheory.UU.Eqv.main | exact GlobalTheory.UU.Eqv.main | (intros; apply GlobalTheory.UU.Eqv.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.PhiMul

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_frm_pow {D : DegPre R} {k : ℕ} {b : TF (R := R) F ⟶ D.P.A} (w : Frm D F k b) (hw : w.IsGen)
    (n N : ℕ) (hN : N = k * n) : ∃ w' : Frm D F N b, w'.IsGen ∧
      ∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (𝟙 _) z J ^ n := by
  obtain ⟨w', h₁, h₂⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε N)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      congr 1
      subst hN
      fin_cases i <;> simp [DegPre.lineε, mul_comm])
    (GeneratorPullback.powGen D.P.L _ _ w n) (powGen_isGen _ _ _ _ hw n)
  exact ⟨w', h₁, fun z J hJ => (h₂ _ _ z J hJ).trans (map_pow _ _ _)⟩


omit [IsDomain R] in
theorem exists_secA_mul {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {a b c : ℕ} (hc : c = a + b)
    (t : SecA A F a) (t' : SecA A F b) : ∃ u : SecA A F c,
      ∀ z J, Good A.L z J → sA u (𝟙 _) z J = sA t (𝟙 _) z J * sA t' (𝟙 _) z J := by
  obtain ⟨u, hu⟩ := exists_sec A.isLB (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left)
    (ε' := fun _ => (c : ℤ)) (fun U _ h => by
      subst hc
      simp [Fintype.prod_sum_type, zpow_add])
    (H1.SectionArithmetic.mulSec (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (a : ℤ))
      (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε' := fun _ => (b : ℤ)) t t')
  exact ⟨u, fun z J hJ => (hu _ _ z J hJ).trans (H1.SectionArithmetic.sval_mulSec _ _ _ z hJ)⟩

theorem phi_mul : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b), w.IsGen → ∀ (n : Fin 3 → ℕ) (N : Fin 3 → ℕ), (∀ i, 1 ≤ n i ∧ N i = k * n i) → n 2 = n 0 + n 1 → ∀ (q : ∀ i, QkPt D.toPre F (N i)) (ω : ∀ i, Frm D.toPre F (N i) (q i).g.b), (∀ i, (q i).y = n i • p.y ∧ (q i).g = p.g ∧ ((ω i).IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val (ω i) (𝟙 _) z J = val w (𝟙 _) z J ^ n i)) → ∀ (t t' : ∀ i, SecA A F (N i)) (s s' : ∀ i, Fam D.toPre F (N i)), (∀ i, U.ExpandsF F (N i) w₀ (t i) (s i) ∧ U.ExpandsF F (N i) w₀ (t' i) (s' i) ∧ PhiRel D.toPre F (N i) (q i) (ω i) (s i) (s' i)) → (∀ z J, Good A.L z J → sA (t 2) (𝟙 _) z J = sA (t 0) (𝟙 _) z J * sA (t 1) (𝟙 _) z J) → ∀ z J, Good A.L z J → sA (t' 2) (𝟙 _) z J = sA (t' 0) (𝟙 _) z J * sA (t' 1) (𝟙 _) z J := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ w₀ hw₀ k hk p w hw n N hn hn2 q ω hq t t' s s' hs ht
  have hN1 : ∀ i, 1 ≤ N i := fun i => by rw [(hn i).2]; exact Nat.mul_pos hk (hn i).1
  have hN2 : N 2 = N 0 + N 1 := by rw [(hn 0).2, (hn 1).2, (hn 2).2, hn2, mul_add]
  have hB := (expBijF_and_expandsF_lin hL R I hI D A G hG U).1 F (N 2) (hN1 2) w₀ hw₀
  obtain ⟨u, hu⟩ := exists_secA_mul hN2 (t' 0) (t' 1)
  obtain ⟨r, hr, -⟩ := hB.1 u
  have hrs : r = s' 2 := by
    refine CoefDet.fam_eq_of_coef_eq hL R I hI D F (N 2) r (s' 2) fun g₀ => ?_
    letI := GlobalTheory.TorusExt.gtGroup D.toPre F
    have hadd : g₀.IsAdd p.g (g₀ + p.g) := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl
    obtain ⟨ω₀, hω₀⟩ : ∃ ω₀ : Frm D.toPre F k g₀.b, ω₀.IsGen :=
      exists_gen_of_local (V := F) D.toPre.P.L D.toPre.P.isLB _ _
    obtain ⟨ω₁, hω₁, -, hφ⟩ := CoefPhi.coef_phi hL R I hI D F k hk p w hw g₀ _ hadd ω₀ hω₀
    choose a ha using fun i => exists_frm_pow ω₀ hω₀ (n i) (N i) (hn i).2
    choose b hb using fun i => exists_frm_pow ω₁ hω₁ (n i) (N i) (hn i).2
    have hc : ∀ i α, coef (s' i) g₀ (a i) (α + (q i).y) = coef (s i) (g₀ + p.g) (b i) α := fun i =>
      hφ (n i) (N i) (hn i).1 (hn i).2 (q i) (hq i).1 (hq i).2.1 (ω i) (a i) (b i) (hq i).2.2 (ha i) (hb i)
        (s i) (s' i) (hs i).2.2
    refine ⟨a 2, (ha 2).1, fun χ => ?_⟩
    have S₀ := GlobalTheory.T.product_of_sections_expands_to_convolution hL R I hI D A G hG U F w₀ hw₀ (N 0) (N 1) (N 2) (hN1 0) (hN1 1) hN2 (t' 0) (t' 1) u
      (s' 0) (s' 1) r (hs 0).2.1 (hs 1).2.1 hr hu g₀ (a 0) (a 1) (a 2) (ha 0).1 (ha 1).1 (ha 2).1
      (fun z J hJ => by rw [(ha 0).2 z J hJ, (ha 1).2 z J hJ, (ha 2).2 z J hJ, hn2, pow_add]) χ
    have S₁ := GlobalTheory.T.product_of_sections_expands_to_convolution hL R I hI D A G hG U F w₀ hw₀ (N 0) (N 1) (N 2) (hN1 0) (hN1 1) hN2 (t 0) (t 1) (t 2)
      (s 0) (s 1) (s 2) (hs 0).1 (hs 1).1 (hs 2).1 ht (g₀ + p.g) (b 0) (b 1) (b 2) (hb 0).1 (hb 1).1 (hb 2).1
      (fun z J hJ => by rw [(hb 0).2 z J hJ, (hb 1).2 z J hJ, (hb 2).2 z J hJ, hn2, pow_add]) (χ - (q 2).y)
    have hy : (q 2).y = (q 0).y + (q 1).y := by rw [(hq 0).1, (hq 1).1, (hq 2).1, hn2, add_smul]
    have S₂ := ((GlobalTheory.AdicSum.sumF_calculus R I hI F _ _ (fun _ => 0) _ 0).2.2 _ (fun ψ => ψ + (q 0).y)
      (add_left_injective _) (fun i hi => absurd ⟨i - (q 0).y, sub_add_cancel _ _⟩ hi)).2 S₀
    have e : ((fun ψ => coef (s' 0) g₀ (a 0) ψ * coef (s' 1) g₀ (a 1) (χ - ψ)) ∘ fun ψ => ψ + (q 0).y) =
        fun ψ => coef (s 0) (g₀ + p.g) (b 0) ψ * coef (s 1) (g₀ + p.g) (b 1) (χ - (q 2).y - ψ) := by
      funext ψ
      rw [← hc 0, ← hc 1, hy]
      have e' : χ - ((q 0).y + (q 1).y) - ψ + (q 1).y = χ - (ψ + (q 0).y) := by abel
      rw [e']
      rfl
    rw [e] at S₂
    rw [(GlobalTheory.AdicSum.sumF_calculus R I hI F _ _ (fun _ => 0) _ _).1 S₂ S₁, ← hc 2, sub_add_cancel]
  obtain rfl : u = t' 2 := (hB.2 (s' 2)).unique (hrs ▸ hr) (hs 2).2.1
  exact hu

end GlobalTheory.UT.PhiMul
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.unif_g_eq_rank_add_g : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => A.g = D.toPre.rank + D.toPre.P.g := by
  first | exact @GlobalTheory.UT.dim_eq_rank_add_dim | exact GlobalTheory.UT.dim_eq_rank_add_dim | (intros; apply GlobalTheory.UT.dim_eq_rank_add_dim <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

theorem _root_.GlobalTheory.T.expansion_pullback_section_endomorphism : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (E : EndU U.toUnifPre), Function.Injective E.h → ∀ (k' k : ℕ), 1 ≤ k → 1 ≤ k' → (∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![(k' : ℤ), -(k : ℤ)]), β.IsGen) → (∃ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ) ∧ ∀ (w₀ : W0 U.toUnifPre) (ρ), NormW U.toUnifPre w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') s s', U.ExpandsF F k w₀ t s → U.ExpandsF F k' w₀ t' s' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ → ∀ (g g' : GtPtF D.toPre F), E.Act g g' → ∀ (w' : Frm D.toPre F k' g.b) (w : Frm D.toPre F k g'.b), w'.IsGen → w.IsGen → (∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J * val κ g.b.left z J = val w (𝟙 _) z J) → (∀ χ, coef s' g w' (E.h χ) = coef s g' w χ) ∧ ∀ β, β ∉ Set.range E.h → coef s' g w' β = 0 := by
  first | exact @GlobalTheory.UT.PullExp.main | exact GlobalTheory.UT.PullExp.main | (intros; apply GlobalTheory.UT.PullExp.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_finite_closed_subscheme_represents_kernel_ample : GlobalFnsSt → ∀ (V : Type) [CommRing V] (B : Over (Sp V)) [GrpObj B], IsAbelianScheme B → ∀ L : LB B.left, L.IsLB → RelAmple B L → ∃ (H : Over (Sp V)) (j : H ⟶ B), IsClosedImmersion j.left ∧ IsFinite H.hom ∧ (∀ (T : Over (Sp V)) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) := by
  first | exact @GlobalTheory.KernelRep.exists_finite_closed_kernel | exact GlobalTheory.KernelRep.exists_finite_closed_kernel | (intros; apply GlobalTheory.KernelRep.exists_finite_closed_kernel <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.generic_iso_extends_semiAbelian_dvr_inducing_formal : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j e).hom.left) → ∀ (ΦK : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (wK : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (ΦK.hom.left ≫ pullback.fst G.hom (jK R)))), (wK.IsGen ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → (Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z jM (fun _ => jL) ^ k).val * gs (r ≫ (j e).hom.left ≫ (fstG I e G).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = ((Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL')) ^ k).val * gs (r ≫ (fstG I e G').left) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL → (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' → gs (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = (Geo.Tor.gw wK r z jL (fun _ => jL') ^ k).val * gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∃ ψ : G' ≅ G, (IsMonHom ψ.hom ∧ (Over.pullback (jK R)).map ψ.hom = ΦK.hom ∧ ∀ e : ℕ, (fstG I e G').left ≫ ψ.hom.left = (j e).hom.left ≫ (fstG I e G).left) := by
  first | exact @GlobalTheory.FormalExt.main | exact GlobalTheory.FormalExt.main | (intros; apply GlobalTheory.FormalExt.main <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_bundleIso_extending_generic_alt : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j e).hom.left) → ∀ (ΦK : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) (wK : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (ΦK.hom.left ≫ pullback.fst G.hom (jK R)))), (wK.IsGen ∧ ∀ (k : ℕ), 1 ≤ k → ∀ (σ' : H0 U'.LG.L k) (σ : H0 U.LG.L k), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → (Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z jM (fun _ => jL) ^ k).val * gs (r ≫ (j e).hom.left ≫ (fstG I e G).left) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = ((Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL')) ^ k).val * gs (r ≫ (fstG I e G').left) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left) (z : Z) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z ∈ U.LG.L.U jL → (r ≫ pullback.fst G'.hom (jK R)) z ∈ U'.LG.L.U jL' → gs (r ≫ ΦK.hom.left ≫ pullback.fst G.hom (jK R)) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL)) (σ.f (fun _ => jL)) = (Geo.Tor.gw wK r z jL (fun _ => jL') ^ k).val * gs (r ≫ pullback.fst G'.hom (jK R)) z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) (fun _ => jL')) (σ'.f (fun _ => jL'))) → ∀ ψ : G' ≅ G, (IsMonHom ψ.hom ∧ (Over.pullback (jK R)).map ψ.hom = ΦK.hom ∧ ∀ e : ℕ, (fstG I e G').left ≫ ψ.hom.left = (j e).hom.left ≫ (fstG I e G).left) → ∃ wL : LB.Iso U'.LG.L (U.LG.L.pull ψ.hom.left), wL.IsGen ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left ((j e).hom.left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ (j e).hom.left) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G').left) z jL jL' := by
  first | exact @GlobalTheory.exists_bundleIso_extending_generic | exact GlobalTheory.exists_bundleIso_extending_generic | (intros; apply GlobalTheory.exists_bundleIso_extending_generic <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.exists_integral_families_span_pullDegeneration : PolBaseChangeSt → GlobalFnsSt → DVR.TwistBaseChangeStatement → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R), AdmBase R I → ∀ (φ : R →+* R') (D : DegData R I) (D' : DegPre R') (hD : IsPullDeg φ D.toPre D') (k : ℕ), 1 ≤ k → ∃ (n : ℕ) (F : Fin n → Fam D.toPre (FractionRing R) k) (f : Fin n → ∀ α, D.toPre.SecB k α) (F' : Fin n → Fam D' (FractionRing R') k) (f' : Fin n → ∀ α, D'.SecB k α), (∀ i, (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) ((F i).s α) (D.toPre.famφB α) (DegPre.famε k) (f i α) (DegPre.prB D.toPre (FractionRing R)).left 1) ∧ (∀ α, GeneratorPullback.SecScal D'.P.L (DegPre.famφ D' (FractionRing R') α) (DegPre.famε k) ((F' i).s α) (D'.famφB α) (DegPre.famε k) (f' i α) (DegPre.prB D' (FractionRing R')).left 1) ∧ (∀ x : D'.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.P.A.left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((D'.famφB x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (D'.famφB x) κ (r z) ∈ D'.P.L.U (q κ)) → Geo.Tor.gs (r ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) z (LB.wchart D.toPre.P.L (D.toPre.famφB (hD.xe x)) p) ((f i (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (D'.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.P.L (D'.famφB x) q) ((f' i x).f q)))) ∧ Submodule.span (FractionRing R') (Set.range F') = ⊤ := by
  first | exact @GlobalTheory.FamSpan.exists_span | exact GlobalTheory.FamSpan.exists_span | (intros; apply GlobalTheory.FamSpan.exists_span <;> assumption)
end
