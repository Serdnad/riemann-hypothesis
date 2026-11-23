module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle074
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle037
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FinitenessStep
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.FormalFunctions
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ZariskiSplit
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle044
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OmegaLatticeDominantCompat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle016
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle024
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveCohomology.Bundle001
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.CompactGapsGE

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.SpecialFibreConnected

theorem mem_range_of_isIntegral {O Ω : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Field Ω]
    [Algebra O Ω] (hinj : Function.Injective (algebraMap O Ω)) (hc : ConstClosed O Ω) (a : Ω)
    (ha : IsIntegral O a) : ∃ o : O, algebraMap O Ω o = a := by
  obtain ⟨x, y, hy, e⟩ := hc a ha.isAlgebraic
  let ι : FractionRing O →ₐ[O] Ω :=
    { IsFractionRing.lift (K := FractionRing O) hinj with
      commutes' := fun o => IsFractionRing.lift_algebraMap hinj o }
  have hy' : algebraMap O Ω y ≠ 0 := fun h => hy (hinj (by rw [h, map_zero]))
  have e' : ι (algebraMap O (FractionRing O) x / algebraMap O (FractionRing O) y) = a := by
    rw [map_div₀, ι.commutes, ι.commutes, ← e, mul_div_cancel_right₀ _ hy']
  have hi : IsIntegral O (algebraMap O (FractionRing O) x / algebraMap O (FractionRing O) y) := by
    rw [← isIntegral_algHom_iff ι ι.toRingHom.injective, e']
    exact ha
  obtain ⟨o, ho⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  exact ⟨o, by rw [← e', ← ho, ι.commutes]⟩

theorem appTop_injective {Z : Scheme.{0}} [IsReduced Z] {Ω : Type} [Field Ω]
    (η : Spec (CommRingCat.of Ω) ⟶ Z) (h : ∀ q : Z, η (IsLocalRing.closedPoint Ω) ⤳ q) :
    Function.Injective η.appTop.hom := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro t ht
  rw [← basicOpen_eq_bot_iff, eq_bot_iff]
  intro q hq
  have h1 : η (IsLocalRing.closedPoint Ω) ∈ Z.basicOpen t :=
    (h q).mem_open (Z.basicOpen t).isOpen hq
  have h2 : IsLocalRing.closedPoint Ω ∈ η ⁻¹ᵁ Z.basicOpen t := h1
  rw [Scheme.preimage_basicOpen_top] at h2
  have h3 : η.appTop t = 0 := ht
  rw [h3, Scheme.basicOpen_zero] at h2
  exact h2.elim

theorem bijective_const {Z : Scheme.{0}} [IsReduced Z] {Ω : Type} [Field Ω]
    (η : Spec (CommRingCat.of Ω) ⟶ Z) (h : ∀ q : Z, η (IsLocalRing.closedPoint Ω) ⤳ q)
    {O : Type} [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [Algebra O Ω]
    (f : Z ⟶ Spec (CommRingCat.of O)) [IsProper f] (hinj : Function.Injective (algebraMap O Ω))
    (hf : η ≫ f = Spec.map (CommRingCat.ofHom (algebraMap O Ω))) (hc : ConstClosed O Ω) :
    Function.Bijective (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom) := by
  let ψ : O →+* Γ(Z, ⊤) := f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom
  let φ : Γ(Z, ⊤) →+* Ω := (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.comp η.appTop.hom
  have hφ : Function.Injective φ :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).1.comp (appTop_injective η h)
  have hcomp : φ.comp ψ = algebraMap O Ω := by
    have : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ f.appTop ≫ η.appTop ≫
        (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom = CommRingCat.ofHom (algebraMap O Ω) := by
      rw [← Scheme.Hom.comp_appTop_assoc, hf, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    exact congrArg (fun q => q.hom) this
  have hψ : ψ.IsIntegral :=
    RingHom.IsIntegral.trans _ _
      (RingHom.isIntegral_of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv).2)
      (isIntegral_appTop_of_universallyClosed f)
  refine ⟨fun a b hab => hinj ?_, fun t => ?_⟩
  · rw [← hcomp]
    exact congrArg φ hab
  · have hi : IsIntegral O (φ t) := by
      obtain ⟨p, hp, e⟩ := hψ t
      refine ⟨p, hp, ?_⟩
      rw [← hcomp, ← Polynomial.hom_eval₂, e, map_zero]
    obtain ⟨o, ho⟩ := mem_range_of_isIntegral hinj hc _ hi
    refine ⟨o, hφ ?_⟩
    rw [← ho, ← hcomp]
    rfl


attribute [local instance] GroundTheory.Arith.SchemeCoh.algebraOfOver in
open GroundTheory.Arith.SchemeCoh in
theorem isConnected_closed {Z : Scheme.{0}} {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O]
    (f : Z ⟶ Spec (CommRingCat.of O)) [IsProper f]
    (h : Function.Bijective (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom)) :
    _root_.IsConnected (f ⁻¹' {IsLocalRing.closedPoint O}) := by
  letI : Z.Over (Spec (.of O)) := ⟨f⟩
  have : IsProper (Z ↘ Spec (.of O)) := (inferInstance : IsProper f)
  exact isConnected_closedFibre_of_surj (A := O) (X := Z) h
    (fun x hx => formalFunctions_mem_range (IsLocalRing.maximalIdeal O) (isCoherent_unit Z) 0 hx 0)

end PositivityTheory.Xgn.SpecialFibreConnected

open PositivityTheory.Xgn.SpecialFibreConnected in
theorem PositivityTheory.Xgn.zero_set_special_fibre_connected : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O Ω] (s : X ⟶ Spec (CommRingCat.of O)) [IsProper s] (ϖ : O), Irreducible ϖ → Function.Injective (algebraMap O Ω) → ξ ≫ s = Spec.map (CommRingCat.ofHom (algebraMap O Ω)) → IsCptGen ξ → ConstClosed O Ω → _root_.IsConnected (zeroSet ξ (algebraMap O Ω ϖ)) := by
  intro X Ω _ ξ O _ _ _ _ s _ ϖ hϖ hinj hs hg hc
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian s
  obtain ⟨U, hU, hcl, hint⟩ := cpt_open_integral X Ω ξ hg
  have hrange : Set.range ξ ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    have hz : z = IsLocalRing.closedPoint Ω := Subsingleton.elim (α := PrimeSpectrum Ω) _ _
    rw [Scheme.Opens.range_ι, hz]
    exact (hU _).2 specializes_rfl
  let η : Spec (CommRingCat.of Ω) ⟶ U.toScheme := IsOpenImmersion.lift U.ι ξ hrange
  have hη : η ≫ U.ι = ξ := IsOpenImmersion.lift_fac _ _ _
  haveI : IsClosedImmersion U.ι := IsClosedImmersion.of_isPreimmersion _ (by rwa [Scheme.Opens.range_ι])
  have hsp : ∀ q : U.toScheme, η (IsLocalRing.closedPoint Ω) ⤳ q := fun q => by
    rw [← U.ι.isOpenEmbedding.isInducing.specializes_iff]
    have e : U.ι (η (IsLocalRing.closedPoint Ω)) = genPt ξ :=
      congrArg (fun g : Spec (CommRingCat.of Ω) ⟶ X => g (IsLocalRing.closedPoint Ω)) hη
    exact e ▸ (hU _).1 q.2
  have hb := bijective_const η hsp (U.ι ≫ s) hinj (by rw [← Category.assoc, hη, hs]) hc
  have hconn := (isConnected_closed (U.ι ≫ s) hb).image U.ι U.ι.continuous.continuousOn
  have hm : ∀ P : PrimeSpectrum O, ϖ ∈ P.asIdeal ↔ P = IsLocalRing.closedPoint O := fun P => by
    have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} := hϖ.maximalIdeal_eq
    constructor
    · intro h
      apply PrimeSpectrum.ext
      refine ((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le P.isPrime.ne_top ?_).symm
      rw [hmax, Ideal.span_singleton_le_iff_mem]
      exact h
    · rintro rfl
      change ϖ ∈ IsLocalRing.maximalIdeal O
      rw [hmax]
      exact Ideal.mem_span_singleton_self ϖ
  have key : ∀ (q : X) (h : genPt ξ ⤳ q),
      ¬ unitAt ξ ⟨q, h⟩ (algebraMap O Ω ϖ) ↔ s q = IsLocalRing.closedPoint O := fun q h => by
    rw [(ConstReg.regular_const X Ω ξ O s hs ⟨q, h⟩ ϖ).2 hg, not_not]
    exact hm _
  convert hconn using 1
  ext q
  constructor
  · rintro ⟨h, hq⟩
    refine ⟨⟨q, (hU q).2 h⟩, ?_, rfl⟩
    exact (key q h).1 hq
  · rintro ⟨z, hz, rfl⟩
    exact ⟨(hU _).1 z.2, (key _ _).2 hz⟩
end

section

open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.Xgn.SequenceFamilyPairing

theorem val_mem {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] (hsm : Smooth G.hom)
    {Ω R B T : Type} [Field Ω] [CommRing R] [CommRing B] [CommRing T]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (x : Spec (CommRingCat.of R) ⟶ X) (t : Spec (CommRingCat.of T) ⟶ X)
    (φ : R →+* Ω) (ψ : R →+* B) (k : B →+* Ω) (s : T →+* B) (g : T →+* Ω)
    (hk : k.comp ψ = φ) (hs : k.comp s = g)
    (hx : Spec.map (CommRingCat.ofHom φ) ≫ x = ξ)
    (ht : Spec.map (CommRingCat.ofHom ψ) ≫ x = Spec.map (CommRingCat.ofHom s) ≫ t)
    {L Li : Type} [AddCommGroup L] [Module R L] [AddCommGroup Li] [Module Ω Li]
    (M₀ : LieModel G x L) (M : LieModel G ξ Li) (j₀ : L → Li)
    (hj₀ : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ (M₀.pt v).left)
    (u₀ : Module.Dual R L) (u : Module.Dual Ω Li) (hu : ∀ v, u (j₀ v) = φ (u₀ v))
    (e : Li) (v : epsAt t ⟶ G) (hv : IsTanAt G t v)
    (he : (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left) : u e ∈ k.range := by
  obtain ⟨L', _, _, ⟨M'⟩⟩ := lieModel_exists X G B (Spec.map (CommRingCat.ofHom ψ) ≫ x)
  obtain ⟨L'', _, _, ⟨M''⟩⟩ := lieModel_exists X G T t
  have hξ : ξ = Spec.map (CommRingCat.ofHom k) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ x := by
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hk, hx]
  obtain ⟨β, hβ, -, hsp, hext⟩ := HTPull.lieBC ψ x _ rfl hsm M₀ M'
  obtain ⟨j', hj', hjs, -, -⟩ := HTPull.lieBC k _ ξ hξ hsm M' M
  obtain ⟨j₂, hj₂, -, -, -⟩ := HTPull.lieBC s t _ ht hsm M'' M'
  obtain ⟨u', hu'⟩ := hext u₀
  have hjj : ∀ l, j' (β l) = j₀ l := fun l => M.inj (Over.OverMorphism.ext (by
    rw [hj', hβ, hj₀, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, HTPull.dualMap_comp, hk]))
  have hall : ∀ e' : L', u (j' e') = k (u' e') := by
    intro e'
    have he' : e' ∈ Submodule.span B (Set.range β) := by rw [hsp]; trivial
    induction he' using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨l, rfl⟩ := h
      rw [hjj, hu, hu', ← hk]
      rfl
    | zero => simp
    | add a b _ _ ha hb => simp [ha, hb]
    | smul a b _ hb => simp [hjs, hb]
  obtain ⟨l, rfl⟩ := M''.onto v hv
  have e1 : e = j' (j₂ l) := M.inj (Over.OverMorphism.ext (by
    rw [he, hj', hj₂, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, HTPull.dualMap_comp, hs]))
  rw [e1, hall]
  exact ⟨_, rfl⟩

theorem val_frac {X : Scheme.{0}} {G : Over X} [GrpObj G] [IsCommMonObj G] (hsm : Smooth G.hom)
    {Ω R : Type} [Field Ω] [CommRing R] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (φ : R →+* Ω) (hφ : Function.Injective φ) (x : Spec (CommRingCat.of R) ⟶ X) (hx : spMap φ ≫ x = ξ)
    (z : Spec (CommRingCat.of R)) (hz : genPt ξ ⤳ x z)
    {L Li : Type} [AddCommGroup L] [Module R L] [AddCommGroup Li] [Module Ω Li]
    (M₀ : LieModel G x L) (M : LieModel G ξ Li) (j₀ : L → Li)
    (hj₀ : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ (M₀.pt v).left)
    (u₀ : Module.Dual R L) (u : Module.Dual Ω Li) (hu : ∀ v, u (j₀ v) = φ (u₀ v))
    (e : Li) (he : e ∈ M.lat ⟨x z, hz⟩) : ∃ r s : R, s ∉ z.asIdeal ∧ φ s * u e = φ r := by
  haveI : z.asIdeal.IsPrime := PrimeSpectrum.isPrime z
  letI alg : Algebra R ((Spec (CommRingCat.of R)).presheaf.stalk z) := StructureSheaf.stalkAlgebra R z
  haveI loc : IsLocalization.AtPrime ((Spec (CommRingCat.of R)).presheaf.stalk z) z.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R z
  have hun : ∀ s : z.asIdeal.primeCompl, IsUnit (φ s) := by
    intro s
    refine IsUnit.mk0 _ fun h => s.2 ?_
    have h0 : (s : R) = 0 := hφ (h.trans (map_zero φ).symm)
    rw [h0]
    exact z.asIdeal.zero_mem
  let lam : (Spec (CommRingCat.of R)).presheaf.stalk z →+* Ω := IsLocalization.lift (M := z.asIdeal.primeCompl) hun
  let lam' : (Spec (CommRingCat.of R)).presheaf.stalk z ⟶ CommRingCat.of Ω := CommRingCat.ofHom lam
  have hlam : ∀ r : R, lam (algebraMap R _ r) = φ r := fun r => IsLocalization.lift_eq hun r
  have e0 : (Spec (CommRingCat.of R)).fromSpecStalk z =
      Spec.map (CommRingCat.ofHom (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk z))) :=
    Spec.fromSpecStalk_eq' _ _
  have e1 : Spec.map (CommRingCat.ofHom lam) ≫ (Spec (CommRingCat.of R)).fromSpecStalk z = spMap φ := by
    rw [e0, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hlam
  have e2 : Spec.map (x.stalkMap z ≫ lam') ≫ X.fromSpecStalk (x z) = ξ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) e1).trans hx)
  have e3 : spMap (genMap ξ ⟨x z, hz⟩) ≫ X.fromSpecStalk (x z) = ξ :=
    GlobalTheory.CompanionTheory.Ar.LieStalk.spMap_genMap_fromSpecStalk ⟨x z, hz⟩
  have e4 : x.stalkMap z ≫ lam' = CommRingCat.ofHom (genMap ξ ⟨x z, hz⟩) :=
    Spec.map_injective ((cancel_mono (X.fromSpecStalk (x z))).1 (e2.trans e3.symm))
  have e5 : ∀ a, lam ((x.stalkMap z).hom a) = genMap ξ ⟨x z, hz⟩ a := fun a => ConcreteCategory.congr_hom e4 a
  have e6 : Spec.map (CommRingCat.ofHom (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk z))) ≫ x =
      Spec.map (CommRingCat.ofHom (x.stalkMap z).hom) ≫ X.fromSpecStalk (x z) :=
    (congrArg (· ≫ x) e0.symm).trans (Scheme.SpecMap_stalkMap_fromSpecStalk x).symm
  obtain ⟨v, hv, hev⟩ := ((lieLat_carrier X G Ω ξ Li M ⟨x z, hz⟩).1 e).1 he
  obtain ⟨b, hb⟩ := val_mem hsm ξ x (X.fromSpecStalk (x z)) φ
    (algebraMap R ((Spec (CommRingCat.of R)).presheaf.stalk z)) lam (x.stalkMap z).hom (genMap ξ ⟨x z, hz⟩)
    (RingHom.ext hlam) (RingHom.ext e5) hx e6 M₀ M j₀ hj₀ u₀ u hu e v hv hev
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj z.asIdeal.primeCompl b
  refine ⟨r, s, s.2, ?_⟩
  rw [← hb, ← hlam, ← hlam, ← map_mul, mul_comm]
  exact congrArg lam hrs

theorem mem_of_frac {O Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (R : Subalgebra O Ω) (a : Ω)
    (h : ∀ z : PrimeSpectrum R, ∃ r s : R, s ∉ z.asIdeal ∧ (s : Ω) * a = r) : a ∈ R := by
  let I : Ideal R :=
    { carrier := {s | (s : Ω) * a ∈ R}
      add_mem' := fun {u v} hu hv => by
        show ((u + v : R) : Ω) * a ∈ R
        rw [Subalgebra.coe_add, add_mul]
        exact add_mem hu hv
      zero_mem' := by
        show ((0 : R) : Ω) * a ∈ R
        simp
      smul_mem' := fun c u hu => by
        show ((c • u : R) : Ω) * a ∈ R
        rw [smul_eq_mul, Subalgebra.coe_mul, _root_.mul_assoc]
        exact mul_mem c.2 hu }
  by_cases hI : I = ⊤
  · have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
    have h2 : ((1 : R) : Ω) * a ∈ R := h1
    simpa using h2
  · obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hI
    obtain ⟨r, s, hs, e⟩ := h ⟨P, hP.isPrime⟩
    exact absurd (hIP (show (s : Ω) * a ∈ R from e ▸ r.2)) hs

end PositivityTheory.Xgn.SequenceFamilyPairing

theorem PositivityTheory.Xgn.sequence_family_pairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), IsArithVar (mCoordIdeal y) (d + 1) → 0 < D.p + D.q → ∀ (p : ℕ) [Fact p.Prime], p ∈ S → ∀ (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime], (p : A) ∈ m → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω], ∀ (G : GenTors 𝔐 p) (c' : ∀ k, J k), mseg y c' ≠ 0 → ∀ (P : ChartPack G O c') (u : Module.Dual Ω 𝔐.Li), u ∈ P.Dh.om → ∀ v : 𝔐.Li, (∀ q : Cpt 𝔐.ξ, InChart 𝔐.ξ (mseg y) c' q → (∀ o : O, algebraMap O Ω o ∈ regAt 𝔐.ξ q) → v ∈ 𝔐.M.lat q) → u v ∈ CR O y c' := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d hd _ p _ hpS A _ _ _ m _ hpm O _ _ _ _ _ _ _ G c' hc' P u
    hu v hv
  rw [P.isHT.1] at hu
  obtain ⟨u₀, rfl⟩ := hu
  refine PositivityTheory.Xgn.SequenceFamilyPairing.mem_of_frac _ _ fun z => ?_
  obtain ⟨h1, h2, -⟩ := PositivityTheory.Xgn.exists_function_at_point E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd p hpS A m hpm O G
    c' hc' P z
  exact PositivityTheory.Xgn.SequenceFamilyPairing.val_frac 𝔐.t.semi.smooth 𝔐.ξ (algebraMap (CR O y c') Ω)
    Subtype.val_injective P.x P.x_gen z (𝔐.all _) P.M 𝔐.M P.toLi P.toLi_pt u₀ (P.j u₀) (P.j_apply u₀) v (hv _ h1 h2)
end
