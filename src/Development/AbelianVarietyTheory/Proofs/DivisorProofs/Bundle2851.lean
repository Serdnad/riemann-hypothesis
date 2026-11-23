module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle242
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomEqOneOfNilpotent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2750
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibLat

open GlobalTheory.SplitTorus (torusMap bcMap)

theorem compat_of_compat_field : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → ∀ (X : Type) [AddCommGroup X] (m : I → X →+ X) (c : T → X →+ ZMod L) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z) (a : o →+* V) (G₁ : Over (Sp V)) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left), IsGrpPullback G₁ G ξ φ₁ → ∀ (j : splitTorus (Sp V) X ⟶ G₁), (∀ t, ExtNear (gγ t) (ξ (closedPoint V))) → ∀ (K : Type) [Field K] (b : V →+* K), Function.Injective b → ∀ (GK : Over (Sp K)) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap b) ψ), Compat f gγ ζ L m c (spMap b ≫ ξ) (b.comp a) (ψ ≫ φ₁) (pullTorus hψ j) → Compat f gγ ζ L m c ξ a φ₁ j := by
  intro o Ω _ _ _ M G _ _ hG I T f gγ ζ L hL hζ X _ m c V _ _ _ ξ a G₁ _ φ₁ h₁ j hext K _ b hb GK _ ψ hψ hK
  haveI hsep : IsSeparated G.hom := hG.separated
  haveI : Flat (splitTorusAff ZU X).hom := (GlobalTheory.ExtUnique.splitTorusAff_flat_and_isSeparated _ _).1
  haveI : Flat (splitTorus (Sp V) X).hom := inferInstanceAs (Flat (pullback.snd _ _))
  haveI : IsSchemeTheoreticallyDominant (spMap b) :=
    GlobalTheory.ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hb
  haveI : QuasiCompact (spMap b) := inferInstance
  haveI : IsSchemeTheoreticallyDominant (bcMap (spMap b) X) :=
    IsSchemeTheoreticallyDominant.of_isPullback (GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).flip
  have hw : φ₁ ≫ G.hom = G₁.hom ≫ ξ := h₁.1.w
  refine ⟨fun e => ?_, fun t => ?_⟩
  · have h1 := hK.1 e
    rw [← pullTorus_torusMap_comp] at h1
    simp only [Category.assoc] at h1
    have e1 := pullTorus_left hψ j
    have e2 := pullTorus_left hψ (torusMap (Sp V) (m e) ≫ j)
    refine GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ (bcMap (spMap b) X) ?_
    · simp only [Category.assoc, Over.w, hw, Over.w_assoc, Over.comp_left]
    · calc bcMap (spMap b) X ≫ j.left ≫ φ₁ ≫ (f e).left
          = (pullTorus hψ j).left ≫ ψ ≫ φ₁ ≫ (f e).left := by rw [reassoc_of% e1]
        _ = (pullTorus hψ (torusMap (Sp V) (m e) ≫ j)).left ≫ ψ ≫ φ₁ := h1
        _ = bcMap (spMap b) X ≫ (torusMap (Sp V) (m e) ≫ j).left ≫ φ₁ := by rw [reassoc_of% e2]
  · obtain ⟨zK, hzK, hvK⟩ := hK.2 t
    haveI : NeZero L := ⟨hL.ne'⟩
    have huL : Units.map a.toMonoidHom ζ ^ L = 1 := by rw [← map_pow, hζ, map_one]
    let φh : Multiplicative X →* (Γ(Sp V, ⊤))ˣ :=
      { toFun := fun χ => unitOn (Units.map a.toMonoidHom ζ ^ (c t (Multiplicative.toAdd χ)).val)
        map_one' := by simp [unitOn]
        map_mul' := fun x y => by
          simp only [toAdd_mul, map_add (f := _), unitOn]
          rw [ZMod.val_add, ← pow_eq_pow_mod _ huL, pow_add, map_mul] }
    let z : Over.mk (𝟙 (Sp V)) ⟶ splitTorus (Sp V) X := (GlobalTheory.splitTorusPointsEquiv (Sp V) X _).symm φh
    have hz : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (Units.map a.toMonoidHom ζ ^ (c t χ).val) := fun χ => by
      simp only [GlobalTheory.UU.chV, z, MulEquiv.apply_symm_apply]
      rfl
    have hwz : (spMap b ≫ z.left) ≫ (splitTorus (Sp V) X).hom = 𝟙 _ ≫ spMap b := by
      rw [Category.assoc, Over.w z]; simp
    let z' : Over.mk (𝟙 (Sp K)) ⟶ splitTorus (Sp K) X :=
      Over.homMk ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift (spMap b ≫ z.left) (𝟙 _) hwz)
        ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_snd _ _ _)
    have hz' : z'.left ≫ bcMap (spMap b) X = spMap b ≫ z.left :=
      (GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_fst _ _ _
    have hcz' : ∀ χ, GlobalTheory.UU.chV z' χ = unitOn (Units.map (b.comp a).toMonoidHom ζ ^ (c t χ).val) := fun χ => by
      ext
      have e := congrArg Units.val (hz χ)
      rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val] at e ⊢
      rw [← GlobalTheory.SplitTorus.bcMap_appTop_chi (spMap b), ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hz',
        Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      erw [e]
      simp only [unitOn, Units.coe_map]
      have := congrArg (fun k => k.hom ((Units.map a.toMonoidHom ζ ^ (c t χ).val : Vˣ) : V))
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom b))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      refine this.symm.trans ?_
      simp
    have hzz : zK = z' := GlobalTheory.SplitTorus.hom_ext fun χ => by
      rw [GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.UU.chV_val,
        ← GlobalTheory.UU.chV_val, hzK, hcz']
    have hvK' : ValAt (gγ t) (spMap b ≫ ξ) (spMap b ≫ (z ≫ j).left ≫ φ₁) := by
      convert hvK using 1
      rw [hzz, Over.comp_left, Over.comp_left]
      simp only [Category.assoc]
      rw [reassoc_of% (pullTorus_left hψ j), reassoc_of% hz']
    obtain ⟨v, hv⟩ := ExtNear.exists_valAt ξ (hext t)
    have hvv : spMap b ≫ v = spMap b ≫ (z ≫ j).left ≫ φ₁ := (hv.comp (spMap b)).unique hvK'
    have hveq : v = (z ≫ j).left ≫ φ₁ := by
      refine GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ (spMap b) hvv
      rw [hv.over]
      simp only [Category.assoc, hw, Over.comp_left, Over.w_assoc]
      exact (Category.id_comp _).symm
    exact ⟨z, hz, hveq ▸ hv⟩

end GlobalTheory.Poinc.FibLat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

noncomputable section

namespace GlobalTheory.Poinc.FibLat.ClosedLift

open GlobalTheory.SplitTorus (torusMap bcMap)

theorem endo_of_closed {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsSeparated G.hom] {V : Type} [CommRing V]
    [IsDomain V] {ξ : Sp V ⟶ S} {G₁ : Over (Sp V)} [GrpObj G₁] {φ₁ : G₁.left ⟶ G.left}
    (h : IsGrpPullback G₁ G ξ φ₁) {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (j : splitTorus (Sp V) X ⟶ G₁) [IsMonHom j] {GK : Over (Sp (FractionRing V))} [GrpObj GK]
    {ψ : GK.left ⟶ G₁.left} (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ)
    (hK : IsTorPart (pullTorus hψ j)) {κ : Type} [Field κ] {b : V →+* κ} {G₀ : Over (Sp κ)} [GrpObj G₀]
    {ψ₀ : G₀.left ⟶ G₁.left} (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀) (h0 : IsTorPart (pullTorus hψ₀ j))
    (u : G ⟶ G) [IsMonHom u] (r : X →+ X)
    (hr : (pullTorus hψ₀ j).left ≫ (ψ₀ ≫ φ₁) ≫ u.left = (torusMap _ r ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁) :
    j.left ≫ φ₁ ≫ u.left = (torusMap _ r ≫ j).left ≫ φ₁ := by
  obtain ⟨u₁, hu₁, pa⟩ := GlobalTheory.SymBaseChange.exists_endo h u
  have hw : u₁.left ≫ φ₁ = φ₁ ≫ u.left := by
    have := congrArg CommaMorphism.left (pa (𝟙 G₁))
    simpa [pushPt] using this
  haveI := hu₁
  obtain ⟨s, hs⟩ := hK.factor (pullTorus hψ (j ≫ u₁)) inferInstance
  rw [← pullTorus_torusMap_comp] at hs
  obtain ⟨_, _⟩ : QuasiCompact (spMap (algebraMap V (FractionRing V))) ∧
      IsSchemeTheoreticallyDominant (spMap (algebraMap V (FractionRing V))) :=
    GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  haveI : IsSeparated G₁.hom := MorphismProperty.of_isPullback h.1 ‹_›
  have key : j ≫ u₁ = torusMap _ s ≫ j :=
    GlobalTheory.ExtUnique.over_hom_ext_of_isPullback
      (GlobalTheory.SplitTorus.isPullback_bcMap (spMap (algebraMap V (FractionRing V))) X)
      (by rw [← pullTorus_left hψ, ← pullTorus_left hψ, hs])
  have k0 : torusMap _ s ≫ pullTorus hψ₀ j = torusMap _ r ≫ pullTorus hψ₀ j := by
    apply hom_ext_of_pullback (hψ₀.comp h)
    have e1 := pullTorus_left hψ₀ (j ≫ u₁)
    have e2 := pullTorus_left hψ₀ j
    calc (torusMap _ s ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁
        = ((pullTorus hψ₀ (j ≫ u₁)).left ≫ ψ₀) ≫ φ₁ := by
          rw [← pullTorus_torusMap_comp, ← key, Category.assoc]
      _ = bcMap (spMap b) X ≫ j.left ≫ φ₁ ≫ u.left := by
          rw [e1]; simp [Category.assoc, hw]
      _ = ((pullTorus hψ₀ j).left ≫ ψ₀) ≫ φ₁ ≫ u.left := by
          rw [e2]; simp only [Category.assoc]
      _ = (torusMap _ r ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁ := by
          rw [← hr]; simp only [Category.assoc]
  have hsr : s = r := h0.cancel k0
  subst hsr
  rw [← key, Over.comp_left, Category.assoc, hw]

theorem compat_of_closed : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → IsUnit (L : o) → (∀ e, IsMonHom (f e)) → (∀ t, gγ t ^ L = 1) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z) (a : o →+* V) (G₁ : Over (Sp V)) [GrpObj G₁] (φ₁ : G₁.left ⟶ G.left), IsGrpPullback G₁ G ξ φ₁ → ∀ (j : splitTorus (Sp V) X ⟶ G₁), IsMonHom j → (∀ t, ExtNear (gγ t) (ξ (closedPoint V))) → ∀ (GK : Over (Sp (FractionRing V))) [GrpObj GK] (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), IsTorPart (pullTorus hψ j) → ∀ (κ : Type) [Field κ] (b : V →+* κ), IsLocalHom b → ∀ (G₀ : Over (Sp κ)) [GrpObj G₀] (ψ₀ : G₀.left ⟶ G₁.left) (hψ₀ : IsGrpPullback G₀ G₁ (spMap b) ψ₀), IsTorPart (pullTorus hψ₀ j) → Compat f gγ ζ L m c (spMap b ≫ ξ) (b.comp a) (ψ₀ ≫ φ₁) (pullTorus hψ₀ j) → Compat f gγ ζ L m c ξ a φ₁ j := by
  intro o Ω _ _ _ M G _ _ hG I T f gγ ζ L hL hζ hLu hf hgγ X _ _ _ m c V _ _ _ ξ a G₁ _ φ₁ h j hj hext GK _ ψ hψ hK
    κ _ b hb G₀ _ ψ₀ hψ₀ h0 hC
  haveI := hG.separated
  haveI := hj
  haveI : NeZero L := ⟨hL.ne'⟩
  refine ⟨fun e => ?_, fun t => ?_⟩
  · haveI := hf e
    exact endo_of_closed h j hψ hK hψ₀ h0 (f e) (m e) (hC.1 e)
  obtain ⟨z₀, hz₀, hv₀⟩ := hC.2 t
  have hζV : (Units.map a.toMonoidHom ζ) ^ L = 1 := by rw [← map_pow, hζ, map_one]
  have hpow : ∀ k : ℕ, ((Units.map a.toMonoidHom ζ) ^ k) ^ L = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, hζV, one_pow]
  let F : Multiplicative X →* Γ(Sp V, ⊤)ˣ :=
    { toFun := fun χ => unitOn (Units.map a.toMonoidHom ζ ^ (c t (Multiplicative.toAdd χ)).val)
      map_one' := by simp [unitOn]
      map_mul' := fun x y => by
        rw [toAdd_mul, map_add (f := _), ZMod.val_add, ← pow_eq_pow_mod _ hζV, pow_add]
        simp [unitOn] }
  let Z1 : Over (Sp V) := Over.mk (𝟙 (Sp V))
  obtain ⟨z, hz⟩ : ∃ z : Z1 ⟶ splitTorus (Sp V) X, GlobalTheory.splitTorusPointsEquiv (Sp V) X Z1 z = F :=
    ⟨_, MulEquiv.apply_symm_apply _ _⟩
  have hzχ : ∀ χ, GlobalTheory.UU.chV z χ = unitOn (Units.map a.toMonoidHom ζ ^ (c t χ).val) := fun χ => by
    show GlobalTheory.splitTorusPointsEquiv (Sp V) X Z1 z (Multiplicative.ofAdd χ) = _
    rw [hz]; rfl
  have hzL : z ^ L = 1 := by
    apply (GlobalTheory.splitTorusPointsEquiv (Sp V) X Z1).injective
    rw [map_pow, hz, map_one]
    refine MonoidHom.ext fun χ => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    show unitOn _ ^ L = 1
    rw [unitOn, ← map_pow, hpow, map_one]

  let x : Over.mk (Z1.hom ≫ ξ) ⟶ G := pushPt h.1.w (z ≫ j)
  have hxL : x ^ L = 1 := by
    have e1 : pushPt h.1.w ((z ≫ j) ^ L) = x ^ L := map_pow (pushHom h Z1) (z ≫ j) L
    rw [← e1, ← pow_comp, hzL, one_comp]
    exact map_one (pushHom h Z1)

  obtain ⟨v, hv⟩ := ExtNear.exists_valAt ξ (hext t)
  have hvb : spMap b ≫ v = (z₀ ≫ pullTorus hψ₀ j).left ≫ ψ₀ ≫ φ₁ := ValAt.unique (hv.comp (spMap b)) hv₀
  obtain ⟨W, hW, s', ⟨hW1, hW2⟩, hs', hsv⟩ := hv
  let H : Over.mk W.ι ⟶ G := Over.homMk hW hW1
  have hne : (W : Set M.Z).Nonempty := ⟨ξ (closedPoint V), by rw [← hs']; exact (s' (closedPoint V)).2⟩
  haveI : Nonempty W.toScheme := ⟨⟨_, hne.some_mem⟩⟩
  haveI : IsIntegral W.toScheme := isIntegral_of_isOpenImmersion W.ι
  have hr : Set.range M.pt ⊆ Set.range W.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hne (x := w) trivial
  let x₀ := IsOpenImmersion.lift W.ι M.pt hr
  have hx₀ : x₀ ≫ W.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  haveI : IsDominant (x₀ ≫ W.ι) := hx₀ ▸ M.isDominant_pt
  haveI : IsDominant x₀ := IsDominant.of_comp_of_isOpenImmersion x₀ W.ι
  have hHL : H ^ L = 1 := by
    let u : Over.mk M.pt ⟶ Over.mk W.ι := Over.homMk x₀ hx₀
    have hu : u ≫ H = gγ t := Over.OverMorphism.ext (hW2 x₀ hx₀)
    have e : u ≫ H ^ L = u ≫ 1 := by rw [comp_pow, hu, hgγ t, comp_one]
    apply Over.OverMorphism.ext
    haveI : IsReduced (Over.mk W.ι).left := inferInstanceAs (IsReduced W.toScheme)
    refine ext_of_isDominant_of_isSeparated (s := G.hom) ?_ x₀ ?_
    · rw [Over.w, Over.w]
    · exact congrArg CommaMorphism.left e
  let σ : Over.mk (Z1.hom ≫ ξ) ⟶ Over.mk W.ι := Over.homMk s' (by
    show s' ≫ W.ι = 𝟙 _ ≫ ξ
    rw [hs', Category.id_comp])
  let y : Over.mk (Z1.hom ≫ ξ) ⟶ G := σ ≫ H
  have hyL : y ^ L = 1 := by
    show (σ ≫ H) ^ L = 1
    rw [← comp_pow, hHL, comp_one]

  have hw' : (spMap b ≫ z.left) ≫ (splitTorus (Sp V) X).hom = 𝟙 _ ≫ spMap b := by
    rw [Category.assoc, Over.w z]; simp [Z1]
  let z' : Over.mk (𝟙 (Sp κ)) ⟶ splitTorus (Sp κ) X :=
    Over.homMk ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift (spMap b ≫ z.left) (𝟙 _) hw')
      ((GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_snd _ _ _)
  have hz'l : z'.left ≫ bcMap (spMap b) X = spMap b ≫ z.left :=
    (GlobalTheory.SplitTorus.isPullback_bcMap (spMap b) X).lift_fst _ _ _
  have hz'χ : ∀ χ, GlobalTheory.UU.chV z' χ = unitOn (Units.map (b.comp a).toMonoidHom ζ ^ (c t χ).val) := fun χ => by
    ext
    have e := congrArg Units.val (hzχ χ)
    rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val] at e ⊢
    rw [← GlobalTheory.SplitTorus.bcMap_appTop_chi (spMap b), ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hz'l,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
    erw [e]
    simp only [unitOn, Units.coe_map]
    have := congrArg (fun k => k.hom ((Units.map a.toMonoidHom ζ ^ (c t χ).val : Vˣ) : V))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom b))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
    refine this.symm.trans ?_
    simp
  have hzz : z₀ = z' := by
    apply (GlobalTheory.splitTorusPointsEquiv (Sp κ) X _).injective
    refine MonoidHom.ext fun χ => ?_
    exact (hz₀ (Multiplicative.toAdd χ)).trans (hz'χ (Multiplicative.toAdd χ)).symm
  have hcl : spMap b ≫ x.left = spMap b ≫ y.left := by
    show spMap b ≫ (z ≫ j).left ≫ φ₁ = spMap b ≫ s' ≫ hW
    rw [hsv, hvb, hzz]
    simp only [Over.comp_left, Category.assoc]
    rw [reassoc_of% (pullTorus_left hψ₀ j), reassoc_of% hz'l]
  have hLV : IsUnit (L : V) := by simpa using hLu.map a
  have hxy : x = y := GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint M.Z G hG.smooth V (Z1.hom ≫ ξ) L hLV x y
    (by rw [hxL, hyL]) κ b hb hcl
  refine ⟨z, hzχ, ?_⟩
  have e' : (z ≫ j).left ≫ φ₁ = v := (congrArg CommaMorphism.left hxy).trans hsv
  rw [e']
  exact ⟨W, hW, s', ⟨hW1, hW2⟩, hs', hsv⟩

end GlobalTheory.Poinc.FibLat.ClosedLift
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.TorusPart
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc.FibLat GlobalTheory.Poinc.Eq8

namespace GlobalTheory.Poinc.FibLat


open GlobalTheory.NonlocalTrait in
theorem exists_trait_torusPart : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (G : Over Y) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ w w' : Y, w ⤳ w' → w ≠ w' → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ξ : Sp V ⟶ Y) (G₁ : Over (Sp V)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (φ₁ : G₁.left ⟶ G.left) (X₁ : Type) (_ : AddCommGroup X₁) (_ : Module.Free ℤ X₁) (_ : Module.Finite ℤ X₁) (j : splitTorus (Sp V) X₁ ⟶ G₁) (GK : Over (Sp (FractionRing V))) (_ : GrpObj GK) (ψ : GK.left ⟶ G₁.left) (hψ : IsGrpPullback GK G₁ (spMap (algebraMap V (FractionRing V))) ψ), ξ (closedPoint V) = w' ∧ (spMap (algebraMap V (FractionRing V)) ≫ ξ) (closedPoint (FractionRing V)) = w ∧ IsGrpPullback G₁ G ξ φ₁ ∧ IsMonHom j ∧ IsTorPart (pullTorus hψ j) := by
  intro Y _ _ G _ _ hG w w' hsp hne
  let s' : Sp (Y.presheaf.stalk w') ⟶ Y := Y.fromSpecStalk w'
  let g : Y.presheaf.stalk w' →+* Y.presheaf.stalk w := (Y.presheaf.stalkSpecializes hsp).hom
  have hgs : spMap g ≫ s' = Y.fromSpecStalk w := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hsp
  have hg : ¬ IsLocalHom g := by
    intro hl
    apply hne
    have h1 : (spMap g) (closedPoint (Y.presheaf.stalk w)) = closedPoint (Y.presheaf.stalk w') :=
      Spec_closedPoint
    calc w = Y.fromSpecStalk w (closedPoint (Y.presheaf.stalk w)) := Scheme.fromSpecStalk_closedPoint.symm
      _ = (spMap g ≫ s') (closedPoint (Y.presheaf.stalk w)) := by rw [hgs]
      _ = s' ((spMap g) (closedPoint (Y.presheaf.stalk w))) := Scheme.Hom.comp_apply _ _ _
      _ = s' (closedPoint (Y.presheaf.stalk w')) := by rw [h1]
      _ = w' := Scheme.fromSpecStalk_closedPoint
  let GR := (Over.pullback s').obj G
  have hGR : IsSemiAbelian GR := IsSemiAbelian.pullback _ G hG
  obtain ⟨V, _, _, hV, ψ, Ω, _, α, β, hψ, hβ, e, ⟨E⟩⟩ :=
    GlobalTheory.exists_trait_nonlocal_torusExtension (Y.presheaf.stalk w') GR hGR (Y.presheaf.stalk w) g hg
  let alg := algebraMap V (FractionRing V)
  let ξ : Sp V ⟶ Y := spMap ψ ≫ s'
  let G₁ := (Over.pullback ξ).obj G
  have h₁ : IsGrpPullback G₁ G ξ (pullback.fst G.hom ξ) := isGrpPullback_pullback G ξ
  have hG₁ : IsSemiAbelian G₁ := IsSemiAbelian.pullback _ G hG
  let GK := (Over.pullback (spMap (alg.comp ψ))).obj GR
  have hK : IsGrpPullback GK G (spMap alg ≫ ξ) _ :=
    ((isGrpPullback_pullback GR (spMap (alg.comp ψ))).comp (isGrpPullback_pullback G s')).congr
      (by rw [spMap_comp', Category.assoc]) rfl
  let ψ' : GK.left ⟶ G₁.left := h₁.1.lift _ (GK.hom ≫ spMap alg) (by rw [hK.1.w, Category.assoc])
  have hψ' : IsGrpPullback GK G₁ (spMap alg) ψ' :=
    h₁.cancel (hK.congr rfl (h₁.1.lift_fst _ _ _).symm) (h₁.1.lift_snd _ _ _)
  letI := E.addCommGroup
  haveI := E.free
  haveI := E.finite
  haveI := E.i_hom
  obtain ⟨j, hj, ej⟩ := GlobalTheory.TorusPart.extend_torus_hom_dvr V G₁ hG₁ GK ψ' hψ' ⟨E⟩ (FractionRing V) (RingHom.id _) GK ψ'
    hψ' E.X E.i E.i_hom
  haveI : IsLocalHom ψ := hψ
  have hαl : IsLocalHom α := ⟨fun x hx => isUnit_iff_ne_zero.2 fun h0 => by simp [h0] at hx⟩
  have hβl : IsLocalHom β := ⟨fun x hx => by
    by_contra hn
    rw [hβ x ((mem_maximalIdeal x).2 hn)] at hx
    exact not_isUnit_zero hx⟩
  have key : spMap α ≫ spMap alg ≫ ξ = spMap β ≫ Y.fromSpecStalk w := by
    calc spMap α ≫ spMap alg ≫ ξ = spMap ((α.comp alg).comp ψ) ≫ s' := by
          simp only [ξ, spMap_comp', Category.assoc]
      _ = spMap (β.comp g) ≫ s' := by rw [e]
      _ = spMap β ≫ Y.fromSpecStalk w := by rw [spMap_comp', Category.assoc, hgs]
  refine ⟨V, inferInstance, inferInstance, hV, ξ, G₁, inferInstance, inferInstance, pullback.fst G.hom ξ, E.X,
    inferInstance, inferInstance, inferInstance, j, GK, inferInstance, ψ', hψ', ?_, ?_, h₁, hj, ?_⟩
  · have h1 : (spMap ψ) (closedPoint V) = closedPoint (Y.presheaf.stalk w') := Spec_closedPoint
    calc ξ (closedPoint V) = s' ((spMap ψ) (closedPoint V)) := Scheme.Hom.comp_apply _ _ _
      _ = s' (closedPoint (Y.presheaf.stalk w')) := by rw [h1]
      _ = w' := Scheme.fromSpecStalk_closedPoint
  · have h1 : (spMap α) (closedPoint Ω) = closedPoint (FractionRing V) := Spec_closedPoint
    have h2 : (spMap β) (closedPoint Ω) = closedPoint (Y.presheaf.stalk w) := Spec_closedPoint
    calc (spMap alg ≫ ξ) (closedPoint (FractionRing V)) = (spMap alg ≫ ξ) ((spMap α) (closedPoint Ω)) := by rw [h1]
      _ = (spMap α ≫ spMap alg ≫ ξ) (closedPoint Ω) := (Scheme.Hom.comp_apply _ _ _).symm
      _ = (spMap β ≫ Y.fromSpecStalk w) (closedPoint Ω) := by rw [key]
      _ = Y.fromSpecStalk w ((spMap β) (closedPoint Ω)) := Scheme.Hom.comp_apply _ _ _
      _ = Y.fromSpecStalk w (closedPoint (Y.presheaf.stalk w)) := by rw [h2]
      _ = w := Scheme.fromSpecStalk_closedPoint
  · have : GlobalTheory.TorusPart.pullTorus hψ' j = E.i := ej
    rw [this]
    exact isTorPart_torusExtension E

end GlobalTheory.Poinc.FibLat
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem splitTorus_hom_eq_of_nilpotent : ∀ (A κ : Type) [CommRing A] [IsLocalRing A] [CommRing κ]
    (π : A →+* κ), Function.Surjective π → IsNilpotent (RingHom.ker π) → ∀ (X : Type)
    [AddCommGroup X] (H : Over (Sp A)) [GrpObj H] [IsCommMonObj H]
    (i₁ i₂ : splitTorus (Sp A) X ⟶ H), IsMonHom i₁ → IsMonHom i₂ →
    GlobalTheory.SplitTorus.bcMap (spMap π) X ≫ i₁.left = GlobalTheory.SplitTorus.bcMap (spMap π) X ≫ i₂.left →
    i₁ = i₂ := by
  intro A κ _ _ _ π hπ hJ X _ H _ _ i₁ i₂ h₁ h₂ h
  set J := RingHom.ker π
  haveI : IsMonHom i₂⁻¹ := inferInstance
  haveI hf : IsMonHom (i₁ * i₂⁻¹) := GlobalTheory.Serre.isMonHom_mul _ _
  set r : Sp (A ⧸ J) ⟶ Sp A := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  let e : A ⧸ J ≃+* κ := RingHom.quotientKerEquivOfSurjective hπ
  have hr : r = spMap e.symm.toRingHom ≫ spMap π := by
    simp only [r, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, Ideal.Quotient.mk_eq_mk]
    rw [RingEquiv.eq_symm_apply]
    rfl

  obtain ⟨l, hl⟩ : ∃ l, l ≫ SplitTorus.bcMap (spMap π) X = pullback.fst (splitTorus (Sp A) X).hom r :=
    ⟨_, (SplitTorus.isPullback_bcMap (spMap π) X).lift_fst (pullback.fst (splitTorus (Sp A) X).hom r)
      (pullback.snd (splitTorus (Sp A) X).hom r ≫ spMap e.symm.toRingHom)
      (by rw [pullback.condition, Category.assoc, ← hr])⟩
  let t : Over.mk (pullback.fst (splitTorus (Sp A) X).hom r ≫ (splitTorus (Sp A) X).hom) ⟶ splitTorus (Sp A) X := Over.homMk (pullback.fst (splitTorus (Sp A) X).hom r)
  have ht : t ≫ i₁ = t ≫ i₂ := by
    ext
    simp only [t, Over.comp_left, Over.homMk_left]
    simp only [← hl, Category.assoc, h]
  have ht1 : t ≫ (i₁ * i₂⁻¹) = t ≫ (toUnit _ ≫ η[H]) := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, ht, mul_inv_cancel, ← Category.assoc,
      Hom.one_def]
    congr 1
  have key := splitTorus_hom_eq_one_of_nilpotent A J hJ X H (i₁ * i₂⁻¹) hf (by
    ext
    · apply pullback.hom_ext
      · simp only [Over.pullback_map_left, pullback.lift_fst]
        exact congrArg CommaMorphism.left ht1
      · simp only [Over.pullback_map_left, pullback.lift_snd])
  rw [← Hom.one_def, mul_inv_eq_one] at key
  exact key

end GlobalTheory
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.TrueGeo


theorem _root_.GlobalTheory.T.fubiniStudy_coordinate_combinations_noCommonZero : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (m N : ℕ) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (g : X ⟶ PSpace (𝓞 K) m) (u : Fin (m + 1) → V) (b : Module.Basis (Fin N) K V) (c : Matrix (Fin (m + 1)) (Fin N) K) (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ),
    g ≫ PSpace.str (𝓞 K) m = p →
    (∀ lam : Fin (m + 1) → 𝓞 K, ∑ k, lam k • u k = 0 → ∑ k, algX p ⊤ (lam k) • GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g = 0) →
    (∀ j, b j = ∑ k, c k j • u k) → (∀ σ, (A σ).det ≠ 0) →
    ∀ τ : 𝓞 K →+* ℂ, Weight.NoCommonZero fun a => ∑ k, (c.map (OfLattice.extEmb τ) * A (OfLattice.extEmb τ)) k a • secVal p τ (GlobalTheory.Cartier.secPull (ProjSpace.coord (𝓞 K) m k) g) := by
  first | exact @GlobalTheory.FubiniStudyFrame.noCommonZero_comb | exact GlobalTheory.FubiniStudyFrame.noCommonZero_comb | (intros; apply GlobalTheory.FubiniStudyFrame.noCommonZero_comb <;> assumption)
end
