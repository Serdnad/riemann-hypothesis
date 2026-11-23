module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle065
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle009
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle007
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle011
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle016
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle035
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle006
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle011
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle007
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.Bundle008
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.ContinuousAtOfClosedRel
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Star
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.UnitarySelfGeneration

open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

noncomputable def genSec (Γ : QFGroup R T) (t : T) :
    Spec (CommRingCat.of (FractionRing R)) ⟶ pullback Γ.G.hom (genPt R).hom :=
  pullback.lift (Γ.pt t).left (𝟙 _) (by rw [Category.id_comp]; exact Over.w (Γ.pt t))

theorem genSec_fst (Γ : QFGroup R T) (t : T) : genSec Γ t ≫ pullback.fst _ _ = (Γ.pt t).left :=
  pullback.lift_fst _ _ _

theorem genSec_snd (Γ : QFGroup R T) (t : T) : genSec Γ t ≫ pullback.snd _ _ = 𝟙 _ :=
  pullback.lift_snd _ _ _

theorem gen_asIdeal (z : Spec (CommRingCat.of (FractionRing R))) : ((genPt R).hom z).asIdeal = ⊥ := by
  have hz : z.asIdeal = ⊥ := (Ideal.eq_bot_or_top z.asIdeal).resolve_right z.2.ne_top
  show Ideal.comap (algebraMap R (FractionRing R)) z.asIdeal = ⊥
  rw [hz]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))

theorem genSec_cover (Γ : QFGroup R T) (a : ↥(pullback Γ.G.hom (genPt R).hom)) : ∃ t z, genSec Γ t z = a := by
  haveI : IsPreimmersion (genPt R).hom := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h1 : Γ.G.hom (pullback.fst Γ.G.hom (genPt R).hom a) = (genPt R).hom (pullback.snd Γ.G.hom (genPt R).hom a) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  obtain ⟨t, z, hz⟩ := Γ.pt_onto (pullback.fst Γ.G.hom (genPt R).hom a) (by rw [h1]; exact gen_asIdeal _)
  refine ⟨t, z, (pullback.fst Γ.G.hom (genPt R).hom).isEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, genSec_fst, hz]

theorem genSec_open [Finite T] (Γ : QFGroup R T) (t : T) : IsOpenImmersion (genSec Γ t) := by
  haveI := Γ.separated
  haveI := Γ.gen_reduced
  have hcl : ∀ s, IsClosedImmersion (genSec Γ s) := fun s => by
    haveI : IsClosedImmersion (genSec Γ s ≫ pullback.snd _ _) := by rw [genSec_snd]; infer_instance
    exact IsClosedImmersion.of_comp _ (pullback.snd Γ.G.hom (genPt R).hom)
  haveI : Subsingleton ↥(Spec (CommRingCat.of (FractionRing R))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing R)))
  let z₀ : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  haveI : Finite ↥(pullback Γ.G.hom (genPt R).hom) :=
    Finite.of_surjective (fun s => genSec Γ s z₀) fun a => by
      obtain ⟨s, z, rfl⟩ := genSec_cover Γ a
      exact ⟨s, by rw [Subsingleton.elim z z₀]⟩
  haveI : T1Space ↥(pullback Γ.G.hom (genPt R).hom) := ⟨fun a => by
    obtain ⟨s, z, rfl⟩ := genSec_cover Γ a
    haveI := hcl s
    have := (genSec Γ s).isClosedEmbedding.isClosedMap {z} (isClosed_discrete _)
    rwa [Set.image_singleton] at this⟩
  let U : (pullback Γ.G.hom (genPt R).hom).Opens := ⟨{genSec Γ t z₀}, isOpen_discrete _⟩
  have hU : Set.range (genSec Γ t) ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim z z₀]
    exact rfl
  have e := IsOpenImmersion.lift_fac U.ι (genSec Γ t) hU
  haveI : IsClosedImmersion (IsOpenImmersion.lift U.ι (genSec Γ t) hU ≫ U.ι) := by rw [e]; exact hcl t
  haveI : IsClosedImmersion (IsOpenImmersion.lift U.ι (genSec Γ t) hU) := IsClosedImmersion.of_comp _ U.ι
  haveI : Surjective (IsOpenImmersion.lift U.ι (genSec Γ t) hU) := ⟨fun u => ⟨z₀, by
    apply U.ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, e]
    exact (u.2 : u.1 = _).symm⟩⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (IsOpenImmersion.lift U.ι (genSec Γ t) hU)
  rw [← e]
  infer_instance

variable {R' : Type} [CommRing R'] [IsDomain R']

noncomputable def fracMap {φ : R →+* R'} (hφ : Function.Injective φ) : FractionRing R →+* FractionRing R' :=
  IsFractionRing.lift (g := (algebraMap R' (FractionRing R')).comp φ)
    ((IsFractionRing.injective R' (FractionRing R')).comp hφ)

theorem fracMap_comp {φ : R →+* R'} (hφ : Function.Injective φ) :
    (fracMap hφ).comp (algebraMap R (FractionRing R)) = (algebraMap R' (FractionRing R')).comp φ := by
  refine RingHom.ext fun a => ?_
  rw [RingHom.comp_apply, fracMap, IsFractionRing.lift_algebraMap]

theorem fracMap_sq {φ : R →+* R'} (hφ : Function.Injective φ) :
    spMap (fracMap hφ) ≫ (genPt R).hom = (genPt R').hom ≫ spMap φ := by
  show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, fracMap_comp]

noncomputable def bcPt (Γ : QFGroup R T) {φ : R →+* R'} (hφ : Function.Injective φ) (t : T) :
    genPt R' ⟶ (Over.pullback (spMap φ)).obj Γ.G :=
  Over.homMk (pullback.lift (spMap (fracMap hφ) ≫ (Γ.pt t).left) (genPt R').hom (by
    rw [Category.assoc, Over.w (Γ.pt t), fracMap_sq])) (pullback.lift_snd _ _ _)

theorem bcPt_fst (Γ : QFGroup R T) {φ : R →+* R'} (hφ : Function.Injective φ) (t : T) :
    (bcPt Γ hφ t).left ≫ pullback.fst Γ.G.hom (spMap φ) = spMap (fracMap hφ) ≫ (Γ.pt t).left :=
  pullback.lift_fst _ _ _

theorem bcPt_mul (Γ : QFGroup R T) {φ : R →+* R'} (hφ : Function.Injective φ) (s t : T) :
    bcPt Γ hφ (s * t) = bcPt Γ hφ s * bcPt Γ hφ t := by
  have h := isGrpPullback_pullback Γ.G (spMap φ)
  let U : Over.mk ((genPt R').hom ≫ spMap φ) ⟶ genPt R := Over.homMk (spMap (fracMap hφ)) (fracMap_sq hφ)
  refine Over.OverMorphism.ext (h.1.hom_ext ?_ ?_)
  · rw [← h.2 (genPt R') (bcPt Γ hφ s) (bcPt Γ hφ t) (U ≫ Γ.pt s) (U ≫ Γ.pt t) (bcPt_fst Γ hφ s).symm
      (bcPt_fst Γ hφ t).symm, ← MonObj.comp_mul, ← map_mul]
    exact bcPt_fst Γ hφ _
  · exact (Over.w _).trans (Over.w _).symm

noncomputable def bcSec (Γ : QFGroup R T) {φ : R →+* R'} (hφ : Function.Injective φ) (t : T) :
    Spec (CommRingCat.of (FractionRing R')) ⟶ pullback (pullback.snd Γ.G.hom (spMap φ)) (genPt R').hom :=
  pullback.lift (bcPt Γ hφ t).left (𝟙 _) (by rw [Category.id_comp]; exact Over.w (bcPt Γ hφ t))

theorem bcSec_spec [Finite T] (Γ : QFGroup R T) {φ : R →+* R'} (hφ : Function.Injective φ) :
    (∀ t, IsOpenImmersion (bcSec Γ hφ t)) ∧ ∀ a, ∃ t z, bcSec Γ hφ t z = a := by
  let q : pullback (pullback.snd Γ.G.hom (spMap φ)) (genPt R').hom ⟶ pullback Γ.G.hom (genPt R).hom :=
    pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ spMap (fracMap hφ)) (by
      rw [Category.assoc, Category.assoc, fracMap_sq, pullback.condition, pullback.condition_assoc])
  have hq₁ : q ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := pullback.lift_fst _ _ _
  have hq₂ : q ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (fracMap hφ) := pullback.lift_snd _ _ _
  have big := (IsPullback.of_hasPullback (pullback.snd Γ.G.hom (spMap φ)) (genPt R').hom).paste_horiz
    (IsPullback.of_hasPullback Γ.G.hom (spMap φ))
  rw [← hq₁, ← fracMap_sq hφ] at big
  have hq : IsPullback q (pullback.snd _ _) (pullback.snd _ _) (spMap (fracMap hφ)) :=
    big.of_right hq₂ (IsPullback.of_hasPullback Γ.G.hom (genPt R).hom)
  have hs : ∀ t, IsPullback (spMap (fracMap hφ)) (bcSec Γ hφ t) (genSec Γ t) q := fun t => by
    have e₁ : bcSec Γ hφ t ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have e₂ : bcSec Γ hφ t ≫ pullback.fst _ _ = (bcPt Γ hφ t).left := pullback.lift_fst _ _ _
    refine IsPullback.of_bot ?_ ?_ hq
    · rw [e₁, genSec_snd]
      exact IsPullback.of_vert_isIso ⟨by simp⟩
    · refine pullback.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, genSec_fst, hq₁, reassoc_of% e₂, bcPt_fst]
      · rw [Category.assoc, Category.assoc, genSec_snd, hq₂, reassoc_of% e₁, Category.comp_id]
  refine ⟨fun t => ?_, fun a => ?_⟩
  · haveI := genSec_open Γ t
    exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hs t) this
  · obtain ⟨t, z, hz⟩ := genSec_cover Γ (q a)
    obtain ⟨w, -, hw⟩ := Scheme.exists_preimage_of_isPullback (hs t) z a hz
    exact ⟨t, w, hw⟩

noncomputable def bcGroup [Finite T] (Γ : QFGroup R T) {φ : R →+* R'} (hφ : Function.Injective φ) : QFGroup R' T where
  G := (Over.pullback (spMap φ)).obj Γ.G
  flat := haveI := Γ.flat; inferInstanceAs (Flat (pullback.snd Γ.G.hom (spMap φ)))
  quasiFinite := haveI := Γ.quasiFinite; inferInstanceAs (LocallyQuasiFinite (pullback.snd Γ.G.hom (spMap φ)))
  separated := haveI := Γ.separated; inferInstanceAs (IsSeparated (pullback.snd Γ.G.hom (spMap φ)))
  quasiCompact := haveI := Γ.quasiCompact; inferInstanceAs (QuasiCompact (pullback.snd Γ.G.hom (spMap φ)))
  finPres := haveI := Γ.finPres; inferInstanceAs (LocallyOfFinitePresentation (pullback.snd Γ.G.hom (spMap φ)))
  pt := MonoidHom.mk' (bcPt Γ hφ) (bcPt_mul Γ hφ)
  pt_inj s t x y h := by
    refine Γ.pt_inj s t (spMap (fracMap hφ) x) (spMap (fracMap hφ) y) ?_
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← bcPt_fst, ← bcPt_fst, Scheme.Hom.comp_apply,
      Scheme.Hom.comp_apply]
    exact congrArg _ h
  pt_onto g hg := by
    let z₀ : Spec (CommRingCat.of (FractionRing R')) := IsLocalRing.closedPoint (FractionRing R')
    obtain ⟨a, ha, -⟩ := Scheme.exists_preimage_of_isPullback
      (IsPullback.of_hasPullback (pullback.snd Γ.G.hom (spMap φ)) (genPt R').hom) g z₀
      (PrimeSpectrum.ext (hg.trans (gen_asIdeal z₀).symm))
    obtain ⟨t, z, rfl⟩ := (bcSec_spec Γ hφ).2 a
    refine ⟨t, z, ?_⟩
    rw [← ha, ← Scheme.Hom.comp_apply]
    have e₂ : bcSec Γ hφ t ≫ pullback.fst _ _ = (bcPt Γ hφ t).left := pullback.lift_fst _ _ _
    rw [e₂]
    rfl
  gen_reduced := by
    haveI : ∀ a : ↥(pullback (pullback.snd Γ.G.hom (spMap φ)) (genPt R').hom),
        _root_.IsReduced ((pullback (pullback.snd Γ.G.hom (spMap φ)) (genPt R').hom).presheaf.stalk a) := fun a => by
      obtain ⟨t, z, rfl⟩ := (bcSec_spec Γ hφ).2 a
      haveI := (bcSec_spec Γ hφ).1 t
      exact isReduced_of_injective ((bcSec Γ hφ t).stalkMap z).hom
        (ConcreteCategory.bijective_of_isIso ((bcSec Γ hφ t).stalkMap z)).1
    exact isReduced_of_isReduced_stalk (pullback (pullback.snd Γ.G.hom (spMap φ)) (genPt R').hom)

theorem bt_exists_bc : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R'), Function.Injective φ → ∃ (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ φ F := by
  intro R _ _ T _ _ Γ R' _ _ φ hφ
  have h := isGrpPullback_pullback Γ.G (spMap φ)
  refine ⟨bcGroup Γ hφ, pullback.fst Γ.G.hom (spMap φ), h.1, h.2, FractionRing R, inferInstance, algebraMap R _,
    RingHom.id _, fracMap hφ, fun t => (Γ.pt t).left, Function.injective_id, rfl, fracMap_comp hφ,
    fun t => Over.w (Γ.pt t), fun t => ?_, fun t => (bcPt_fst Γ hφ t).symm⟩
  rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

end PositivityTheory.UnitarySelfGeneration
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M GlobalTheory.CompanionTheory.Ar.Cmp Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)} {e : ℕ}
  {Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}

theorem ptsat_segre (z : (Σ k, ι k) → ℂ) : segre (star z) = star (segre z) := by
  funext i
  simp [segre]

theorem ptsat_cons (y : Fin e → ℂ) : star (Fin.cons 1 y : Fin (e + 1) → ℂ) = Fin.cons 1 (star y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem ptsat_mem {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : star z ∈ mcPts P :=
  ((GlobalTheory.T.complex_conjugation_herm_compat K ι).1 P z).2 hz

theorem ptsat_symm (h : ∀ w, Ψ' w = star (Ψ (star w))) (w) : Ψ w = star (Ψ' (star w)) := by
  rw [h, star_star, star_star]

theorem ptsat_fibre (h : ∀ w, Ψ' w = star (Ψ (star w))) {y w} (hw : w ∈ fibre P Ψ' y) :
    star w ∈ fibre P Ψ (star y) := by
  obtain ⟨z, hz, rfl, h2⟩ := hw
  exact ⟨star z, ptsat_mem hz, ptsat_segre z, by rw [ptsat_symm h, star_star, h2, ptsat_cons]⟩

theorem ptsat_sheet (h : ∀ w, Ψ' w = star (Ψ (star w))) {y w γ} (hγ : IsSheet P Ψ' y w γ) :
    IsSheet P Ψ (star y) (star w) (star ∘ γ ∘ star) := by
  refine ⟨by simp only [Function.comp_apply, star_star, ptsat_segre, hγ.1], ?_⟩
  have ht : Tendsto (star : (Fin e → ℂ) → Fin e → ℂ) (𝓝 (star y)) (𝓝 y) := by
    simpa using (continuous_star (R := Fin e → ℂ)).tendsto (star y)
  filter_upwards [ht.eventually hγ.2] with y' hy'
  refine ⟨by simpa using hy'.1.star_star, ptsat_mem hy'.2.1, ?_⟩
  rw [ptsat_symm h, Function.comp_apply, Function.comp_apply, ptsat_segre, star_star, hy'.2.2, ptsat_cons,
    star_star]

end

theorem c_ptsat : SheetIndepStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (A : HermLine ι) (s : MRing ι), IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ w i, Ψ' w i = starRingEnd ℂ (Ψ (fun c => starRingEnd ℂ (w c)) i)) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSectionOn P A s → IsGoodProj P Ψ' ∧ ptsIntegralAt P Ψ' (pot fun j => conjLine (L j)) (logNorm (conjLine A) s) = ptsIntegralAt P Ψ (pot L) (logNorm A s) := by
  intro hS K _ ι _ P e Ψ Ψ' L A s hP hΨ h0 hL hA hs
  have h : ∀ w, Ψ' w = star (Ψ (star w)) := fun w => funext (h0 w)
  refine ⟨fun z hz h1 => hΨ _ (ptsat_mem hz) (by rw [ptsat_symm h, ptsat_segre, star_star, h1, star_zero]), ?_⟩
  have hm : MeasureTheory.MeasurePreserving (star : (Fin e → ℂ) → Fin e → ℂ) :=
    MeasureTheory.volume_preserving_pi fun _ => Complex.conjLIE.measurePreserving
  have he : MeasurableEmbedding (star : (Fin e → ℂ) → Fin e → ℂ) :=
    (starL' ℝ : (Fin e → ℂ) ≃L[ℝ] (Fin e → ℂ)).toHomeomorph.measurableEmbedding
  unfold ptsIntegralAt
  rw [← hm.integral_comp he (fun y => ∑ᶠ w ∈ fibre P Ψ y, sheetDensity P Ψ (pot L) (logNorm A s) y w)]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hm.quasiMeasurePreserving.ae (hS K ι P e Ψ L A s hP hΨ hL hA hs)] with y hy
  refine finsum_mem_eq_of_bijOn star ⟨fun w hw => ptsat_fibre h hw, star_injective.injOn, fun w hw =>
    ⟨star w, by simpa using ptsat_fibre (ptsat_symm h) hw, star_star w⟩⟩ fun w _ => ?_
  unfold sheetDensity
  by_cases h1 : ∃ γ, IsSheet P Ψ' y w γ
  · have h2 : ∃ γ, IsSheet P Ψ (star y) (star w) γ := ⟨_, ptsat_sheet h h1.choose_spec⟩
    rw [dite_eq_left h1, dite_eq_left h2, hy _ _ _ h2.choose_spec (ptsat_sheet h h1.choose_spec),
      (GlobalTheory.T.complex_conjugation_herm_compat K ι).2.2.2.1]
    have h3 := c_madens e (fun j y' => pot L j ((star ∘ h1.choose ∘ star) y')) y
    congr 1
    · simp only [Function.comp_apply, star_star]
      rfl
    · refine Eq.trans ?_ h3
      congr 1
      funext j y'
      show _ = pot L j (star (h1.choose (star (star y'))))
      rw [star_star]
      rfl
  · have h2 : ¬ ∃ γ, IsSheet P Ψ (star y) (star w) γ := fun ⟨γ, hγ⟩ =>
      h1 ⟨_, by simpa only [star_star] using ptsat_sheet (ptsat_symm h) hγ⟩
    rw [dite_eq_right h1, dite_eq_right h2]

end PositivityTheory.UnitarySelfGeneration
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_iso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : HostAut H), Nonempty (TwIso D g) := by
  intro E _ _ _ H D g
  have := D.fin
  have := D.proj
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.twisted_module_finite_projective_rank (𝓞 E) g.s D.La
  have := finite_int_of_finite_ringOfIntegers E D.La
  have := finite_int_of_finite_ringOfIntegers E (TwMod g.s D.La)
  have := free_int_of_projective_ringOfIntegers E D.La
  have := free_int_of_projective_ringOfIntegers E (TwMod g.s D.La)
  refine GlobalTheory.T.pro_isometry_of_local_isometries (𝓞 E) D.La (TwMod g.s D.La) D.EF (twForm D g) fun p hp => ?_
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨φ, k1, k2⟩ := tw_g_padic E H.bar H.bar_eq H.unram p D.La (TwMod g.s D.La) D.EF (twForm D g) h3.symm D.alt
    D.unimod D.adj D.alt D.unimod fun a x y => (D.adj (g.s a) x y).trans (by rw [← g.s_bar]; rfl)
  exact GlobalTheory.T.padic_isometry_equivariance p (𝓞 E) D.La (TwMod g.s D.La) D.EF (twForm D g) φ k1 k2

end PositivityTheory.UnitarySelfGeneration
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace PositivityTheory.UnitarySelfGeneration

theorem tw_ok : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (g : HostAut H) (a : TwIso D g), TwOK o g a := by
  intro E _ _ _ H D l B _ b S s o g a
  obtain ⟨hm1, hm2⟩ := tw_mb E H l g
  refine ⟨fun x hx => o.eta_ker _ (tw_sub _ g.s D.La (a.a l.M) l.Mb hm1.le x hx), fun k _ _ x β hx => ?_⟩
  obtain ⟨hd, I, h1, h2, h3⟩ := o.geom k x β hx
  obtain ⟨J, hJ1, hJ2⟩ := tw_tate E H D g a k _ _ _ I
  refine ⟨tw_det E H D g S _ _ k x _ hd, J, by rw [hJ1]; exact h1, fun y => ?_, fun y hy => ?_⟩
  · rw [hJ2]
    exact h2 _
  · rw [hJ2]
    exact h3 _ (tw_sub _ g.s D.La (a.a l.M) _ hm2.le y hy)

end PositivityTheory.UnitarySelfGeneration
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

namespace PositivityTheory.UnitarySelfGeneration

open HolomorphicMinorCharts in
theorem r_holmap : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e e' : ℕ) (X Y : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [TopologicalSpace Y] (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (U : X → Set X) (lam : X → X → (Σ k, ι k) → ℂ) (V : Y → Set Y) (mu : Y → Y → (Σ k, ι k) → ℂ), IsEmbedded A P U lam → (∀ y, IsOpen (V y) ∧ y ∈ V y) → (∀ y p, B.HoloOn (V y) fun y' => mu y y' p) → (∀ y, ∀ y' ∈ V y, mu y y' ∈ mcPts P) → (∀ y y', ∀ w ∈ V y ∩ V y', SameOrbit (mu y w) (mu y' w)) → ∃ π : Y → X, HoloMap B A π ∧ ∀ y, SameOrbit (lam (π y) (π y)) (mu y y) := by
  intro K _ ι _ P e e' X Y _ _ _ _ A B U lam V mu hE hV hm hmem hc
  choose π hπ using fun y => hE.surj (mu y y) (hmem y y (hV y).2)
  have hcl := isClosed_minors (U := U) (lam := lam) (V := V) (mu := mu) (fun x => ⟨hE.isOpen x, hE.mem_U x⟩)
    (fun x p => holo_continuousAt (hE.holo x p) (hE.mem_U x)) hE.compat hV
    (fun y p => holo_continuousAt (hm y p) (hV y).2) hc
  have hcont : ∀ y, ContinuousAt π y := fun y =>
    continuousAt_of_closed_rel hcl (fun y => minors_of_so (hπ y)) fun x hx =>
      hE.inj _ _ (so_trans (so_of_minors hx (hE.mem x x (hE.mem_U x)).1 (hmem y y (hV y).2).1) (so_symm (hπ y)))
  refine ⟨π, ⟨continuous_iff_continuousAt.mpr hcont, fun j k w hw => ?_⟩, hπ⟩
  set y := (B.chart j).symm w with hy
  have h := analyticAt_factor (A := A) (B := B) (U := U (π y)) (lam := lam (π y)) (V := V y) (mu := mu y) (π := π)
    (y := y) (hE.holo _) (hE.mem_U _) (hm y) (hV y).2 (hcont y) (hE.mem _ _ (hE.mem_U _)).1 (hE.immersion (π y))
    (by
      filter_upwards [(hV y).1.mem_nhds (hV y).2, hcont y ((hE.isOpen _).mem_nhds (hE.mem_U (π y)))] with w' h1 h2
      exact so_trans (hE.compat _ _ _ ⟨h2, hE.mem_U _⟩) (so_trans (hπ w') (hc _ _ _ ⟨(hV _).2, h1⟩)))
    j k ((B.chart j).map_target hw.1) hw.2
  rwa [hy, (B.chart j).right_inv hw.1] at h

end PositivityTheory.UnitarySelfGeneration
end
