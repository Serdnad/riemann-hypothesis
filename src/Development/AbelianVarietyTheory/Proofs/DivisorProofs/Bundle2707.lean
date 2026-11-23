module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.NormalisedBlowupCone
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle633
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle632
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitMulClauseOfGeneratesIffNonzero
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasiRegularSeqOfIsFreeGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2683
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LiePush
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.GeneratorPullback.PullAlong
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheaf
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieLift

theorem grpPullback_self {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem isLieBasis_cast {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n m : ℕ} (h : n = m)
    {w : Fin m → (epsR R ⟶ G)} (hw : IsLieBasis w) : IsLieBasis (fun j : Fin n => w (j.cast h)) := by
  subst h
  simpa using hw

theorem dual_eq_id {K : Type} [Field K] (F : DualNumber K →+* DualNumber K)
    (h₁ : ∀ a, F (algebraMap K _ a) = algebraMap K _ (RingHom.id K a)) (h₂ : F DualNumber.eps = DualNumber.eps) :
    F = RingHom.id _ := by
  let Fa : DualNumber K →ₐ[K] DualNumber K := { F with commutes' := h₁ }
  have : Fa = AlgHom.id K _ := DualNumber.algHom_ext h₂
  exact RingHom.ext fun z => congrArg (fun q : DualNumber K →ₐ[K] DualNumber K => q z) this

theorem main : ∀ (K : Type) [Field K] (G : Over (Sp K)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ σ' : L.L.Sec) (x x' : KeyIn K) (hg' : x'.P.g = x.P.g) (y y' : Fin x.P.g → (epsR K ⟶ G)) (M : Matrix (Fin x.P.g) (Fin x.P.g) K), KeyOn (RingHom.id K) x G L σ y → KeyOn (RingHom.id K) x' G L σ' (fun i => y' (i.cast hg')) → (∀ i, IsLieComb (M i) y (y' i)) → ∃ (v : Fin x.P.g → (epsR K ⟶ x.P.A)) (hv : IsLieBasis v), (∀ i, IsLieComb (M i) x.v (v i)) ∧ KeyOn (RingHom.id K) ⟨x.P, x.g_pos, x.rig, x.rig_gen, x.th, x.th_ne, v, hv⟩ G L σ y' := by
  intro K _ G _ _ L σ σ' x x' hg' y y' M hx hx' hM
  obtain ⟨φ, he, ψ, F, hφ, hψ, hmaps, hsec, hF₁, hF₂, hxv⟩ := hx
  obtain ⟨φ', -, -, F', hφ', -, -, -, hF₁', hF₂', hxv'⟩ := hx'
  have e : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id _
  have e' : spMap (RingHom.id (DualNumber K)) = 𝟙 (Sp (DualNumber K)) := Spec.map_id _
  have hF := dual_eq_id F hF₁ hF₂
  have hF' := dual_eq_id F' hF₁' hF₂'
  subst hF hF'
  have eR : spMap (Chart.dualMapR (RingHom.id K)) = 𝟙 (Sp (DualNumber K)) := by
    refine Eq.trans (congrArg spMap (RingHom.ext fun z => ?_)) e'
    ext <;> simp [Chart.dualMapR]

  have hw : ∀ i, (y' i).left ≫ G.hom = (epsR K).hom ≫ spMap (RingHom.id K) := fun i => by
    rw [e, Category.comp_id]; exact Over.w (y' i)
  let v : Fin x.P.g → (epsR K ⟶ x.P.A) := fun i => Over.homMk (hφ.1.lift (y' i).left (epsR K).hom (hw i))
    (hφ.1.lift_snd _ _ _)
  have hvφ : ∀ i, (v i).left ≫ φ = (y' i).left := fun i => hφ.1.lift_fst _ _ _

  let χ : x.P.A.left ⟶ x'.P.A.left := hφ'.1.lift φ x.P.A.hom hφ.1.w
  have hχ : χ ≫ φ' = φ := hφ'.1.lift_fst _ _ _
  have hχ' : χ ≫ x'.P.A.hom = x.P.A.hom ≫ spMap (RingHom.id K) := by
    rw [hφ'.1.lift_snd, e, Category.comp_id]
  have hn : IsGrpPullback x.P.A G (spMap (RingHom.id K) ≫ spMap (RingHom.id K)) (χ ≫ φ') := by
    rw [hχ, e, Category.comp_id, ← e]; exact hφ
  have hC : IsGrpPullback x.P.A x'.P.A (spMap (RingHom.id K)) χ := IsGrpPullback.cancel hφ' hn hχ'
  have := x'.P.isAb.smooth
  have hvχ : ∀ j, (v j).left ≫ χ = spMap (Chart.dualMapR (RingHom.id K)) ≫ (x'.v (j.cast hg'.symm)).left := by
    intro j
    apply hφ'.1.hom_ext
    · rw [Category.assoc, hχ, hvφ, eR, Category.id_comp, hxv', e', Category.id_comp]
      simp
    · rw [Category.assoc, hχ', ← Category.assoc, Over.w (v j), eR, Category.id_comp, Over.w (x'.v _), e,
        Category.comp_id]
  have hv : IsLieBasis v := Chart.isLieBasis_baseChange (RingHom.id K) hC
    (isLieBasis_cast hg'.symm x'.basis) hvχ
  refine ⟨v, hv, fun i => ?_, φ, he, ψ, RingHom.id _, hφ, hψ, hmaps, hsec, hF₁, hF₂, fun i => ?_⟩
  · apply Chart.comb_baseChange (RingHom.id K) hφ (hM i)
    · intro j
      rw [hxv, e', Category.id_comp, eR, Category.id_comp]
    · rw [hvφ, eR, Category.id_comp]
  · rw [hvφ, e', Category.id_comp]

end GlobalTheory.LieLift
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.KeyVals

variable {S : Scheme.{0}}

abbrev FF (S : Scheme.{0}) [IsIntegral S] : Type := S.presheaf.stalk (genericPoint S)

instance fieldFF (S : Scheme.{0}) [IsIntegral S] : Field (FF S) := inferInstanceAs (Field S.functionField)

def genPt (S : Scheme.{0}) [IsIntegral S] : Sp (FF S) ⟶ S := S.fromSpecStalk (genericPoint S)

theorem genPt_le [IsIntegral S] (U : S.Opens) (h : genericPoint S ∈ U) : ⊤ ≤ genPt S ⁻¹ᵁ U := by
  intro p _
  have hp : (genPt S).base p ∈ Set.range (S.fromSpecStalk (genericPoint S)).base := ⟨p, rfl⟩
  rw [Scheme.range_fromSpecStalk] at hp
  exact hp.mem_open U.isOpen h

theorem spMap_germ_fromSpec [IsIntegral S] (W : S.Opens) (hW : IsAffineOpen W) (h : genericPoint S ∈ W) :
    spMap (S.presheaf.germ W (genericPoint S) h).hom ≫ hW.fromSpec = genPt S :=
  hW.fromSpecStalk_eq_fromSpecStalk h

abbrev bG {R : Type} [CommRing R] (G : Over S) (ξ : Sp R ⟶ S) : Over (Sp R) := (Over.pullback ξ).obj G

instance isCommMonObj_bG {R : Type} [CommRing R] (G : Over S) [GrpObj G] [IsCommMonObj G] (ξ : Sp R ⟶ S) :
    IsCommMonObj (bG G ξ) := Functor.isCommMonObj_obj

def eb {R : Type} [CommRing R] (ξ : Sp R ⟶ S) : (𝟙_ (Over (Sp R))).left ⟶ (𝟙_ (Over S)).left := ξ

theorem eSec_bG {R : Type} [CommRing R] (G : Over S) [GrpObj G] (ξ : Sp R ⟶ S) :
    eSec (bG G ξ) ≫ pullback.fst G.hom ξ = eb ξ ≫ eSec G :=
  LieVB.unitSec_comp (isGrpPullback_pullback G ξ)

def bL {R : Type} [CommRing R] {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) (ξ : Sp R ⟶ S) :
    RigLB (bG G ξ) where
  L := L.L.pull (pullback.fst G.hom ξ)
  rig := rigPullOf (G' := bG G ξ) (G := G) (pullback.fst G.hom ξ) (eb ξ) (eSec_bG G ξ) L.L L.rig
  isLB := LB.isLB_pull L.isLB _
  rigGen := LBxP.isGen_pullAlong L.L (pullback.fst G.hom ξ) (eb ξ) (fun _ : PUnit => eSec G) (fun _ => 1)
    (fun _ => eSec (bG G ξ)) (fun _ => eSec_bG G ξ) L.rig L.rigGen

def IsLocSec {R : Type} [CommRing R] {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {δ : LB S}
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (ξ : Sp R ⟶ S) (s : (bL L ξ).L.Sec) : Prop :=
  ∀ (j : (bL L ξ).L.ι) (h : (bL L ξ).L.U j ≤
      pullback.fst G.hom ξ ⁻¹ᵁ (CechPic.tens L.L (δ.pull G.hom)).U (j PUnit.unit, fun _ => i)),
    s.f j = ((pullback.fst G.hom ξ).appLE _ _ h).hom (σ.f (j PUnit.unit, fun _ => i))

def pfr {R : Type} [CommRing R] {G : Over S} [GrpObj G] {g : ℕ} (c : VB.Chart (LieVB.omega G) g) (ξ : Sp R ⟶ S)
    (hc : ⊤ ≤ ξ ⁻¹ᵁ c.U) (k : Fin g) : Γ(LieVB.omega (bG G ξ), ⊤) :=
  (LieVB.omegaBase (isGrpPullback_pullback G ξ)).app ⊤ (QCoh.pullbackSections ξ (LieVB.omega G) hc (c.e k))

def IsDual {R : Type} [CommRing R] {G : Over S} [GrpObj G] {g : ℕ} (c : VB.Chart (LieVB.omega G) g)
    (ξ : Sp R ⟶ S) (y : Fin g → (epsR R ⟶ bG G ξ)) : Prop :=
  ∃ hc : ⊤ ≤ ξ ⁻¹ᵁ c.U, ∀ j, ∃ v : Pdiv.LieG (bG G ξ), v.1 = y j ∧ ∀ k,
    VB.dualApp (LieVB.tangent v) le_top (pfr c ξ hc k) = if j = k then 1 else 0

def IsKeyVal (κ : Rule) [IsIntegral S] [CharZero (FF S)] {G : Over S} [GrpObj G] [IsCommMonObj G] (g : ℕ) (L : RigLB G)
    {δ : LB S} (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (c : VB.Chart (LieVB.omega G) g) (i : δ.ι) (v : FF S) : Prop :=
  ∃ (s : (bL L (genPt S)).L.Sec) (y : Fin g → (epsR (FF S) ⟶ bG G (genPt S))) (x : KeyIn (FF S)) (hg : x.P.g = g),
    IsLocSec σ i (genPt S) s ∧ IsDual c (genPt S) y ∧
    KeyOn (RingHom.id (FF S)) x (bG G (genPt S)) (bL L (genPt S)) s (fun j => y (j.cast hg)) ∧ v = κ (FF S) x

end GlobalTheory.KeyVals

end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

namespace GlobalTheory.NormBlLift

theorem effCartier_comap_of_idlAlong {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] (a : Sp R ⟶ X) (f : R) (hf : f ≠ 0) (hJ : idlAlong J a = Ideal.span {f}) :
    FinalTheorems.EffCartier (J.comap a) := by
  rw [idlAlong_eq_idealAlong, GlobalTheory.IndefiniteRowSideFullHecke.NormalisedBlowupCone.idealAlong] at hJ
  set e := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv with he
  have hI : (J.comap a).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {e.symm f} := by
    have h2 := congrArg (Ideal.map e.symm.toRingHom) hJ
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_map] at h2
    have : e.symm.toRingHom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom = RingHom.id _ := by
      ext x; exact e.symm_apply_apply x
    rw [this, Ideal.map_id] at h2
    exact h2
  intro x
  refine ⟨⟨⊤, isAffineOpen_top _⟩, e.symm f, trivial, ?_, hI⟩
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · apply e.injective
    have := congrArg e hz
    rw [map_mul, map_zero, e.apply_symm_apply] at this
    rw [map_zero]; exact (mul_eq_zero.1 this).resolve_left hf
  · apply e.injective
    have := congrArg e hz
    rw [map_mul, map_zero, e.apply_symm_apply] at this
    rw [map_zero]; exact (mul_eq_zero.1 this).resolve_right hf

end GlobalTheory.NormBlLift

namespace GlobalTheory.NormBlLift

theorem lift_normBl : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z S : Scheme.{0}) (i : F.X ⟶ Z) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] [IsOpenImmersion i] (J : Z.IdealSheafData), IsNormBl π J → j ≫ π = i → π ⁻¹' Set.range i = Set.range j → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (a : Sp R ⟶ Z) (y : Sp (FractionRing R) ⟶ F.X), jK R ≫ a = y ≫ i → ∀ f : R, f ≠ 0 → idlAlong J a = Ideal.span {f} → ∃! ξ : Sp R ⟶ S, ξ ≫ π = a := by
  intro g n F Z S i π j _ _ J hN hji hpre R _ _ _ _ _ a y hy f hf hJ
  obtain ⟨-, S₀, π₀, ν, U, hB, hνπ, hfin, -, -, -⟩ := hN
  have hE : FinalTheorems.EffCartier (J.comap a) := effCartier_comap_of_idlAlong J a f hf hJ
  have hEK : FinalTheorems.EffCartier (J.comap (jK R ≫ a)) := by
    refine effCartier_comap_of_idlAlong J (jK R ≫ a) (algebraMap R (FractionRing R) f) ?_ ?_
    · exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hf
    · rw [show jK R = spMap (algebraMap R (FractionRing R)) from rfl, GlobalTheory.TraitOrder.idlAlong_comp, hJ,
        Ideal.map_span, Set.image_singleton]
  obtain ⟨b, hb, hbu⟩ := hB.2 _ a hE
  have hK : (y ≫ j) ≫ ν = jK R ≫ b := by
    refine (hB.2 _ _ hEK).unique ?_ ?_
    · rw [Category.assoc, Category.assoc, hνπ, hji, hy]
    · rw [Category.assoc, hb]
  have L := GlobalTheory.existsUnique_lift_spec_of_isLocalization (nonZeroDivisors R) le_rfl ν (y ≫ j) b hK
  obtain ⟨c, ⟨hc1, hc2⟩, -⟩ := L
  refine ⟨c, by show c ≫ π = a; rw [← hνπ, ← Category.assoc, hc2, hb], fun c' hc' => ?_⟩
  have h1 : c' ≫ ν = b := hbu _ (by show (c' ≫ ν) ≫ π₀ = a; rw [Category.assoc, hνπ]; exact hc')
  have hr : Set.range (jK R ≫ c') ⊆ Set.range j := by
    rintro _ ⟨w, rfl⟩
    rw [← hpre]
    show π ((jK R ≫ c') w) ∈ Set.range i
    rw [← Scheme.Hom.comp_apply, Category.assoc, hc', hy, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  have h2 : jK R ≫ c' = y ≫ j := by
    have hl := IsOpenImmersion.lift_fac j (jK R ≫ c') hr
    rw [← hl]
    congr 1
    rw [← cancel_mono i, ← hji, ← Category.assoc, hl, Category.assoc, hc', hy, hji]
  exact (GlobalTheory.existsUnique_lift_spec_of_isLocalization (nonZeroDivisors R) le_rfl ν (y ≫ j) b hK).unique ⟨h2, h1⟩ ⟨hc1, hc2⟩

end GlobalTheory.NormBlLift
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven.ThetaNorm

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D A G), ∀ (σ : U.LG.L.Sec) (σ₁ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α), NzFib σ → (∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i)) → (∀ e, U.ExpandsAt e 1 σ₁ f) → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (ϑ : Fam D.toPre C 1) (c : C), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C α) (DegPre.famε 1) (ϑ.s α) (D.toPre.famφB α) (DegPre.famε 1) (f α) (DegPre.prB D.toPre C).left 1) → ν.FamV ϑ (c • N.vth) → ‖c‖ = 1 := by
  intro V _ _ _ _ hc D A G _ _ hG U σ σ₁ f hNz hch hE C _ _ _ _ _ _ hC N ν hI ϑ c hϑ hV
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hL4 : Laws4 := GlobalTheory.allSixLaws.2.2.2.1
  have hS : SecBaseChangeSt := hL.secBaseChange
  have h1 : ReciprocityTheory.ChartRestriction.G.DVR.NonzeroOnSpecial U σ₁ := by
    obtain ⟨z, hz, hzn⟩ := hNz (IsLocalRing.closedPoint V)
    refine GlobalTheory.ThetaUnit.nonzeroOnSpecial_of_mem U σ₁ z hz ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hzn
    have hle : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i :=
      fun y hy => Set.mem_iInter.1 hy 0
    have hzi : z ∈ U.LG.L.U i := G.left.basicOpen_le _ hi
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, ?_⟩
    rw [hch i hle]
    change z ∈ G.left.basicOpen ((G.left.presheaf.map (homOfLE hle).op) (σ.f i))
    rw [Scheme.basicOpen_res]
    exact ⟨fun _ ⟨k, hk⟩ => hk ▸ hzi, hi⟩
  have hCL : CLND V := (GlobalTheory.ThetaCompare.clnd_iff_of_dvr V).2 hc
  obtain ⟨f', hf', hgen'⟩ := ReciprocityTheory.ChartRestriction.G.DVR.isTheta_of_nonzeroOnSpecial' hL hL4 hCL rfl U σ₁ h1 0
  have hgen := GlobalTheory.ThetaCompare.secBGenerates_of_expandsAt hS le_rfl U.toUnifPre hf' (hE 0) hgen'
  obtain ⟨g, hg⟩ := GlobalTheory.ThetaCompare.exists_corr_right D.toPre ν.th
  have hgg := (GlobalTheory.ThetaCompare.generates_iff_secBGenerates hS hg).1 (fun s => ν.th_gen s)
  have hgs := (GlobalTheory.ThetaCompare.secBGenerates_iff_smul (g : GlobalTheory.ConstFam.SecBMod D.toPre 1 0)).1 hgg
  have hfs := (GlobalTheory.ThetaCompare.secBGenerates_iff_smul ((f 0 : D.toPre.SecB 1 0) : GlobalTheory.ConstFam.SecBMod D.toPre 1 0)).1 hgen
  obtain ⟨u, hu⟩ := (GlobalTheory.ThetaCompare.generates_iff_unit_smul (fun s => (hgs s).exists) _).1 (fun s => (hfs s).exists)
  have hum : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul D.toPre.P.A.hom (u : V) (f 0) g :=
    (GlobalTheory.ThetaUnit.secIsMul_iff _ _ _ _).2 hu

  let z : Sp C := IsLocalRing.closedPoint C
  have hJ := GlobalTheory.Ex.FamVal.good ν z
  have hcst : ∀ a : C, cst (𝟙 (Sp C)) z a = toStk z a := fun a => by
    rw [cst, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_eq _ _ ⊤ trivial, toStk]
    rfl
  have hc0 : N.c 0 = 1 := by
    have h := N.c_add 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hx : ∀ x, c * N.th x * ν.rg = algebraMap (FractionRing V) C (algebraMap V _ (u : V)) * (N.th x * ν.rg) := by
    intro x
    have H := (GlobalTheory.Ex.FamVal.famV_iff ν z ϑ _).1 hV 0 x
    have e1 := ReciprocityTheory.ChartRestriction.G.H1.sval_scal (hϑ 0) (GlobalTheory.Ex.FamVal.pt ν x).left z hJ
    have e2 := GlobalTheory.IndivisibleSection.sval_of_secIsMul hum
      ((GlobalTheory.Ex.FamVal.pt ν x).left ≫ (DegPre.prB D.toPre C).left) z hJ
    have e3 := ReciprocityTheory.ChartRestriction.G.H1.sval_scal hg ((GlobalTheory.Ex.FamVal.pt ν x).left ≫ (DegPre.prB D.toPre C).left) z hJ
    have e4 : toStk z (N.th x * ν.rg) = sval ν.th (ν.eA x).left z ν.J :=
      (congrArg (toStk z) (ν.th_eq x)).trans (GlobalTheory.Ex.FamVal.toStk_sF hJ _ _)
    have ep : (GlobalTheory.Ex.FamVal.pt ν x).left ≫ (DegPre.prB D.toPre C).left = (ν.eA x).left := by
      rw [← Over.comp_left, lift_snd]
    rw [map_zero] at H
    rw [Category.comp_id, ep, ← e4] at e3
    rw [ep] at e2
    rw [e1, ep, e2, ← e3] at H
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, pow_one] at H
    have ec : cst ((ν.eA x).left ≫ D.toPre.P.A.hom) z (u : V) =
        toStk z (algebraMap (FractionRing V) C (algebraMap V _ (u : V))) := by
      have ew : (ν.eA x).left ≫ D.toPre.P.A.hom =
          (𝟙 (Sp C) ≫ spMap (algebraMap (FractionRing V) C)) ≫ spMap (algebraMap V (FractionRing V)) := by
        rw [Category.id_comp]; exact Over.w (ν.eA x)
      rw [ew, cst_comp, cst_comp, hcst]
    have ev : N.vth 0 x = N.th x := by
      simp [NumD.vth, N.ψ_zero, hc0]
    rw [ev, ← GlobalTheory.Ex.FamVal.rg_eq, ec, ← map_mul, ← map_mul] at H
    exact (toStk z).injective H
  have hL2 : Laws2 := GlobalTheory.abelianSchemeLaws_all.2
  have hB := GlobalTheory.Ex.brFam hL hL2 V D.toPre D.psi_even D.tau_bimult C N ν 1 le_rfl
  obtain ⟨x, hx0⟩ : ∃ x, N.th x ≠ 0 := by
    by_contra hno
    push_neg at hno
    obtain ⟨s, f0, hf0, hne⟩ := hB.2.2.2.1
    obtain ⟨c', hc'⟩ := hB.2.2.2.2.1 s f0 hf0
    refine hne ?_
    rw [hc']
    funext α y
    simp [NumD.vth, hno]
  have hcu : c = algebraMap (FractionRing V) C (algebraMap V _ (u : V)) := by
    have h := hx x
    rw [_root_.mul_assoc] at h
    exact mul_right_cancel₀ (mul_ne_zero hx0 (GlobalTheory.Ex.FamVal.rg_ne ν)) h
  have n1 := hC.1 (u : V)
  have n2 := hC.1 ((u⁻¹ : Vˣ) : V)
  have hprod : ‖algebraMap (FractionRing V) C (algebraMap V _ (u : V))‖ *
      ‖algebraMap (FractionRing V) C (algebraMap V _ ((u⁻¹ : Vˣ) : V))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  rw [hcu]
  nlinarith [norm_nonneg (algebraMap (FractionRing V) C (algebraMap V _ ((u⁻¹ : Vˣ) : V))),
    norm_nonneg (algebraMap (FractionRing V) C (algebraMap V _ (u : V)))]

end GlobalTheory.KeyEven.ThetaNorm
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.Poinc

theorem stalkId_finsetProd {X : Scheme.{0}} {ι : Type} (s : Finset ι) (K : ι → X.IdealSheafData) (x : X) :
    FinalTheorems.stalkId (∏ c ∈ s, K c) x = ∏ c ∈ s, FinalTheorems.stalkId (K c) x := by
  classical
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
  simp only [ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ _ x ⟨U, hU⟩ hx]
  induction s using Finset.induction_on with
  | empty => simp [Ideal.map_top]
  | insert c s hc ih =>
    rw [Finset.prod_insert hc, Finset.prod_insert hc, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul, ih]

theorem stalkId_prodPow {X : Scheme.{0}} {ι : Type} [Fintype ι] (K : ι → X.IdealSheafData) (e : ι → ℕ) (x : X) :
    FinalTheorems.stalkId (∏ c, K c ^ e c) x = ∏ c, FinalTheorems.stalkId (K c) x ^ e c := by
  rw [stalkId_finsetProd]
  simp only [GlobalTheory.Vanishing.stalkId_pow]

theorem exists_valOn_of_pieces : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S) (φ : InvFun ℤ) {ι : Type} [Fintype ι] (W : ι → Set S) (J : ι → S.IdealSheafData) (d : ι → ℕ), (∀ c, IsClopen (W c)) → (∀ x, ∃! c, x ∈ W c) → (∀ c, 1 ≤ d c) → (∀ c, ∀ x ∈ (J c).support, x ∈ W c ∧ x ∉ Set.range j) → (∀ c (T : Trait F) (ξ : Sp T.V ⟶ S), jK T.V ≫ ξ = T.y ≫ j → ξ (closedPoint T.V) ∈ W c → ∃ a : ℕ, (a : ℝ) = d c * φ.evalZ T.β ∧ idlAlong (J c) ξ = Ideal.span {T.ϖ ^ a}) → ∃ (d' : ℕ) (J' : S.IdealSheafData), 1 ≤ d' ∧ (∀ x ∈ J'.support, x ∉ Set.range j) ∧ ValOn F j φ J' d' := by
  intro o _ ζ g n F S j φ ι _ W J d _ huniq hd hsupp htr
  classical
  have hdvd : ∀ c, d c ∣ ∏ c, d c := fun c => Finset.dvd_prod_of_mem (s := Finset.univ) d (Finset.mem_univ c)
  have htop : ∀ c x, x ∉ W c → FinalTheorems.stalkId (J c) x = ⊤ := fun c x hx =>
    GlobalTheory.Vanishing.stalkId_eq_top (J c) fun hs => hx (hsupp c x hs).1
  refine ⟨∏ c, d c, ∏ c, J c ^ ((∏ c, d c) / d c), ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun c _ => by have := hd c; omega)
  · intro x hx
    obtain ⟨c, hc, -⟩ := huniq x
    by_cases hs : x ∈ (J c).support
    · exact (hsupp c x hs).2
    · exfalso
      refine (mem_support_iff_stalkId _ x).1 hx ?_
      rw [stalkId_prodPow, ← Ideal.one_eq_top]
      refine Finset.prod_eq_one fun c' _ => ?_
      by_cases e : c' = c
      · subst e; rw [GlobalTheory.Vanishing.stalkId_eq_top (J c') hs, ← Ideal.one_eq_top, one_pow]
      · rw [htop c' x fun h => e ((huniq x).unique h hc), ← Ideal.one_eq_top, one_pow]
  · intro T ξ hξ
    obtain ⟨c, hc, -⟩ := huniq (ξ (closedPoint T.V))
    obtain ⟨a, ha, hJ⟩ := htr c T ξ hξ hc
    refine ⟨(∏ c, d c) / d c * a, ?_, ?_⟩
    · have hd0 : (d c : ℝ) ≠ 0 := by have := hd c; positivity
      rw [Nat.cast_mul, Nat.cast_div (hdvd c) hd0, ha]
      field_simp
    · unfold idlAlong at hJ ⊢
      rw [stalkId_prodPow, Finset.prod_eq_single c, Ideal.map_pow, hJ, Ideal.span_singleton_pow, ← pow_mul, mul_comm]
      · intro c' _ e
        rw [htop c' _ fun h => e ((huniq _).unique h hc), ← Ideal.one_eq_top, one_pow]
      · intro h; exact absurd (Finset.mem_univ c) h

end GlobalTheory.Poinc
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem Trait.finrank_le : ∀ (g n : ℕ), 2 ≤ n → ∀ (F : SFam g n (zetaAway n)) (T : Trait F),
    Module.finrank ℤ T.D.toPre.X ≤ g := by
  intro g n hn F T
  have hn0 : n ≠ 0 := by omega
  have hζ : IsUnit (zetaAway n) := by rw [← cycBase_ζ hn0]; exact Units.isUnit _
  have hd : SmoothOfRelativeDimension g F.univ.A.hom :=
    GlobalTheory.SiegSharpCover.smoothDim F.univ hn hζ (isUnit_natCast hn0)
  have hA : SmoothOfRelativeDimension g T.A.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback T.cart.1 hd
  have e : T.A.g = g :=
    H1.dim_unique _ T.A.smoothDim hA ((η[T.A.A]).left (IsLocalRing.closedPoint _))
  have hR : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, T.complete⟩
  have h := GlobalTheory.TateUnif.rank_add_dim hR T.semi T.U
  omega

theorem Trait.finrank_le_of_three_le : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)), 3 ≤ n → ∀ T : Trait F,
    Module.finrank ℤ T.D.toPre.X ≤ g :=
  fun g n F hn T => Trait.finrank_le g n (by omega) F T

end GlobalTheory.Poinc
end
