module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsDegenerationDataExtensionOverDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle117
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle179
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle679
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle058
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle171
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle044
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveCubeBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiUnitOnAbelianLocusUniformisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle123
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle089
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle120
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle046
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
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
import Mathlib.RingTheory.Etale.Weakly
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle015
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullDegComp

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem exists_generic_lift {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {i : R →+* R'}
    (hi : Function.Injective i) {D : DegPre R} {D' : DegPre R'} (p : IsPullDeg i D D') :
    ∃ s : (TK R).left ⟶ p.W.toScheme, s ≫ p.W.ι = jK R := by
  have H : Set.range (jK R).base ⊆ Set.range p.W.ι.base := by
    rintro _ ⟨y, rfl⟩
    let z' : (TK R').left := (default : PrimeSpectrum (FractionRing R'))
    have e₁ : (genMap hi).base z' = y := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) _ _
    have e₂ : (jK R' ≫ spMap i).base z' = (genMap hi ≫ jK R).base z' := by
      rw [← fracMap_sq hi, Category.id_comp]
    refine ⟨(p.g).base z', ?_⟩
    rw [← Scheme.Hom.comp_apply, p.g_comm]
    exact e₂.trans (by rw [Scheme.Hom.comp_apply, e₁])
  exact ⟨IsOpenImmersion.lift p.W.ι (jK R) H, IsOpenImmersion.lift_fac _ _ _⟩

theorem nonempty_isPullDeg_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R'']
    [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} (hi : Function.Injective i) (hj : Function.Injective j)
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D'') :
    Nonempty (IsPullDeg (j.comp i) D D'') := by
  have hji : Function.Injective (j.comp i) := hj.comp hi
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  obtain ⟨s, hs⟩ := exists_generic_lift hi p
  obtain ⟨r, -⟩ := GlobalTheory.DvrDeg.exists_isPullDeg_of_val hji D D'' p.psiW s hs gp w (T.pgen_comp D'.P.isLB g₁ g₂) hr
    (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have sj : jK R'' ≫ spMap j = genMap hj ≫ jK R' := (Category.id_comp _).symm.trans (fracMap_sq hj)
      have s' : genMap hj ≫ jK R' ≫ spMap i = genMap hji ≫ jK R :=
        (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) sj.symm).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) sc).trans ((Category.id_comp _).symm.trans (fracMap_sq hji)))))
      have v₁ := psi_val p _ _ s' hJ hJ' (q.xe x)
      have v₂ := psi_val q _ _ (fracMap_sq hj) hJ' hJ'' x
      have hx : D''.xK x ≫ proj q = genMap hj ≫ D'.xK (q.xe x) := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = genMap hj ≫ jK R' ≫ (D'.c (q.xe x)).left
        rw [Category.assoc, q.c_pr, ← Category.assoc, ← Category.assoc, ← sj]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      rw [v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r⟩

end GlobalTheory.PullDegComp

namespace GlobalTheory.Mum

theorem hasFin_of_finExt : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R']
    [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')),
    Nonempty (IsPullDeg ρ D.toPre D'.toPre) → HasFin D' → HasFin D := by
  intro R R' _ _ _ _ _ _ ρ hρ D D' ⟨p⟩ ⟨R'', _, _, _, σ, D'', hσ, ⟨q⟩, hH⟩
  exact ⟨R'', _, _, _, σ.comp ρ, D'', ⟨hσ.1, hσ.2.1.comp hρ.2.1, hσ.2.2.comp hρ.2.2⟩,
    GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hρ.2.1 hσ.2.1 p q, hH⟩

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnifDvrBaseChange

theorem exists_pelUnif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V], CDvr V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W], GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → ∀ f : V →+* W, Function.Injective f → IsLocalHom f →
    ∀ tW : SAB H (Sp W), Nonempty (SABMap tW t (spMap f)) →
      ∃ (PW : PELUnif (maximalIdeal W) tW) (e : PW.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X),
        ∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : Wˣ, PsiCoord PW.D.toPre y (u * f r) := by
  intro E _ _ _ H V _ _ _ hV t P W _ _ _ hW hWd f hfi hfl tW ⟨m⟩
  obtain ⟨hVd, hVc, hV0⟩ := hV
  obtain ⟨⟨hWN, -, hWI, hWc⟩, hW0⟩ := hW
  obtain ⟨L₁, L₂, -⟩ := GlobalTheory.firstFiveLaws

  have j : Function.Injective ((algebraMap W (FractionRing W)).comp f) := (IsFractionRing.injective W _).comp hfi
  let g : FractionRing V →+* FractionRing W := IsFractionRing.lift j
  have eg : jK W ≫ spMap f = spMap g ≫ jK V :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  have hpW : GlobalTheory.LN.PolAt tW (jK W) := GlobalTheory.DatUniq.polAt_pull m (GlobalTheory.DatUniq.polAt_of_unif P) (jK W) (spMap g) eg.symm
  obtain ⟨B, -, gen, hg, hw, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H W tW hpW

  have := t.semi.separated
  have := t.semi.smooth
  let p₀ : Sp (FractionRing V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) ∈ abLocus t.G := by
    rw [← GlobalTheory.TraitChartForm.jK_apply_eq_bot V p₀]
    exact (GlobalTheory.ZJ.AbelianLocus.mem_abLocus_iff t.G (IsPullback.of_hasPullback t.G.hom (jK V)) p₀).2
      (GlobalTheory.DatUniq.polAt_of_unif P).1

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let Wv : Set (Sp V) := abLocus t.G ∩ {p | ϖ ∉ p.asIdeal}
  have hWo : IsOpen Wv :=
    (GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi).inter (PrimeSpectrum.isOpen_basicOpen (a := ϖ))
  have hne : Wv ≠ Set.univ := fun h => by
    have : closedPoint V ∈ Wv := h ▸ Set.mem_univ _
    exact this.2 hϖ.not_isUnit
  have hψ : ∀ y, PsiUnitOn P.D.toPre y Wv := fun y => GlobalTheory.DvrDataCompare.psiUnitOn_of_ne_univ P.D.toPre y hne
  have hker : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum V) ∈ Wv := by
    have hk : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum V) = ⟨⊥, Ideal.isPrime_bot⟩ :=
      PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot f).1 hfi)
    rw [hk]
    exact ⟨hgen, fun h => hϖ.ne_zero ((Submodule.mem_bot V).1 h)⟩
  have hloc : ∀ a ∈ maximalIdeal V, f a ∈ maximalIdeal W := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit f a h)
  obtain ⟨PW, e, he⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H V W f t tW m P Wv inferInstance inferInstance
    hVc hWN hWI hWc hloc hWo Set.inter_subset_left hψ hker ⟨B, gen, hg, hw⟩
  refine ⟨PW, e.symm, fun y r hr => ?_⟩
  obtain ⟨u, hu⟩ := he _ r hr
  exact ⟨u, by simpa using hu⟩

end GlobalTheory.UnifDvrBaseChange
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PolPoint

theorem isProper_of_image {S T : Scheme.{0}} (A : Over S) (B : Over T) (g : T ⟶ S) (φ : B.left ⟶ A.left)
    (h : IsPullback φ B.hom A.hom g) (W : S.Opens) (hg : ∀ t, g t ∈ W) (hpr : IsProper (A.hom ∣_ W)) :
    IsProper B.hom := by
  have hr : Set.range g ⊆ Set.range W.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hg y
  have hr' : Set.range φ ⊆ Set.range (A.hom ⁻¹ᵁ W).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    show A.hom (φ y) ∈ W
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
    exact hg _
  let l := IsOpenImmersion.lift W.ι _ hr
  let ψ := IsOpenImmersion.lift (A.hom ⁻¹ᵁ W).ι φ hr'
  have hl : l ≫ W.ι = g := IsOpenImmersion.lift_fac _ _ hr
  have hψ : ψ ≫ (A.hom ⁻¹ᵁ W).ι = φ := IsOpenImmersion.lift_fac _ _ hr'
  have big : IsPullback (ψ ≫ (A.hom ⁻¹ᵁ W).ι) B.hom A.hom (l ≫ W.ι) := by rw [hψ, hl]; exact h
  have sq : IsPullback ψ B.hom (A.hom ∣_ W) l := by
    refine IsPullback.of_right big ?_ (isPullback_morphismRestrict A.hom W).flip
    rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, hψ, h.w, Category.assoc, hl]
  exact MorphismProperty.of_isPullback (P := @IsProper) sq hpr

theorem exists_field_point_polarised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ W : (Sp R).Opens, IsProper (G.hom ∣_ W) → ∀ y : PrimeSpectrum R, y ∈ W → y.asIdeal ≠ ⊥ → ∃ (K₁ : Type) (_ : Field K₁) (z : Sp K₁ ⟶ Sp R), z (closedPoint K₁) = y ∧ IsProper (pullback.snd G.hom z) ∧ RelAmple ((Over.pullback z).obj G) (U.LG.L.pull (pullback.fst G.hom z)) ∧ KTriv ((Over.pullback z).obj G) (U.LG.L.pull (pullback.fst G.hom z)) := by
  intro R _ _ _ hR D A G _ _ hG U W hW y hyW hy
  obtain ⟨⟨hN, -, -, -⟩, -⟩ := hR
  let O := Localization.AtPrime y.asIdeal
  have hiO : Function.Injective (algebraMap R O) :=
    IsLocalization.injective O y.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsDomain O := IsLocalization.isDomain_localization y.asIdeal.primeCompl_le_nonZeroDivisors
  haveI : IsNoetherianRing O := IsLocalization.isNoetherianRing y.asIdeal.primeCompl O hN
  have hf : ¬ IsField O := by
    intro hfO
    apply hy
    have h1 : maximalIdeal O = ⊥ := (IsLocalRing.isField_iff_maximalIdeal_eq).1 hfO
    have h2 := Localization.AtPrime.under_maximalIdeal (I := y.asIdeal)
    rw [← h2, Ideal.under, h1]
    exact Ideal.comap_bot_of_injective _ hiO
  obtain ⟨V, _, _, _, ρ, hρ, hloc⟩ := GlobalTheory.KTrivSpread.exists_dvr O hf
  let a : R →+* V := ρ.comp (algebraMap R O)
  have ha : Function.Injective a := hρ.comp hiO
  have hgen : ∀ q : PrimeSpectrum V, spMap a q ∈ W := by
    intro q
    have hle : PrimeSpectrum.comap a q ≤ y := by
      show Ideal.comap a q.asIdeal ≤ y.asIdeal
      intro s hs
      rw [← Localization.AtPrime.under_maximalIdeal (I := y.asIdeal)]
      exact IsLocalRing.le_maximalIdeal (q.isPrime.comap ρ).ne_top hs
    exact ((PrimeSpectrum.le_iff_specializes _ _).1 hle).mem_open W.isOpen hyW
  let B := (Over.pullback (spMap a)).obj G
  have hcart : IsPullback (pullback.fst G.hom (spMap a)) B.hom G.hom (spMap a) := IsPullback.of_hasPullback _ _
  have hpB : IsProper B.hom := isProper_of_image G B (spMap a) _ hcart W hgen hW
  have hsB := IsSemiAbelian.pullback (spMap a) G hG
  have hAb : IsAbelianScheme B := ⟨hsB.comm, hsB.smooth, hpB, hsB.geomConnected⟩
  obtain ⟨hL, hL2, -⟩ := GlobalTheory.allSixLaws
  let M := GlobalTheory.ValueForm.modelCP U.toUnifPre hL.globalFns
  let φ := U.gen.inv.left ≫ pullback.fst G.hom (jK R)
  have hφ : IsGrpPullback A.A G (spMap (algebraMap R (FractionRing R))) φ :=
    GlobalTheory.ThetaBaseChange.grp_generic U.toUnifPre
  have hgi : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have hLφ : LBIso A.L (M.L.L.pull φ) := LBIso.chartPull (h := U.gen.inv.left) (chartPullSec A.L _ _ hgi)
    (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => rfl) U.ext
  obtain ⟨P', M', φ', hφ', hL', hM'⟩ :=
    GlobalTheory.PolExtendDVR.exists_baseChange (K' := FractionRing V) hL.polBaseChange a ha A G M φ hφ hLφ
  obtain ⟨hAB, hKB⟩ := GlobalTheory.polarisation_extends_dvr hL hL2 V (FractionRing V) P' B M' φ' hAb hφ' hL'
  let r := IsLocalRing.residue V
  obtain ⟨z, hz0⟩ : ∃ z : Sp (IsLocalRing.ResidueField V) ⟶ Sp R, z = spMap (r.comp a) := ⟨_, rfl⟩
  have hz : z = spMap r ≫ spMap a := by
    rw [hz0]
    unfold spMap
    rw [← Spec.map_comp]
    rfl
  let ψ : pullback G.hom z ⟶ B.left := pullback.lift (pullback.fst G.hom z) (pullback.snd G.hom z ≫ spMap r)
    (by rw [pullback.condition, hz, Category.assoc])
  have hψ : ψ ≫ pullback.fst G.hom (spMap a) = pullback.fst G.hom z := pullback.lift_fst _ _ _
  have hψ2 : ψ ≫ B.hom = ((Over.pullback z).obj G).hom ≫ spMap r := pullback.lift_snd _ _ _
  have hgz : IsGrpPullback ((Over.pullback z).obj G) B (spMap r) ψ :=
    (isGrpPullback_pullback G (spMap a)).cancel ((isGrpPullback_pullback G z).congr hz hψ.symm) hψ2
  have hiso : LBIso (U.LG.L.pull (pullback.fst G.hom z)) (M'.L.L.pull ψ) := by
    have e := GlobalTheory.PolExtendDVR.lbIso_pull_comp hM' ψ
    rw [hψ] at e
    exact e.symm
  obtain ⟨w, hw⟩ := hiso
  have hw' := (isGen_iff w).1 hw
  refine ⟨IsLocalRing.ResidueField V, inferInstance, z, ?_, ?_, ?_, ?_⟩
  · have e1 : PrimeSpectrum.comap r (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)) =
        IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint r
    have e2 : PrimeSpectrum.comap ρ (IsLocalRing.closedPoint V) = IsLocalRing.closedPoint O :=
      IsLocalRing.comap_closedPoint ρ
    have e3 : PrimeSpectrum.comap (algebraMap R O) (IsLocalRing.closedPoint O) = y :=
      PrimeSpectrum.ext Localization.AtPrime.under_maximalIdeal
    rw [hz0]
    show PrimeSpectrum.comap (algebraMap R O) (PrimeSpectrum.comap ρ
      (PrimeSpectrum.comap r (IsLocalRing.closedPoint (IsLocalRing.ResidueField V)))) = y
    rw [e1, e2, e3]
  · exact MorphismProperty.of_isPullback (P := @IsProper) hgz.1 hpB
  · exact relAmple_pull hgz.1 M'.L.isLB (pull_isLB U.LG.isLB _) hw' ⊤ (isAffineOpen_top _) (fun _ => trivial) hAB
  · exact kTriv_pull hgz M'.L.isLB (pull_isLB U.LG.isLB _) hw' hKB

end GlobalTheory.PolPoint
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TorsFixed

theorem fixed_of_classes_fixed : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ (V : Type) [CommRing V] [IsDomain V] (φ : R →+* V) [Algebra (FractionRing R) (AlgebraicClosure (FractionRing V))], (∀ r, algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ (φ r))) → ∀ k : ℕ, 1 ≤ k → ∀ σ : (AlgebraicClosure (FractionRing V)) ≃+* (AlgebraicClosure (FractionRing V)), (∀ v : V, σ (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v)) = algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (algebraMap V _ v)) → (∀ p q : QkPt D.toPre (AlgebraicClosure (FractionRing V)) k, QkExt σ.toRingHom p q → QkPt.Equiv D.toPre (AlgebraicClosure (FractionRing V)) p q) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ k = 1 → spMap σ.toRingHom ≫ x.left = x.left := by
  intro R _ _ _ hB D A G _ _ hG U V _ _ φ _ hc k hk σ hσ hQ x hx
  haveI : CharZero R := hB.2
  have hL : GlobalTheory.UT.LL := GlobalTheory.firstFiveLaws

  have sq : (jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V) ≫ spMap φ =
      jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R := by
    show (spMap _ ≫ spMap _) ≫ spMap φ = spMap _ ≫ spMap _
    rw [← spMap_comp, ← spMap_comp, ← spMap_comp]
    congr 1
    ext r
    exact (hc r).symm
  have wx : x.left ≫ pullback.snd G.hom (spMap φ) = jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V := Over.w x
  have w₁ : (x.left ≫ pullback.fst G.hom (spMap φ)) ≫ G.hom = jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, wx, sq]
  let xG : Over.mk (jFK (R := R) (AlgebraicClosure (FractionRing V)) ≫ jK R) ⟶ G :=
    Over.homMk (x.left ≫ pullback.fst G.hom (spMap φ)) w₁
  have hxG : xG ^ k = 1 :=
    (GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull sq (isGrpPullback_pullback G (spMap φ)) (x := xG) (x' := x) rfl).1 hx

  have := U.gen_hom
  have : IsMonHom U.gen.symm.hom := inferInstanceAs (IsMonHom U.gen.inv)
  have gp : IsGrpPullback A.A G (jK R) (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  let x₀ : TFK (R := R) (AlgebraicClosure (FractionRing V)) ⟶ A.A :=
    Over.homMk (gp.1.lift (x.left ≫ pullback.fst G.hom (spMap φ)) (jFK (R := R) (AlgebraicClosure (FractionRing V))) w₁)
      (gp.1.lift_snd _ _ _)
  have e₀ : x₀.left ≫ (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) = x.left ≫ pullback.fst G.hom (spMap φ) :=
    gp.1.lift_fst _ _ _
  have hx₀ : x₀ ^ k = 1 := (GlobalTheory.PsiAbelian.pow_eq_one_iff_of_pull rfl gp (x := xG) (x' := x₀) e₀).2 hxG

  have hσR : ∀ r : R, σ (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r)) =
      algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) (algebraMap R _ r) := fun r => by
    rw [hc r, hσ]
  let σ' : AlgebraicClosure (FractionRing V) →ₐ[FractionRing R] AlgebraicClosure (FractionRing V) :=
    ⟨σ.toRingHom, fun a => RingHom.congr_fun
      (IsLocalization.ringHom_ext (nonZeroDivisors R)
        (j := σ.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))))
        (k := algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))) (RingHom.ext hσR)) a⟩
  have hσf : σ.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V))) =
      algebraMap (FractionRing R) (AlgebraicClosure (FractionRing V)) := RingHom.ext σ'.commutes

  obtain ⟨f, hf, hsurj, hfi, -, -⟩ :=
    GlobalTheory.TorsionIso.torsion_eq hL R (maximalIdeal R) hB.1 D A G hG U (AlgebraicClosure (FractionRing V)) k hk
  obtain ⟨p, hp⟩ := hsurj x₀ hx₀
  obtain ⟨q, hpq⟩ := qkExtExists R D.toPre (AlgebraicClosure (FractionRing V))
    (AlgebraicClosure (FractionRing V)) σ.toRingHom σ'.commutes k p
  have heq : f q = x₀ := ((hfi p q).2 (hQ p q hpq)).symm.trans hp
  have s₂ : spMap σ.toRingHom ≫ jFK (R := R) (AlgebraicClosure (FractionRing V)) =
      jFK (R := R) (AlgebraicClosure (FractionRing V)) := by
    refine (spMap_comp _ _).symm.trans ?_
    exact congrArg spMap hσf
  have wx₀ : x₀.left ≫ A.A.hom = jFK (R := R) (AlgebraicClosure (FractionRing V)) := Over.w x₀
  let x' : TFK (R := R) (AlgebraicClosure (FractionRing V)) ⟶ A.A :=
    Over.homMk (spMap σ.toRingHom ≫ x₀.left) (by rw [Category.assoc, wx₀, s₂]; rfl)
  have hq : QkToAkU U.toUnifPre (AlgebraicClosure (FractionRing V)) k q x' :=
    (GlobalTheory.TorsionExt.qkToAkU_iff_of_qkExt hL R (maximalIdeal R) hB.1 D A G hG U (AlgebraicClosure (FractionRing V))
      (AlgebraicClosure (FractionRing V)) σ' k hk p q x₀ x' hpq rfl).1 ((hf p x₀).2 hp.symm)
  have fix : spMap σ.toRingHom ≫ x₀.left = x₀.left := congrArg (fun z => z.left) (((hf q x').1 hq).trans heq)

  have sV : spMap σ.toRingHom ≫ jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V =
      jFK (R := V) (AlgebraicClosure (FractionRing V)) ≫ jK V := by
    show spMap _ ≫ spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [← spMap_comp, ← spMap_comp]
    congr 1
    ext v
    exact hσ v
  refine pullback.hom_ext (f := G.hom) (g := spMap φ) ?_ ?_
  · rw [Category.assoc, ← e₀, ← Category.assoc, fix]
  · rw [Category.assoc, wx, sV]

end GlobalTheory.Mum.TorsFixed
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_finExt_etale_of_isSeparable : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R],
    AdmBase R (maximalIdeal R) → ∀ (k' : Type) [Field k'] [Algebra (ResidueField R) k']
    [Module.Finite (ResidueField R) k'] [Algebra.IsSeparable (ResidueField R) k'],
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R')
      (σ : k' →+* ResidueField R'), FinExt ρ ∧ ρ.Etale ∧
      σ.comp ((algebraMap (ResidueField R) k').comp (residue R)) = (residue R').comp ρ := by
  intro R _ _ _ hR k' _ _ _ _
  obtain ⟨hN, -, hIC, hC⟩ := hR
  haveI := hN; haveI := hIC; haveI := hC
  obtain ⟨A, _, _, hfin, het, hloc, ⟨ε⟩⟩ := GlobalTheory.exists_etale_lift_of_isSeparable R k'
  haveI : IsLocalHom (algebraMap R A) :=
    ((local_hom_tfae (algebraMap R A)).out 1 5).mpr (comap_eq_maximalIdeal_of_finite _)
  have hm : (maximalIdeal R).map (algebraMap R A) = maximalIdeal A :=
    Algebra.FormallyUnramified.map_maximalIdeal
  obtain ⟨hD, hI⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale R (maximalIdeal A)
    (Localization.AtPrime (maximalIdeal A))
  let e := IsLocalization.atUnits A (maximalIdeal A).primeCompl
    (S := Localization.AtPrime (maximalIdeal A)) (fun y hy => by
      rw [IsUnit.mem_submonoid_iff]
      by_contra h
      exact hy ((IsLocalRing.mem_maximalIdeal y).mpr h))
  haveI : IsDomain A := e.toMulEquiv.isDomain
  haveI : IsIntegrallyClosed A := IsIntegrallyClosed.of_equiv e.toRingEquiv.symm
  haveI : IsNoetherian R A := inferInstance
  haveI : IsNoetherianRing A := isNoetherian_of_tower R inferInstance
  let g2 : ResidueField R ⊗[R] A →ₐ[R] ResidueField A :=
    Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R (ResidueField R) (ResidueField A))
      (IsScalarTower.toAlgHom R A (ResidueField A)) (fun _ _ => Commute.all _ _)
  let σ : k' →+* ResidueField A := g2.toRingHom.comp ε.symm.toRingHom
  refine ⟨A, inferInstance, inferInstance, inferInstance, algebraMap R A, σ,
    ⟨⟨inferInstance, inferInstance, inferInstance, ?_⟩, ?_, RingHom.finite_algebraMap.mpr hfin⟩,
    RingHom.etale_algebraMap.mpr het, ?_⟩
  · have := GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal R) A
    rwa [hm] at this
  · haveI : Module.Free R A := Module.free_of_flat_of_isLocalRing
    intro x y hxy
    rw [← sub_eq_zero]
    have h0 : (x - y) • (1 : A) = 0 := by
      rw [Algebra.smul_def, _root_.mul_one, map_sub, hxy, sub_self]
    exact (smul_eq_zero.mp h0).resolve_right one_ne_zero
  · ext r
    simp only [RingHom.comp_apply, σ, AlgEquiv.coe_toRingEquiv, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, AlgHom.toRingHom_eq_coe]
    change g2 (algebraMap (ResidueField R) (ResidueField R ⊗[R] A) (residue R r)) = _
    rw [Algebra.TensorProduct.algebraMap_apply]
    simp [g2]

end GlobalTheory.Mum
end
