module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2938
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2939
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2972
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2974
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle046
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2900
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle039
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupGaloisMapMul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2980
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2983
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsSecNeObj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

noncomputable section

theorem GlobalTheory.Mum.Two.Fac.pt_ext (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (a b : 𝟙_ (Over (Sp R)) ⟶ D.P.A)
    (h : toUnit (TF (R := R) F) ≫ a = toUnit (TF (R := R) F) ≫ b) : a = b := by
  have : IsDominant (jK R) := isDominant_jK
  have : Surjective (jFK (R := R) F) := GlobalTheory.Balanced.surjective_spMap (algebraMap (FractionRing R) F)
  have : IsDominant (jFK (R := R) F) := inferInstance
  have : IsProper D.P.A.hom := D.P.isAb.proper
  have e := congrArg (fun m => m.left) h
  simp only [Over.comp_left] at e
  refine Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R)) D.P.A.hom
    ((Over.w a).trans (Over.w b).symm) (jFK (R := R) F ≫ jK R) ?_)
  simpa using e


open GlobalTheory.Mum.Two.Fac in
theorem GlobalTheory.Mum.Two.Fac.periods_of_factor : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D' : DegPre R), D'.TauBimult → ∀ (O : Type) [Ring O] [StarRing O] [Module O D'.X] (o : D'.OAct O) (e f : O) (inc : D₀.P.A ⟶ D'.P.A) (pr : D'.P.A ⟶ D₀.P.A) (h : D₀.X →+ D'.X) (φ : D'.X →+ D₀.X), IsMonHom inc → IsMonHom pr → pr ≫ inc = o.onB.act e → (∀ χ, ∃ u : LB.Gen (CmpLB D' D₀ pr (h χ) χ), Nrm u) → LBIso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ o.onB.act f) : G2 D₀.P.A ⟶ G2 D'.P.A).left) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F], (∀ (y : D'.X) (g : GtPtF D' F), GtPtF.IsIota y g → ∃ g' : GtPtF D₀ F, Act D' D₀ pr h g g' ∧ GtPtF.IsIota (φ y) g') → (∀ y, h (φ y) = star e • f • e • y) → (∀ y, D₀.c (φ y) = D'.c y ≫ pr) ∧ ∃ w : LB.Iso (abelian₂ D₀.P.A D₀.P.L) ((abelian₂ D'.P.A D'.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ inc) (snd D₀.P.A D₀.P.A ≫ inc ≫ o.onB.act f) : G2 D₀.P.A ⟶ G2 D'.P.A).left), w.IsGen ∧ ∀ y y' z J J', Good D'.P.L z J → Good D₀.P.L z J' → val (D₀.tau (φ y) (φ y')) (𝟙 _) z J' = GlobalTheory.PolDeg.lamVal w (lift (toUnit (TK R) ≫ D₀.c (φ y)) (toUnit (TK R) ≫ D₀.c (φ y'))).left z J J' * val (D'.tau (e • y) (f • e • y')) (𝟙 _) z J := by
  intro R _ _ D₀ D' hB O _ _ _ o e f inc pr h φ hinc hpr hpi hu hw F _ _ hiota hh
  have hG := GlobalTheory.globalFns_holds
  have hi (y : D'.X) : ∃ g : GtPtF D' F, GtPtF.IsIota y g := GlobalTheory.TorusExt.exists_iota hB y
  have hc : ∀ y, D₀.c (φ y) = D'.c y ≫ pr := by
    intro y
    obtain ⟨g, hg⟩ := hi y
    obtain ⟨g', ha, hg'⟩ := hiota y g hg
    have h1 := ha.1
    rw [hg'.1, hg.1] at h1
    refine pt_ext R D₀ F _ _ ?_
    simpa only [Category.assoc] using h1
  refine ⟨hc, ?_⟩
  haveI := hinc
  haveI := hpr
  haveI : IsMonHom (o.onB.act f) := o.onB.hom f
  haveI : IsMonHom (o.onB.act e) := o.onB.hom e
  haveI : IsMonHom (o.onB.act (star e)) := o.onB.hom (star e)
  obtain ⟨w, hwg, hwn⟩ := GlobalTheory.T.exists_mumfordBundleIso_twoHom_normalisedAtOrigin D₀.P.A D'.P.A D₀.P.L D'.P.L D₀.P.isLB D'.P.isLB inc (inc ≫ o.onB.act f) hw
  have hw1 := GlobalTheory.T.mumfordBundleIso_value_one_zero_first_factor D₀.P.A D'.P.A D₀.P.L D'.P.L D₀.P.isLB D'.P.isLB D₀.P.isAb inc (inc ≫ o.onB.act f)
    w hwg hwn
  refine ⟨w, hwg, fun y y' z J J' hJ hJ' => ?_⟩
  obtain ⟨ur, hur, hur0⟩ := exists_ros hG D'.P.isAb D'.P.isLB (o.onB.act e) (o.onB.act (star e)) (o.onB.rosati e)
  have hur1 := GlobalTheory.T.rosatiGenerator_value_one_zero_first_factor D'.P.A D'.P.L D'.P.isLB D'.P.isAb _ _ ur hur hur0
  obtain ⟨JN₀, hJN, hl, hr⟩ := exists_good_join D'.P.isLB D₀.P.isLB hJ hJ'
  obtain ⟨u, hun⟩ := hu (φ y')
  obtain ⟨g, hg⟩ := hi y
  obtain ⟨g', ha, hg'⟩ := hiota y g hg
  have A := GlobalTheory.T.torusExtensionPointAction_period_value_fractionField R D₀ D' pr h F y (φ y) _ g' hg hg' ha (φ y') u hun z JN₀ hJN
  rw [hl, hr] at A
  have B := val_corr hJ (o.tau_bal e ur hur hur0 y (f • e • y')) (𝟙 _)
  beta_reduce at B
  rw [val_mul hJ, val_pull hJ, Category.id_comp, ← hh y'] at B
  have hq : D₀.c (φ y') ≫ inc ≫ o.onB.act f = D'.c (f • e • y') := by
    rw [hc, o.c_lin, o.c_lin, ← hpi]; simp only [Category.assoc]
  have hq' : D'.c (h (φ y')) = D'.c (f • e • y') ≫ o.onB.act (star e) := by
    rw [hh y', o.c_lin]
  have C := GlobalTheory.T.mumfordIso_eq_rosatiGenerator_mul_comparison R D₀ D' inc pr (o.onB.act e) (o.onB.act f) (o.onB.act (star e)) hpi w hwg hw1 ur hur hur1
    (h (φ y')) (φ y') (D'.c (f • e • y')) hq hq' u hun (TK R) (toUnit (TK R) ≫ D'.c y) z JN₀ hJN
  rw [hl, hr, Category.assoc, ← hc] at C
  rw [A, ← B, C]
  show _ = _ * _ * val (D'.tau (e • y) (f • e • y')) (𝟙 _) z J
  rw [mul_comm (val ur _ z J)]
  ac_rfl
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CodimOneExtend

theorem extAt_of_flat {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X XK XV XF : Scheme.{0}} {p : X ⟶ Sp R} {J : XK ⟶ X} {q : XK ⟶ Sp K}
    (H : IsPullback J q p (spMap (algebraMap R K))) (φ : XV ⟶ X) [Flat φ] (A : XF ⟶ XV)
    (hA : ∀ U, Function.Injective (A.app U).hom) (B : XF ⟶ XK) (w : B ≫ J = A ≫ φ) (W : X.Opens)
    (f : Γ(XK, J ⁻¹ᵁ W)) (s : Γ(XV, φ ⁻¹ᵁ W)) (h₂ : A ⁻¹ᵁ φ ⁻¹ᵁ W ≤ B ⁻¹ᵁ J ⁻¹ᵁ W)
    (hs : (A.appLE _ _ le_rfl).hom s = (B.appLE _ _ h₂).hom f) (v : XV) (hv : φ v ∈ W) :
    GenericExtend.ExtAt J W f (φ v) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hvU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hv W.isOpen
  have hUW : U ≤ W := hUW
  obtain ⟨a, ha, b, hb⟩ := loc_surj (nonZeroDivisors R) H hU (resG XK (J.preimage_mono hUW) f)
  have hb' : ∀ z, J z ∈ U → gs (𝟙 XK) z (J ⁻¹ᵁ U) ((J.app U).hom b) =
      cst (J ≫ p) z a * gs (𝟙 XK) z (J ⁻¹ᵁ W) f := fun z hz ↦ by
    rw [gs_pull (𝟙 XK) J z U hz, Category.id_comp, hb z hz, gs_res (𝟙 XK) z _ hz]
  have hw : ∀ t, J (B t) = φ (A t) := fun t ↦ by
    rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  have e : (φ.app U).hom b = constFn (φ ≫ p) _ a * resG XV (φ.preimage_mono hUW) s := by
    refine hA _ (fn_ext fun t ht ↦ ?_)
    have ht' : J (B t) ∈ U := by rw [hw]; exact ht
    have k := congrArg (B.stalkMap t).hom (hb' (B t) ht')
    rw [map_mul, ← gs_stalkMap B t _ ht', ← gs_stalkMap B t _ (hUW ht'), H1.cst_stalkMap, gs_pull B J t U ht',
      w] at k
    have k' := congrArg (gs (𝟙 XF) t _) hs
    rw [gs_appLE A _ _ _ (𝟙 XF) t (hUW ht), gs_appLE B _ _ _ (𝟙 XF) t (hUW ht), Category.id_comp,
      Category.id_comp] at k'
    rw [gs_pull (𝟙 XF) A t _ ht, gs_pull (𝟙 XF) A t _ ht, Category.id_comp, gs_mul A t _ ht,
      gs_pull A φ t U ht, gs_constFn _ _ A t ht, gs_res A t _ ht, k, k', reassoc_of% w]
  have hd : cst p (φ v) a ∣ gs (𝟙 X) (φ v) U b := by
    refine dvd_descend φ v ?_
    have k := congrArg (gs (𝟙 XV) v _) e
    rw [gs_pull (𝟙 XV) φ v U hvU, gs_mul (𝟙 XV) v _ hvU, gs_constFn _ _ (𝟙 XV) v hvU, Category.id_comp,
      Category.id_comp] at k
    rw [← gs_stalkMap φ v U hvU, H1.cst_stalkMap, k]
    exact dvd_mul_right _ _
  obtain ⟨t, ht⟩ := hd
  obtain ⟨U', hU', c, rfl⟩ := X.presheaf.exists_germ_eq t
  have hm : φ v ∈ U ⊓ U' := ⟨hvU, hU'⟩
  have e₁ : gs (𝟙 X) (φ v) (U ⊓ U') (resG X inf_le_left b) =
      gs (𝟙 X) (φ v) (U ⊓ U') (constFn p (U ⊓ U') a * resG X inf_le_right c) := by
    rw [gs_res (𝟙 X) (φ v) _ hm, gs_mul (𝟙 X) (φ v) _ hm, gs_res (𝟙 X) (φ v) _ hm, gs_constFn p _ (𝟙 X) (φ v) hm,
      Category.id_comp, ht, gs_eq (𝟙 X) (φ v) U' hU']
    rfl
  rw [gs_eq (𝟙 X) (φ v) _ hm, gs_eq (𝟙 X) (φ v) _ hm] at e₁
  obtain ⟨O, hO, i₁, i₂, e'⟩ := X.presheaf.germ_eq (φ v) hm hm _ _ e₁
  have le : O ≤ U ⊓ U' := i₁.le
  refine ⟨O, le.trans (inf_le_left.trans hUW), resG X (le.trans inf_le_right) c, hO, fn_ext fun z hz ↦ ?_⟩
  have hz' : J z ∈ U ⊓ U' := le hz
  have k := (gs_res J z le hz _).symm.trans ((congrArg (gs J z O) e').trans (gs_res J z le hz _))
  have k' : gs J z (U ⊓ U') (resG X inf_le_left b) =
      gs J z (U ⊓ U') (constFn p (U ⊓ U') a * resG X inf_le_right c) := k
  rw [gs_res J z _ hz', gs_mul J z _ hz', gs_res J z _ hz', gs_constFn p _ J z hz'] at k'
  have k₂ := hb' z hz'.1
  rw [gs_pull (𝟙 XK) J z U hz'.1, Category.id_comp, k'] at k₂
  have hu : IsUnit (cst (J ≫ p) z a) := by
    rw [H.w, cst_comp]
    refine IsUnit.of_mul_eq_one (cst q z (algebraMap R K a)⁻¹) ?_
    rw [← H1.cst_mul, mul_inv_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha), H1.cst_one]
  rw [gs_appLE J _ _ _ (𝟙 XK) z hz, Category.id_comp, gs_res J z _ hz, gs_res (𝟙 XK) z _ hz]
  exact hu.mul_left_cancel k₂

theorem exists_cDvr_flat (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [CharZero R] (𝔭 : Ideal R) [𝔭.IsPrime] (h : 𝔭.height = 1) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V), GlobalTheory.LN.CDvr V ∧ ∃ φ : R →+* V,
      Function.Injective φ ∧ φ.Flat ∧ (IsLocalRing.maximalIdeal V).comap φ = 𝔭 := by
  have := ((GlobalTheory.normal_domain_height_one.{0, 0, 0} R (FractionRing R)).1 𝔭 h).1
  have hi : Function.Injective (algebraMap R (Localization.AtPrime 𝔭)) :=
    IsLocalization.injective _ 𝔭.primeCompl_le_nonZeroDivisors
  have : CharZero (Localization.AtPrime 𝔭) := charZero_of_injective_algebraMap hi
  obtain ⟨V, _, _, _, hV, j, hj, hl⟩ :=
    GlobalTheory.DvrCompletion.exists_cDvr_of_isDiscreteValuationRing (Localization.AtPrime 𝔭)
  refine ⟨V, _, _, _, hV, j.comp (algebraMap R _), hj.comp hi, ?_, ?_⟩
  · refine RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance) ?_
    let _ := j.toAlgebra
    have : FaithfulSMul (Localization.AtPrime 𝔭) V := (faithfulSMul_iff_algebraMap_injective _ _).2 hj
    exact (inferInstance : Module.Flat (Localization.AtPrime 𝔭) V)
  · rw [← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap]
    exact Localization.AtPrime.under_maximalIdeal

theorem exists_map_fractionRing {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V)
    (hφ : Function.Injective φ) : ∃ φK : FractionRing R →+* FractionRing V,
      φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ :=
  ⟨IsLocalization.map (M := nonZeroDivisors R) (T := nonZeroDivisors V) (FractionRing V) φ
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective φ hφ), IsLocalization.map_comp _⟩

theorem extAt_of_coheight_le_one : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (χ : Sp R ⟶ S) (W : (Over.mk χ ⊗ G).left.Opens) (f : Γ((Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⊗ G).left, ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)), (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ (φ : R →+* V) (φK : FractionRing R →+* FractionRing V) (h : spMap φK ≫ spMap (algebraMap R (FractionRing R)) ≫ χ = spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ), φK.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ → ∃ s : Γ((Over.mk (spMap φ ≫ χ) ⊗ G).left, ((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W), ∀ (O : (Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⊗ G).left.Opens) (h₁ : O ≤ ((Over.homMk (spMap (algebraMap V (FractionRing V))) rfl : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ)) ▷ G).left ⁻¹ᵁ (((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)) (h₂ : O ≤ ((Over.homMk (spMap φK) h : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) ▷ G).left ⁻¹ᵁ (((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ⁻¹ᵁ W)), (((Over.homMk (spMap (algebraMap V (FractionRing V))) rfl : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ)) ▷ G).left.appLE _ O h₁).hom s = (((Over.homMk (spMap φK) h : Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) ▷ G).left.appLE _ O h₂).hom f) → ∀ y ∈ W, Order.coheight y ≤ 1 → y ∉ Set.range ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left → GlobalTheory.GenericExtend.ExtAt ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left W f y := by
  intro S G _ hG R _ _ _ _ _ χ W f hf y hy h1 hr
  have := hG.smooth
  have fl : ∀ T : Over S, Flat (fst T G).left := fun T ↦
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback T.hom G.hom).flip inferInstance
  have := fl (Over.mk χ)
  have H := ThetaRuleCompare.isPullback_whisker (A := G)
    (Over.homMk (spMap (algebraMap R (FractionRing R))) rfl :
      Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ)
  let x : PrimeSpectrum R := (fst (Over.mk χ) G).left y
  have hx1 : Order.coheight ((fst (Over.mk χ) G).left y) ≤ 1 := GenericExtend.coheight_apply_le_one _ h1
  have hx0 : x.asIdeal ≠ ⊥ := fun h0 ↦ hr (by
    obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback H y (⊥ : PrimeSpectrum (FractionRing R)) (by
      refine PrimeSpectrum.ext (h0.trans ?_)
      exact (Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))).symm)
    exact ⟨z, hz⟩)
  have hx : x.asIdeal.height = 1 := by
    refine le_antisymm ?_ (ENat.one_le_iff_ne_zero.2 fun h0 ↦ hx0 (Ideal.height_eq_zero_iff_eq_bot.1 h0))
    exact (idealHeight_eq_coheight (CommRingCat.of R) x).trans_le hx1
  obtain ⟨V, _, _, _, hV, φ, hφ, hfl, hc⟩ := exists_cDvr_flat R x.asIdeal hx
  obtain ⟨φK, hK⟩ := exists_map_fractionRing φ hφ
  have hK' : spMap φK ≫ spMap (algebraMap R (FractionRing R)) =
      spMap (algebraMap V (FractionRing V)) ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hK]
  obtain ⟨s, hs⟩ := hf V hV φ φK (by rw [reassoc_of% hK']) hK
  have HV := ThetaRuleCompare.isPullback_whisker (A := G)
    (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ)
  have HF := ThetaRuleCompare.isPullback_whisker (A := G)
    (Over.homMk (spMap (algebraMap V (FractionRing V))) rfl :
      Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ))
  have hφf : Flat (spMap φ) := Flat.SpecMap_iff.2 hfl
  have := MorphismProperty.of_isPullback (P := @Flat) HV.flip hφf
  have := fl (Over.mk (spMap φ ≫ χ))
  obtain ⟨v, rfl, -⟩ := Scheme.exists_preimage_of_isPullback HV y (IsLocalRing.closedPoint V)
    (PrimeSpectrum.ext hc.symm)
  have w : ((Over.homMk (spMap φK) (by simp only [Over.mk_hom]; rw [reassoc_of% hK']) :
      Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶
        Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ)) ▷ G).left ≫
      ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl :
        Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left =
      ((Over.homMk (spMap (algebraMap V (FractionRing V))) rfl :
        Over.mk (spMap (algebraMap V (FractionRing V)) ≫ spMap φ ≫ χ) ⟶ Over.mk (spMap φ ≫ χ)) ▷ G).left ≫
      ((Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ χ) ⟶ Over.mk χ) ▷ G).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← comp_whiskerRight, ← comp_whiskerRight]
    congr 2
    exact Over.OverMorphism.ext hK'
  have hA := Exist.CubicalExtension.app_injective_generic HF
  have h₂ := congrArg (· ⁻¹ᵁ W) w
  simp only [Scheme.Hom.comp_preimage] at h₂
  exact extAt_of_flat H _ _ hA _ w W f s h₂.ge (hs _ le_rfl h₂.ge) v hy

end GlobalTheory.CodimOneExtend
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.PullUnifId

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_isPullDeg_of_valW' {i : R →+* R'} (D : DegPre R) (D' : DegPre R')
    {W : (Sp R).Opens} (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf i)
    {Φ : D'.P.A.left ⟶ D.P.A.left} (gp : IsGrpPullback D'.P.A D.P.A (spMap i) Φ)
    (w : LB.Iso D'.P.L (D.P.L.pull Φ)) (hw : PGen w)
    (hr : PMaps w (K := PUnit) (fun _ => eSec D'.P.A) (fun _ => eSec D.P.A) (fun _ => 1) D'.rig D.rig (spMap i))
    (xe : D'.X ≃+ D.X) (hc : ∀ x, (D'.c x).left ≫ Φ = spMap i ≫ (D.c (xe x)).left)
    (hψ : ∀ (x : D'.X) (z : (TK R').left) J J', Good D.P.L z J → Good D'.P.L z J' →
      val (ψW.psi (xe x)) g z J = (om w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J') :
    ∃ hD : IsPullDeg i D D', proj hD = Φ ∧ hD.xe = xe ∧ HEq hD.w w := by
  obtain ⟨e, e_hom, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf i))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = specOf i ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  have hx : ∀ x, g ≫ (toUnit (TW W) ≫ D.c (xe x)).left =
      D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) := fun x => by
    show g ≫ W.ι ≫ (D.c (xe x)).left = (jK R' ≫ (D'.c x).left) ≫ _
    rw [Category.assoc, hc, ← Category.assoc, hg, Category.assoc]
  choose b hb vb using fun x => exists_gen D.P.isLB (K' := PUnit)
    (φ' := fun _ => D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf i)) (ε' := fun _ => -1)
    (fun U _ h => Finset.prod_congr rfl fun _ _ => congrArg (fun q => h q ^ (-1 : ℤ)) (hx x))
    (LB.pullGen D.P.L _ _ (ψW.psi (xe x)) g) (DVR.pullGen_isGen _ _ _ _ (ψW.psi_gen _) g)
  choose psi hpsi vpsi using fun x => DegPull.exists_down_val hw D.P.isLB D'.P.isLB (K := PUnit)
    (φ' := fun _ => D'.xK x) (ε := fun _ => -1) (fun _ => rfl) (b x) (hb x)
  have eψ : ∀ x, psi x = D'.psi x := fun x => TorusExt.gen_ext_val D'.P.isLB (hpsi x) (D'.psi_gen x) fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
    have v := vpsi x _ (𝟙 _) y _ _ (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have u := hψ x y J J' hJ hJ'
    have v₁ : val (b x) (𝟙 _) y J = val (ψW.psi (xe x)) g y J :=
      (vb x _ _ y J hJ).trans ((val_pull hJ _ _ _).trans (by rw [Category.id_comp]))
    have v₂ : val (b x) (𝟙 _) y J = (om w y J J' (D'.xK x))⁻¹ * val (psi x) (𝟙 _) y J' := by
      refine v.trans (congrArg₂ (· * ·) ?_ rfl)
      rw [pw, Fintype.prod_unique, zpow_neg_one]
      simp only [om, Category.id_comp]
    exact mul_left_cancel (v₂.symm.trans (v₁.trans u))
  refine ⟨⟨e, e_hom, w, (isGen_iff w).2 hw, hE, ?_, xe, hc, W, ψW, g, hg, fun x => ⟨b x, fun jN jL => ?_,
      corr_of_val D.P.isLB fun y J hJ => vb x _ _ y J hJ⟩⟩, rfl, rfl, HEq.rfl⟩
  · exact (maps_iff w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf i) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf i) hE D.P.L) (fun _ => rfl)).2 hr
  · rw [← eψ]
    refine unit_ext fun y hy => ?_
    have v := vpsi x _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
    refine (gm_res _ y _ hy _).trans (v.trans (Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      (gm_res _ y _ hy _)))))
    rw [pw, Fintype.prod_unique]
    exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull (𝟙 _) _ y _ hy _))

theorem exists_isPullDeg_comp {R'' : Type} [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''}
    (hj : Function.Injective j) {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D')
    (q : IsPullDeg j D' D'') :
    ∃ (r : IsPullDeg (j.comp i) D D'') (w : LB.Iso D''.P.L (D.P.L.pull (proj q ≫ proj p))),
      proj r = proj q ≫ proj p ∧ r.xe = q.xe.trans p.xe ∧ HEq r.w w ∧ Tri p.w q.w w := by
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
  have sj : jK R'' ≫ spMap j = genMap hj ≫ jK R' := (Category.id_comp _).symm.trans (fracMap_sq hj)
  have hg : (genMap hj ≫ p.g) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, p.g_comm, ← Category.assoc, ← sj, Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  obtain ⟨r, r₁, r₂, r₃⟩ := exists_isPullDeg_of_valW' D D'' p.psiW (genMap hj ≫ p.g) hg gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := PsiEvenPull.psi_pull p (q.xe x) (genMap hj) z hJ hJ'
      have v₂ := psi_val q _ _ (fracMap_sq hj) hJ' hJ'' x
      have hx : D''.xK x ≫ proj q = genMap hj ≫ D'.xK (q.xe x) := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = genMap hj ≫ jK R' ≫ (D'.c (q.xe x)).left
        rw [Category.assoc, q.c_pr, ← Category.assoc, ← Category.assoc, ← sj]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      change _ = (om p.w z J J' (genMap hj ≫ D'.xK (q.xe x)))⁻¹ * val (D'.psi (q.xe x)) (genMap hj) z J' at v₁
      rw [v₂, Category.id_comp, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, w, r₁, r₂, r₃, T⟩

end GlobalTheory.PullUnifId

namespace GlobalTheory.PullUnifId

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

def pullIdIso (φ : R →+* R') (G : Over (Spec (CommRingCat.of R))) :
    (Over.pullback (specOf (RingHom.id R'))).obj ((Over.pullback (specOf φ)).obj G) ≅ (Over.pullback (specOf φ)).obj G :=
  Over.isoMk (pullbackLeftPullbackSndIso G.hom (specOf φ) (specOf (RingHom.id R')) ≪≫
    pullback.congrHom rfl (by rw [specOf_id, Category.id_comp])) (by
      show _ ≫ pullback.snd _ _ = pullback.snd _ _
      simp only [Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map]
      erw [pullback.lift_snd]
      simp)

theorem pullIdIso_fst (φ : R →+* R') (G : Over (Spec (CommRingCat.of R))) :
    (pullIdIso φ G).hom.left ≫ pullback.fst G.hom (specOf φ) =
      pullback.fst _ (specOf (RingHom.id R')) ≫ pullback.fst G.hom (specOf φ) := by
  simp only [pullIdIso, Over.isoMk_hom_left, Iso.trans_hom, Category.assoc, pullback.congrHom_hom, pullback.map]
  simp

end GlobalTheory.PullUnifId

namespace GlobalTheory.PullUnifId

open GlobalTheory.PsiEvenPull (proj)

theorem isPullUnif_comp_id : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R')
    (D : DegData R I) (D' D'' : DegData R' I') (hD : IsPullDeg φ D.toPre D'.toPre)
    (hid : IsPullDeg (RingHom.id R') D'.toPre D''.toPre)
    (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' A'' : PolAV (Spec (CommRingCat.of (FractionRing R'))))
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    (G' G'' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] [GrpObj G''] [IsCommMonObj G'']
    (bc : G' ≅ (Over.pullback (specOf φ)).obj G) (bc' : G'' ≅ (Over.pullback (specOf (RingHom.id R'))).obj G')
    (U : Unif I D A G) (U' : Unif I' D' A' G') (U'' : Unif I' D'' A'' G''),
    IsPullUnif φ hD bc U U' → IsPullUnif (RingHom.id R') hid bc' U' U'' →
    ∃ (h : IsPullDeg φ D.toPre D''.toPre) (bc'' : G'' ≅ (Over.pullback (specOf φ)).obj G),
      IsPullUnif φ h bc'' U U'' ∧ (∀ x, h.xe x = hD.xe (hid.xe x)) ∧
      h.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ) =
        hid.e.hom.left ≫ pullback.fst D'.toPre.P.A.hom (specOf (RingHom.id R')) ≫
          hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ) ∧
      bc''.hom.left ≫ pullback.fst G.hom (specOf φ) =
        bc'.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R')) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) ∧
      (IsMonHom bc.hom → IsMonHom bc'.hom → IsMonHom bc''.hom) := by
  intro R R' _ _ _ _ I I' φ D D' D'' hD hid A A' A'' G _ _ G' G'' _ _ _ _ bc bc' U U' U'' H₁ H₂
  obtain ⟨r, w, r₁, r₂, r₃, T⟩ := exists_isPullDeg_comp (j := RingHom.id R') (fun _ _ h => h) hD hid
  let bc'' : G'' ≅ (Over.pullback (specOf φ)).obj G :=
    bc' ≪≫ (Over.pullback (specOf (RingHom.id R'))).mapIso bc ≪≫ pullIdIso φ G
  have hb : bc''.hom.left ≫ pullback.fst G.hom (specOf φ) =
      bc'.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R')) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) := by
    have := pullIdIso_fst φ G
    simp only [bc'', Iso.trans_hom, Over.comp_left, Category.assoc, this, Functor.mapIso_hom]
    congr 1
    simp only [Over.pullback, Over.homMk_left]
    rw [← Category.assoc, pullback.lift_fst, Category.assoc]
  refine ⟨r, bc'', GalMul.isPullUnif_comp (i := φ) (j := RingHom.id R') r₁ r₂ r₃ T
      (hb.trans (Category.assoc _ _ _).symm) H₁ H₂, fun x => congrArg (fun e => e x) r₂,
      r₁.trans (Category.assoc _ _ _), hb, fun m₁ m₂ => ?_⟩
  have p₁ : IsGrpPullback G' G (specOf φ) (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf φ))).congr (Category.id_comp _) rfl
  have p₂ : IsGrpPullback G'' G' (specOf (RingHom.id R')) (bc'.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R'))) :=
    ((isGrpPullback_of_iso bc').comp (isGrpPullback_pullback G' (specOf (RingHom.id R')))).congr (Category.id_comp _) rfl
  have p : IsGrpPullback G'' G (specOf φ) (bc'.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id R')) ≫
      bc.hom.left ≫ pullback.fst G.hom (specOf φ)) :=
    (p₂.comp p₁).congr (by rw [specOf_id, Category.id_comp]) (Category.assoc _ _ _)
  obtain ⟨e, he, hf⟩ := grpPullback_iso p (isGrpPullback_pullback G (specOf φ))
  have : bc''.hom = e.hom := by
    ext1
    apply pullback.hom_ext
    · exact hb.trans hf.symm
    · exact (Over.w bc''.hom).trans (Over.w e.hom).symm
  rw [this]
  exact he

end GlobalTheory.PullUnifId
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.polarisationBundleIso_generic_extends_normalLocal : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), AdmBase R' (maximalIdeal R') → Function.Injective ρ → ∀ (D₁ D₂ : DegPre R) (D₃ : DegPre R') (E : DegPre (FractionRing R')) (p : IsPullDeg ρ D₁ D₃) (q₁ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) (q₂ : IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) (Φ : D₃.P.A.left ⟶ D₂.P.A.left) (κ : E.P.A.left ⟶ D₃.P.A.left), IsGrpPullback D₃.P.A D₂.P.A (spMap ρ) Φ → IsGrpPullback E.P.A D₃.P.A (spMap (algebraMap R' (FractionRing R'))) κ → κ ≫ GlobalTheory.PsiEvenPull.proj p = GlobalTheory.PsiEvenPull.proj q₁ → κ ≫ Φ = GlobalTheory.PsiEvenPull.proj q₂ → ∃ w : LB.Iso D₃.P.L (D₂.P.L.pull Φ), PGen w := by
  first | exact @GlobalTheory.Mum.genBundle_extends | exact GlobalTheory.Mum.genBundle_extends | (intros; apply GlobalTheory.Mum.genBundle_extends <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj

theorem _root_.GlobalTheory.T.verticalVectorField_unique_combination_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (δ : Fin n → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), (∀ a, IsField (t.G.hom ⁻¹ᵁ U.1) (δ a)) → (∀ a (O : t.G.left.Opens) (h : O ≤ t.G.hom ⁻¹ᵁ U.1) (r : Γ(X, U.1)), δ a O ((t.G.hom.appLE U.1 O h).hom r) = 0) → (∀ a (O : t.G.left.Opens), O ≤ t.G.hom ⁻¹ᵁ U.1 → ∀ (f : Γ(t.G.left, O)) (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left) (w : Sp (DualNumber S) ⟶ t.G.left), g₀ ≫ t.G.hom = spMap φ ≫ chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → IsTranslate t φ g₀ (v a) w → valR g₀ O (δ a O f) = (valR w O f).snd) → ∀ (W : t.G.left.Opens) (hW : W ≤ t.G.hom ⁻¹ᵁ U.1) (e : ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)), IsField W e → (∀ r : Γ(X, U.1), e W ((t.G.hom.appLE U.1 W hW).hom r) = 0) → ∃! c : Fin n → Γ(t.G.left, W), ∀ (O : t.G.left.Opens) (hO : O ≤ W) (f : Γ(t.G.left, O)), e O f = ∑ a, resG t.G.left hO (c a) * δ a O f := by
  first | exact @GlobalTheory.VertSpan.vert_span | exact GlobalTheory.VertSpan.vert_span | (intros; apply GlobalTheory.VertSpan.vert_span <;> assumption)
end
