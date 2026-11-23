module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2900
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3161
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamily
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2816
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3191
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle185
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2876
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBasisRaynaudTangentInvariantFields
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogDerivPolarizationRaynaudEqPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2940
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3169
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaugedTorusInvariantHeatOperator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3136
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataPsiMemMaximalIdealTendstoZero
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc

private theorem fieldPt_lift_preimm {X' X : Scheme.{0}} (j : X' ⟶ X) [IsPreimmersion j] {K : Type} [Field K]
    (y : Sp K ⟶ X) (ξ : X') (h : y (IsLocalRing.closedPoint K) = j ξ) : ∃ z : Sp K ⟶ X', z ≫ j = y := by
  obtain ⟨⟨p, φ⟩, hy⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
  have hp : p = j ξ := by
    rw [← h, ← hy]
    exact (X.fromSpecResidueField_apply p _).symm
  subst hp
  have : IsIso (j.residueFieldMap ξ) := by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨(j.residueFieldMap ξ).hom.injective, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := X'.residue_surjective ξ a
    obtain ⟨b, rfl⟩ := j.stalkMap_surjective ξ a
    exact ⟨X.residue _ b, congr($(Scheme.residue_residueFieldMap j ξ).hom b)⟩
  refine ⟨Spec.map (inv (j.residueFieldMap ξ) ≫ φ) ≫ X'.fromSpecResidueField ξ, ?_⟩
  rw [← hy, Scheme.SpecToEquivOfField_symm_apply, Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← Spec.map_comp,
    IsIso.hom_inv_id_assoc]

theorem oAct_along_traits_of_over : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (r : Y.Z ⟶ C.Z), X₁.S.Over₀ Y U₀ → Y.pt ≫ r = X₁.uΩ ≫ C.i → ∃ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) ∧ (∀ z : Y.Z, r z ∈ Set.range C.i → z ∈ abLocus out.G) ∧ (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ Y.Z), jK T.V ≫ ξ ≫ r = T.y ≫ C.i → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) := by
  intro E _ _ _ H Dw l Xo c C X₁ Y U₀ EE out r hO hpt
  obtain ⟨wi⟩ := nonempty_uWit X₁
  obtain ⟨f, ψ, hfm, -, -, -, H0⟩ := GlobalTheory.T.semiAbelianAction_eq_universal_at_fieldPoints_of_thetaModel E H Dw l Xo c C X₁ Y U₀ EE out r hO hpt wi
  refine ⟨f, hfm, ?_, ?_⟩
  · rintro z ⟨x, hx⟩ K _ _ t ⟨p, hp⟩
    haveI := C.isPreimmersion_i
    obtain ⟨y, hy⟩ := fieldPt_lift_preimm C.i (t ≫ r) x (by
      have e : (t ≫ r) (IsLocalRing.closedPoint K) = r (t p) := by
        rw [Subsingleton.elim (α := PrimeSpectrum K) (IsLocalRing.closedPoint K) p]
        exact Scheme.Hom.comp_apply _ _ _
      rw [e, hp, hx])
    obtain ⟨tK, ⟨m⟩⟩ := GlobalTheory.ModFam.exists_sabPull (y ≫ pullback.fst _ _) Xo.univ.t
    obtain ⟨γ, hγ, -, -⟩ := H0 K t y hy.symm tK ⟨m⟩
    haveI : IsProper Xo.univ.t.G.hom := Xo.univ.proper
    haveI : IsProper tK.G.hom := MorphismProperty.of_isPullback m.cart.1 inferInstance
    rw [← hγ.1.isoPullback_inv_snd]
    infer_instance
  · intro T ξ hξ
    obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
    obtain ⟨γ, hγ, hγL, hγa⟩ := H0 (FractionRing T.V) (jK T.V ≫ ξ) T.y (by rw [Category.assoc]; exact hξ) tK ⟨m₂⟩
    obtain ⟨β, hβ, hφβ, hβa⟩ := GlobalTheory.T.exists_grpPullback_completeDVR_of_generic_compat T.V T.cdvr T.t.G T.t.semi Y.Z out.G out.semi ξ tK.G m₁.φ γ m₁.cart hγ
    refine ⟨β, hβ, ?_, fun a => hβa (T.t.act.act a) (f a) (tK.act.act a) (m₁.act a) (hγa a)⟩
    have h₁ : LBIso tK.PP.L (T.t.PP.L.pull m₁.φ) := by
      obtain ⟨w, hw, -⟩ := m₁.lin
      exact ⟨w, hw⟩
    have hL := out.L.isLB
    refine GlobalTheory.T.lineBundleIso_of_generic_semiAbelian_completeDVR T.V T.cdvr T.t.G T.t.semi tK.G m₁.φ m₁.cart _ _ T.t.PP.isLB (pull_isLB hL β) ?_
    exact LBIso.trans (pull_isLB T.t.PP.isLB _) tK.PP.isLB (pull_isLB (pull_isLB hL β) _) (LBIso.symm h₁)
      (LBIso.trans tK.PP.isLB (pull_isLB hL γ) (pull_isLB (pull_isLB hL β) _) hγL
        (GenSpread.lbIso_pull_pull hL m₁.φ hφβ.symm))

end GlobalTheory.UPoinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc

theorem oAct_along_traits : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → ∃ f : 𝓞 E → (out.G ⟶ out.G), (∀ a, IsMonHom (f a)) ∧ (∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ∃ β : T.t.G.left ⟶ out.G.left, IsGrpPullback T.t.G out.G ξ β ∧ LBIso T.t.PP.L (out.L.L.pull β) ∧ ∀ a, (T.t.act.act a).left ≫ β = β ≫ (f a).left) := by
  intro E _ _ _ H Dw l Xo c C X₁ M U₀ EE out hAdm
  obtain ⟨f, hfm, H0⟩ := GlobalTheory.T.integerAction_extends_semiAbelian_thetaModel E H Dw l Xo c C X₁ M U₀ EE out hAdm
  refine ⟨f, hfm, ?_⟩
  rintro T ξ ⟨ξ₀, hξ₀, hlies⟩
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := T.gen
  obtain ⟨γ, hγ, hγL, hγa⟩ := H0 (FractionRing T.V) ξ₀ T.y hlies tK ⟨m₂⟩
  obtain ⟨β, hβ, hφβ, hβa⟩ := GlobalTheory.T.exists_grpPullback_completeDVR_of_generic_compat T.V T.cdvr T.t.G T.t.semi M.Z out.G out.semi ξ tK.G m₁.φ γ m₁.cart
    (hγ.congr hξ₀ rfl)
  refine ⟨β, hβ, ?_, fun a => hβa (T.t.act.act a) (f a) (tK.act.act a) (m₁.act a) (hγa a)⟩
  have h₁ : LBIso tK.PP.L (T.t.PP.L.pull m₁.φ) := by
    obtain ⟨w, hw, -⟩ := m₁.lin
    exact ⟨w, hw⟩
  have hL := out.L.isLB
  refine GlobalTheory.T.lineBundleIso_of_generic_semiAbelian_completeDVR T.V T.cdvr T.t.G T.t.semi tK.G m₁.φ m₁.cart _ _ T.t.PP.isLB (pull_isLB hL β) ?_
  exact LBIso.trans (pull_isLB T.t.PP.isLB _) tK.PP.isLB (pull_isLB (pull_isLB hL β) _) (LBIso.symm h₁)
    (LBIso.trans tK.PP.isLB (pull_isLB hL γ) (pull_isLB (pull_isLB hL β) _) hγL
      (GenSpread.lbIso_pull_pull hL m₁.φ hφβ.symm))

end GlobalTheory.UPoinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PolDeg.refine_monomial_of_polarised : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : Data R) (m : ℕ) (t : Fin m → R) (δ : Fin m → LinearMap.BilinForm ℤ Q.X), IsCN R → Q.IsMonomialTau t δ → (∀ i, t i ∈ maximalIdeal R) → (∀ i, t i ≠ 0) → (∀ i y z, δ i y z = δ i z y) → (∀ i y, 0 ≤ δ i y y) → (∀ y, y ≠ 0 → ∃ i, 0 < δ i y y) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : Fin m → R') (D : DegData R' (maximalIdeal R')) (e : D.toPre.X ≃+ Q.X), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ Refines Q ρ D.toPre e ∧ IsMonomial D.toPre r fun i => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ i) := by
  intro R _ _ _ Q m t δ hCN hmono htm ht0 hsymm hnn hdef
  obtain ⟨R₁, _, _, _, ρ₁, P, β, β₂, hCN₁, hinj₁, hfin₁, hloc₁, hpb, hsq, hiso⟩ := GlobalTheory.T.exists_symmetricPolarisation_finiteExtension R Q hCN
  haveI : IsNoetherianRing R₁ := hCN₁.1
  obtain ⟨D, e, f, hD⟩ := GlobalTheory.T.exists_symmetric_data_compare_polarised_up_to_function R R₁ Q ρ₁ P β β₂ hinj₁ hpb hsq hiso
  obtain ⟨hfs, hfc⟩ := GlobalTheory.T.polarisedPeriod_comparison_symm_cocycle R R₁ Q ρ₁ D e f hinj₁ hD
  obtain ⟨g, hg⟩ := GlobalTheory.T.symmetric_twoCocycle_free_abelian_isCoboundary D.X _ f hfs hfc
  have hD₁ : Half Q ρ₁ (rescale D g) e (fun _ _ => 1) :=
    GlobalTheory.T.refinesPolarisedData_rescale_coboundary R R₁ Q ρ₁ D e f (fun _ _ => 1) g hD (fun a b => by rw [hg a b, _root_.mul_one])
  have hb₁ : (rescale D g).TauBimult := GlobalTheory.T.tauBimult_of_refines_polarised_data R R₁ Q ρ₁ (rescale D g) e hinj₁ hD₁
  obtain ⟨h, hhom, hev⟩ := GlobalTheory.T.exists_hom_evenDefect_bimultiplicative_periods R₁ (rescale D g) hb₁
  obtain ⟨R₂, _, _, _, σ, gam, r, et, hCN₂, hinj₂, hfin₂, hloc₂, hgam, hr, hη, hη2⟩ :=
    GlobalTheory.T.exists_sqrt_latticeHom_finiteExtension_complete R₁ (rescale D g).X h m (fun i => ρ₁ (t i)) hCN₁ hhom
  haveI : IsNoetherianRing R₂ := hCN₂.1
  obtain ⟨D₂, β', v, xe, hpb', hv, hc', hrig, hpsi⟩ := GlobalTheory.T.exists_baseChange_raw_degenerationData_injective R₁ R₂ σ (rescale D g) gam hgam
  have hD₂ := GlobalTheory.T.refinesPolarisedData_baseChange_symmetric R Q R₁ R₂ σ (rescale D g) D₂ β' v xe gam hgam hpb' hv hc' hrig hpsi ρ₁ e hinj₁ hD₁
  have hev₂ := GlobalTheory.T.evenDefect_degenerationData_baseChange R₁ R₂ σ (rescale D g) D₂ β' v xe gam hgam hpb' hv hc' hrig hpsi h hev
  have hinj : Function.Injective (σ.comp ρ₁) := hinj₂.comp hinj₁
  have hηx : ∀ a b : D₂.X, et (xe (a + b)) = et (xe a) * et (xe b) := fun a b => by rw [map_add (f := _), hη]
  have hD₃ : Half Q (σ.comp ρ₁) (rescale D₂ fun χ => et (xe χ)) (xe.trans e) (fun _ _ => 1) :=
    GlobalTheory.T.refinesPolarisedData_rescale_coboundary R R₂ Q (σ.comp ρ₁) D₂ (xe.trans e) (fun _ _ => 1) (fun _ _ => 1) (fun χ => et (xe χ)) hD₂
      (fun a b => by rw [hηx, _root_.mul_one, mul_right_comm (et (xe a)), mul_inv_cancel, _root_.one_mul, mul_inv_cancel])
  have hev₃ : (rescale D₂ fun χ => et (xe χ)).PsiEven :=
    GlobalTheory.T.rescaleDegDataTrivialisations_psiEven_of_sqrt R₂ D₂ _ (fun χ => et (xe χ)) hev₂ hηx (fun a => hη2 (xe a))
  have hb₃ : (rescale D₂ fun χ => et (xe χ)).TauBimult :=
    GlobalTheory.T.tauBimult_of_refines_polarised_data R R₂ Q (σ.comp ρ₁) _ (xe.trans e) hinj hD₃
  have hr' : ∀ i, r i ^ 2 = (σ.comp ρ₁) (t i) := fun i => hr i
  have hmon := GlobalTheory.T.exists_monomial_trivialisation_sqrt_refinedPolarisedData R R₂ Q (σ.comp ρ₁) (rescale D₂ fun χ => et (xe χ)) (xe.trans e) m t r δ hCN₂ hinj hD₃
    hev₃ hb₃ hmono hnn ht0 hr'
  have hrm : ∀ i, r i ∈ maximalIdeal R₂ := by
    intro i
    refine (inferInstance : (maximalIdeal R₂).IsPrime).mem_of_pow_mem 2 ?_
    rw [hr' i, mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (mem_maximalIdeal _).1 (htm i) ((isUnit_map_iff (σ.comp ρ₁) _).1 hu)
  have key : ∀ (D₃ : DegPre R₂) (e' : D₃.X ≃+ Q.X), D₃.PsiEven → D₃.TauBimult →
      Half Q (σ.comp ρ₁) D₃ e' (fun _ _ => 1) →
      IsMonomial D₃ r (fun i => (2 : ℤ) • pull e'.toIntLinearEquiv.toLinearMap (δ i)) →
      ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (r : Fin m → R')
        (D : DegData R' (maximalIdeal R')) (e : D.toPre.X ≃+ Q.X), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧
        IsLocalHom ρ ∧ (∀ i, r i ^ 2 = ρ (t i)) ∧ Refines Q ρ D.toPre e ∧
        IsMonomial D.toPre r fun i => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ i) := by
    intro D₃ e' h1 h2 h3 h4
    obtain ⟨DD, rfl⟩ := GlobalTheory.T.degenerationData_of_monomial_even_bimultiplicative R₂ D₃ m r (fun i => (2 : ℤ) • pull e'.toIntLinearEquiv.toLinearMap (δ i))
      h1 h2 h4 hrm (fun i y z => by simp [pull, hsymm i (e' y) (e' z)])
      (fun y hy => by
        obtain ⟨i, hi⟩ := hdef (e' y) (by simpa using hy)
        exact ⟨i, by simpa [pull] using hi⟩)
    exact ⟨R₂, inferInstance, inferInstance, inferInstance, σ.comp ρ₁, r, DD, e', hCN₂, hinj,
      hfin₂.comp hfin₁, inferInstance, hr', h3.refines, h4⟩
  exact key _ _ hev₃ hb₃ hD₃ hmon
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
open GlobalTheory.Mum.TensPos GlobalTheory.PsiScalUnit GlobalTheory.Mum.TensPol

theorem _root_.GlobalTheory.T.exists_periodScalarCoordinate_polarisedData_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (Q : GlobalTheory.PolDeg.Data R) (a b : Q.X), ∃ k, Q.TauCoord a b k := by
  first | exact @GlobalTheory.Mum.TensPol.exists_tauCoord | exact GlobalTheory.Mum.TensPol.exists_tauCoord | (intros; apply GlobalTheory.Mum.TensPol.exists_tauCoord <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FlagTan

theorem exists_dir_eq_of_smooth : ∀ (k₀ : Type) [Field k₀] (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k₀)) (n : ℕ),
    SmoothOfRelativeDimension n s → ∀ (K : Type) [Field K] (κ : k₀ →+* K) (ι : Type) [Fintype ι],
    Fintype.card ι = n → ∀ Xι : Spec (CommRingCat.of (TrivSqZeroExt K (ι → K))) ⟶ X,
    Xι ≫ s = Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.inlHom K (ι → K)).comp κ)) →
    (∀ M M' : ι → K,
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom) ≫ Xι =
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (Fintype.linearCombination K M')).toRingHom) ≫ Xι → M = M') →
    ∀ x' : Spec (CommRingCat.of (DualNumber K)) ⟶ X,
    x' ≫ s = Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.inlHom K K).comp κ)) →
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ x' =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom) ≫ Xι →
    ∃ M : ι → K, x' = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom) ≫ Xι := by
  intro k₀ _ X s n hs K _ κ ι _ hι Xι hXs hinj x' hx's hred
  have hloc : ∀ (M : Type) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M],
      IsLocalHom (TrivSqZeroExt.fstHom K K M).toRingHom :=
    fun M _ _ _ _ => ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
  have cp : ∀ (M : Type) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M],
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K M).toRingHom) (IsLocalRing.closedPoint K) =
        IsLocalRing.closedPoint (TrivSqZeroExt K M) := fun M _ _ _ _ => by
    haveI := hloc M
    exact IsLocalRing.comap_closedPoint _
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := hs.exists_isStandardSmoothOfRelativeDimension
    ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom) ≫ Xι) (IsLocalRing.closedPoint K))
  have h1 : Xι (IsLocalRing.closedPoint (TrivSqZeroExt K (ι → K))) ∈ V := by
    rw [← cp]; exact hxV
  have h2 : x' (IsLocalRing.closedPoint (DualNumber K)) ∈ V := by
    rw [← cp]; have := hxV; rw [← hred] at this; exact this
  obtain ⟨R, rfl⟩ := GlobalTheory.T.exists_ringHom_spec_factor_fromSpec_of_closedPoint_mem X V hV _ Xι h1
  obtain ⟨g, rfl⟩ := GlobalTheory.T.exists_ringHom_spec_factor_fromSpec_of_closedPoint_mem X V hV _ x' h2
  letI := (s.appLE U V e).hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n Γ(Spec (CommRingCat.of k₀), U) Γ(X, V) := hstd
  have key := IsAffineOpen.SpecMap_appLE_fromSpec s hU hV e
  have mono : ∀ {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) {A : Type} [CommRing A] (φ ψ : Γ(Y, W) →+* A),
      Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec = Spec.map (CommRingCat.ofHom ψ) ≫ hW.fromSpec → φ = ψ := by
    intro Y W hW A _ φ ψ h
    have := Spec.map_injective ((cancel_mono hW.fromSpec).1 h)
    exact congrArg CommRingCat.Hom.hom this
  have hsp : ∀ {A : Type} [CommRing A] (φ : Γ(X, V) →+* A),
      (Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec) ≫ s =
        Spec.map (CommRingCat.ofHom (φ.comp (s.appLE U V e).hom)) ≫ hU.fromSpec := by
    intro A _ φ
    rw [Category.assoc, ← key, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hc : ∀ (M : Type) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
      (φ : Γ(X, V) →+* TrivSqZeroExt K M),
      (Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec) ≫ s =
        Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.inlHom K M).comp κ)) →
      ∀ a, φ (s.appLE U V e a) = TrivSqZeroExt.inl (φ (s.appLE U V e a)).fst := by
    intro M _ _ _ _ φ hφ a
    have e1 := hsp φ
    have e2 : Spec.map (CommRingCat.ofHom (((TrivSqZeroExt.inlHom K M).comp (TrivSqZeroExt.fstHom K K M).toRingHom).comp
        (φ.comp (s.appLE U V e).hom))) ≫ hU.fromSpec =
        Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.inlHom K M).comp κ)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← e1, hφ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    have := mono hU _ _ (e2.trans (hφ.symm.trans e1))
    exact (RingHom.congr_fun this a).symm
  obtain ⟨M, hM⟩ := GlobalTheory.T.square_zero_deformation_factors_through_linear Γ(Spec (CommRingCat.of k₀), U) Γ(X, V) K n hstd ι hι R (hc _ R hXs)
    (fun M M' h => hinj M M' (by
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, h]))
    g (fun b => by
      have := mono hV ((TrivSqZeroExt.fstHom K K K).toRingHom.comp g) ((TrivSqZeroExt.fstHom K K (ι → K)).toRingHom.comp R) (by
        rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]
        exact hred)
      exact RingHom.congr_fun this b)
    (hc _ g hx's)
  refine ⟨M, ?_⟩
  rw [hM, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

theorem eq_of_isKS_eq : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' x'' : Sp (DualNumber K) ⟶ Xo.X) (M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsTanX y x'' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x'' M → x' = x'' := by
  intro hP hG E _ _ _ H Dw l Xo c K _ _ y x' x'' M hpq h' h'' k' k''
  obtain ⟨X, hX, hXy, hXM⟩ : ∃ X : Sp (TrivSqZeroExt K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧
      spMap (TrivSqZeroExt.fstHom c.F K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)).toRingHom ≫ X = y.x ∧
      ∀ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K,
        GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) M := by
    first
    | exact GlobalTheory.T.universal_first_order_deformation hP hG E H Dw l Xo c K y hpq
    | exact GlobalTheory.T.universal_first_order_deformation hP E H Dw l Xo c K y hpq
    | exact (GlobalTheory.T.universal_first_order_deformation hP hG E H Dw l Xo c K y hpq)
  have htan : ∀ N, GlobalTheory.FlagTan.IsTanX y (spMap (GlobalTheory.FlagTan.dir c N).toRingHom ≫ X) := fun N => by
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, hX, sOf, sOf, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact (GlobalTheory.FlagTan.dir c N).commutes _
    · rw [← Category.assoc, ← Spec.map_comp, ← hXy]
      congr 2
      ext z
      simp
  have uniq := fun x hx => GlobalTheory.T.kodaira_spencer_matrix_unique hP E H Dw l Xo c K y x hpq hx
  have key := exists_dir_eq_of_smooth (KA l) Xo.X Xo.s Dw.dim Xo.smooth K ((algebraMap c.F K).comp (IntermediateField.inclusion c.le).toRingHom)
    (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H)) (GlobalTheory.FlagTan.card_HIx (GlobalTheory.FlagTan.isHalf_psiSet H)) X
    (by rw [hX, sOf])
    (fun N N' e => uniq _ (htan N) N N' (hXM N) (e ▸ hXM N'))
  have hk : ∀ x, GlobalTheory.FlagTan.IsTanX y x → ∃ N, x = spMap (GlobalTheory.FlagTan.dir c N).toRingHom ≫ X := fun x hx =>
    key x (by rw [hx.1, sOf]) (hx.2.trans hXy.symm)
  obtain ⟨N', rfl⟩ := hk x' h'
  obtain ⟨N'', rfl⟩ := hk x'' h''
  rw [uniq _ (htan N') N' M (hXM N') k', uniq _ (htan N'') N'' M (hXM N'') k'']

end GlobalTheory.FlagTan
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.commuting_heatOperators_act_on_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ (i0 : h.J) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ) (hx' : x' ≫ t.G.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∀ (δL : Fin n → Derivation ℤ (FractionRing Ω) (FractionRing Ω)), (∀ a ω, δL a ((algebraMap Ω (FractionRing Ω)) ω) = (algebraMap Ω (FractionRing Ω)) (δ a ω)) → ∃ (dt : Derivation ℤ (FractionRing Ω) (FractionRing Ω)) (u' : Fin n → (FractionRing Ω)) (p p' : (FractionRing Ω)), (∀ r, dt ((algebraMap Ω (FractionRing Ω)) (φ r)) = (algebraMap Ω (FractionRing Ω)) (φ (D r))) ∧ ∀ (k : ℕ), 1 ≤ k → ∀ s : (FractionRing Ω), (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (s)) → (∃ (r : R) (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ ω ∧ (algebraMap Ω (FractionRing Ω)) ω = (algebraMap Ω (FractionRing Ω)) (φ r) * (ringOp ⇑dt (fun a => ⇑(δL a)) (((algebraMap Ω (FractionRing Ω)).comp φ).mapMatrix h.Θ) u' p p' k s)) := by
  first | exact @GlobalTheory.Heat.heat_acts_on_values | exact GlobalTheory.Heat.heat_acts_on_values | (intros; apply GlobalTheory.Heat.heat_acts_on_values <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatUniq

theorem comb_kills_weight_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (K : Type) (Wk : K → Y.H.left.Opens) (jk : K → Q.P.L.ι), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → (∀ k, Wk k ≤ Y.q.left ⁻¹ᵁ Q.P.L.U (jk k)) → ∀ (P : ∀ k, Γ(Y.H.left, Wk k)) (e : Fin n → R), (∀ k, IsWt Y 0 _ (P k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (P k') Wo - rsT (P k) Wo = ∑ a, constFn Y.H.hom Wo (e a) * dlg Y.H Y.q.left Q.P.L (dd a) (jk k) (jk k') Wo) → ∀ (V : Q.P.A.left.Opens) f, IsWt Y 0 (Y.q.left ⁻¹ᵁ V) f → ∑ a, constFn Y.H.hom _ (e a) * dd a _ f = 0 := by
  intro R _ _ _ _ _ Q O _ _ _ oa Y n v dd hinv K Wk jk hWk hcov hjk P e hP hcob V f hf
  haveI : IsMonHom Y.q := Y.q_linear.isMonHom
  obtain ⟨dw, hdw⟩ := GlobalTheory.RayBasis.exists_isInv (∑ a, e a • v a)
  obtain ⟨δ, hδ⟩ := GlobalTheory.RayBasis.exists_isInv (GlobalTheory.Heat.LiePush.pushL Y.q (∑ a, e a • v a))
  have hcomb : ∀ (W : Y.H.left.Opens) (s : Γ(Y.H.left, W)),
      dw W s = ∑ a, constFn Y.H.hom W (e a) * dd a W s := by
    intro W s
    have h := GlobalTheory.Heat.LiePush.isInv_pbT (𝟙 Y.H) hdw (w := v) hinv e
      (PullbackSections.tanM_ext (by rw [GlobalTheory.Heat.LiePush.tv_pushL]; exact Category.comp_id _)) W s W le_rfl
    simpa only [Over.id_left, GlobalTheory.Heat.LiePush.pbT_id] using h
  have hpull : ∀ (U : Q.P.A.left.Opens) (s : Γ(Q.P.A.left, U)) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ U →
      dw W (pbT Y.q.left s W) = pbT Y.q.left (δ U s) W := by
    intro U s W hW
    have h := GlobalTheory.Heat.LiePush.isInv_pbT Y.q hdw (g := 1) (w := fun _ => GlobalTheory.Heat.LiePush.pushL Y.q (∑ a, e a • v a))
      (d' := fun _ => δ) (fun _ => hδ) (fun _ => 1) (by simp) U s W hW
    have h1 : constFn Q.P.A.hom U (1 : R) = 1 := by simp [constFn]
    simpa [h1] using h
  obtain ⟨Vs, b, hVcov, hVle, hb⟩ := GlobalTheory.T.raynaud_cech_relation_dlog_descends_to_abelian_part R Q O oa Y dw δ hpull K Wk jk hWk hcov hjk P hP
    (fun k k' Wo hWo => by
      rw [hcob k k' Wo hWo]
      simp only [dlg, hcomb, Finset.sum_mul, _root_.mul_assoc])
  have hw0 : GlobalTheory.Heat.LiePush.pushL Y.q (∑ a, e a • v a) = 0 := GlobalTheory.T.tangentVector_eq_zero_of_logDeriv_coboundary R Q.P _ δ hδ K Vs jk hVcov hVle b hb
  have hδ0 : ∀ (U : Q.P.A.left.Opens) (s : Γ(Q.P.A.left, U)), δ U s = 0 := by
    intro U s
    have h := GlobalTheory.Heat.LiePush.isInv_pbT (𝟙 Q.P.A) hδ (g := 0) (w := Fin.elim0) (d' := Fin.elim0)
      (fun a => a.elim0) Fin.elim0
      (by rw [hw0, map_zero]; simp) U s U le_rfl
    simpa only [Over.id_left, GlobalTheory.Heat.LiePush.pbT_id, Finset.univ_eq_empty, Finset.sum_empty] using h
  obtain ⟨g, hg⟩ := GlobalTheory.Heat.AbConst.exists_app_eq Y hf
  have hfg : f = pbT Y.q.left g (Y.q.left ⁻¹ᵁ V) := by
    rw [← hg, GlobalTheory.KS.pbT_of_le _ le_rfl, Scheme.Hom.app_eq_appLE]
  rw [← hcomb, hfg, hpull V g _ le_rfl, hδ0, GlobalTheory.KS.pbT_zero]

end GlobalTheory.HeatUniq
end
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.HeatInvLift.exists_invLift_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (Dd : DegData R (maximalIdeal R)) (O : Type) [CommRing O] [StarRing O] [Module O Dd.toPre.X] (oa : Dd.toPre.OAct O) (Y : Ray oa) (D : Derivation ℤ R R), ∃ (J : Type) (V : J → Dd.toPre.P.A.left.Opens) (j : J → Dd.toPre.P.L.ι) (d : J → Fld Y.H.left), ⨆ i, V i = ⊤ ∧ (∀ i, V i ≤ Dd.toPre.P.L.U (j i)) ∧ (∀ i, IsLift Y.H ⇑D (Y.q.left ⁻¹ᵁ V i) (d i)) ∧ ∀ i, (∀ (α : Dd.toPre.X) (V' : Dd.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ V' ≤ Y.q.left ⁻¹ᵁ V i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V') f → IsWt Y α (Y.q.left ⁻¹ᵁ V') (d i _ f)) := by
  intro R _ _ _ _ _ _ Dd O _ _ _ oa Y D
  let J := {p : Dd.toPre.P.A.left.affineOpens × Dd.toPre.P.L.ι // p.1.1 ≤ Dd.toPre.P.L.U p.2}
  have H := fun i : J => GlobalTheory.T.exists_torusInvariant_lift_derivation_raynaud R Dd.toPre O oa Y i.1.1 D
  choose d hd using H
  refine ⟨J, fun i => i.1.1.1, fun i => i.1.2, d, ?_, fun i => i.2, fun i => (hd i).1, fun i α V' hV' f hf => ?_⟩
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ (⨆ k, Dd.toPre.P.L.U k) := by rw [Dd.toPre.P.isLB.cover]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVk⟩ :=
      Dd.toPre.P.A.left.isBasis_affineOpens.exists_subset_of_mem_open hk (Dd.toPre.P.L.U k).isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨V, hV⟩, k), hVk⟩, hxV⟩
  · have e : Y.q.left ⁻¹ᵁ (V' ⊓ i.1.1.1) = Y.q.left ⁻¹ᵁ V' := by
      rw [Scheme.Hom.preimage_inf]; exact inf_eq_left.2 hV'
    have key := (hd i).2 α (V' ⊓ i.1.1.1) inf_le_right
    rw [e] at key
    exact key f hf
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_gauged_torusInvariant_heatOperator : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd ⇑D), (∀ i, (∃ V : Q.P.A.left.Opens, h₁.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h₁.p i) ∧ IsWt Y 0 _ (h₁.p' i) ∧ ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h₁.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → IsWt Y α (Y.q.left ⁻¹ᵁ V) (h₁.d i _ f)) → ∀ (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X), e.IsGen → (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) → ∃ h' : Heat Y.H Y.q.left Q.P.L dd ⇑D, IsBasic Y h' ∧ h'.Θ = h₁.Θ ∧ h'.u = h₁.u ∧ ∀ (k : ℕ) (σ σ' : SecM ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L k) (ρ ρ' : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ' r z J = sval σ' r z J * ((val e r z J) ^ k).val) → h₁.Acts k σ σ' → h'.Acts k ρ ρ' := by
  first | exact @GlobalTheory.Heat.Gauge.exists_gauge_heat | exact GlobalTheory.Heat.Gauge.exists_gauge_heat | (intros; apply GlobalTheory.Heat.Gauge.exists_gauge_heat <;> assumption)
end
