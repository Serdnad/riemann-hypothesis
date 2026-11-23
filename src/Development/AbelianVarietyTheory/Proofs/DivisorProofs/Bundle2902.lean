module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2771
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2772
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle815
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle112
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2775
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorPartTorusExtension
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle003

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.splitOver_powObj_eight : ∀ (R : Type) [CommRing R] (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (I : Ideal R), GlobalTheory.LN.SplitOver G₀ I → GlobalTheory.LN.SplitOver (powObj G₀ 8) I := by
  first | exact @GlobalTheory.SplitPow.splitExtensionModuloIdeal_eighth_power | exact GlobalTheory.SplitPow.splitExtensionModuloIdeal_eighth_power | (intros; apply GlobalTheory.SplitPow.splitExtensionModuloIdeal_eighth_power <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

namespace GlobalTheory.Poinc.Sep.Spz

theorem exists_stalk_factor : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (R : Subalgebra o Ω) (K : Type) [Field K] (x : Sp K ⟶ M.Z) (yK : R →+* K), (∀ a ∈ R, a ∈ M.O (x (closedPoint K))) → (∀ a : R, yK a = M.val x a) → ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsNoetherianRing O) (_ : IsIntegrallyClosed O) (_ : Algebra O Ω) (_ : IsFractionRing O Ω) (xO : Sp O ⟶ M.Z) (u : R →+* O) (v : O →+* K), spMap (algebraMap O Ω) ≫ xO = M.pt ∧ (algebraMap O Ω).comp u = R.val.toRingHom ∧ spMap v ≫ xO = x ∧ v.comp u = yK := by
  intro o Ω _ _ _ _ M hN R K _ x yK hR hy
  haveI := ArithBase.ded (o := o) (Ω := Ω)
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  haveI : IsIntegrallyClosed (M.O (x (closedPoint K))) := RatModel.isIntegrallyClosed_O (M := M) hN _
  haveI : IsNoetherianRing (M.O (x (closedPoint K))) :=
    isNoetherianRing_of_ringEquiv _ (M.stalkEquiv (x (closedPoint K)))
  have h1 : CommRingCat.ofHom (M.stalkEquiv (x (closedPoint K))).toRingHom ≫
      CommRingCat.ofHom (algebraMap (M.O (x (closedPoint K))) Ω) =
      M.Z.presheaf.stalkSpecializes (M.pt_specializes (closedPoint Ω) (x (closedPoint K))) ≫
        Scheme.stalkClosedPointTo (R := CommRingCat.of Ω) M.pt := by
    ext a; rfl
  have h3 : CommRingCat.ofHom (M.stalkEquiv (x (closedPoint K))).toRingHom ≫
      CommRingCat.ofHom (RatModel.valLoc x (x (closedPoint K)) specializes_rfl) =
      M.Z.presheaf.stalkSpecializes (specializes_rfl (x := x (closedPoint K))) ≫
        Scheme.stalkClosedPointTo (R := CommRingCat.of K) x := by
    ext a; simp [RatModel.valLoc]
  refine ⟨M.O (x (closedPoint K)), inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, spMap (M.stalkEquiv (x (closedPoint K))).toRingHom ≫ M.Z.fromSpecStalk (x (closedPoint K)),
    (Subalgebra.inclusion (fun a ha => hR a ha) : R →ₐ[o] M.O (x (closedPoint K))).toRingHom,
    RatModel.valLoc x (x (closedPoint K)) specializes_rfl, ?_, ?_, ?_, ?_⟩
  · rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, h1, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · ext a; rfl
  · rw [← Category.assoc, spMap, spMap, ← Spec.map_comp, h3, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · ext a
    simp [RatModel.valLoc_eq_val, hy]

end GlobalTheory.Poinc.Sep.Spz
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical


theorem _root_.GlobalTheory.T.exists_affineOpen_finiteType_int_of_model : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (x : M.Z), ∃ U : M.Z.Opens, IsAffineOpen U ∧ x ∈ U ∧ Algebra.FiniteType ℤ Γ(M.Z, U) := by
  first | exact @GlobalTheory.RatModel.exists_affineOpen_finiteType_int | exact GlobalTheory.RatModel.exists_affineOpen_finiteType_int | (intros; apply GlobalTheory.RatModel.exists_affineOpen_finiteType_int <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.isNoetherian_functionFieldModel_arithBase : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), AlgebraicGeometry.IsNoetherian M.Z := by
  first | exact @GlobalTheory.ratModel_isNoetherian_of_arithBase | exact GlobalTheory.ratModel_isNoetherian_of_arithBase | (intros; apply GlobalTheory.ratModel_isNoetherian_of_arithBase <;> assumption)
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

theorem GlobalTheory.ValPt.exists_dvr_factor : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → ∀ (κ : FractionRing V →+* PadicAlgCl p), (∀ x, ‖κ x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → ∀ y : Sp (OO p) ⟶ M.Z, ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (fV : V →+* V') (fK : FractionRing V →+* FractionRing V') (κ' : FractionRing V' →+* PadicAlgCl p) (iV : V' →+* OO p) (ξ : Sp V' ⟶ M.Z), IsLocalHom fV ∧ (∀ x, fK (algebraMap V _ x) = algebraMap V' _ (fV x)) ∧ κ'.comp fK = κ ∧ IsLocalHom iV ∧ (∀ x, (iV x : PadicAlgCl p) = κ' (algebraMap V' _ x)) ∧ spMap iV ≫ ξ = y := by
  intro o Ω _ _ _ _ M p _ V _ _ _ hc κ hV y

  haveI : CharZero (FractionRing V) := κ.charZero
  haveI : CharZero V := (algebraMap V (FractionRing V)).charZero
  set x : M.Z := y (cPt p) with hxdef
  obtain ⟨φ, hφloc, hφ, -⟩ := GlobalTheory.ValPt.exists_unique_stalk_hom M.Z x p y rfl
  obtain ⟨U, hU, hxU, hft⟩ := GlobalTheory.RatModel.exists_affineOpen_finiteType_int o Ω M x
  have hQ := GlobalTheory.PadicUnitBall.padic_mem_range p V hc κ hV
  let y₀ : Γ(M.Z, U) →+* PadicAlgCl p := (OO p).subtype.comp (φ.comp (M.Z.presheaf.germ U x hxU).hom)
  obtain ⟨W, _, _, _, hcW, _, fV, fK, κ', -, hfVloc, -, hfK, hκ', hW, hy₀⟩ :=
    GlobalTheory.DvrFinExt.exists_finite_extension p V hc κ hV hQ Γ(M.Z, U) y₀
  let j : W →+* PadicAlgCl p := κ'.comp (algebraMap W (FractionRing W))
  have hj : Function.Injective j :=
    κ'.injective.comp (IsFractionRing.injective W (FractionRing W))
  let ψ : M.Z.presheaf.stalk x →+* PadicAlgCl p := (OO p).subtype.comp φ

  have hψK : ∀ s, ψ s ∈ κ'.range := by
    intro s
    let xU : U := ⟨x, hxU⟩
    letI := M.Z.presheaf.algebra_section_stalk xU
    haveI := hU.isLocalization_stalk xU
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (hU.primeIdealOf xU).asIdeal.primeCompl (show M.Z.presheaf.stalk (xU : M.Z) from s)
    have hb : IsUnit (algebraMap Γ(M.Z, U) (M.Z.presheaf.stalk (xU : M.Z)) (b : Γ(M.Z, U))) :=
      IsLocalization.map_units _ b
    have hb' : ψ (algebraMap Γ(M.Z, U) (M.Z.presheaf.stalk (xU : M.Z)) (b : Γ(M.Z, U))) ≠ 0 :=
      ((hb.map φ).map (OO p).subtype).ne_zero
    have hga : ∀ c : Γ(M.Z, U), ψ (algebraMap Γ(M.Z, U) (M.Z.presheaf.stalk (xU : M.Z)) c) = y₀ c := fun c => rfl
    obtain ⟨ka, hka⟩ := hy₀ a
    obtain ⟨kb, hkb⟩ := hy₀ (b : Γ(M.Z, U))
    have e1 : ψ s * y₀ b = y₀ a := by
      rw [← hga, ← hga, ← map_mul, hab]
    have hb'' : y₀ b ≠ 0 := by rw [← hga]; exact hb'
    refine ⟨ka * kb⁻¹, ?_⟩
    rw [map_mul, map_inv₀, hka, hkb, ← e1, mul_inv_cancel_right₀ hb'']
  have hψW : ∀ s, ψ s ∈ j.range := by
    intro s
    obtain ⟨k, hk⟩ := hψK s
    have hn : ‖κ' k‖ ≤ 1 := by rw [hk]; exact (mem_OO_iff _).1 (φ s).2
    obtain ⟨w, hw⟩ := (hW k).1 hn
    exact ⟨w, by rw [← hk, ← hw]; rfl⟩
  let e := RingEquiv.ofBijective j.rangeRestrict ⟨fun a b h => hj (congrArg Subtype.val h), j.rangeRestrict_surjective⟩
  let φ' : M.Z.presheaf.stalk x →+* W := e.symm.toRingHom.comp (ψ.codRestrict j.range hψW)
  have hjφ' : ∀ s, j (φ' s) = ψ s := by
    intro s
    have h := e.apply_symm_apply (ψ.codRestrict j.range hψW s)
    exact congrArg Subtype.val h
  have hjO : ∀ w, j w ∈ OO p := fun w => (mem_OO_iff _).2 ((hW _).2 ⟨w, rfl⟩)
  let iV : W →+* OO p := j.codRestrict (OO p) hjO
  have hiVloc : IsLocalHom iV := by
    constructor
    intro w hw
    obtain ⟨u, hu⟩ := hw
    have hw0 : j w ≠ 0 := by
      intro h0
      have : ((u : OO p) : PadicAlgCl p) = 0 := by rw [hu]; exact h0
      exact u.ne_zero (Subtype.ext this)
    have hwne : algebraMap W (FractionRing W) w ≠ 0 := fun h => hw0 (by simp [j, h])
    have hinv : ‖κ' (algebraMap W (FractionRing W) w)⁻¹‖ ≤ 1 := by
      have h1 : ((u⁻¹ : (OO p)ˣ) : OO p) * (u : OO p) = 1 := u.inv_mul
      have h2 : ((((u⁻¹ : (OO p)ˣ) : OO p) : PadicAlgCl p)) * j w = 1 := by
        have := congrArg (fun t : OO p => (t : PadicAlgCl p)) h1
        simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
        rw [hu] at this; exact this
      have h3 : κ' (algebraMap W (FractionRing W) w)⁻¹ = (((u⁻¹ : (OO p)ˣ) : OO p) : PadicAlgCl p) := by
        rw [map_inv₀]
        exact (eq_inv_of_mul_eq_one_left h2).symm
      rw [h3]; exact (mem_OO_iff _).1 (Subtype.prop _)
    obtain ⟨w', hw'⟩ := (hW _).1 hinv
    have hww : w * w' = 1 := by
      apply IsFractionRing.injective W (FractionRing W)
      rw [map_mul, hw', map_one, mul_inv_cancel₀ hwne]
    exact ⟨⟨w, w', hww, by rw [mul_comm]; exact hww⟩, rfl⟩
  have hcomp : iV.comp φ' = φ := by
    ext s
    exact hjφ' s
  refine ⟨W, inferInstance, inferInstance, inferInstance, fV, fK, κ', iV, spMap φ' ≫ M.Z.fromSpecStalk x,
    hfVloc, hfK, hκ', hiVloc, fun w => rfl, ?_⟩
  rw [← Category.assoc, ← hφ, ← hcomp]
  show (Spec.map (CommRingCat.ofHom iV) ≫ Spec.map (CommRingCat.ofHom φ')) ≫ _ = Spec.map (CommRingCat.ofHom (iV.comp φ')) ≫ _
  rw [← Spec.map_comp]
  rfl
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


theorem _root_.GlobalTheory.T.thetaGroupOfPoint_eq_along_modelHom : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (M Y : RatModel o Ω) (q : Y.Z ⟶ M.Z), Y.pt ≫ q = M.pt → M.HasDiv S.th → ∀ w : Y.Z, S.HH Y w = S.HH M (q w) := by
  first | exact @GlobalTheory.Poinc.HHFibre.HH_eq_of_hom | exact GlobalTheory.Poinc.HHFibre.HH_eq_of_hom | (intros; apply GlobalTheory.Poinc.HHFibre.HH_eq_of_hom <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR


theorem _root_.GlobalTheory.T.exists_integralClosure_finite_galoisStable_thetaRing : ∀ {o₁ Ω₁ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [ArithBase o₁ Ω₁] (R₁ : Subalgebra o₁ Ω₁), R₁.FG → (∀ x : Ω₁, ∃ a ∈ R₁, ∃ b ∈ R₁, x = a / b) → ∀ {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [ArithBase o₂ Ω₂] [Algebra Ω₁ Ω₂] [FiniteDimensional Ω₁ Ω₂] (κ : o₁ →+* o₂), κ.Finite → (algebraMap o₂ Ω₂).comp κ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) → ∃ (R : Subalgebra o₂ Ω₂) (h : R₁ →+* R), R.FG ∧ (∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ (∀ a, ((h a : R) : Ω₂) = algebraMap Ω₁ Ω₂ a) ∧ h.Finite ∧ IsIntegrallyClosed R ∧ ∀ σ : Ω₂ ≃ₐ[Ω₁] Ω₂, ∀ x ∈ R, σ x ∈ R := by
  first | exact @GlobalTheory.Poinc.NormalClosureRing.exists_integralClosure_finite | exact GlobalTheory.Poinc.NormalClosureRing.exists_integralClosure_finite | (intros; apply GlobalTheory.Poinc.NormalClosureRing.exists_integralClosure_finite <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_dvr_centred_point_generic_both_models : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (Y X M : RatModel o Ω)
    (f : M.Z ⟶ X.Z) (d : Y.Z ⟶ X.Z), X.IsHom M (AlgHom.id o Ω) f → X.IsHom Y (AlgHom.id o Ω) d → IsOpenImmersion d →
    ∀ z : M.Z, f z ∈ Set.range d → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V)
      (ξ : Sp V ⟶ M.Z) (τ : Sp V ⟶ Y.Z) (κ : Ω →+* FractionRing V), z ∈ Set.range ξ ∧
      spMap (algebraMap V (FractionRing V)) ≫ ξ = spMap κ ≫ M.pt ∧
      spMap (algebraMap V (FractionRing V)) ≫ τ = spMap κ ≫ Y.pt := by
  first | exact @GlobalTheory.DvrTrait.exists_trait | exact GlobalTheory.DvrTrait.exists_trait | (intros; apply GlobalTheory.DvrTrait.exists_trait <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem _root_.GlobalTheory.T.torsionLabel_eq_weilPairing_toricTorsionPoint : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real), ∃ sg : ℤˣ, ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (τ' : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (b : S.Gam), τ' ^ (S.r * S.N) = 1 → (∀ (q : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), q.y = 0 → GlobalTheory.UT.IsTor τ' q.g → QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) q x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left) → ∀ (a : S.Gam) (β : u.D.toPre.X), l.yy a = QuotientAddGroup.mk β → ((τ' (Multiplicative.ofAdd β) : (PadicAlgCl p)ˣ) : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * ((sg : ℤ) • eStd S.g _ b a).val))) := by
  first | exact @GlobalTheory.Poinc.UTestLabel.char_eq_weil_of_label | exact GlobalTheory.Poinc.UTestLabel.char_eq_weil_of_label | (intros; apply GlobalTheory.Poinc.UTestLabel.char_eq_weil_of_label <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR


theorem _root_.GlobalTheory.T.thetaRealisation_labels_injective_of_grpPullback : ∀ {o₂ Ω₂ : Type} [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₂ : ThetaSys o₂ Ω₂) (ρ₂ : S₂.Real) {T : Scheme.{0}} (G : Over T) [GrpObj G] (f : Sp S₂.R ⟶ T) (φ : ρ₂.P.A.left ⟶ G.left), IsGrpPullback ρ₂.P.A G f φ → ∀ x y : S₂.Gam, (ρ₂.pt x).left ≫ φ = (ρ₂.pt y).left ≫ φ → x = y := by
  first | exact @GlobalTheory.Poinc.Sep.realPt_inj_of_grpPullback | exact GlobalTheory.Poinc.Sep.realPt_inj_of_grpPullback | (intros; apply GlobalTheory.Poinc.Sep.realPt_inj_of_grpPullback <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR


theorem _root_.GlobalTheory.T.exists_thetaRealisation_label_perm_of_ringEndo : ∀ {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] (S₁ : ThetaSys o₁ Ω₁) (S₂ : ThetaSys o₂ Ω₂) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (om : S₁.R →+* S₂.R) (φ : ρ₂.P.A.left ⟶ ρ₁.P.A.left), IsGrpPullback ρ₂.P.A ρ₁.P.A (spMap om) φ → ∀ τ : S₂.R →+* S₂.R, τ.comp om = om → ∃ gl : S₂.Gam →+ S₂.Gam, ∀ a, (ρ₂.pt (gl a)).left ≫ φ = spMap τ ≫ (ρ₂.pt a).left ≫ φ := by
  first | exact @GlobalTheory.Poinc.labelHom_of_comp_eq | exact GlobalTheory.Poinc.labelHom_of_comp_eq | (intros; apply GlobalTheory.Poinc.labelHom_of_comp_eq <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.realisedThetaSystem_thetaConstant_neg_even_upToRoot : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (a : S.Gam), ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a := by
  first | exact @GlobalTheory.ThetaParity.theta_neg | exact GlobalTheory.ThetaParity.theta_neg | (intros; apply GlobalTheory.ThetaParity.theta_neg <;> assumption)
end
