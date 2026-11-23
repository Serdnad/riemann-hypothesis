module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle225
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitLatticesIsoFormsProportionalRamification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle113
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3163
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3137
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3271
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3199
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3314
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3272
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3348
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle077
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3214
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3174
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2881
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2882
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2893
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3349
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
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.GenTrait

theorem spMap_stalkHom_fromSpecStalk {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω)
    (x : M.Z) : spMap (M.stalkHom x) ≫ M.Z.fromSpecStalk x = M.pt := by
  have e2 : spMap (M.stalkHom x) = spMap (Scheme.stalkClosedPointTo (R := .of Ω) M.pt).hom ≫
      Spec.map (M.Z.presheaf.stalkSpecializes (M.pt_specializes (IsLocalRing.closedPoint Ω) x)) := by
    rw [RatModel.stalkHom]
    show Spec.map _ = _
    rw [CommRingCat.ofHom_hom, Spec.map_comp]
    rfl
  rw [e2, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk M.pt

end GlobalTheory.Poinc.GenTrait


open GlobalTheory.Poinc.GenTrait in
theorem GlobalTheory.Poinc.exists_trait_of_stalk_dvr : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [CharZero Ω] (M : RatModel o' Ω) (y₀ : Sp Ω ⟶ F.X) (x : M.Z) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → ∀ θ : M.Z.presheaf.stalk x →+* V, Function.Injective θ → ∃ (T : Trait F) (f : V →+* T.V) (γ : Ω →+* FractionRing T.V), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, γ (M.stalkHom x a) = algebraMap T.V (FractionRing T.V) (f (θ a))) ∧ jK T.V ≫ spMap (f.comp θ) ≫ M.Z.fromSpecStalk x = spMap γ ≫ M.pt ∧ T.y = spMap γ ≫ y₀ := by
  intro g n o _ ζ F o' Ω _ _ _ _ M y₀ x V _ _ _ hcomp θ hθ
  haveI : CharZero (M.Z.presheaf.stalk x) := (M.stalkHom x).charZero
  haveI : CharZero V := charZero_of_injective_ringHom hθ
  have hB : GlobalTheory.Mum.Base V := ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩
  let θ' : M.O x →+* FractionRing V :=
    ((algebraMap V (FractionRing V)).comp θ).comp (M.stalkEquiv x).symm.toRingHom
  have hθ' : Function.Injective θ' :=
    (IsFractionRing.injective V (FractionRing V)).comp (hθ.comp (M.stalkEquiv x).symm.injective)
  let γ₀ : Ω →+* FractionRing V := IsFractionRing.lift (A := M.O x) (K := Ω) hθ'
  have hγ₀ : ∀ a, γ₀ (M.stalkHom x a) = algebraMap V (FractionRing V) (θ a) := by
    intro a
    have h := IsFractionRing.lift_algebraMap (A := M.O x) (K := Ω) hθ' (M.stalkEquiv x a)
    rw [← RatModel.coe_stalkEquiv]
    refine h.trans ?_
    simp [θ']
  obtain ⟨T, f, fK, hfi, hfl, -, hc, hy⟩ :=
    GlobalTheory.Poinc.traitExtSt g n o ζ F V hB inferInstance (spMap γ₀ ≫ y₀)
  refine ⟨T, f, fK.comp γ₀, hfi, hfl, ?_, ?_, ?_⟩
  · intro a
    rw [RingHom.comp_apply, hγ₀, hc]
  · have e : (algebraMap T.V (FractionRing T.V)).comp (f.comp θ) = (fK.comp γ₀).comp (M.stalkHom x) := by
      ext a
      simp only [RingHom.comp_apply, hγ₀, hc]
    rw [← spMap_stalkHom_fromSpecStalk M x, ← Category.assoc, Formalism.L2.Pj.spMap_comp', e, ← Formalism.L2.Pj.spMap_comp',
      Category.assoc]
  · rw [hy, ← Category.assoc, Formalism.L2.Pj.spMap_comp']
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TraitExtLab

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  show Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp]
  rfl

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (u' : Sp S.R ⟶ F.X) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₀ ≫ u' = spMap ι ≫ T.y → ∃ (T' : Trait F) (ι' : FractionRing T'.V →+* PadicAlgCl p) (yK : S.R →+* FractionRing T'.V) (e : T'.D.toPre.X ≃+ T.D.toPre.X) (k : ℕ), (∀ x, ‖ι' x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T'.V (FractionRing T'.V))) ∧ ι'.comp yK = y₀ ∧ spMap yK ≫ u' = T'.y ∧ ‖ι (algebraMap T.V _ T.ϖ)‖ = ‖ι' (algebraMap T'.V _ T'.ϖ)‖ ^ k ∧ ∀ a b, T'.β a b = k * T.β (e a) (e b) := by
  intro g n F o Ω _ _ _ _ S u' p _ y₀ T ι hι hy
  haveI : Algebra.FiniteType ℤ o := ArithBase.ft (o := o) (Ω := Ω)
  haveI : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  haveI : Algebra.FiniteType ℤ S.R := Algebra.FiniteType.trans (S := o) inferInstance inferInstance
  have hQ := GlobalTheory.T.padic_mem_range_complete_dvr_padicAlgCl p T.V T.complete ι hι
  obtain ⟨W, _, _, _, hWc, _, fV, fK, κ, hfV, hfVl, -, hfK, hκι, hκ, hy₀⟩ :=
    GlobalTheory.T.exists_finite_extension_complete_dvr_padicAlgCl p T.V T.complete ι hι hQ S.R y₀
  have hbase : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hWc⟩, inferInstance⟩
  obtain ⟨T', f, gK, hf, hfl, hff, hgK, hTy⟩ :=
    traitExtSt g n _ (zetaAway n) F W hbase inferInstance (spMap fK ≫ T.y)
  letI : Algebra (FractionRing W) (FractionRing T'.V) := gK.toAlgebra
  letI : Algebra W T'.V := f.toAlgebra
  haveI : Module.Finite W T'.V := hff
  haveI : Algebra.IsIntegral W T'.V := Algebra.IsIntegral.of_finite W T'.V
  haveI : IsLocalHom (algebraMap W T'.V) := hfl
  have hcomp : (algebraMap (FractionRing W) (FractionRing T'.V)).comp (algebraMap W (FractionRing W)) =
      (algebraMap T'.V (FractionRing T'.V)).comp (algebraMap W T'.V) := RingHom.ext hgK
  have hI : ∀ a : T'.V, _root_.IsIntegral (FractionRing W) (algebraMap T'.V (FractionRing T'.V) a) := fun a =>
    IsIntegral.map_of_comp_eq (algebraMap W (FractionRing W)) (algebraMap T'.V (FractionRing T'.V)) hcomp
      (Algebra.IsIntegral.isIntegral a)
  haveI : Algebra.IsAlgebraic (FractionRing W) (FractionRing T'.V) := ⟨fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := T'.V) x
    rw [div_eq_mul_inv]
    exact (hI a).isAlgebraic.mul (hI b).isAlgebraic.inv⟩
  letI : Algebra (FractionRing W) (PadicAlgCl p) := κ.toAlgebra
  let ιA : FractionRing T'.V →ₐ[FractionRing W] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let ι' : FractionRing T'.V →+* PadicAlgCl p := ιA
  have hι'κ : ι'.comp gK = κ := ιA.comp_algebraMap
  have hint := GlobalTheory.unitBall_eq_of_integral_dvr p W T'.V hf κ ι' (fun v => by
    show ι' (algebraMap T'.V (FractionRing T'.V) (f v)) = _
    rw [← hgK]
    exact congrArg (fun h : FractionRing W →+* PadicAlgCl p => h (algebraMap W (FractionRing W) v)) hι'κ) hκ
  have hιc : ι'.comp (gK.comp fK) = ι := by rw [← RingHom.comp_assoc, hι'κ, hκι]

  have hr : ∀ a, y₀ a ∈ ι'.range := fun a => by
    obtain ⟨x, hx⟩ := hy₀ a
    exact ⟨gK x, by rw [← hx, ← hι'κ]; rfl⟩
  let eι : FractionRing T'.V ≃+* ι'.range := RingEquiv.ofBijective ι'.rangeRestrict
    ⟨fun a b hab => ι'.injective (congrArg Subtype.val hab), ι'.rangeRestrict_surjective⟩
  let yK : S.R →+* FractionRing T'.V := eι.symm.toRingHom.comp (y₀.codRestrict ι'.range hr)
  have hyK : ι'.comp yK = y₀ := RingHom.ext fun a =>
    congrArg Subtype.val (eι.apply_symm_apply (y₀.codRestrict ι'.range hr a))

  have hne : f (fV T.ϖ) ≠ 0 := fun h => T.irr.ne_zero (hfV (hf (by rw [h, map_zero, map_zero])))
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne T'.irr
  have hbase' : GlobalTheory.Mum.Base T'.V := ⟨⟨inferInstance, inferInstance, inferInstance, T'.complete⟩, inferInstance⟩
  haveI : IsLocalHom (f.comp fV) := by
    haveI : IsLocalHom f := hfl
    haveI : IsLocalHom fV := hfVl
    exact RingHom.isLocalHom_comp f fV
  obtain ⟨e₀, he₀⟩ := TraitUniq.traitUniq g n _ (zetaAway n) F T T' T'.V (f.comp fV) (RingHom.id _) (gK.comp fK)
    (RingHom.id _) hbase' inferInstance (hf.comp hfV) Function.injective_id inferInstance inferInstance
    (fun a => by simp only [RingHom.comp_apply, hfK, hgK]) (fun a => rfl)
    (by rw [hTy, spMap_comp', Category.assoc]; rw [show spMap (RingHom.id (FractionRing T'.V)) = 𝟙 _ from Spec.map_id _, Category.id_comp])
    T'.ϖ m 1 T'.irr hm (by rw [pow_one, RingHom.id_apply])
  refine ⟨T', ι', yK, e₀.symm, m, hint, hyK, ?_, ?_, ?_⟩
  · haveI : Epi (spMap ι') := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (spMap ι'), ← Category.assoc, ← spMap_comp', hyK, hy, hTy, ← hιc, spMap_comp', spMap_comp',
      Category.assoc, Category.assoc]
  · obtain ⟨u, hu⟩ := hm
    have hunit : ∀ w : T'.Vˣ, ‖ι' (algebraMap T'.V _ (w : T'.V))‖ = 1 := fun w => by
      have h1 := (hint _).2 ⟨(w : T'.V), rfl⟩
      have h2 := (hint _).2 ⟨((w⁻¹ : T'.Vˣ) : T'.V), rfl⟩
      have h3 : ‖ι' (algebraMap T'.V _ (w : T'.V))‖ * ‖ι' (algebraMap T'.V _ ((w⁻¹ : T'.Vˣ) : T'.V))‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
      nlinarith [norm_nonneg (ι' (algebraMap T'.V _ (w : T'.V))),
        norm_nonneg (ι' (algebraMap T'.V _ ((w⁻¹ : T'.Vˣ) : T'.V)))]
    have e1 : ι (algebraMap T.V _ T.ϖ) = ι' (algebraMap T'.V _ (f (fV T.ϖ))) := by
      rw [← hιc, RingHom.comp_apply, RingHom.comp_apply, hfK, hgK]
    have e2 : f (fV T.ϖ) = T'.ϖ ^ m * ((u⁻¹ : T'.Vˣ) : T'.V) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [e1, e2, map_mul, map_mul, norm_mul, hunit, mul_one, map_pow, map_pow, norm_pow]
  · intro a b
    have h := he₀ (e₀.symm a) (e₀.symm b)
    simp only [AddEquiv.apply_symm_apply, Nat.cast_one, one_mul] at h
    exact h.symm

end GlobalTheory.TraitExtLab
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section
namespace GlobalTheory.TInj

theorem tautChart_eq_of_genPt : ∀ {g n : ℕ} {φ : InvFun ℤ}, 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (C : Taut (zetaAway n) g n φ) (G₁ : Over (Sp C.R)) [GrpObj G₁] [IsCommMonObj G₁] (y : Sp (FractionRing C.R) ⟶ F.X) (α₁ : pullback G₁.hom (jK C.R) ⟶ F.univ.A.left), C.IsFam F G₁ y α₁ → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (θ₁ θ₂ : C.R →+* R'), IsCN R' → Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ (κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing C.R)), κ₁ ≫ jK C.R = jK R' ≫ spMap θ₁ → κ₂ ≫ jK C.R = jK R' ≫ spMap θ₂ → κ₁ ≫ y = κ₂ ≫ y → spMap (θ₁.comp C.iw) ≫ C.u = spMap (θ₂.comp C.iw) ≫ C.u ∧ (θ₁.comp C.iw = θ₂.comp C.iw → ∀ k, θ₁ (C.s k) = θ₂ (C.s k)) := by
  intro g n φ hn F C G₁ _ _ y α₁ hC R' _ _ _ θ₁ θ₂ hR' hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨hsa, -, -, hM, hys⟩ := hC
  have hn1 : 1 ≤ n := by omega
  have hCN : IsCN C.R := hM.isCN
  obtain ⟨R₁, _, _, _, ρ, D, e', hR₁, hρ, hρf, hρl, href⟩ := GlobalTheory.T.exists_refinement_tautologicalChart_finiteExtension hn1 C hCN
  obtain ⟨β, ββ, w, hFrom⟩ := GlobalTheory.T.comesFromBase_of_refines_polarisedData C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n C.R R₁ ρ C.iw C.s C.Q C.e D.toPre e' hρ C.data href
  obtain ⟨G₀, _, _, π, A₀, U₀, hU⟩ := hM.unif R₁ ρ hR₁ hρ hρf D e' href
  obtain ⟨hπ, κρ, πK, α₀, α₂, hκρ, -, hA, hsq, hL, -⟩ := hU
  have hsa₀ : IsSemiAbelian G₀ := GlobalTheory.Mum.EvenDesc.isSemiAbelian_of_isGrpPullback hπ hsa
  obtain ⟨V, _, _, _, _, η', f₁, f₂, hVc, hη', hf₁, hf₂, hlf₁, hlf₂, hc₁, hc₂⟩ :=
    exists_cDvr_two_embeddings C.R R₁ R' ρ hρ hρf hR' θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂
  obtain ⟨κf₁, hκf₁⟩ := exists_genericMap hf₁
  obtain ⟨κf₂, hκf₂⟩ := exists_genericMap hf₂
  obtain ⟨κη, hκη⟩ := exists_genericMap hη'
  have e₁ : κf₁ ≫ κρ = κη ≫ κ₁ := GlobalTheory.T.genericPointMap_over_ringHom_unique (f₁.comp ρ) _ _
    (by rw [Category.assoc, hκρ, ← Category.assoc, hκf₁, Category.assoc, ← spMap_comp])
    (by rw [Category.assoc, hκ₁, ← Category.assoc, hκη, Category.assoc, ← spMap_comp, hc₁])
  have e₂ : κf₂ ≫ κρ = κη ≫ κ₂ := GlobalTheory.T.genericPointMap_over_ringHom_unique (f₂.comp ρ) _ _
    (by rw [Category.assoc, hκρ, ← Category.assoc, hκf₂, Category.assoc, ← spMap_comp])
    (by rw [Category.assoc, hκ₂, ← Category.assoc, hκη, Category.assoc, ← spMap_comp, hc₂])
  have hy₀ : κf₁ ≫ (κρ ≫ y) = κf₂ ≫ (κρ ≫ y) := by
    rw [← Category.assoc, e₁, Category.assoc, hy, ← Category.assoc, ← e₂, Category.assoc]
  have hmap : ∀ f : R₁ →+* V, IsLocalHom f → (maximalIdeal R₁).map f ≤ maximalIdeal V := fun f hf =>
    Ideal.map_le_iff_le_comap.mpr fun x hx => (mem_maximalIdeal _).2 (map_nonunit f x ((mem_maximalIdeal _).1 hx))
  haveI : CharZero R₁ := hR₁.2.2.2
  obtain ⟨D₁, D₂, hD₁, hD₂, j₁, j₂, b, φ', hE₁, hE₂, hMatch, hpairs⟩ :=
    GlobalTheory.T.uniformisation_pullbacks_match_torsionPairs F.univ (GlobalTheory.LowChart.isUnit_zetaAway n hn) hn1 R₁ (maximalIdeal R₁)
      ⟨hR₁.1, inferInstance, hR₁.2.1, hR₁.2.2.1⟩ D A₀ G₀ U₀ hsa₀ (κρ ≫ y) α₀ ⟨hA, α₂, hsq, hL⟩ V hVc f₁ f₂ hf₁ hf₂
      (hmap f₁ hlf₁) (hmap f₂ hlf₂) κf₁ κf₂ hκf₁ hκf₂ hy₀
  obtain ⟨ββ₁, w₁, hFrom₁⟩ := GlobalTheory.T.comesFromBase_of_pullback_injective_domains C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n R₁ V
    (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₁ D₁.toPre hD₁ hf₁ hFrom
  obtain ⟨ββ₂, w₂, hFrom₂⟩ := GlobalTheory.T.comesFromBase_of_pullback_injective_domains C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n R₁ V
    (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₂ D₂.toPre hD₂ hf₂ hFrom
  have hne₀ : ∀ k, ρ (C.s k) ≠ 0 := fun k => (map_ne_zero_iff ρ hρ).2 (C.s_ne_zero k)
  have htaut : ∀ a : Fin C.T.r → ℤ, ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) n)
      (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) n),
      p₁.y = (hD₁.xe.trans (e'.trans C.e)).symm a ∧
      TautPt C.T (f₁.comp (ρ.comp C.iw)) (fun k => f₁ (ρ (C.s k))) (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n
        D₁.toPre (hD₁.xe.trans (e'.trans C.e)) ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
        (AlgebraicClosure (FractionRing V)) a p₁.g ∧
      p₂.y = (hD₂.xe.trans (e'.trans C.e)).symm a ∧
      TautPt C.T (f₂.comp (ρ.comp C.iw)) (fun k => f₂ (ρ (C.s k))) (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n
        D₂.toPre (hD₂.xe.trans (e'.trans C.e)) ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂
        (AlgebraicClosure (FractionRing V)) a p₂.g ∧ QImg b φ' p₁ p₂ := by
    intro a
    obtain ⟨p₀, hp₀y, hp₀⟩ := GlobalTheory.T.periodPart_mem_tautologicalPoint_torsion C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n R₁ D.toPre
      (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w D.tau_bimult hFrom hne₀
      (AlgebraicClosure (FractionRing R₁)) a
    obtain ⟨p₁, p₂, hp₁y, hTr₁, hp₂y, hTr₂, hQ⟩ := hpairs p₀
    refine ⟨p₁, p₂, ?_, ?_, ?_, ?_, hQ⟩
    · rw [hp₁y, hp₀y]; rfl
    · exact GlobalTheory.T.tautologicalPoint_transport_fieldMap C.T _ n R₁ V (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₁
        D₁.toPre hD₁ ββ₁ w₁ hf₁ D₁.tau_bimult hFrom hFrom₁ _ _ j₁ hE₁ a p₀.g p₁.g hp₀ hTr₁
    · rw [hp₂y, hp₀y]; rfl
    · exact GlobalTheory.T.tautologicalPoint_transport_fieldMap C.T _ n R₁ V (maximalIdeal R₁) D (ρ.comp C.iw) (fun k => ρ (C.s k)) (e'.trans C.e) β ββ w f₂
        D₂.toPre hD₂ ββ₂ w₂ hf₂ D₂.tau_bimult hFrom hFrom₂ _ _ j₂ hE₂ a p₀.g p₂.g hp₀ hTr₂
  have hlev := GlobalTheory.T.exists_level_point_pairs_lower_base C.toLowBase hn1 R₁ V (maximalIdeal R₁) (maximalIdeal V) D D₁ D₂ (ρ.comp C.iw) β hFrom.1
    f₁ f₂ hD₁ hD₂ (AlgebraicClosure (FractionRing R₁)) (AlgebraicClosure (FractionRing V)) j₁ j₂ b φ' hE₁ hE₂ hpairs
  have hloc : ∀ f : R₁ →+* V, IsLocalHom f → ∀ x, x ∈ maximalIdeal C.R → f (ρ x) ∈ maximalIdeal V := fun f hf x hx =>
    (mem_maximalIdeal _).2 (map_nonunit f _ (map_nonunit ρ x ((mem_maximalIdeal _).1 hx)))
  have hbd₁ : ∀ k, f₁ (ρ (C.s (.inl k))) ∈ maximalIdeal V ∧ f₁ (ρ (C.s (.inl k))) ≠ 0 := fun k =>
    ⟨hloc f₁ hlf₁ _ (C.bd k), (map_ne_zero_iff f₁ hf₁).2 (hne₀ _)⟩
  have hbd₂ : ∀ k, f₂ (ρ (C.s (.inl k))) ∈ maximalIdeal V ∧ f₂ (ρ (C.s (.inl k))) ≠ 0 := fun k =>
    ⟨hloc f₂ hlf₂ _ (C.bd k), (map_ne_zero_iff f₂ hf₂).2 (hne₀ _)⟩
  have hu₁ : ∀ k, IsUnit (f₁ (ρ (C.s (.inr k)))) := fun k => ((C.tor k).map ρ).map f₁
  have hu₂ : ∀ k, IsUnit (f₂ (ρ (C.s (.inr k)))) := fun k => ((C.tor k).map ρ).map f₂
  have hfin1 := GlobalTheory.T.tautological_lattice_identification_eq_id C.T φ C.m C.N n (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) hn C.cone C.defin V
    D₁.toPre D₂.toPre (f₁.comp (ρ.comp C.iw)) (fun k => f₁ (ρ (C.s k))) (hD₁.xe.trans (e'.trans C.e))
    ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
    (f₂.comp (ρ.comp C.iw)) (fun k => f₂ (ρ (C.s k))) (hD₂.xe.trans (e'.trans C.e))
    ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂ b φ' (AlgebraicClosure (FractionRing V))
    D₁.tau_bimult D₂.tau_bimult hFrom₁ hFrom₂ hbd₁ hu₁ hbd₂ hu₂ hMatch htaut
  have hb := GlobalTheory.T.structureMap_eq_of_same_genericImage_moduli F.s y C.b hys θ₁ θ₂ κ₁ κ₂ hκ₁ hκ₂ hy
  have k₁ : f₁.comp (ρ.comp C.iw) = η'.comp (θ₁.comp C.iw) := by
    rw [← RingHom.comp_assoc, hc₁, RingHom.comp_assoc]
  have k₂ : f₂.comp (ρ.comp C.iw) = η'.comp (θ₂.comp C.iw) := by
    rw [← RingHom.comp_assoc, hc₂, RingHom.comp_assoc]
  have hbase : (f₁.comp (ρ.comp C.iw)).comp C.toLowBase.T.b = (f₂.comp (ρ.comp C.iw)).comp C.toLowBase.T.b := by
    rw [k₁, k₂]
    change η'.comp (θ₁.comp C.b) = η'.comp (θ₂.comp C.b)
    rw [hb]
  obtain ⟨hU', hβeq⟩ := GlobalTheory.T.siegelFibrePower_point_eq_of_matching_lower_data C.toLowBase hn (GlobalTheory.LowChart.isUnit_zetaAway n hn) (isUnit_natCast (by omega))
    (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) V
    D₁.toPre D₂.toPre (f₁.comp (ρ.comp C.iw)) (fun k => f₁ (ρ (C.s k))) (hD₁.xe.trans (e'.trans C.e))
    ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
    (f₂.comp (ρ.comp C.iw)) (fun k => f₂ (ρ (C.s k))) (hD₂.xe.trans (e'.trans C.e))
    ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂ b φ' (AlgebraicClosure (FractionRing V))
    D₁.tau_bimult D₂.tau_bimult hFrom₁ hFrom₂ hbase hMatch hfin1 htaut hlev
  refine ⟨GlobalTheory.T.specMap_comp_eq_of_comp_injective_localScheme C.u (θ₁.comp C.iw) (θ₂.comp C.iw) η' hη' (by rw [← k₁, ← k₂]; exact hU'), fun heq k => ?_⟩
  have hω : f₁.comp (ρ.comp C.iw) = f₂.comp (ρ.comp C.iw) := by rw [k₁, k₂, heq]
  have hβ₂ := hβeq hω
  rw [← hω] at hFrom₂ htaut
  have hs := GlobalTheory.T.tautological_coords_eq_of_matching_data C.T (fun k => (C.ε k : LinearMap.BilinForm ℤ (Fin C.T.r → ℤ))) n V (f₁.comp (ρ.comp C.iw))
    D₁.toPre D₂.toPre (fun k => f₁ (ρ (C.s k))) (hD₁.xe.trans (e'.trans C.e))
    ((hD₁.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₁)) ≫ β) ββ₁ w₁
    (fun k => f₂ (ρ (C.s k))) (hD₂.xe.trans (e'.trans C.e))
    ((hD₂.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf f₂)) ≫ β) ββ₂ w₂ b φ' (AlgebraicClosure (FractionRing V))
    hn1 ⟨C.ε, fun _ => rfl⟩ D₁.tau_bimult D₂.tau_bimult hFrom₁ hFrom₂ (fun k => (map_ne_zero_iff f₁ hf₁).2 (hne₀ k))
    (fun k => (map_ne_zero_iff f₂ hf₂).2 (hne₀ k)) hMatch hfin1 hβ₂ htaut
  have h1 := congrFun hs k
  have h2 := DFunLike.congr_fun hc₁ (C.s k)
  have h3 := DFunLike.congr_fun hc₂ (C.s k)
  simp only [RingHom.comp_apply] at h1 h2 h3
  exact hη' (by rw [← h2, ← h3]; exact h1)

end GlobalTheory.TInj
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem exists_ringHom_val_of_regAt : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} (X₂ : Setup F W i) (z : X₂.M.Z) {V : Type} [CommRing V] [IsDomain V] (ev : X₂.M.Z.presheaf.stalk z →+* V), RegAt X₂ z ev → ∃ yK : X₂.S.R →+* FractionRing V, ∀ a : X₂.S.R, yK a = X₂.M.val (jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) a := by
  intro g n F W Z i X₂ z V _ _ ev hr
  have hR : X₂.S.R ≤ X₂.M.O ((jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) (IsLocalRing.closedPoint (FractionRing V))) :=
    fun a ha => hr a ha
  exact ⟨(RatModel.valHomOf (jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) _
    (RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (M := X₂.M) (jK V ≫ spMap ev ≫ X₂.M.Z.fromSpecStalk z) (IsLocalRing.closedPoint (FractionRing V))))).comp
      (Subalgebra.inclusion hR).toRingHom, fun a => rfl⟩

theorem Tower.comp_act₂_of_comp_act : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {K : Type} [Field K] (A' : Over (Sp K)) (y₂ : 𝔗.X₂.S.R →+* K) (φ₂ : A'.left ⟶ 𝔗.X₂.ρ.P.A.left), φ₂ ≫ 𝔗.X₂.ρ.P.A.hom = A'.hom ≫ spMap y₂ → ∀ (e : A' ⟶ A') (a : Matrix (Fin 8) (Fin 8) ℤ), e.left ≫ φ₂ ≫ 𝔗.φ = φ₂ ≫ 𝔗.φ ≫ (act a).left → e.left ≫ φ₂ = φ₂ ≫ (𝔗.act₂ a).left := by
  intro g n F W Z i X₁ act 𝔗 K _ A' y₂ φ₂ hφ e a h
  refine 𝔗.cart.1.hom_ext ?_ ?_
  · simp only [Category.assoc, 𝔗.act_eq a]
    simpa only [Category.assoc] using h
  · simp only [Category.assoc, Over.w (𝔗.act₂ a), hφ]
    rw [← Category.assoc, Over.w e]

theorem Tower.pt_iff_pt_gl : ∀ {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z} {X₁ : Setup F W i} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)} (𝔗 : Tower X₁ act) {K : Type} [Field K] (A' : Over (Sp K)) [GrpObj A'] (ya yb : 𝔗.X₂.S.R →+* K) (φa φb : A'.left ⟶ 𝔗.X₂.ρ.P.A.left) (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), IsGrpPullback A' 𝔗.X₂.ρ.P.A (spMap ya) φa → IsGrpPullback A' 𝔗.X₂.ρ.P.A (spMap yb) φb → φa ≫ 𝔗.φ = φb ≫ 𝔗.φ → ya = yb.comp (𝔗.sR σ) → ∀ {L : Type} [Field L] (j : K →+* L) (x : Sp L ⟶ A'.left), x ≫ A'.hom = spMap j → ∀ a, (x ≫ φa = spMap (j.comp ya) ≫ (𝔗.X₂.ρ.pt a).left ↔ x ≫ φb = spMap (j.comp yb) ≫ (𝔗.X₂.ρ.pt (𝔗.gl σ a)).left) := by
  intro g n F W Z i X₁ act 𝔗 K _ A' _ ya yb φa φb σ ha hb hab hy L _ j x hx a
  have hc := 𝔗.cart.1
  have hsec : ∀ b, (𝔗.X₂.ρ.pt b).left ≫ 𝔗.X₂.ρ.P.A.hom = 𝟙 _ := fun b => Over.w (𝔗.X₂.ρ.pt b)
  have hsp : ∀ y : 𝔗.X₂.S.R →+* K, spMap j ≫ spMap y = spMap (j.comp y) := fun y => by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hxa : (x ≫ φa) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp ya) := by
    rw [Category.assoc, ha.1.w, ← Category.assoc, hx, hsp]
  have hxb : (x ≫ φb) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp yb) := by
    rw [Category.assoc, hb.1.w, ← Category.assoc, hx, hsp]
  have hra : (spMap (j.comp ya) ≫ (𝔗.X₂.ρ.pt a).left) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp ya) := by
    rw [Category.assoc, hsec]
    exact Category.comp_id _
  have hrb : (spMap (j.comp yb) ≫ (𝔗.X₂.ρ.pt (𝔗.gl σ a)).left) ≫ 𝔗.X₂.ρ.P.A.hom = spMap (j.comp yb) := by
    rw [Category.assoc, hsec]
    exact Category.comp_id _
  have hg : spMap (j.comp yb) ≫ (𝔗.X₂.ρ.pt (𝔗.gl σ a)).left ≫ 𝔗.φ = spMap (j.comp ya) ≫ (𝔗.X₂.ρ.pt a).left ≫ 𝔗.φ := by
    rw [𝔗.gl_pt, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc, ← hy]
  constructor
  · intro h1
    refine hc.hom_ext ?_ (hxb.trans hrb.symm)
    rw [Category.assoc, ← hab, ← Category.assoc, h1, Category.assoc, Category.assoc, hg]
  · intro h1
    refine hc.hom_ext ?_ (hxa.trans hra.symm)
    rw [Category.assoc, hab, ← Category.assoc, h1, Category.assoc, Category.assoc, hg]

end GlobalTheory.Poinc.Sep

namespace GlobalTheory

theorem exists_baseChange_member_of_tower : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (𝔗 : Tower X₁ act) (z₂ : 𝔗.X₂.M.Z), 𝔗.p z₂ = z₁ → ∀ x₀ : X₁.S.Gam, X₁.M.Div X₁.S.th x₀ z₁ → ∃ eps : X₁.S.Gam → ℕ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V), 𝔪.Terms x₀ lab T → ∀ (V' : Type) [CommRing V'] [IsDomain V'] [IsLocalRing V'] (io : V →+* V'), IsCN V' → Function.Injective io → io.Finite → ∃ 𝔪₂ : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ → UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ, (∀ ev₂ h (zt : 𝔗.X₂.M.Z.presheaf.stalk z₂), 𝔗.X₂.M.stalkHom z₂ zt = algebraMap 𝔗.X₂.o₁ 𝔗.X₂.Ω₁ 𝔗.X₂.S.ζ → (𝔪₂ ev₂ h).Terms (𝔗.lam x₀) (fun c => 𝔗.lam (lab c)) (fun mu c => ev₂ zt ^ eps (lab c) * io (T mu c))) ∧ ∀ ev₂ h ev₂' h' (σ : 𝔗.X₂.Ω₁ ≃ₐ[X₁.Ω₁] 𝔗.X₂.Ω₁), (∀ x x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x) → ev₂' x = ev₂ x') → (∀ x, ∃ x', 𝔗.X₂.M.stalkHom z₂ x' = σ (𝔗.X₂.M.stalkHom z₂ x)) → ∀ a mu, (𝔪₂ ev₂' h').YY a mu ↔ (𝔪₂ ev₂ h).YY (𝔗.gl σ a) mu := by
  intro g hg n hn hodd F Z z i _ hproj hnorm hiz hdense W hE8 hth X₁ z₁ act hact 𝔗 z₂ hz₂ x₀ hdiv
  obtain ⟨eps, heps⟩ := GlobalTheory.T.thetaSetupTower_member_terms_baseChange X₁ act 𝔗 z₁ z₂ hz₂ x₀ hdiv
  refine ⟨eps, ?_⟩
  intro V _ _ _ ev X _ m t δ 𝔪 C lab T hT V' _ _ _ io hcn hinj hfin
  have hle : nonZeroDivisors V ≤ (nonZeroDivisors V').comap io :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective io hinj
  let f : FractionRing V →+* FractionRing V' := IsLocalization.map (FractionRing V') io hle
  have hf : ∀ v, f (algebraMap V (FractionRing V) v) = algebraMap V' (FractionRing V') (io v) :=
    fun v => IsLocalization.map_eq hle v
  obtain ⟨D', e₈', G', _, _, A', U', ψ, hD, bc, hsemi, hψ, hw, hbc, hPU, hxe, hgen, hE, hpsi⟩ :=
    GlobalTheory.T.exists_baseChange_finite_injective_complete_normal X₁ z₁ act V ev X m t δ 𝔪 V' io f hf hcn hinj hfin
  have hreg : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ → RegAt 𝔗.X₂ z₂ ev₂ :=
    fun ev₂ h => GlobalTheory.T.deeperThetaRing_regular_at_extension_point 𝔗 hz₂ ev io ev₂ hinj h 𝔪.reg
  choose yK hyK using fun (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (h : 𝔗.Ext ev io ev₂) =>
    exists_ringHom_val_of_regAt 𝔗.X₂ z₂ ev₂ (hreg ev₂ h)
  have hyKc : ∀ ev₂ h, (yK ev₂ h).comp 𝔗.om = f.comp 𝔪.yK := by
    intro ev₂ h
    ext a
    simp only [RingHom.comp_apply]
    rw [hyK, 𝔪.yK_eq]
    exact GlobalTheory.T.deeperTheta_value_image_eq_image_value 𝔗 hz₂ ev io ev₂ f hf hinj h 𝔪.reg a
  have hsq : ∀ ev₂ h, spMap (yK ev₂ h) ≫ spMap 𝔗.om = spMap f ≫ spMap 𝔪.yK := by
    intro ev₂ h
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hyKc ev₂ h]
  choose φ₂ hφ₂ using fun (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (h : 𝔗.Ext ev io ev₂) =>
    GlobalTheory.T.isGrpPullback_paste_factorisation X₁.ρ.P.A 𝔗.X₂.ρ.P.A 𝔪.A.A A'.A (spMap 𝔗.om) (spMap 𝔪.yK) (spMap f) (spMap (yK ev₂ h)) 𝔗.φ 𝔪.φ ψ
      𝔗.cart 𝔪.cart hψ (hsq ev₂ h)
  choose wl hwl using fun (ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V') (h : 𝔗.Ext ev io ev₂) =>
    GlobalTheory.T.exists_lineBundleIso_pullback_commSquare A'.L 𝔪.A.L X₁.ρ.P.L 𝔗.X₂.ρ.P.L ψ 𝔪.φ (φ₂ ev₂ h) 𝔗.φ A'.isLB 𝔪.A.isLB X₁.ρ.P.isLB 𝔗.X₂.ρ.P.isLB
      (hφ₂ ev₂ h).2.symm hw ⟨𝔪.wl, 𝔪.wl_gen⟩ 𝔗.lb
  let 𝔪₂ : ∀ ev₂ : 𝔗.X₂.M.Z.presheaf.stalk z₂ →+* V', 𝔗.Ext ev io ev₂ →
      UMem 𝔗.X₂ z₂ 𝔗.act₂ V' ev₂ X (fun k => io (t k)) δ := fun ev₂ h =>
    { cn := hcn
      loc := h.1
      reg := hreg ev₂ h
      yK := yK ev₂ h
      yK_eq := hyK ev₂ h
      D := D'
      e₈ := e₈'
      G := G'
      semi := hsemi
      A := A'
      U := U'
      φ := φ₂ ev₂ h
      cart := (hφ₂ ev₂ h).1
      wl := wl ev₂ h
      wl_gen := hwl ev₂ h
      equiv := fun a a' hc => by
        obtain ⟨E, hE1, hE2⟩ := 𝔪.equiv a a' hc
        obtain ⟨E', hE'1, hE'2⟩ := hE E
        refine ⟨E', ?_, fun mu => hD.xe.injective ?_⟩
        · have e2 := (hφ₂ ev₂ h).2
          refine Tower.comp_act₂_of_comp_act 𝔗 A'.A (yK ev₂ h) (φ₂ ev₂ h) (hφ₂ ev₂ h).1.1.w E'.aA a ?_
          calc E'.aA.left ≫ φ₂ ev₂ h ≫ 𝔗.φ = E'.aA.left ≫ ψ ≫ 𝔪.φ := by rw [e2]
            _ = ψ ≫ E.aA.left ≫ 𝔪.φ := by rw [← Category.assoc, hE'1, Category.assoc]
            _ = ψ ≫ 𝔪.φ ≫ (act a).left := by rw [hE1]
            _ = φ₂ ev₂ h ≫ 𝔗.φ ≫ (act a).left := by rw [← Category.assoc, ← e2, Category.assoc]
        · rw [hE'2, hxe, hE2, hxe]
      psi := hpsi }
  refine ⟨𝔪₂, ?_, ?_⟩
  · intro ev₂ h zt hzt
    exact heps V ev X m t δ 𝔪 C lab T hT V' io f hf hinj hfin ev₂ (𝔪₂ ev₂ h) ψ hD bc h (hyKc ev₂ h) hψ hw
      (hφ₂ ev₂ h).2 hbc hPU hxe hgen zt hzt
  · intro ev₂ h ev₂' h' σ h1 h2 a mu
    have hy : yK ev₂' h' = (yK ev₂ h).comp (𝔗.sR σ) := by
      ext b
      simp only [RingHom.comp_apply]
      rw [hyK, hyK]
      exact GlobalTheory.T.deeperTheta_value_galoisConjugate_extension 𝔗 ev₂ ev₂' σ h1 h2 (hreg ev₂ h) (hreg ev₂' h') b
    unfold UMem.YY
    refine exists_congr fun p => exists_congr fun x => and_congr_right fun _ => and_congr_right fun _ => ?_
    exact Tower.pt_iff_pt_gl 𝔗 A'.A (yK ev₂' h') (yK ev₂ h) (φ₂ ev₂' h') (φ₂ ev₂ h) σ (hφ₂ ev₂' h').1 (hφ₂ ev₂ h).1
      ((hφ₂ ev₂' h').2.trans (hφ₂ ev₂ h).2.symm) hy
      (algebraMap (FractionRing V') (AlgebraicClosure (FractionRing V'))) x.left (Over.w x) a

end GlobalTheory
end
end
