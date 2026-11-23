module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle065
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle081
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle127
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2887
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelObjIsoHomSubtype
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2899
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.SqrtNegDiscMemCoeffField
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle649
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle048
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle200
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
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
import Mathlib.RingTheory.RootsOfUnity.Lemmas
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsNumberFieldQkPointsComplexDegeneration
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

theorem GlobalTheory.Poinc.Sep.Spz.torAt_of_spread₂ : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], GlobalTheory.Mum.Base V₁ → ∀ (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left), IsGrpPullback G₁ H ξ₁ β₁ → ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂], GlobalTheory.Mum.Base V₂ → ∀ (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₂ → ∀ (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left), IsGrpPullback G₂ H ξ₂ β₂ → ∀ ρ : D₂.toPre.X →+ D₁.toPre.X, Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → ∀ (o : Type) [CommRing o] (s : B ⟶ Sp o) (o₁ : o →+* V₁) (o₂ : o →+* V₂), ξ₁ ≫ s = spMap o₁ → ξ₂ ≫ s = spMap o₂ → ∀ (k : ℕ) (ζ : o), 1 ≤ k → IsUnit (k : o) → ζ ^ k = 1 → ∀ (Wo : B.Opens) (h : Wo.toScheme ⟶ H.left) (ξ₁' : Sp V₁ ⟶ Wo.toScheme) (ξ₂' : Sp V₂ ⟶ Wo.toScheme), h ≫ H.hom = Wo.ι → ξ₁' ≫ Wo.ι = ξ₁ → ξ₂' ≫ Wo.ι = ξ₂ → ∀ (F₁ : Type) [Field F₁] [IsAlgClosed F₁] [Algebra (FractionRing V₁) F₁] (F₂ : Type) [Field F₂] [IsAlgClosed F₂] [Algebra (FractionRing V₂) F₂] (c : D₁.toPre.X →+ ℤ) (x₁ : TFK (R := V₁) F₁ ⟶ A₁.A) (x₂ : TFK (R := V₂) F₂ ⟶ A₂.A), TorAt U₁ F₁ k (algebraMap (FractionRing V₁) F₁ (algebraMap V₁ (FractionRing V₁) (o₁ ζ))) c x₁ → x₁.left ≫ genMap U₁ ≫ β₁ = spMap (algebraMap (FractionRing V₁) F₁) ≫ jK V₁ ≫ ξ₁' ≫ h → x₂ ^ k = 1 → x₂.left ≫ genMap U₂ ≫ β₂ = spMap (algebraMap (FractionRing V₂) F₂) ≫ jK V₂ ≫ ξ₂' ≫ h → TorAt U₂ F₂ k (algebraMap (FractionRing V₂) F₂ (algebraMap V₂ (FractionRing V₂) (o₂ ζ))) (c.comp ρ) x₂ := by
  intro B H _ _ hH V₁ _ _ _ hV₁ G₁ _ _ hG₁ D₁ A₁ U₁ ξ₁ β₁ hβ₁ V₂ _ _ _ hV₂ G₂ _ _ hG₂ D₂ A₂ U₂ ξ₂ β₂ hβ₂ ρ hS o _ s o₁ o₂ hs₁ hs₂ k ζ hk hku hζ Wo h ξ₁' ξ₂' hh h₁ h₂ F₁ _ _ _ F₂ _ _ _ c x₁ x₂ hx₁ hx₁g hx₂ hx₂g
  have hw₁ : o₁ ζ ^ k = 1 := by rw [← map_pow, hζ, map_one]
  have hw₂ : o₂ ζ ^ k = 1 := by rw [← map_pow, hζ, map_one]
  have hA := GlobalTheory.T.toricTorsionSection_eq_torusPoint_at_closedPointField B H V₁ hV₁ G₁ hG₁ D₁ A₁ U₁ ξ₁ β₁ hβ₁ (ξ₁' ≫ h) (by rw [Category.assoc, hh, h₁]) k (o₁ ζ) hk hw₁
    F₁ c x₁ hx₁ hx₁g
  obtain ⟨κ, _, b, hb, Gκ, _, m, hm, τ, z, hτ, hz, he⟩ := GlobalTheory.T.torusPointSection_along_spreadingTrait B H hH V₁ G₁ D₁ A₁ U₁ ξ₁ β₁ V₂ G₂ D₂ A₂ U₂ ξ₂ β₂ ρ
    hS o s o₁ o₂ hs₁ hs₂ k ζ hk hζ Wo h ξ₁' ξ₂' hh h₁ h₂ c hA
  exact GlobalTheory.T.toricTorsionPoint_of_torusPoint_at_closedPointField B H V₂ hV₂ G₂ hG₂ D₂ A₂ U₂ ξ₂ β₂ hβ₂ (ξ₂' ≫ h) (by rw [Category.assoc, hh, h₂]) k (o₂ ζ) hk
    (by simpa using hku.map o₂) hw₂ F₂ (c.comp ρ) x₂ hx₂ hx₂g κ b hb Gκ m hm τ hτ z hz he
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

noncomputable section
namespace GlobalTheory.Poinc.Sep.Spz
open GlobalTheory.TorusExt GlobalTheory.ZH.TorusPerp GlobalTheory.QkNumberField GlobalTheory.TorsionExt

theorem isPrimitiveRoot_map_of_isUnit_order {o K : Type} [CommRing o] [IsDomain o] [CommRing K] [IsDomain K] (φ : o →+* K)
    {m : ℕ} (hm : 0 < m) {q : o} (hq : IsPrimitiveRoot q m) (hu : IsUnit (m : o)) : IsPrimitiveRoot (φ q) m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine IsPrimitiveRoot.mk_of_lt _ hm (by rw [← map_pow, hq.pow_eq_one, map_one]) fun l hl hlt h1 => ?_
  have hp := congrArg φ hq.prod_one_sub_pow_eq_order
  rw [map_prod] at hp
  have hz : ∏ k ∈ Finset.range n, φ (1 - q ^ (k + 1)) = 0 := by
    refine Finset.prod_eq_zero (i := l - 1) (Finset.mem_range.2 (by omega)) ?_
    rw [map_sub, map_one, map_pow, Nat.sub_add_cancel hl, h1, sub_self]
  rw [hz] at hp
  have hu' : IsUnit (φ ((n : o) + 1)) := by
    have := hu.map φ; simpa using this
  exact hu'.ne_zero hp.symm

theorem intCast_eq_of_zpow_eq {K : Type} [Field K] {m : ℕ} [NeZero m] {z : K} (hz : IsPrimitiveRoot z m) {a : ℤ}
    {b : ZMod m} (h : z ^ a = z ^ (b.val : ℤ)) : (a : ZMod m) = b := by
  have hz0 : z ≠ 0 := hz.ne_zero (NeZero.ne m)
  have h1 : z ^ (a - (b.val : ℤ)) = 1 := by rw [zpow_sub₀ hz0, h, div_self (zpow_ne_zero _ hz0)]
  have h2 := (hz.zpow_eq_one_iff_dvd _).1 h1
  have h3 : ((a - (b.val : ℤ) : ℤ) : ZMod m) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h2
  rw [Int.cast_sub, sub_eq_zero, Int.cast_natCast, ZMod.natCast_zmod_val] at h3
  exact h3

theorem torAt_char_eq_weil : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ sg : ℤˣ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (c : 𝔪.D.toPre.X →+ ℤ) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), TorAt 𝔪.U (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))))) c x → x.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt τ).left → ∀ a mu, 𝔪.YY a mu → ((c (𝔪.e₈ mu) : ℤ) : ZMod (X₁.S.r * X₁.S.N)) = ((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a := by
  intro g n F W Z i X₁ z₁ act
  refine ⟨1, ?_⟩
  intro V _ _ _ ev X _ m t δ 𝔪 τ c x hT hxo a mu hY
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hL : LL := GlobalTheory.firstFiveLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hk : 1 ≤ X₁.S.r * X₁.S.N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega))
  obtain ⟨τ', q, hτv, hqy, hqt, hqx⟩ := hT
  obtain ⟨p', x', hp'y, hp'x, hx'o⟩ := hY
  have W₁ := weilQkIs_tor hG q p' hqy hqt
  have W₂ := (GlobalTheory.UT.weilQkIs_iff_weilIs hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk q p' x x' hqx hp'x (τ' (Multiplicative.ofAdd p'.y))).1 W₁
  have := X₁.ρ.P.isAb.comm
  have hy : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) := (spMap_comp _ _).symm
  let h : Over.mk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) (by simp)
  have hh : h.left = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) := hy
  have hζ : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) :=
    X₁.S.prim.pow (pow_pos hk 2) (pow_two _)
  let c₀ : (X₁.S.R)ˣ := Units.map (algebraMap X₁.o₁ X₁.S.R).toMonoidHom (hζ.isUnit (by omega)).unit
  have w := GlobalTheory.CommPairing.weilIs_pull hG X₁.ρ.P.isAb X₁.ρ.P.isLB h
    (X₁.ρ.weil τ a (c₀ ^ (eStd X₁.S.g _ τ a).val) (by rw [pow_mul, map_pow]; rfl))
  have W₃ := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ X₁.ρ.P.isLB 𝔪.A.isLB 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩
    (TFK (R := V) (AlgebraicClosure (FractionRing V))) _
    x x' (h ≫ X₁.ρ.pt τ) (h ≫ X₁.ρ.pt a) _ ?_ ?_).2 w
  · rw [hh, map_unitOn] at W₃
    have e := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG 𝔪.A.isAb 𝔪.A.isLB W₂ W₃)
    rw [hp'y] at e
    have e' := congrArg Units.val e
    simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingHom.coe_comp, Function.comp_apply, Units.val_pow_eq_pow_val, c₀, IsUnit.unit_spec] at e'
    rw [hτv] at e'
    rw [Units.val_one, one_smul]
    haveI : IsDomain X₁.o₁ := X₁.ar.ded.toIsDomain
    haveI : NeZero (X₁.S.r * X₁.S.N) := ⟨by omega⟩
    have hzp := isPrimitiveRoot_map_of_isUnit_order ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (𝔪.yK.comp (algebraMap X₁.o₁ X₁.S.R))) (by omega) hζ X₁.S.unit
    refine intCast_eq_of_zpow_eq hzp ?_
    rw [zpow_natCast]
    simp only [RingHom.coe_comp, Function.comp_apply, map_pow] at e' ⊢
    exact e'
  · show h.left ≫ (X₁.ρ.pt τ).left = _
    rw [hh, hxo]
  · show h.left ≫ (X₁.ρ.pt a).left = _
    rw [hx'o, hh]

end GlobalTheory.Poinc.Sep.Spz
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum
open Scheme.AffineZariskiSite

noncomputable section

theorem exists_finite_of_isFinSub : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsIntegral S] [IsDominant gp]
    (F : ∀ V : S.Opens, Subring Γ(Sp K, gp ⁻¹ᵁ V)), IsFinSub gp F →
    ∃ (S' : Scheme.{0}) (h : S' ⟶ S) (gp' : Sp K ⟶ S') (hgp : gp' ≫ h = gp),
      IsFinite h ∧ IsIntegral S' ∧ IsDominant gp' ∧
      ∀ V : S.Opens, IsAffineOpen V → ∀ x ∈ F V, ∃ c : Γ(S', h ⁻¹ᵁ V),
        (gp'.appLE (h ⁻¹ᵁ V) (gp ⁻¹ᵁ V) (le_preimage_of_comp_eq gp gp' h hgp V)).hom c = x := by
  first
  | exact @_root_.GlobalTheory.RelativeSpectrum.exists_finite_cover
  | exact _root_.GlobalTheory.RelativeSpectrum.exists_finite_cover
  | (apply _root_.GlobalTheory.RelativeSpectrum.exists_finite_cover <;> assumption)
  | (intros; apply _root_.GlobalTheory.RelativeSpectrum.exists_finite_cover <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RelativeSpectrum.exists_finite_cover <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RelativeSpectrum.exists_finite_cover ..)

end

end GlobalTheory.Mum
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum
theorem secLift_app_res {X Y : Scheme.{0}} (a : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)) :
    (a.app V).hom ((X.presheaf.map (homOfLE h).op).hom x) =
      (Y.presheaf.map (homOfLE (extLI_preimage_mono a h)).op).hom ((a.app U).hom x) := by
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.naturality]
  rfl

theorem secLift_comp_app {X Y Z : Scheme.{0}} (a : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) (x : Γ(X, U)) :
    ((a ≫ f).app U).hom x = (a.app (f ⁻¹ᵁ U)).hom ((f.app U).hom x) := by
  simp [Scheme.Hom.comp_app]
  rfl

theorem secLift_g {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (k : ℕ) (i j : Fin 1 → L.ι) :
    ((LB.LinComb L (K := Fin 1) (fun _ => φ) (fun _ => (k : ℤ))).g i j).val =
      ((Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i 0))
        (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) j 0)) :
        LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) j ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (j 0)))).op).hom
        ((φ.app (L.U (i 0) ⊓ L.U (j 0))).hom (L.g (i 0) (j 0)))) ^ k := by
  simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
  rfl
theorem secLift_rr {Y : Scheme.{0}} {U V W : Y.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(Y, U)) :
    (Y.presheaf.map (homOfLE h2).op).hom ((Y.presheaf.map (homOfLE h1).op).hom x) =
      (Y.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl
theorem secLift_res_comp {X Y Z : Scheme.{0}} (a : Z ⟶ Y) (f : Y ⟶ X) (U : X.Opens) {V : Z.Opens}
    (h : V ≤ (a ≫ f) ⁻¹ᵁ U) (h' : V ≤ a ⁻¹ᵁ (f ⁻¹ᵁ U)) (x : Γ(X, U)) :
    (Z.presheaf.map (homOfLE h).op).hom (((a ≫ f).app U).hom x) =
      (Z.presheaf.map (homOfLE h').op).hom ((a.app (f ⁻¹ᵁ U)).hom ((f.app U).hom x)) := by
  rw [secLift_comp_app]
  rfl
end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem secLift_compat {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (k : ℕ) (s : SecK L φ k) (i i' : Fin 1 → L.ι) :
    (Y.presheaf.map (homOfLE (inf_le_left : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i)).op).hom (s.f i) =
      ((Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i 0))
        (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i' 0)) :
        LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i' 0)))).op).hom
        ((φ.app (L.U (i 0) ⊓ L.U (i' 0))).hom (L.g (i 0) (i' 0)))) ^ k *
      (Y.presheaf.map (homOfLE (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i')).op).hom (s.f i') := by
  have h := s.compat i i'
  rw [secLift_g] at h
  exact h

def secLift_ofCompat {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (k : ℕ) (σf : ∀ i : Fin 1 → L.ι, Γ(Y, LB.wchart L (K := Fin 1) (fun _ => φ) i))
    (h : ∀ i i' : Fin 1 → L.ι, (Y.presheaf.map (homOfLE (inf_le_left : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i)).op).hom (σf i) =
      ((Y.presheaf.map (homOfLE (le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i 0))
        (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => φ) i' 0)) :
        LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ φ ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i' 0)))).op).hom
        ((φ.app (L.U (i 0) ⊓ L.U (i' 0))).hom (L.g (i 0) (i' 0)))) ^ k *
      (Y.presheaf.map (homOfLE (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => φ) i ⊓ LB.wchart L (K := Fin 1) (fun _ => φ) i' ≤ LB.wchart L (K := Fin 1) (fun _ => φ) i')).op).hom (σf i')) :
    SecK L φ k where
  f := σf
  compat i i' := (h i i').trans (congrArg (· * _) (secLift_g L φ k i i').symm)


theorem secK_lift_of_local_lift : ∀ {X X' Y : Scheme.{0}} (L : LB X) (f : X' ⟶ X) (a : Y ⟶ X') (α : Y ⟶ X) (e : a ≫ f = α) (k : ℕ), (∀ U : X'.Opens, Function.Injective (a.app U).hom) → ∀ (s : SecK L α k) (n : ℕ) (j : Fin n → L.ι) (W : Fin n → X'.Opens), (⨆ b, W b = ⊤) → ∀ (hW : ∀ b, W b ≤ f ⁻¹ᵁ L.U (j b)), (∀ b, ∃ y : Γ(X', W b), (a.app (W b)).hom y = (Y.presheaf.map (homOfLE (extLI_le_chart L f a α e (W b) (j b) (hW b))).op).hom (s.f (fun _ => j b))) → ∃ σ : SecK L f k, ∀ j' : Fin 1 → L.ι, (a.app (LB.wchart L (K := Fin 1) (fun _ => f) j')).hom (σ.f j') = (Y.presheaf.map (homOfLE (extLI_le_wchart L f a α e j')).op).hom (s.f j') := by
  intro X X' Y L f a α e k hinj s n j W hWtop hW hloc
  subst e
  have step1 : ∀ j' : Fin 1 → L.ι, ∃ y : Γ(X', LB.wchart L (K := Fin 1) (fun _ => f) j'),
      (a.app _).hom y = (Y.presheaf.map (homOfLE (extLI_le_wchart L f a (a ≫ f) rfl j')).op).hom (s.f j') := by
    intro j'
    refine GlobalTheory.T.exists_preimage_of_local_preimages_injective a hinj _ W (by rw [hWtop]; exact le_top) _ ?_
    intro b
    obtain ⟨y, hy⟩ := hloc b
    have h1 : LB.wchart L (K := Fin 1) (fun _ => f) j' ⊓ W b ≤ f ⁻¹ᵁ (L.U (j' 0) ⊓ L.U (j b)) :=
      fun x hx => ⟨LB.wchart_le L (K := Fin 1) (fun _ => f) j' 0 hx.1, hW b hx.2⟩
    refine ⟨(X'.presheaf.map (homOfLE h1).op).hom ((f.app _).hom (L.g (j' 0) (j b))) ^ k *
      (X'.presheaf.map (homOfLE (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => f) j' ⊓ W b ≤ W b)).op).hom y, ?_⟩
    have hc2 := congrArg (Y.presheaf.map (homOfLE (show a ⁻¹ᵁ (LB.wchart L (K := Fin 1) (fun _ => f) j' ⊓ W b) ≤
      LB.wchart L (K := Fin 1) (fun _ => a ≫ f) j' ⊓ LB.wchart L (K := Fin 1) (fun _ => a ≫ f) (fun _ => j b) from
      fun x hx => ⟨extLI_le_wchart L f a (a ≫ f) rfl j' hx.1, extLI_le_chart L f a (a ≫ f) rfl (W b) (j b) (hW b) hx.2⟩)).op).hom
      (secLift_compat L (a ≫ f) k s j' (fun _ => j b))
    rw [map_mul, map_pow] at hc2
    erw [secLift_rr, secLift_rr, secLift_rr] at hc2
    rw [map_mul, map_pow, secLift_app_res, secLift_app_res, hy]
    erw [secLift_rr, secLift_rr]
    rw [hc2]
    exact congrArg (fun t => t ^ k * _) (secLift_res_comp a f _ _ _ _).symm
  choose σf hσ using step1
  refine ⟨secLift_ofCompat L f k σf fun i i' => ?_, hσ⟩
  apply hinj (LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i')
  have hG : LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i' ≤ f ⁻¹ᵁ (L.U (i 0) ⊓ L.U (i' 0)) :=
    le_inf (inf_le_left.trans (LB.wchart_le L (K := Fin 1) (fun _ => f) i 0))
      (inf_le_right.trans (LB.wchart_le L (K := Fin 1) (fun _ => f) i' 0))
  have e1 := secLift_app_res a (inf_le_left : LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i' ≤ LB.wchart L (K := Fin 1) (fun _ => f) i) (σf i)
  have e2 := secLift_app_res a hG ((f.app (L.U (i 0) ⊓ L.U (i' 0))).hom (L.g (i 0) (i' 0)))
  have e3 := secLift_app_res a (inf_le_right : LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i' ≤ LB.wchart L (K := Fin 1) (fun _ => f) i') (σf i')
  rw [map_mul, map_pow, e1]
  erw [e2, e3]
  rw [hσ, hσ]
  erw [secLift_rr, secLift_rr]
  have hc := congrArg (Y.presheaf.map (homOfLE (show a ⁻¹ᵁ (LB.wchart L (K := Fin 1) (fun _ => f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => f) i') ≤
      LB.wchart L (K := Fin 1) (fun _ => a ≫ f) i ⊓ LB.wchart L (K := Fin 1) (fun _ => a ≫ f) i' from
      fun x hx => ⟨extLI_le_wchart L f a (a ≫ f) rfl i hx.1, extLI_le_wchart L f a (a ≫ f) rfl i' hx.2⟩)).op).hom
      (secLift_compat L (a ≫ f) k s i i')
  rw [map_mul, map_pow] at hc
  erw [secLift_rr, secLift_rr, secLift_rr] at hc
  rw [hc]
  exact congrArg (fun t => t ^ k * _) (secLift_res_comp a f (L.U (i 0) ⊓ L.U (i' 0)) _ _ _)
end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.galois_automorphism_acts_on_deeper_level_labels : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁), ∃ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a ∧ ∀ x, a (D.lab x) = D.lab x := by
  first | exact @GlobalTheory.Poinc.GalAct.exists_galLab | exact GlobalTheory.Poinc.GalAct.exists_galLab | (intros; apply GlobalTheory.Poinc.GalAct.exists_galLab <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_tateIso_roots {Dw : Datum H} (l : Level H) {k : Type} [Field k] {Q : Type} [Group Q]
    {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso Dw k Q act e) (z : ℕ → kˣ)
    (hz : ∀ n, 0 < n → IsPrimitiveRoot (z n) n) (hzp : ∀ n m, 0 < n → 0 < m → z (n * m) ^ m = z n)
    (hA : z l.A = I.ζ l.A) :
    ∃ I' : TateIso Dw k Q act e, (∀ n, 0 < n → I'.ζ n = z n) ∧ (∀ a, I'.ev l.A a = I.ev l.A a) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), I'.ev l.M a = I.ev l.M a := by
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with h0 | hpq
  · have hs : Subsingleton Dw.La := AllClasses.subsingleton_of_rank_zero Dw h0
    have hEF : ∀ a b : Dw.La, Dw.EF a b = 0 := fun a b => by
      rw [Subsingleton.elim a 0, map_zero, LinearMap.zero_apply]
    refine ⟨{ I with ζ := z, ζ_prim := hz, ζ_pow := hzp, isom := fun n hn a b => ?_ }, fun _ _ => rfl,
      fun _ => rfl, fun _ _ => rfl⟩
    simpa [hEF] using I.isom n hn a b
  · exact GlobalTheory.LocM.RootsPrescribe.roots E H Dw l k Q act e I z hpq hz hzp hA

theorem exists_genFib {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {t : SAB H (Sp R)} (P : PELUnif I t)
    (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK t (jK R)) {S : Scheme.{0}} (t₀ : SAB H S)
    (z : Sp (FractionRing R) ⟶ S) (m2 : SABMap tK t₀ z) : letI := H.starRing;
    ∃ ψ₁ : P.A.A.left ⟶ tK.G.left, ψ₁ ≫ m1.φ = P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) ∧
      IsGrpPullback P.A.A t₀.G z (ψ₁ ≫ m2.φ) ∧ LBIso P.A.L (t₀.PP.L.pull (ψ₁ ≫ m2.φ)) ∧
      ∀ a : 𝓞 E, (P.oA.act a).left ≫ ψ₁ ≫ m2.φ = (ψ₁ ≫ m2.φ) ≫ (t₀.act.act a).left := by
  letI := H.starRing
  have := P.U.gen_hom
  have : IsMonHom P.U.gen.symm.hom := by show IsMonHom P.U.gen.inv; infer_instance
  set k : P.A.A.left ⟶ t.G.left := P.U.gen.inv.left ≫ pullback.fst t.G.hom (jK R) with hk
  have gpG : IsGrpPullback P.A.A t.G (jK R) k :=
    ((isGrpPullback_of_iso P.U.gen.symm).comp (isGrpPullback_pullback t.G (jK R))).congr (Category.id_comp _) rfl
  let ψ₁ : P.A.A.left ⟶ tK.G.left := m1.cart.1.lift k P.A.A.hom gpG.1.w
  have hψ₁ : ψ₁ ≫ m1.φ = k := m1.cart.1.lift_fst _ _ _
  have hψ₂ : ψ₁ ≫ tK.G.hom = P.A.A.hom := m1.cart.1.lift_snd _ _ _
  have n : IsGrpPullback P.A.A t.G (𝟙 _ ≫ jK R) (ψ₁ ≫ m1.φ) :=
    gpG.congr (Category.id_comp _).symm hψ₁.symm
  have cart1 : IsGrpPullback P.A.A tK.G (𝟙 _) ψ₁ := m1.cart.cancel n (hψ₂.trans (Category.comp_id _).symm)
  have cart : IsGrpPullback P.A.A t₀.G z (ψ₁ ≫ m2.φ) := (cart1.comp m2.cart).congr (Category.id_comp _) rfl
  have actA : ∀ x, (P.oA.act x).left ≫ k = k ≫ (t.act.act x).left := by
    intro x
    have e : P.oA.act x ≫ P.U.gen.inv = P.U.gen.inv ≫ (Over.pullback (jK R)).map (t.act.act x) := by
      rw [Iso.comp_inv_eq, Category.assoc]
      exact ((Iso.inv_comp_eq _).2 (P.lin.ext x)).symm
    rw [hk, ← Category.assoc, ← Over.comp_left, e, Over.comp_left, Category.assoc]
    exact congrArg _ (pullback.lift_fst _ _ _)
  have actK : ∀ a : 𝓞 E, (P.oA.act a).left ≫ ψ₁ = ψ₁ ≫ (tK.act.act a).left := by
    intro a
    apply m1.cart.1.hom_ext
    · calc ((P.oA.act a).left ≫ ψ₁) ≫ m1.φ = (P.oA.act a).left ≫ k := by rw [Category.assoc, hψ₁]
        _ = k ≫ (t.act.act a).left := actA a
        _ = (ψ₁ ≫ (tK.act.act a).left) ≫ m1.φ := by rw [Category.assoc ψ₁, m1.act a, ← Category.assoc, hψ₁]
    · rw [Category.assoc, hψ₂, Over.w (P.oA.act a), Category.assoc, Over.w (tK.act.act a), hψ₂]

  have hgi : P.U.gen.inv.left ≫ P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have B₁ : LBIso (P.A.L.pull (𝟙 _)) (P.U.LG.L.pull k) :=
    LBIso.chartPull (chartPullSame P.A.L (fun _ => 𝟙 _) (fun _ => P.U.gen.hom.left) _ P.U.gen.inv.left
        (fun _ => hgi.symm))
      (chartPullSame P.U.LG.L (fun _ => k) (fun _ => pullback.fst t.G.hom (jK R)) _ P.U.gen.inv.left
        (fun _ => rfl)) P.U.ext
  have B₁' : LBIso P.A.L (t.PP.L.pull k) := by
    rw [← P.bundle]
    exact LBIso.chartPull (chartPullUnpull P.A.L (𝟙 _) rfl) (chartPullId _) B₁
  obtain ⟨w₂, -, g₂, -⟩ := rigIso_congr rfl m1.cm m1.lin rfl rfl
  have B₂ : LBIso (tK.PP.L.pull ψ₁) (t.PP.L.pull k) :=
    LBIso.chartPull (chartPullPull tK.PP.L ψ₁)
      (chartPullSame t.PP.L (fun _ => k) (fun _ => m1.φ) _ ψ₁ (fun _ => hψ₁.symm)) ⟨w₂, g₂⟩
  obtain ⟨w₃, -, g₃, -⟩ := rigIso_congr rfl m2.cm m2.lin rfl rfl
  have B₃ : LBIso (tK.PP.L.pull ψ₁) (t₀.PP.L.pull (ψ₁ ≫ m2.φ)) :=
    LBIso.chartPull (chartPullPull tK.PP.L ψ₁)
      (chartPullSame t₀.PP.L (fun _ => ψ₁ ≫ m2.φ) (fun _ => m2.φ) _ ψ₁ (fun _ => rfl)) ⟨w₃, g₃⟩
  have BL : LBIso P.A.L (t₀.PP.L.pull (ψ₁ ≫ m2.φ)) :=
    LBIso.trans P.A.isLB (pull_isLB tK.PP.isLB _) (pull_isLB t₀.PP.isLB _)
      (LBIso.trans P.A.isLB (pull_isLB t.PP.isLB _) (pull_isLB tK.PP.isLB _) B₁' (LBIso.symm B₂)) B₃
  refine ⟨ψ₁, hψ₁, cart, BL, fun a => ?_⟩
  rw [← Category.assoc, actK, Category.assoc, m2.act a, Category.assoc]

end GlobalTheory.LowDat

namespace GlobalTheory.LowDat

theorem exists_xfLevel : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R)))
    (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
    ∃ I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F), GlobalTheory.LowDat.XFLevel C tK m1 m2 F I := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C tK m1 m2 F _ _ _
  letI := H.starRing
  have := hR.2
  have hT := GlobalTheory.FlatTors.torsionIso_holds E H R _ hR.1 C.t C.P
  have hM' : 0 < l.M' := Nat.lcm_pos (by have := l.three_le; omega) l.A_pos
  let β : KA l →+* F := (toF C F).comp (IntermediateField.inclusion c.le).toRingHom
  have hx : (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) ≫ Xo.s = spMap β := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc C.y, C.y_over]
    simp only [β, toF, spMap_comp, Category.assoc]
  obtain ⟨-, J0, hζ0, jA, jM⟩ := Xo.univ.geom F (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) β hx
  haveI := c.fin
  obtain ⟨w, hw1, hw2, hw3⟩ := GlobalTheory.HostModel.exists_roots c.F F (toF C F)
  have hwA : w l.A = J0.ζ l.A := Units.ext (by
    rw [hw3 l.A l.A_pos ⟨zeta l.A, c.le (IntermediateField.subset_adjoin _ _ (by simp))⟩ rfl, hζ0]
    rfl)
  obtain ⟨J, hJζ, hJA, hJM⟩ := exists_tateIso_roots l J0 w hw1 hw2 hwA
  obtain ⟨ψ₁, h1, gψ, lψ, aψ⟩ := exists_genFib C.P tK m1 Xo.univ.t (C.y ≫ pullback.fst _ _) m2
  obtain ⟨I, hI, eI⟩ := GlobalTheory.ArcOfPoint.exists_tateIsoQ Dw hR.1 C.P hT Xo.univ.t _ _ gψ lψ aψ F J
  refine ⟨I, ?_, ?_⟩
  · rw [hI, hJζ _ hM', hw3 _ hM' ⟨zeta l.M', c.zeta_mem⟩ rfl]
  · intro k a σ hσ x hx
    have hk : 0 < k := by
      rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
      exacts [l.A_pos, by have := l.three_le; omega]
    have hJσ : toUnit _ ≫ σ = J.ev k a := by
      rcases hσ with ⟨rfl, rfl⟩ | ⟨rfl, ha, rfl⟩
      · rw [hJA]; exact jA a
      · rw [hJM a ha]; exact jM a ha
    obtain ⟨f, f₁, f₂, f₃, -⟩ := hT F k hk
    obtain ⟨e, he⟩ : ∃ e : (TFK (R := R) F ⟶ C.P.A.A) ≃*
        (Over.mk (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _) ⟶ Xo.univ.t.G),
        ∀ x, (e x).left = x.left ≫ ψ₁ ≫ m2.φ := GlobalTheory.LiePull.exists_pushEquiv gψ (TFK (R := R) F) _ rfl
    have hx' : (e.symm (J.ev k a)).left ≫ ψ₁ ≫ m2.φ = (J.ev k a).left := by
      rw [← he, MulEquiv.apply_symm_apply]
    have hxk : e.symm (J.ev k a) ^ k = 1 := by
      rw [← map_pow, (J.onto k hk _).2 ⟨a, rfl⟩, map_one]
    obtain ⟨p, hp⟩ := f₂ _ hxk
    have hpe := eI k hk a p _ hx' ((f₁ p _).2 hp.symm)
    have hxx : x = e.symm (J.ev k a) := by
      rw [(f₁ _ _).1 hx, ← hp]; exact ((f₃ _ _).2 hpe).symm
    refine ⟨x.left ≫ ψ₁, by rw [Category.assoc, h1], ?_⟩
    rw [Category.assoc, hxx, hx', ← hJσ, Over.comp_left]
    have ht : (toUnit (Over.mk (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _))).left =
        jFK (R := R) F ≫ C.y ≫ pullback.fst _ _ := by
      simpa using Over.w (toUnit (Over.mk (jFK (R := R) F ≫ C.y ≫ pullback.fst _ _)))
    rw [ht]
    simp only [Category.assoc]

end GlobalTheory.LowDat
end
end
