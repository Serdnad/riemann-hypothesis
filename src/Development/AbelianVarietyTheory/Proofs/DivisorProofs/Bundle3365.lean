module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3354
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3035
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierMultipleGlobalSectionsChartEqSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3113
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3357
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3341
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3332
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2827
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle536
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3220
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3257
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle125
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3358
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3342
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle751
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.PowerSeries.Ideal
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.TraitCen

variable {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω]

theorem isNoetherianRing_stalk (M : RatModel o' Ω) (x : M.Z) : IsNoetherianRing (M.Z.presheaf.stalk x) := by
  have : IsDedekindDomain o' := ArithBase.ded (Ω := Ω)
  have := M.lft
  have : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  infer_instance

theorem isDomain_stalk (M : RatModel o' Ω) (x : M.Z) : IsDomain (M.Z.presheaf.stalk x) :=
  (M.stalkHom_injective x).isDomain _

theorem charZero_stalk (M : RatModel o' Ω) (x : M.Z) : CharZero (M.Z.presheaf.stalk x) := by
  have : CharZero Ω := ArithBase.char (o := o')
  exact ⟨fun a b e => Nat.cast_injective (R := Ω) (by simpa using congrArg (M.stalkHom x) e)⟩

theorem exists_cdvr (M : RatModel o' Ω) (U₀ : M.Z.Opens) (hU : (U₀ : Set M.Z).Nonempty) (x : M.Z) :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : CharZero W)
      (_ : IsAdicComplete (maximalIdeal W) W) (a : Sp W ⟶ M.Z),
      a (closedPoint W) = x ∧ ∀ t, (jK W ≫ a) t ∈ U₀ := by
  let O := M.Z.presheaf.stalk x
  have : IsNoetherianRing O := isNoetherianRing_stalk M x
  have : IsDomain O := isDomain_stalk M x
  have : CharZero O := charZero_stalk M x

  have hη : genericPoint M.Z ∈ U₀ := by
    obtain ⟨z, hz⟩ := hU
    exact (genericPoint_specializes z).mem_open U₀.isOpen hz
  have h1 : genericPoint M.Z ∈ Set.range (M.Z.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes x
  obtain ⟨q, hq⟩ := h1
  obtain ⟨_, ⟨f₀, rfl⟩, hqf, hf⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (a := q) (show q ∈ (M.Z.fromSpecStalk x) ⁻¹' (U₀ : Set M.Z) from by simpa [hq] using hη)
    (U₀.isOpen.preimage (M.Z.fromSpecStalk x).continuous)
  have hf₀ : f₀ ≠ 0 := fun h => hqf (by simp [h])

  let κ := ResidueField (PowerSeries O)
  let p := ringChar κ
  let c : PowerSeries O := if p = 0 then 1 else (p : PowerSeries O)
  have hc0 : c ≠ 0 := by
    by_cases hp : p = 0
    · simp [c, hp]
    · simp only [c, hp, if_false]
      rw [← map_natCast (PowerSeries.C (R := O))]
      exact (map_ne_zero_iff _ (PowerSeries.C_injective)).2 (Nat.cast_ne_zero.2 hp)
  let f : PowerSeries O := PowerSeries.X * PowerSeries.C f₀ * c
  have hfm : f ∈ maximalIdeal (PowerSeries O) := by
    refine Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ ?_)
    rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
    simp
  have hf0 : f ∉ (⊥ : Ideal (PowerSeries O)) := by
    rw [Ideal.mem_bot]
    exact mul_ne_zero (mul_ne_zero PowerSeries.X_ne_zero ((map_ne_zero_iff _ PowerSeries.C_injective).2 hf₀)) hc0
  let φ : PowerSeries O →+* AlgebraicClosure κ := (algebraMap κ (AlgebraicClosure κ)).comp (residue (PowerSeries O))
  obtain ⟨W, _, _, _, hW, ψ, ιk, hψf, hψ⟩ :=
    GlobalTheory.GeomTrait.exists_dvr hfm ⊥ Ideal.isPrime_bot hf0 φ
  let ψ' : O →+* W := ψ.comp PowerSeries.C
  have hψloc : IsLocalHom ψ := ⟨fun a ha => isUnit_of_map_unit φ a (by
    have h := (ha.map (residue W)).map ιk
    rw [← hψ]
    exact h)⟩
  have hCloc : IsLocalHom (PowerSeries.C (R := O)) := ⟨fun a ha => by
    simpa using ha.map (PowerSeries.constantCoeff (R := O))⟩
  have hψ'loc : IsLocalHom ψ' := RingHom.isLocalHom_comp ψ _
  have hψ'f₀ : ψ' f₀ ≠ 0 := fun h => hψf (by
    simp only [f, map_mul]
    rw [show ψ (PowerSeries.C f₀) = ψ' f₀ from rfl, h, mul_zero, zero_mul])
  have hcz : CharZero W := by
    obtain ⟨q, hq⟩ := CharP.exists W
    rcases CharP.char_is_prime_or_zero W q with hqp | hq0
    · exfalso
      have hqW : (q : W) = 0 := CharP.cast_eq_zero W q
      have hqκ : (q : κ) = 0 := by
        have h := congrArg (ιk.comp (residue W)) hqW
        rw [map_natCast, map_zero] at h
        refine (map_eq_zero_iff (algebraMap κ (AlgebraicClosure κ)) (algebraMap κ _).injective).1 ?_
        rw [map_natCast]
        exact h
      have : CharP κ q := (CharP.charP_iff_prime_eq_zero hqp).2 hqκ
      have hpq : p = q := ringChar.eq κ q
      have hp : p ≠ 0 := hpq ▸ hqp.ne_zero
      apply hψf
      have hc : c = (q : PowerSeries O) := by simp only [c, if_neg hp, hpq]
      show ψ (PowerSeries.X * PowerSeries.C f₀ * c) = 0
      rw [hc, map_mul, map_natCast, hqW, mul_zero]
    · subst hq0
      exact CharP.charP_to_charZero W
  let a : Sp W ⟶ M.Z := Spec.map (CommRingCat.ofHom ψ') ≫ M.Z.fromSpecStalk x
  refine ⟨W, inferInstance, inferInstance, inferInstance, hcz, hW, a, ?_, fun t => ?_⟩
  · have h : (Spec.map (CommRingCat.ofHom ψ')) (closedPoint W) = closedPoint O := IsLocalRing.comap_closedPoint ψ'
    show M.Z.fromSpecStalk x ((Spec.map (CommRingCat.ofHom ψ')) (closedPoint W)) = x
    rw [h, Scheme.fromSpecStalk_closedPoint]
  · have ht : (jK W) t = (⊥ : PrimeSpectrum W) := by
      apply PrimeSpectrum.ext
      change Ideal.comap (algebraMap W (FractionRing W)) t.asIdeal = ⊥
      rw [@Ideal.eq_bot_of_prime _ _ t.asIdeal t.isPrime]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
    have hm : (PrimeSpectrum.comap ψ' ⊥ : PrimeSpectrum O) ∈ (PrimeSpectrum.basicOpen f₀ : Set (PrimeSpectrum O)) := by
      show f₀ ∉ Ideal.comap ψ' ⊥
      rw [Ideal.mem_comap, Ideal.mem_bot]
      exact hψ'f₀
    have := hf hm
    simp only [a, Scheme.Hom.comp_apply, ht]
    exact this

theorem exists_trait_cen : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (o' Ω : Type) [CommRing o']
    [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (M : RatModel o' Ω) (U₀ : M.Z.Opens), (U₀ : Set M.Z).Nonempty →
    ∀ (X : Scheme.{0}) (u₀ : U₀.toScheme ⟶ X) (u : X ⟶ F.X) (x : M.Z), IsClosed ({x} : Set M.Z) →
      ∃ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ u₀ u T ξ ∧ ξ (IsLocalRing.closedPoint T.V) = x := by
  intro g n o _ ζ F o' Ω _ _ _ _ M U₀ hU X u₀ u x _
  obtain ⟨W, _, _, _, _, hc, a, ha, hg⟩ := exists_cdvr M U₀ hU x
  have hr : Set.range (jK W ≫ a) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact hg t
  let ξ₀' : Sp (FractionRing W) ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι (jK W ≫ a) hr
  have hξ₀' : ξ₀' ≫ U₀.ι = jK W ≫ a := IsOpenImmersion.lift_fac _ _ _
  have hB : GlobalTheory.Mum.Base W := ⟨⟨inferInstance, inferInstance, inferInstance, hc⟩, inferInstance⟩
  obtain ⟨T, f, fK, -, hloc, -, hcomp, hy⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n o ζ F W hB inferInstance (ξ₀' ≫ u₀ ≫ u)
  refine ⟨T, spMap f ≫ a, ⟨spMap fK ≫ ξ₀', ?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hξ₀', ← Category.assoc, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact hcomp r
  · rw [hy, Category.assoc]
  · have h : (spMap f) (closedPoint T.V) = closedPoint W := IsLocalRing.comap_closedPoint f
    show a ((spMap f) (closedPoint T.V)) = x
    rw [h, ha]

end GlobalTheory.Poinc.TraitCen
end
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

theorem GlobalTheory.UPoinc.exists_uTrait_of_stalk_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [CharZero Ω] (M : RatModel o' Ω) (y₀ : Sp Ω ⟶ Xo.XF c) (x : M.Z) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V], IsAdicComplete (maximalIdeal V) V → ∀ θ : M.Z.presheaf.stalk x →+* V, Function.Injective θ → ∃ (T : UTrait Xo c) (f : V →+* T.V) (γ : Ω →+* FractionRing T.V), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, γ (M.stalkHom x a) = algebraMap T.V (FractionRing T.V) (f (θ a))) ∧ jK T.V ≫ spMap (f.comp θ) ≫ M.Z.fromSpecStalk x = spMap γ ≫ M.pt ∧ T.y = spMap γ ≫ y₀ := by
  intro E _ _ _ H Dw l Xo c o' Ω _ _ _ _ M y₀ x V _ _ _ hcomp θ hθ
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
    GlobalTheory.UTraitExt.uTraitExtSt E H Dw l Xo c V hB inferInstance (spMap γ₀ ≫ y₀)
  refine ⟨T, f, fK.comp γ₀, hfi, hfl, ?_, ?_, ?_⟩
  · intro a
    rw [RingHom.comp_apply, hγ₀, hc]
  · have e : (algebraMap T.V (FractionRing T.V)).comp (f.comp θ) = (fK.comp γ₀).comp (M.stalkHom x) := by
      ext a
      simp only [RingHom.comp_apply, hγ₀, hc]
    rw [← GlobalTheory.Poinc.GenTrait.spMap_stalkHom_fromSpecStalk M x, ← Category.assoc, Formalism.L2.Pj.spMap_comp', e,
      ← Formalism.L2.Pj.spMap_comp', Category.assoc]
  · rw [hy, ← Category.assoc, Formalism.L2.Pj.spMap_comp']
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

theorem _root_.GlobalTheory.T.cartierMultipleGlobalSections_chart_eq_span : ∀ (σ : Setup) (x : Sp σ.R) (k : ℕ), Sec (σ.D₁ x) k = spanBy (GlobalTheory.Desc.cst (σ.C x).G.hom) (σ.θ x '' σ.N k) := by
  first | exact @GlobalTheory.Desc.ChartSpan.sec_eq_spanBy | exact GlobalTheory.Desc.ChartSpan.sec_eq_spanBy | (intros; apply GlobalTheory.Desc.ChartSpan.sec_eq_spanBy <;> assumption)
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

noncomputable section
namespace GlobalTheory.Poinc.Sep.TwistResid

theorem twist_resid : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y1) → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), lab c ∈ X₁.S.supI X₁.M z₁ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ (sg : ℤˣ) (e : ℕ), TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ e → ∀ s u : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) → X₁.M.stalkHom z₁ u = X₁.S.th (lab c + τ) / X₁.S.th (lab c) → ev1 (s * u) - 1 ∈ maximalIdeal V1 := by
  classical
  intro g n F W Z i X₁ z₁ act x₀ hx₀ V _ _ _ ev Y _ m t δ 𝔪 C lab hlab T hT c hc τ hτ sg e hTw s u hs hu
  have hcd : X₁.M.Div X₁.S.th (lab c) z₁ := hc
  have hqO : X₁.S.th (lab c) / X₁.S.th x₀ ∈ X₁.M.O z₁ := hx₀.2 (lab c)
  let r := (X₁.M.stalkEquiv z₁).symm ⟨_, hqO⟩
  have hr : X₁.M.stalkHom z₁ r = X₁.S.th (lab c) / X₁.S.th x₀ := by
    rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
  have hrU : IsUnit r := ((RatModel.isUnit_O_iff (⟨_, hqO⟩ : X₁.M.O z₁)).2
    ⟨div_ne_zero hcd.1 hx₀.1, by rw [inv_div]; exact hcd.2 x₀⟩).map (X₁.M.stalkEquiv z₁).symm
  obtain ⟨zt, hzt⟩ := exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))
  obtain ⟨wt, hwt⟩ := GlobalTheory.T.twistWeight_wellDefined_on_lattice_class g n F W Z i X₁ z₁ act x₀ hx₀ V ev Y m t δ 𝔪 sg τ hτ
  let wt' : (Fin 8 → Y) → ZMod (X₁.S.r * X₁.S.N) := fun mu => if mu = 0 then 0 else wt mu
  have hwt' : ∀ a mu, 𝔪.YY a mu → wt' mu = (sg : ℤ) • eStd X₁.S.g _ τ a := by
    intro a mu h
    by_cases h0 : mu = 0
    · subst h0
      have ha : a ∈ X₁.S.HH X₁.M z₁ := (GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i X₁ z₁ act x₀ hx₀ V ev Y m t δ 𝔪 a).2 h
      have h1 : eStd X₁.S.g _ τ a = 0 := hτ a ha
      simp only [wt', if_pos rfl, h1, smul_zero]
    · simp only [wt', if_neg h0]
      exact hwt a mu h
  have hh : X₁.M.stalkHom z₁ (s * u * r) = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e) * X₁.S.th (lab c + τ) / X₁.S.th x₀ := by
    rw [map_mul, map_mul, hs, hu, hr]
    field_simp [hcd.1, hx₀.1]
  obtain ⟨N, -, -, -, hN⟩ := hTw zt (s * u * r) hzt hh wt' hwt'
  obtain ⟨S, hS⟩ := hN 1
  have h1 := hS (insert 0 S) (Finset.subset_insert _ _)
  have hle : maximalIdeal V ^ 1 • N ≤ (maximalIdeal V : Submodule V V) :=
    Submodule.smul_le.2 fun a ha b _ => by
      rw [smul_eq_mul]; exact Ideal.mul_mem_right b _ (by simpa using ha)
  have h2 := hle h1
  rw [← Finset.add_sum_erase _ _ (Finset.mem_insert_self 0 S)] at h2
  have h3 : ∑ mu ∈ (insert 0 S).erase 0, ev zt ^ (wt' mu).val * T mu c ∈ maximalIdeal V :=
    Ideal.sum_mem _ fun mu hmu => Ideal.mul_mem_left _ _
      (GlobalTheory.T.thetaModelMember_term_mem_maximalIdeal g n F W Z i X₁ z₁ act x₀ hx₀ V ev Y m t δ 𝔪 C lab hlab T hT c mu (Finset.ne_of_mem_erase hmu))
  have h0 : ev zt ^ (wt' 0).val * T 0 c = T 0 c := by simp [wt']
  rw [h0] at h2
  have h4 : ev (s * u * r) - T 0 c ∈ maximalIdeal V := by
    have := Ideal.add_mem _ h2 h3
    simpa [sub_add_eq_sub_sub, sub_add_cancel] using this
  have h5 := GlobalTheory.T.divisor_stalk_evaluation_linear_map_family g n F W Z i X₁ z₁ act x₀ hx₀ V ev Y m t δ 𝔪 C lab hlab T hT c r hr
  have h6 : (ev (s * u) - 1) * ev r ∈ maximalIdeal V := by
    have := Ideal.sub_mem _ h4 h5
    rw [map_mul] at this
    convert this using 1; ring
  exact (Ideal.mul_unit_mem_iff_mem _ (hrU.map ev)).1 h6

end GlobalTheory.Poinc.Sep.TwistResid
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
open GlobalTheory.Poinc.Sep


theorem _root_.GlobalTheory.T.thetaSetup_translation_exponents_affine : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (m2 : ℕ) (t2 : Fin m2 → V2) (δ2 : Fin m2 → LinearMap.BilinForm ℤ Y2) (𝔪2 : UMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ F1 F2 : X₁.S.Gam → ℕ, (∀ a ∈ X₁.S.HH X₁.M z₁, TransExp 𝔪1 x₀ a τ (F1 a)) ∧ (∀ a ∈ X₁.S.HH X₁.M z₁, TransExp 𝔪2 x₀ a τ (F2 a)) ∧ ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((F1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((F2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩) := by
  first | exact @GlobalTheory.Poinc.Sep.trans_exp_affine | exact GlobalTheory.Poinc.Sep.trans_exp_affine | (intros; apply GlobalTheory.Poinc.Sep.trans_exp_affine <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.semiabelianModel_fibre_specialization_chain : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ y y' : Y.Z, πY y = z₁ → πY y' = z₁ → Relation.EqvGen (fun a b : Y.Z => πY a = z₁ ∧ πY b = z₁ ∧ a ⤳ b) y y' := by
  first | exact @GlobalTheory.SpecChain.fibre_chain | exact GlobalTheory.SpecChain.fibre_chain | (intros; apply GlobalTheory.SpecChain.fibre_chain <;> assumption)
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
open GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GSep.FrameExpEx
open GlobalTheory.Poinc.TorsRatio

theorem torsFrame_ratio : ∀ (V : Type) [CommRing V] [IsDomain V] (A : PolAV (Sp (FractionRing V))) (ρA : LB.Gen (A.L.pull (eSec A.A))), ρA.IsGen → ∀ (N : ℕ), 1 ≤ N → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e e' : FrAt x), IsTorsFrame A ρA N x e → IsTorsFrame A ρA N x e' → ∃ l : FractionRing V, l ^ (N ^ 2) = 1 ∧ ∀ z J, Good A.L z J → (Geo.Tor.val e' (𝟙 _) z J).val = GlobalTheory.Poinc.TorsRatio.cstK z l * (Geo.Tor.val e (𝟙 _) z J).val := by
  intro V _ _ A ρA _ N _ x e e' H H'
  obtain ⟨-, he, α, hα, nα, cα⟩ := H
  obtain ⟨-, he', α', hα', nα', cα'⟩ := H'
  obtain ⟨l, hl0, hl⟩ := frame_ratio he he'
  have hp : Function.Surjective A.A.hom.appTop.hom := (GlobalTheory.globalFns_holds _ _ A.isAb).2
  have hαα : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.A.left) (z : Z) J, Good A.L z J →
      Geo.Tor.val α r z J = Geo.Tor.val α' r z J :=
    gen_unique A.isLB A.A.hom (eSec A.A) (Over.w η[A.A]) hp hα hα' (fun w I hI => by
      have a := val_corr hI nα (𝟙 _)
      have b := val_corr hI nα' (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a b
      exact a.trans b.symm)
  let z : (TFK (R := V) (FractionRing V)).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  choose J hJ using fun χ : (TFK (R := V) (FractionRing V)).left ⟶ A.A.left => Geo.Tor.exists_chart A.isLB (χ z)
  replace hJ : Good A.L z J := hJ
  have q : Geo.Tor.val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) = Geo.Tor.val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := by
    have a := val_corr hJ cα (𝟙 _)
    have b := val_corr hJ cα' (𝟙 _)
    have p₁ : Geo.Tor.val (powFrame A.A A.L x e ((N : ℤ) ^ 2)) (𝟙 _) z J =
      Geo.Tor.val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    have p₂ : Geo.Tor.val (powFrame A.A A.L x e' ((N : ℤ) ^ 2)) (𝟙 _) z J =
      Geo.Tor.val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    rw [val_mul hJ, val_pull hJ] at a b
    rw [← p₁, ← p₂, a, b, hαα _ _ z J hJ]
  have hlN : l ^ (N ^ 2) = 1 := by
    have q' := congrArg Units.val q
    rw [show ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, hl z J hJ, mul_pow, ← map_pow] at q'
    have hu : IsUnit ((Geo.Tor.val e (𝟙 _) z J).val ^ (N ^ 2)) := (Units.isUnit _).pow _
    have h1 : cstK z (l ^ (N ^ 2)) = cstK z 1 := by
      rw [map_one]
      exact hu.mul_left_inj.1 (by rw [_root_.one_mul]; exact q'.symm)
    exact (cstK z).injective h1
  exact ⟨l, hlN, hl⟩

end GlobalTheory.GSep.FrameExpEx

namespace GlobalTheory.GSep.FrameExpEx
open GlobalTheory.GSep.TwistTranslate


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem exists_frExp : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (Y : Type) [AddCommGroup Y] (t : Y → V) (δ : I → Y → Y) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev Y t δ), ∀ a ∈ X₁.S.HH X₁.M z₁, ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ e : ℕ, GlobalTheory.GSep.TransTerms.FrExp 𝔪 a τ e := by
  intro I X₁ z₁ act x₀ hdiv V _ _ _ ev Y _ t δ 𝔪 a ha τ hτ
  obtain ⟨T, hT⟩ := GlobalTheory.T.thetaMember_exists_terms_dividing_group_label I X₁ z₁ act x₀ hdiv V ev Y t δ 𝔪 a ha
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, -⟩ := hT
  obtain ⟨χ₀, hχ₀, hyp⟩ := GlobalTheory.T.exists_level_killed_char_of_torus_label I X₁ z₁ act V ev Y t δ 𝔪 τ hτ
  have hT₀ : GlobalTheory.GSep.TransTerms.TorChar 𝔪 τ χ₀ := ⟨hχ₀, hyp⟩
  obtain ⟨ρA, hρA, htors⟩ := exists_rig_torsFrame 𝔪 x fr hx hfr
  have hg₀ : IsTor χ₀ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀)) :=
    (isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ₀)
  obtain ⟨p, xτ, hpy, hpg, hq, hxτ⟩ := hyp _ hg₀
  have hadd := (GlobalTheory.TorusExt.isAdd_iff_eq (g' ()) (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀)) _).2 rfl
  have hb := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  obtain ⟨w₂, hw₂g, hw₂v⟩ : ∃ w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 (g' () + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀)).b,
      w₂.IsGen ∧ ∀ z J, val w₂ (𝟙 _) z J = val (w ()) (𝟙 _) z J := by
    revert hb
    generalize (g' () + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀)).b = b
    rintro rfl
    exact ⟨w (), (hc ()).2.1, fun _ _ => rfl⟩
  obtain ⟨e₂, he₂, hov⟩ := over_translate 𝔪 w₀ hw₀ ρA hρA (x a) (fr a) (htors _)
    (g' ()) (w ()) (hc ()).1 (hc ()).2.1 (hc ()).2.2 χ₀ hχ₀ _ hg₀ p xτ hpy hpg hq _ hadd w₂ (fun z J _ => hw₂v z J)
    (x (a + τ)) (x_add 𝔪 x hx a τ xτ hxτ)
  have hN : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  obtain ⟨l, hl, hlv⟩ := torsFrame_ratio V 𝔪.A ρA hρA _ hN _ _ _ he₂ (htors (a + τ))
  obtain ⟨e, he⟩ := eq_yK_zeta_pow 𝔪 l hl
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hl
    exact zero_ne_one hl
  refine ⟨e, ⟨χ₀, hT₀⟩, x, fr, th, w₀, s, g' (), w (), hx, hfr, hth, hw₀, hs, (hc ()).1, (hc ()).2.1, (hc ()).2.2, ?_⟩
  intro χ hχ g₀ hg₀' g'' hadd'' w'' _ hval
  obtain rfl : χ₀ = χ := GlobalTheory.T.thetaMember_torus_character_unique I X₁ z₁ act V ev Y t δ 𝔪 τ χ₀ χ hT₀ hχ
  obtain rfl : g₀ = GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ₀) :=
    (GlobalTheory.TorusExt.isTorusPtF_iff_eq g₀ χ₀).1 ((isTor_iff _ _).1 hg₀')
  obtain rfl := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).1 hadd''
  refine GlobalTheory.T.thetaMember_lies_over_rescale_frames I X₁ z₁ act V ev Y t δ 𝔪 w₀ _ w₂ w'' (x (a + τ)) e₂ (fr (a + τ)) l hl0 hlv (fun z J hJ => ?_) hov
  rw [hw₂v, hval z J hJ, he]

end GlobalTheory.GSep.FrameExpEx
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_carried_frame_off_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β), ∀ y : G.left, G.hom y ≠ closedPoint R → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  first | exact @GlobalTheory.Mum.exists_carried_frame_off_closed | exact GlobalTheory.Mum.exists_carried_frame_off_closed | (intros; apply GlobalTheory.Mum.exists_carried_frame_off_closed <;> assumption)
end

section

namespace GlobalTheory.GoodMetric

theorem goodChernWeil : GlobalTheory.Published.GoodChernWeil :=
  goodChernWeil_of_goodTopChernForm GlobalTheory.T.goodMetric_topChernForm_integral_eq_smooth GlobalTheory.T.chernNumbers_eq_integral_chernForms_smoothMetric GlobalTheory.T.fullFlagBundle_pushForward_formula

end GlobalTheory.GoodMetric
end
