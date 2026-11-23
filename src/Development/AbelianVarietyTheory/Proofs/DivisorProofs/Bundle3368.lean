module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3363
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRatPointOfFiniteType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle113
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3362
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle681
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle665
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2754
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2917
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


theorem _root_.GlobalTheory.T.exists_finiteExtension_idempotentFactor_trait_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁) (G₁ : Over (Sp R₁)) [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left) (β₁₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (gen₁ : (Over.pullback (jK R₁)).obj G₁ ≅ A₁.A), FinExt ρ₁ → IsGrpPullback G₁ G (spMap ρ₁) β₁ → Geo.Tor.IsSquare β₁ β₁₂ → IsMonHom gen₁.hom → ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₁₂) → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ₂ : R →+* R₂) (D₂ D₂' : DegData R₂ (maximalIdeal R₂)) (F₂ : Factor D₂.toPre D₂'.toPre) (A₂' : PolAV (Sp (FractionRing R₂))) (G₂' : Over (Sp R₂)) (_ : GrpObj G₂') (_ : IsCommMonObj G₂') (U₂' : Unif (maximalIdeal R₂) D₂' A₂' G₂') (oA₂ : A₂'.OAct F₂.O) (oG₂ : RingAct G₂' F₂.O) (G₂ : Over (Sp R₂)) (_ : GrpObj G₂) (_ : IsCommMonObj G₂) (inc₂ : G₂ ⟶ G₂') (pr₂ : G₂' ⟶ G₂) (β₂ : G₂.left ⟶ G.left) (β₂₂ : (G2 G₂).left ⟶ (G2 G).left) (A₂ : PolAV (Sp (FractionRing R₂))) (gen₂ : ((Over.pullback (jK R₂)).obj G₂) ≅ A₂.A) (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R₂ →+* W) (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (βW : GW.left ⟶ G₂.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G₂.hom (jK R₂)), FinExt ρ₂ ∧ Base R₂ ∧ IsSemiAbelian G₂' ∧ U₂'.toUnifPre.OLinear F₂.O F₂.o oA₂ oG₂ ∧ IsSemiAbelian G₂ ∧ IsMonHom inc₂ ∧ IsMonHom pr₂ ∧ inc₂ ≫ pr₂ = 𝟙 G₂ ∧ pr₂ ≫ inc₂ = oG₂.act F₂.e ∧ IsGrpPullback G₂ G (spMap ρ₂) β₂ ∧ Geo.Tor.IsSquare β₂ β₂₂ ∧ IsMonHom gen₂.hom ∧ ExtLam G₂ (A₂.L.pull gen₂.hom.left) ((abelian₂ G₂' U₂'.LG.L).pull (lift (fst G₂ G₂ ≫ inc₂) (snd G₂ G₂ ≫ inc₂ ≫ oG₂.act F₂.f) : G2 G₂ ⟶ G2 G₂').left) ∧ LBIso ((abelian₂ G₂' U₂'.LG.L).pull (lift (fst G₂ G₂ ≫ inc₂) (snd G₂ G₂ ≫ inc₂ ≫ oG₂.act F₂.f) : G2 G₂ ⟶ G2 G₂').left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₂₂) ∧ GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ IsGrpPullback GW G₂ (spMap φ) βW ∧ κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW ∧ LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A₂.L.pull gen₂.hom.left).pull κ) := by
  first | exact @GlobalTheory.Mum.FactorMove.exists_finExt_factor_trait | exact GlobalTheory.Mum.FactorMove.exists_finExt_factor_trait | (intros; apply GlobalTheory.Mum.FactorMove.exists_finExt_factor_trait <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.exists_unitary_local_periods_thetaModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C) (Y : RatModel X₁.o₁ X₁.Ω₁) (U₀ : Y.Z.Opens) (EE : Y.Lat X₁.S.J) (out : ZHOut X₁.ρ Y U₀ EE) (πY : Y.Z ⟶ X₁.M.Z), X₁.S.admitted Y U₀ → X₁.S.IsEE Y U₀ EE → X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY → ∀ x : Y.Z, ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (j : Y.Z.presheaf.stalk x →+* R) (Λ : Type) (_ : AddCommGroup Λ) (_ : Module (𝓞 E) Λ) (p : Λ → R) (c₀ : ℕ), IsNoetherianRing R ∧ CharZero R ∧ GlobalTheory.Poinc.Eq8.IsCpl j ∧ 1 ≤ c₀ ∧ ∀ (T : UTrait Xo c) (ψ : R →+* T.V), IsLocalHom ψ → T.y ≫ C.i = jK T.V ≫ (spMap (ψ.comp j) ≫ Y.Z.fromSpecStalk x) ≫ πY ≫ X₁.π → ∃ e : Λ ≃ₗ[𝓞 E] T.P.D.toPre.X, ∀ a, ∃ k : ℕ, (k : ℤ) = c₀ * T.be (e a) (e a) ∧ Associated (ψ (p a)) (T.ϖ ^ k) := by
  first | exact @GlobalTheory.UPoinc.UPeriods.main | exact GlobalTheory.UPoinc.UPeriods.main | (intros; apply GlobalTheory.UPoinc.UPeriods.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.classicalPoint_factors_through_siegelModuli_trait : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z), IsOpenImmersion i → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ Y.Z), Set.range (gPt p ≫ y ≫ πY ≫ X₁.π) ⊆ Set.range i → ∃ (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p) (j : T.V →+* OO p) (ξ : Sp T.V ⟶ Y.Z), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) ∧ (∀ v, (j v : PadicAlgCl p) = ι (algebraMap T.V (FractionRing T.V) v)) ∧ IsLocalHom j ∧ spMap j ≫ ξ = y ∧ jK T.V ≫ ξ ≫ πY ≫ X₁.π = T.y ≫ i := by
  first | exact @GlobalTheory.Poinc.exists_trait_of_classical_point | exact GlobalTheory.Poinc.exists_trait_of_classical_point | (intros; apply GlobalTheory.Poinc.exists_trait_of_classical_point <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.exists_trait_lift_thetaSetup_model_after_extension : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (i : F.X ⟶ Z) (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i), IsClopen (Set.range X₁.π) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ Z), jK T.V ≫ ξ = T.y ≫ i → ξ (closedPoint T.V) ∈ Set.range X₁.π → ∃ (T' : Trait F) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V) (ξ₁ : Sp T'.V ⟶ X₁.M.Z), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) ∧ T'.y = spMap fK ≫ T.y ∧ spMap f ≫ ξ = ξ₁ ≫ X₁.π ∧ jK T'.V ≫ ξ₁ ≫ X₁.π = T'.y ≫ i := by
  first | exact @GlobalTheory.Poinc.traitLift_setup | exact GlobalTheory.Poinc.traitLift_setup | (intros; apply GlobalTheory.Poinc.traitLift_setup <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

theorem _root_.GlobalTheory.T.norm_descent_ideal_thetaModel_to_clopen_component : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∀ W : Set Z, IsClopen W → IsIrreducible W → ∀ (W8 : Matrix (Fin 8) (Fin 8) ℤ) (X₁ : Setup F W8 i) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = W → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range i) → (∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong J₁ ξ₁ = Ideal.span {T.ϖ ^ a}) → ∃ (k : ℕ) (J : Z.IdealSheafData), 1 ≤ k ∧ (∀ x ∈ J.support, x ∈ W ∧ x ∉ Set.range i) ∧ ∀ (T : Trait F) (ξ₁ : Sp T.V ⟶ X₁.M.Z), jK T.V ≫ ξ₁ ≫ X₁.π = T.y ≫ i → idlAlong J (ξ₁ ≫ X₁.π) = idlAlong J₁ ξ₁ ^ k := by
  first | exact @GlobalTheory.NormDown.normDescent | exact GlobalTheory.NormDown.normDescent | (intros; apply GlobalTheory.NormDown.normDescent <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Extend

theorem pow_exp_eq {V : Type} [CommRing V] [IsDomain V] {ϖ : V} (h : Irreducible ϖ) {a b : ℕ}
    (e : Associated (ϖ ^ a) (ϖ ^ b)) : a = b :=
  le_antisymm ((pow_dvd_pow_iff h.ne_zero h.not_isUnit).1 e.dvd) ((pow_dvd_pow_iff h.ne_zero h.not_isUnit).1 e.symm.dvd)

theorem form_eq_zero {X I : Type} [AddCommGroup X] (B : LinearMap.BilinForm ℤ X) (hB : ∀ a b, B a b = B b a) (b : I → X)
    (hb : Submodule.span ℤ (Set.range b) = ⊤) (h : ∀ i j, B (b i + b j) (b i + b j) = 0) : B = 0 := by
  have h1 : ∀ i j, B (b i) (b i) + 2 * B (b i) (b j) + B (b j) (b j) = 0 := by
    intro i j
    have := h i j
    simp only [map_add (f := _), LinearMap.add_apply] at this
    rw [hB (b j) (b i)] at this
    linarith
  have h2 : ∀ i, B (b i) (b i) = 0 := fun i => by have := h1 i i; linarith
  have h3 : ∀ i j, B (b i) (b j) = 0 := fun i j => by have := h1 i j; have := h2 i; have := h2 j; linarith
  refine LinearMap.ext_on_range hb fun i => LinearMap.ext_on_range hb fun j => ?_
  simpa using h3 i j

theorem evalZ_prop {g n : ℕ} (hn : 2 ≤ n) {F : SFam g n (zetaAway n)} {φ : InvFun ℤ} (hφ : IsPolFan id g φ) (T T' : Trait F)
    (e : T.D.toPre.X ≃+ T'.D.toPre.X) (m s : ℕ) (he : ∀ a b, (m : ℤ) * T'.β (e a) (e b) = s * T.β a b) :
    (m : ℝ) * φ.evalZ T'.β = s * φ.evalZ T.β := by
  have hon := hφ T.D.toPre.X (Trait.finrank_le g n hn F T)
  have hc : toReal T.β ∈ psdCone (bar := (id : ℤ → ℤ)) (X := T.D.toPre.X) :=
    GlobalTheory.PolFan.TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 T.symm) fun x => by simpa using T.mono.nonneg 0 x
  have hc' : toReal (pull e.toIntLinearEquiv.toLinearMap T'.β) ∈ psdCone (bar := (id : ℤ → ℤ)) (X := T.D.toPre.X) :=
    GlobalTheory.PolFan.TameZ.toReal_mem_psdCone_int (mem_balForms_int.2 fun a b => T'.symm _ _) fun x => by
      simpa using T'.mono.nonneg 0 (e x)
  rw [← evalR_toReal φ T.β, ← hon.homog _ hc s s.cast_nonneg,
    ← evalZ_pull φ (r := e.toIntLinearEquiv.toLinearMap) e.surjective, ← evalR_toReal,
    ← hon.homog _ hc' m m.cast_nonneg]
  congr 1
  refine LinearMap.ext₂ fun a b => ?_
  have h := he a b
  simp only [toReal_apply, pull_apply, LinearMap.smul_apply, smul_eq_mul]
  exact_mod_cast h

theorem idlAlong_ne_bot {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    (ξ : Sp R ⟶ X) (h : (jK R ≫ ξ) (closedPoint (FractionRing R)) ∉ J.support) : idlAlong J ξ ≠ ⊥ := by
  intro h0
  have h1 := idlAlong_eq_top_of_notMem_support X J _ _ h
  have eq_map : ∀ {S : Type} [CommRing S] [IsLocalRing S] (χ : Sp S ⟶ X)
      (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1),
      idlAlong J χ = (J.ideal U).map (χ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of S)).hom).hom := by
    intro S _ _ χ U hle
    have hx : χ (closedPoint S) ∈ U.1 := hle trivial
    unfold idlAlong
    rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
    congr 2
  have h2 : idlAlong J (jK R ≫ ξ) = (idlAlong J ξ).map (algebraMap R (FractionRing R)) := by
    obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
      (show ξ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
    have hle : ⊤ ≤ ξ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem ξ hx).ge
    have hle' : ⊤ ≤ (jK R ≫ ξ) ⁻¹ᵁ U := fun x _ => hle (show jK R x ∈ (⊤ : (Sp R).Opens) from trivial)
    rw [eq_map ξ ⟨U, hU⟩ hle, eq_map _ ⟨U, hU⟩ hle', Ideal.map_map]
    congr 1
    have e : (jK R ≫ ξ).appLE U ⊤ hle' = ξ.appLE U ⊤ hle ≫ (jK R).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
    rfl
  rw [h0, Ideal.map_bot] at h2
  exact bot_ne_top (h2.symm.trans h1)

theorem isCpl_props {O R : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R] [IsLocalRing R]
    {j : O →+* R} (hj : IsCpl j) : Function.Injective j ∧ IsLocalHom j ∧
      ∀ (V : Type) [CommRing V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → ∀ φ : O →+* V, IsLocalHom φ →
        ∃ ψ : R →+* V, IsLocalHom ψ ∧ ψ.comp j = φ := by
  obtain ⟨e, he⟩ := hj
  have hj : j = e.toRingHom.comp (algebraMap O _) := RingHom.ext fun a => (he a).symm
  have hl : IsLocalHom (algebraMap O (AdicCompletion (maximalIdeal O) O)) := inferInstance
  refine ⟨?_, ?_, fun V _ _ hV φ hφ => ?_⟩
  · rw [hj]
    exact e.injective.comp (AdicCompletion.of_injective (maximalIdeal O) O)
  · refine ⟨fun a ha => ?_⟩
    rw [← he, MulEquiv.isUnit_map] at ha
    exact isUnit_of_map_unit _ _ ha
  · obtain ⟨ψ, h1, h2⟩ := GlobalTheory.LocalCompletion.exists_localHom_adicCompletion_extend O V hV φ hφ
    refine ⟨ψ.comp e.symm.toRingHom, ⟨fun a ha => ?_⟩, RingHom.ext fun a => ?_⟩
    · have := isUnit_of_map_unit ψ _ ha
      exact (MulEquiv.isUnit_map e.symm).1 this
    · rw [← h2, RingHom.comp_apply, ← he]
      simp

theorem orders_extend : ∀ (g n : ℕ), 3 ≤ n → ∀ (F : SFam g n (zetaAway n)) (φ : InvFun ℤ), IsPolFan id g φ → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), SharpOver F W ρ.P u → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (D : GlobalTheory.EffCartierData M.Z) (ι : ℕ), (∀ z ∈ D.idealSheaf.support, z ∉ V) → (∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (γ : Ω →+* FractionRing T.V), jK T.V ≫ ξ = spMap γ ≫ M.pt → T.y = spMap γ ≫ spMap S.R.val.toRingHom ≫ u → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a}) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M V v (𝟙 F.X) T ξ → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.β ∧ idlAlong D.idealSheaf ξ = Ideal.span {T.ϖ ^ a} := by
  intro g n hn F φ hφ W hW o' Ω _ _ _ _ S ρ u hu M U₀ EE FinalForm hU V v hv D ι hD hgen T ξ hT
  haveI : CharZero Ω := ArithBase.char o'
  haveI : IsDedekindDomain o' := ArithBase.ded Ω
  haveI := M.lft
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨R, _, _, _, j, Λ, _, p, c, hR, hj, hc, hper⟩ :=
    GlobalTheory.T.thetaModel_point_lattice_periods_traits g n _ _ F W hW o' Ω S ρ u hu M U₀ EE FinalForm hU V v hv (ξ (closedPoint T.V))
  haveI := hR.1.1
  haveI := hR.2
  obtain ⟨jinj, jloc, jext⟩ := isCpl_props hj
  obtain ⟨ψ, ψloc, hψ⟩ := jext T.V T.complete (Scheme.stalkClosedPointTo ξ).hom inferInstance
  have hξ : spMap (ψ.comp j) ≫ M.Z.fromSpecStalk (ξ (closedPoint T.V)) = ξ := by
    rw [hψ]
    exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  obtain ⟨d, hd⟩ : ∃ d, FinalTheorems.stalkId D.idealSheaf (ξ (closedPoint T.V)) = Ideal.span {d} := by
    obtain ⟨i, hi⟩ := D.exists_mem (ξ (closedPoint T.V))
    exact ⟨_, D.stalkId_idealSheaf i _ hi⟩
  have hid : idlAlong D.idealSheaf ξ = Ideal.span {ψ (j d)} := by
    rw [idlAlong, hd, Ideal.map_span, Set.image_singleton, ← hψ]
    rfl
  obtain ⟨ξ₀, hξ₀, hξ₀'⟩ := hT
  have hmem : (jK T.V ≫ ξ) (closedPoint (FractionRing T.V)) ∈ V := by
    rw [← hξ₀]
    exact (ξ₀ (closedPoint (FractionRing T.V))).2
  have hne := idlAlong_ne_bot D.idealSheaf ξ fun h => hD _ h hmem
  obtain ⟨a, ha⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne T.irr
  refine ⟨a, ?_, ha⟩
  have hda : Associated (ψ (j d)) (T.ϖ ^ a) := Ideal.span_singleton_eq_span_singleton.1 (hid.symm.trans ha)
  obtain ⟨e, he⟩ := hper T ψ ψloc (by rw [hξ]; exact ⟨ξ₀, hξ₀, hξ₀'⟩)
  choose k hk hk' using he
  haveI := T.D.toPre.finX
  obtain ⟨N, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := T.D.toPre.X)
  obtain ⟨A, _, _, _, ϖ', ψ', m, m', k', hA, hϖ', ψ'inj, ψ'loc, hm, hm', hk''⟩ :=
    GlobalTheory.T.exists_complete_dvr_with_proportional_valuations R T.V T.ϖ T.irr ψ ψloc (Option (Fin N × Fin N))
      (fun i => i.elim (j d) fun ii => p (e.symm (b ii.1 + b ii.2)))
      (fun i => i.elim a fun ii => k (e.symm (b ii.1 + b ii.2)))
      (by rintro (_ | ii); exacts [hda, hk' _])
  obtain ⟨T', f, γ, finj, floc, -, hγ, hy⟩ := GlobalTheory.T.exists_trait_moduli_of_stalk_completeDVR g n _ _ F o' Ω M (spMap S.R.val.toRingHom ≫ u)
    (ξ (closedPoint T.V)) A hA (ψ'.comp j) (ψ'inj.comp jinj)
  have hrange : Set.range M.pt ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact (M.pt_specializes w _).mem_open V.isOpen hmem
  have hx₀ := IsOpenImmersion.lift_fac V.ι M.pt hrange
  obtain ⟨e', he'⟩ := hper T' (f.comp ψ') inferInstance
    ⟨spMap γ ≫ IsOpenImmersion.lift V.ι M.pt hrange, by rw [Category.assoc, hx₀]; exact hγ.symm,
      by rw [Category.comp_id, Category.assoc, hv _ hx₀, hy]⟩
  obtain ⟨r, hr⟩ := IsDiscreteValuationRing.associated_pow_irreducible
    ((map_ne_zero_iff f finj).2 hϖ'.ne_zero) T'.irr
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hr
    exact hϖ'.not_isUnit ((isUnit_map_iff f ϖ').1 (associated_one_iff_isUnit.1 hr))
  have hpow : ∀ {x : A} {l : ℕ}, Associated x (ϖ' ^ l) → Associated (f x) (T'.ϖ ^ (r * l)) := by
    intro x l h
    have h1 := h.map f
    rw [map_pow] at h1
    rw [pow_mul]
    exact h1.trans hr.pow_pow
  obtain ⟨a', ha', hid'⟩ := hgen T' _ γ hγ hy
  rw [GlobalTheory.TraitStalk.idlAlong_spMap_fromSpecStalk _ _ _ _ _ inferInstance, hd, Ideal.map_span,
    Set.image_singleton, Ideal.span_singleton_eq_span_singleton] at hid'
  have h0 := hk'' none
  have ea : a' = r * k' none := pow_exp_eq T'.irr (hid'.symm.trans (hpow h0.1))
  have h02 : m * k' none = m' * a := h0.2
  let E := e.symm.trans e'
  have hz := form_eq_zero ((m : ℤ) • pull E.toIntLinearEquiv.toLinearMap T'.β - ((m' * r : ℕ) : ℤ) • T.β)
    (fun x y => by
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, pull_apply]
      rw [T.symm x y, T'.symm]) b hb (fun i i' => by
      obtain ⟨l, hl, hl'⟩ := he' (e.symm (b i + b i'))
      obtain ⟨h1, h2⟩ := hk'' (some (i, i'))
      have h3 : l = r * k' (some (i, i')) := pow_exp_eq T'.irr (hl'.symm.trans (hpow h1))
      have h4 := hk (e.symm (b i + b i'))
      rw [e.apply_symm_apply] at h4
      have h5 : (m : ℤ) * k' (some (i, i')) = m' * k (e.symm (b i + b i')) := by exact_mod_cast h2
      have hc0 : (c : ℤ) ≠ 0 := by omega
      change (m : ℤ) * T'.β (e' (e.symm (b i + b i'))) (e' (e.symm (b i + b i'))) -
        ((m' * r : ℕ) : ℤ) * T.β (b i + b i') (b i + b i') = 0
      refine mul_left_cancel₀ hc0 ?_
      rw [h3] at hl
      push_cast at hl ⊢
      linear_combination (-(m : ℤ)) * hl + r * h5 + m' * r * h4)
  have hev := evalZ_prop (by omega) hφ T T' E m (m' * r) fun x y =>
    sub_eq_zero.1 (congrArg (fun B : LinearMap.BilinForm ℤ T.D.toPre.X => B x y) hz)
  have h02' : (m : ℝ) * k' none = m' * a := by exact_mod_cast h02
  have hmr : ((m' : ℝ) * r) ≠ 0 := by
    have : m' ≠ 0 := by omega
    positivity
  refine mul_left_cancel₀ hmr ?_
  rw [ea] at ha'
  push_cast at ha' hev
  linear_combination (-(r : ℝ)) * h02' + m * ha' + ι * hev

end GlobalTheory.Poinc.Extend
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem traitLabels : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (u' : Sp S.R ⟶ F.X), IsDiagEnd F W ρ.P u' ε → ∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (T : Trait F) (ι : FractionRing T.V →+* PadicAlgCl p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap T.V (FractionRing T.V))) → spMap y₀ ≫ u' = spMap ι ≫ T.y → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (u : ρ.UTest p y₀) (l : u.Lab) (j : u.D.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ χ, l.q χ = -Real.log ‖ι (algebraMap T.V (FractionRing T.V) T.ϖ)‖ * ((qW W T.β (j χ) : ℤ) : ℝ)) ∧ ∀ (m : ℕ) (pk pk' : QkPt u.D.toPre (PadicAlgCl p) m) (x x' : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk x → QkToAkU u.U.toUnifPre (PadicAlgCl p) m pk' x' → x'.left ≫ u.φ = x.left ≫ u.φ ≫ (ε E).left → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b) := by
  intro g n F W hW o Ω _ _ _ _ S ρ ε u' hD p _ y₀ T ι hι hsp hint
  obtain ⟨T', ι', yK, e, k, hι', hfac, hy', hϖ, hβ⟩ := GlobalTheory.T.exists_trait_finiteExtension_classicalPoint_factors g n F o Ω S u' p y₀ T ι hι hsp
  obtain ⟨A, φ, cart, lb, εA, hDA, huniq⟩ := GlobalTheory.T.exists_pullback_eighth_power_endomorphisms_field_point g n F W S.R ρ.P ε u' hD (FractionRing T'.V) yK
  rw [hy'] at hDA
  obtain ⟨G', _, _, hsemi, D', U', j', hpsi, hcong⟩ := GlobalTheory.T.eighthPower_trait_uniformisation_lattice_pow_eight g n F W hW T' A εA hDA
  letI : Algebra (FractionRing T'.V) (PadicAlgCl p) := ι'.toAlgebra
  let u : ρ.UTest p y₀ := { V := T'.V, complete := T'.complete, norm_le := hι', yK := yK, fac := hfac, A := A, φ := φ, cart := cart, lb := lb, G := G', semi := hsemi, D := D', U := U' }
  obtain ⟨l⟩ := GlobalTheory.ZH.labels_exist GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2 GlobalTheory.ZH.uTors_closed o Ω S ρ p y₀ u hint
  let jj : u.D.toPre.X ≃+ (Fin 8 → T.D.toPre.X) := j'.trans (AddEquiv.piCongrRight fun _ => e)
  refine ⟨u, l, jj, ?_, ?_⟩
  · intro χ

    obtain ⟨v, hv⟩ := hpsi χ
    obtain ⟨jc, hjc, hval⟩ := GlobalTheory.T.psi_value_fractionRing_of_psiCoord T'.V D'.toPre χ _ hv
    have hq := l.q_eq χ jc hjc
    change ‖algebraMap (FractionRing T'.V) (PadicAlgCl p) (valF (𝟙 (Sp (FractionRing T'.V))) _ ((D'.toPre.psi χ).s jc).val)‖ = _ at hq
    rw [hval, RingHom.algebraMap_toAlgebra] at hq

    have hunit : ‖ι' (algebraMap T'.V _ (v : T'.V))‖ = 1 := by
      have h1 : ‖ι' (algebraMap T'.V _ (v : T'.V))‖ ≤ 1 := (hι' _).2 ⟨_, rfl⟩
      have h2 : ‖ι' (algebraMap T'.V _ ((v⁻¹ : T'.Vˣ) : T'.V))‖ ≤ 1 := (hι' _).2 ⟨_, rfl⟩
      have h3 : ‖ι' (algebraMap T'.V _ (v : T'.V))‖ * ‖ι' (algebraMap T'.V _ ((v⁻¹ : T'.Vˣ) : T'.V))‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
      nlinarith [norm_nonneg (ι' (algebraMap T'.V _ (v : T'.V))), norm_nonneg (ι' (algebraMap T'.V _ ((v⁻¹ : T'.Vˣ) : T'.V)))]
    set a := ‖ι' (algebraMap T'.V _ T'.ϖ)‖ with ha
    have hq0 : 0 ≤ qW W T'.β (j' χ) :=
      qW_nonneg_of_posW W hW.1 T'.β T'.symm (GlobalTheory.Poinc.Basic₂.trait_nonneg T') (j' χ)
    have hsc : qW W T'.β (j' χ) = (k : ℤ) * qW W T.β (jj χ) := by
      simp only [qW, hβ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      simp only [jj, AddEquiv.trans_apply, AddEquiv.piCongrRight_apply]
      ring
    rw [map_mul, map_mul, norm_mul, hunit, one_mul, map_pow, map_pow, norm_pow] at hq
    rw [← ha] at hq
    have hN : ((qW W T'.β (j' χ)).toNat : ℝ) = ((k : ℤ) : ℝ) * (qW W T.β (jj χ) : ℝ) := by
      rw [← Int.cast_mul, ← hsc]
      exact_mod_cast Int.toNat_of_nonneg hq0
    have hapos : 0 < a := by
      rw [ha, norm_pos_iff]
      intro h0
      have : algebraMap T'.V (FractionRing T'.V) T'.ϖ = 0 := ι'.injective (by rw [h0, map_zero])
      exact T'.irr.ne_zero (IsFractionRing.injective T'.V (FractionRing T'.V) (by rw [this, map_zero]))
    have hl : -l.q χ = ((qW W T'.β (j' χ)).toNat : ℝ) * Real.log a := by
      rw [← Real.log_pow, hq, Real.log_exp]
    rw [hϖ, Real.log_pow]
    rw [hN] at hl
    push_cast at hl ⊢
    linarith
  · intro m pk pk' x x' E hm h1 h2 hx
    have hc := hcong (PadicAlgCl p) m pk pk' x x' E hm h1 h2 (huniq _ x x' E hx)
    obtain ⟨w, hw⟩ := hc
    refine ⟨fun a => e (w a), ?_⟩
    funext a
    have := congrFun hw a
    simp only [jj, AddEquiv.trans_apply, AddEquiv.piCongrRight_apply, Pi.add_apply, Pi.smul_apply, Finset.sum_apply] at this ⊢

    rw [this, map_add (f := _), map_sum, map_nsmul]
    simp [map_zsmul]

end GlobalTheory.Poinc
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8

theorem GlobalTheory.Poinc.Sep.sharpRef_equivariant_of_unif_pow : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ρ : V →+* V₁), IsCN V₁ → Function.Injective ρ → ρ.Finite → ∀ (D₀ : DegData V₁ (maximalIdeal V₁)) (e₀ : D₀.toPre.X ≃+ Q.X), Refines Q ρ D₀.toPre e₀ → ∀ (G₀ : Over (Sp V₁)) [GrpObj G₀] [IsCommMonObj G₀] (A₀ : PolAV (Sp (FractionRing V₁))) (U₀ : Unif (maximalIdeal V₁) D₀ A₀ G₀) (y : Sp (FractionRing V₁) ⟶ F.X) (α : A₀.A.left ⟶ F.univ.A.left) (α₂ : (G2 A₀.A).left ⟶ (G2 F.univ.A).left), IsSemiAbelian G₀ → IsGrpPullback A₀.A F.univ.A y α → IsSquare α α₂ → LBIso (abelian₂ A₀.A A₀.L) (F.univ.P.pull α₂) → ∀ (P : PolAV (Sp (FractionRing V₁))) (c : SiegPre g n ζ (y ≫ F.s)) (φc : c.A.left ⟶ F.univ.A.left) (φ₂ : (G2 c.A).left ⟶ (G2 F.univ.A).left), IsGrpPullback c.A F.univ.A y φc → IsSquare φc φ₂ → LBIso c.P (F.univ.P.pull φ₂) → (∀ a, (c.lev a).left ≫ φc = y ≫ (F.univ.lev a).left) → ∀ pr : Fin 8 → (P.A ⟶ c.A), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing V₁))) (y' : Fin 8 → (T' ⟶ c.A)), ∃! x : T' ⟶ P.A, ∀ a, x ≫ pr a = y' a) → LBIso P.L (LB.LinComb c.P (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (G : Over (Sp V₁)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V₁ (maximalIdeal V₁)) (U : Unif (maximalIdeal V₁) D P G) (q : Fin 8 → (G ⟶ G₀)), (∀ u, IsMonHom (q u)) → (∀ (T' : Over (Sp V₁)) (y' : Fin 8 → (T' ⟶ G₀)), ∃! x : T' ⟶ G, ∀ u, x ≫ q u = y' u) → (∀ u, ((Over.pullback (jK V₁)).map (q u) ≫ U₀.gen.hom).left ≫ α = (U.gen.hom ≫ pr u).left ≫ φc) → ∃ e : (Fin 8 → Q.X) ≃+ D.toPre.X, SharpRef W Q ρ D.toPre e ∧ ∀ a a' : Matrix (Fin 8) (Fin 8) ℤ, (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ E : EndU U.toUnifPre, (∀ u, E.aG ≫ q u = (List.ofFn fun v => q v ^ a u v).prod) → ∀ mu, E.h (e mu) = e fun u => ∑ v, a' u v • mu v := by
  intro g n o _ ζ F W hW V _ _ _ Q V₁ _ _ _ ρ hCN hinj hfin D₀ e₀ hR G₀ _ _ A₀ U₀ y α α₂ hsa hpb hsq hlb P cS φc φ₂ hpbc hsqc hlbc hlev pr hpr hpru hPL G _ _ hG D U q hq hqu hqc
  obtain ⟨ch, hch, hbij⟩ := GlobalTheory.T.characters_eightfold_product_eq_eighthPower V₁ hCN D₀ A₀ G₀ hsa U₀ D P G hG U q hq hqu
  let act : Matrix (Fin 8) (Fin 8) ℤ → (Fin 8 → Q.X) → (Fin 8 → Q.X) := fun N mu u => ∑ v, N u v • mu v
  have hact : ∀ N N' mu, act N (act N' mu) = act (N * N') mu := by
    intro N N' mu
    funext u
    simp only [act, Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, mul_smul]
    exact Finset.sum_comm
  have hone : ∀ mu, act 1 mu = mu := by
    intro mu
    funext u
    simp [act, Matrix.one_apply]
  have hdet : IsUnit (W + W.transpose).det := by rw [hW.2]; exact isUnit_one
  have hM1 : (W + W.transpose) * (W + W.transpose)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hM2 : (W + W.transpose)⁻¹ * (W + W.transpose) = 1 := Matrix.nonsing_inv_mul _ hdet
  have hactadd : ∀ N mu mu', act N (mu + mu') = act N mu + act N mu' := by
    intro N mu mu'
    funext u
    simp [act, smul_add, Finset.sum_add_distrib]
  let f : (Fin 8 → Q.X) →+ D.toPre.X :=
    { toFun := fun mu => ∑ u, ch u (e₀.symm (act (W + W.transpose) mu u))
      map_zero' := by
        have : act (W + W.transpose) 0 = 0 := by funext u; simp [act]
        simp [this]
      map_add' := by
        intro mu mu'
        simp only [hactadd, Pi.add_apply, map_add (f := _), Finset.sum_add_distrib] }
  have hfb : Function.Bijective f := by
    have hA : Function.Bijective (act (W + W.transpose)) := by
      refine ⟨fun x y hxy => ?_, fun x => ⟨act (W + W.transpose)⁻¹ x, by rw [hact, hM1, hone]⟩⟩
      have := congrArg (act (W + W.transpose)⁻¹) hxy
      rwa [hact, hact, hM2, hone, hone] at this
    have hE : Function.Bijective (fun x : Fin 8 → Q.X => fun u => e₀.symm (x u)) := by
      refine ⟨fun x y hxy => ?_, fun x => ⟨fun u => e₀ (x u), by funext u; simp⟩⟩
      funext u
      exact e₀.symm.injective (congrFun hxy u)
    exact hbij.comp (hE.comp hA)
  let e : (Fin 8 → Q.X) ≃+ D.toPre.X := AddEquiv.ofBijective f hfb
  refine ⟨e, GlobalTheory.T.degenerationData_eighthPower_via_characterMaps g n o ζ F W hW V Q V₁ ρ hCN hinj hfin D₀ e₀ hR G₀ A₀ U₀ y α α₂ hsa hpb hsq hlb P cS φc φ₂ hpbc hsqc hlbc hlev pr hpr hpru hPL G hG D U q hq hqu hqc ch hch e (fun mu => rfl), ?_⟩
  intro a a' hM E hE mu
  have hEc := GlobalTheory.T.uniformisation_endomorphism_closedFibreTorus_characterMap V₁ hCN D P G hG U E
  have key := GlobalTheory.T.characterMap_of_integral_matrix_action V₁ hCN D₀ A₀ G₀ hsa U₀ D P G hG U q hq ch hch a E.aG E.h E.homG hEc hE
  show E.h (f mu) = f (act a' mu)

  simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_sum, key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_

  simp only [← map_zsmul, ← map_sum]
  congr 2
  have h3 : act (W + W.transpose) (act a' mu) = act a.transpose (act (W + W.transpose) mu) := by
    rw [hact, hact, hM]
  rw [h3]
  simp [act, Matrix.transpose_apply]
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.polarisedAbelianPart_fibre_conjugate_iso_mumford : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ mu c c', IsUnit (u mu c') → ∃ r ∈ k₀, ev (u mu c) = r * ev (u mu c')) → ∀ (σ : K ≃+* K), (∀ r ∈ k₀, σ r = r) → ∀ (a : Q.X) (p : Sp K ⟶ ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left), p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) = spMap (ev.comp ρ) ≫ (Q.c a).left → p ≫ pullback.snd Q.B.hom (spMap (ev.comp ρ)) = 𝟙 _ → ∃ (f : ((Over.pullback (spMap (ev.comp ρ))).obj Q.B).left ⟶ ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B).left) (f₂ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left), IsGrpPullback ((Over.pullback (spMap (ev.comp ρ))).obj Q.B) ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B) (𝟙 _) f ∧ IsSquare f f₂ ∧ (∀ (ψ₀ : (G2 ((Over.pullback (spMap (ev.comp ρ))).obj Q.B)).left ⟶ (G2 Q.B).left) (ψσ : (G2 ((Over.pullback (spMap (σ.toRingHom.comp (ev.comp ρ)))).obj Q.B)).left ⟶ (G2 Q.B).left), IsSquare (pullback.fst Q.B.hom (spMap (ev.comp ρ))) ψ₀ → IsSquare (pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ)))) ψσ → LBIso ((abelian₂ Q.B Q.M.L).pull ψ₀) ((abelian₂ Q.B Q.M.L).pull (f₂ ≫ ψσ))) ∧ p ≫ f ≫ pullback.fst Q.B.hom (spMap (σ.toRingHom.comp (ev.comp ρ))) = spMap σ.toRingHom ≫ p ≫ pullback.fst Q.B.hom (spMap (ev.comp ρ)) := by
  first | exact @GlobalTheory.Poinc.Sep.conj_fibre_core | exact GlobalTheory.Poinc.Sep.conj_fibre_core | (intros; apply GlobalTheory.Poinc.Sep.conj_fibre_core <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_thetaSection_normalised_unit_at_traits : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ Φ : IntFam (maximalIdeal R) D.toPre (m ^ 2) → SecK C.P.L.L C.α (m ^ 2), (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, ∀ F, T.Exp 1 u (Φ F) F) → ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ θ : SecK C.P.L.L C.α 1, ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W), ∃ u : Wˣ, T.Exp 1 u θ F₁ := by
  first | exact @GlobalTheory.Mum.exists_theta_unit_at_traits | exact GlobalTheory.Mum.exists_theta_unit_at_traits | (intros; apply GlobalTheory.Mum.exists_theta_unit_at_traits <;> assumption)
end
