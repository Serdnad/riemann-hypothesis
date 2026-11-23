module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle070
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3424
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFibrePowerPointLiftsToLowerBase
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle075
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassSumFunctionsThetaMembers
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3425
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2449
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle035
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2929
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3289
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle344
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle599
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3427
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle067
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle546

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.idempotentFactor_uniformised_of_degData_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (G₁ : Over (Sp R₁)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (U₁ : Unif (maximalIdeal R₁) D₁ A₁ G₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G' U'.LG.L).pull (β₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) := by
  first | exact @GlobalTheory.Mum.factor_unif | exact GlobalTheory.Mum.factor_unif | (intros; apply GlobalTheory.Mum.factor_unif <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.siegelFibrePower_point_lifts_to_lower_base : ∀ (n : ℕ), 3 ≤ n → Odd n → ∀ (h : ℕ) (F : SFam h n (zetaAway n)) (r : ℕ) (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsDiscreteValuationRing V₁ → ∀ (b₁ : cycAway n →+* V₁) (v : Sp V₁ ⟶ (GlobalTheory.LowChart.powA F r).left) (hs : v ≫ GlobalTheory.LowChart.toO F r = spMap b₁), ∃ (L : LowBase (zetaAway n) n) (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V₁ →+* V') (κ : L.W →+* V') (e : (Fin L.T.r → ℤ) ≃+ (Fin r → ℤ)), L.h = h ∧ IsCN V' ∧ IsDiscreteValuationRing V' ∧ Function.Injective f ∧ f.Finite ∧ IsLocalHom f ∧ IsLocalHom κ ∧ κ.comp L.T.b = f.comp b₁ ∧ ∃ (B' : Over (Sp V')) (_ : GrpObj B') (β' : B'.left ⟶ (GlobalTheory.LowChart.siegAt F v _ hs).A.left) (β'' : B'.left ⟶ L.T.B.left) (β₂ : (G2 B').left ⟶ (G2 (GlobalTheory.LowChart.siegAt F v _ hs).A).left) (β₂' : (G2 B').left ⟶ (G2 L.T.B).left), IsGrpPullback B' (GlobalTheory.LowChart.siegAt F v _ hs).A (spMap f) β' ∧ IsGrpPullback B' L.T.B (spMap κ) β'' ∧ IsSquare β' β₂ ∧ IsSquare β'' β₂' ∧ LBIso ((GlobalTheory.LowChart.siegAt F v _ hs).P.pull β₂) ((abelian₂ L.T.B L.T.M.L).pull β₂') ∧ ∀ a : Fin L.T.r → ℤ, ∃ x : Sp V' ⟶ B'.left, x ≫ B'.hom = 𝟙 _ ∧ x ≫ β' = spMap f ≫ (GlobalTheory.LowChart.cAt F v _ hs ((n : ℤ) • e a)).left ∧ x ≫ β'' = spMap κ ≫ (L.T.c₀ ((n : ℤ) • a)).left := by
  first | exact @GlobalTheory.LowLift.main | exact GlobalTheory.LowLift.main | (intros; apply GlobalTheory.LowLift.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

theorem _root_.GlobalTheory.T.exists_finite_theta_tuples_least_orders_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), ∃ (ι : ℕ) (K : Type) (_ : Fintype K) (Jk : K → Type) (_ : ∀ k, Fintype (Jk k)) (t : ∀ k, Jk k → X₁.Ω₁), 1 ≤ ι ∧ (∀ k j, t k j ≠ 0) ∧ ∀ (M : RatModel X₁.o₁ X₁.Ω₁) (U₀ : M.Z.Opens) (EE : M.Lat X₁.S.J) (out : ZHOut X₁.ρ M U₀ EE), X₁.S.admitted M U₀ → X₁.S.IsEE M U₀ EE → ∀ x : M.Z, ∃ k, ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ M.Z), (∃ ξ₀ : Sp (FractionRing T.V) ⟶ U₀.toScheme, ξ₀ ≫ U₀.ι = jK T.V ≫ ξ ∧ X₁.Lies (ξ₀ ≫ out.u₀) T.y) → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T.be ∧ (∀ j, UOrdGe M T ξ (t k j) a) ∧ ∃ j, UOrdEq M T ξ (t k j) a := by
  first | exact @GlobalTheory.UPoinc.exists_uLocTuples_theta | exact GlobalTheory.UPoinc.exists_uLocTuples_theta | (intros; apply GlobalTheory.UPoinc.exists_uLocTuples_theta <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_semiAbelian_descent_of_toricCharts_corrected_sep : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → ∀ (tF : SAB H (Xo.XF c)), SABMap tF Xo.univ.t (pullback.fst _ _) → ∃ (G : Over S) (_ : GrpObj G) (_ : IsCommMonObj G) (e : tF.G.left ⟶ G.left), IsSemiAbelian G ∧ IsGrpPullback tF.G G j e ∧ abLocus G = Set.range j ∧ ∀ {k : Type} [Field k] {m n : ℕ} (C : MonoFam Xo c φ (ChartRing k m n)), IsTaut C → ∀ ξ : Sp (ChartRing k m n) ⟶ S, C.y ≫ j = jK _ ≫ ξ → ∀ (tK : SAB H (Sp (FractionRing (ChartRing k m n)))) (a : SABMap tK C.t (jK _)) (b : SABMap tK tF C.y), ∃ πC : C.t.G.left ⟶ G.left, IsGrpPullback C.t.G G ξ πC ∧ a.φ ≫ πC = b.φ ≫ e := by
  first | exact @GlobalTheory.UChartDesc.exists_semiAbelian_of_charts_sepB | exact GlobalTheory.UChartDesc.exists_semiAbelian_of_charts_sepB | (intros; apply GlobalTheory.UChartDesc.exists_semiAbelian_of_charts_sepB <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.fourierTermSystem_exact_of_geometric_uniformisation : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : O → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam) (Φ : VPre bar q W (X₁.M.Z.presheaf.stalk z₁)) (lab : Φ.Q → X₁.S.Gam), GlobalTheory.GSep.IsGeo X₁ z₁ act x₀ Φ lab → Φ.Exact (X₁.S.r * X₁.S.N) := by
  first | exact @GlobalTheory.GSep.ExactSums.exact_of_isGeo | exact GlobalTheory.GSep.ExactSums.exact_of_isGeo | (intros; apply GlobalTheory.GSep.ExactSums.exact_of_isGeo <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_class_sum_functions_theta_members : ∀ (I : Type) (X₁ : GlobalTheory.GSep.GSet) (z₁ : X₁.M.Z) (act : I → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∃ f : X₁.S.Gam → X₁.S.Gam → X₁.Ω₁, (∀ a b, ∀ w : X₁.M.Z, X₁.M.Div X₁.S.th x₀ w → f a b ∈ X₁.M.O w) ∧ (∀ a a' b, a - a' ∈ X₁.S.HH X₁.M z₁ → f a b = f a' b) ∧ ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (t : X → V) (δ : I → X → X) (𝔪 : GlobalTheory.GSep.GMem X₁ z₁ act V ev X t δ) (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : X → C → V, 𝔪.Terms x₀ lab T → ∀ (c : C) (a : X₁.S.Gam) (κ : X), 𝔪.YY a κ → ∀ h : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ h = f a (lab c) → SumI (maximalIdeal V) (fun nu : X => T (κ + (X₁.S.r * X₁.S.N) • nu) c) (ev h) := by
  first | exact @GlobalTheory.GSep.ClassSumFun.exists_classSum_fun | exact GlobalTheory.GSep.ClassSumFun.exists_classSum_fun | (intros; apply GlobalTheory.GSep.ClassSumFun.exists_classSum_fun <;> assumption)
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

namespace GlobalTheory.LogKSChart

theorem exists_derivation_intAlgebra {A : Type} [CommRing A] (inst : Algebra ℤ A) (D : @Derivation ℤ A A _ _ _ inst _ _) :
    ∃ D' : @Derivation ℤ A A _ _ _ (Ring.toIntAlgebra A) _ _, ⇑D' = ⇑D := by
  obtain rfl : inst = Ring.toIntAlgebra A := Subsingleton.elim _ _
  exact ⟨D, rfl⟩



theorem exists_isKS_of_logDer : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ D : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ i, D (bdParam k m d i) ∈ Ideal.span {bdParam k m d i}) → ∃ Θ, IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab n v hv hcomb D hD
  letI := H.starRing
  haveI : IsAdicComplete (maximalIdeal k) k := by rw [maximalIdeal_eq_bot]; infer_instance
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) :=
    GlobalTheory.PlaceInt.isAdicComplete_mvPowerSeries_finite (V := k) _
  obtain ⟨Y⟩ : Nonempty (Ray P.oD) := inferInstance
  obtain ⟨n', vY, dd, hdd⟩ := GlobalTheory.T.exists_invariant_tangent_basis_raynaudExtension (ChartRing k m d) P.D.toPre (𝓞 E) P.oD Y
  have hne : ∀ i, bdParam k m d i ≠ 0 := fun i h => by
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1)) h
    simp [MvPowerSeries.coeff_X] at this
  obtain ⟨D', hD'⟩ := exists_derivation_intAlgebra _ D
  obtain ⟨h, hb, hdef⟩ := GlobalTheory.T.exists_torusInvariant_heatOperator_commuting_periods (ChartRing k m d) P.D (𝓞 E) P.oD Y n' vY dd hdd m (bdParam k m d) gam hmon hne D'
    (by rw [hD']; exact hD)
  revert h
  rw [hD']
  intro h hb hdef
  obtain ⟨v', hv', hks⟩ := GlobalTheory.T.exists_kodairaSpencer_chart_of_heat_operators E H k m d t P gam hmon hli hab (𝓞 E) P.oD Y n' vY dd hdd D hD h hb hdef
  choose B hB using fun a => (hcomb (v' a) (hv' a)).exists
  exact ⟨_, GlobalTheory.KSFrameChange.isKS_frame_change E H (Sp (ChartRing k m d)) t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) n' n v' v (Matrix.of B) (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) _ hv' hv hB hks⟩

end GlobalTheory.LogKSChart
end
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.homotopyInvariance_tateTwist_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Eqv _ (spMap (Polynomial.C : A →+* Polynomial A)) (tw q i) := by
  first | (exact @GlobalTheory.homotopyInvariance_strictlyHenselian) | (exact GlobalTheory.homotopyInvariance_strictlyHenselian) | (intros; apply GlobalTheory.homotopyInvariance_strictlyHenselian  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.GSumCls

theorem congMod_iff {X J : Type} [AddCommGroup X] (m : ℕ) (u v : J → X) :
    CongMod m u v ↔ ∀ i, CongMod m (u i) (v i) := by
  constructor
  · rintro ⟨w, hw⟩ i
    exact ⟨w i, by rw [hw]; rfl⟩
  · intro h
    choose w hw using h
    exact ⟨w, funext fun i => by rw [hw i]; rfl⟩

theorem norm_val_root_mul {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} (hM : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z)
    {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {z : M.Z} (hy : y (cPt p) = z) {u x : Ω} {k : ℕ} (hk : 0 < k)
    (hu : u ^ k = 1) (hx : x ∈ M.O z) : ‖M.val (gPt p ≫ y) (u * x)‖ = ‖M.val (gPt p ≫ y) x‖ := by
  haveI := RatModel.isIntegrallyClosed_O hM z
  have hint : IsIntegral (M.O z) u := ⟨_, Polynomial.monic_X_pow_sub_C (1 : M.O z) hk.ne', by simp [hu]⟩
  obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  have hmem : u ∈ M.O z := hv ▸ v.2
  have hs := RatModel.gPt_specializes hy
  have h1 : (⟨u, hmem⟩ : M.O z) ^ k = 1 := Subtype.ext hu
  have h2 : M.val (gPt p ≫ y) u ^ k = 1 := by
    have := congrArg (RatModel.valHomOf (gPt p ≫ y) z hs) h1
    rwa [map_pow, map_one] at this
  have h3 : ‖M.val (gPt p ≫ y) u‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 (by rw [← norm_pow, h2, norm_one])
  rw [RatModel.val_mul hs hmem hx, norm_mul, h3, one_mul]

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem onto_of_isLab {X : Setup F W i} {ε} {p : ℕ} [Fact p.Prime] {z : X.M.Z} {c : CTrait X p z} {yy}
    (h : IsLab X ε c yy) (ν : Fin 8 → c.T.D.toPre.X) : ∃ a, yy a = QuotientAddGroup.mk ν := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, -, y₀, -, u, l, j, -, hyy, -⟩ := h
  obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk (j.symm ν))
  exact ⟨a, by simpa using hyy a _ ha⟩

theorem tendsto_of_isLab {X : Setup F W i} {ε} {p : ℕ} [Fact p.Prime] {z : X.M.Z} {c : CTrait X p z} {yy}
    (h : IsLab X ε c yy) :
    Filter.Tendsto (fun ν : Fin 8 → c.T.D.toPre.X => c.sc * (qW W c.T.β ν : ℤ)) Filter.cofinite Filter.atTop := by
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', ε', -, -, -, y₀, -, u, l, j, hq, -⟩ := h
  refine (l.pos.comp j.symm.injective.tendsto_cofinite).congr fun ν => ?_
  rw [Function.comp_apply, hq, AddEquiv.apply_symm_apply]

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (z₂ : D.X.M.Z), D.q z₂ = z₁ → ∃ U : X₁.S.HH X₁.M z₁ → D.X.Ω₁, (∀ κ, ∃ k : ℕ, 0 < k ∧ U κ ^ k = 1) ∧ ∀ (c : CTrait X₁ p z₁) (yy₁ : X₁.S.Gam →+ ModN (X₁.S.r * X₁.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab X₁ ε₁ c yy₁ → ∃ t : (Fin 8 → c.T.D.toPre.X) → X₁.S.HH X₁.M z₁ → PadicAlgCl p, (∀ μ κ, ‖t μ κ‖ ≤ Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ (∀ μ, ∃ κ, ‖t μ κ‖ = Real.exp (-(c.sc * (qW W c.T.β μ : ℤ)))) ∧ ∀ (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y), y (cPt p) = z₂ → ∀ yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X), IsLab D.X D.ε (D.lift c y h) yy → D.Compat yy₁ yy → ∀ a ν κ, yy a = QuotientAddGroup.mk ν → ∀ δ : ℝ, 0 < δ → ∃ S₀ : Finset (Fin 8 → c.T.D.toPre.X), ∀ S : Finset (Fin 8 → c.T.D.toPre.X), (∀ μ ∈ S, ∀ u, CongMod D.m (μ u) (ν u)) → (∀ μ ∈ S₀, (∀ u, CongMod D.m (μ u) (ν u)) → μ ∈ S) → ‖D.X.M.val (gPt p ≫ y) (U κ * GSum.part D z₁ z₂ a κ) - ∑ μ ∈ S, t μ κ‖ ≤ δ := by
  intro g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p _ z₁ z₂ hz
  obtain ⟨U, hU, hgeq⟩ := GlobalTheory.T.thetaWeightPart_value_depends_trait_labels_class g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D z₁ z₂ hz
  refine ⟨U, hU, fun c yy₁ hlab => ?_⟩
  have hs : ∀ χ : Fin 8 → c.T.D.toPre.X, ‖c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ)‖ ^ (qW W c.T.β χ).toNat =
      Real.exp (-(c.sc * (qW W c.T.β χ : ℤ))) := fun χ => by
    have h0 := qW_nonneg_of_posW W X₁.posW c.T.β c.T.symm (Basic₂.trait_nonneg c.T) χ
    rw [← c.exp_neg_sc_mul, ← Int.cast_natCast (R := ℝ), Int.toNat_of_nonneg h0]
  by_cases hex : ∃ y : Sp (OO p) ⟶ D.X.M.Z, y ≫ D.q = c.y ∧ y (cPt p) = z₂
  swap
  · refine ⟨fun μ _ => c.ι (algebraMap c.T.V (FractionRing c.T.V) c.T.ϖ) ^ (qW W c.T.β μ).toNat,
      fun μ _ => by rw [norm_pow, hs], fun μ => ⟨0, by rw [norm_pow, hs]⟩, fun y h hy => (hex ⟨y, h, hy⟩).elim⟩
  obtain ⟨y₀, h₀, hy₀⟩ := hex
  obtain ⟨yy₀, hlab₀, hcomp₀⟩ :=
    GLift.labels_lift g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D p z₁ c yy₁ hlab y₀ h₀
  choose a ha using onto_of_isLab hlab₀
  have hpart : ∀ b κ, GSum.part D z₁ z₂ b κ ∈ D.X.M.O z₂ := fun b κ => by
    rw [GSum.part, Finset.sum_div]
    refine sum_mem fun j _ => ?_
    rw [mul_div_assoc]
    exact mul_mem ((D.X.M.O z₂).algebraMap_mem _)
      (GlobalTheory.T.weightParts_over_dividing_thetaConstant_integral g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D z₁ _ j z₂ hz)
  have hnorm : ∀ b κ, ‖D.X.M.val (gPt p ≫ y₀) (U κ * GSum.part D z₁ z₂ b κ)‖ =
      ‖D.X.M.val (gPt p ≫ y₀) (GSum.part D z₁ z₂ b κ)‖ := fun b κ => by
    obtain ⟨k, hk, hu⟩ := hU κ
    exact norm_val_root_mul (haveI := D.X.normal; GlobalTheory.IsNormalScheme.pred _) hy₀ hk hu (hpart b κ)
  have hsc := c.scale_pos
  obtain ⟨t, ht1, ht2, ht3⟩ := GlobalTheory.T.lattice_class_sums_of_terms_prescribed_norms p (Fin 8 → c.T.D.toPre.X) (X₁.S.HH X₁.M z₁) D.m
    (fun ν => c.sc * (qW W c.T.β ν : ℤ)) _ _ (tendsto_of_isLab hlab) hs
    (fun ν κ => D.X.M.val (gPt p ≫ y₀) (U κ * GSum.part D z₁ z₂ (a ν) κ))
    (fun ν ν' κ h => hgeq p c yy₁ hlab y₀ h₀ hy₀ yy₀ hlab₀ hcomp₀ y₀ h₀ hy₀ yy₀ hlab₀ hcomp₀ _ _ ν ν' κ (ha ν) (ha ν') h)
    (fun ν κ h => by
      rw [hnorm]
      refine GlobalTheory.T.weightPart_least_vector_norm_le_exp g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D z₁ z₂ hz p c yy₁ hlab y₀ h₀ hy₀ yy₀
        hlab₀ hcomp₀ _ ν κ (ha ν) fun χ hχ => ?_
      exact_mod_cast le_of_mul_le_mul_left (h χ hχ) hsc)
    (fun ν h => by
      simp only [hnorm]
      refine GlobalTheory.T.weightPart_unique_least_vector_attains_exp g n F W Z i X₁ hg hn hodd himm he8 hth hproj ε₁ hdiag D z₁ z₂ hz p c yy₁ hlab y₀ h₀ hy₀ yy₀
        hlab₀ hcomp₀ _ ν (ha ν) fun χ hχ hne => ?_
      exact_mod_cast lt_of_mul_lt_mul_left (h χ hχ hne) hsc.le)
  refine ⟨t, ht1, ht2, fun y h hy yy hl hc b ν κ hb δ hδ => ?_⟩
  obtain ⟨S₀, hS₀⟩ := ht3 ν κ δ hδ
  refine ⟨S₀, fun S h1 h2 => ?_⟩
  rw [hgeq p c yy₁ hlab y h hy yy hl hc y₀ h₀ hy₀ yy₀ hlab₀ hcomp₀ b (a ν) ν ν κ hb (ha ν) ⟨0, by simp⟩]
  exact hS₀ S (fun χ hχ => (congMod_iff _ _ _).2 (h1 χ hχ)) fun χ hχ hcg => h2 χ hχ ((congMod_iff _ _ _).1 hcg)

end GlobalTheory.Poinc.GSumCls
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

theorem _root_.GlobalTheory.T.dualNumber_hodge_summand_eq_graph_coordinates : ∀ (k : Type) [Field k] (A₀ : Over (Sp k)) [GrpObj A₀], IsAbelianScheme A₀ → ∀ (f : HdR A₀ →ₗ[k] HdR A₀) (E : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀)), (∃ M : Submodule (TrivSqZeroExt k k) (Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀), IsCompl E M) → (∀ y : HdR A₀, y ∈ Fil A₀ ↔ ∃ e ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ (GlobalTheory.FODef.sqZero k k)) rfl A₀).Corr e y) → (∀ x ∈ Fil A₀, ∃ e ∈ E, ∀ c, e ((GlobalTheory.FODef.constMorV k k A₀).pull c) = TrivSqZeroExt.inl (x c) + TrivSqZeroExt.inr (f x c)) → ∀ e : Crys (divided₂ (GlobalTheory.FODef.sqZero k k)) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) A₀, e ∈ E ↔ (GlobalTheory.HTGlueLie.fstC A₀ e ∈ Fil A₀ ∧ (GlobalTheory.HTGlueLie.sndC A₀ e : HdR A₀) - f (GlobalTheory.HTGlueLie.fstC A₀ e) ∈ Fil A₀) := by
  first | (exact @GlobalTheory.HTGlueLie.fo_summand_coords) | (exact GlobalTheory.HTGlueLie.fo_summand_coords) | (intros; apply GlobalTheory.HTGlueLie.fo_summand_coords  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.laurentKummerCupProduct_bijective_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ i : ℤ, Function.Bijective (gmPhi q A i) := by
  first | (exact @GlobalTheory.EtC.gmPhi_bijective) | (exact GlobalTheory.EtC.gmPhi_bijective) | (intros; apply GlobalTheory.EtC.gmPhi_bijective  <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

theorem _root_.GlobalTheory.T.exists_etaleLevelStructure_at_geometricPoint : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (w0 : Ideal (𝓞 D.F)) (r : ℕ), N.Coprime p → IsEtPlace b w0 → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ l : D.La → (Over.mk x ⟶ o.A), IsEtLevOver o w0 r l := by
  first | (exact @GlobalTheory.UPel.HT.EtLev.exists_etLevOver_geomPt) | (exact GlobalTheory.UPel.HT.EtLev.exists_etLevOver_geomPt) | (intros; apply GlobalTheory.UPel.HT.EtLev.exists_etLevOver_geomPt  <;> assumption)
end
