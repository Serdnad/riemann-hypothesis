module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3130
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorComponentsTorusExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3127
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3161
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3259
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle440
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3256
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle018
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3201
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3258
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3198
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3262
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3263
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2932
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TensBal
open GlobalTheory.TensAct
open ReciprocityTheory.ChartRestriction.G.DVR (cP cPoint_add)

theorem triv_span {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) (hB : D.TauBimult) {c : Vec r →₀ ℤ}
    (hc : c ∈ Submodule.span ℤ (Set.range fun p : Vec r × Vec r × Vec r => theta p.1 p.2.1 p.2.2)) : Triv T c := by
  induction hc using Submodule.span_induction with
  | mem x hx => obtain ⟨p, rfl⟩ := hx; exact GlobalTheory.T.isStronglyTrivial_cubicalThetaFinsupp_tensor R D D' W T hB _ _ _
  | zero => exact GlobalTheory.T.isStronglyTrivialFormalSumTensor_zero R D D' W T
  | add x y _ _ hx hy => exact GlobalTheory.T.isStronglyTrivialFormalSumTensor_add R D D' W T _ _ hx hy
  | smul n x _ hx =>
    induction n using Int.induction_on with
    | zero => rw [zero_smul]; exact GlobalTheory.T.isStronglyTrivialFormalSumTensor_zero R D D' W T
    | succ k ih => rw [add_smul, one_smul]; exact GlobalTheory.T.isStronglyTrivialFormalSumTensor_add R D D' W T _ _ ih hx
    | pred k ih =>
      rw [sub_smul, one_smul, sub_eq_add_neg]
      exact GlobalTheory.T.isStronglyTrivialFormalSumTensor_add R D D' W T _ _ ih (GlobalTheory.T.isStronglyTrivialFormalSumTensor_neg R D D' W T _ hx)

theorem tau_tens {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) {z : (TK R).left} {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') (p q : D'.X) :
    val (D'.tau p q) (𝟙 _) z J' = isoV T.w z J J' (cP D' (TK R) (p + q)).left * qv T z J (p + q) *
      (isoV T.w z J J' (cP D' (TK R) p).left * qv T z J p)⁻¹ *
      (isoV T.w z J J' (cP D' (TK R) q).left * qv T z J q)⁻¹ * (val D'.rigK (𝟙 _) z J')⁻¹ := by
  rw [GlobalTheory.TauBalBox.tau_val D' hJ', T.psi _ z J J' hJ hJ', T.psi _ z J J' hJ hJ', T.psi _ z J J' hJ hJ']
  rfl

theorem tauBal_tens : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (A A' : Matrix (Fin r) (Fin r) ℤ), A.transpose * (W + W.transpose) = (W + W.transpose) * A' → D'.toPre.TauBal (GlobalTheory.TensAct.matAct T A) (GlobalTheory.TensAct.matAct T A') (GlobalTheory.TensAct.latAct T A) (GlobalTheory.TensAct.latAct T A') := by
  intro R _ _ I D D' r W T A A' hA u' hu' hn' y y'
  obtain ⟨Ξ, hΞ, hΞ0, hΞv⟩ := triv_span T D.tau_bimult (GlobalTheory.T.rosatiBalanceFormalSum_mem_span_cubicalTheta W A A' hA)
  refine corr_of_val D'.toPre.P.isLB fun z J' hJ' => ?_
  obtain ⟨J, hJ⟩ := GlobalTheory.BoxFamily.exists_good_at D.toPre.P.isLB z
  have key := GlobalTheory.T.rosatiGenerator_tensorPower_corresponds_formalSum R D.toPre D'.toPre W T A A' u' hu' hn' Ξ hΞ hΞ0 z J J' hJ hJ' y y'
  rw [hΞv z J hJ y y', GlobalTheory.T.rosatiBalanceFormalSum_psiValues_eq_tauProduct R D.toPre D'.toPre W T D.tau_bimult A A' z J hJ y y'] at key
  have pr := prod_ros (matAct T A) (matAct T A') (cP D'.toPre (TK R) y) (cP D'.toPre (TK R) y')
    (isoV T.w z J J')
  have l₁ : cP D'.toPre (TK R) y ≫ matAct T A = cP D'.toPre (TK R) (latAct T A y) := by
    rw [cP, cP, c_lin, Category.assoc]
  have l₂ : cP D'.toPre (TK R) y' ≫ matAct T A' = cP D'.toPre (TK R) (latAct T A' y') := by
    rw [cP, cP, c_lin, Category.assoc]
  rw [l₁, l₂, ← cPoint_add, ← cPoint_add] at pr
  change ∏ a, isoV T.w z J J' (D'.toPre.pt2 y y' ≫ rosatiφ D'.toPre.P.A (matAct T A) (matAct T A') a) ^ rosatiε a = _ at pr
  rw [pr] at key
  rw [val_mul hJ', val_pull hJ', Category.id_comp, tau_tens T hJ hJ', tau_tens T hJ hJ']
  have e0 : rosatiε 0 = 1 := rfl
  have e1 : rosatiε 1 = -1 := rfl
  have e2 : rosatiε 2 = -1 := rfl
  have e3 : rosatiε 3 = -1 := rfl
  have e4 : rosatiε 4 = 1 := rfl
  have e5 : rosatiε 5 = 1 := rfl
  have r0 : rosLat T A A' y y' 0 = latAct T A y + y' := rfl
  have r1 : rosLat T A A' y y' 1 = latAct T A y := rfl
  have r2 : rosLat T A A' y y' 2 = y' := rfl
  have r3 : rosLat T A A' y y' 3 = y + latAct T A' y' := rfl
  have r4 : rosLat T A A' y y' 4 = y := rfl
  have r5 : rosLat T A A' y y' 5 = latAct T A' y' := rfl
  simp only [Fin.prod_univ_six, e0, e1, e2, e3, e4, e5, r0, r1, r2, r3, r4, r5] at key
  apply Additive.ofMul.injective
  have k' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at k' ⊢
  linear_combination (norm := abel) k'

end GlobalTheory.TensBal
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange


theorem _root_.GlobalTheory.T.torsionFrame_value_localUnits_mul_subfield : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A), b ^ N₁ = 1 → DefOver k₀ (spMap ev ≫ b.left ≫ β) →
    ∀ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)),
      (t.IsGen ∧ ∀ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ N₁) (N₁ ^ 2) 1), Normd κ →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
          val t r z J ^ (N₁ ^ 2) * val κ (r ≫ b.left) z J = 1) →
    ∃ c ∈ k₀, (val t (spMap ev) z J).val =
      ((GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (η[D.P.A]).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ b.left)).val * toStk z c := by
  first | exact @GlobalTheory.USep.EvG.frame_ev | exact GlobalTheory.USep.EvG.frame_ev | (intros; apply GlobalTheory.USep.EvG.frame_ev <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange


theorem _root_.GlobalTheory.T.characterValue_mem_localUnits_mul_subfield : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (a : D.X) (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A), b ^ N₁ = 1 → DefOver k₀ (spMap ev ≫ b.left ≫ β) →
    ∀ χ : LB.Gen (LB.LinComb D.P.L ![(D.c a * b).left, (D.c a).left, b.left, (η[D.P.A]).left] DegPre.gtε),
      (χ.IsGen ∧ ∀ (T : Over (Sp V₁)) (z : T.left) J, Good D.P.L z J →
        ∏ i ∈ Finset.range N₁, cubV D.cub z J (toUnit T ≫ D.c a) (toUnit T ≫ b ^ i) (toUnit T ≫ b) = val χ T.hom z J ^ N₁) →
    ∃ c ∈ k₀, (val χ (spMap ev) z J).val =
      (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a * b).left) * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left))⁻¹ * (GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ b.left))⁻¹ *
        GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (η[D.P.A]).left)).val * toStk z c := by
  first | exact @GlobalTheory.USep.EvG.chi_mem | exact GlobalTheory.USep.EvG.chi_mem | (intros; apply GlobalTheory.USep.EvG.chi_mem <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange


theorem _root_.GlobalTheory.T.symmetryGenerator_value_localUnits_mul_subfield : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ a : D.X, ∃ c ∈ k₀, (val D.sym (spMap ev ≫ (D.c a).left) z J).val =
      ((GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c (-a)).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left)).val * toStk z c := by
  first | exact @GlobalTheory.USep.EvG.SymVal.sym_val | exact GlobalTheory.USep.EvG.SymVal.sym_val | (intros; apply GlobalTheory.USep.EvG.SymVal.sym_val <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

theorem _root_.GlobalTheory.T.exists_genericFibre_product_sumPolarisedAbelianVariety : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (A : PolAV (Sp (FractionRing R))) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumPolAV A A₁ A₂ a₁ a₂ → ∃ gen : (Over.pullback (jK R)).obj (G₁ ⊗ G₂) ≅ A.A, IsMonHom gen.hom ∧ gen.hom ≫ a₁ = (Over.pullback (jK R)).map (fst G₁ G₂) ≫ U₁.gen.hom ∧ gen.hom ≫ a₂ = (Over.pullback (jK R)).map (snd G₁ G₂) ≫ U₂.gen.hom ∧ ∀ (L : LB (G₁ ⊗ G₂).left) (wL : LB.Iso L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)), L.IsLB → wL.IsGen → ∃ w : LB.Iso (A.L.pull gen.hom.left) (L.pull (pullback.fst (G₁ ⊗ G₂).hom (jK R))), w.IsGen := by
  first | exact @GlobalTheory.ProdGen.exists_gen_prod | exact GlobalTheory.ProdGen.exists_gen_prod | (intros; apply GlobalTheory.ProdGen.exists_gen_prod <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.mumfordBundle_iso_along_homs_descends_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], AdmBase R (maximalIdeal R) → ∀ (D₁ D₂ : DegData R (maximalIdeal R)) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (f g : G₁ ⟶ G₂) (fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom fB → IsMonHom gB → Over₀ U₁.toUnifPre U₂.toUnifPre f fB → Over₀ U₁.toUnifPre U₂.toUnifPre g gB → LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G₂ U₂.LG.L).pull (lift (fst G₁ G₁ ≫ f) (snd G₁ G₁ ≫ g) : G2 G₁ ⟶ G2 G₂).left) → LBIso (abelian₂ D₁.toPre.P.A D₁.toPre.P.L) ((abelian₂ D₂.toPre.P.A D₂.toPre.P.L).pull (lift (fst D₁.toPre.P.A D₁.toPre.P.A ≫ fB) (snd D₁.toPre.P.A D₁.toPre.P.A ≫ gB) : G2 D₁.toPre.P.A ⟶ G2 D₂.toPre.P.A).left) := by
  first | exact @GlobalTheory.HomMum.lbIso_descends | exact GlobalTheory.HomMum.lbIso_descends | (intros; apply GlobalTheory.HomMum.lbIso_descends <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.crossRelation_hom_gives_expansionTerm_convolution_rel : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (w₁ : W0 U₁.toUnifPre) (w₂ : W0 U₂.toUnifPre), w₁.IsGen → w₂.IsGen → ∀ (j j' : ℕ), 1 ≤ j → 1 ≤ j' → ∀ (t₁ t₂ : SecA A₂ F j) (t₁' t₂' : SecA A₁ F j') s₁ s₂ s₁' s₂', U₂.ExpandsF F j w₂ t₁ s₁ → U₂.ExpandsF F j w₂ t₂ s₂ → U₁.ExpandsF F j' w₁ t₁' s₁' → U₁.ExpandsF F j' w₁ t₂' s₂' → CrossH c t₁ t₂ t₁' t₂' → ∀ (g : GtPtF D₁.toPre F) (g' : GtPtF D₂.toPre F), Act D₁.toPre D₂.toPre b h g g' → ∀ (w : Frm D₂.toPre F j g'.b) (w' : Frm D₁.toPre F j' g.b), w.IsGen → w'.IsGen → ∀ α, SumF I F (fun p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} => coef s₁ g' w p.1.1 * coef s₂' g w' p.1.2 - coef s₂ g' w p.1.1 * coef s₁' g w' p.1.2) 0 := by
  first | exact @GlobalTheory.Mum.MixTwo.main | exact GlobalTheory.Mum.MixTwo.main | (intros; apply GlobalTheory.Mum.MixTwo.main <;> assumption)
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt.Transv

theorem fin_max : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n),
    {𝔮 : Ideal (𝓞 E) | 𝔮.IsMaximal ∧ (n : 𝓞 E) ∈ 𝔮}.Finite :=
  GlobalTheory.T.finite_maximal_ideals_containing_natCast'

theorem exists_sep : ∀ {E : Type} [Field E] [NumberField E] (n : ℕ) (hn : 0 < n) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal),
    ∃ e : 𝓞 E, e - 1 ∈ 𝔭 ∧ ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮 :=
  GlobalTheory.T.exists_one_mod_maximal_mem_other_maximals_over_nat

theorem sup_eq_top : ∀ {E : Type} [Field E] [NumberField E] {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (N : Submodule (𝓞 E) X) (n : ℕ) (hn : 0 < n)
    (h : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → N ⊔ 𝔮 • (⊤ : Submodule (𝓞 E) X) = ⊤),
    N ⊔ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) X) = ⊤ :=
  GlobalTheory.T.sup_smul_top_eq_top_of_forall_maximal_over_nat

theorem exists_ker_vec : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hi : img D y Z' 𝔭 ≠ ⊤),
    ∃ v : Z', y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X) ∧ ∃ ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E, ℓ₀ v ∉ 𝔭 :=
  GlobalTheory.T.exists_vector_mapsInto_ideal_of_not_onto_mod

theorem exists_real_theta : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (𝔭 : Ideal (𝓞 E))
    (h𝔭 : 𝔭.IsMaximal),
    ∃ θ : 𝓞 E →+ ℤ, (∀ t, θ (H.bar t) = θ t) ∧ ∃ s : 𝓞 E, s ∉ 𝔭 ∧ H.bar s ∉ 𝔭 ∧
      ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u) :=
  GlobalTheory.T.exists_conj_invariant_trace_generator_local

theorem img_bar_ne_top : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hn : 0 < n) (hc : Cois D y n) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hn𝔭 : (n : 𝓞 E) ∈ 𝔭) (hi : img D y Z' 𝔭 ≠ ⊤) (hL : (perp D Z ⊓ perp D Z').map y ≤ img D y Z' 𝔭),
    img D y Z' (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E)) ≠ ⊤ :=
  GlobalTheory.T.isotropicImage_not_onto_mod_conj_ideal

theorem improves_A : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (m : D.La) (hm : m ∈ perp D Z ⊓ perp D Z') (hym : y m ∉ img D y Z' 𝔭)
    (hA : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭 ∨ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' :=
  GlobalTheory.T.exists_oppositeSubmodule_improved_mod_prime_of_orthogonal

theorem rankOneChange_improves_real_prime_first : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' :=
  GlobalTheory.T.exists_rankOneChange_improves_image_real_prime

theorem rankOneChange_improves_nonreal_prime : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭)
    (e : 𝓞 E) (he1 : e - 1 ∈ 𝔭) (he : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭 → e ∈ 𝔮)
    (e' : 𝓞 E) (he1' : e' - 1 ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (he' : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 → 𝔮 ≠ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) → e' ∈ 𝔮)
    (v : Z') (hv : y v ∈ 𝔭 • (⊤ : Submodule (𝓞 E) X)) (ℓ₀ : Z' →ₗ[𝓞 E] 𝓞 E) (hℓ₀ : ℓ₀ v ∉ 𝔭)
    (v₂ : Z') (hv₂ : y v₂ ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) X)) (ℓ₁ : Z' →ₗ[𝓞 E] 𝓞 E)
    (hℓ₁ : ℓ₁ v₂ ∉ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E))
    (θ : 𝓞 E →+ ℤ) (hθ : ∀ t, θ (H.bar t) = θ t) (s : 𝓞 E) (hs : s ∉ 𝔭) (hs' : H.bar s ∉ 𝔭)
    (hgen : ∀ ψ : 𝓞 E →+ ℤ, ∃ t : 𝓞 E, ∀ u, ψ (s * u) = θ (t * u))
    (hZ : ¬ Z.map y ≤ img D y Z' 𝔭),
    ∃ Z'', Improves D y n 𝔭 Z Z' Z'' :=
  GlobalTheory.T.exists_oppositeSubmodule_improved_mod_prime_of_ne_conj

theorem img_top_of {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hc : Cois D y n)
    (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (𝔭 : Ideal (𝓞 E)) (hn𝔭 : (n : 𝓞 E) ∈ 𝔭)
    (hZ : Z.map y ≤ img D y Z' 𝔭) (hL : ∀ m ∈ perp D Z ⊓ perp D Z', y m ∈ img D y Z' 𝔭) :
    img D y Z' 𝔭 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, e, hae⟩ := hc.1 x
  obtain ⟨z, hz, m, hm, b, hb, rfl⟩ := h.exists_decomp a
  have h1 : y (z + m + b) ∈ img D y Z' 𝔭 := by
    rw [map_add (f := _), map_add (f := _)]
    exact add_mem (add_mem (hZ ⟨z, hz, rfl⟩) (hL m hm)) (Submodule.mem_sup_left ⟨b, hb, rfl⟩)
  have h2 : n • e ∈ img D y Z' 𝔭 := by
    apply Submodule.mem_sup_right
    rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
    exact Submodule.smul_mem_smul hn𝔭 trivial
  have h3 : x = y (z + m + b) - n • e := by rw [hae]; abel
  rw [h3]
  exact sub_mem h1 h2

theorem improve {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ) (hn : 0 < n) (hc : Cois D y n) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z')
    (hr : Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X) (𝔭 : Ideal (𝓞 E)) (h𝔭 : 𝔭.IsMaximal)
    (hn𝔭 : (n : 𝓞 E) ∈ 𝔭) (hi : img D y Z' 𝔭 ≠ ⊤) : ∃ Z'', Improves D y n 𝔭 Z Z' Z'' := by
  obtain ⟨e, he1, he⟩ := exists_sep (E := E) n hn 𝔭 h𝔭
  obtain ⟨v, hv, ℓ₀, hℓ₀⟩ := exists_ker_vec D y Z Z' h hr 𝔭 h𝔭 hi
  obtain ⟨θ, hθ, s, hs, hs', hgen⟩ := exists_real_theta H 𝔭 h𝔭
  by_cases hA : ∃ m ∈ perp D Z ⊓ perp D Z', y m ∉ img D y Z' 𝔭 ∧
      (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ 𝔭 ∨ Z.map y ≤ img D y Z' 𝔭)
  · obtain ⟨m, hm, hym, hA⟩ := hA
    exact improves_A D y n Z Z' h 𝔭 h𝔭 hn𝔭 e he1 he v hv ℓ₀ hℓ₀ m hm hym hA
  have hZ : ¬ Z.map y ≤ img D y Z' 𝔭 := fun hZ =>
    hi (img_top_of D y n hc Z Z' h 𝔭 hn𝔭 hZ fun m hm => by_contra fun h' => hA ⟨m, hm, h', Or.inr hZ⟩)
  by_cases hb : 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔭
  · exact rankOneChange_improves_real_prime_first D y n Z Z' h 𝔭 h𝔭 hb e he1 he v hv ℓ₀ hℓ₀ θ hθ s hs hs' hgen hZ
  have hL : (perp D Z ⊓ perp D Z').map y ≤ img D y Z' 𝔭 := by
    rintro _ ⟨m, hm, rfl⟩
    exact by_contra fun h' => hA ⟨m, hm, h', Or.inl hb⟩
  have hi' := img_bar_ne_top D y n hn hc Z Z' h hr 𝔭 h𝔭 hn𝔭 hi hL
  have h𝔭' : (𝔭.map (H.bar : 𝓞 E →+* 𝓞 E)).IsMaximal := Ideal.map_isMaximal_of_equiv H.bar
  have hn𝔭' : (n : 𝓞 E) ∈ 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    simpa using Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hn𝔭
  obtain ⟨e', he1', he'⟩ := exists_sep (E := E) n hn _ h𝔭'
  obtain ⟨v₂, hv₂, ℓ₁, hℓ₁⟩ := exists_ker_vec D y Z Z' h hr _ h𝔭' hi'
  exact rankOneChange_improves_nonreal_prime D y n Z Z' h 𝔭 h𝔭 hn𝔭 hb e he1 he e' he1' he' v hv ℓ₀ hℓ₀ v₂ hv₂ ℓ₁ hℓ₁ θ hθ s hs hs' hgen hZ

end GlobalTheory.LowFilt.Transv

namespace GlobalTheory.LowFilt

open GlobalTheory.LowFilt.Transv in
theorem exists_opp_transv : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → Cois D y n → ∀ Z Z₀ : Submodule (𝓞 E) D.La, IsOpp D Z Z₀ →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X →
    ∃ Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' ∧ ∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e := by
  intro E _ _ _ H D X _ _ _ _ y n hn hc Z Z₀ h0 hr
  classical
  let S := {𝔮 : Ideal (𝓞 E) | 𝔮.IsMaximal ∧ (n : 𝓞 E) ∈ 𝔮}
  haveI : Finite S := (fin_max (E := E) n hn).to_subtype
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  let F : Submodule (𝓞 E) D.La → (S → Submodule (𝓞 E) X) := fun Z' q => img D y Z' q.1
  haveI : IsNoetherian (𝓞 E) X := isNoetherian_of_isNoetherianRing_of_finite (𝓞 E) X
  have h1 : WellFoundedLT (S → (Submodule (𝓞 E) X)ᵒᵈ) := Pi.wellFoundedLT
  haveI : WellFoundedGT (S → Submodule (𝓞 E) X) := h1
  have wf : WellFounded (fun a b : S → Submodule (𝓞 E) X => b < a) := wellFounded_gt
  obtain ⟨_, ⟨Z', hZ', rfl⟩, hmax⟩ := wf.has_min (F '' {Z' | IsOpp D Z Z'}) ⟨_, Z₀, h0, rfl⟩
  have htop : ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (n : 𝓞 E) ∈ 𝔮 →
      Z'.map y ⊔ 𝔮 • (⊤ : Submodule (𝓞 E) X) = ⊤ := by
    intro 𝔮 hq hnq
    by_contra hne
    obtain ⟨Z'', h1, h2, h3⟩ := improve D y n hn hc Z Z' hZ' hr 𝔮 hq hnq hne
    exact hmax (F Z'') ⟨Z'', h1, rfl⟩
      (lt_of_le_not_ge (fun q => h2 q.1 q.2.1 q.2.2) fun hle => h3 (hle ⟨𝔮, hq, hnq⟩))
  have hall := sup_eq_top (Z'.map y) n hn htop
  refine ⟨Z', hZ', fun x => ?_⟩
  have hx : x ∈ Z'.map y ⊔ Ideal.span {(n : 𝓞 E)} • (⊤ : Submodule (𝓞 E) X) := by rw [hall]; trivial
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_sup] at hx
  obtain ⟨_, ⟨b, hb, rfl⟩, w, hw, hsum⟩ := hx
  obtain ⟨e', -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hw
  refine ⟨b, hb, -e', ?_⟩
  rw [smul_neg, ← Nat.cast_smul_eq_nsmul (𝓞 E), ← hsum]
  abel

end GlobalTheory.LowFilt
end
end

section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt


theorem _root_.GlobalTheory.T.exists_isometry_kernel_coisotropic_mod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → Cois D y n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X →
    (∀ a, (∃ e, y a = N • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + N • e) →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∃ g : D.La ≃ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧
      ∀ a, (∃ e, y (g a) = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e := by
  first | exact @GlobalTheory.LowFilt.exists_isometry_kerIs | exact GlobalTheory.LowFilt.exists_isometry_kerIs | (intros; apply GlobalTheory.LowFilt.exists_isometry_kerIs <;> assumption)
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

theorem _root_.GlobalTheory.T.exists_externalTensor_rigidified_cubical_product : ∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (L₁ : RigLB G₁) (L₂ : RigLB G₂) (c₁ : CubicalStr G₁ L₁) (c₂ : CubicalStr G₂ L₂) (s₁ : SymGen G₁ L₁.L) (s₂ : SymGen G₂ L₂.L), s₁.IsGen → s₂.IsGen → LB.Gen.Corr L₁.L _ _ _ _ (LB.pullGen L₁.L _ _ s₁ (eSec G₁)) (LB.oneGen L₁.L) → LB.Gen.Corr L₂.L _ _ _ _ (LB.pullGen L₂.L _ _ s₂ (eSec G₂)) (LB.oneGen L₂.L) → ∃ (L : RigLB (G₁ ⊗ G₂)) (c : CubicalStr (G₁ ⊗ G₂) L) (s : SymGen (G₁ ⊗ G₂) L.L) (w : LB.Iso L.L (extLB L₁.L L₂.L (fst G₁ G₂).left (snd G₁ G₂).left)), s.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec (G₁ ⊗ G₂))) (LB.oneGen L.L) ∧ StrBox (fst G₁ G₂) (snd G₁ G₂) w L.rig L₁.rig L₂.rig c.t c₁.t c₂.t s s₁ s₂ := by
  first | exact @GlobalTheory.GrpBox.exists_prod | exact GlobalTheory.GrpBox.exists_prod | (intros; apply GlobalTheory.GrpBox.exists_prod <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

theorem _root_.GlobalTheory.T.expansionModIdealPow_boxProduct_eq_boxProduct : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (A : PolAV (Sp (FractionRing R))) (U : UnifPre I D A (G₁ ⊗ G₂)), Function.Bijective (q₁.prod q₂) → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)) (wL : LB.Iso U.LG.L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)) (e k : ℕ), (U.gt e).pG.left ≫ p₁.left = ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ (U₁.gt e).pG.left → (U.gt e).pG.left ≫ p₂.left = ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ (U₂.gt e).pG.left → (∀ x, IsBoxGen (Y := (thickObj R I e (G₁ ⊗ G₂)).left) (Y₁ := (thickObj R I e G₁).left) (Y₂ := (thickObj R I e G₂).left) wM ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ((U.gt e).t x) ((U₁.gt e).t (q₁ x)) ((U₂.gt e).t (q₂ x))) → BoxSq (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left) (T₂ := (thickObj R I e G₂).left) wM wL (U.w e) (U₁.w e) (U₂.w e) ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left → ∀ (σ : H0 U.LG.L k) (σ₁ : H0 U₁.LG.L k) (σ₂ : H0 U₂.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (f₁ : ∀ α : D₁.toPre.X, D₁.toPre.SecB k α) (f₂ : ∀ α : D₂.toPre.X, D₂.toPre.SecB k α), IsBoxSec wL (fst G₁ G₂).left (snd G₁ G₂).left σ σ₁ σ₂ → (∀ α, IsBoxSec wM p₁.left p₂.left (f α) (f₁ (q₁ α)) (f₂ (q₂ α))) → U₁.ExpandsAt e k σ₁ f₁ → U₂.ExpandsAt e k σ₂ f₂ → U.ExpandsAt e k σ f := by
  first | exact @GlobalTheory.ProdUnif.expandsAt_boxProd | exact GlobalTheory.ProdUnif.expandsAt_boxProd | (intros; apply GlobalTheory.ProdUnif.expandsAt_boxProd <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

theorem _root_.GlobalTheory.T.boxFamily_linearIndependent_productDegeneration : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)) (F : Type) [Field F] [Algebra (FractionRing R) F] (k m n : ℕ) (b₁ : Fin m → Fam D₁ F k) (b₂ : Fin n → Fam D₂ F k) (b : Fin m × Fin n → Fam D F k), LinearIndependent F b₁ → LinearIndependent F b₂ → (∀ a, IsBoxFam₂ p₁ p₂ q₁ q₂ w F k (b a) (b₁ a.1) (b₂ a.2)) → LinearIndependent F b := by
  first | exact @GlobalTheory.ProdIndep.boxFam₂_linearIndependent | exact GlobalTheory.ProdIndep.boxFam₂_linearIndependent | (intros; apply GlobalTheory.ProdIndep.boxFam₂_linearIndependent <;> assumption)
end
