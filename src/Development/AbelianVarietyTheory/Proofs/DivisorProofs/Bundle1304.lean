module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyTermTranslateBoundFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1212
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1214
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubeFaceMiddleProjProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle011
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusExt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle710
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.Bundle001

@[expose] public section

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

noncomputable section

namespace GlobalTheory.HSNef

open MeasureTheory

theorem gdeg_nonneg_of_semiPos : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ L : HermLB p, L.SemiPos D → 0 ≤ gdeg L D := by
  intro k _ X _ p D _ L hL
  unfold gdeg chInt
  refine finsum_nonneg fun σ => ?_
  rw [Weight.chernInt, Weight.chernPart_neg_eq_zero (L.cInf σ) (hL σ)]
  simp only [Measure.restrict_zero, integral_zero_measure, sub_zero]
  exact integral_nonneg fun _ => zero_le_one

end GlobalTheory.HSNef
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.NefFibPrime

theorem isClosedImmersion_spMap_zmod (p : ℕ) : IsClosedImmersion (spMap (Int.castRingHom (ZMod p))) :=
  IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective (Int.castRingHom (ZMod p)))

theorem topSelf_nonneg_of_nefFib (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (L : HermLB q) (p : ℕ)
    [Fact p.Prime] (h : ArInt.NefFib L) (Z : Scheme.{0})
    (i : Z ⟶ pullback (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))))
    [IsClosedImmersion i] [IsIntegral Z] [Algebra (ZMod p) Γ(Z, ⊤)] (hd : topologicalKrullDim Z = 1) :
    0 ≤ topSelfIntersection (ZMod p) ((L.B.pull (pullback.fst (q ≫ spMap (Int.castRingHom k))
      (spMap (Int.castRingHom (ZMod p))))).pull i) 1 := by
  have := isClosedImmersion_spMap_zmod p
  have : IsClosedImmersion (pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p)))) :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _).flip this
  set f := pullback.fst (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod p))) with hf
  have h1 := h Z (i ≫ f) (ZMod p) hd
  have e : topSelfIntersection (ZMod p) ((L.B.pull f).pull i) 1 = topSelfIntersection (ZMod p) (L.B.pull (i ≫ f)) 1 := by
    rw [topSelf_def, topSelf_def]
    refine interNum_congr_cls (ZMod p) _ (fun _ => LB.isLB_pull (LB.isLB_pull L.isLB f) i)
      (fun _ => LB.isLB_pull L.isLB (i ≫ f)) fun _ => ?_
    show pull i (pull f (cls L.B L.isLB)) = pull (i ≫ f) (cls L.B L.isLB)
    rw [← pull_comp]
  rw [e]
  exact h1

end GlobalTheory.NefFibPrime
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.familyTerm_translate_bound_functionalEquation : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (IsLocalRing.maximalIdeal V)) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ q, N.Int q → ∀ (k : ℕ), 1 ≤ k → ∀ (s : Fam D.toPre C k) (gm₀ : GtPt D.toPre (epsR V)) (gm : GtPt D.toPre (TE V C)), GtTan gm₀ → GtPt.IsPull (spMap (dualMap (toF V C))) gm₀ gm → ∀ α mu : N.X, ‖(jc ν s gm (α + k • mu)).fst‖ ≤ Real.exp (-((k : ℝ) * q mu + QuadraticMap.polar q mu α)) * ‖(trVal ν s gm α mu).fst‖ ∧ ‖(jc ν s gm (α + k • mu)).snd‖ ≤ Real.exp (-((k : ℝ) * q mu + QuadraticMap.polar q mu α)) * max ‖(trVal ν s gm α mu).fst‖ ‖(trVal ν s gm α mu).snd‖ := by
  first | exact @GlobalTheory.MBLow.TranslBound.main | exact GlobalTheory.MBLow.TranslBound.main | (intros; apply GlobalTheory.MBLow.TranslBound.main <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.integralSectionValue_tangent_eq_adicExpansionSum : AllV fun {V} _ _ _ {D} {A} {G} _ _ U => ∀ (y : epsR V ⟶ G) (gm₀ : GtPt D.toPre (epsR V)), IsTangent y → TanRel U.toUnifPre y gm₀ → ∀ (k : ℕ) (jG : U.LG.L.ι) (J : (Sp (DualNumber V) ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), ⊤ ≤ y.left ⁻¹ᵁ U.LG.L.U jG → (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.toPre.P.L.U (J ψ)) → ∃ W : (DualNumber V)ˣ, (W : DualNumber V).fst * GlobalTheory.MBLow.TanExp.rigVal U.LG jG = GlobalTheory.MBLow.TanExp.rigValD D.toPre (J gm₀.b.left) ∧ ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e, U.toUnifPre.ExpandsAt e k σ f) → GlobalTheory.UT.SumI (IsLocalRing.maximalIdeal V) (fun α => GlobalTheory.MBLow.TanExp.termV J gm₀ (f α)) ((W : DualNumber V) ^ k * valR y.left (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) fun _ => jG) (σ.f fun _ => jG)) := by
  first | exact @GlobalTheory.MBLow.TanExp.value_mul_sumI | exact GlobalTheory.MBLow.TanExp.value_mul_sumI | (intros; apply GlobalTheory.MBLow.TanExp.value_mul_sumI <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

theorem _root_.GlobalTheory.T.holomorphic_functionValues_classicalUniformisation : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (D : DegPre R) (N : NumD ℂ)
    (ν : NumOf D ℂ N) (g : ℕ) (d : AB N.toNumB g) (x : KeyIn ℂ) (u : HolUnif x.P.A x.P.L g) (φ : x.P.A.left ⟶ D.P.A.left),
    IsGrpPullback x.P.A D.P.A (spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) φ → (∀ z, (ν.eA (d.ex z)).left = (u.ex z).left ≫ φ) →
    ∀ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)), IsOpen {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} ∧
      DifferentiableOn ℂ (fun z => valF (ptB ν d z) U f) {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ U} := by
  first | exact @GlobalTheory.MBLow.Cl.HolB.hol_ptB | exact GlobalTheory.MBLow.Cl.HolB.hol_ptB | (intros; apply GlobalTheory.MBLow.Cl.HolB.hol_ptB <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.smoothWeightedLineBundle_logSectionNorm_properties : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (M : MLine p σ) (s : M.B.Sec), Measurable (M.logSec s) ∧ (∀ y : CxPts p σ, 0 < M.φ.nsq (secVal p σ s) y ↔ y ∈ ptsIn p σ (nonzeroLocus s)) ∧ (∀ y, CInfAt (M.φ.nsq (secVal p σ s)) y) ∧ ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), ∀ y ∈ ptsIn p σ (nonzeroLocus s), (M.addFn u hu).logSec s y = M.logSec s y - u y / 2 := by
  first | exact @GlobalTheory.Mix.SecNorm.logSec_basic | exact GlobalTheory.Mix.SecNorm.logSec_basic | (intros; apply GlobalTheory.Mix.SecNorm.logSec_basic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasSum_dualNumber_coords_of_adicSum : ∀ (V : Type) [CommRing V] [IsDomain V] [IsNoetherianRing V] (I : Ideal V) (C : Type) [NormedField C] [IsUltrametricDist C] [Algebra (FractionRing V) C], CExt V I C → ∀ {Ix : Type} (x : Ix → DualNumber V) (s : DualNumber V), GlobalTheory.UT.SumI I x s → HasSum (fun i => toF V C (x i).fst) (toF V C s.fst) ∧ HasSum (fun i => toF V C (x i).snd) (toF V C s.snd) := by
  first | exact @GlobalTheory.AdicDual.hasSum_fst_snd | exact GlobalTheory.AdicDual.hasSum_fst_snd | (intros; apply GlobalTheory.AdicDual.hasSum_fst_snd <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section
namespace GlobalTheory.MBLow.Cl.CubeVal

theorem prod_three' {M : Type} [CommMonoid M] (F : Finset (Fin 3) → M) :
    ∏ s, F s = F ∅ * F {0} * F {1} * F {2} * F {0, 1} * F {0, 2} * F {1, 2} * F {0, 1, 2} := by
  rw [show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  ac_rfl

theorem prod_three {M : Type} [CommMonoid M] (F : thK.{0} → M) :
    ∏ I, F I = F ⟨∅⟩ * F ⟨{0}⟩ * F ⟨{1}⟩ * F ⟨{2}⟩ * F ⟨{0, 1}⟩ * F ⟨{0, 2}⟩ * F ⟨{1, 2}⟩ * F ⟨{0, 1, 2}⟩ :=
  (Equiv.prod_comp (Equiv.ulift.symm : Finset (Fin 3) ≃ thK.{0}) F).symm.trans (prod_three' fun s => F ⟨s⟩)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem ex_sum (d : AB N.toNumB g) {κ : Type} (s : Finset κ) (v : κ → Fin g → ℂ) :
    d.ex (∑ i ∈ s, v i) = ∏ i ∈ s, d.ex (v i) := by
  classical
  have h0 : d.ex 0 = 1 := by
    have e := d.ex_add 0 0
    rw [add_zero] at e
    exact (mul_eq_left.1 e.symm)
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, d.ex_add, ih]

theorem pt_thφ (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) (I : thK.{0}) :
    (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left ≫ thφ D.P.A (x3 D.P.A) I =
      (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left := by
  show _ ≫ (psum D.P.A (x3 D.P.A) I.down).left = _
  rw [← Over.comp_left, CubePf.CubeCoordinateSums.psum_eq_prod, CubePf.CubeCoordinateSums.comp_prod, ex_sum, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  fin_cases i <;> simp [x3]

end GlobalTheory.MBLow.Cl.CubeVal

namespace GlobalTheory.MBLow.Cl.CubeVal

theorem thε_vals : thε ⟨(∅ : Finset (Fin 3))⟩ = -1 ∧ thε ⟨({0} : Finset (Fin 3))⟩ = 1 ∧ thε ⟨({1} : Finset (Fin 3))⟩ = 1 ∧
    thε ⟨({2} : Finset (Fin 3))⟩ = 1 ∧ thε ⟨({0, 1} : Finset (Fin 3))⟩ = -1 ∧ thε ⟨({0, 2} : Finset (Fin 3))⟩ = -1 ∧
    thε ⟨({1, 2} : Finset (Fin 3))⟩ = -1 ∧ thε ⟨({0, 1, 2} : Finset (Fin 3))⟩ = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem prod_const_zpow (r : ℂ) (hr : r ≠ 0) : ∏ I : thK.{0}, r ^ thε I = 1 := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := thε_vals
  rw [prod_three, e0, e1, e2, e3, e4, e5, e6, e7]
  field_simp

theorem alg (a b f : thK.{0} → ℂ) (r θ V : ℂ) (hr : r ≠ 0) (hf : ∀ I, f I ≠ 0) (h : ∀ I, f I * r = a I * b I)
    (h1 : θ = (∏ I, a I ^ thε I) * V) (h2 : θ = ∏ I, f I ^ thε I) : V = ∏ I, b I ^ thε I := by
  have ha : ∀ I, a I ≠ 0 := fun I => left_ne_zero_of_mul (h I ▸ mul_ne_zero (hf I) hr)
  have hA : (∏ I, a I ^ thε I) ≠ 0 := Finset.prod_ne_zero_iff.2 fun I _ => zpow_ne_zero _ (ha I)
  have hAB : (∏ I, a I ^ thε I) * ∏ I, b I ^ thε I = ∏ I, f I ^ thε I := by
    rw [← Finset.prod_mul_distrib]
    have e : ∀ I, a I ^ thε I * b I ^ thε I = f I ^ thε I * r ^ thε I := fun I => by
      rw [← mul_zpow, ← mul_zpow, h I]
    simp only [e, Finset.prod_mul_distrib, prod_const_zpow r hr, _root_.mul_one]
  rw [h1] at h2
  exact mul_left_cancel₀ hA (h2.trans hAB.symm)

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

theorem theta_eq_prod (d : AB N.toNumB g) (hc : d.Cub) (x y z : Fin g → ℂ) :
    (N.θ (d.ex x) (d.ex y) (d.ex z) : ℂ) = ∏ I : thK.{0}, (d.fr (∑ i ∈ I.down, ![x, y, z] i) : ℂ) ^ thε I := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ := thε_vals
  have h := congrArg Units.val (hc x y z)
  simp only [Units.val_mul] at h
  rw [prod_three, e0, e1, e2, e3, e4, e5, e6, e7]
  simp [Finset.sum_insert, d.fr_zero, ← add_assoc]
  have := (d.fr (x + y)).ne_zero
  have := (d.fr (x + z)).ne_zero
  have := (d.fr (y + z)).ne_zero
  field_simp
  linear_combination h

end GlobalTheory.MBLow.Cl.CubeVal

namespace GlobalTheory.MBLow.Cl


open CubeVal in
theorem cube_val_frame : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ}
    {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g), d.Cub → ∀ (G : Geo ν d) (x y z : Fin g → ℂ) (j : thK.{0} → D.P.L.ι),
    (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ D.P.L.U (j I)) →
    valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j)
      (D.cub.t.s j).val = ∏ I : thK.{0}, G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) ^ thε I := by
  intro R _ _ D _ N g ν d hc G x y z j hj
  have hpt := pt_thφ ν d x y z
  set p := (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left with hp
  have htr : ∀ I : thK.{0}, (d.fr (∑ i ∈ I.down, ![x, y, z] i) : ℂ) * ν.rg =
      valF (p ≫ thφ D.P.A (x3 D.P.A) I) (D.P.L.U (ν.J (p ≫ thφ D.P.A (x3 D.P.A) I)) ⊓ D.P.L.U (j I))
        (D.P.L.g (ν.J (p ≫ thφ D.P.A (x3 D.P.A) I)) (j I)).val * G.frG (j I) (∑ i ∈ I.down, ![x, y, z] i) := by
    intro I
    rw [hpt I, G.fr_eq]
    exact G.fr_compat _ _ _ fun q _ => ⟨ν.good _ (x := q) trivial, hj I (x := q) trivial⟩
  have hin : ⊤ ≤ p ⁻¹ᵁ (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) (fun I => ν.J (p ≫ thφ D.P.A (x3 D.P.A) I)) ⊓
      LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) j) := fun q _ =>
    ⟨Set.mem_iInter.2 fun I => ν.good (p ≫ thφ D.P.A (x3 D.P.A) I) (x := q) trivial,
      Set.mem_iInter.2 fun I => by
        have h := hj I
        rw [← hpt I] at h
        exact h (x := q) trivial⟩
  have e1 := PullbackSections.vtf_isGen_val D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t D.cub.isGen p _ j hin
  have e2 := ν.θ_eq (d.ex x) (d.ex y) (d.ex z)
  exact alg _ _ (fun I => (d.fr (∑ i ∈ I.down, ![x, y, z] i) : ℂ)) ν.rg _ _ (SymFrame.rg_ne ν) (fun I => Units.ne_zero _)
    htr (e2.trans e1) (theta_eq_prod d hc x y z)

end GlobalTheory.MBLow.Cl

end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

theorem _root_.GlobalTheory.T.le_arithVolume_of_frequently_smallSections_lower : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (L : HermLB p) (a : ℝ), (∀ ε : ℝ, 0 < ε → ∃ᶠ N : ℕ in atTop, (L.pow N).smallSec.Finite ∧ (a / (D + 1).factorial - ε) * (N : ℝ) ^ (D + 1) ≤ Real.log ((L.pow N).smallSec.ncard : ℝ)) → (a : EReal) ≤ arVol L D := by
  first | exact @GlobalTheory.VolBr.le_arVol_of_frequently_le | exact GlobalTheory.VolBr.le_arVol_of_frequently_le | (intros; apply GlobalTheory.VolBr.le_arVol_of_frequently_le <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.mixedChernFormDensity_pullback_matching_charts : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (π : Y ⟶ X) (hπ : π ≫ p = q) (L : Fin D → MLine p σ) (c : AlgChart p σ D) (c' : AlgChart q σ D), (∀ w ∈ c'.e.source, ptMap π hπ σ w ∈ c.e.source ∧ c'.e w = c.e (ptMap π hπ σ w)) → ∀ w ∈ c'.e.source, dens (fun i => (L i).pull π hπ) c' w = dens L c (ptMap π hπ σ w) := by
  first | exact @GlobalTheory.MixPull.dens_pull | exact GlobalTheory.MixPull.dens_pull | (intros; apply GlobalTheory.MixPull.dens_pull <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.mixedChernFormDensity_update_tensor_add : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → MLine p σ) (i : Fin D) (A B : MLine p σ) (c : AlgChart p σ D), ∀ y ∈ c.e.source, dens (Function.update L i (A.tens B)) c y = dens (Function.update L i A) c y + dens (Function.update L i B) c y := by
  first | exact @GlobalTheory.Mix.dens_update_tens | exact GlobalTheory.Mix.dens_update_tens | (intros; apply GlobalTheory.Mix.dens_update_tens <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

theorem _root_.GlobalTheory.T.continuousOn_mixedChernFormDensityInChart : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ) (L : Fin D → MLine p σ) (c : AlgChart p σ D), ContinuousOn (dens L c) c.e.source := by
  first | exact @GlobalTheory.Mix.continuousOn_dens | exact GlobalTheory.Mix.continuousOn_dens | (intros; apply GlobalTheory.Mix.continuousOn_dens <;> assumption)
end
