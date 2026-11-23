module

public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle125
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle031
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2686
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRaynaudPointUnitPartCoordinates
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle015
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle066
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle074
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle126
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle661
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2635
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.PsiEvenCoordUnit

open GlobalTheory.PeriodBalance GlobalTheory.PsiTauCoordRel

theorem alg' {G : Type} [CommGroup G] (a b c x y : G) (h : b * y * c = a * x) : y = a * b⁻¹ * c⁻¹ * x := by
  rw [mul_right_comm (a * b⁻¹), mul_right_comm a, ← h, mul_right_comm (b * y), mul_right_comm b, mul_inv_cancel,
    _root_.one_mul, mul_inv_cancel_right]

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R), D.PsiEven →
    ∀ (y : D.X) (x x' : (FractionRing R)ˣ), IsPsiCoord D y x → IsPsiCoord D (-y) x' →
      ∃ u : Rˣ, (x' : FractionRing R) = algebraMap R (FractionRing R) u * x := by
  intro R _ _ _ D hE y x x' hx hx'
  haveI : IsProper D.P.A.hom := D.P.isAb.proper
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of (FractionRing R))) := ⟨⟨⊥, Ideal.isPrime_bot⟩⟩
  obtain ⟨J, hJ, hJc⟩ := exists_good_integral ξ D.P.isLB D.P.A.hom
  let cU : Rˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ := Units.map (cst ξ).toMonoidHom
  let kU : (FractionRing R)ˣ →* ((Spec (CommRingCat.of (FractionRing R))).presheaf.stalk ξ)ˣ :=
    Units.map (kst ξ).toMonoidHom
  have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hE y) (𝟙 _))
  rw [val_pull hJ] at e
  obtain ⟨w, hw⟩ : ∃ w : Rˣ, val D.sym (𝟙 _ ≫ D.xK y) ξ J = cU w := by
    have : 𝟙 _ ≫ D.xK y = jK R ≫ (D.c y).left := by rw [Category.id_comp]; exact xK_eq D y
    rw [this]
    refine val_int ξ hJc D.sym (D.c y).left fun k => ?_
    obtain ⟨q, hq⟩ : ∃ q : D.P.A ⟶ D.P.A,
        (![(ι[D.P.A]).left, 𝟙 D.P.A.left] : Fin 2 → _) k = q.left := by
      fin_cases k
      · exact ⟨_, rfl⟩
      · exact ⟨𝟙 _, rfl⟩
    rw [hq, Category.assoc, Over.w q, Over.w]; rfl
  obtain ⟨j, h, i1, rfl⟩ := hx
  obtain ⟨j', h', i1', rfl⟩ := hx'
  obtain ⟨c1, g1⟩ := val_psi_chart D ξ hJ hJc y j i1 (h trivial)
  obtain ⟨c2, g2⟩ := val_psi_chart D ξ hJ hJc (-y) j' i1' (h' trivial)
  have e1 : gm (𝟙 _) ξ (LB.wchart D.P.L _ j) ((D.psi y).s j) = kU (genVal (D.psi y) j h) :=
    Units.ext (gm_genVal ξ (D.psi y) j h)
  have e2 : gm (𝟙 _) ξ (LB.wchart D.P.L _ j') ((D.psi (-y)).s j') = kU (genVal (D.psi (-y)) j' h') :=
    Units.ext (gm_genVal ξ (D.psi (-y)) j' h')
  have f : cU c2 * kU (genVal (D.psi (-y)) j' h') * cU w = cU c1 * kU (genVal (D.psi y) j h) :=
    (congrArg₂ (· * ·) (g2.trans (congrArg (cU c2 * ·) e2)) hw).symm.trans
      (e.trans (g1.trans (congrArg (cU c1 * ·) e1)))
  refine ⟨c1 * c2⁻¹ * w⁻¹, ?_⟩
  have k3 : genVal (D.psi (-y)) j' h' = Units.map (algebraMap R (FractionRing R)).toMonoidHom (c1 * c2⁻¹ * w⁻¹) *
      genVal (D.psi y) j h := by
    refine Units.map_injective (f := (kst ξ).toMonoidHom) (kst_injective ξ) ?_
    rw [map_mul]
    change kU _ = cU (c1 * c2⁻¹ * w⁻¹) * kU _
    rw [map_mul, map_mul, map_inv, map_inv]
    exact alg' _ _ _ _ _ f
  exact congrArg Units.val k3

end GlobalTheory.PsiEvenCoordUnit
end
end

section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArLieBase

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {T : Scheme.{0}}
  (t : SAB H T)

def LatPres {R : Type} [CommRing R] (x : Sp R ⟶ T) (kind : ℕ → Bool) (sc : ℕ → ℝ) {g M : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (h : Fin M → Fin g → R) : Prop :=
  (∃ n : ℕ, n ≠ 0 ∧ ∀ i, Pi.single i (n : R) ∈ Submodule.span R (Set.range h)) ∧
  ∀ (p : ℕ) [Fact p.Prime] (φ : R →+* ↥(intO ℂ_[p])), ∃ δ : ℂ_[p], ‖δ‖ = (p : ℝ) ^ (-sc p) ∧
    ∀ (cf : Fin g → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ t.G.left),
      IsCombAtG t (spMap ((intO ℂ_[p]).subtype.comp φ) ≫ x)
        (fun i => spMap (dualMap ((intO ℂ_[p]).subtype.comp φ)) ≫ e i) cf w →
      (spMap (epsMul δ) ≫ w ∈ lat t p (spMap ((intO ℂ_[p]).subtype.comp φ) ≫ x) (kind p) ↔
        ∀ j, ‖∑ i, ((φ (h j i) : ↥(intO ℂ_[p])) : ℂ_[p]) * cf i‖ ≤ 1)

end Tangent

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)


abbrev LocAssign {X W : Scheme.{0}} (r : ℕ) (jB : W ⟶ X) (U : X.Opens) : Type 1 :=
  ∀ (K : Type) [CommRing K] (x : Sp K ⟶ W), ⊤ ≤ (x ≫ jB) ⁻¹ᵁ U → Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)

end Free

end GlobalTheory.ArLieBase

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

theorem _root_.GlobalTheory.T.exists_derivation_lift_raynaud_preimage_affine : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens) (D : Derivation ℤ R R), ∃ δ : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1) → Γ(Y.H.left, Y.q.left ⁻¹ᵁ V.1), (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = a * δ b + b * δ a) ∧ ∀ r, δ (constFn Y.H.hom _ r) = constFn Y.H.hom _ (D r) := by
  first | exact @GlobalTheory.LiftDer.exists_lift_preimage | exact GlobalTheory.LiftDer.exists_lift_preimage | (intros; apply GlobalTheory.LiftDer.exists_lift_preimage <;> assumption)
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

theorem _root_.GlobalTheory.T.isAffineOpen_preimage_projection_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.affineOpens), IsAffineOpen (Y.q.left ⁻¹ᵁ V.1) := by
  first | exact @GlobalTheory.RayEv.Ray.isAffineOpen_preimage_q | exact GlobalTheory.RayEv.Ray.isAffineOpen_preimage_q | (intros; apply GlobalTheory.RayEv.Ray.isAffineOpen_preimage_q <;> assumption)
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

theorem _root_.GlobalTheory.T.torusWeightScalar_zeroCharacter_eq_one : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (S : Type) [CommRing S] (φ : R →+* S) (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ), x' ≫ Y.q = x ≫ Y.q → (∀ χ y J, Good Q.P.L y J → val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) → c 0 = 1 := by
  first | exact @GlobalTheory.Heat.weight_scalar_zero_eq_one | exact GlobalTheory.Heat.weight_scalar_zero_eq_one | (intros; apply GlobalTheory.Heat.weight_scalar_zero_eq_one <;> assumption)
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

theorem _root_.GlobalTheory.T.raynaudProjection_sectionValues_identity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α) (C : R), (∀ (y : Y.H.left) J, Good Q.P.L y J → sval σ' Y.q.left y J = sval σ'' Y.q.left y J + gs (𝟙 _) y ⊤ (scal Y.H.hom C) * sval σ Y.q.left y J) → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ' x.left z J = sval σ'' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom C) * sval σ x.left z J := by
  first | exact @GlobalTheory.FourierDescent.values_identity | exact GlobalTheory.FourierDescent.values_identity | (intros; apply GlobalTheory.FourierDescent.values_identity <;> assumption)
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
open ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.raynaudShift_unitIdentity_fractionField : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), Q.TauBimult → ∀ (k : ℕ) (mu α : Q.X) (xp : 𝟙_ (Over (Sp R)) ⟶ Y.H) (A₀ B₀ P₀ : R) (ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c mu).left) fun _ => -1)) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)).left ≫ Y.q.left] ![1, -1])), xp ≫ Y.q = Q.c mu → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z A₀ * (val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s α) (𝟙 Z) z J).val = cst (g ≫ jK R) z B₀ * (val (Q.tau mu α) g z J).val) → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val (Q.psi mu) g z J).val = cst (g ≫ jK R) z P₀ * (val ψ₀ (g ≫ jK R) z J).val) → (∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → val e y.left z J * val ψ₀ T.hom z J * val Q.rig T.hom z J * val ((Y.Φ T (y * (toUnit T ≫ xp⁻¹))).s mu) (𝟙 _) z J = 1) → ∀ (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k))), u.IsGen → LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left) (DegPre.famMult Q (FractionRing R) k mu α) → ∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (pp : Over.mk (g ≫ jK R) ⟶ DegPre.BF Q (FractionRing R)) (yp : Over.mk (g ≫ jK R) ⟶ Y.H), (pp ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R) = g → pp ≫ DegPre.prB Q (FractionRing R) = yp ≫ Y.q → ∀ (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z B₀ * (val u (show Z ⟶ _ from pp.left) z J).val * (val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 Z) z J).val * ((val e (show Z ⟶ Y.H.left from (yp * (toUnit _ ≫ xp)).left) z J) ^ k).val = cst (g ≫ jK R) z (P₀ ^ k * A₀) * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 Z) z J).val := by
  first | exact @GlobalTheory.ShiftUnit.shift_unit_identity | exact GlobalTheory.ShiftUnit.shift_unit_identity | (intros; apply GlobalTheory.ShiftUnit.shift_unit_identity <;> assumption)
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
open ReciprocityTheory.ChartRestriction.G.DVR

theorem _root_.GlobalTheory.T.exists_raynaudPoint_unitPart_coordinates : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (m : ℕ) (t : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), Q.TauBimult → (∀ i, t i ≠ 0) → ∀ (n : Q.X → Fin m → ℕ), (∀ χ i, gam i χ χ = 2 * n χ i) → ∀ (ψ₀ : ∀ χ : Q.X, LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c χ).left) fun _ => -1)), (∀ χ, (ψ₀ χ).IsGen) → (∀ χ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val (Q.psi χ) r z J).val = cst (r ≫ jK R) z (∏ i, t i ^ n χ i) * (val (ψ₀ χ) (r ≫ jK R) z J).val) → ∀ mu : Q.X, ∃ xp : 𝟙_ (Over (Sp R)) ⟶ Y.H, xp ≫ Y.q = Q.c mu ∧ ∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (χ : Q.X) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z (∏ i, t i ^ n (mu + χ) i) * (val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s χ) (𝟙 Z) z J).val = cst (g ≫ jK R) z (∏ i, t i ^ (n mu i + n χ i)) * (val (Q.tau mu χ) g z J).val := by
  first | exact @GlobalTheory.UnitPartPt.exists_unitPartPt | exact GlobalTheory.UnitPartPt.exists_unitPartPt | (intros; apply GlobalTheory.UnitPartPt.exists_unitPartPt <;> assumption)
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

namespace GlobalTheory.TanRay

open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv_mem mkT tv_mkT tanM_ext tv_add tv_smul)

theorem tanBasis_of_isPointOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∃ b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G), ∀ a, b a = v' a := by
  intro E _ _ _ H R _ _ _ _ _ _ t P
  letI := H.starRing
  intro Y n vH v' hv
  have hc : IsAdicComplete ((maximalIdeal R).map (algebraMap R (DualNumber R))) (DualNumber R) := by
    have : Module.Finite R (DualNumber R) := inferInstanceAs (Module.Finite R (R × R))
    exact GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal R) (DualNumber R)
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  have hT : GlobalTheory.AdicColimit.IsAdicColimit (maximalIdeal R) (overAt (𝟙 (Sp R)) (DualNumber R)) := by
    refine GlobalTheory.AdicColimit.IsAdicColimit.of_iso (Over.isoMk (Iso.refl _) ?_)
      (GlobalTheory.AdicColimit.isAdicColimit_spec_of_isLocalRing R (maximalIdeal R) (DualNumber R)
        (algebraMap R (DualNumber R)) hc)
    simp
  have hΦ := Y.rep
  obtain ⟨J, hJ⟩ := GlobalTheory.TorusModel.exists_mulEquiv P.U.toUnifPre GlobalTheory.allSixLaws.1.globalFns hΦ
  have nat : ∀ (k : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ overAt (𝟙 (Sp R)) (DualNumber R))
      (w : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ Y.H), J _ hT (k ≫ w) = k ≫ J _ hT w := fun k w =>
    (hJ _ hT _ _).2 (((hJ _ hT w _).1 rfl).pull k (hΦ.1 _ _ k _))
  have hs : ∀ (a : R) (w : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ Y.H),
      J _ hT (smT (𝟙 (Sp R)) a w) = smT (𝟙 (Sp R)) a (J _ hT w) := fun a w => nat _ w
  have mem : ∀ v : TanM (𝟙 (Sp R)) Y.H, smT (𝟙 (Sp R)) 0 (J _ hT (tv v)) = 1 := fun v => by
    rw [← hs, tv_mem, map_one]
  let L : TanM (𝟙 (Sp R)) Y.H →ₗ[R] TanM (𝟙 (Sp R)) t.G :=
    { toFun := fun v => mkT (J _ hT (tv v)) (mem v)
      map_add' := fun u v => tanM_ext (by
        simp only [tv_mkT, tv_add, map_mul])
      map_smul' := fun a v => tanM_ext (by
        simp only [tv_mkT, tv_smul, RingHom.id_apply, hs]) }
  have hL : Function.Bijective L := by
    refine ⟨fun u v h => tanM_ext ((J _ hT).injective ?_), fun w => ?_⟩
    · have := congrArg tv h
      simpa [L, tv_mkT] using this
    · have h0 : smT (𝟙 (Sp R)) 0 ((J _ hT).symm (tv w)) = 1 := by
        apply (J _ hT).injective
        rw [hs, MulEquiv.apply_symm_apply, tv_mem, map_one]
      refine ⟨mkT _ h0, tanM_ext ?_⟩
      show J _ hT ((J _ hT).symm (tv w)) = tv w
      exact MulEquiv.apply_symm_apply _ _
  refine ⟨vH.map (LinearEquiv.ofBijective L hL), fun a => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.ofBijective_apply]
  refine tanM_ext ?_
  exact (hJ _ hT _ _).2 (hv a)

end GlobalTheory.TanRay
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.PolDeg

theorem idlAlong_vanishingIdeal_compl (S : Scheme.{0}) (U : S.Opens) (R : Type) [CommRing R] [IsLocalRing R]
    (ξ : Sp R ⟶ S) (f : R) (hf : (Ideal.span {f}).IsRadical) (hU : ∀ p : Sp R, ξ p ∈ (U : Set S) ↔ f ∉ p.asIdeal)
    (hrad : ∀ I : Ideal (S.presheaf.stalk (ξ (closedPoint R))), I.IsRadical →
      (I.map (Scheme.stalkClosedPointTo ξ).hom).IsRadical) :
    idlAlong (Scheme.IdealSheafData.vanishingIdeal U.compl) ξ = Ideal.span {f} := by
  have hs := GlobalTheory.VanStalk.van_spec U.compl (ξ (closedPoint R))
  refine GlobalTheory.VanStalk.eq_of_forall_prime (hrad _ hs.1) hf fun q => ?_
  rw [idlAlong, Ideal.map_le_iff_le_comap, Ideal.span_singleton_le_iff_mem]
  refine (hs.2 (PrimeSpectrum.comap (Scheme.stalkClosedPointTo ξ).hom q)).symm.trans ?_
  have e := congrArg (fun g => g q) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)
  change (Spec.map (Scheme.stalkClosedPointTo ξ) ≫ S.fromSpecStalk (ξ (closedPoint R))) q ∈ (U.compl : Set S) ↔ _
  rw [e]
  change ξ q ∉ (U : Set S) ↔ _
  rw [hU q, not_not]

end GlobalTheory.PolDeg
end
end

section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.PullAlong

theorem idlAlong_comap_eq : ∀ {X Y : Scheme.{0}} (π : Y ⟶ X) (J : X.IdealSheafData) {R : Type} [CommRing R]
    [IsLocalRing R] (ξ : Sp R ⟶ Y), idlAlong (J.comap π) ξ = idlAlong J (ξ ≫ π) := by
  intro X Y π J R _ _ ξ
  unfold idlAlong
  rw [GlobalTheory.VanStalk.stalkId_comap, Ideal.map_map, Scheme.stalkClosedPointTo_comp]
  rfl

end GlobalTheory.PullAlong
end
end

section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

theorem _root_.GlobalTheory.T.mul_mem_cuspForms_of_boundedSection_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : Rul Xo c), Nonempty (KeySec Xo c) → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → 1 ≤ Dw.p + Dw.q → Even G₀.2 → (∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → G₀.1 (τ, j) ≤ G₀.1 (τ, i)) → s ∈ secZ Xo c (exZ Dw G₀) → s ∈ suppOn Z → (∀ σ, GoodEmb c σ → ∃ C : ℝ, ∀ z ∈ framesOn (U σ) Z, homN (U σ) x G₀ s z ≤ C) → ∀ G : WTZ E, Even G.2 → ∀ f ∈ cuspOn U Z G, f * s ∈ cuspOn U Z (G + G₀) := by
  first | exact @GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd | exact GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd | (intros; apply GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd <;> assumption)
end
