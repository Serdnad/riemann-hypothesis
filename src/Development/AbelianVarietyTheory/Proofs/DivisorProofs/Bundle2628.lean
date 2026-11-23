module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2602
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorIdealSheafPrincipalisingFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle013
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle633
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle655
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle654
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle050
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSecReadingDecreasingIntegerExponents
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle640
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle014
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Polynomial.Basic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.OrthonormalFlagTranslateHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle013
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle014
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective

@[expose] public section

section

set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatCore GlobalTheory.LineNorm GlobalTheory.FlatModel
open MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv actR)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FlatDenom

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

def IsProjMat {X : Scheme.{0}} (t : SAB H X) {R : Type} [CommRing R] (ξ : Sp R ⟶ X) (σ : 𝓞 E →+* R) {g : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (U : Matrix (Fin g) (Fin g) R) : Prop :=
  ∀ (S : Type) [CommRing S] (φ : R →+* S),
    EigRowsAt t (spMap φ ≫ ξ) (φ.comp σ) (bcV t φ e) (U.map φ) ∧
    ∀ w v, IsCombAtG t (spMap φ ≫ ξ) (bcV t φ e) w v → IsEigG t (φ.comp σ) v →
      Matrix.vecMul w (U.map φ) = ((discr E : ℤ) : S) • w


open GlobalTheory.FlatModel.Proj in
theorem exists_isProjMat {X : Scheme.{0}} {t : SAB H X} {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {g : ℕ}
    {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (he : IsTanBasis t ξ e) (σ : 𝓞 E →+* R) :
    ∃ U : Matrix (Fin g) (Fin g) R, IsProjMat t ξ σ e U := by
  classical
  let b := RingOfIntegers.basis E
  obtain ⟨c, hc1, hc2⟩ := exists_dual b (discr_ne_zero E)
  have hbas : ∀ w, IsTanAtG t ξ w → ∃ a, IsCombAtG t ξ e a w := fun w hw => by
    have h0 : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _
    have h1 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by
      have : dualMap (RingHom.id R) = RingHom.id _ := by ext s <;> simp [dualMap]
      rw [this]
      exact Spec.map_id _
    have := he.2 R (RingHom.id R) w (by rwa [h0, Category.id_comp])
    simp only [h0, h1, Category.id_comp] at this
    exact this.exists
  choose ρ hρ using fun (a : 𝓞 E) (k : Fin g) =>
    hbas _ (GlobalTheory.LieMet.isTan_tv (actR t.act a (GlobalTheory.LieMet.tanOf (he.1 k))))
  refine ⟨Matrix.of fun k j => ∑ i, σ (c i) * ρ (b i) k j, fun S _ φ => ?_⟩
  have he' := isTanBasis_bc he φ
  let T : Fin g → TanM (spMap φ ≫ ξ) t.G := fun j => GlobalTheory.LieMet.tanOf (he'.1 j)
  have hT : bcV t φ e = fun j => (tv (T j)).left := rfl
  have hA : ∀ a k, actR t.act a (T k) = ∑ j, φ (ρ a k j) • T j := fun a k => by
    refine (GlobalTheory.LieMet.isComb_iff T _ _).1 ?_
    have := GlobalTheory.GradedPieces.comb_map φ rfl (hρ a k)
    have e1 : spMap (dualMap φ) ≫ (tv (actR t.act a (GlobalTheory.LieMet.tanOf (he.1 k)))).left =
        (tv (actR t.act a (T k))).left := (Category.assoc _ _ _).symm
    rw [e1] at this
    exact this
  have hU : ∀ k, ∑ j, φ (∑ i, σ (c i) * ρ (b i) k j) • T j = ∑ i, (φ.comp σ) (c i) • actR t.act (b i) (T k) := fun k => by

    simp only [hA, map_sum, map_mul, Finset.sum_smul, Finset.smul_sum, smul_smul, RingHom.comp_apply]
    exact Finset.sum_comm
  refine ⟨fun k u hu a => ?_, fun w v hw hv => ?_⟩
  · rw [hT] at hu
    rw [eq_of_comb T hu, GlobalTheory.ShFam.Pad.Pull.eig_iff]
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [hU]
    exact eig_proj _ _ b c hc1 a _
  · rw [hT] at hw
    have hv0 := eq_of_comb T hw
    have hv1 : ∀ a, actR t.act a (∑ i, w i • T i) = (φ.comp σ) a • ∑ i, w i • T i := fun a => by
      rw [← GlobalTheory.ShFam.Pad.Pull.eig_iff, ← hv0]
      exact hv a
    have h2 := proj_eig _ _ b c hc2 _ hv1
    have h3 : ∑ j, (∑ k, w k • fun j => φ (∑ i, σ (c i) * ρ (b i) k j)) j • T j =
        ∑ j, (((discr E : ℤ) : S) • w) j • T j := by
      have h4 : ∑ j, (((discr E : ℤ) : S) • w) j • T j = ((discr E : ℤ) : S) • ∑ j, w j • T j := by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
      rw [h4]
      refine Eq.trans ?_ h2
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, hU]

      simp only [map_sum, map_smul, Finset.smul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    have hu := he.2 S φ _ (GlobalTheory.LieMet.isTan_tv (∑ j, (((discr E : ℤ) : S) • w) j • T j))
    have h5 := hu.unique ((GlobalTheory.LieMet.isComb_iff T _ _).2 rfl) ((GlobalTheory.LieMet.isComb_iff T _ _).2 h3.symm)
    rw [h5]
    funext j
    simp [Matrix.vecMul, dotProduct, Finset.sum_apply]

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def IsFrameCoord (Y : Model Xo c β) {R : Type} [CommRing R] (ξ : Sp R ⟶ Y.X) {g : ℕ}
    (e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)) (U : Matrix (Fin g) (Fin g) R) {k : Type} [CommRing k]
    [Algebra c.F k] (φ : R →+* k) (y : FrPt Xo c k) (σ : E →+* ℂ) (M : Matrix (Fin (Dw.mult σ)) (Fin g) k)
    (C : Matrix (Fin g) (Fin (Dw.mult σ)) k) : Prop :=
  (∀ i, ∃ w : Sp (DualNumber k) ⟶ Y.oF.t.G.left,
    w ≫ Y.oF.t.G.hom = spMap (algebraMap k (DualNumber k)) ≫ GlobalTheory.AllWt.ptF y ∧ w ≫ Y.m0.toSABMap.φ = y.u σ i ∧
      IsCombAtG Y.t (spMap φ ≫ ξ) (bcV Y.t φ e) (M i) (w ≫ Y.m.φ)) ∧
  C * M = U.map φ ∧ M * C = ((discr E : ℤ) : k) • (1 : Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) k)

def DetLaw (Z : Comp Xo c) (f : Rul Xo c) (σ₁ σ₂ : E →+* ℂ) : Prop :=
  IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f ∧
  ∀ (k : Type) [Field k] [Algebra c.F k] (z y : FrPt Xo c k), LiesOn Z y → z.x = y.x →
    ∀ (g₁ : Matrix (Fin (Dw.mult σ₁)) (Fin (Dw.mult σ₁)) k) (g₂ : Matrix (Fin (Dw.mult σ₂)) (Fin (Dw.mult σ₂)) k),
      (∀ i, IsCombAt y.x (y.u σ₁) (g₁ i) (z.u σ₁ i)) → (∀ i, IsCombAt y.x (y.u σ₂) (g₂ i) (z.u σ₂ i)) →
      evR Xo c f z * g₁.det = g₂.det * evR Xo c f y

theorem isPreimmersion_fst (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) :
    IsPreimmersion (pullback.fst Y.s (spMap (algebraMap (𝓞 c.F) c.F))) := by
  have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
  infer_instance

theorem isPreimmersion_j (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) : IsPreimmersion Y.j := by
  have := isPreimmersion_fst Y
  have := Y.jQ_open
  unfold Model.j
  infer_instance

end GlobalTheory.FlatDenom

end
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm

namespace GlobalTheory.CoverNorm

theorem unitAt_fnMap_of {X Z : Scheme.{0}} [IsIntegral X] [IsIntegral Z] (g : Z ⟶ X)
    (hη : g (genericPoint Z) ⤳ genericPoint X) {x : Z} {t : X.functionField} (h : UnitAt (g x) t) :
    UnitAt x (SmallSec.fnMap g hη t) := by
  have h0 : t ≠ 0 := h.ne_zero
  rw [unitAt_iff ((map_ne_zero _).2 h0), ← map_inv₀]
  exact ⟨ProjSpace.regAt_fnMap_of g hη h.regAt, ProjSpace.regAt_fnMap_of g hη h.inv.regAt⟩

end GlobalTheory.CoverNorm
end
end

section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem _root_.GlobalTheory.T.exists_denominatorIdealSheaf_principalising_family : ∀ (Y : Scheme.{0}) [IsIntegral Y] (N : ℕ) (w : Fin (N + 1) → Y.functionField) (i₀ : Fin (N + 1)) (U : Y.Opens),
    w i₀ = 1 → (∀ y ∈ U, ∃ k, w k ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y (w j / w k)) →
    ∃ I : Y.IdealSheafData, I ≠ ⊥ ∧ (∀ y ∈ U, y ∉ I.support) ∧
      ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (s : Y' ⟶ Y) (hη : s (genericPoint Y') = genericPoint Y),
        ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (I.comap s) → ∀ y' : Y', ∃ k,
          GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k) ≠ 0 ∧ ∀ j, GlobalTheory.Cartier.RegAt y'
            (GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w j) / GlobalTheory.TrueGeo.SmallSec.fnMap s (specializes_of_eq hη) (w k)) := by
  first | exact @GlobalTheory.DenomIdeal.exists_idealSheaf | exact GlobalTheory.DenomIdeal.exists_idealSheaf | (intros; apply GlobalTheory.DenomIdeal.exists_idealSheaf <;> assumption)
end

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine
open GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects GlobalTheory.Reg

namespace GlobalTheory.KeyFourth

theorem prod_zpow_four_smul_keyEx {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {S : Type} [CommRing S] (t : Ix Dw → Sˣ) :
    (∏ i, t i ^ ((4 : ℤ) • keyEx Dw) i) = kch t ^ 4 := by
  rw [kch, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_comm, zpow_mul]
  norm_cast


set_option maxHeartbeats 1000000 in
theorem exists_unit_secZ_keyRule : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.FamUnit κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)), 1 ≤ Dw.p + Dw.q → ∃ K : (Rul Xo c)ˣ, (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) ∧ (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) := by
  set_option synthInstance.maxHeartbeats 200000 in
    intro κ h₁ h₂ h₃ E _ _ _ H Dw l Xo c g e hpq
    obtain ⟨hL, -, h, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
    have hex : ∃ v : ∀ Z : Comp Xo c, (Om Z)ˣ, ∀ C : FChart h,
        ∃ (Φ : FibKey Xo C.R C.y.x) (u : (C.R)ˣ), Tied e C.y.s C.y.u Φ ∧ GlobalTheory.KeyCl.IsValue κ Φ.key (u : C.R) ∧
          ((u : C.R) : Om C.Z) = ((kch C.t ^ 4 * v C.Z : (Om C.Z)ˣ) : Om C.Z) := by
      have hc : ∀ Z : Comp Xo c, CharZero (Om Z) := fun Z =>
        charZero_of_injective_algebraMap (algebraMap c.F (Om Z)).injective
      choose Ψ hΨ using fun Z : Comp Xo c => GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e (Om Z) (genFr h Z) hpq
      refine ⟨fun Z => κ (Om Z) (Ψ Z).key, fun C => ?_⟩
      haveI := C.sm
      haveI : IsIntegrallyClosed C.R := isIntegrallyClosed_of_smooth c.F C.R
      haveI : IsNoetherianRing C.R := Algebra.FiniteType.isNoetherianRing c.F C.R
      haveI : CharZero C.R := charZero_of_injective_algebraMap (algebraMap c.F C.R).injective
      obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e C.R C.y hpq
      obtain ⟨Φ', hΦ'⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e (Om C.Z) C.yg hpq
      obtain ⟨u, hu⟩ := h₃ C.R Φ.key
      refine ⟨Φ, u, hΦ, hu, ?_⟩
      rw [← GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power κ h₁ h₂ E H Dw l Xo c g e (Om C.Z) C.t _ _ (Ψ C.Z) Φ' C.bor (hΨ _) hΦ']
      exact (hu (Om C.Z) _ _ (GlobalTheory.T.universal_triple_fibres_base_change_key_data E H Dw l Xo c g e _ _ C.R.val C.y C.yg Φ Φ' C.gen hΦ hΦ')).symm
    obtain ⟨v, hv⟩ := hex
    obtain ⟨f, hf, hfb⟩ := GlobalTheory.T.exists_integer_exponent_section_of_chart_regular E H Dw l Xo c h ((4 : ℤ) • keyEx Dw) (fun Z => (v Z : Om Z)) fun C => by
      obtain ⟨-, u, -, -, huv⟩ := hv C
      rw [prod_zpow_four_smul_keyEx, ← Units.val_mul, ← huv]
      exact (u : C.R).2
    obtain ⟨f', hf', hfb'⟩ := GlobalTheory.T.exists_integer_exponent_section_of_chart_regular E H Dw l Xo c h (-((4 : ℤ) • keyEx Dw))
        (fun Z => (((v Z)⁻¹ : (Om Z)ˣ) : Om Z)) fun C => by
      obtain ⟨-, u, -, -, huv⟩ := hv C
      have hm : Units.map (C.R.val : C.R →* Om C.Z) u = kch C.t ^ 4 * v C.Z := Units.ext huv
      have hp : (∏ i, C.t i ^ (-((4 : ℤ) • keyEx Dw)) i) = (kch C.t ^ 4)⁻¹ := by
        rw [← prod_zpow_four_smul_keyEx, ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [Pi.neg_apply, zpow_neg]
      have hq : (kch C.t ^ 4)⁻¹ * (v C.Z)⁻¹ = Units.map (C.R.val : C.R →* Om C.Z) u⁻¹ := by
        rw [map_inv, hm, mul_inv_rev, mul_comm]
      rw [hp, ← Units.val_mul, hq]
      exact ((u⁻¹ : (C.R)ˣ) : C.R).2
    have h0 : GlobalTheory.AllWt.secZ Xo c 0 = sec Xo c 0 0 := by
      rw [← GlobalTheory.AllWt.secZ_nat]
      congr 1
      funext i
      cases i <;> rfl
    have hm := GlobalTheory.AllWt.mul_mem_secZ hf hf'
    rw [add_neg_cancel, h0] at hm
    have h1 := GlobalTheory.AllWt.one_mem_secZ (Xo := Xo) (c := c)
    rw [h0] at h1
    have hff : f * f' = 1 := by
      refine sub_eq_zero.1 (sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _ (sub_mem hm h1) fun Z => ?_)
      have e₁ : evC h Z (f * f') = evC h Z f * evC h Z f' := by simp only [evC, evR, evalAt_mul]
      have e₂ : evC h Z (1 : Rul Xo c) = 1 := evalAt_one _ _ _ (hL.test _ _)
      have e₃ := (evalL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (genFr h Z)).map_sub
        (f * f') 1
      refine e₃.trans ?_
      change evC h Z (f * f') - evC h Z 1 = 0
      rw [e₁, e₂, hfb, hfb', Units.mul_inv, sub_self]
    refine ⟨⟨f, f', hff, (mul_comm _ _).trans hff⟩, hf, ?_⟩
    intro F _ _ _ y Φ hΦ
    change evR Xo c f y = _
    obtain ⟨C, ψ, z, t', hz, hb⟩ := hA h F y
    obtain ⟨ΦC, u, hΦC, hu, huv⟩ := hv C
    obtain ⟨p, a, u₀, hu₀⟩ := hL.test C.R C.y
    have k₁ : evR Xo c f C.yg = C.R.val (evR Xo c f C.y) := by
      rw [GlobalTheory.FlagTan.evR_eq hf.1 hu₀, GlobalTheory.FlagTan.evR_eq hf.1 (GlobalTheory.FlagTan.frMap_comp (χ := C.R.val.comp a) hu₀ C.gen fun _ => rfl)]
      rfl
    have k₂ : evR Xo c f C.yg = ((u : C.R) : Om C.Z) := by
      rw [GlobalTheory.FlagTan.evR_frBor hf C.bor, prod_zpow_four_smul_keyEx, huv]
      have := hfb C.Z
      simp only [evC] at this
      rw [this, Units.val_mul]
    have k₃ : evR Xo c f C.y = (u : C.R) := Subtype.val_injective (k₁.symm.trans k₂)
    have k₄ : evR Xo c f z = ψ (u : C.R) := by
      rw [GlobalTheory.FlagTan.evR_eq hf.1 (GlobalTheory.FlagTan.frMap_comp (χ := ψ.comp a) hu₀ hz fun _ => rfl), ← k₃, GlobalTheory.FlagTan.evR_eq hf.1 hu₀]
      rfl
    obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.exists_universalTripleFibre_at_framedPoint E H Dw l Xo c g e F z hpq
    have k₅ := GlobalTheory.T.theta_key_rule_triangular_frame_change_fourth_power κ h₁ h₂ E H Dw l Xo c g e F t' z y Ψ Φ hb hΨ hΦ
    have k₆ : (κ F Ψ.key : F) = ψ (u : C.R) :=
      hu F ψ.toRingHom Ψ.key (GlobalTheory.T.universal_triple_fibres_base_change_key_data E H Dw l Xo c g e C.R F ψ C.y z ΦC Ψ hz hΦC hΨ)
    rw [GlobalTheory.FlagTan.evR_frBor hf hb, prod_zpow_four_smul_keyEx, k₄, k₅, Units.val_mul, k₆]

end GlobalTheory.KeyFourth
end
end

section

noncomputable section

namespace GlobalTheory.KeyArchNorm

section Value

open AlgebraicGeometry CategoryTheory Limits NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth

theorem norm_rule_of_coord {κ : GlobalTheory.KeyCl.Rule} (hκ : GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ) (x : KeyIn ℂ) {g : ℕ}
    (hg : g = x.P.g) (u : HolUnif x.P.A x.P.L g) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    {θ : (Fin g → ℂ) → ℂ} {Fd : Set (Fin g → ℂ)} {ξ : ℝ} (hξ : 0 < ξ) (p : Fin x.P.g ≃ Fin g)
    (hA : u.IsAH Hm χ) (hR : u.IsRig x.rig) (hF : u.IsFn x.th θ) (hD : ∀ i, u.IsDiff (Pi.single (p i) 1) (x.v i))
    (hFd : IsAddFundamentalDomain u.Λ Fd volume)
    (hN : (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (hermForm Hm z z).re)) / (volume Fd).toReal = 1)
    (hH : Hm = ((2 * ξ : ℝ) : ℂ) • (1 : Matrix (Fin g) (Fin g) ℂ)) :
    ‖(κ ℂ x : ℂ)‖ = (2 * Real.pi) ^ (2 * g) * (2 * Real.pi * ξ) ^ (2 * g) := by
  subst hg
  obtain ⟨⟨Ef, hE, hb⟩, -⟩ := unimodular_and_tangent_of_isAH thetaUnifAV_all x.P x.rig x.rig_gen u Hm χ hA
  have := u.discrete
  have hv := volume_mul_det_eq_one_of_unimodular _ u.Λ u.full Hm Ef Fd hA.1 hA.2.1 hE hb hFd
  have hd : Hm.det.re = (2 * ξ) ^ x.P.g := by
    rw [hH, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin, ← Complex.ofReal_pow, Complex.ofReal_re]
  let W : Matrix (Fin x.P.g) (Fin x.P.g) ℂ := Matrix.of fun i => Pi.single (p i) 1
  have hW : ‖W.det‖ = 1 := by
    have e : W = (1 : Matrix (Fin x.P.g) (Fin x.P.g) ℂ).submatrix p id := by
      ext i j
      simp [W, Pi.single_apply, Matrix.one_apply, eq_comm]
    rw [e, Matrix.det_permute, Matrix.det_one, mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign p) with h | h <;> simp [h]
  have key := hκ x u Hm W χ θ Fd 1 _ hA hR hF hD hFd hN.symm rfl
  rw [hd] at hv
  rw [hW, eq_inv_of_mul_eq_one_left hv] at key
  have hπ := Real.pi_pos
  simp only [mul_one, one_pow] at key
  rw [← key]
  simp only [mul_pow, pow_mul']
  field_simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem norm_rule_of_isOrtho {κ : GlobalTheory.KeyCl.Rule} (hκ : GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ) {g : ℕ}
    (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {ξ : ℝ} (h0 : 0 < ξ)
    (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp) (x : (U.X k).dom) (hξ : ∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = ξ)
    (hx : (U.X k).IsOrtho x.1) (Φ : FibKey Xo ℂ (U.un k x).x)
    (hΦ : Tied (S := ℂ) e (U.un k x).s (U.un k x).u Φ) :
    ‖(κ ℂ Φ.key : ℂ)‖ = (2 * Real.pi) ^ (2 * g) * (2 * Real.pi * ξ) ^ (2 * g) := by
  obtain ⟨ht, hg, hv⟩ := hΦ
  subst hg
  obtain ⟨W⟩ := PullbackSections.nonempty_unfAt hU k x
  obtain ⟨Wu⟩ := PullbackSections.nonempty_unitAt W (PullbackSections.PfSupAtUnit.dmin_ortho _ hx)
  have hH := OrthoHerm.hm_eq_smul_one E H Dw l Xo c σ r U ξ hσ hU k x W Wu hξ hx
  obtain ⟨u, χ, hΛ, hA, hR, hF, hg, hD⟩ := OrthoMetric.exists_unif W.F (W.ik k) W.per W.pt Φ ht Wu.herm Wu.pos Wu.c2
    Wu.c3 Wu.c4 Wu.c5 Wu.c6 Wu.c7
  have hFd : IsAddFundamentalDomain u.Λ Wu.Fd volume := hΛ ▸ Wu.c8
  have key := norm_rule_of_coord hκ Φ.key hg u h0 (e.trans W.e.symm) hA hR hF (fun i => by
    obtain ⟨w, hw, hd⟩ := hD _ _ ((U.un k x).tan (e i).1 (e i).2) (W.der (e i).1 (e i).2)
    have hwv : w = Φ.v i :=
      Over.OverMorphism.ext (Φ.m.cart.1.hom_ext (hw.trans (hv i).symm) ((Over.w w).trans (Over.w (Φ.v i)).symm))
    rw [hwv] at hd
    exact hd) hFd Wu.c9 hH
  rw [hg] at key
  exact key

end Value

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

section Weight

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem wtOf_fst (τ : E →+* ℂ) (i : ℕ) (hi : i < Dw.mult τ) : (wtOf Dw 0 (-4)).1 (τ, i) = 4 := by
  by_cases h : τ (H.rt : E) = H.rt0
  · have hp : i < Dw.p := by simpa [Datum.mult, h] using hi
    rw [wtOf_big _ _ ⟨τ, h⟩ i hp]
    simp
  · have hq : i < Dw.q := by simpa [Datum.mult, h] using hi
    have e := wtOf_small (Dw := Dw) 0 (-4) ⟨conjEmb τ, conj_mem h⟩ i hq
    simp only [_root_.GlobalTheory.AllWt.conjEmb_conjEmb] at e
    rw [e]
    simp

theorem exZ_wtOf : exZ Dw (wtOf Dw 0 (-4)) = (4 : ℤ) • keyEx Dw := by
  funext i
  rcases i with _ | ⟨τ, i⟩
  · rfl
  · exact wtOf_fst τ i i.2

theorem lieFacZ_mul {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) {x : ℝ} (hx : 0 < x) :
    lieFacZ Dw x (wtOf Dw 0 (-4)) * (2 * Real.pi * x) ^ (2 * g) = 1 := by
  have hg : ∑ τ : E →+* ℂ, Dw.mult τ = g := by
    have := Fintype.card_congr e
    simpa using this.symm
  have hs : (∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), ((wtOf Dw 0 (-4)).1 (τ, i) : ℝ)) = 4 * g := by
    rw [← hg, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_congr rfl fun (i : Fin (Dw.mult τ)) _ => by rw [wtOf_fst τ i i.2]]
    simp [mul_comm]
  have hπ : 0 < 2 * Real.pi * x := by positivity
  rw [lieFacZ, hs, ← Real.exp_log (pow_pos hπ (2 * g)), ← Real.exp_add, Real.log_pow, Real.exp_eq_one_iff]
  push_cast
  ring

end Weight

theorem homN_key_const : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.KeyCl.Homog (fun _ => 1) κ → GlobalTheory.KeyCl.Funct κ → GlobalTheory.KeyCl.ArchNorm (fun _ => 1) κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (x : ℝ) (K : (Rul Xo c)ˣ), GoodEmb c σ → IsUnf U → (∀ k (τ : E →+* ℂ), ‖τ (U.X k).ξ0‖ = x) → Nonempty (KeySec Xo c) → 1 ≤ Dw.p + Dw.q → (K : Rul Xo c) ∈ secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∃ C : ℝ, 0 < C ∧ |Real.log C| ≤ 2 * (g : ℝ) * Real.log (2 * Real.pi) ∧ ∀ k, ∀ y ∈ (U.X k).dom, homN U x (wtOf Dw 0 (-4)) (K : Rul Xo c) ⟨k, y⟩ = C := by
  intro κ _ _ hκ E _ _ _ H Dw l Xo c g e σ r U x K hσ hU hx hS hpq hK hval
  have hπ : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  refine ⟨(2 * Real.pi) ^ (2 * g), by positivity, ?_, fun k y hy => ?_⟩
  · rw [abs_of_nonneg (Real.log_nonneg (one_le_pow₀ hπ)), Real.log_pow]
    push_cast
    exact le_rfl
  have hsec := GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU E H Dw l Xo c σ r U hS hσ hU hpq (wtOf Dw 0 (-4)) (even_wtOf _ _)
    (fun τ i j hij hj => by rw [wtOf_fst τ j hj, wtOf_fst τ i (hij.trans_lt hj)]) K (exZ_wtOf (Dw := Dw) ▸ hK) k
  have hb := FrameDegreeData.bOf_mem (U.X k) hy
  have hz := OrthogonalFrameDomain.rmul_mem_dom (U.X k) hy hb
  have ho := FrameDegreeData.ortho_bOf (U.X k) hy
  have hp := FrameDegreeData.pnorm_rmul (U.X k) _ _ hsec.2.1 y hy _ hb
  generalize rmul y (FrameDegreeData.bOf (U.X k) y) = z at hz ho hp
  obtain ⟨τ₀⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h0 : 0 < x := hx k τ₀ ▸ norm_pos_iff.2 ((map_ne_zero τ₀).2 (U.X k).ξ0_ne)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : FibKey Xo ℂ (U.un k ⟨z, hz⟩).x, Tied (S := ℂ) e (U.un k ⟨z, hz⟩).s (U.un k ⟨z, hz⟩).u Φ :=
    @GlobalTheory.KeyFourth.exists_tied E _ _ _ H Dw l Xo c g e ℂ _ _ σ.toAlgebra (U.un k ⟨z, hz⟩) hpq
  have hv : rdU U (K : Rul Xo c) k z = (κ ℂ Φ.key : ℂ) := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hz, dif_pos]
    exact @hval ℂ _ _ σ.toAlgebra (U.un k ⟨z, hz⟩) Φ hΦ
  have hn : (U.X k).pnorm (modelWt U (wtOf Dw 0 (-4)) k) (rdU U (K : Rul Xo c) k) z = ‖(κ ℂ Φ.key : ℂ)‖ := by
    simp [Data.pnorm, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho _ ho, hv]
  show lieFacZ Dw x _ * (U.X k).pnorm (modelWt U (wtOf Dw 0 (-4)) k) (rdU U (K : Rul Xo c) k) y = _
  rw [← hp, hn, norm_rule_of_isOrtho hκ e h0 hσ hU k ⟨z, hz⟩ (hx k) ho Φ hΦ, mul_left_comm, lieFacZ_mul e h0, mul_one]

end GlobalTheory.KeyArchNorm
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.de_rham_to_h1_structure_surjective_abelian : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) := by
  first | exact @GlobalTheory.PtExt.toH1O_surjective_of_abelian | exact GlobalTheory.PtExt.toH1O_surjective_of_abelian | (intros; apply GlobalTheory.PtExt.toH1O_surjective_of_abelian <;> assumption)
end
