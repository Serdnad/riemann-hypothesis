module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle104
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle707
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle702
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle703
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IntegralOfPullAl
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SquareOfGeneric

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CechPic

section Pt

variable {S : Scheme.{0}} {G : Over S} [GrpObj G]

theorem pull_one_eq_zero (L : RigLB G) {T : Over S} :
    pull (1 : T ⟶ G).left (cls L.L L.isLB) = 0 := by
  have a := (cls_eq_zero_iff (pull_isLB L.isLB (eSec G))).2 ⟨L.rig, L.rigGen⟩
  rw [cls_pull L.isLB] at a
  rw [Hom.one_def, Over.comp_left, pull_comp]
  change pull _ (pull (eSec G) _) = 0
  rw [a, map_zero]

theorem pull_inv (L : RigLB G) (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]))
    (hs : s.IsGen) {T : Over S} (x : T ⟶ G) :
    pull x⁻¹.left (cls L.L L.isLB) = pull x.left (cls L.L L.isLB) := by
  have e := (cls_eq_zero_iff (LB.isLB_linComb L.isLB _ _)).2 ⟨s, hs⟩
  rw [cls_linComb L.isLB, Fin.sum_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, pull_id, one_smul, neg_smul] at e
  have e' : pull (ι[G]).left (cls L.L L.isLB) = cls L.L L.isLB := by
    rw [← sub_eq_zero, sub_eq_add_neg]; exact e
  rw [Hom.inv_def, Over.comp_left, pull_comp, e']

theorem lam_self [IsCommMonObj G] (L : RigLB G) (hΘ : ∃ t : LB.Gen (Theta G L.L), t.IsGen)
    (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs : s.IsGen)
    {T : Over S} (x : T ⟶ G) :
    lam (cls L.L L.isLB) x x = 2 • pull x.left (cls L.L L.isLB) := by
  have h := lam_mul_left L.isLB hΘ x⁻¹ x x
  rw [inv_mul_cancel, lam_one_left] at h
  have h2 : lam (cls L.L L.isLB) x⁻¹ x = - pull x⁻¹.left (cls L.L L.isLB) - pull x.left (cls L.L L.isLB) := by
    simp only [lam, inv_mul_cancel, pull_one_eq_zero]; abel
  calc lam (cls L.L L.isLB) x x
      = (lam (cls L.L L.isLB) x⁻¹ x + lam (cls L.L L.isLB) x x) - lam (cls L.L L.isLB) x⁻¹ x := by abel
    _ = 2 • pull x.left (cls L.L L.isLB) := by rw [← h, h2, pull_inv L s hs]; abel

theorem lam_pull_fst {S' : Scheme.{0}} (f : S' ⟶ S) (c : Pic G.left) {T : Over S'}
    (x y : T ⟶ (Over.pullback f).obj G) :
    lam (CechPic.pull (pullback.fst G.hom f) c) x y =
      lam c (pushPt (isGrpPullback_pullback G f).1.w x) (pushPt (isGrpPullback_pullback G f).1.w y) := by
  have h := isGrpPullback_pullback G f
  have e1 : (x * y).left ≫ pullback.fst G.hom f = (pushPt h.1.w x * pushPt h.1.w y).left :=
    congrArg (fun z => z.left) (map_mul (pushHom h T) x y)
  have e0 : (1 : T ⟶ (Over.pullback f).obj G).left ≫ pullback.fst G.hom f = (1 : Over.mk (T.hom ≫ f) ⟶ G).left :=
    congrArg (fun z => z.left) (map_one (pushHom h T))
  simp only [lam, ← pull_comp, e1, e0]
  rfl

end Pt

end GlobalTheory.SquareOfGeneric

namespace GlobalTheory.SquareOfGeneric

open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CechPic

theorem diag_lam_eq (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G]
    [IsCommMonObj G] (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R)))
    (U : Unif (maximalIdeal R) D A G) (L : LB ((Over.pullback (jK R)).obj G).left) (hL : L.IsLB)
    (eL : LBIso L (U.LG.L.pull (pullback.fst G.hom (jK R))))
    (h : (abelian₂ ((Over.pullback (jK R)).obj G) L).IsLB) :
    CechPic.pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G))).left
        (cls _ h) = 2 • CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L U.LG.isLB) := by
  have e₁ : cls _ h = lam (cls L hL) (fst _ _) (snd _ _) := cls_cube_two hL _ _ h
  have e₂ : cls L hL = CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L U.LG.isLB) :=
    (cls_eq_iff hL (pull_isLB U.LG.isLB _)).2 eL
  rw [e₁, pull_lam, lift_fst, lift_snd, e₂, lam_pull_fst,
    lam_self U.LG ⟨U.cubG.t, U.cubG.isGen⟩ U.symG U.symG_gen]
  rfl

end GlobalTheory.SquareOfGeneric

open GlobalTheory.CechPic MonoidalCategory CartesianMonoidalCategory MonObj in
theorem GlobalTheory.squares_iso_of_lam_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G) (L L' : LB ((Over.pullback (jK R)).obj G).left), L.IsLB → L'.IsLB → LBIso L (U.LG.L.pull (pullback.fst G.hom (jK R))) → LBIso L' (U'.LG.L.pull (pullback.fst G.hom (jK R))) → LBIso (abelian₂ ((Over.pullback (jK R)).obj G) L) (abelian₂ ((Over.pullback (jK R)).obj G) L') → LBIso (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) := by
  intro R _ _ _ hR G _ _ hG D D' A A' U U' L L' hL hL' eL eL' eΛ
  have hΛ := (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL' _ _)).2 eΛ
  have key := congrArg (CechPic.pull (lift (𝟙 ((Over.pullback (jK R)).obj G))
    (𝟙 ((Over.pullback (jK R)).obj G))).left) hΛ
  have k₁ := GlobalTheory.SquareOfGeneric.diag_lam_eq R G D A U L hL eL (LB.isLB_linComb hL _ _)
  have k₂ := GlobalTheory.SquareOfGeneric.diag_lam_eq R G D' A' U' L' hL' eL' (LB.isLB_linComb hL' _ _)
  replace key := k₁.symm.trans (key.trans k₂)
  refine GlobalTheory.T.lineBundleIso_of_generic_iso_normal_local_base R hR.1 hR.2.1 G.left G.hom (eSec G) hG.smooth hG.quasiCompact
    (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hG.smooth hG.geomConnected)
    (Over.w η[G]) _ _ (LB.isLB_linComb U'.LG.isLB _ _) (LB.isLB_linComb U.LG.isLB _ _) ?_
  refine (cls_eq_iff (pull_isLB (LB.isLB_linComb U'.LG.isLB _ _) _) (pull_isLB (LB.isLB_linComb U.LG.isLB _ _) _)).1 ?_
  rw [cls_pull (LB.isLB_linComb U'.LG.isLB _ _), cls_pull (LB.isLB_linComb U.LG.isLB _ _),
    cls_linComb U'.LG.isLB, cls_linComb U.LG.isLB]
  simp only [Fin.sum_univ_one, pull_id, map_zsmul]
  rw [two_zsmul, two_zsmul, ← two_nsmul, ← two_nsmul]
  exact key.symm
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.complexMatrix_eq_of_hermForm_im_eq_real_span : ∀ (g r : ℕ) (Hm Hm' : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ), Submodule.span ℝ (Set.range l) = ⊤ → (∀ i j, (hermForm Hm (l i) (l j)).im = (hermForm Hm' (l i) (l j)).im) → Hm = Hm' := by
  first | exact @GlobalTheory.hermForm_eq_of_im_eq_on_span | exact GlobalTheory.hermForm_eq_of_im_eq_on_span | (intros; apply GlobalTheory.hermForm_eq_of_im_eq_on_span <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.hermForm_im_intMatrix_transpose_neg : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (l : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℤ), Hm.IsHermitian → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → Mᵀ = -M := by
  first | exact @GlobalTheory.hermForm_im_antisymm | exact GlobalTheory.hermForm_im_antisymm | (intros; apply GlobalTheory.hermForm_im_antisymm <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PsiFourth

theorem key : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + 2 • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (mu α : D'.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D'.toPre.P.A) (z : T.left) (J : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D'.toPre.P.L z J → sval (f' (α + 2 • mu)) y.left z J = sval (f' α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D'.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D'.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2) → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2) → (¬ ∀ j, (f 0).f j = 0) → ∀ (y : D'.toPre.X) (r r' : R), PsiCoord D.toPre (xe (2 • y)) r → PsiCoord D'.toPre (2 • y) r' → Associated (r ^ 4) (r' ^ 4) := by
  intro R _ _ _ hR D D' Φ w hw hΦ xe hc f f' hf hf' hcorr hcub hne y r r' hr hr'
  have := D.toPre.P.isAb.smooth
  have := D.toPre.P.isAb.geomConnected
  haveI : IsIntegral (DegPre.BF D.toPre (FractionRing R)).left :=
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D.toPre.P.A.hom).geometrically_isIntegral
      (TF (R := R) (FractionRing R)).hom _ _ (IsPullback.of_hasPullback _ D.toPre.P.A.hom).flip
  have ne : ∀ J, Geo.Tor.Good D.toPre.P.L (genericPoint (DegPre.BF D.toPre (FractionRing R)).left) J →
      sval (f 0) (DegPre.prB D.toPre (FractionRing R)).left (genericPoint (DegPre.BF D.toPre (FractionRing R)).left) J ≠ 0 := by
    intro J hJ h0
    apply hne
    have hL := D.toPre.P.isLB
    have inj := PullIntegral.prB_app_injective D.toPre (FractionRing R)
    have e₀ := ThetaScalar.eq_zero_of_germ (H1.SectionArithmetic.pullSec (f 0) (DegPre.prB D.toPre (FractionRing R)).left) _ hJ
      (by rw [H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ, Category.id_comp, h0])
    exact fun j => PullIntegral.sec_ext_of_inj hL _ inj (s' := ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secZero) (fun y J hJ => by
      have := ThetaScalar.sval_eq_zero _ e₀ (𝟙 _) y hJ
      rw [H1.SectionArithmetic.sval_pullSec _ _ _ y hJ] at this
      rw [this]
      exact (ThetaScalar.sval_eq_zero ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secZero (fun _ => rfl) _ y hJ).symm) j
  exact GlobalTheory.T.psi_coordinates_fourthPower_associated R D D' Φ w hw (xe (2 • y)) (2 • y) _
    (fun J J' hJ hJ' => GlobalTheory.T.weightTwoFactor_sq_values_correspond R D D' Φ w hΦ xe hc f f' hf hf' hcorr hcub y _ J J' hJ hJ'
      inferInstance (ne J hJ)) r r' hr hr'

end GlobalTheory.PsiFourth
end

end

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.isMonHom_of_squaredDegenerationData_functionalEquation : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + 2 • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (mu α : D'.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D'.toPre.P.A) (z : T.left) (J : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D'.toPre.P.L z J → sval (f' (α + 2 • mu)) y.left z J = sval (f' α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D'.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D'.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2) → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2) → (¬ ∀ j, (f 0).f j = 0) → ∀ (y : D'.toPre.X) (r r' : R), PsiCoord D.toPre (xe (2 • y)) r → PsiCoord D'.toPre (2 • y) r' → Associated (r ^ 4) (r' ^ 4) := by
  first | exact @GlobalTheory.PsiFourth.key | exact GlobalTheory.PsiFourth.key | (intros; apply GlobalTheory.PsiFourth.key <;> assumption)

end
end
