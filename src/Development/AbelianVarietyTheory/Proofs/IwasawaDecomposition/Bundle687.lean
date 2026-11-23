module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle122
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle039
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.CancelSecAct
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle678
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle003
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle540
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle010
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle035
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle027
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle034
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle624
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqDescend

variable {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem wchart_sq_le (φ : K → (Y ⟶ X)) (p : K → Fin 1 → L.ι) :
    LB.wchart (SqLB.sq L) φ p ≤ LB.wchart L φ (fun k => p k 0) :=
  fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) 0

theorem gm_sq_g' (f : Y ⟶ X) (y : Y) (j j' : Fin 1 → L.ι) (hj : f y ∈ (SqLB.sq L).U j)
    (hj' : f y ∈ (SqLB.sq L).U j') :
    gm f y ((SqLB.sq L).U j ⊓ (SqLB.sq L).U j') ((SqLB.sq L).g j j') =
      gm f y (L.U (j 0) ⊓ L.U (j' 0)) (L.g (j 0) (j' 0)) ^ (2 : ℤ) := by
  obtain ⟨a, rfl⟩ : ∃ a, j = fun _ => a := ⟨j 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  obtain ⟨b, rfl⟩ : ∃ b, j' = fun _ => b := ⟨j' 0, funext fun i => by rw [Subsingleton.elim i 0]⟩
  exact SqLB.gm_sq_g f y (Set.mem_iInter.1 hj 0) (Set.mem_iInter.1 hj' 0)

theorem gs_sub (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a - b) = gs f y U a - gs f y U b := by simp only [gs_eq f y U h, map_sub]

theorem gs_zero (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

theorem trF_sq (φ : K → (Y ⟶ X)) (ε : K → ℤ) (y : Y) (p p' : K → Fin 1 → L.ι)
    (hy : y ∈ LB.wchart (SqLB.sq L) φ p ⊓ LB.wchart (SqLB.sq L) φ p') :
    (∏ k, gm (𝟙 Y ≫ φ k) y ((SqLB.sq L).U (p k) ⊓ (SqLB.sq L).U (p' k)) ((SqLB.sq L).g (p k) (p' k)) ^ ε k) =
      trF φ ε (𝟙 Y) y (fun k => p k 0) (fun k => p' k 0) ^ 2 := by
  simp only [trF]
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [gm_sq_g' (𝟙 Y ≫ φ k) y (p k) (p' k) (Set.mem_iInter.1 hy.1 k) (Set.mem_iInter.1 hy.2 k), ← zpow_mul, ← zpow_natCast,
    ← zpow_mul]
  congr 1
  push_cast
  ring

def sqSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) :
    LB.Sec (LB.LinComb (SqLB.sq L) φ ε) where
  f := fun p => (Y.presheaf.map (homOfLE (wchart_sq_le φ p)).op).hom (s.f (fun k => p k 0)) *
    (Y.presheaf.map (homOfLE (wchart_sq_le φ p)).op).hom (s.f (fun k => p k 0))
  compat := fun p p' => fn_ext fun y hy => by
    have h₁ := wchart_sq_le φ p hy.1
    have h₂ := wchart_sq_le φ p' hy.2
    have eA : gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (wchart_sq_le φ p)).op).hom (s.f (fun k => p k 0))) =
        gs (𝟙 Y) y (LB.wchart L φ (fun k => p k 0)) (s.f (fun k => p k 0)) := gs_res (𝟙 Y) y _ hy.1 _
    have eB : gs (𝟙 Y) y _ ((Y.presheaf.map (homOfLE (wchart_sq_le φ p')).op).hom (s.f (fun k => p' k 0))) =
        gs (𝟙 Y) y (LB.wchart L φ (fun k => p' k 0)) (s.f (fun k => p' k 0)) := gs_res (𝟙 Y) y _ hy.2 _
    have eL := (gs_res (𝟙 Y) y inf_le_left hy _).trans ((gs_mul (𝟙 Y) y _ hy.1 _ _).trans (congrArg₂ (· * ·) eA eA))
    have eR := (gs_mul (𝟙 Y) y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit (𝟙 Y) y _ hy _).trans
      (congrArg Units.val ((gm_linComb (SqLB.sq L) φ ε (𝟙 Y) y p p' hy.1 hy.2).trans (trF_sq φ ε y p p' hy))))
      ((gs_res (𝟙 Y) y inf_le_right hy _).trans ((gs_mul (𝟙 Y) y _ hy.2 _ _).trans (congrArg₂ (· * ·) eB eB))))
    refine eL.trans (Eq.trans ?_ eR.symm)
    rw [sec_trans s (𝟙 Y) y h₁ h₂, Units.val_pow_eq_pow_val]
    ring

theorem good_sq {J : (Z ⟶ X) → L.ι} {z : Z} (hJ : Good L z J) : Good (SqLB.sq L) z (fun q _ => J q) :=
  fun ψ => Set.mem_iInter.2 fun _ => hJ ψ

theorem sval_sqSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (sqSec s) r z (fun q _ => J q) = sval s r z J ^ 2 := by
  have h0 := hJ.mem φ r
  have hm : r z ∈ LB.wchart (SqLB.sq L) φ (fun k _ => J (r ≫ φ k)) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => Set.mem_iInter.1 h0 k
  exact (gs_mul r z _ hm _ _).trans ((congrArg₂ (· * ·) (gs_res r z _ hm _) (gs_res r z _ hm _)).trans
    (pow_two _).symm)

def secSub {M : LB Y} (a b : LB.Sec M) : LB.Sec M where
  f := fun i => a.f i - b.f i
  compat := fun i j => by rw [map_sub, map_sub, a.compat, b.compat, mul_sub]

theorem sval_secSub {M : LB X} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (a b : LB.Sec (LB.LinComb M φ ε)) (r : Z ⟶ Y)
    (z : Z) {J : (Z ⟶ X) → M.ι} (hJ : Good M z J) :
    sval (secSub a b) r z J = sval a r z J - sval b r z J :=
  gs_sub r z _ (hJ.mem φ r) _ _

end GlobalTheory.SqDescend


open GlobalTheory.SqDescend in
theorem GlobalTheory.sq_corr_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ (α : D.toPre.X) (α' : D'.toPre.X), (∀ κ, D'.toPre.famφB α' κ ≫ Φ.hom.left = Φ.hom.left ≫ D.toPre.famφB α κ) → ∀ (s : D.toPre.SecB 2 α) (s' : D'.toPre.SecB 2 α'), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R (maximalIdeal R) e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (r ≫ (U.gt e).pG.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (r ≫ (U'.gt e).pG.left ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' (r ≫ (U'.gt e).pG.left) z J' ^ 2) → ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' → sval s (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval s' ρ z J' ^ 2 := by
  intro R _ _ _ hCN G _ _ hSA D D' A A' U U' Φ w hw hpG α α' hφ s s' hE Z ρ z J J' hJ hJ'
  classical
  have hL := D.toPre.P.isLB
  have hL' := D'.toPre.P.isLB
  have hM : (SqLB.sq D.toPre.P.L).IsLB := DVR.linComb_isLB _ hL _ _
  have hM' : (SqLB.sq D'.toPre.P.L).IsLB := DVR.linComb_isLB _ hL' _ _
  obtain ⟨a, ha, -⟩ := SecPull.existsUnique_secPull _ _ _ _ _ _ Φ.hom.left hM hM' w hw (Fin 4)
    (D'.toPre.famφB α') (D.toPre.famφB α) (DegPre.famε 2) Φ.hom.left hφ (sqSec s)
  have hT : ∀ (Z : Scheme.{0}) (r : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι)
      (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Good D.toPre.P.L z J → Good D'.toPre.P.L z J' →
      sval s (r ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q)
        (r ≫ D'.toPre.famφB α' κ) ^ DegPre.famε 2 κ).val * sval a r z (fun q _ => J' q) := by
    intro Z r z J J' hJ hJ'
    rw [← sval_sqSec s _ z hJ]
    exact ExpTrans.sec_val w _ _ _ Φ.hom.left hφ (sqSec s) a r z (ha Z r z) (good_sq hJ) (good_sq hJ')
  have hvan : ∀ (e : ℕ) (q : Fin 4 → Fin 1 → D'.toPre.P.L.ι),
      ((U'.gt e).pG.left.app _).hom ((secSub a (sqSec s')).f q) = 0 := by
    intro e q
    refine fn_ext fun y hy => ?_
    choose J₁ hJ₁ using fun ψ : (thickObj R (maximalIdeal R) e G).left ⟶ D.toPre.P.A.left =>
      exists_chart hL (ψ y)
    choose J₂ hJ₂ using fun ψ : (thickObj R (maximalIdeal R) e G).left ⟶ D'.toPre.P.A.left =>
      exists_chart hL' (ψ y)
    have g₁ : Good D.toPre.P.L y J₁ := hJ₁
    have g₂ : Good D'.toPre.P.L y J₂ := hJ₂
    have e1 := hE e _ (𝟙 _) y J₁ J₂ g₁ g₂
    have e2 := hT _ (U'.gt e).pG.left y J₁ J₂ g₁ g₂
    simp only [Category.id_comp] at e1
    rw [hpG e, e1, ← sval_sqSec s' _ y g₂] at e2
    have e3 := (Units.mul_right_inj _).1 e2
    have hΔ : sval (secSub a (sqSec s')) (U'.gt e).pG.left y (fun q _ => J₂ q) = 0 := by
      rw [sval_secSub a (sqSec s') _ y (good_sq g₂), e3, sub_self]
    refine (gs_pull (𝟙 _) (U'.gt e).pG.left y _ hy _).trans ?_
    rw [Category.id_comp, gs_zero]
    refine (sec_trans (secSub a (sqSec s')) (U'.gt e).pG.left y (j := q) hy ((good_sq g₂).mem _ _)).trans ?_
    change _ * sval (secSub a (sqSec s')) (U'.gt e).pG.left y (fun q _ => J₂ q) = 0
    rw [hΔ, mul_zero]
  obtain ⟨hN, -, -, -⟩ := TorRef.admissibleBase_of_completeNormalLocalCharZero hCN
  have hI : maximalIdeal R ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  have := D'.toPre.P.isAb.smooth
  have := D'.toPre.P.isAb.geomConnected
  have h0 := (sec_eq_zero_and_hom_eq_of_thickenings R (maximalIdeal R) hI D'.toPre.P.A).1 _
    (DVR.linComb_isLB _ hM' _ _) (secSub a (sqSec s'))
    fun e q => (ExtDiv.pG_app_eq_zero_iff (U'.gt e) _ _).1 (hvan e q)
  have key : sval a ρ z (fun q _ => J' q) = sval (sqSec s') ρ z (fun q _ => J' q) := by
    have h1 : sval (secSub a (sqSec s')) ρ z (fun q _ => J' q) = 0 := by
      show gs _ _ _ _ = 0
      exact (congrArg (gs ρ z _) (h0 _)).trans (gs_zero _ _ _)
    have h2 := sval_secSub a (sqSec s') ρ z (good_sq hJ')
    rw [h1] at h2
    exact sub_eq_zero.1 h2.symm
  rw [hT Z ρ z J J' hJ hJ', key, sval_sqSec s' ρ z hJ']
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.WtSecond

lemma left_eq {S : Scheme.{0}} {A B C : Over S} {f : A ⟶ B} {g : B ⟶ C} {h : A ⟶ C} (H : f ≫ g = h) :
    f.left ≫ g.left = h.left :=
  (Over.comp_left _ _ _ f g).symm.trans (congrArg (fun k => k.left) H)

lemma appLE_congr {A B : Scheme.{0}} {f g : A ⟶ B} (h : f = g) {U : B.Opens} {W : A.Opens}
    (e : W ≤ f ⁻¹ᵁ U) (e' : W ≤ g ⁻¹ᵁ U) : f.appLE U W e = g.appLE U W e' := by
  subst h; rfl

section Core

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def chg (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    WeightPf.Te D I e ⊗ thickObj R I e G ⟶ WeightPf.Te D' I e ⊗ thickObj R I e G :=
  lift (fst (WeightPf.Te D I e) (thickObj R I e G) ≫ θ.inv) (snd (WeightPf.Te D I e) (thickObj R I e G))

lemma chg_fst (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    chg (G := G) θ ≫ fst (WeightPf.Te D' I e) (thickObj R I e G) =
      fst (WeightPf.Te D I e) (thickObj R I e G) ≫ θ.inv :=
  lift_fst _ _

lemma chg_snd (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    chg (G := G) θ ≫ snd (WeightPf.Te D' I e) (thickObj R I e G) = snd (WeightPf.Te D I e) (thickObj R I e G) :=
  lift_snd _ _

lemma chg_chg (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e) :
    chg (G := G) θ ≫ chg (G := G) θ.symm = 𝟙 _ := by
  refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, chg_fst, ← Category.assoc, chg_fst, Category.assoc, Iso.symm_inv, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]
  · rw [Category.assoc, chg_snd, chg_snd, Category.id_comp]

lemma chg_act (g : GtCoord I D e G) (g' : GtCoord I D' e G) (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e)
    (hi : θ.hom ≫ g.i = g'.i) : chg θ ≫ WeightPf.act g' = WeightPf.act g := by
  have hgi : θ.inv ≫ g'.i = g.i := (Iso.inv_comp_eq θ).2 hi.symm
  have h1 : chg θ ≫ lift (fst (WeightPf.Te D' I e) (thickObj R I e G) ≫ g'.i) (snd _ _) =
      lift (fst (WeightPf.Te D I e) (thickObj R I e G) ≫ g.i) (snd _ _) := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, lift_fst, lift_fst, ← Category.assoc, chg_fst, Category.assoc, hgi]
    · rw [Category.assoc, lift_snd, lift_snd, chg_snd]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ μ[thickObj R I e G]) h1)

end Core

section Weight

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

lemma chg_weight (g : GtCoord I D e G) (g' : GtCoord I D' e G) (θ : WeightPf.Te D' I e ≅ WeightPf.Te D I e)
    (hi : θ.hom ≫ g.i = g'.i) (x₀ : D'.X → D.X)
    (hx : ∀ x, θ.hom.left.appTop.hom (charUnit (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D.X (x₀ x)).val =
      (charUnit (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.X x).val)
    (α' : D'.X) (jt : Fin 4 → D'.P.L.ι) (hjt : LB.Coh D'.P.L (D'.Oφ g'.pG α') jt)
    (W' : (WeightPf.Te D I e ⊗ thickObj R I e G).left.Opens) (hs : W' ≤ (snd (WeightPf.Te D I e) (thickObj R I e G)).left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt)
    (ha : W' ≤ (WeightPf.act g).left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt) :
    ((WeightPf.act g).left.appLE _ W' ha).hom ((g'.t α').s jt).val =
      ((WeightPf.Te D I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP D.X (thickObj R I e G) (x₀ α')) *
      ((snd (WeightPf.Te D I e) (thickObj R I e G)).left.appLE _ W' hs).hom ((g'.t α').s jt).val := by
  have hΨs : chg (G := G) θ.symm ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)) = (snd (WeightPf.Te D' I e) (thickObj R I e G)) := chg_snd θ.symm
  have hact' : chg (G := G) θ.symm ≫ WeightPf.act g = WeightPf.act g' :=
    chg_act g' g θ.symm (by rw [Iso.symm_hom, ← hi, Iso.inv_hom_id_assoc])
  have hs'' : (chg (G := G) θ.symm).left ⁻¹ᵁ W' ≤ (snd (WeightPf.Te D' I e) (thickObj R I e G)).left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt := by
    have h1 : (snd (WeightPf.Te D' I e) (thickObj R I e G)).left = (chg (G := G) θ.symm).left ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left :=
      (left_eq hΨs).symm
    rw [h1, Scheme.Hom.comp_preimage]
    exact fun y hy => hs hy
  have ha'' : (chg (G := G) θ.symm).left ⁻¹ᵁ W' ≤ (WeightPf.act g').left ⁻¹ᵁ LB.wchart D'.P.L (D'.Oφ g'.pG α') jt := by
    have h1 : (WeightPf.act g').left = (chg (G := G) θ.symm).left ≫ (WeightPf.act g).left :=
      (left_eq hact').symm
    rw [h1, Scheme.Hom.comp_preimage]
    exact fun y hy => ha hy
  have hΦW : W' ≤ (chg (G := G) θ).left ⁻¹ᵁ ((chg (G := G) θ.symm).left ⁻¹ᵁ W') := by
    have h2 : (chg (G := G) θ).left ≫ (chg (G := G) θ.symm).left = 𝟙 _ :=
      (left_eq (chg_chg θ)).trans (Over.id_left _)
    rw [← Scheme.Hom.comp_preimage, h2]
    exact fun y hy => hy
  have key := WeightPf.t_act g' α' jt hjt _ hs'' ha''
  have k2 := congrArg ((chg (G := G) θ).left.appLE _ W' hΦW).hom key
  have e0 : (chg (G := G) θ).left ≫ (WeightPf.act g').left = (WeightPf.act g).left :=
    left_eq (chg_act g g' θ hi)
  have e1 : (chg (G := G) θ).left ≫ (snd (WeightPf.Te D' I e) (thickObj R I e G)).left = (snd (WeightPf.Te D I e) (thickObj R I e G)).left :=
    left_eq (chg_snd θ)
  have L : ∀ x, ((chg (G := G) θ).left.appLE _ W' hΦW).hom (((WeightPf.act g').left.appLE _ _ ha'').hom x) =
      ((WeightPf.act g).left.appLE _ W' ha).hom x := by
    intro x
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    exact congrArg (fun φ => φ.hom x) (appLE_congr e0 _ ha)
  have S : ∀ x, ((chg (G := G) θ).left.appLE _ W' hΦW).hom (((snd (WeightPf.Te D' I e) (thickObj R I e G)).left.appLE _ _ hs'').hom x) =
      ((snd (WeightPf.Te D I e) (thickObj R I e G)).left.appLE _ W' hs).hom x := by
    intro x
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]
    exact congrArg (fun φ => φ.hom x) (appLE_congr e1 _ hs)
  have hres : ∀ x, ((chg (G := G) θ).left.appLE _ W' hΦW).hom (((WeightPf.Te D' I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom x) =
      ((WeightPf.Te D I e ⊗ thickObj R I e G).left.presheaf.map (homOfLE le_top).op).hom ((chg (G := G) θ).left.appTop.hom x) := by
    intro x
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE]
    first | erw [Scheme.Hom.appLE_map] | rfl
  have hchi : (chg (G := G) θ).left.appTop.hom (TorusInj.chiP D'.X (thickObj R I e G) α') =
      TorusInj.chiP D.X (thickObj R I e G) (x₀ α') := by
    unfold TorusInj.chiP
    rw [← SplitTorusHom.appTop_comp, chg_fst, SplitTorusHom.appTop_comp, ← hx α',
      ← SplitTorusHom.appTop_comp θ.inv θ.hom, Iso.inv_hom_id, SplitTorusHom.appTop_id]
  rw [map_mul] at k2
  exact (L _).symm.trans (k2.trans (congrArg₂ (· * ·) ((hres _).trans (congrArg _ hchi)) (S _)))

end Weight

theorem wt_second : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G) (e : ℕ) (xe : D'.toPre.X ≃+ D.toPre.X), GlobalTheory.CharAgree.Match (U.gt e) (U'.gt e) xe → ∀ (α' : D'.toPre.X) (jt : Fin 4 → D'.toPre.P.L.ι), LB.Coh D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt → ∀ (W' : (WeightPf.Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left.Opens) (hs : W' ≤ (snd (WeightPf.Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt) (ha : W' ≤ (WeightPf.act (U.gt e)).left ⁻¹ᵁ LB.wchart D'.toPre.P.L (D'.toPre.Oφ (U'.gt e).pG α') jt), ((WeightPf.act (U.gt e)).left.appLE _ W' ha).hom (((U'.gt e).t α').s jt).val = ((WeightPf.Te D.toPre (maximalIdeal R) e ⊗ thickObj R (maximalIdeal R) e G).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP D.toPre.X (thickObj R (maximalIdeal R) e G) (xe α')) * ((snd (WeightPf.Te D.toPre (maximalIdeal R) e) (thickObj R (maximalIdeal R) e G)).left.appLE _ W' hs).hom (((U'.gt e).t α').s jt).val := by
  intro R _ _ _ hCN G _ _ hG D D' A A' U U' e xe hM α' jt hjt W' hs ha
  have hR := admissibleBase_of_completeNormalLocalCharZero hCN
  obtain ⟨hN, -, -, -⟩ := hR
  have hI : maximalIdeal R ≠ ⊤ := (maximalIdeal.isMaximal R).ne_top
  obtain ⟨θ, hθ, hi⟩ := CharAgree.exists_torus_iso hI (U.gt e) (U'.gt e)
  have := CharAgree.connected_thick hI e
  obtain ⟨x₀, hx⟩ := exists_addEquiv_of_splitTorus_iso _ D.toPre.X D'.toPre.X θ hθ

  have hM₀ : CharAgree.Match (U.gt e) (U'.gt e) x₀ := by
    intro Z r z J J' hJ hJ' _ h' x
    let FinalForm : Over (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (e + 1)))) :=
      Over.mk (r ≫ (thickObj R (maximalIdeal R) e G).hom)
    let a : FinalForm ⟶ thickObj R (maximalIdeal R) e G := Over.homMk r rfl
    let τ := (U'.gt e).isKernel.lift a (toUnit _) ((CharAgree.comp_q_eq_one_iff (U'.gt e) a).2 h')
    have hτ : τ ≫ (U'.gt e).i = a := (U'.gt e).isKernel.lift_fst _ _ _
    have hτ' : (τ ≫ θ.hom) ≫ (U.gt e).i = a := by rw [Category.assoc, hi, hτ]
    have k := (TorusCoord.val_torus_point_and_translate R (maximalIdeal R) D.toPre e G (U.gt e) FinalForm
      (τ ≫ θ.hom) 1 z J hJ (x₀ x)).1
    have k' := (TorusCoord.val_torus_point_and_translate R (maximalIdeal R) D'.toPre e G (U'.gt e) FinalForm
      τ 1 z J' hJ' x).1
    rw [hτ'] at k
    rw [hτ] at k'
    refine k.trans (Eq.trans (Units.ext ?_) k'.symm)
    rw [gm_val _ _ ⊤ trivial, gm_val _ _ ⊤ trivial]
    refine congrArg (FinalForm.left.presheaf.germ ⊤ z trivial).hom ?_
    exact (SplitTorusHom.appTop_comp τ θ.hom _).trans (congrArg τ.left.appTop.hom (hx x))
  have hxe : (xe : D'.toPre.X → D.toPre.X) = x₀ := CharAgree.match_unique hI _ _ hM hM₀
  rw [congrFun hxe α']
  exact chg_weight (U.gt e) (U'.gt e) θ hi x₀ hx α' jt hjt W' hs ha

end GlobalTheory.WtSecond
end
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj

theorem _root_.GlobalTheory.T.span_periodLattice_complexSemiAbelian_eq_top : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsSemiAbelian G → ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective (e) ∧ IsHolTo Set.univ (fun z => (show Sp ℂ ⟶ G.left from (e z).left)) ∧ (∀ w, ∃! v : epsPt (y) ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ (∀ v : epsPt (y) ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) → Submodule.span ℂ {z | e z = 1} = ⊤ := by
  first | exact @GlobalTheory.PeriodSpan.span_ker_eq_top | exact GlobalTheory.PeriodSpan.span_ker_eq_top | (intros; apply GlobalTheory.PeriodSpan.span_ker_eq_top <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiCompare

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem feq_of_expandsAt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (k : ℕ), 1 ≤ k → ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e : ℕ, U.ExpandsAt e k σ f) → ∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + k • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) k α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) k mu α) κ.left z J).val := by
  intro R _ _ _ hCN G _ _ hSA D A U k hk σ f hE mu α T κ y z J hJ
  have hR : AdmBase R (maximalIdeal R) := admissibleBase_of_completeNormalLocalCharZero hCN
  have := hR.1
  obtain ⟨s, hs⟩ := exists_sec U.LG.isLB (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK R))
    (ε' := fun _ => ((k : ℕ) : ℤ)) (fun _ _ h => by simp only [Category.comp_id])
    (H1.SectionArithmetic.pullSec σ (pullback.fst G.hom (jK R)))
  have hU := U.expand k hk
  obtain ⟨E, hsE, -⟩ := hU.1 s
  obtain ⟨g, hg, hgE⟩ := IntegralExpansionLocal.main R (maximalIdeal R) le_rfl D A G U.toUnifPre k σ s
    (SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ =>
      ((hs _ _ y J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ y hJ)).symm) E hsE
  have H := (comb_eq_zero_iff_expansion_comb_eq_zero R _ hR D A G U.toUnifPre k 2 ![1, -1] ![σ, σ] ![f, g]
    (fun i => by fin_cases i; exacts [hE, hg])).1 (fun j => by
      simp [Fin.sum_univ_two, Out.scal])
  obtain rfl : f = g := funext fun α => SecOps.sec_ext fun j => by
    have := H α j
    simpa [Fin.sum_univ_two, Out.scal, add_neg_eq_zero] using this
  let ρ : T ⟶ DegPre.BF D.toPre (FractionRing R) := lift κ y
  have ρ₁ : ρ ≫ fst _ _ = κ := lift_fst _ _
  have ρ₂ : ρ ≫ DegPre.prB D.toPre (FractionRing R) = y := lift_snd _ _
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D.toPre) (F := FractionRing R) GlobalTheory.globalFns_holds k mu α
  have vu := hv u hu hc _ ρ z J hJ
  have hrel := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 (E.fe mu α u hu hc) _ ρ.left z J hJ
  rw [← SectionScalarValuation.secScal_sval (hgE _) _ z hJ, ← SectionScalarValuation.secScal_sval (hgE _) _ z hJ] at hrel
  have htr : (ρ ≫ DegPre.trF D.toPre (FractionRing R) mu) ≫ DegPre.prB D.toPre (FractionRing R) =
      y * cP D.toPre T mu := by
    rw [Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, ρ₂, comp_cP, comp_cP]
  rw [vu] at hrel
  rw [← htr, ← congrArg (fun q => sval (f (α + k • mu)) q.left z J) ρ₂]
  rw [ρ₁] at hrel
  simp only [Over.comp_left]
  exact hrel

end GlobalTheory.PsiCompare
end
end
