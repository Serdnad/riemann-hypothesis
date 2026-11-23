module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle490
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle075
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle076
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle067
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2734
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle028
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle012

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.UT.OLinEnd

noncomputable section

namespace GlobalTheory.Mum.EFix

section Pts
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
variable {O : Type} [Ring O] [StarRing O] [Module O D.X]

theorem exists_gtPtAct (hG : GlobalFnsSt) (oa : D.OAct O) {k : ℕ} (a : O) (p : QkPt D F k) :
    ∃ q : QkPt D F k, q.y = a • p.y ∧ GtPtAct oa a p.g q.g := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have hr := oa.onB.rosati (star a)
  have hbal := oa.tau_bal (star a)
  rw [star_star] at hr hbal
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.P.isAb D.P.isLB _ _ hr
  have cf : ∀ (T) (x : O) χ, cP D T (x • χ) = cP D T χ ≫ oa.onB.act x := fun T x χ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  have ra := fun {y : (TF (R := R) F).left} {J} (hJ : Good D.P.L y J) =>
    ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := TF (R := R) F) hJ
  have vu : ∀ {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ x w : TF (R := R) F ⟶ D.P.A,
      val (LB.pullGen D.P.L _ _ u (lift x w).left) (𝟙 _) y J = val₂ u y J x w := fun hJ x w => by
    rw [val_pull hJ, Category.id_comp]; rfl
  have u₁ : ∀ {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ w, val₂ u y J 1 w = 1 := fun {y J} hJ w => by
    have C : IsCub (cubV D.cub y J) := isCub_cubV D.cub hJ
    have e := (ra hJ 1 1 w).1
    rw [_root_.mul_one, MonObj.one_comp, C.face, C.face, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have u₂ : ∀ {y : (TF (R := R) F).left} {J}, Good D.P.L y J → ∀ w, val₂ u y J w 1 = 1 := fun {y J} hJ w => by
    have C : IsCub (cubV D.cub y J) := isCub_cubV D.cub hJ
    have e := (ra hJ 1 1 w).2
    rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
    exact mul_eq_left.1 e.symm
  have ex : ∀ g : GtPtF D F, ∃ g' : GtPtF D F, g'.b = g.b ≫ oa.onB.act a ∧ ∀ χ y J, Good D.P.L y J →
      val (g'.s χ) (𝟙 _) y J = val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := by
    intro g
    have vv : ∀ χ y J, Good D.P.L y J → val (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left)) (𝟙 _) y J =
        val (g.s (star a • χ)) (𝟙 _) y J * val₂ u y J (cP D _ χ) g.b := fun χ y J hJ =>
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (vu hJ _ _))
    obtain ⟨g', hb, hv⟩ := exists_gt (g.b ≫ oa.onB.act a) (fun χ => LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
        (LB.pullGen D.P.L _ _ u (lift (cP D _ χ) g.b).left))
      (fun χ => mulGen_isGen _ _ _ _ _ _ _ (g.isGen _) (pullGen_isGen _ _ _ _ hu _)) (fun χ U _ h => by
        refine (prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _ (prod_gt g.b (star a • χ) h)
          (prod_ros _ _ (cP D _ χ) g.b h)).trans ?_
        rw [prod_gt, cf]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) (fun y J hJ => by
        rw [vv 0 y J hJ, smul_zero, cPoint_zero, u₁ hJ, _root_.mul_one]
        exact (val_corr hJ g.s_zero _).trans (val_one _)) (fun χ χ' y J hJ => by
        have e₁ := (ra hJ (cP D _ χ) (cP D _ χ') g.b).1
        have e₂ := gt_mul (𝟙 (TF (R := R) F)) hJ g (star a • χ) (star a • χ')
        rw [Category.id_comp, cf, cf, Over.id_left] at e₂
        rw [vv _ y J hJ, vv _ y J hJ, vv _ y J hJ, smul_add, cPoint_add, _root_.mul_assoc]
        refine (congrArg _ e₁).trans ?_
        rw [← _root_.mul_assoc]
        exact (congrArg (· * _) e₂).trans (mul_mul_mul_comm _ _ _ _))
    exact ⟨g', hb, fun χ y J hJ => (hv χ y J hJ).trans (vv χ y J hJ)⟩
  choose act hb hv using ex
  have add : ∀ g g' g'' : GtPtF D F, g.IsAdd g' g'' → (act g).IsAdd (act g') (act g'') := fun g g' g'' h => by
    obtain ⟨b₁, v₁⟩ := (isAdd_iff _ _ _).1 h
    refine (isAdd_iff _ _ _).2 ⟨by rw [hb, hb, hb, b₁, MonObj.mul_comp], fun χ y J hJ => ?_⟩
    have e₁ := (ra hJ g.b g'.b (cP D _ χ)).2
    have e₂ := v₁ (star a • χ) y J hJ
    rw [cf] at e₂
    rw [← b₁] at e₁
    rw [hv _ _ y J hJ, hv _ _ y J hJ, hv _ _ y J hJ, hb, hb, _root_.mul_assoc]
    refine (congrArg _ e₁).trans ?_
    rw [← _root_.mul_assoc]
    exact (congrArg (· * _) e₂).trans (mul_mul_mul_comm _ _ _ _)
  obtain ⟨h, ⟨gs, g₀, gst, gl⟩, hι⟩ := p.eq
  obtain ⟨ιb, ιv⟩ := (isIota_iff _ _).1 hι
  let q : QkPt D F k := ⟨a • p.y, act p.g, act h, ⟨fun i => act (gs i), by
      obtain ⟨z₁, z₂⟩ := (isZero_iff _).1 g₀
      exact (isZero_iff _).2 ⟨by rw [hb, z₁, MonObj.one_comp], fun χ y J hJ => by
        rw [hv _ _ y J hJ, z₂ _ y J hJ, z₁, u₂ hJ, _root_.mul_one]⟩,
      fun i => add _ _ _ (gst i), congrArg act gl⟩, (isIota_iff _ _).2 ⟨by rw [hb, ιb, cf], fun χ y J hJ => by
      let κ : TF (R := R) F ⟶ TK R := Over.homMk (𝟙 _ ≫ jFK (R := R) F) (by
        rw [Category.id_comp]; rfl)
      have e := (val_mul hJ _ _ _).symm.trans (val_corr hJ (hbal u hu u₀ χ p.y) κ.left)
      have e' : val (LB.pullGen D.P.L _ _ u (D.pt2 χ p.y)) κ.left y J = val₂ u y J (cP D _ χ) (cP D _ p.y) := by
        rw [val_pull hJ, val₂, ← comp_cP D κ, ← comp_cP D κ p.y, ← comp_lift]; rfl
      rw [hv _ _ y J hJ, ιv _ y J hJ, ιb, ← e']
      exact (congrArg₂ (· * ·) (tau_symm (𝟙 (TF (R := R) F)) hJ _ _) rfl).trans
        (e.trans (tau_symm (𝟙 (TF (R := R) F)) hJ _ _))⟩⟩
  refine ⟨q, rfl, hb _, fun u' hu' u₀' χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) rfl ?_) (hv p.g χ y J hJ).symm)
  rw [val_pull hJ, Category.id_comp]
  have z2 : zero2 D.P.A ≫ (snd D.P.A D.P.A).left ≫ D.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w (lift η[D.P.A] η[D.P.A])
  exact gen_unique D.P.isLB _ (zero2 D.P.A) z2 (surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2) hu' hu
    (fun y I hI => by
      have a₁ := val_corr hI u₀' (𝟙 _)
      have a₂ := val_corr hI u₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a₁ a₂
      exact a₁.trans a₂.symm) _ _ y J hJ

end Pts

section End
variable {R : Type} [CommRing R] [IsDomain R]

theorem exists_u (hG : GlobalFnsSt) (D : DegPre R) {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O)
    (a : O) (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε)) (hu : u.IsGen)
    (u₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) (χ : D.X) :
    ∃ v : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.Oφ (𝟙 _) (star a • χ)) (D.Oφ (oa.onB.act a) χ)) (Sum.elim Oε Oinvε)),
      Normd v ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
        Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := by
  have := oa.onB.hom a
  have := oa.onB.hom (star a)
  have cf : ∀ (T) (x : O) χ, cP D T (x • χ) = cP D T χ ≫ oa.onB.act x := fun T x χ => by
    rw [cP, oa.c_lin, ← Category.assoc]; rfl
  obtain ⟨v, hv, vv⟩ := exists_gen D.P.isLB
    (φ' := Sum.elim (D.Oφ (𝟙 _) (star a • χ)) (D.Oφ (oa.onB.act a) χ)) (ε' := Sum.elim Oε Oinvε)
    (fun U _ h => by
      refine (prod_ros _ _ (cP D _ χ) (𝟙 D.P.A) h).trans (Eq.symm ?_)
      refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ (prod_Oφ D (𝟙 _) (star a • χ) h)
        (prod_Oφ_inv D (oa.onB.act a) χ h)).trans ?_
      rw [cf, Category.id_comp]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.pullGen D.P.L _ _ u (lift (cP D D.P.A χ) (𝟙 D.P.A)).left) (pullGen_isGen _ _ _ _ hu _)
  have key : ∀ (T : Over (Spec (CommRingCat.of R))) (x : T ⟶ D.P.A) (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J),
      Good D.P.L z J → val v (r ≫ x.left) z J = val u (r ≫ (lift (cP D T χ) x).left) z J := fun T x Z r z J hJ => by
    rw [vv Z _ z J hJ, val_pull hJ, Category.assoc, ← Over.comp_left, comp_lift, comp_cP, Category.comp_id]
  refine ⟨v, ⟨hv, corr_of_val D.P.isLB fun y J hJ => ?_⟩, key⟩
  have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J) := isCub_cubV D.cub hJ
  have e := (ros_add D.cub hG D.P.isAb _ _ u hu u₀ (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) hJ 1 1 (cP D _ χ)).2
  rw [_root_.mul_one, MonObj.one_comp, C.face₃, C.face₃, _root_.mul_one, _root_.one_mul] at e
  have e' : val₂ u (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J (cP D _ χ) 1 = 1 := mul_eq_left.1 e.symm
  have k := key (𝟙_ (Over (Spec (CommRingCat.of R)))) 1 _ (𝟙 _) y J hJ
  have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  rw [o] at k
  refine (val_pull hJ _ _ _).trans (k.trans (Eq.trans ?_ (val_one _).symm))
  rw [Category.id_comp]
  exact e'

theorem endU_of_oLinear : LL → AllU fun {R} _ _ {I} {D} {A} {G} _ _ U => ∀ (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → ∀ a : O, ∃ E : EndU U.toUnifPre, E.aG = ιG.act a ∧ E.aA = ιA.act a ∧ E.aB = ιD.onB.act a ∧ (∀ χ, E.h χ = star a • χ) ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (g g' : GtPtF D.toPre F), E.Act g g' ↔ GtPtAct ιD a g g' := by
  intro hL R _ _ _ I _ D A G _ _ _ U O _ _ _ ιD ιA ιG hO a
  have hG := hL.1.globalFns
  have := ιD.onB.hom a
  have := ιD.onB.hom (star a)
  have hr := ιD.onB.rosati (star a)
  rw [star_star] at hr
  obtain ⟨u, hu, u₀⟩ := exists_ros hG D.toPre.P.isAb D.toPre.P.isLB _ _ hr
  choose v hv vv using exists_u hG D.toPre ιD a u hu u₀
  refine ⟨{ aG := ιG.act a, aA := ιA.act a, aB := ιD.onB.act a, homG := ιG.hom a, homA := ιA.hom a,
            homB := ιD.onB.hom a, h := DistribSMul.toAddMonoidHom D.toPre.X (star a), ext := hO.ext a,
            q_lin := fun e => hO.q_lin e a, i_lin := fun e => hO.i_lin e a, u := v, u_norm := hv,
            t_lin := fun e χ Z x z J hJ => ?_ }, rfl, rfl, rfl, fun _ => rfl, fun F _ _ g g' => ?_⟩
  · have e₁ := val_corr hJ (hL.2.2.2.1.tLin R I O D A G U.toUnifPre ιD ιA ιG hO e a u hu u₀ χ) x
    refine ((val_pull hJ _ _ _).symm.trans e₁.symm).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_))
    exact (val_pull hJ _ _ _).trans (vv χ _ (U.gt e).pG Z x z J hJ).symm
  · have k : ∀ χ z J, Good D.toPre.P.L z J →
        val (v χ) g.b.left z J = val u (𝟙 _ ≫ (lift (cP D.toPre _ χ) g.b).left) z J := fun χ z J hJ =>
      (congrArg (fun q => val (v χ) q z J) (Category.id_comp g.b.left).symm).trans (vv χ _ g.b _ (𝟙 _) z J hJ)
    refine and_congr Iff.rfl ⟨fun H u' hu' u₀' χ => corr_of_val D.toPre.P.isLB fun z J hJ => ?_, fun H χ z J hJ => ?_⟩
    · refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) rfl ?_) (H χ z J hJ).symm)
      exact (val_pull hJ _ _ _).trans ((ros_unique hG D.toPre hu hu' u₀ u₀' _ _ z J hJ).trans (k χ z J hJ).symm)
    · refine (val_corr hJ (H u hu u₀ χ) (𝟙 _)).symm.trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl ?_))
      exact (val_pull hJ _ _ _).trans (k χ z J hJ).symm

end End

end GlobalTheory.Mum.EFix
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

namespace GlobalTheory.Poinc.IntEval
open GlobalTheory.UT.CoefBasic GlobalTheory.ExpansionValueZero GlobalTheory.BoxExpansion

theorem coef_comb_pull : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (g : GtPt D (𝟙_ (Over (Sp R)))) (g' : GtPtF D (FractionRing R)), GtPt.IsPullF (FractionRing R) (toUnit (TF (R := R) (FractionRing R))).left g g' → ∀ (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, g.b.left] (DegPre.lineε 1))) (l : FractionRing R), l ≠ 0 → ∀ (k : ℕ) (wk : Frm D (FractionRing R) k g'.b), wk.IsGen → (∀ (z : (TF (R := R) (FractionRing R)).left) (J : ((TF (R := R) (FractionRing R)).left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → GlobalTheory.UT.cst (FractionRing R) z (l ^ k) * (val wk (𝟙 _) z J).val = (val t (toUnit (TF (R := R) (FractionRing R))).left z J ^ k).val) → ∀ (s : Fam D (FractionRing R) k) (n : ℕ) (c : Fin n → FractionRing R) (fs : Fin n → ∀ α : D.X, D.SecB k α), (∀ α : D.X, GeneratorPullback.SecLin D.P.L (DegPre.famφ D (FractionRing R) α) (DegPre.famε k) (s.s α) (D.famφB α) (DegPre.famε k) (fun i => fs i α) (DegPre.prB D (FractionRing R)).left (fun i => scal (fst (TF (R := R) (FractionRing R)) D.P.A).left (c i))) → ∀ a : Fin n → D.X → R, (∀ (i : Fin n) (α : D.X) (Z : Scheme.{0}) (r : Z ⟶ Sp R) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → sval (fs i α) (r ≫ g.b.left) z J * (val (g.s α) r z J).val * (val t r z J ^ k).val = Geo.Tor.cst r z (a i α) * (val (L := D.P.L) D.rig r z J ^ k).val) → ∀ α : D.X, l ^ k * coef s g' wk α = ∑ i, c i * algebraMap R (FractionRing R) (a i α) := by
  intro R _ _ D g g' hP t l hl k wk hwk hl' s n c fs hs a ha α
  have hτ : (toUnit (TF (R := R) (FractionRing R))).left = jFK (R := R) (FractionRing R) ≫ jK R := by
    have := Over.w (toUnit (TF (R := R) (FractionRing R)))
    simpa using this
  have hb : g'.b.left = (toUnit (TF (R := R) (FractionRing R))).left ≫ g.b.left := hP.1
  have hlk : (l ^ k) ≠ 0 := pow_ne_zero _ hl
  suffices key : IsCoef k g' wk α (s.s α) ((l ^ k)⁻¹ * ∑ i, c i * algebraMap R (FractionRing R) (a i α)) by
    rw [coef_eq key, ← _root_.mul_assoc, mul_inv_cancel₀ hlk, _root_.one_mul]
  intro z J hJ
  have e₂ : (lift (𝟙 (TF (R := R) (FractionRing R))) g'.b).left ≫ (DegPre.prB D (FractionRing R)).left =
      (toUnit (TF (R := R) (FractionRing R))).left ≫ g.b.left := by
    rw [← Over.comp_left]
    erw [lift_snd]
    exact hb
  have e₃ : (lift (𝟙 (TF (R := R) (FractionRing R))) g'.b).left ≫ (fst (TF (R := R) (FractionRing R)) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have v : val (g'.s α) (𝟙 _) z J = val (g.s α) (toUnit (TF (R := R) (FractionRing R))).left z J := by
    rw [val_corr hJ (hP.2 α), val_pull hJ, Category.id_comp]
  have bi : ∀ i, gs (lift (𝟙 (TF (R := R) (FractionRing R))) g'.b).left z ⊤
      (scal (fst (TF (R := R) (FractionRing R)) D.P.A).left (c i)) = cstH z (c i) := fun i =>
    ((gs_pull _ _ z ⊤ trivial _).trans (by rw [e₃]; rfl)).trans (cst_eq z _)
  have hai : ∀ i, sval (fs i α) ((toUnit (TF (R := R) (FractionRing R))).left ≫ g.b.left) z J *
      (val (g.s α) (toUnit (TF (R := R) (FractionRing R))).left z J).val *
      (val t (toUnit (TF (R := R) (FractionRing R))).left z J ^ k).val =
      cstH z (algebraMap R (FractionRing R) (a i α)) *
        (val (L := D.P.L) D.rig (toUnit (TF (R := R) (FractionRing R))).left z J ^ k).val := fun i => by
    rw [ha i α _ _ z J hJ]
    congr 1
    rw [hτ, GlobalTheory.UT.EvalZero.cst_base]
    simp
  have hr : rigV D (TF (R := R) (FractionRing R)).hom z J =
      val (L := D.P.L) D.rig (toUnit (TF (R := R) (FractionRing R))).left z J := by
    rw [hτ]; rfl
  have hw := hl' z J hJ
  rw [cst_eq] at hw ⊢
  refine ((IsUnit.mk0 _ hlk).map (cstH (R := R) z)).mul_left_cancel ?_
  rw [secLin_val (hs α) _ z hJ, e₂, v, hr]
  simp only [bi]

  rw [← _root_.mul_assoc, ← map_mul, ← _root_.mul_assoc, mul_inv_cancel₀ hlk, _root_.one_mul, map_sum,
  Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := hai i
  have h2 := hw
  simp only [Units.val_pow_eq_pow_val, map_mul] at h1 h2 ⊢
  linear_combination (-(cstH (R := R) z (c i))) * h1 - cstH (R := R) z (c i) *
    sval (fs i α) ((toUnit (TF (R := R) (FractionRing R))).left ≫ g.b.left) z J *
    (val (g.s α) (toUnit (TF (R := R) (FractionRing R))).left z J).val * h2

end GlobalTheory.Poinc.IntEval
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.SecBasisPull

open GlobalTheory.VVRank GlobalTheory.EmbPull GlobalTheory.ThetaReal

theorem eq_zero_of_smul_eq_zero (hS : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) {T : Over S}
    [IsAffine T.left] {t : LB.Sec (LPow P.A P.L 1 T)} (ht : IsGenSec P.A P.L 1 t) (r : Γ(T.left, ⊤))
    (hr : r • (SecM.ofSec P.A t : SecM P.A P.L 1 T) = 0) : r = 0 := by
  let I : Ideal Γ(T.left, ⊤) := Submodule.comap (LinearMap.toSpanSingleton Γ(T.left, ⊤) Γ(T.left, ⊤) r) ⊥
  have memI : ∀ a, a ∈ I ↔ a * r = 0 := fun a => by
    simp [I, LinearMap.toSpanSingleton_apply, smul_eq_mul]
  have key : ∀ p : T.left, ∃ g ∈ I, p ∈ T.left.basicOpen g := fun p => by
    obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom p)
    haveI hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
    obtain ⟨g, hg, hp⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V) ⟨p, hV⟩ trivial
    let W := T.left.basicOpen g
    let l : overRes W ⟶ overRes (T := baseOver S) V := Over.homMk
      (IsOpenImmersion.lift V.ι (W.ι ≫ T.hom) (by
        rw [Scheme.Opens.range_ι]
        rintro _ ⟨y, rfl⟩
        exact hg y.2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
    have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen g
    haveI : IsAffine (overRes W).left := hW
    obtain ⟨c, -⟩ := exists_basis P 1 b hb (overRes W) l
    let σ := (overResι W).left.appTop.hom
    let k₀ : Fin (1 ^ P.g) := @default _ hq.toInhabited
    obtain ⟨n, u, hu⟩ := exists_pow_extend_secM P 1 g (c k₀)
    obtain ⟨e, he⟩ := ht (SecM.toSec P.A u)
    have hue : u = e • SecM.ofSec P.A t := Subtype.ext (funext he)
    obtain ⟨d, hd⟩ : ∃ d, pullM P.A P.L 1 (overResι W) (SecM.ofSec P.A t) = d • c k₀ := by
      have := c.sum_repr (pullM P.A P.L 1 (overResι W) (SecM.ofSec P.A t))
      rw [Fintype.sum_unique] at this
      exact ⟨_, this.symm⟩
    have coef : ∀ x y : Γ((overRes W).left, ⊤), x • c k₀ = y • c k₀ → x = y := fun x y h => by
      have := congrArg (fun v => c.repr v k₀) h
      simp only [LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
        smul_eq_mul, _root_.mul_one] at this
      exact this
    have e1 : σ (g ^ n) = σ e * d := coef _ _ (by
      rw [← hu, hue, LinearMap.map_smulₛₗ, hd, smul_smul])
    have e2 : σ r * d = 0 := coef _ _ (by
      rw [← smul_smul, ← hd, ← LinearMap.map_smulₛₗ, hr, map_zero, zero_smul])
    have e3 : σ (r * g ^ n) = 0 := by rw [map_mul, e1, mul_left_comm, e2, mul_zero]
    have e4 := (congrArg (fun q => q.hom (r * g ^ n)) (Scheme.Opens.ι_appTop W)).symm.trans e3
    obtain ⟨m, hm⟩ := GlobalTheory.AffineThickening.exists_pow_mul_eq_zero (isAffineOpen_top T.left) _ g (r * g ^ n)
      (Scheme.Opens.ι_image_top W) e4
    refine ⟨g ^ (m + n), (memI _).2 (by rw [pow_add, _root_.mul_assoc, mul_comm (g ^ n), hm]), ?_⟩
    rw [Scheme.mem_basicOpen_top] at hp ⊢
    rw [map_pow]
    exact hp.pow _
  have hI : Ideal.span (I : Set Γ(T.left, ⊤)) = ⊤ :=
    (isAffineOpen_top T.left).self_le_iSup_basicOpen_iff.1 fun p _ => by
      obtain ⟨g, hg, hp⟩ := key p
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g, hg⟩, hp⟩
  rw [Ideal.span_eq, Ideal.eq_top_iff_one] at hI
  simpa using (memI 1).1 hI

theorem univBasis_of_isGenSec (hS : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) {T : Over S} [IsAffine T.left]
    {th : LB.Sec (LPow P.A P.L 1 T)} (hth : IsGenSec P.A P.L 1 th) :
    UnivBasis P 1 (fun _ : Fin 1 => SecM.ofSec P.A th) := by
  intro T' _ h
  have hg := isGenSec_pullS P hS h hth
  let t' : SecM P.A P.L 1 T' := SecM.ofSec P.A (pullS P.A 1 h th)
  let l := LinearMap.toSpanSingleton Γ(T'.left, ⊤) (SecM P.A P.L 1 T') t'
  have inj : Function.Injective l := (injective_iff_map_eq_zero l).2 fun r hr =>
    eq_zero_of_smul_eq_zero hS P hg r (by simpa only [l, LinearMap.toSpanSingleton_apply] using hr)
  have surj : Function.Surjective l := fun s => by
    obtain ⟨r, hr⟩ := hg (SecM.toSec P.A s)
    exact ⟨r, Subtype.ext (funext fun j => (hr j).symm)⟩
  let E := LinearEquiv.ofBijective l ⟨inj, surj⟩
  refine ⟨(Module.Basis.singleton (Fin 1) Γ(T'.left, ⊤)).map E, fun i => ?_⟩
  rw [Module.Basis.map_apply, Module.Basis.singleton_apply]
  show l 1 = _
  rw [LinearMap.toSpanSingleton_apply, one_smul]
  rfl

end GlobalTheory.SecBasisPull
end


open GlobalTheory.SecBasisPull GlobalTheory.ThetaReal in
theorem GlobalTheory.SecBasisPull.exists_secBasis_pull : ∀ {R R' : Type} [CommRing R] [CommRing R'] (P : PolAV (Sp R)) (P' : PolAV (Sp R')) (f : R →+* R') (ψ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A (spMap f) ψ → LBIso P'.L (P.L.pull ψ) → ∀ th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R))), IsSecBasis _ (fun _ : Fin 1 => th) → ∃ th' : LB.Sec (LPow P'.A P'.L 1 (baseOver (Sp R'))), IsSecBasis _ (fun _ : Fin 1 => th') := by
  intro R R' _ _ P P' f ψ hp hw th hth
  obtain ⟨-, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  haveI : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Sp R))
  haveI : IsAffine (baseOver (Sp R')).left := inferInstanceAs (IsAffine (Sp R'))
  have hgen : IsGenSec P.A P.L 1 th := fun s => by
    obtain ⟨r, hr, -⟩ := hth s
    exact ⟨r 0, fun j => (hr j).trans (Fin.sum_univ_one _)⟩
  have hU := univBasis_of_isGenSec hL₂.secBaseChangeAny P hgen
  obtain ⟨b, hb⟩ := GlobalTheory.UnivBasisMove.univBasis_move _ _ (spMap f) P P' ψ hp hw 1 (Fin 1) (baseOver (Sp R)) (spMap f)
    (Category.comp_id _) _ hU
  obtain ⟨c, -⟩ := hb.exists_basis
  refine ⟨SecM.toSec P'.A (c 0), fun s => ?_⟩
  have e : ∀ i : Fin 1, c i = c 0 := fun i => congrArg c (Subsingleton.elim _ _)
  have := existsUnique_of_basis c s
  simp only [e] at this
  exact this
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.BaseTerms

def FrPull {V V' : Type} [CommRing V] [IsDomain V] [CommRing V'] [IsDomain V']
    {A : PolAV (Sp (FractionRing V))} {A₂ : PolAV (Sp (FractionRing V'))} {ψ : A₂.A.left ⟶ A.A.left}
    (w : LB.Iso A₂.L (A.L.pull ψ)) (f : FractionRing V →+* FractionRing V')
    (x₂ : TFK (R := V') (FractionRing V') ⟶ A₂.A) (fr₂ : FrAt x₂) (x : TFK (R := V) (FractionRing V) ⟶ A.A) (fr : FrAt x)
    (ρ : FractionRing V') : Prop :=
  ∀ (z : (TFK (R := V') (FractionRing V')).left) (J : ((TFK (R := V') (FractionRing V')).left ⟶ A.A.left) → A.L.ι)
    (J' : ((TFK (R := V') (FractionRing V')).left ⟶ A₂.A.left) → A₂.L.ι), Good A.L z J → Good A₂.L z J' →
    ((gw w x₂.left z (J (x₂.left ≫ ψ)) (J' x₂.left) : _) * (val fr₂ (𝟙 _) z J' : _) : ((TFK (R := V') (FractionRing V')).left.presheaf.stalk z)) =
      @id ((TFK (R := V') (FractionRing V')).left.presheaf.stalk z) (GlobalTheory.UT.cst (R := V') (FractionRing V') z ρ) *
        (val fr (show (TFK (R := V') (FractionRing V')).left ⟶ (TFK (R := V) (FractionRing V)).left from spMap f) z J : _)

end GlobalTheory.Poinc.Sep.BaseTerms
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_baseChange_raw_degenerationData_injective : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsNoetherianRing R₂] (σ : R₁ →+* R₂) (D₁ : DegPre R₁) (gam : FractionRing R₁ →+* FractionRing R₂), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) → ∃ (D₂ : DegPre R₂) (β : D₂.P.A.left ⟶ D₁.P.A.left) (v : LB.Iso D₂.P.L (D₁.P.L.pull β)) (xe : D₂.X ≃+ D₁.X), IsGrpPullback D₂.P.A D₁.P.A (spMap σ) β ∧ v.IsGen ∧ (∀ x, (D₂.c x).left ≫ β = spMap σ ≫ (D₁.c (xe x)).left) ∧ GlobalTheory.PsiRing.RigCmp σ D₁ D₂ β v ∧ GlobalTheory.PsiRing.PsiCmp D₁ D₂ β v xe (spMap gam) := by
  first | exact @GlobalTheory.BaseChangeDeg.exists_baseChange | exact GlobalTheory.BaseChangeDeg.exists_baseChange | (intros; apply GlobalTheory.BaseChangeDeg.exists_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PsiRing

theorem secIsMul_of_mult : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (th g : GlobalTheory.UU.SecBT D (𝟙_ _) 1 0) (b : R), GlobalTheory.PsiRing.Mult D th g b → ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul (𝟙_ _ ⊗ D.P.A).hom b g th := by
  intro R _ _ D th g b h
  refine GlobalTheory.IndivisibleSection.secIsMul_of_sval D.P.isLB fun y J hJ => ?_
  have e := h _ (𝟙 _) y J hJ
  rwa [Category.id_comp] at e

end GlobalTheory.PsiRing
end
