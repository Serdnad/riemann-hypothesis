module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle016
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2810
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2647
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2709
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle113
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
public import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2812
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantFieldConstCoeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2717
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AwayToAwayRightEqOfComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2250
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudTorusWeightZeroInvariantFieldCoeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Std.Tactic.BVDecide.Normalize.BitVec
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2847
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle063
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.PolDeg GlobalTheory.CechPic
open GlobalTheory.Mum.PowData
open GlobalTheory.Mum.Two

noncomputable section
namespace GlobalTheory.PairPts

private theorem psum_two_01 {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] {0, 1} = u * v := by
  have hl : (List.finRange 2).filter (· ∈ ({0, 1} : Finset (Fin 2))) = [0, 1] := by decide
  rw [psum, hl]
  simp [padd, pzero, Hom.mul_def, Hom.one_def]

private theorem psum_two_e {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] ∅ = 1 := by
  have hl : (List.finRange 2).filter (· ∈ (∅ : Finset (Fin 2))) = [] := by decide
  rw [psum, hl]
  simp [pzero, Hom.one_def]

private theorem psum_two_0 {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] {0} = u := by
  have hl : (List.finRange 2).filter (· ∈ ({0} : Finset (Fin 2))) = [0] := by decide
  rw [psum, hl]
  have := psum_two_e G u v
  rw [psum] at this
  simp only [List.foldr_cons, List.foldr_nil, List.filter] at this ⊢
  show u * pzero G T = u
  simp [pzero, Hom.one_def] at this ⊢

private theorem psum_two_1 {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (u v : T ⟶ G) :
    psum G ![u, v] {1} = v := by
  have hl : (List.finRange 2).filter (· ∈ ({1} : Finset (Fin 2))) = [1] := by decide
  rw [psum, hl]
  show v * pzero G T = v
  simp [pzero, Hom.one_def]

theorem lamPts_fst_eq_psum : ∀ {S₀ S : Scheme.{0}} (B₀ : Over S₀) [GrpObj B₀] [IsCommMonObj B₀] (B : Over S) [GrpObj B] [IsCommMonObj B] (f : S₀ ⟶ S) (β : B₀.left ⟶ B.left) (β₂ : (G2 B₀).left ⟶ (G2 B).left), IsGrpPullback B₀ B f β → IsSquare β β₂ → ∀ (Y : Over S₀) (x y : Y ⟶ B₀) (x' y' : Y ⟶ (Over.pullback f).obj B), x'.left ≫ pullback.fst B.hom f = x.left ≫ β → y'.left ≫ pullback.fst B.hom f = y.left ≫ β → ∀ k : Fin 4, lamPts x' y' k ≫ pullback.fst B.hom f = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) ((![{0, 1}, {0}, {1}, ∅] : Fin 4 → Finset (Fin 2)) k)).left := by
  intro S₀ S B₀ _ _ B _ _ f β β₂ hβ hsq Y x y x' y' hx hy k
  have hm : ((lift x y).left ≫ β₂) ≫ (G2 B).hom = (Over.mk (Y.hom ≫ f)).hom := by
    have h1 : (G2 B).hom = (fst B B).left ≫ B.hom := (Over.w (fst B B)).symm
    rw [h1, Category.assoc, ← Category.assoc β₂, hsq.1, Category.assoc, hβ.1.w, ← Category.assoc,
      ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Category.assoc x.left, Over.w x]
    rfl
  let u : Over.mk (Y.hom ≫ f) ⟶ G2 B := Over.homMk ((lift x y).left ≫ β₂) hm
  have key : ∀ g : G2 B ⟶ B, (lift x y).left ≫ β₂ ≫ g.left = (u ≫ g).left := fun g => by
    simp [u]
  have hu1 : (u ≫ fst B B).left = x.left ≫ β := by
    rw [← key, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst]
  have hu2 : (u ≫ snd B B).left = y.left ≫ β := by
    rw [← key, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd]
  have h := isGrpPullback_pullback B f
  have m : (x' * y').left ≫ pullback.fst B.hom f = ((u ≫ fst B B) * (u ≫ snd B B)).left :=
    (h.2 Y x' y' _ _ (hu1.trans hx.symm) (hu2.trans hy.symm)).symm
  have o : (1 : Y ⟶ (Over.pullback f).obj B).left ≫ pullback.fst B.hom f =
      (1 : Over.mk (Y.hom ≫ f) ⟶ B).left :=
    congrArg (fun z => z.left) (map_one (pushHom h Y))
  have hx2 : x2 B = ![fst B B, snd B B] := rfl
  fin_cases k
  · show (x' * y').left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) {0, 1}).left
    rw [hx2, psum_two_01, key, comp_mul, m]
  · show x'.left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) {0}).left
    rw [hx2, psum_two_0, key, hu1, hx]
  · show y'.left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) {1}).left
    rw [hx2, psum_two_1, key, hu2, hy]
  · show (1 : Y ⟶ (Over.pullback f).obj B).left ≫ _ = (lift x y).left ≫ β₂ ≫ (psum B (x2 B) ∅).left
    rw [hx2, psum_two_e, key, o]
    congr 1
    simp [Hom.one_def]

end GlobalTheory.PairPts
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PsiRing GlobalTheory.PrimCocycle

noncomputable section

namespace GlobalTheory.RefPull

open GlobalTheory.HalfBC

theorem refines_pull : ∀ {V V₀ V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₀] [IsDomain V₀] [CommRing V₁] [IsDomain V₁] (Q : Data V) (ρ₀ : V →+* V₀) (D₀ : DegPre V₀) (e₀ : D₀.X ≃+ Q.X), Function.Injective ρ₀ → Refines Q ρ₀ D₀ e₀ → ∀ (ρ : V₀ →+* V₁) (D₁ : DegPre V₁) (hD : IsPullDeg ρ D₀ D₁), Function.Injective ρ → Refines Q (ρ.comp ρ₀) D₁ (hD.xe.trans e₀) := by
  intro V V₀ V₁ _ _ _ _ _ _ Q ρ₀ D₀ e₀ hρ₀ H ρ D₁ hD hρ
  obtain ⟨β₀, β₂₀, w₀, pb₀, sq₀, gen₀, c₀, tau₀⟩ := H
  have gp := pull_grp hD
  have hΛQ : (abelian₂ Q.B Q.M.L).IsLB := DVR.linComb_isLB _ Q.M.isLB _ _
  have hΛ₀ : (abelian₂ D₀.P.A D₀.P.L).IsLB := DVR.linComb_isLB _ D₀.P.isLB _ _
  have hΛ₁ : (abelian₂ D₁.P.A D₁.P.L).IsLB := DVR.linComb_isLB _ D₁.P.isLB _ _
  obtain ⟨w', T⟩ := exists_comp hΛ₀ w₀ (lamIso gp hD.w) ((isGen_iff _).1 gen₀)
    (pgen_lamIso gp hD.w ((isGen_iff _).1 hD.w_gen)) hΛQ hΛ₁
  set β : D₁.P.A.left ⟶ D₀.P.A.left := hD.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf ρ) with hβ
  let gam : FractionRing V₀ →+* FractionRing V₁ := GlobalTheory.ArcPull.fracMap hρ
  have hgam : ∀ r, gam (algebraMap V₀ _ r) = algebraMap V₁ _ (ρ r) := GlobalTheory.ArcPull.fracMap_algebraMap hρ
  have sgam := gam_comm ρ gam hgam
  obtain ⟨κ₁, hκ₁, hκu⟩ := exists_kappa ρ₀ ρ gam hgam hρ₀
  have key : ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 D₁.P.A).left) (z : Z) J J₁ J', Good Q.M.L z J → Good D₀.P.L z J₁ →
      Good D₁.P.L z J' → lamVal w' p z J J' = lamVal w₀ (p ≫ sqOf gp) z J J₁ *
        ∏ I, gw hD.w (p ≫ lamφ D₁.P.A I) z (J₁ ((p ≫ lamφ D₁.P.A I) ≫ β)) (J' (p ≫ lamφ D₁.P.A I)) ^ lamε I := by
    intro Z p z J J₁ J' hJ hJ₁ hJ'
    have t := T Z p z (fun I => J (p ≫ (sqOf gp ≫ β₂₀) ≫ lamφ Q.B I))
      (fun I => J₁ ((p ≫ sqOf gp) ≫ lamφ D₀.P.A I)) (fun I => J' (p ≫ lamφ D₁.P.A I))
      (Set.mem_iInter.2 fun I => hJ (p ≫ (sqOf gp ≫ β₂₀) ≫ lamφ Q.B I))
      (Set.mem_iInter.2 fun I => hJ₁ ((p ≫ sqOf gp) ≫ lamφ D₀.P.A I))
      (Set.mem_iInter.2 fun I => hJ' (p ≫ lamφ D₁.P.A I))
    refine t.trans (congrArg₂ (· * ·) ?_ ?_)
    · show _ = gw w₀ (p ≫ sqOf gp) z (fun I => J ((p ≫ sqOf gp) ≫ β₂₀ ≫ lamφ Q.B I))
        (fun I => J₁ ((p ≫ sqOf gp) ≫ lamφ D₀.P.A I))
      simp only [Category.assoc]
    · rw [gw_lamIso gp hD.w p z _ _ (fun I => by
        have := hJ₁ ((p ≫ sqOf gp) ≫ lamφ D₀.P.A I)
        rw [Category.assoc, sqOf_lamφ, ← Category.assoc] at this ⊢
        exact this) (fun I => hJ' (p ≫ lamφ D₁.P.A I))]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [Category.assoc, sqOf_lamφ, ← Category.assoc]
  refine ⟨β ≫ β₀, sqOf gp ≫ β₂₀, w', ?_, ⟨?_, ?_⟩, (isGen_iff _).2 (T.pgen_comp hΛ₀ ((isGen_iff _).1 gen₀)
    (pgen_lamIso gp hD.w ((isGen_iff _).1 hD.w_gen))), ?_, ?_⟩
  · exact (IsGrpPullback.comp gp pb₀).congr (spMap_comp_spMap' ρ₀ ρ) rfl
  · rw [Category.assoc, sq₀.1, ← Category.assoc, (isSquare_sqOf gp).1, Category.assoc]
  · rw [Category.assoc, sq₀.2, ← Category.assoc, (isSquare_sqOf gp).2, Category.assoc]
  · intro a
    show (D₁.c a).left ≫ β ≫ β₀ = spMap (ρ.comp ρ₀) ≫ (Q.c (e₀ (hD.xe a))).left
    rw [← Category.assoc, hβ, hD.c_pr, Category.assoc, c₀, ← Category.assoc, spMap_comp_spMap']
  · intro κ hκ a b z J J' hJ hJ'
    obtain rfl := hκu κ hκ
    choose J₁ hJ₀ using fun χ : (TK V₁).left ⟶ D₀.P.A.left => exists_chart D₀.P.isLB (χ z)
    have hJ₁ : Good D₀.P.L z J₁ := hJ₀
    let g₀ : (TK V₁).left ⟶ (TK V₀).left := spMap gam
    have hx : ∀ χ, D₁.xK χ ≫ β = g₀ ≫ D₀.xK (hD.xe χ) := fun χ => by
      show (jK V₁ ≫ (D₁.c χ).left) ≫ β = spMap gam ≫ jK V₀ ≫ (D₀.c (hD.xe χ)).left
      rw [Category.assoc, hβ, hD.c_pr, ← Category.assoc, ← sgam, Category.assoc]
    have hP : (lift (toUnit (TK V₁) ≫ D₁.c a) (toUnit (TK V₁) ≫ D₁.c b)).left ≫ sqOf gp =
        g₀ ≫ (lift (toUnit (TK V₀) ≫ D₀.c (hD.xe a)) (toUnit (TK V₀) ≫ D₀.c (hD.xe b))).left := by
      apply pullback.hom_ext
      · show _ ≫ (fst D₀.P.A D₀.P.A).left = _ ≫ (fst D₀.P.A D₀.P.A).left
        rw [Category.assoc, (isSquare_sqOf gp).1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc,
          ← Over.comp_left, lift_fst]
        exact hx a
      · show _ ≫ (snd D₀.P.A D₀.P.A).left = _ ≫ (snd D₀.P.A D₀.P.A).left
        rw [Category.assoc, (isSquare_sqOf gp).2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc,
          ← Over.comp_left, lift_snd]
        exact hx b
    have t₁ := tau₀ κ₁ hκ₁ (hD.xe a) (hD.xe b) (g₀ z) (fun ψ => J (g₀ ≫ ψ)) (fun ψ => J₁ (g₀ ≫ ψ))
      (fun ψ => hJ (g₀ ≫ ψ)) (fun ψ => hJ₁ (g₀ ≫ ψ))
    have t₂ := (congrArg (Units.map (g₀.stalkMap z).hom.toMonoidHom) t₁).trans (map_mul _ _ _)
    have n₁ : val (D₀.tau (hD.xe a) (hD.xe b)) (g₀ ≫ 𝟙 _) z J₁ = Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (D₀.tau (hD.xe a) (hD.xe b)) (𝟙 _) (g₀ z) (fun ψ => J₁ (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ (𝟙 _) g₀ z J₁ hJ₁).2.2.1 _)
    have nQ : val (Q.tau (e₀ (hD.xe a)) (e₀ (hD.xe b))) (g₀ ≫ κ₁) z J = Units.map (g₀.stalkMap z).hom.toMonoidHom
        (val (Q.tau (e₀ (hD.xe a)) (e₀ (hD.xe b))) κ₁ (g₀ z) (fun ψ => J (g₀ ≫ ψ))) :=
      Units.ext ((GlobalTheory.values_natural _ _ _ _ _ _ _ _ κ₁ g₀ z J hJ).2.2.1 _)
    rw [Category.comp_id] at n₁
    have A := n₁.trans (t₂.trans (congrArg₂ (· * ·) (lamVal_comp w₀ g₀ _ z J J₁ hJ hJ₁).symm nQ.symm))
    let h : ((TK V₁).left ⟶ D₁.P.A.left) → ((TK V₁).left.presheaf.stalk z)ˣ :=
      fun q => gw hD.w q z (J₁ (q ≫ β)) (J' q)
    have tv := GlobalTheory.ArcPull.tau_val hD g₀ (𝟙 _) (GlobalTheory.ArcPull.fracMap_sq hρ) hJ₁ hJ' a b
    have K := (key _ (lift (toUnit (TK V₁) ≫ D₁.c a) (toUnit (TK V₁) ≫ D₁.c b)).left z J J₁ J' hJ hJ₁ hJ').trans
      (congrArg₂ (· * ·) (congrArg (fun q => lamVal w₀ q z J J₁) hP)
        (prod_lam (DVR.cP D₁ (TK V₁) a) (DVR.cP D₁ (TK V₁) b) h))
    have o₀ : ∀ x, h (DVR.cP D₁ (TK V₁) x).left = GlobalTheory.ArcPull.om hD.w z J₁ J' (D₁.xK x) := fun _ => rfl
    have o₁ : h (1 : TK V₁ ⟶ D₁.P.A).left = GlobalTheory.ArcPull.om hD.w z J₁ J' (1 : TK V₁ ⟶ D₁.P.A).left := rfl
    rw [← DVR.cPoint_add] at K
    simp only [o₀, o₁] at K
    simp only [Category.id_comp] at tv
    rw [K]
    show _ = _ * val (Q.tau (e₀ (hD.xe a)) (e₀ (hD.xe b))) (spMap gam ≫ κ₁) z J
    apply Additive.ofMul.injective
    have eA := congrArg Additive.ofMul A
    have eT := congrArg Additive.ofMul tv
    simp only [ofMul_mul, ofMul_inv] at eA eT ⊢
    linear_combination (norm := abel) eA - eT

end GlobalTheory.RefPull
end
end

section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FlagTan

theorem eq_const_of_isKS_zero : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
      (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K)
      (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → IsTanX y x' → IsKS (psiSet H) y x' 0 →
        x' = spMap (algebraMap K (DualNumber K)) ≫ y.x := by
  intro P G E _ _ _ H Dw l Xo c K _ _ y x' hpq hx hks
  obtain ⟨A, _, A', _, π, π', i, h, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_group_lift_kodaira_spencer_zero P E H Dw l Xo c K y x' hpq hx hks
  obtain ⟨q, hq1, hq2⟩ := GlobalTheory.T.group_lift_tangent_compatibility P G E H Dw l Xo c K y x' hpq hx A A' π π' i h h1 h2 h3 h4
  obtain ⟨o, m⟩ := GlobalTheory.obj_pull E H Dw l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ Xo.s (x' ≫ Xo.s) x' rfl rfl
    (by rw [spMap, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]) Xo.univ
  have e := Xo.unram K x' o m
    (GlobalTheory.T.group_lift_tangent_uniqueness P G E H Dw l Xo c K y x' hpq hx A A' π π' i q h h1 h2 h3 hq1 hq2 o m)
  rw [← hx.2]
  conv_lhs => rw [e]
  rfl

end GlobalTheory.FlagTan
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
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.abelian_part_constant_heat_operator_symbol_in_maximal_ideal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ (B' : Over (Sp (DualNumber k))) (_ : GrpObj B') (π₁ π₂ : B'.left ⟶ P.D.toPre.P.A.left), IsGrpPullback B' P.D.toPre.P.A (spMap ρ) π₁ ∧ IsGrpPullback B' P.D.toPre.P.A (spMap (constHom ρ)) π₂ ∧ (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) := by
  first | exact @GlobalTheory.Heat.AbConstAlong.abelian_part_const | exact GlobalTheory.Heat.AbConstAlong.abelian_part_const | (intros; apply GlobalTheory.Heat.AbConstAlong.abelian_part_const <;> assumption)
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

namespace GlobalTheory.InvCoefUniq

open TrivSqZeroExt (inl inr)

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {n : ℕ}

theorem valR_coef_eq_zero [Smooth G.hom] (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) {dd : Fin n → Fld G.left}
    (hd : ∀ a, IsInv G (v a) (dd a)) {W : G.left.Opens} (hW : IsAffineOpen W) (c : Fin n → Γ(G.left, W))
    (hc : ∀ f, ∑ a, c a * dd a W f = 0) (S : Type) [CommRing S] (g : Sp S ⟶ G.left) (hg : ⊤ ≤ g ⁻¹ᵁ W)
    (a : Fin n) : valR g W (c a) = 0 := by
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) (g ≫ G.hom)
  let φ : R →+* S := φ'.hom
  have hφ : g ≫ G.hom = spMap φ := hφ'.symm
  letI : Algebra R S := φ.toAlgebra
  let z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := R) S ⟶ G := Over.homMk g hφ
  let s : Fin n → S := fun b => valR g W (c b)
  obtain ⟨u, hb, hu⟩ := GlobalTheory.HeatMod.TorField.exists_isLieBasis v
  let e : Fin n → DualNumber S := fun b => inr (s b)
  have he : ∀ i j, e i * e j = 0 := fun _ _ => TrivSqZeroExt.inr_mul_inr _ _ _
  obtain ⟨a₁, a₂⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (GlobalTheory.SqZero.inlS R S).toRingHom g W hg
  obtain ⟨b₁, b₂⟩ := GlobalTheory.HeatMod.TorField.valR_prod hu hb.1 hd e he
    (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) W a₁ Finset.univ
  have a₃ : ∀ x, valR (A := DualNumber S) (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z).left W x =
      inl (valR g W x) := a₂
  have key : ∀ f, ∑ i, s i * valR g W (dd i W f) = 0 := fun f => by
    have := congrArg (valR g W) (hc f)

    simpa [GlobalTheory.Points.valR_eq g W hg, map_sum, map_mul, s] using this
  have hP : GlobalTheory.SqZero.lieExp u e (fun i => he i i) *
      (ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z) =
      ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.inlS R S) ≫ z := by
    refine Over.OverMorphism.ext (GlobalTheory.Points.ext_of_valR hW b₁ a₁ fun f => ?_)
    refine (b₂ f).trans ?_
    rw [add_eq_left]
    simp only [a₃, e]
    ext
    · simp [TrivSqZeroExt.fst_sum]
    · simpa [TrivSqZeroExt.snd_sum] using key f
  have h1 : GlobalTheory.SqZero.lieExp u e (fun i => he i i) = 1 := mul_eq_right.1 hP
  have h0 : GlobalTheory.SqZero.lieExp u (fun _ => (0 : DualNumber S)) (fun _ => mul_zero _) = 1 :=
    GlobalTheory.SqZero.lieExp_eq_one hb.1 _ (fun _ => rfl) _
  have hJ := GlobalTheory.SqZero.ker_fst_sq (R := R) (S := S) S
  have hz := ((GlobalTheory.SqZero.expBij (DualNumber S) hb) _ hJ).1 e (fun _ => 0)
    (fun i => by simp [RingHom.mem_ker, e]) (fun _ => zero_mem _) (fun i => he i i) (fun _ => mul_zero _)
    (h1.trans h0.symm)
  have := congrArg TrivSqZeroExt.snd (congrFun hz a)
  simpa [e, s] using this

theorem coef_eq_zero : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom → ∀ (n : ℕ) (v : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) G)) (dd : Fin n → Fld G.left), (∀ a, IsInv G (v a) (dd a)) → ∀ (W : G.left.Opens) (c : Fin n → Γ(G.left, W)), (∀ O, O ≤ W → ∀ f, ∑ a, rsT (c a) O * dd a O f = 0) → ∀ a, c a = 0 := by
  intro R _ G _ _ hs n v dd hd W c hc a
  haveI := hs
  refine GlobalTheory.KS.eq_of_rsT_eq (J := {W' : G.left.affineOpens // W'.1 ≤ W}) (fun W' => W'.1.1) (fun W' => W'.2)
    ?_ (c a) 0 fun W' => ?_
  · intro x hx
    obtain ⟨W', hW', hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W', hW'⟩, hWU⟩, hxW⟩
  · rw [GlobalTheory.KS.rsT_zero]
    exact GlobalTheory.Heat.Adjust.eq_zero_of_valR_points _ _ fun S _ g hg =>
      valR_coef_eq_zero v hd W'.1.2 (fun b => rsT (c b) W'.1.1) (hc W'.1.1 W'.2) S g hg a

end GlobalTheory.InvCoefUniq
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

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.FieldCompat

open GlobalTheory.CechKS GlobalTheory.LogKSBal

theorem isTr_comp {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) {G : Over (Sp R)} [GrpObj G]
    {A : Over (Sp K)} [GrpObj A] (m : A.left ⟶ G.left) (hm : IsGrpPullback A G (spMap x₀) m)
    (w : TanM (𝟙 (Sp R)) G) (v : epsR K ⟶ A)
    (hv : v.left ≫ m = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) ≫ (tv w).left) {B : Type} [CommRing B] (φ : K →+* B)
    (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) (y : Sp (DualNumber B) ⟶ A.left) (hy : IsTransl φ x v y) :
    IsTr G (φ.comp x₀) (x ≫ m) w (y ≫ m) := by
  obtain ⟨x₁, v₁, a, b, rfl⟩ := hy
  have dc : (dualMap φ).comp (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) = dualMap (φ.comp x₀) :=
    RingHom.ext fun c ↦ by ext <;> simp [dualMap, ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  obtain ⟨p, q, h₁, h₂, h₃⟩ := exists_mul_of_isGrpPullback hm _ x₁ v₁
    (spMap (algebraMap B (DualNumber B)) ≫ (x ≫ m) ≫ G.hom) (by
      change _ = spMap ((algebraMap B (DualNumber B)).comp φ) ≫ spMap x₀
      rw [Category.assoc, hm.1.w, ← Category.assoc x, hx, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp'])
  refine ⟨p, q, ?_, ?_, h₃⟩
  · rw [h₁, a]; exact Category.assoc _ _ _
  · rw [h₂, b, ← dc, ← GlobalTheory.LogKSLoc.spMap_comp' (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) (dualMap φ)]
    refine (Category.assoc _ _ _).trans ?_
    rw [hv]
    exact (Category.assoc (spMap (dualMap φ)) (spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀)) _).symm

theorem invField_baseChange : ∀ {R : Type} [CommRing R] {K : Type} [Field K] (x₀ : R →+* K) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ G.left), IsGrpPullback A G (spMap x₀) m → ∀ (w : TanM (𝟙 (Sp R)) G) (e : Fld G.left), IsInv G w e → ∀ (v : epsR K ⟶ A), IsTangent v → v.left ≫ m = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR x₀) ≫ (tv w).left → ∀ (dd : ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)), GlobalTheory.KS.IsInvDer v dd → ∀ (O : G.left.Opens) (f : Γ(G.left, O)), dd (m ⁻¹ᵁ O) ((m.app O).hom f) = pbT m (e O f) (m ⁻¹ᵁ O) := by
  intro R _ K _ x₀ G _ _ A _ _ m hm w e he v hvt hv dd hdd O f
  refine ext_valR _ _ fun B _ y hy => ?_
  have hb : y ≫ A.hom = spMap (Spec.preimage (y ≫ A.hom)).hom := (Spec.map_preimage _).symm
  generalize (Spec.preimage (y ≫ A.hom)).hom = β at hb
  obtain ⟨y', hy'⟩ := exists_isTransl β y hb v
  have hO : ⊤ ≤ y' ⁻¹ᵁ (m ⁻¹ᵁ O) := le_preimage_of_red (hy'.red hvt) hy
  rw [← snd_valR_transl hvt hdd hy' hy, CoeffWt.valR_app _ _ _ hO, valR_pbT y m le_rfl hy]
  refine he.2 B (β.comp x₀) (y ≫ m) (y' ≫ m) O f ?_ hy (isTr_comp x₀ m hm w v hv β y hb y' hy')
  rw [Category.assoc, hm.1.w, ← Category.assoc, hb, GlobalTheory.LogKSLoc.spMap_comp']

end GlobalTheory.Heat.FieldCompat
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

theorem _root_.GlobalTheory.T.raynaud_cech_relation_dlog_descends_to_abelian_part : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (δH : Fld Y.H.left) (δ : Fld Q.P.A.left), (∀ (U : Q.P.A.left.Opens) (s : Γ(Q.P.A.left, U)) (W : Y.H.left.Opens), W ≤ Y.q.left ⁻¹ᵁ U → δH W (pbT Y.q.left s W) = pbT Y.q.left (δ U s) W) → ∀ (K : Type) (Wk : K → Y.H.left.Opens) (jk : K → Q.P.L.ι), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → (∀ k, Wk k ≤ Y.q.left ⁻¹ᵁ Q.P.L.U (jk k)) → ∀ (P : ∀ k, Γ(Y.H.left, Wk k)), (∀ k, IsWt Y 0 _ (P k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (P k') Wo - rsT (P k) Wo = dlg Y.H Y.q.left Q.P.L δH (jk k) (jk k') Wo) → ∃ (V : K → Q.P.A.left.Opens) (b : ∀ k, Γ(Q.P.A.left, V k)), ⨆ k, V k = ⊤ ∧ (∀ k, V k ≤ Q.P.L.U (jk k)) ∧ ∀ k k', rsT (b k') (V k ⊓ V k') - rsT (b k) (V k ⊓ V k') = dlg Q.P.A (𝟙 _) Q.P.L δ (jk k) (jk k') (V k ⊓ V k') := by
  first | exact @GlobalTheory.Heat.AbDescent.descent | exact GlobalTheory.Heat.AbDescent.descent | (intros; apply GlobalTheory.Heat.AbDescent.descent <;> assumption)
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

theorem _root_.GlobalTheory.T.raynaud_weight_zero_compatible_functions_eq_base_constant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (K : Type) (Wk : K → Y.H.left.Opens), (∀ k, ∃ V : Q.P.A.left.Opens, Wk k = Y.q.left ⁻¹ᵁ V) → ⨆ k, Wk k = ⊤ → ∀ F : ∀ k, Γ(Y.H.left, Wk k), (∀ k, IsWt Y 0 _ (F k)) → (∀ k k' (Wo : Y.H.left.Opens), Wo ≤ Wk k ⊓ Wk k' → rsT (F k) Wo = rsT (F k') Wo) → ∃ r : R, ∀ k, F k = constFn Y.H.hom _ r := by
  first | exact @GlobalTheory.Heat.AbConstGlob.main | exact GlobalTheory.Heat.AbConstGlob.main | (intros; apply GlobalTheory.Heat.AbConstGlob.main <;> assumption)
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

theorem _root_.GlobalTheory.T.existsUnique_pullback_of_raynaudTorusWeight_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (V : Q.P.A.left.Opens) (f : Γ(Y.H.left, Y.q.left ⁻¹ᵁ V)), IsWt Y 0 _ f → ∃! f' : Γ(Q.P.A.left, V), pbT Y.q.left f' (Y.q.left ⁻¹ᵁ V) = f := by
  first | exact @GlobalTheory.Heat.exists_unique_pbT_of_isWt_zero | exact GlobalTheory.Heat.exists_unique_pbT_of_isWt_zero | (intros; apply GlobalTheory.Heat.exists_unique_pbT_of_isWt_zero <;> assumption)
end
