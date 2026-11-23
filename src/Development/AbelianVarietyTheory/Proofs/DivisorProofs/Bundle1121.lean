module

public import Mathlib.RingTheory.Henselian
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle070
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle007
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem existsUnique_torsion_lift_of_henselian : ∀ (W : Type) [CommRing W] [HenselianLocalRing W] (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (p : Sp W ⟶ S) (N : ℕ), IsUnit (N : W) → ∀ x₀ : Over.mk (spMap (residue W) ≫ p) ⟶ G, x₀ ^ N = 1 → ∃! x : Over.mk p ⟶ G, x ^ N = 1 ∧ spMap (residue W) ≫ x.left = x₀.left := by
  intro W _ _ S G _ _ hG p N hN x₀ hx₀
  have := hG.smooth
  let G' := (Over.pullback p).obj G
  have : Smooth G'.hom := inferInstanceAs (Smooth (pullback.snd G.hom p))
  have hN' : IsUnit (N : Γ(Sp W, ⊤)) := by
    simpa using hN.map (Scheme.ΓSpecIso (CommRingCat.of W)).inv.hom
  have : Etale (mulN G' N).left := GrpTangent.etale_mulN G' hN'
  let T : Over (Sp W) := Over.mk (𝟙 (Sp W))
  let T₀ : Over (Sp W) := Over.mk (spMap (residue W))
  let r : T₀ ⟶ T := Over.homMk (spMap (residue W)) (by simp [T, T₀])
  let e := TorsionLift.ptsEquiv p G T p (Category.id_comp p)
  let e₀ := TorsionLift.ptsEquiv p G T₀ (spMap (residue W) ≫ p) rfl
  have hpow : ∀ {Z : Over (Sp W)} (y : Z ⟶ G'),
      y ^ N = 1 ↔ y.left ≫ (mulN G' N).left = (1 : Z ⟶ G').left := by
    intro Z y
    rw [← GrpTangent.comp_mulN]
    exact ⟨fun h => by rw [← Over.comp_left, h],
      fun h => Over.OverMorphism.ext (by rw [Over.comp_left, h])⟩
  have key : ∀ y₀ : T₀ ⟶ G', y₀ ^ N = 1 → ∃! y : T ⟶ G', y ^ N = 1 ∧ r ≫ y = y₀ := by
    intro y₀ hy₀
    have hone : (1 : T₀ ⟶ G').left = spMap (residue W) ≫ (1 : T ⟶ G').left := by
      rw [← comp_one r, Over.comp_left]
      rfl
    obtain ⟨l, ⟨hl₁, hl₂⟩, hl₃⟩ := existsUnique_lift_of_etale_of_henselian (mulN G' N).left
      (residue W) residue_surjective y₀.left (1 : T ⟶ G').left
      (by rw [(hpow y₀).1 hy₀, hone])
    have hlw : l ≫ G'.hom = T.hom := by
      rw [← Over.w (mulN G' N), ← Category.assoc, hl₂]
      exact Over.w _
    refine ⟨Over.homMk l hlw, ⟨(hpow _).2 hl₂, Over.OverMorphism.ext hl₁⟩, ?_⟩
    rintro y ⟨hy₁, hy₂⟩
    exact Over.OverMorphism.ext (hl₃ y.left ⟨congrArg Over.Hom.left hy₂, (hpow y).1 hy₁⟩)
  have h := key (e₀.symm x₀) (by rw [← map_pow, hx₀, map_one])
  refine (e.toEquiv.existsUnique_congr fun y => ?_).1 h
  change _ ↔ e y ^ N = 1 ∧ _ ≫ (e y).left = _
  rw [← map_pow, map_eq_one_iff e e.injective, MulEquiv.eq_symm_apply]
  refine and_congr_right fun _ => ?_
  have : (e₀ (r ≫ y)).left = spMap (residue W) ≫ (e y).left := by
    rw [TorsionLift.ptsEquiv_left, TorsionLift.ptsEquiv_left, Over.comp_left, Category.assoc]
    rfl
  rw [← this]
  exact ⟨fun h => by rw [h], Over.OverMorphism.ext⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AxisPairing

theorem weilIs_comp_eq_one_of_pull_isGen {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left)
    (hA : IsAbelianScheme A) (hP : P.IsLB) (ψ : A ⟶ G2 A) [IsMonHom ψ]
    (hg : ∃ t : (P.pull ψ.left).Gen, t.IsGen) {n : ℤ} {T : Over S} {u v : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (h : Out.WeilIs (G2 A) P n (u ≫ ψ) (v ≫ ψ) c) : c = 1 := by
  have hL : (P.pull ψ.left).IsLB := LB.isLB_pull hP ψ.left
  have h0 : GlobalTheory.CechPic.cls _ hL = 0 := (GlobalTheory.CechPic.cls_eq_zero_iff hL).2 hg
  have hw : LBIso (lbPow (P.pull ψ.left) 1) (P.pull ψ.left) := by
    have hp : (lbPow (P.pull ψ.left) 1).IsLB := LB.isLB_pull hL _
    refine (GlobalTheory.CechPic.cls_eq_iff hp hL).1 ?_
    rw [GlobalTheory.CechPic.cls_lbPow hL 1 hp, one_smul]
  have h1 := GlobalTheory.WeilIsogeny.weilIs_pull_hom GlobalTheory.globalFns_holds hA hL hP ψ hw h
  rw [Nat.cast_one, _root_.mul_one] at h1
  have iso : LBIso (lbPow (P.pull ψ.left) 0) ((P.pull ψ.left).pull (𝟙 A : A ⟶ A).left) := by
    apply (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_pull hL _)).1
    rw [GlobalTheory.CechPic.cls_lbPow hL, GlobalTheory.CechPic.cls_pull hL,
      Over.id_left, GlobalTheory.CechPic.pull_id, h0, zero_smul]
  have h2 := (GlobalTheory.weilIs_along_hom GlobalTheory.globalFns_holds S A A (𝟙 A)
    (P.pull ψ.left) (P.pull ψ.left) 0 n T u v c c hA hA hL hL inferInstance iso
    (by simpa using h1)).2 h1
  simpa using h2

theorem axes : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c : Γ(T.left, ⊤)ˣ), (Out.WeilIs (G2 A) P n (lift u 1) (lift v 1) c → c = 1) ∧ (Out.WeilIs (G2 A) P n (lift 1 u) (lift 1 v) c → c = 1) := by
  intro S A _ _ P hA hP h₂ h₁ n T u v c
  have := GlobalTheory.Raynaud.ProdToric.isMonHom_lift_id_one A A
  have := GlobalTheory.Raynaud.ProdToric.isMonHom_lift_one_id A A
  have e₁ : ∀ w : T ⟶ A, w ≫ lift (𝟙 A) (1 : A ⟶ A) = lift w 1 := fun w => by
    rw [comp_lift, Category.comp_id, MonObj.comp_one]
  have e₂ : ∀ w : T ⟶ A, w ≫ lift (1 : A ⟶ A) (𝟙 A) = lift 1 w := fun w => by
    rw [comp_lift, Category.comp_id, MonObj.comp_one]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← e₁ u, ← e₁ v] at h
    exact weilIs_comp_eq_one_of_pull_isGen P hA hP _ h₁ h
  · rw [← e₂ u, ← e₂ v] at h
    exact weilIs_comp_eq_one_of_pull_isGen P hA hP _ h₂ h

end GlobalTheory.AxisPairing
end
