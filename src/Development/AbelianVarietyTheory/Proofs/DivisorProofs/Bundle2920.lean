module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle066
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2794
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2857
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle015
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle068
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle071
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2708
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2795
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2854

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem lbIso_pull_pull_comp {X Y Z : Scheme.{0}} {M : LB X} (hM : M.IsLB) (F : Y ⟶ X) (g : Z ⟶ Y) :
    LBIso ((M.pull F).pull g) (M.pull (g ≫ F)) :=
  Geo.Tor.LBIso.chartPull (h := g) (Geo.Tor.chartPullPull (M.pull F) g g rfl)
    (Geo.Tor.chartPullSame M (fun _ => g ≫ F) (fun _ => F) (fun _ => 1) g (fun _ => rfl))
    (GlobalTheory.PolBaseChange.lbIso_refl (LB.isLB_pull hM F))

theorem exists_gen_pull_pull_iff {X Y Z : Scheme.{0}} {M : LB X} (hM : M.IsLB) (F : Y ⟶ X) (g : Z ⟶ Y) :
    (∃ t : LB.Gen ((M.pull F).pull g), t.IsGen) ↔ ∃ t : LB.Gen (M.pull (g ≫ F)), t.IsGen := by
  have h₁ := LB.isLB_pull (LB.isLB_pull hM F) g
  have h₂ := LB.isLB_pull hM (g ≫ F)
  exact ⟨GlobalTheory.CM.PairingIso.exists_gen_of_lbIso h₁ h₂ (lbIso_pull_pull_comp hM F g),
    GlobalTheory.CM.PairingIso.exists_gen_of_lbIso h₂ h₁ (Geo.Tor.LBIso.symm (lbIso_pull_pull_comp hM F g))⟩

theorem left_tensor_ext {S : Scheme.{0}} {X Y : Over S} {Z : Scheme.{0}} (u v : Z ⟶ (X ⊗ Y).left)
    (h₁ : u ≫ (fst X Y).left = v ≫ (fst X Y).left) (h₂ : u ≫ (snd X Y).left = v ≫ (snd X Y).left) : u = v := by
  rw [Over.fst_left] at h₁
  rw [Over.snd_left] at h₂
  exact pullback.hom_ext h₁ h₂

theorem pull_gen_lam_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (inc : G ⟶ G'), IsMonHom inc → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∀ (T : Over (Sp (FractionRing R))) (x : T ⟶ ((Over.pullback (jK R)).obj G)), (∃ t : LB.Gen ((((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left), t.IsGen) → ∃ t : LB.Gen (letI := A'.isAb.comm; (abelian₂ A'.A A'.L).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ (x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom)) (fst ((Over.pullback (jK R)).obj G) T ≫ ((Over.pullback (jK R)).map inc ≫ U'.gen.hom) ≫ oA.act F.f) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 A'.A).left), t.IsGen := by
  intro R _ _ _ D D' F A' G' _ _ U' oA oG hlin G _ _ inc hinc κ₀ hκ T x ht
  letI := A'.isAb.comm
  haveI : IsMonHom U'.gen.hom := U'.gen_hom
  have hL' : U'.LG.L.IsLB := U'.LG.isLB
  have hQ : (abelian₂ G' U'.LG.L).IsLB := DVR.linComb_isLB _ hL' _ _
  have hA : A'.L.IsLB := A'.isLB
  have hQA : (abelian₂ A'.A A'.L).IsLB := DVR.linComb_isLB _ hA _ _
  obtain ⟨β₂, hβ₂, Hβ⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (jK R) G' ((Over.pullback (jK R)).obj G')
    (pullback.fst G'.hom (jK R)) (Geo.Tor.isGrpPullback_pullback G' (jK R))
  have E₁ := Hβ U'.LG.L (U'.LG.L.pull (pullback.fst G'.hom (jK R))) _ (abelian₂ G' U'.LG.L) (𝟙 _) hL'
    (LB.isLB_pull hL' _) hQ (GlobalTheory.PolBaseChange.lbIso_refl (LB.isLB_pull hL' _))
    (Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl hQ))
  obtain ⟨γ₂, hγ₂, Hγ⟩ := lbIso_lam_pull_of_isGrpPullback _ _ (𝟙 _) A'.A ((Over.pullback (jK R)).obj G')
    U'.gen.hom.left (Geo.Tor.isGrpPullback_of_iso U'.gen)
  have E₂ := Hγ A'.L (U'.LG.L.pull (pullback.fst G'.hom (jK R))) _ (abelian₂ A'.A A'.L) (𝟙 _) hA
    (LB.isLB_pull hL' _) hQA (Geo.Tor.LBIso.symm U'.ext)
    (Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullId _) (Geo.Tor.chartPullPull _ (𝟙 _) (𝟙 _) rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl hQA))
  have E₃ := Geo.Tor.LBIso.trans (LB.isLB_pull hQ _) (DVR.linComb_isLB _ (LB.isLB_pull hL' _) _ _)
    (LB.isLB_pull hQA _) (Geo.Tor.LBIso.symm E₁) E₂
  let m := (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x ≫ (Over.pullback (jK R)).map inc)
    (fst ((Over.pullback (jK R)).obj G) T ≫ (Over.pullback (jK R)).map inc ≫ (Over.pullback (jK R)).map (oG.act F.f))).left
  have E₄ := Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullPull _ m m rfl) (Geo.Tor.chartPullPull _ m m rfl) E₃
  obtain ⟨t, ht⟩ := ht
  let φl := (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left
  let ψl := (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left
  let χl := (lift (snd ((Over.pullback (jK R)).obj G) T ≫ (x ≫ ((Over.pullback (jK R)).map inc) ≫ U'.gen.hom)) (fst ((Over.pullback (jK R)).obj G) T ≫ (((Over.pullback (jK R)).map inc) ≫ U'.gen.hom) ≫ oA.act F.f) :
    ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 A'.A).left
  have hinc' : ((Over.pullback (jK R)).map inc).left ≫ pullback.fst G'.hom (jK R) = pullback.fst G.hom (jK R) ≫ inc.left :=
    pullback.lift_fst _ _ _
  have hf' : ((Over.pullback (jK R)).map (oG.act F.f)).left ≫ pullback.fst G'.hom (jK R) = pullback.fst G'.hom (jK R) ≫ (oG.act F.f).left :=
    pullback.lift_fst _ _ _
  have hgen : ((Over.pullback (jK R)).map (oG.act F.f)).left ≫ U'.gen.hom.left = U'.gen.hom.left ≫ (oA.act F.f).left :=
    congrArg Over.Hom.left (hlin.ext F.f)
  have hφ1 : φl ≫ (fst G' G').left = (fst G G).left ≫ inc.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_fst (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f))
  have hφ2 : φl ≫ (snd G' G').left = (snd G G).left ≫ inc.left ≫ (oG.act F.f).left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_snd (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f))
  have hψ1 : ψl ≫ (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)).left = (snd ((Over.pullback (jK R)).obj G) T).left ≫ x.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_fst (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T))
  have hψ2 : ψl ≫ (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)).left = (fst ((Over.pullback (jK R)).obj G) T).left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_snd (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T))
  have hm1 : m ≫ (fst ((Over.pullback (jK R)).obj G') ((Over.pullback (jK R)).obj G')).left = (snd ((Over.pullback (jK R)).obj G) T).left ≫ x.left ≫ ((Over.pullback (jK R)).map inc).left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_fst (snd ((Over.pullback (jK R)).obj G) T ≫ x ≫ ((Over.pullback (jK R)).map inc)) (fst ((Over.pullback (jK R)).obj G) T ≫ ((Over.pullback (jK R)).map inc) ≫ ((Over.pullback (jK R)).map (oG.act F.f))))
  have hm2 : m ≫ (snd ((Over.pullback (jK R)).obj G') ((Over.pullback (jK R)).obj G')).left = (fst ((Over.pullback (jK R)).obj G) T).left ≫ ((Over.pullback (jK R)).map inc).left ≫ ((Over.pullback (jK R)).map (oG.act F.f)).left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_snd (snd ((Over.pullback (jK R)).obj G) T ≫ x ≫ ((Over.pullback (jK R)).map inc)) (fst ((Over.pullback (jK R)).obj G) T ≫ ((Over.pullback (jK R)).map inc) ≫ ((Over.pullback (jK R)).map (oG.act F.f))))
  have hχ1 : χl ≫ (fst A'.A A'.A).left = (snd ((Over.pullback (jK R)).obj G) T).left ≫ x.left ≫ ((Over.pullback (jK R)).map inc).left ≫ U'.gen.hom.left := by
    simpa only [Over.comp_left] using congrArg Over.Hom.left (lift_fst (snd ((Over.pullback (jK R)).obj G) T ≫ (x ≫ ((Over.pullback (jK R)).map inc) ≫ U'.gen.hom)) (fst ((Over.pullback (jK R)).obj G) T ≫ (((Over.pullback (jK R)).map inc) ≫ U'.gen.hom) ≫ oA.act F.f))
  have hχ2 : χl ≫ (snd A'.A A'.A).left = (fst ((Over.pullback (jK R)).obj G) T).left ≫ ((Over.pullback (jK R)).map inc).left ≫ U'.gen.hom.left ≫ (oA.act F.f).left := by
    have := congrArg Over.Hom.left (lift_snd (snd ((Over.pullback (jK R)).obj G) T ≫ (x ≫ ((Over.pullback (jK R)).map inc) ≫ U'.gen.hom)) (fst ((Over.pullback (jK R)).obj G) T ≫ (((Over.pullback (jK R)).map inc) ≫ U'.gen.hom) ≫ oA.act F.f))
    simp only [Over.comp_left, Category.assoc] at this
    exact this
  have eq1 : ψl ≫ κ₀ ≫ φl = m ≫ β₂ ≫ 𝟙 _ := by
    apply left_tensor_ext
    · simp only [Category.assoc, Category.comp_id]
      rw [hφ1, reassoc_of% hκ.1]
      rw [reassoc_of% hψ1]
      rw [hβ₂.1]
      rw [reassoc_of% hm1]
      simp only [Category.assoc, hinc']
    · simp only [Category.assoc, Category.comp_id]
      rw [hφ2, reassoc_of% hκ.2]
      rw [reassoc_of% hψ2]
      rw [hβ₂.2]
      rw [reassoc_of% hm2]
      simp only [Category.assoc, hf']
      rw [reassoc_of% hinc']
  have eq2 : m ≫ γ₂ ≫ 𝟙 _ = χl := by
    apply left_tensor_ext
    · simp only [Category.assoc, Category.comp_id]
      rw [hγ₂.1]
      rw [reassoc_of% hm1, hχ1]
    · simp only [Category.assoc, Category.comp_id]
      rw [hγ₂.2]
      rw [reassoc_of% hm2, hχ2, hgen]
  have hP1 := LB.isLB_pull (LB.isLB_pull (LB.isLB_pull hQ φl) κ₀) ψl
  have hP2 := LB.isLB_pull (LB.isLB_pull hQ (κ₀ ≫ φl)) ψl
  have g₀ := GlobalTheory.CM.PairingIso.exists_gen_of_lbIso hP1 hP2
    (Geo.Tor.LBIso.chartPull (Geo.Tor.chartPullPull _ ψl ψl rfl) (Geo.Tor.chartPullPull _ ψl ψl rfl)
      (lbIso_pull_pull_comp hQ φl κ₀)) ⟨t, ht⟩
  have g₁ := (exists_gen_pull_pull_iff hQ (κ₀ ≫ φl) ψl).1 g₀
  rw [eq1] at g₁
  have g₂ := (exists_gen_pull_pull_iff hQ (β₂ ≫ 𝟙 _) m).2 g₁
  have g₃ := GlobalTheory.CM.PairingIso.exists_gen_of_lbIso (LB.isLB_pull (LB.isLB_pull hQ _) _)
    (LB.isLB_pull (LB.isLB_pull hQA _) _) E₄ g₂
  have g₄ := (exists_gen_pull_pull_iff hQA (γ₂ ≫ 𝟙 _) m).1 g₃
  rw [eq2] at g₄
  exact g₄

end GlobalTheory.Mum
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.UpExt GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section
namespace GlobalTheory.Mum.UpExt

theorem torsion_from_closure : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 → ∃ y : TFK (R := R) (Kb R) ⟶ A.A, y ^ N = 1 ∧ x.left = spMap em.toRingHom ≫ y.left := by
  intro R _ _ A F _ _ _ em N hN x hx
  obtain ⟨K', _, _, hfin, H⟩ := TorsRational.exists_ext_points (FractionRing R) (torsion A.A N)
    (AbTorsionAnyBase.isFinite_and_flat_torsion (Sp (FractionRing R)) A.A A.isAb N hN).1
  let i : K' →ₐ[FractionRing R] Kb R := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let : Algebra K' (Kb R) := i.toRingHom.toAlgebra
  have : IsScalarTower (FractionRing R) K' (Kb R) :=
    IsScalarTower.of_algebraMap_eq' i.comp_algebraMap.symm
  have hmul : x ≫ mulN A.A N = toUnit _ ≫ η := by
    rw [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, hx, Hom.one_def]
  let t0 : _ ⟶ torsion A.A N := pullback.lift x (toUnit _) hmul
  have ht0 : t0 ≫ torsion.ι A.A N = x := pullback.lift_fst _ _ _
  have hs : (TFK (R := R) F).hom = spMap (em.toRingHom.comp (algebraMap (FractionRing R) (Kb R))) :=
    congrArg spMap em.comp_algebraMap.symm
  obtain ⟨w, hw⟩ := H (Kb R) F em.toRingHom t0.left ((Over.w t0).trans hs)
  have hw2 : w ≫ (torsion A.A N).hom = (TFK (R := R) (Kb R)).hom := by
    have : Surjective (spMap em.toRingHom) := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
    have : Epi (spMap em.toRingHom) := Flat.epi_of_flat_of_surjective _
    apply (cancel_epi (spMap em.toRingHom)).1
    rw [← Category.assoc, hw, Over.w t0, hs, ← spMap_comp_spMap]
    rfl
  let w1 : TFK (R := R) (Kb R) ⟶ torsion A.A N := Over.homMk w hw2
  refine ⟨w1 ≫ torsion.ι A.A N, ?_, ?_⟩
  · have hc : torsion.ι A.A N ≫ mulN A.A N = toUnit _ ≫ η :=
      pullback.condition.trans (congrArg (· ≫ η) (toUnit_unique _ _))
    have h1 : (w1 ≫ torsion.ι A.A N) ≫ mulN A.A N = toUnit _ ≫ η := by
      rw [Category.assoc, hc, ← Category.assoc, comp_toUnit]
    rwa [GrpTangent.mulN_eq_pow, MonObj.comp_pow, Category.comp_id, ← Hom.one_def] at h1
  · rw [← ht0, Over.comp_left, ← hw, Category.assoc]
    rfl

end GlobalTheory.Mum.UpExt
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.exists_iso_refinements_same_polarised : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ D : DegPre R), SamePol D₀ D →
  ∃ (β : D₀.P.A ≅ D.P.A) (xe : D₀.X ≃+ D.X), IsMonHom β.hom ∧ (∀ χ, D₀.c χ ≫ β.hom = D.c (xe χ)) ∧
    ∃ wΛ : LB.Iso (abelian₂ D₀.P.A D₀.P.L)
        ((abelian₂ D.P.A D.P.L).pull (lift (fst D₀.P.A D₀.P.A ≫ β.hom) (snd D₀.P.A D₀.P.A ≫ β.hom) : G2 D₀.P.A ⟶ G2 D.P.A).left),
      wΛ.IsGen ∧
      ∀ (a a' : D₀.X) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι)
        (J' : ((TK R).left ⟶ D₀.P.A.left) → D₀.P.L.ι), Good D.P.L z J → Good D₀.P.L z J' →
        val (D₀.tau a a') (𝟙 _) z J' =
          GlobalTheory.PolDeg.lamVal wΛ (lift (toUnit (TK R) ≫ D₀.c a) (toUnit (TK R) ≫ D₀.c a')).left z J J' *
            val (D.tau (xe a) (xe a')) (𝟙 _) z J := by
  first | exact @GlobalTheory.MumCmp.SamePolIso.exists_iso | exact GlobalTheory.MumCmp.SamePolIso.exists_iso | (intros; apply GlobalTheory.MumCmp.SamePolIso.exists_iso <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

theorem _root_.GlobalTheory.T.samePolarised_of_two_idempotentFactors : ∀ (R : Type) [CommRing R] [IsDomain R] (D₁ D₂ D' : DegPre R), D₁.TauBimult → ∀ (F₁ : Factor D₁ D') (F₂ : Factor D₂ D'), F₁.o.onB.act F₁.e = F₂.o.onB.act F₂.e → F₁.o.onB.act F₁.f = F₂.o.onB.act F₂.f → (∀ z : D'.X, F₁.e • z = F₂.e • z) → (∀ z : D'.X, F₁.f • z = F₂.f • z) → SamePol D₁ D₂ := by
  first | exact @GlobalTheory.Mum.TwoFac.samePol_of_two_factors | exact GlobalTheory.Mum.TwoFac.samePol_of_two_factors | (intros; apply GlobalTheory.Mum.TwoFac.samePol_of_two_factors <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem fieldPoint_lift_of_isPreimmersion {X' X : Scheme.{0}} (j : X' ⟶ X) [IsPreimmersion j] {K : Type} [Field K]
    (y : Sp K ⟶ X) (ξ : X') (h : y (IsLocalRing.closedPoint K) = j ξ) : ∃ z : Sp K ⟶ X', z ≫ j = y := by
  obtain ⟨⟨p, φ⟩, hy⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
  have hp : p = j ξ := by
    rw [← h, ← hy]
    exact (X.fromSpecResidueField_apply p _).symm
  subst hp
  have : IsIso (j.residueFieldMap ξ) := by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨(j.residueFieldMap ξ).hom.injective, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := X'.residue_surjective ξ a
    obtain ⟨b, rfl⟩ := j.stalkMap_surjective ξ a
    exact ⟨X.residue _ b, congr($(Scheme.residue_residueFieldMap j ξ).hom b)⟩
  refine ⟨Spec.map (inv (j.residueFieldMap ξ) ≫ φ) ≫ X'.fromSpecResidueField ξ, ?_⟩
  rw [← hy, Scheme.SpecToEquivOfField_symm_apply, Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← Spec.map_comp,
    IsIso.hom_inv_id_assoc]

theorem Emb.exists_lift_fieldExt (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S)
    [GrpObj G'] (E : Emb π G') (Ω : Type) [Field Ω] (ν : Sp Ω ⟶ PSpace R E.N) (s : Sp Ω ⟶ S)
    (hν : ν ≫ PSpace.str R E.N = s ≫ π)
    (hg : ∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g ∈ Set.range ν) :
    ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω') (q : Sp Ω' ⟶ E.H.toScheme),
      q ≫ E.f = spMap io ≫ ν ∧ q ≫ E.H.ι ≫ G'.hom = spMap io ≫ s := by
  obtain ⟨g, hg, w, hw⟩ := hg
  obtain ⟨y, hy⟩ := (Emb.range_closed R S π G' E).1 g hg
  have hsub : ∀ a b : Sp Ω, a = b := fun a b => Subsingleton.elim (α := PrimeSpectrum Ω) a b
  have hx : ∀ v, (s ≫ π) v = closedPoint R := by
    intro v
    rw [hsub v w, ← hν, Scheme.Hom.comp_apply, hw, ← Scheme.Hom.comp_apply, E.f_over]
    simpa only [Scheme.Hom.comp_apply] using hg
  obtain ⟨κ, hκ⟩ := spMap_factor_residueField_of_closedPoint R Ω (s ≫ π) hx
  have := E.imm
  obtain ⟨y₀, hy₀⟩ := fieldPoint_lift_of_isPreimmersion E.j ν y (by rw [hsub (closedPoint Ω) w, hw, hy])
  have hcl : IsClosedImmersion (spMap (residue R)) :=
    IsClosedImmersion.spec_of_surjective _ (residue_surjective (R := R))
  have hY : y₀ ≫ E.Y.hom = spMap κ := by
    rw [← cancel_mono (spMap (residue R)), Category.assoc, ← E.j_over, ← Category.assoc, hy₀, hν, hκ,
      ← Spec.map_comp]
    rfl
  obtain ⟨Ω', _, io, e, l, -, hl1, hl2⟩ := E.fib Ω s κ hκ
  let t : Sp Ω' ⟶ pullback E.Y.hom (spMap (io.comp κ)) :=
    pullback.lift (spMap io ≫ y₀) (𝟙 _) (by rw [Category.assoc, hY, Category.id_comp, ← Spec.map_comp]; rfl)
  have h1 : t ≫ pullback.fst _ _ = spMap io ≫ y₀ := pullback.lift_fst _ _ _
  have h2 : t ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have he : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id]; rfl
  have hw' : e.inv.left ≫ pullback.snd G'.hom (spMap io ≫ s) = pullback.snd E.Y.hom (spMap (io.comp κ)) :=
    Over.w e.inv
  refine ⟨Ω', inferInstance, io, t ≫ e.inv.left ≫ l, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, hl2, ← Category.assoc e.inv.left, he, ← hy₀, ← Category.assoc (spMap io), ← h1]
    simp
  · rw [Category.assoc, Category.assoc, ← Category.assoc l, hl1]
    erw [pullback.condition, ← Category.assoc e.inv.left, hw', ← Category.assoc, h2, Category.id_comp]

end GlobalTheory.Mum
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.closedPoint_range_eq_fixedGroup_image : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] (E : Emb π G'), (∀ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R → ∃ y : E.Y.left, E.f g = E.j y) ∧ (Surjective π → ∀ y : E.Y.left, ∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g = E.j y) := by
  first | exact @GlobalTheory.Mum.Emb.range_closed | exact GlobalTheory.Mum.Emb.range_closed | (intros; apply GlobalTheory.Mum.Emb.range_closed <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem _root_.GlobalTheory.T.levelPoints_algClosure_fractionRing_bijective : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (D : DegPre R) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) (N : ℕ), 1 ≤ N → (∀ p : QkPt D (Kb R) N, ∃! p' : QkPt D F N, QkExt em.toRingHom p p') ∧ ∀ p' : QkPt D F N, ∃! p : QkPt D (Kb R) N, QkExt em.toRingHom p p' := by
  first | exact @GlobalTheory.Mum.qkPt_algClosure_bijective | exact GlobalTheory.Mum.qkPt_algClosure_bijective | (intros; apply GlobalTheory.Mum.qkPt_algClosure_bijective <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GalFixQ

open GlobalTheory.TorusExt

theorem qkExt_equiv_of_rational : ∀ (R₂ : Type) [CommRing R₂] [IsDomain R₂] [IsLocalRing R₂] (D₂ : DegData R₂ (maximalIdeal R₂)) (n : ℕ), (∀ p : QkPt D₂.toPre (Kb R₂) n, ∃ (p₀ : QkPt D₂.toPre (FractionRing R₂) n) (p₁ : QkPt D₂.toPre (Kb R₂) n), QkExt (algebraMap (FractionRing R₂) (Kb R₂)) p₀ p₁ ∧ QkPt.Equiv D₂.toPre (Kb R₂) p₁ p) → ∀ σ : Kb R₂ →ₐ[FractionRing R₂] Kb R₂, ∀ p p' : QkPt D₂.toPre (Kb R₂) n, QkExt σ.toRingHom p p' → QkPt.Equiv D₂.toPre (Kb R₂) p p' := by
  intro R₂ _ _ _ D₂ n hrat σ p p' hpp'
  have hB := D₂.tau_bimult
  have hf : σ.toRingHom.comp (algebraMap (FractionRing R₂) (Kb R₂)) = algebraMap (FractionRing R₂) (Kb R₂) :=
    σ.comp_algebraMap
  have ha : (algebraMap (FractionRing R₂) (Kb R₂)).comp (algebraMap (FractionRing R₂) (FractionRing R₂)) =
      algebraMap (FractionRing R₂) (Kb R₂) := by
    rw [Algebra.algebraMap_self, RingHom.comp_id]
  obtain ⟨p₀, p₁, e₁, h₁⟩ := hrat p
  have hq : QkExt σ.toRingHom p₁ (qkExt hB σ.toRingHom hf p₁) := (qkExt_iff hB _ hf _ _).2 rfl
  have e₂ := GlobalTheory.LabTrans.qkExt_trans e₁ hq
  rw [hf] at e₂
  have hfix : qkExt hB σ.toRingHom hf p₁ = p₁ :=
    ((qkExt_iff hB _ ha _ _).1 e₂).trans ((qkExt_iff hB _ ha _ _).1 e₁).symm
  rw [hfix] at hq
  exact equiv_trans hB (equiv_symm hB h₁) (equiv_of_qkExt hB σ.toRingHom hf hq hpp' h₁)

end GlobalTheory.Mum.GalFixQ
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem isMonomialTau_inl_of_tauIn : ∀ (V : Type) [CommRing V] [IsDomain V] (Q : Data V) (τ₀ : GlobalTheory.Poinc.Sep.Gens Q) (m N : ℕ) (s : Fin m ⊕ Fin N → V) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X), (∀ k, IsUnit (s (.inr k))) → GlobalTheory.Poinc.Sep.TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → Q.IsMonomialTau (fun k => s (.inl k)) (fun k => ε (.inl k)) := by
  intro V _ _ Q τ₀ m N s ε hs h a b
  obtain ⟨k, hk, hc⟩ := Model.isMonomialTau_of_tauIn h a b
  let alg : V →* FractionRing V := (algebraMap V (FractionRing V) : V →* FractionRing V)
  let w : Vˣ := ∏ j : Fin N, (hs j).unit ^ ε (.inr j) a b
  refine ⟨k * Units.map alg w⁻¹, ?_, GlobalTheory.PolDeg.Taut.tauCoord_mul_unit hc w⁻¹⟩
  have hprod : (k : FractionRing V) = (∏ i : Fin m, algebraMap V (FractionRing V) (s (.inl i)) ^ ε (.inl i) a b) *
      ∏ j : Fin N, algebraMap V (FractionRing V) (s (.inr j)) ^ ε (.inr j) a b := by
    rw [hk, ← Fintype.prod_sum_type (fun x => algebraMap V (FractionRing V) (s x) ^ ε x a b)]
    exact Fintype.prod_equiv finSumFinEquiv.symm _ _ (fun _ => rfl)
  have hw : ((Units.map alg w : (FractionRing V)ˣ) : FractionRing V) =
      ∏ j : Fin N, algebraMap V (FractionRing V) (s (.inr j)) ^ ε (.inr j) a b := by
    simp [w, alg, Units.coe_prod, map_zpow₀]
  rw [Units.val_mul, map_inv, Units.val_inv_eq_inv_val, hw, hprod, mul_inv_cancel_right₀]
  exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _
    ((IsFractionRing.injective V (FractionRing V)).ne_iff' (map_zero _) |>.2 (hs j).ne_zero)

end GlobalTheory.Poinc.Sep
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.evenDefect_degenerationData_baseChange : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (R₂ : Type) [CommRing R₂] [IsDomain R₂] (σ : R₁ →+* R₂) (D₁ : DegPre R₁) (D₂ : DegPre R₂) (β : D₂.P.A.left ⟶ D₁.P.A.left) (v : LB.Iso D₂.P.L (D₁.P.L.pull β)) (xe : D₂.X ≃+ D₁.X) (gam : FractionRing R₁ →+* FractionRing R₂), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) → IsGrpPullback D₂.P.A D₁.P.A (spMap σ) β → v.IsGen → (∀ x, (D₂.c x).left ≫ β = spMap σ ≫ (D₁.c (xe x)).left) → GlobalTheory.PsiRing.RigCmp σ D₁ D₂ β v → GlobalTheory.PsiRing.PsiCmp D₁ D₂ β v xe (spMap gam) → ∀ h : D₁.X → (FractionRing R₁)ˣ, EvenDefect D₁ h → EvenDefect D₂ fun χ => Units.map gam.toMonoidHom (h (xe χ)) := by
  first | exact @GlobalTheory.PolDeg.evenDefect_baseChange | exact GlobalTheory.PolDeg.evenDefect_baseChange | (intros; apply GlobalTheory.PolDeg.evenDefect_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.refinesPolarisedData_baseChange_symmetric : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : Data R) (R₁ : Type) [CommRing R₁] [IsDomain R₁] (R₂ : Type) [CommRing R₂] [IsDomain R₂] (σ : R₁ →+* R₂) (D₁ : DegPre R₁) (D₂ : DegPre R₂) (β : D₂.P.A.left ⟶ D₁.P.A.left) (v : LB.Iso D₂.P.L (D₁.P.L.pull β)) (xe : D₂.X ≃+ D₁.X) (gam : FractionRing R₁ →+* FractionRing R₂), (∀ r, gam (algebraMap R₁ _ r) = algebraMap R₂ _ (σ r)) → IsGrpPullback D₂.P.A D₁.P.A (spMap σ) β → v.IsGen → (∀ x, (D₂.c x).left ≫ β = spMap σ ≫ (D₁.c (xe x)).left) → GlobalTheory.PsiRing.RigCmp σ D₁ D₂ β v → GlobalTheory.PsiRing.PsiCmp D₁ D₂ β v xe (spMap gam) → ∀ (ρ : R →+* R₁) (e : D₁.X ≃+ Q.X), Function.Injective ρ → Half Q ρ D₁ e (fun _ _ => 1) → Half Q (σ.comp ρ) D₂ (xe.trans e) (fun _ _ => 1) := by
  first | exact @GlobalTheory.HalfBC.half_baseChange | exact GlobalTheory.HalfBC.half_baseChange | (intros; apply GlobalTheory.HalfBC.half_baseChange <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.hasPolarisedChart_of_monomialPreChart_semiAbelianExt : ∀ {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S) [IsOpenImmersion j] (G : Over S) [GrpObj G] (e : F.univ.A.left ⟶ G.left) (φ : InvFun ℤ) (BD : GlobalTheory.EffCartierData S) (d : ℕ) (x : S), n ≠ 0 → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → IsGrpPullback F.univ.A G j e → abLocus G = Set.range j → PreChart F s j φ BD d x → HasPolChart F s j e φ BD d x := by
  first | exact @GlobalTheory.PolDeg.hasPolChart_of_preChart_of_extension | exact GlobalTheory.PolDeg.hasPolChart_of_preChart_of_extension | (intros; apply GlobalTheory.PolDeg.hasPolChart_of_preChart_of_extension <;> assumption)
end
