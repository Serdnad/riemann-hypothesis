module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle538
public import ReciprocityTheory.SemistableReduction.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle537
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
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle058

@[expose] public section

section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open Opposite

namespace GlobalTheory.EndLoc.HomFixGlue

theorem pullPull_mem {X Y Z Y' Z' : Scheme.{0}} (M : LB X) (F : Y ⟶ X) (G : Z ⟶ Y) (F' : Y' ⟶ X) (G' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (hc : G' ≫ F' = h ≫ G ≫ F) (J : PUnit → PUnit → M.ι) (y : Z')
    (hy : y ∈ ((M.pull F').pull G').U J) :
    h y ∈ ((M.pull F).pull G).U (fun _ => fun _ => J PUnit.unit PUnit.unit) := by
  have h1 := mem_pull.1 (mem_pull.1 hy)
  have e : F (G (h y)) = F' (G' y) := by
    have := congrArg (fun k => k y) hc
    simpa using this.symm
  exact mem_pull.2 (mem_pull.2 (by rw [e]; exact h1))

def chartPullPullPull {X Y Z Y' Z' : Scheme.{0}} (M : LB X) (F : Y ⟶ X) (G : Z ⟶ Y) (F' : Y' ⟶ X) (G' : Z' ⟶ Y')
    (h : Z' ⟶ Z) (hc : G' ≫ F' = h ≫ G ≫ F) : ChartPull ((M.pull F').pull G') ((M.pull F).pull G) h where
  idx J := fun _ => fun _ => J PUnit.unit PUnit.unit
  le J y hy := pullPull_mem M F G F' G' h hc J y hy
  g y J J' hj hj' := by
    have a1 := gm_pull_g (M.pull F') G' (𝟙 _) y J J' hj hj'
    have a2 := gm_pull_g M F' (𝟙 _ ≫ G') y (J PUnit.unit) (J' PUnit.unit) (mem_pull.1 hj) (mem_pull.1 hj')
    have m1 := pullPull_mem M F G F' G' h hc J y hj
    have m2 := pullPull_mem M F G F' G' h hc J' y hj'
    have b1 := gm_pull_g (M.pull F) G h y _ _ m1 m2
    have b2 := gm_pull_g M F (h ≫ G) y (fun _ => J PUnit.unit PUnit.unit) (fun _ => J' PUnit.unit PUnit.unit)
      (mem_pull.1 m1) (mem_pull.1 m2)
    rw [a1, a2, b1, b2]
    have e : (𝟙 _ ≫ G') ≫ F' = (h ≫ G) ≫ F := by simp [hc]
    rw [e]

section
variable {S : Scheme.{0}}

variable (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left)

end

end GlobalTheory.EndLoc.HomFixGlue
end
end

section

open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiftSys

theorem exists_opens_preimage_eq_of_sqZero_aug (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁]
    (q : R₁ →ₐ[R₀] R₀) (hq : ∀ y y', q y = 0 → q y' = 0 → y * y' = 0) (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀)
    (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀) (hp : IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁))) (W : X₁.Opens) :
    ∃ W₀ : X₀.Opens, pr ⁻¹ᵁ W₀ = W := by
  have hcomp : (q : R₁ →+* R₀).comp (algebraMap R₀ R₁) = RingHom.id R₀ := RingHom.ext fun r ↦ q.commutes r
  have hsp : spMap (q : R₁ →+* R₀) ≫ spMap (algebraMap R₀ R₁) = 𝟙 (Sp R₀) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    exact Spec.map_id _
  let i : X₀ ⟶ X₁ := hp.lift (𝟙 X₀) (s₀ ≫ spMap (q : R₁ →+* R₀))
    (by rw [Category.id_comp, Category.assoc, hsp, Category.comp_id])
  have hi1 : i ≫ pr = 𝟙 X₀ := hp.lift_fst _ _ _
  have hi2 : i ≫ s₁ = s₀ ≫ spMap (q : R₁ →+* R₀) := hp.lift_snd _ _ _
  have hout : IsPullback (i ≫ pr) s₀ s₀ (spMap (q : R₁ →+* R₀) ≫ spMap (algebraMap R₀ R₁)) := by
    rw [hi1, hsp]; exact IsPullback.id_horiz s₀
  have hsq : IsPullback i s₀ s₁ (spMap (q : R₁ →+* R₀)) := IsPullback.of_right hout hi2 hp
  have hsurj : Function.Surjective (q : R₁ →+* R₀) := fun r ↦ ⟨algebraMap R₀ R₁ r, q.commutes r⟩
  have hI : (RingHom.ker (q : R₁ →+* R₀)) ^ 2 = 0 := by
    rw [sq, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro y hy y' hy'
    exact (Ideal.mem_bot).2 (hq y y' (RingHom.mem_ker.1 hy) (RingHom.mem_ker.1 hy'))
  have hisurj : Surjective i := surjective_of_isPullback_sqZero hI hsurj rfl hsq
  have key : ∀ x : X₁, i.base (pr.base x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := hisurj.surj x
    have h : pr.base (i.base y) = y := by rw [← Scheme.Hom.comp_apply, hi1]; rfl
    rw [h]
  refine ⟨i ⁻¹ᵁ W, ?_⟩
  ext x
  change i.base (pr.base x) ∈ W ↔ x ∈ W
  rw [key]

end GlobalTheory.LiftSys
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.typicalCurveEigenspace_and_basisExists : TypicalCurveEigenspace ∧ TypicalCurveBasisExists := by
  first | exact @GlobalTheory.TypicalCurveBases.typical_curves_tangent_and_bases | exact GlobalTheory.TypicalCurveBases.typical_curves_tangent_and_bases | (intros; apply GlobalTheory.TypicalCurveBases.typical_curves_tangent_and_bases <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

theorem _root_.GlobalTheory.T.root_extraction_lemma_sheaf : RootStatement := by
  first | exact @GlobalTheory.RootTrick.root_statement | exact GlobalTheory.RootTrick.root_statement | (intros; apply GlobalTheory.RootTrick.root_statement <;> assumption)
end

section

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.DepthStages

theorem _root_.GlobalTheory.T.root_trick_finset_curves_block_inverse : RootStatement → ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ),
    p.Prime → v (p : C) = 1 → ∀ (d h : ℕ) (ty : Fin d → ZMod h) (i : ZMod h) (G : LogFGL v d)
      (γ : Fin d → Fin d → PowerSeries C) (S : Finset (Fin d)),
      (∀ a ∈ S, IsCurve v (γ a)) → (∀ a ∈ S, G.IsOfType p ty i (γ a)) → ∀ (n j : ℕ), 1 ≤ n →
      ∀ (V : Type) [AddCommGroup V] [Module C V] (La : (Fin d → C) →ₗ[C] V),
        Module.finrank C (Submodule.span C
          ((fun a => La (G.lc p (γ a) n)) '' (S : Set (Fin d)))) ≤ j →
        ∃ (x y : Matrix (Fin d) (Fin d) C) (D : Finset (Fin d)), D ⊆ S ∧ D.card ≤ j ∧
          (∀ a b, IsIntV v (x a b)) ∧ (∀ a b, IsIntV v (y a b)) ∧
          (∀ a b, x a b ≠ 0 → a ∈ S ∧ b ∈ S) ∧ (∀ a b, y a b ≠ 0 → a ∈ S ∧ b ∈ S) ∧
          (∀ a c, a ∈ S → c ∈ S → ∑ b, x a b * y b c = if a = c then 1 else 0) ∧
          ∀ a ∈ S, a ∉ D → La (∑ b, x a b ^ (p ^ n) • G.lc p (γ b) n) = 0 := by
  first | exact @GlobalTheory.RootFin.root_fin | exact GlobalTheory.RootFin.root_fin | (intros; apply GlobalTheory.RootFin.root_fin <;> assumption)
end

section

open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop

theorem _root_.GlobalTheory.T.blockSphereProb_zeroSet_eq_zero_of_ne_zero : ∀ (B n : ℕ) (a : Fin B → ℕ) (g : MvPolynomial (Fin B × Fin n) ℂ), 0 < n → g ≠ 0 → IsMultiHomogeneous a g → blockSphereProb B n {z | eval (blockPoint z) g = 0} = 0 := by
  first | exact @GlobalTheory.SphereMeanNull.blockSphereProb_zeroSet_eq_zero | exact GlobalTheory.SphereMeanNull.blockSphereProb_zeroSet_eq_zero | (intros; apply GlobalTheory.SphereMeanNull.blockSphereProb_zeroSet_eq_zero <;> assumption)
end
