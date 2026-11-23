module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.PublishedTheorems.AbelianLaws.PrincipalPolarisationOneSection
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.RigDesc

theorem exists_unit_of_gen : ∀ {Z P Q : Scheme.{0}} (g : Z ⟶ P) (f : P ⟶ Q) (M : LB P), M.IsLB →
    ∀ (c : LB.Gen (LB.LinComb M (K := Fin 2) ![pullback.fst f f, pullback.snd f f] ![-1, 1])), c.IsGen →
    ∀ (τ : LB.Gen (M.pull g)), τ.IsGen →
    ∃ (u : Γ(pullback (g ≫ f) (g ≫ f), ⊤)) (hu : IsUnit u),
      ∀ (W : Scheme.{0}) (a b : W ⟶ Z) (hab : a ≫ g ≫ f = b ≫ g ≫ f) (w : W) (J : (W ⟶ P) → M.ι), Good M w J →
        gm (pullback.lift a b hab) w ⊤ hu.unit =
          val τ a w J * val c (pullback.lift (a ≫ g) (b ≫ g) (by simpa using hab)) w J * (val τ b w J)⁻¹ := by
  intro Z P Q g f M hM c hc τ hτ
  have hm : (pullback.fst (g ≫ f) (g ≫ f) ≫ g) ≫ f = (pullback.snd (g ≫ f) (g ≫ f) ≫ g) ≫ f := by
    simpa using pullback.condition (f := g ≫ f) (g := g ≫ f)
  let m : pullback (g ≫ f) (g ≫ f) ⟶ pullback f f := pullback.lift _ _ hm
  have m₁ : m ≫ pullback.fst f f = pullback.fst (g ≫ f) (g ≫ f) ≫ g := pullback.lift_fst _ _ hm
  have m₂ : m ≫ pullback.snd f f = pullback.snd (g ≫ f) (g ≫ f) ≫ g := pullback.lift_snd _ _ hm
  obtain ⟨t, -, hv⟩ := exists_gen hM (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fintype.prod_unique, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, m₁, m₂]
      simp)
    (LB.mulGen M _ _ _ _ (LB.mulGen M _ _ _ _ (LB.pullGen M _ _ τ (pullback.fst (g ≫ f) (g ≫ f))) (LB.pullGen M _ _ c m))
      (LB.invGen M _ _ (LB.pullGen M _ _ τ (pullback.snd (g ≫ f) (g ≫ f)))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hτ _) (DVR.pullGen_isGen _ _ _ _ hc _))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hτ _)))
  have le : (⊤ : (pullback (g ≫ f) (g ≫ f)).Opens) ≤
      LB.wchart M (PEmpty.elim : PEmpty → (pullback (g ≫ f) (g ≫ f) ⟶ P)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨(res le (t.s PEmpty.elim)).val, Units.isUnit _, fun W a b hab w J hJ => ?_⟩
  have e₁ : pullback.lift a b hab ≫ pullback.fst (g ≫ f) (g ≫ f) = a := pullback.lift_fst _ _ _
  have e₂ : pullback.lift a b hab ≫ pullback.snd (g ≫ f) (g ≫ f) = b := pullback.lift_snd _ _ _
  have e₃ : pullback.lift a b hab ≫ m = pullback.lift (a ≫ g) (b ≫ g) (by simpa using hab) := by
    apply pullback.hom_ext
    · rw [Category.assoc, m₁, ← Category.assoc, e₁, pullback.lift_fst]
    · rw [Category.assoc, m₂, ← Category.assoc, e₂, pullback.lift_snd]
  rw [IsUnit.unit_of_val_units]
  refine ((gm_res _ w le trivial _).trans (val_of t _ w J PEmpty.elim (fun k => k.elim)).symm).trans ?_
  rw [hv W _ w J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, val_pull hJ, e₁, e₂, e₃]

end GlobalTheory.CompanionTheory.RigDesc
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.SecNorm

theorem exists_gen_normalised_along : ∀ {X Y S₀ : Scheme.{0}} {M : LB X}, M.IsLB → ∀ {K K₂ : Type} [Fintype K] [Fintype K₂] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (φ₂ : K₂ → (S₀ ⟶ X)) (ε₂ : K₂ → ℤ) (p : Y ⟶ S₀) (e : S₀ ⟶ Y), e ≫ p = 𝟙 S₀ → FormEq (fun k => e ≫ φ k) ε φ₂ ε₂ →
    ∀ (t : LB.Gen (LB.LinComb M φ ε)), t.IsGen → ∀ (R : LB.Gen (LB.LinComb M φ₂ ε₂)), R.IsGen →
    ∃ t' : LB.Gen (LB.LinComb M φ ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (s : Z ⟶ S₀) (z : Z) (J : (Z ⟶ X) → M.ι), Good M z J → val t' (s ≫ e) z J = val R s z J := by
  intro X Y S₀ M hM K K₂ _ _ φ ε φ₂ ε₂ p e he hF t ht R hR
  obtain ⟨t', ht', hv⟩ := exists_gen hM (φ' := φ) (ε' := ε)
    (fun U _ h => by
      have c := hF U (fun ψ => h (p ≫ ψ))
      simp only [Category.assoc] at c
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Category.assoc, c.symm]
      simp)
    (LB.mulGen M _ _ _ _ (LB.mulGen M _ _ _ _ t (LB.invGen M _ _ (LB.pullGen M _ _ t (p ≫ e))))
      (LB.pullGen M _ _ R p))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
      (DVR.pullGen_isGen _ _ _ _ hR _))
  refine ⟨t', ht', fun Z s z J hJ => ?_⟩
  have h₁ : (s ≫ e) ≫ p = s := by rw [Category.assoc, he, Category.comp_id]
  have h₂ : (s ≫ e) ≫ p ≫ e = s ≫ e := by rw [← Category.assoc, h₁]
  rw [hv Z (s ≫ e) z J hJ, val_mul hJ, val_mul hJ, val_inv, val_pull hJ, val_pull hJ, h₁, h₂, mul_inv_cancel,
    _root_.one_mul]

end GlobalTheory.CompanionTheory.SecNorm
end
