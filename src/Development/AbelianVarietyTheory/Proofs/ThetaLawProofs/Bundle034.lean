module

public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle001
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.LevBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRuleOneOfKeyFormula
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicThetaOfLevelBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyIsLimitBaseChange
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle033
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.KeyFormula.DegProd

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem _root_.GlobalTheory.T.exists_point_thetaPullbacks_isUnit : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ) (ξ : Fin 4 → Pt x), (m : K) ≠ 0 → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∃ y : 𝟙_ (Over (Sp K)) ⟶ Out.powObj x.P.A 4, ∀ (p : (𝟙_ (Over (Sp K))).left) J, Good x.P.L p J → ∀ r, IsUnit (gs (y.left ≫ (alMap x al r (ξ r)).left) p (x.P.L.U (J (y.left ≫ (alMap x al r (ξ r)).left))) (x.th.f (J (y.left ≫ (alMap x al r (ξ r)).left)))) := by
  first | exact @GlobalTheory.SimilNonvan.exists_pt_isUnit | exact GlobalTheory.SimilNonvan.exists_pt_isUnit | (intros; apply GlobalTheory.SimilNonvan.exists_pt_isUnit <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa


theorem _root_.GlobalTheory.T.exists_holomorphic_theta_of_level_basis : Out.Laws → ThetaUnifAV → ∀ (g m : ℕ) (a b : Fin g → ℂ) (al : Matrix (Fin 4) (Fin 4) ℤ) (Th : Fin (m ^ g) → (Fin g → Fin g → ℂ) → (Fin g → ℂ) → ℂ), charHalf g a b → 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → LevBasis a b m Th → ∃ lam : (Fin g → Fin g → ℂ) → ℂ, DifferentiableOn ℂ lam (Key.phDom g) ∧ ∀ p ∈ Key.phDom g, ∀ (x : KeyIn ℂ) (h : x.P.g = g) (u : HolUnif x.P.A x.P.L g) (bs : Fin (m ^ x.P.g) → RR x m) (la : ℂˣ), Wit x h u (per p) a b → (∀ k, FnPw x u (bs k) (Th (k.cast (by rw [h])) p)) → IsSquareDeterminantComparison x m al bs la → (la : ℂ) = lam p := by
  first | exact @GlobalTheory.SimilTheta.l2Val_holomorphic | exact GlobalTheory.SimilTheta.l2Val_holomorphic | (intros; apply GlobalTheory.SimilTheta.l2Val_holomorphic <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyKa

namespace GlobalTheory

theorem lbIso_descends_to_subfield_containing_finset :
    ∀ (k K : Type) [Field k] [Field K] (σ : k →+* K) (X₀ : Over (Sp k)) (X : Over (Sp K)) (φ : X.left ⟶ X₀.left) (M N : LB X₀.left), IsPullback φ X.hom X₀.hom (spMap σ) → QuasiCompact X₀.hom → QuasiSeparated X₀.hom → M.IsLB → N.IsLB → LBIso (M.pull φ) (N.pull φ) → ∃ s : Finset K, ∀ (k₁ : Type) [Field k₁] (α : k →+* k₁) (β : k₁ →+* K), β.comp α = σ → (s : Set K) ⊆ Set.range β → ∀ (X₁ : Over (Sp k₁)) (χ : X₁.left ⟶ X₀.left), IsPullback χ X₁.hom X₀.hom (spMap α) → LBIso (M.pull χ) (N.pull χ) := by
  intro k K _ _ σ X₀ X φ M N hφ hqc hqs hM hN H
  letI := σ.toAlgebra
  have same : ∀ {Y Y' : Scheme.{0}} (a : Y ⟶ X₀.left) (j : Y' ⟶ Y) (a' : Y' ⟶ X₀.left), a' = j ≫ a →
      LBIso (M.pull a) (N.pull a) → LBIso (M.pull a') (N.pull a') := fun a j a' e h =>
    LBIso.chartPull (chartPullSame M _ _ _ j fun _ => e) (chartPullSame N _ _ _ j fun _ => e) h
  have hφ' : IsPullback φ X.hom X₀.hom (spMap (algebraMap k K)) := hφ
  have H₁ := same φ hφ'.isoPullback.inv (pullback.fst X₀.hom (spMap (algebraMap k K)))
    (IsPullback.isoPullback_inv_fst hφ').symm H
  obtain ⟨R, hR₀, ⟨s, rfl⟩, hiso⟩ := exists_fg_lbIso (C := K) (R₀ := ⊥) X₀.hom Subalgebra.fg_bot
    (M.pull (pullback.fst _ _)) (N.pull (pullback.fst _ _)) (pull_isLB hM _) (pull_isLB hN _)
    (LBIso.chartPull
      (chartPullOut M _ _ _ _ fun _ => (baseChangeMap_fst X₀.hom _).symm)
      (chartPullOut N _ _ _ _ fun _ => (baseChangeMap_fst X₀.hom _).symm) H₁)
  have H₂ := LBIso.chartPull (chartPullIn M _ _ _) (chartPullIn N _ _ _) hiso
  refine ⟨s, ?_⟩
  intro k₁ _ α β hαβ hs X₁ χ hχ
  have hR : ∀ x : Algebra.adjoin k (s : Set K), ∃ y, β y = x := by
    rintro ⟨x, hx⟩
    change x ∈ β.range
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact hs hx
    | algebraMap r => exact ⟨α r, RingHom.congr_fun hαβ r⟩
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  choose ρ₀ hρ₀ using hR
  let ρ : Algebra.adjoin k (s : Set K) →+* k₁ :=
    { toFun := ρ₀
      map_one' := β.injective (by simp [hρ₀])
      map_mul' := fun x y ↦ β.injective (by simp [hρ₀])
      map_zero' := β.injective (by simp [hρ₀])
      map_add' := fun x y ↦ β.injective (by simp [hρ₀]) }
  have hρ₂ : ρ.comp (algebraMap k _) = α := RingHom.ext fun r ↦ β.injective
    ((hρ₀ _).trans (RingHom.congr_fun hαβ r).symm)
  let j : X₁.left ⟶ pullback X₀.hom (spMap (algebraMap k (Algebra.adjoin k (s : Set K)))) :=
    pullback.lift χ (X₁.hom ≫ spMap ρ) (by rw [Category.assoc, spMap_comp_ring, hρ₂, hχ.w])
  have hj₁ : j ≫ pullback.fst _ _ = χ := pullback.lift_fst _ _ _
  refine same _ j χ ?_ H₂
  rw [baseChangeMap_fst, hj₁]

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

theorem _root_.GlobalTheory.T.exists_section_boxProduct_div_generator : ∀ (X Y : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K₁ K₂ : Type) [Fintype K₁] [Fintype K₂] (φ : K₁ → (Y ⟶ X)) (ψ : K₂ → (Y ⟶ X)) (e : ℤ) (th : L.Sec) (w : LB.Gen (LB.LinComb L (K := K₁ ⊕ K₂) (Sum.elim φ ψ) (Sum.elim (fun _ => 1) (fun _ => -e)))), w.IsGen → ∃ s : LB.Sec (LB.LinComb L ψ (fun _ => e)), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J, Good L z J → ∏ k, gs (r ≫ φ k) z (L.U (J (r ≫ φ k))) (th.f (J (r ≫ φ k))) = (val w r z J).val * sval s r z J := by
  first | exact @GlobalTheory.KeyQuot.exists_sec_quot | exact GlobalTheory.KeyQuot.exists_sec_quot | (intros; apply GlobalTheory.KeyQuot.exists_sec_quot <;> assumption)
end
