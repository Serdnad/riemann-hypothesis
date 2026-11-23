module

public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsVVGenOfIsThetaFamily
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle012
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle007
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
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB

@[expose] public section

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaFamily_origin_germ_of_multiplication : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (N m : ℕ) (J : Type) (x : J → ((Out.baseOver (Sp K)) ⟶ P.A)) (th : LB.Sec (Out.LPow P.A P.L 1 (Out.baseOver (Sp K)))) (t : J → LB.Sec (Out.LPow P.A P.L N (Out.baseOver (Sp K)))) (ρ : P.A.left ⟶ ((Out.baseOver (Sp K)) ⊗ P.A).left) (e : ρ ≫ (snd (Out.baseOver (Sp K)) P.A).left = 𝟙 P.A.left) (a : J), Out.IsGenSec P.A P.L 1 th → IsThetaFamily P N m x th t → x a = 1 → (∃ l, (PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) (th)).f l ≠ 0) ∧ (∀ (y : P.A.left) k l, y ∈ (lbPow P.L N).U k → (Out.mulA P.A m).left y ∈ (lbPow P.L 1).U l → Associated (gs (𝟙 P.A.left) y ((lbPow P.L N).U k) ((PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((N : ℕ) : ℤ) (t a)).f k)) (gs (Out.mulA P.A m).left y ((lbPow P.L 1).U l) ((PowSec.down P.L (snd (Out.baseOver (Sp K)) P.A).left ρ e ((1 : ℕ) : ℤ) (th)).f l))) := by
  first | exact @GlobalTheory.ThetaGerm.germ_origin | exact GlobalTheory.ThetaGerm.germ_origin | (intros; apply GlobalTheory.ThetaGerm.germ_origin <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.thetaPt_support_meets_every_coset : Out.Laws → ∀ (g n N' : ℕ), 2 ≤ n → n ^ 2 ∣ N' → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg : P.g = g) (ze : Γ(Sp K, ⊤)ˣ) (lev : Out.Level P (N' ^ 2) ze) (v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((Out.baseOver (Sp K)).left, ⊤)), Out.IsThetaPt P N' (levelPoint lev hg) v → ∀ c : Fin (2 * g) → ZMod (N' ^ 2), ∃ d : Fin (2 * g) → ZMod (N' ^ 2), v (c + n • d) ≠ 0 := by
  first | exact @GlobalTheory.ThetaSupport.exists_ne_zero_in_coset | exact GlobalTheory.ThetaSupport.exists_ne_zero_in_coset | (intros; apply GlobalTheory.ThetaSupport.exists_ne_zero_in_coset <;> assumption)
end

section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.levelBasis_eq_of_same_thetaPt : Out.Laws → ∀ (g n j N' : ℕ), Odd n → N' = n ^ j → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (hg : P.g = g) (ze : Γ(Sp K, ⊤)ˣ) (lev lev' : Out.Level P (N' ^ 2) ze) (v : (Fin (2 * g) → ZMod (N' ^ 2)) → Γ((Out.baseOver (Sp K)).left, ⊤)), Out.IsThetaPt P N' (levelPoint lev hg) v → Out.IsThetaPt P N' (levelPoint lev' hg) v → (∀ i, levelBasis lev hg i ^ N' = levelBasis lev' hg i ^ N') → (∀ c : Fin (2 * g) → ZMod (N' ^ 2), ∃ d : Fin (2 * g) → ZMod (N' ^ 2), v (c + n • d) ≠ 0) → ∀ i, levelBasis lev hg i = levelBasis lev' hg i := by
  first | exact @GlobalTheory.levelBasis_eq_of_isThetaPt | exact GlobalTheory.levelBasis_eq_of_isThetaPt | (intros; apply GlobalTheory.levelBasis_eq_of_isThetaPt <;> assumption)
end
