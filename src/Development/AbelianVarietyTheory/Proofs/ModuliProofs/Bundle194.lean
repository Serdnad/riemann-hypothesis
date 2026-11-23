module

public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle191
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFullLevelModelOfFamilyBirationalModel
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

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_thetaObject_over_complete_dvr_specialisation : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) Mat κ (w w' : J) [Finite J] (R K : Type) [CommRing R] [IsDomain R] [CharZero R] [Algebra.FiniteType ℤ R] [Field K] [Algebra R K] [IsFractionRing R K] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (t : TObj g (N' ^ 2) J b (spMap (algebraMap R K) ≫ spMap β)) (𝔪 : Ideal R), 𝔪.IsMaximal → t.HasTh (𝟙 _) (fun a => algebraMap R K (v a)) → t.Shape Mat κ → t.Prim w w' → ∃ (V F : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (_ : Finite (IsLocalRing.ResidueField V)) (_ : Field F) (_ : CharZero F) (_ : Algebra V F) (_ : IsFractionRing V F) (y : R →+* V) (tF : TObj g (N' ^ 2) J b (spMap (algebraMap V F) ≫ spMap (y.comp β))), (IsLocalRing.maximalIdeal V).comap y = 𝔪 ∧ tF.Shape Mat κ ∧ tF.Prim w w' ∧ tF.HasTh (𝟙 _) (fun a => algebraMap V F (y (v a))) := by
  first | exact @GlobalTheory.ZM.exists_obj_over_complete_dvr | exact GlobalTheory.ZM.exists_obj_over_complete_dvr | (intros; apply GlobalTheory.ZM.exists_obj_over_complete_dvr <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

theorem _root_.GlobalTheory.T.exists_clopen_locus_torsionSections_heckeKernel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over S) ⟶ o.t.G)), admitted l 𝔓 p → (∀ j, σ j ^ p ^ 2 = 1) → ∃ V : S.Opens, IsClosed (V : Set S) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), Set.range x ⊆ V ↔ (Function.Injective fun j => x ≫ (σ j).left) ∧ ∃ C : Subgroup (Over.mk x ⟶ o.t.G), (C : Set _) = Set.range (fun j => toUnit (Over.mk x) ≫ σ j) ∧ o.t.HeckeKer (Over.mk x) D 𝔓 p i C := by
  first | exact @GlobalTheory.exists_clopen_heckeKer_iff | exact GlobalTheory.exists_clopen_heckeKer_iff | (intros; apply GlobalTheory.exists_clopen_heckeKer_iff <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_theta_family_from_very_dense_points : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → ∃ t : TObj g ((n ^ j) ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → TMap t' t (spMap x) := by
  first | exact @GlobalTheory.ZM.exists_tObj_of_veryDense | exact GlobalTheory.ZM.exists_tObj_of_veryDense | (intros; apply GlobalTheory.ZM.exists_tObj_of_veryDense <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

theorem _root_.GlobalTheory.T.exists_fullLevel_model_of_family_birationalModel : GlobalTheory.LN.HomExtSt → Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (MM : Scheme.{0}) (sM : MM ⟶ Sp (RZ H n N)) (tM : SAB H MM) (lev : D.La → (𝟙_ (Over MM) ⟶ tM.G)) (m : ℕ) (C : ZOn sM tM m), 1 ≤ D.p + D.q → AuxiliaryInertOddPrime H n → (∃ j, 1 ≤ j ∧ N = n ^ j) → 0 < m → FamCore D sM tM lev → SiegClause D sM tM lev → ∃ T : Top Xo n N, Nonempty (GlobalTheory.LN.AmpFrames T.t.G T.t.PP.L (m ^ 2)) := by
  first | exact @GlobalTheory.TopOfFamily.exists_top | exact GlobalTheory.TopOfFamily.exists_top | (intros; apply GlobalTheory.TopOfFamily.exists_top <;> assumption)
end
