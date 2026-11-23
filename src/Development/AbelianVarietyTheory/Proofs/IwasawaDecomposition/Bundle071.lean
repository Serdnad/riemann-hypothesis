module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.CanonGenIsGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle010

@[expose] public section

section

open Formalism.ConjugateSelfDual Formalism.MainNotions.N Polynomial

namespace GlobalTheory

theorem matrix_system_nonzero_solution_descends {k L Γ : Type} [Field k] [Field L] (f : k →+* L)
    {a b c : ℕ} (A : Γ → Matrix (Fin a) (Fin a) k) (B : Γ → Matrix (Fin b) (Fin b) k)
    (Q : Matrix (Fin c) (Fin a) k) (C : Matrix (Fin a) (Fin b) L) :
    C ≠ 0 → (∀ g, (A g).map f * C = C * (B g).map f) → Q.map f * C = 0 →
      ∃ X : Matrix (Fin a) (Fin b) k, X ≠ 0 ∧ (∀ g, A g * X = X * B g) ∧ Q * X = 0 := by
  intro hC hAB hQ
  letI := f.toAlgebra
  obtain ⟨i₀, j₀, hij⟩ : ∃ i j, C i j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hC (Matrix.ext h)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual k L, φ (C i₀ j₀) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hij ((Module.forall_dual_apply_eq_zero_iff k (C i₀ j₀)).mp h)
  have key : ∀ (x : k) (y : L), φ (f x * y) = x * φ y := by
    intro x y
    have h1 : f x * y = x • y := (Algebra.smul_def x y).symm
    rw [h1, map_smul, smul_eq_mul]
  have key' : ∀ (x : k) (y : L), φ (y * f x) = φ y * x := by
    intro x y
    rw [mul_comm y, key, mul_comm]
  refine ⟨C.map φ, ?_, ?_, ?_⟩
  · intro h
    apply hφ
    have := congrFun (congrFun h i₀) j₀
    simpa using this
  · intro g
    ext i j
    have := congrArg φ (congrFun (congrFun (hAB g) i) j)

    simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, key, key'] using this
  · ext i j
    have := congrArg φ (congrFun (congrFun hQ i) j)

    simpa only [Matrix.mul_apply, Matrix.map_apply, map_sum, key, Matrix.zero_apply, map_zero]
    using this

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem _root_.GlobalTheory.T.exists_inertia_moves_tame_root : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] [CharZero W]
    (F : Type) [Field F] [Algebra (FractionRing W) F] [IsAlgClosure (FractionRing W) F] (ϖ : W), Irreducible ϖ →
    ∀ k : ℕ, IsUnit (k : W) → ∃ (O : ValuationSubring F) (φ : W →+* O) (σ : F →ₐ[FractionRing W] F) (π : F),
      IsLocalHom φ ∧ (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) ∧
      (∀ x ∈ O, O.valuation (σ x - x) < 1) ∧ π ^ k = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ) ∧
      IsPrimitiveRoot (σ π / π) k := by
  first | exact @GlobalTheory.InertiaTameRoot.exists_inertia_moves_root | exact GlobalTheory.InertiaTameRoot.exists_inertia_moves_root | (intros; apply GlobalTheory.InertiaTameRoot.exists_inertia_moves_root <;> assumption)
end

section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqLevel

open TopologicalSpace

variable {X : Scheme.{0}}

abbrev sqLB (L : LB X) : LB X := LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)

theorem mem_sq {L : LB X} {x : X} {J : Fin 1 → L.ι} : x ∈ (sqLB L).U J ↔ x ∈ L.U (J 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    exact h⟩

theorem mem_sq_pull {Y : Scheme.{0}} {L : LB X} {F : Y ⟶ X} {y : Y} {J : PUnit → Fin 1 → L.ι} :
    y ∈ ((sqLB L).pull F).U J ↔ F y ∈ L.U (J PUnit.unit 0) :=
  mem_pull.trans mem_sq

theorem gm_sq_g {Y : Scheme.{0}} (L : LB X) (r : Y ⟶ X) (y : Y) (J J' : Fin 1 → L.ι) (hJ : r y ∈ L.U (J 0))
    (hJ' : r y ∈ L.U (J' 0)) :
    gm r y ((sqLB L).U J ⊓ (sqLB L).U J') ((sqLB L).g J J') = gm r y _ (L.g (J 0) (J' 0)) ^ 2 := by
  refine (gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => 2) r y J J' (mem_sq.2 hJ) (mem_sq.2 hJ')).trans ?_
  rw [Fin.prod_univ_one, Category.comp_id]
  exact zpow_two _ |>.trans (pow_two _).symm

theorem gm_sq_pull_g {Y Z : Scheme.{0}} (L : LB X) (F : Y ⟶ X) (r : Z ⟶ Y) (z : Z) (J J' : PUnit → Fin 1 → L.ι)
    (hJ : F (r z) ∈ L.U (J PUnit.unit 0)) (hJ' : F (r z) ∈ L.U (J' PUnit.unit 0)) :
    gm r z (((sqLB L).pull F).U J ⊓ ((sqLB L).pull F).U J') (((sqLB L).pull F).g J J') =
      gm (r ≫ F) z _ (L.g (J PUnit.unit 0) (J' PUnit.unit 0)) ^ 2 :=
  (gm_pull_g (sqLB L) F r z J J' (mem_sq_pull.2 hJ) (mem_sq_pull.2 hJ')).trans
    (gm_sq_g L (r ≫ F) z _ _ hJ hJ')

variable {B G E : Scheme.{0}} {M : LB B} {L : LB G} {p : E ⟶ B} {f : E ⟶ G}

theorem sqIso_le (q : (PUnit → Fin 1 → M.ι) × (PUnit → Fin 1 → L.ι)) :
    ((sqLB M).pull p).U q.1 ⊓ ((sqLB L).pull f).U q.2 ≤
      (M.pull p).U (fun _ => q.1 PUnit.unit 0) ⊓ (L.pull f).U (fun _ => q.2 PUnit.unit 0) :=
  fun _ h => ⟨mem_pull.2 (mem_sq_pull.1 h.1), mem_pull.2 (mem_sq_pull.1 h.2)⟩

def sqIso (w : LB.Iso (L.pull f) (M.pull p)) : LB.Iso ((sqLB L).pull f) ((sqLB M).pull p) :=
  ⟨fun q => res (sqIso_le q) (w.s (fun _ => q.1 PUnit.unit 0, fun _ => q.2 PUnit.unit 0)) ^ 2⟩

theorem gw_sqIso (w : LB.Iso (L.pull f) (M.pull p)) {Z : Scheme.{0}} (r : Z ⟶ E) (z : Z) (J : Fin 1 → M.ι)
    (K : PUnit → Fin 1 → L.ι) (hJ : p (r z) ∈ M.U (J 0)) (hK : f (r z) ∈ L.U (K PUnit.unit 0)) :
    gw (sqIso w) r z J K = gw w r z (J 0) (fun _ => K PUnit.unit 0) ^ 2 := by
  have hm : r z ∈ ((sqLB M).pull p).U (fun _ => J) ⊓ ((sqLB L).pull f).U K :=
    ⟨mem_sq_pull.2 hJ, mem_sq_pull.2 hK⟩
  exact (map_pow _ _ _).trans (congrArg (· ^ 2) (gm_res r z _ hm _))

theorem sqIso_isGen {w : LB.Iso (L.pull f) (M.pull p)} (hw : w.IsGen) : (sqIso w).IsGen := by
  rw [isGen_iff] at hw ⊢
  intro Y r y j j' k k' hj hj' hk hk'
  have hj₀ := mem_sq.1 hj
  have hj₀' := mem_sq.1 hj'
  have hk₀ := mem_sq_pull.1 hk
  have hk₀' := mem_sq_pull.1 hk'
  rw [gw_sqIso w r y j k hj₀ hk₀, gw_sqIso w r y j' k' hj₀' hk₀', gm_sq_g M (r ≫ p) y j j' hj₀ hj₀',
    gm_sq_pull_g L f r y k k' hk₀ hk₀']
  have e := hw Y r y (j 0) (j' 0) (fun _ => k PUnit.unit 0) (fun _ => k' PUnit.unit 0) hj₀ hj₀'
    (mem_pull.2 hk₀) (mem_pull.2 hk₀')
  rw [gm_pull_g L f r y _ _ (mem_pull.2 hk₀) (mem_pull.2 hk₀')] at e
  rw [e, mul_pow, mul_pow, inv_pow]

end GlobalTheory.SqLevel
end
end
