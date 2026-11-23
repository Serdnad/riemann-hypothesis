module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle146
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle024
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle078
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.WittVector.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittVectorGaussNormUltrametric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle081
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Formalism.ResultantValuation.ResultantAdjugateProofs.Laplace
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle089
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle082
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle085
public import Mathlib.Data.Matrix.Mul
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle079
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Group.Tannery
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Normed.Group.Indicator
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower

@[expose] public section

section

open Filter Topology
open scoped ENNReal

namespace GlobalTheory.EulerSum

variable {I X : Type} [Zero X]

noncomputable def ofFinset (S : Finset I) (y : S → X) : I →₀ X := by
  classical
  exact Finsupp.onFinset S (fun i => if h : i ∈ S then y ⟨i, h⟩ else 0) (by
    intro i hi; by_contra h; exact hi (dif_neg h))

theorem ofFinset_apply (S : Finset I) (y : S → X) (i : S) : ofFinset S y i = y i := by
  classical
  simp [ofFinset, Finsupp.onFinset_apply, i.2]

theorem ofFinset_apply_of_notMem (S : Finset I) (y : S → X) {i : I} (h : i ∉ S) :
    ofFinset S y i = 0 := by
  classical
  simp [ofFinset, Finsupp.onFinset_apply, h]

theorem ofFinset_injective (S : Finset I) : Function.Injective (ofFinset (X := X) S) := by
  intro y z h; funext i; rw [← ofFinset_apply S y i, ← ofFinset_apply S z i, h]

theorem support_ofFinset_subset (S : Finset I) (y : S → X) : (ofFinset S y).support ⊆ S := by
  intro i hi
  by_contra h
  exact (Finsupp.mem_support_iff.1 hi) (ofFinset_apply_of_notMem S y h)

theorem mem_range_ofFinset (S : Finset I) (l : I →₀ X) (hl : l.support ⊆ S) :
    l ∈ Set.range (ofFinset S) := by
  refine ⟨fun i => l i, ?_⟩
  ext i
  by_cases h : i ∈ S
  · exact ofFinset_apply S _ ⟨i, h⟩
  · rw [ofFinset_apply_of_notMem S _ h]
    exact (Finsupp.notMem_support_iff.1 (fun hi => h (hl hi))).symm

theorem prod_ofFinset {M : Type} [CommMonoid M] (f : I → X → M) (hf0 : ∀ v, f v 0 = 1)
    (S : Finset I) (y : S → X) : (ofFinset S y).prod f = ∏ i : S, f i (y i) := by
  rw [Finsupp.prod_of_support_subset _ (support_ofFinset_subset S y) f (fun i _ => hf0 i),
    ← Finset.prod_coe_sort S]
  exact Finset.prod_congr rfl fun i _ => by rw [ofFinset_apply]

theorem tsum_indicator_support_subset {R : Type} [CommSemiring R] [TopologicalSpace R]
    (f : I → X → R) (hf0 : ∀ v, f v 0 = 1) (S : Finset I) :
    ∑' l : I →₀ X, ({l : I →₀ X | l.support ⊆ S}.indicator (fun l => l.prod f) l) =
      ∑' y : S → X, ∏ i : S, f i (y i) := by
  refine ((ofFinset_injective S).tsum_eq ?_).symm.trans ?_
  · intro l hl
    by_contra h
    exact hl (Set.indicator_of_notMem (fun hs => h (mem_range_ofFinset S l hs)) _)
  · refine tsum_congr fun y => ?_
    rw [Set.indicator_of_mem (show ofFinset S y ∈ {l : I →₀ X | l.support ⊆ S} from
      support_ofFinset_subset S y), prod_ofFinset f hf0]

theorem prod_tsum_eq_tsum_indicator_ennreal (f : I → X → ℝ≥0∞) (hf0 : ∀ v, f v 0 = 1)
    (S : Finset I) :
    ∏ v ∈ S, ∑' x, f v x =
      ∑' l : I →₀ X, ({l : I →₀ X | l.support ⊆ S}.indicator (fun l => l.prod f) l) := by
  rw [tsum_indicator_support_subset f hf0 S,
    GlobalTheory.VolBoxMajorant.tsum_pi_prod_ennreal' (fun (i : S) x => f i x),
    Finset.prod_coe_sort S (fun v => ∑' x, f v x)]

theorem prod_tsum_eq_tsum_indicator (f : I → X → ℂ) (hf0 : ∀ v, f v 0 = 1)
    (hv : ∀ v, Summable fun x => ‖f v x‖) (S : Finset I) :
    ∏ v ∈ S, ∑' x, f v x =
      ∑' l : I →₀ X, ({l : I →₀ X | l.support ⊆ S}.indicator (fun l => l.prod f) l) := by
  classical
  rw [tsum_indicator_support_subset f hf0 S,
    (GlobalTheory.hasSum_pi_prod_of_summable_norm S (fun _ => X) (fun i x => f i x)
      (fun i => hv i)).tsum_eq,
    Finset.prod_coe_sort S (fun v => ∑' x, f v x)]

theorem hasProd_tsum_finsupp_ennreal (f : I → X → ℝ≥0∞) (hf0 : ∀ v, f v 0 = 1) :
    HasProd (fun v => ∑' x, f v x) (∑' l : I →₀ X, l.prod f) := by
  classical
  have hmono : Monotone (fun S : Finset I => ∏ v ∈ S, ∑' x, f v x) := by
    intro S T hST
    exact Finset.prod_le_prod_of_subset_of_one_le' hST
      (fun v _ _ => (hf0 v).symm.le.trans (ENNReal.le_tsum 0))
  have hsup : ⨆ S : Finset I, ∏ v ∈ S, ∑' x, f v x = ∑' l : I →₀ X, l.prod f := by
    simp_rw [prod_tsum_eq_tsum_indicator_ennreal f hf0]
    refine le_antisymm (iSup_le fun S => ENNReal.tsum_le_tsum fun l => ?_) ?_
    · exact Set.indicator_le_self _ _ l
    · rw [ENNReal.tsum_eq_iSup_sum]
      refine iSup_le fun T => le_iSup_of_le (T.biUnion Finsupp.support) ?_
      calc ∑ l ∈ T, l.prod f
          = ∑ l ∈ T, ({l : I →₀ X | l.support ⊆ T.biUnion Finsupp.support}.indicator
              (fun l => l.prod f) l) :=
            Finset.sum_congr rfl fun l hl =>
              (Set.indicator_of_mem (show l ∈ {l : I →₀ X | l.support ⊆ T.biUnion Finsupp.support}
                from Finset.subset_biUnion_of_mem Finsupp.support hl) (fun l : I →₀ X => l.prod f)).symm
        _ ≤ _ := ENNReal.sum_le_tsum T
  have := tendsto_atTop_iSup hmono
  rw [hsup] at this
  exact this

theorem tsum_finsupp_eq_tprod_ennreal (f : I → X → ℝ≥0∞) (hf0 : ∀ v, f v 0 = 1) :
    ∑' l : I →₀ X, l.prod f = ∏' v, ∑' x, f v x :=
  (hasProd_tsum_finsupp_ennreal f hf0).tprod_eq.symm

theorem summable_norm_local (f : I → X → ℂ)
    (hsum : Summable fun p : I × {x : X // x ≠ 0} => ‖f p.1 p.2‖) (v : I) :
    Summable fun x => ‖f v x‖ := by
  have h1 : Summable fun x : {x : X // x ≠ 0} => ‖f v x‖ :=
    ((summable_prod_of_nonneg fun _ => norm_nonneg _).1 hsum).1 v
  haveI : Finite ↥({x : X | x ≠ 0}ᶜ) :=
    ((Set.finite_singleton (0 : X)).subset (by intro x hx; simpa using hx)).to_subtype
  exact (summable_subtype_and_compl (s := {x : X | x ≠ 0})).1 ⟨h1, Summable.of_finite⟩

theorem summable_norm_finsupp_prod (f : I → X → ℂ) (hf0 : ∀ v, f v 0 = 1)
    (hsum : Summable fun p : I × {x : X // x ≠ 0} => ‖f p.1 p.2‖) :
    Summable fun l : I →₀ X => ‖l.prod f‖ := by
  classical
  have hP := (summable_prod_of_nonneg fun _ => norm_nonneg _).1 hsum
  let a : I → ℝ := fun v => ∑' x : {x : X // x ≠ 0}, ‖f v x‖
  have hA : Summable a := hP.2
  have ha0 : ∀ v, 0 ≤ a v := fun v => tsum_nonneg fun _ => norm_nonneg _
  let g : I → X → ℝ≥0∞ := fun v x => ENNReal.ofReal ‖f v x‖
  have hg0 : ∀ v, g v 0 = 1 := by intro v; simp [g, hf0 v]
  have hgv : ∀ v, ∑' x, g v x = ENNReal.ofReal (1 + a v) := by
    intro v
    rw [ENNReal.tsum_eq_add_tsum_ite 0, hg0, ENNReal.ofReal_add zero_le_one (ha0 v),
      ENNReal.ofReal_one, ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hP.1 v)]
    congr 1
    refine Eq.trans ?_ (tsum_subtype {x : X | x ≠ 0} (fun x => ENNReal.ofReal ‖f v x‖)).symm
    refine tsum_congr fun x => ?_
    by_cases hx : x = 0 <;> simp [hx, g]
  have hprod : ∀ l : I →₀ X, ENNReal.ofReal ‖l.prod f‖ = l.prod g := by
    intro l
    simp only [Finsupp.prod, norm_prod, g]
    exact ENNReal.ofReal_prod_of_nonneg fun _ _ => norm_nonneg _
  refine summable_of_sum_le (c := Real.exp (∑' v, a v)) (fun _ => norm_nonneg _) fun T => ?_
  have hS := prod_tsum_eq_tsum_indicator_ennreal g hg0 (T.biUnion Finsupp.support)
  rw [← ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le,
    ENNReal.ofReal_sum_of_nonneg fun _ _ => norm_nonneg _]
  calc ∑ l ∈ T, ENNReal.ofReal ‖l.prod f‖
      = ∑ l ∈ T, ({l : I →₀ X | l.support ⊆ T.biUnion Finsupp.support}.indicator
          (fun l => l.prod g) l) :=
        Finset.sum_congr rfl fun l hl => by
          rw [hprod, Set.indicator_of_mem (show l ∈ {l : I →₀ X | l.support ⊆ T.biUnion Finsupp.support}
            from Finset.subset_biUnion_of_mem Finsupp.support hl) (fun l : I →₀ X => l.prod g)]
    _ ≤ _ := ENNReal.sum_le_tsum T
    _ = ∏ v ∈ T.biUnion Finsupp.support, ∑' x, g v x := hS.symm
    _ = ENNReal.ofReal (∏ v ∈ T.biUnion Finsupp.support, (1 + a v)) := by
        rw [ENNReal.ofReal_prod_of_nonneg fun v _ => by linarith [ha0 v]]
        exact Finset.prod_congr rfl fun v _ => hgv v
    _ ≤ ENNReal.ofReal (Real.exp (∑' v, a v)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc ∏ v ∈ T.biUnion Finsupp.support, (1 + a v)
            ≤ ∏ v ∈ T.biUnion Finsupp.support, Real.exp (a v) :=
              Finset.prod_le_prod₀ (fun v _ => by linarith [ha0 v])
                fun v _ => by linarith [Real.add_one_le_exp (a v)]
          _ = Real.exp (∑ v ∈ T.biUnion Finsupp.support, a v) := (Real.exp_sum _ _).symm
          _ ≤ Real.exp (∑' v, a v) := Real.exp_le_exp.2 (hA.sum_le_tsum _ (fun v _ => ha0 v))

theorem hasProd_tsum_finsupp (f : I → X → ℂ) (hf0 : ∀ v, f v 0 = 1)
    (hsum : Summable fun p : I × {x : X // x ≠ 0} => ‖f p.1 p.2‖) :
    HasProd (fun v => ∑' x, f v x) (∑' l : I →₀ X, l.prod f) := by
  classical
  have hN := summable_norm_finsupp_prod f hf0 hsum
  have key : (fun S : Finset I => ∏ v ∈ S, ∑' x, f v x) = fun S =>
      ∑' l : I →₀ X, ({l : I →₀ X | l.support ⊆ S}.indicator (fun l => l.prod f) l) :=
    funext (prod_tsum_eq_tsum_indicator f hf0 (summable_norm_local f hsum))
  show Tendsto (fun S : Finset I => ∏ v ∈ S, ∑' x, f v x) atTop _
  rw [key]
  refine tendsto_tsum_of_dominated_convergence (bound := fun l : I →₀ X => ‖l.prod f‖) hN
    (fun l => ?_) (Eventually.of_forall fun S l => norm_indicator_le_norm_self _ _)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop l.support] with S hS
  exact (Set.indicator_of_mem (show l ∈ {l : I →₀ X | l.support ⊆ S} from hS)
    (fun l : I →₀ X => l.prod f)).symm

theorem euler_product_intVec {I : Type} (n : ℕ) (f : I → (Fin n → ℤ) → ℂ)
    (hf0 : ∀ v, f v 0 = 1)
    (hsum : Summable fun p : I × {x : Fin n → ℤ // x ≠ 0} => ‖f p.1 p.2‖) :
    (Summable fun l : I →₀ (Fin n → ℤ) => ‖l.prod f‖) ∧
      HasProd (fun v => ∑' x, f v x) (∑' l : I →₀ (Fin n → ℤ), l.prod f) ∧
      ∑' l : I →₀ (Fin n → ℤ), l.prod f = ∏' v, ∑' x, f v x :=
  ⟨summable_norm_finsupp_prod f hf0 hsum, hasProd_tsum_finsupp f hf0 hsum,
    (hasProd_tsum_finsupp f hf0 hsum).tprod_eq.symm⟩

theorem euler_product_intVec_ennreal {I : Type} (n : ℕ) (f : I → (Fin n → ℤ) → ℝ≥0∞)
    (hf0 : ∀ v, f v 0 = 1) :
    HasProd (fun v => ∑' x, f v x) (∑' l : I →₀ (Fin n → ℤ), l.prod f) ∧
      ∑' l : I →₀ (Fin n → ℤ), l.prod f = ∏' v, ∑' x, f v x :=
  ⟨hasProd_tsum_finsupp_ennreal f hf0, tsum_finsupp_eq_tprod_ennreal f hf0⟩

end GlobalTheory.EulerSum
end

section

open Polynomial
open Classical

namespace GlobalTheory

theorem dominantIndex_prod_X_sub_C (K : Type) [NormedField K] [IsUltrametricDist K]
    (ρ : ℝ) (hρ : 0 < ρ) (s : Multiset K) :
    ∀ c : K, c ≠ 0 →
      (∀ j, ‖(C c * (s.map fun a => X - C a).prod).coeff j‖ * ρ ^ j ≤
        ‖(C c * (s.map fun a => X - C a).prod).coeff (Multiset.card (s.filter fun z => ‖z‖ ≤ ρ))‖ *
          ρ ^ Multiset.card (s.filter fun z => ‖z‖ ≤ ρ)) ∧
      ∀ j, Multiset.card (s.filter fun z => ‖z‖ ≤ ρ) < j →
        ‖(C c * (s.map fun a => X - C a).prod).coeff j‖ * ρ ^ j <
        ‖(C c * (s.map fun a => X - C a).prod).coeff (Multiset.card (s.filter fun z => ‖z‖ ≤ ρ))‖ *
          ρ ^ Multiset.card (s.filter fun z => ‖z‖ ≤ ρ) := by
  induction s using Multiset.induction_on with
  | empty =>
    intro c hc
    simp only [Multiset.map_zero, Multiset.prod_zero, mul_one, Multiset.filter_zero,
      Multiset.card_zero, pow_zero, coeff_C_zero]
    refine ⟨fun j => ?_, fun j hj => ?_⟩
    · rcases Nat.eq_zero_or_pos j with h | h
      · subst h; simp
      · rw [coeff_C, if_neg (Nat.pos_iff_ne_zero.mp h)]; simp
    · rw [coeff_C, if_neg (Nat.pos_iff_ne_zero.mp hj)]; simp [hc]
  | cons a s ih =>
    intro c hc
    obtain ⟨h1, h2⟩ := ih c hc
    have heq : C c * ((a ::ₘ s).map fun a => X - C a).prod =
        (X - C a) * (C c * (s.map fun a => X - C a).prod) := by
      rw [Multiset.map_cons, Multiset.prod_cons, mul_left_comm]
    rw [heq, Multiset.filter_cons]
    by_cases ha : ‖a‖ ≤ ρ
    · rw [if_pos ha, Multiset.singleton_add, Multiset.card_cons]
      exact GlobalTheory.T.newtonPolygon_lastDominantIndex_mul_X_sub_C K _ a ρ _ hρ ha h1 h2
    · rw [if_neg ha, zero_add]
      exact GlobalTheory.T.newtonPolygon_dominant_index_X_sub_C_mul K _ a ρ _ hρ (not_le.mp ha) h1 h2

theorem card_roots_closedBall_eq_dominantIndex :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ), 0 < ρ → f ≠ 0 → (∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧ ∀ j, Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff (Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ))‖ * ρ ^ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) := by
  intro K _ _ _ f ρ hρ hf
  have key := dominantIndex_prod_X_sub_C K ρ hρ f.roots f.leadingCoeff
    (leadingCoeff_ne_zero.mpr hf)
  rw [C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree] at key
  exact key

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.witt_vector_gauss_norm_ultrametric : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [CharP R l] [PerfectRing R l] (a : R → ℝ), (∀ x, 0 ≤ a x ∧ a x ≤ 1) → a 0 = 0 → a 1 = 1 → (∀ x y, a (x * y) = a x * a y) → (∀ x y, a (x + y) ≤ max (a x) (a y)) → ∀ r : ℝ, 0 < r → r < 1 → ∀ N : WittVector l R → ℝ, (∀ x, N x = ⨆ n : ℕ, a (x.coeff n) ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → (∀ x y, N (x + y) ≤ max (N x) (N y)) ∧ (∀ x, N (-x) = N x) ∧ ∀ x y, N (x * y) ≤ N x * N y := by
  first | exact @GlobalTheory.WittGauss.gaussNorm_ultrametric_submul | exact GlobalTheory.WittGauss.gaussNorm_ultrametric_submul | (intros; apply GlobalTheory.WittGauss.gaussNorm_ultrametric_submul <;> assumption)
end

section


theorem _root_.GlobalTheory.T.riesz_eigenvector_sesquilinear_function_space : ∀ (X : Type) (C : Submodule ℂ (X → ℂ)), FiniteDimensional ℂ C →
    ∀ (ip Φ : (X → ℂ) → (X → ℂ) → ℂ),
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → ip (a • f + f') g = star a * ip f g + ip f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → ip f (a • g + g') = a * ip f g + ip f g') →
    (∀ f g : X → ℂ, f ∈ C → g ∈ C → ip g f = star (ip f g)) →
    (∀ f : X → ℂ, f ∈ C → f ≠ 0 → 0 < (ip f f).re) →
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → Φ (a • f + f') g = star a * Φ f g + Φ f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → Φ f (a • g + g') = a * Φ f g + Φ f g') →
    (∀ f : X → ℂ, f ∈ C → ∃ h : X → ℂ, h ∈ C ∧ ∀ g : X → ℂ, g ∈ C → ip h g = Φ f g) ∧
    (C ≠ ⊥ → ∃ c : ℂ, ∃ e : X → ℂ, e ∈ C ∧ e ≠ 0 ∧ ∀ f : X → ℂ, f ∈ C → Φ f e = c * ip f e) := by
  first | exact @GlobalTheory.riesz_and_eigenvector_of_sesq_on_fun_space | exact GlobalTheory.riesz_and_eigenvector_of_sesq_on_fun_space | (intros; apply GlobalTheory.riesz_and_eigenvector_of_sesq_on_fun_space <;> assumption)
end

section

open Polynomial

namespace GlobalTheory

theorem weylNumerator_laplace : ∀ (a b : ℕ) (α : Fin a → ℂˣ) (β : Fin b → ℂˣ) (l : Fin (a + b) → ℤ), (Matrix.of fun i j : Fin (a + b) => (((Fin.addCases α β i : ℂˣ) ^ l j : ℂˣ) : ℂ)).det = ∑ J : {J : Finset (Fin (a + b)) // J.card = a}, (-1 : ℂ) ^ ((∑ j ∈ J.1, (j : ℕ)) + a * (a - 1) / 2) * (Matrix.of fun i k : Fin a => ((α i ^ l (J.1.orderEmbOfFin J.2 k) : ℂˣ) : ℂ)).det * (Matrix.of fun i k : Fin b => ((β i ^ l (J.1ᶜ.orderEmbOfFin (by rw [Finset.card_compl, J.2]; simp) k) : ℂˣ) : ℂ)).det := by
  intro a b α β l
  rw [Formalism.ResultantValuation.laplaceExpansionRows ℂ a b]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  rw [Nat.add_comm (a * (a - 1) / 2)]
  congr 2
  · congr 1
    ext i k
    simp [Matrix.submatrix]
  · congr 1
    ext i k
    simp [Matrix.submatrix]

end GlobalTheory
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

theorem _root_.GlobalTheory.T.injective_tensor_lift_equivariant_maps_of_irreducible : ∀ (H X Y : Type) [Group H] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] (τ : Representation ℂ H X) (ρ : Representation ℂ H Y), ρ.IsIrreducible → (∀ T : ρ.IntertwiningMap ρ, ∃ c : ℂ, ∀ v, T v = c • v) → ∀ (M : Submodule ℂ (Y →ₗ[ℂ] X)), (∀ φ ∈ M, ∀ g v, φ (ρ g v) = τ g (φ v)) → Function.Injective (TensorProduct.lift M.subtype) := by
  first | exact @GlobalTheory.SmGL.EvalInj.lift_subtype_injective | exact GlobalTheory.SmGL.EvalInj.lift_subtype_injective | (intros; apply GlobalTheory.SmGL.EvalInj.lift_subtype_injective <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem GlobalTheory.gen_type_core : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) O, (¬ ∃ (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K)) → ∃ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 ∧ ∀ g : GL (Fin r) (IsLocalRing.ResidueField O), (∀ v, a ⬝ᵥ v = 0 → (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).mulVec v = v) → ∀ L : Matrix (Fin r) (Fin r) O, L.map (IsLocalRing.residue O) = (g : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) → ∃ h : GL (Fin r ⊕ Fin t) O, (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl i) (Sum.inl j) - (1 : Matrix (Fin r) (Fin r) O) i j ∈ Ideal.span {ϖ}) ∧ (∀ i j, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr i) (Sum.inl j) ∈ Ideal.span {ϖ}) ∧ (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) * (Matrix.fromBlocks L 0 0 (1 : Matrix (Fin t) (Fin t) O) * x) = x := by
  intro O K _ _ _ _ _ _ _ r t ϖ hϖ x hx
  obtain ⟨a, ha, hA⟩ := GlobalTheory.T.exists_residue_annihilator_of_not_standard_column_form_alt O K r t ϖ hϖ x hx
  refine ⟨a, ha, fun g hg L hL => ?_⟩
  set S : Submodule K (Fin r ⊕ Fin t → K) := Submodule.span K (Set.range fun j => fun i => algebraMap O K (x i j)) with hS
  let U : Submodule O (Fin r ⊕ Fin t → O) := Submodule.comap ((Algebra.linearMap O K).compLeft (Fin r ⊕ Fin t)) (S.restrictScalars O)
  have hU : ∀ u, u ∈ U ↔ (fun i => algebraMap O K (u i)) ∈ S := fun u => Iff.rfl
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_residue_first_block_factor_of_second O r t U a (fun u hu h2 => hA u ((hU u).1 hu) h2) (g : Matrix (Fin r) (Fin r) _) hg
  obtain ⟨P, hP1, hP2⟩ := GlobalTheory.T.dvr_matrix_proj_preimage_alt O K (Fin r ⊕ Fin t) S
  set bt : Matrix (Fin r) (Fin t) O := b.map (Function.surjInv IsLocalRing.residue_surjective) with hbt
  have hbt' : bt.map (IsLocalRing.residue O) = b := by
    ext i j; simp [hbt, Function.surjInv_eq]
  set q₀ : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O := Matrix.fromBlocks L bt 0 1 with hq₀

  have key : ∀ u ∈ U, ∀ i, IsLocalRing.residue O (Matrix.mulVec (1 - q₀) u i) = 0 := by
    intro u hu i
    have h1 := hb u hu
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, map_sub, sub_eq_zero]
    rw [RingHom.map_mulVec, hq₀, Matrix.fromBlocks_map]
    rw [Matrix.fromBlocks_mulVec]
    rcases i with i | i
    · have := congrFun h1 i
      simp only [Sum.elim_inl, Pi.add_apply] at this ⊢
      rw [hL, hbt']
      simpa [Function.comp_def] using this.symm
    · simp [Function.comp_def]
  have hPx : P * x = x := by
    ext i j
    have := hP2 (fun i => x i j) (Submodule.subset_span ⟨j, rfl⟩)
    exact congrFun this i
  set q := q₀ + (1 - q₀) * P with hq
  have hqx : q * x = x := by
    rw [hq, Matrix.add_mul, Matrix.mul_assoc, hPx, Matrix.sub_mul, Matrix.one_mul]; abel
  have hqq : ∀ i j, IsLocalRing.residue O (q i j) = IsLocalRing.residue O (q₀ i j) := by
    intro i j
    have hcol : (fun l => P l j) ∈ U := by
      have := hP1 (Pi.single j 1)
      rw [hU]; simpa [Matrix.mulVec_single] using this
    have := key _ hcol i
    rw [hq, Matrix.add_apply, map_add (f := _)]
    have e : ((1 - q₀) * P) i j = Matrix.mulVec (1 - q₀) (fun l => P l j) i := rfl
    rw [e, this, add_zero]
  obtain ⟨h, h1, h2, h3⟩ := GlobalTheory.T.gl_factor_fromBlocks_mod_uniformizer_alt O r t ϖ hϖ g L hL bt q hqq
  exact ⟨h, h1, h2, by rw [← Matrix.mul_assoc, h3, hqx]⟩
end

section

namespace GlobalTheory

theorem matrix_near_one_pow_prime_deep : ∀ (l : ℕ) [Fact l.Prime] (n : Type) [Fintype n] [DecidableEq n]
    (X : Matrix n n ℚ_[l]) (k : ℕ), (∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-2 : ℤ)) →
    (∀ i j, ‖(X ^ l - 1) i j‖ ≤ (l : ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2))) →
    ∀ i j, ‖(X - 1) i j‖ ≤ (l : ℝ) ^ (-((k : ℤ) + 2)) := by
  intro l hl n _ _ X k h1 h2 i j
  have hL : (2:ℝ) ≤ l := by exact_mod_cast hl.out.two_le
  have hLpos : (0:ℝ) < l := by linarith
  set u : ℝ := (l:ℝ)⁻¹ with hu
  have u0 : 0 < u := inv_pos.mpr hLpos
  have uhalf : u ≤ 1 / 2 := by
    rw [hu, one_div]; exact inv_anti₀ (by norm_num) hL
  have hz : ∀ m : ℕ, (l:ℝ) ^ (-(m:ℤ)) = u ^ m := fun m => by
    rw [zpow_neg, zpow_natCast, inv_pow]
  have e2 : (l:ℝ) ^ (-2:ℤ) = u ^ 2 := hz 2
  have e3 : (l:ℝ) ^ (-(((k + 1 : ℕ) : ℤ) + 2)) = u ^ (k + 3) := by
    rw [← hz]; congr 1
  have e4 : (l:ℝ) ^ (-((k : ℤ) + 2)) = u ^ (k + 2) := by
    rw [← hz]; congr 1
  rw [e4]
  set Y := X - 1 with hY
  haveI : Nonempty (n × n) := ⟨(i, j)⟩
  obtain ⟨⟨i0, j0⟩, hmax⟩ := Finite.exists_max (fun p : n × n => ‖Y p.1 p.2‖)
  set t := ‖Y i0 j0‖ with ht
  have hall : ∀ a b, ‖Y a b‖ ≤ t := fun a b => hmax (a, b)
  suffices hs : t ≤ u ^ (k + 2) from (hall i j).trans hs
  have t0 : 0 ≤ t := norm_nonneg _
  have tsmall : t ≤ u ^ 2 := e2 ▸ h1 i0 j0
  have u1 : u ≤ 1 := by linarith
  have t1 : t ≤ 1 := tsmall.trans (pow_le_one₀ u0.le u1)
  have hR := GlobalTheory.T.norm_one_add_pow_sub_one_sub_smul_le_sq ℚ_[l] n Y t t0 t1 hall l i0 j0
  have hX : (1 + Y) = X := by rw [hY]; abel
  rw [hX] at hR
  have key : ‖((l:ℚ_[l]) • Y) i0 j0‖ ≤ max (‖(X ^ l - 1) i0 j0‖) (t ^ 2) := by
    have : ((l:ℚ_[l]) • Y) i0 j0 = (X ^ l - 1) i0 j0 - (X ^ l - 1 - (l:ℚ_[l]) • Y) i0 j0 := by
      simp [Matrix.sub_apply]
    rw [this]
    have hu' : ∀ a b : ℚ_[l], ‖a - b‖ ≤ max ‖a‖ ‖b‖ := fun a b => by
      rw [sub_eq_add_neg, ← norm_neg b]; exact IsUltrametricDist.norm_add_le_max _ _
    exact (hu' _ _).trans (max_le_max le_rfl hR)
  have hnorm : ‖((l:ℚ_[l]) • Y) i0 j0‖ = u * t := by
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, Padic.norm_p]
  rw [hnorm] at key
  rcases le_max_iff.mp key with h | h
  · have h' : u * t ≤ u * u ^ (k + 2) := by
      rw [← pow_succ', ← e3]; exact h.trans (h2 i0 j0)
    exact le_of_mul_le_mul_left h' u0
  · rcases t0.eq_or_lt with h0 | h0
    · rw [← h0]; positivity
    · exfalso
      have : u ≤ t := by nlinarith
      nlinarith

end GlobalTheory
end
