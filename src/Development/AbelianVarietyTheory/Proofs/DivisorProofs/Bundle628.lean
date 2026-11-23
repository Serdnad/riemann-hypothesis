module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle374
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle582
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.Integers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle583
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle017
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle013
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadTie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle002

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

theorem _root_.GlobalTheory.T.le_of_injOn_differentiableOn_complex : ∀ (d d' : ℕ) (U : Set (Fin d → ℂ)) (f : (Fin d → ℂ) → (Fin d' → ℂ)), IsOpen U → U.Nonempty → DifferentiableOn ℂ f U → Set.InjOn f U → d ≤ d' := by
  first | exact @GlobalTheory.InjHol.le_of_injOn_differentiableOn | exact GlobalTheory.InjHol.le_of_injOn_differentiableOn | (intros; apply GlobalTheory.InjHol.le_of_injOn_differentiableOn <;> assumption)
end

section

open Complex Matrix

theorem _root_.GlobalTheory.T.thetaFunction_ne_zero_at_divisionPoint_selfDual : ∀ (V : Type) [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (g : ℕ) (B : LinearMap.BilinForm ℚ V) (p : V →ₗ[ℤ] (Fin g → ℂ)), Function.Injective p → ∀ L : Submodule ℤ V, L.FG → (∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ k : ℤ, B x y = k) → Submodule.span ℝ (p '' (L : Set V)) = ⊤ → ∀ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ u v, (p u ⬝ᵥ Hm.mulVec (star (p v))).im = (B u v : ℝ)) → ∀ c : V → ℂ, (∀ v, ‖c v‖ = 1) → ∀ N : ℕ, 2 ≤ N → ∀ f : (Fin g → ℂ) → ℂ, Differentiable ℂ f → f ≠ 0 → (∀ v ∈ L, ∀ z, f (z + p v) = c v * cexp (N * (Real.pi * (z ⬝ᵥ Hm.mulVec (star (p v))) + Real.pi / 2 * (p v ⬝ᵥ Hm.mulVec (star (p v))))) * f z) → ∃ v ∈ L, f ((N : ℂ)⁻¹ • p v) ≠ 0 := by
  first | exact @GlobalTheory.ThetaDivisionPoints.exists_ne_zero_of_selfDual | exact GlobalTheory.ThetaDivisionPoints.exists_ne_zero_of_selfDual | (intros; apply GlobalTheory.ThetaDivisionPoints.exists_ne_zero_of_selfDual <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory

namespace HolConj

variable {J : Type} [Fintype J] [DecidableEq J] {d : J → ℕ}

def unit (j : J) (p q : Fin (d j)) : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ :=
  Pi.single j (Matrix.single p q 1)

lemma pi_single_mul_ne {R : J → Type} [∀ i, MulZeroClass (R i)] {i j : J} (h : i ≠ j)
    (x : R i) (y : R j) : (Pi.single i x : Π k, R k) * Pi.single j y = 0 := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [Pi.single_apply, Ne.symm h]
  · simp [Pi.single_apply, hk]

lemma unit_mul_ne_factor {j j' : J} (h : j ≠ j') (p q : Fin (d j)) (p' q' : Fin (d j')) :
    unit (d := d) j p q * unit j' p' q' = 0 :=
  pi_single_mul_ne h _ _

lemma unit_mul_same (j : J) (p q r : Fin (d j)) :
    unit (d := d) j p q * unit j q r = unit j p r := by
  simp only [unit, ← Pi.single_mul, Matrix.single_mul_single_same, _root_.mul_one]

lemma unit_mul_ne (j : J) (p q p' r : Fin (d j)) (h : q ≠ p') :
    unit (d := d) j p q * unit j p' r = 0 := by
  simp only [unit, ← Pi.single_mul, Matrix.single_mul_single_of_ne _ _ _ _ h, Pi.single_zero]

lemma pi_single_sum {R : J → Type} [∀ i, AddCommMonoid (R i)] {X : Type} (s : Finset X)
    (j : J) (f : X → R j) :
    (Pi.single j (∑ x ∈ s, f x) : Π k, R k) = ∑ x ∈ s, Pi.single j (f x) :=
  map_sum (AddMonoidHom.single R j) f s

lemma sum_unit_diag : ∑ j, ∑ k, unit (d := d) j k k = 1 := by
  simp only [unit]
  have : ∀ j, ∑ k, (Pi.single j (Matrix.single k k (1:ℂ)) : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
      = Pi.single j 1 := by
    intro j
    rw [← Matrix.sum_single_one, pi_single_sum]
  simp only [this]
  exact Finset.univ_sum_single (fun j => (1 : Matrix (Fin (d j)) (Fin (d j)) ℂ))

lemma eq_sum_unit (t : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    t = ∑ j, ∑ p, ∑ q, t j p q • unit j p q := by
  conv_lhs => rw [← Finset.univ_sum_single t]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Matrix.matrix_eq_sum_single (t j)]
  simp only [unit, pi_single_sum, ← Pi.single_smul, Matrix.smul_single, smul_eq_mul, _root_.mul_one]

end HolConj

end GlobalTheory

namespace GlobalTheory

namespace HolConj

variable {J : Type} [Fintype J] [DecidableEq J] {d : J → ℕ} [∀ j, NeZero (d j)]
variable {A : Type} [Ring A] [Algebra ℂ A]

def conjMat (f g : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] A) : A :=
  ∑ j, ∑ k, f (unit j k 0) * g (unit j 0 k)

lemma conjMat_self (f : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] A) :
    conjMat f f = 1 := by

  simp only [conjMat, ← map_mul, unit_mul_same, ← map_sum, sum_unit_diag, map_one]

lemma conjMat_unit (f g : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] A)
    (j' : J) (p q : Fin (d j')) :
    f (unit j' p q) * conjMat f g = conjMat f g * g (unit j' p q) := by
  have hL : f (unit j' p q) * conjMat f g = f (unit j' p 0) * g (unit j' 0 q) := by
    simp only [conjMat, Finset.mul_sum, ← _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_eq_single j']
    · rw [Finset.sum_eq_single q]
      · rw [unit_mul_same]
      · intro k _ hk
        rw [unit_mul_ne _ _ _ _ _ (Ne.symm hk), map_zero, zero_mul]
      · simp
    · intro j _ hj
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [unit_mul_ne_factor (Ne.symm hj), map_zero, zero_mul]
    · simp
  have hR : conjMat f g * g (unit j' p q) = f (unit j' p 0) * g (unit j' 0 q) := by
    simp only [conjMat, Finset.sum_mul, _root_.mul_assoc, ← map_mul]
    rw [Finset.sum_eq_single j']
    · rw [Finset.sum_eq_single p]
      · rw [unit_mul_same]
      · intro k _ hk
        rw [unit_mul_ne _ _ _ _ _ hk, map_zero, mul_zero]
      · simp
    · intro j _ hj
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [unit_mul_ne_factor hj, map_zero, mul_zero]
    · simp
  rw [hL, hR]

lemma conjMat_intertwines (f g : (Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] A)
    (t : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    f t * conjMat f g = conjMat f g * g t := by
  rw [eq_sum_unit t]

  simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
  conjMat_unit]

end HolConj

theorem holFamily_conj_const : ∀ (S : Type) [Ring S] [Algebra ℂ S] [FiniteDimensional ℂ S] [IsSemisimpleRing S] (g m : ℕ) (B : Set (Fin m → ℂ)) (b₀ : Fin m → ℂ) (F : (Fin m → ℂ) → (S →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ)), IsOpen B → b₀ ∈ B → (∀ a i j, DifferentiableOn ℂ (fun b => F b a i j) B) → ∃ (B' : Set (Fin m → ℂ)) (h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ h b₀ = 1 ∧ (∀ i j, DifferentiableOn ℂ (fun b => h b i j) B') ∧ ∀ b ∈ B', IsUnit (h b) ∧ ∀ a, F b a * h b = h b * F b₀ a := by
  intro S _ _ _ _ g m B b₀ F hB hb₀ hF
  obtain ⟨n, d, hd, ⟨e⟩⟩ := IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed ℂ S
  let f : (Fin m → ℂ) →
      ((Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) :=
    fun b => (F b).comp e.symm.toAlgHom
  let h : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun b => HolConj.conjMat (f b) (f b₀)
  have hdiff : ∀ i j, DifferentiableOn ℂ (fun b => h b i j) B := by
    intro i j
    simp only [h, f, HolConj.conjMat, Matrix.sum_apply, Matrix.mul_apply, AlgHom.comp_apply]
    refine DifferentiableOn.fun_sum fun _ _ => DifferentiableOn.fun_sum fun _ _ =>
      DifferentiableOn.fun_sum fun _ _ => (hF _ _ _).mul_const _
  have hc : ContinuousOn h B :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hdiff i j).continuousOn
  have hdet : ContinuousOn (fun b => (h b).det) B :=
    (continuous_id.matrix_det).comp_continuousOn hc
  have h₀ : h b₀ = 1 := HolConj.conjMat_self _
  refine ⟨B ∩ (fun b => (h b).det) ⁻¹' {0}ᶜ, h,
    hdet.isOpen_inter_preimage hB isOpen_compl_singleton, ⟨hb₀, by simp [h₀]⟩,
    Set.inter_subset_left, h₀, fun i j => (hdiff i j).mono Set.inter_subset_left, ?_⟩
  rintro b ⟨-, hb⟩
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hb), fun a => ?_⟩
  have := HolConj.conjMat_intertwines (f b) (f b₀) (e a)
  simpa [f] using this

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory

theorem dimH_image_le_of_differentiableOn_complex {d d' : ℕ} {U : Set (Fin d → ℂ)}
    {f : (Fin d → ℂ) → (Fin d' → ℂ)} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) :
    dimH (f '' U) ≤ (Module.finrank ℝ (Fin d → ℂ) : ENNReal) := by
  set S : ℕ → Set (Fin d → ℂ) := fun n =>
    {x | ∀ y, dist y x < 1 / ((n : ℝ) + 1) → dist (f y) (f x) ≤ ((n : ℝ) + 1) * dist y x}
    with hS
  have hcov : f '' U ⊆ ⋃ n, f '' S n := by
    rintro _ ⟨x, hx, rfl⟩
    have hd : DifferentiableAt ℂ f x := (hf x hx).differentiableAt (hU.mem_nhds hx)
    obtain ⟨C, hC, hCw⟩ := hd.hasFDerivAt.isBigO_sub.exists_pos
    obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.1 hCw.bound
    obtain ⟨n, hn⟩ := exists_nat_gt (max C (1 / ε))
    refine Set.mem_iUnion.2 ⟨n, x, ?_, rfl⟩
    intro y hy
    have hn1 : C < (n : ℝ) + 1 := by linarith [le_max_left C (1 / ε)]
    have hn2 : 1 / ε < (n : ℝ) + 1 := by linarith [le_max_right C (1 / ε)]
    have hy' : dist y x < ε := by
      refine lt_of_lt_of_le hy ?_
      rw [div_le_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at hn2
      linarith
    have := hεb hy'
    rw [dist_eq_norm, dist_eq_norm]
    calc ‖f y - f x‖ ≤ C * ‖y - x‖ := this
      _ ≤ ((n : ℝ) + 1) * ‖y - x‖ := by gcongr
  have hSn : ∀ n, dimH (f '' S n) ≤ dimH (S n) := by
    intro n
    apply dimH_image_le_of_locally_lipschitzOn
    intro x _
    refine ⟨((n : NNReal) + 1), S n ∩ Metric.ball x (1 / (2 * ((n : ℝ) + 1))),
      inter_mem_nhdsWithin _ (Metric.ball_mem_nhds _ (by positivity)), ?_⟩
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    have hab : dist a b < 1 / ((n : ℝ) + 1) := by
      have h1 := Metric.mem_ball.1 ha.2
      have h2 := Metric.mem_ball'.1 hb.2
      calc dist a b ≤ dist a x + dist x b := dist_triangle _ _ _
        _ < 1 / (2 * ((n : ℝ) + 1)) + 1 / (2 * ((n : ℝ) + 1)) := add_lt_add h1 h2
        _ = 1 / ((n : ℝ) + 1) := by field_simp; ring
    have := hb.1 a hab
    simpa using this
  calc dimH (f '' U) ≤ dimH (⋃ n, f '' S n) := dimH_mono hcov
    _ = ⨆ n, dimH (f '' S n) := dimH_iUnion _
    _ ≤ dimH (Set.univ : Set (Fin d → ℂ)) :=
        iSup_le fun n => (hSn n).trans (dimH_mono (Set.subset_univ _))
    _ = _ := Real.dimH_univ_eq_finrank _

theorem le_of_countable_holomorphic_images_cover :
    ∀ (d d' : ℕ) (K : Type) [Countable K] (U : K → Set (Fin d → ℂ))
      (f : K → (Fin d → ℂ) → (Fin d' → ℂ)) (W : Set (Fin d' → ℂ)),
      (∀ i, IsOpen (U i)) → (∀ i, DifferentiableOn ℂ (f i) (U i)) → IsOpen W →
      W.Nonempty → W ⊆ ⋃ i, f i '' U i → d' ≤ d := by
  intro d d' K _ U f W hU hf hW hne hcov
  obtain ⟨w, hw⟩ := hne
  have h1 : dimH W = (Module.finrank ℝ (Fin d' → ℂ) : ENNReal) :=
    Real.dimH_of_mem_nhds (hW.mem_nhds hw)
  have h2 : dimH W ≤ (Module.finrank ℝ (Fin d → ℂ) : ENNReal) := by
    calc dimH W ≤ dimH (⋃ i, f i '' U i) := dimH_mono hcov
      _ = ⨆ i, dimH (f i '' U i) := dimH_iUnion _
      _ ≤ _ := iSup_le fun i => dimH_image_le_of_differentiableOn_complex (hU i) (hf i)
  rw [h1] at h2
  have h3 : Module.finrank ℝ (Fin d' → ℂ) ≤ Module.finrank ℝ (Fin d → ℂ) := by
    exact_mod_cast h2
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype] at h3
  simp at h3
  omega

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section
namespace GlobalTheory.SpecBC

theorem baseChange_specDecomp : ∀ (g a m : ℕ) (O : Type) [CommRing O] (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (χ : Fin a → (O →+* ℂ)) (ω : O) (l l' : ℂ) (E : Fin a → Matrix (Fin g) (Fin g) ℂ), l ≠ l' → (∀ i j, i ≠ j → ∃ c, χ i c ≠ χ j c) → (∀ i, E i * E i = E i) → (∀ i, (E i).trace = (m : ℂ)) → (∀ i c, ρ c * E i = χ i c • E i) → (∀ i c, E i * ρ c = χ i c • E i) → (l - l') • ∑ i, E i = ρ ω - l' • (1 : Matrix (Fin g) (Fin g) ℂ) → (∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (x : Fin g → R'), (ρ ω).map j *ᵥ x = j l • x → ∃ y : Fin a → Fin g → R', (∀ i c, (ρ c).map j *ᵥ y i = j (χ i c) • y i) ∧ x = ∑ i, y i) ∧ ∀ (k : Type) [Field k] (j : ℂ →+* k) (i : Fin a), χ i ω = l → Module.finrank k (⨅ c, LinearMap.ker (Matrix.mulVecLin ((ρ c).map j) - j (χ i c) • LinearMap.id) : Submodule k (Fin g → k)) = m := by
  intro g a m O _ ρ χ ω l l' E hll hsep hidem htr hrE hEr hsum
  have hsm : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (r : ℂ) (M : Matrix (Fin g) (Fin g) ℂ),
      (r • M).map j = j r • M.map j := by
    intro R' _ j r M; ext; simp
  have hmul : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (M N : Matrix (Fin g) (Fin g) ℂ),
      (M * N).map j = M.map j * N.map j := by
    intro R' _ j M N; exact Matrix.map_mul

  have hrel : ∀ (R' : Type) [CommRing R'] (j : ℂ →+* R') (x : Fin g → R'),
      j (l - l') • ∑ i, (E i).map j *ᵥ x = (ρ ω).map j *ᵥ x - j l' • x := by
    intro R' _ j x
    have h := congrArg (fun M => (RingHom.mapMatrix j M) *ᵥ x) hsum
    simp only [RingHom.mapMatrix_apply] at h
    have hs : (∑ i, E i).map j = ∑ i, (E i).map j := by ext; simp [Matrix.sum_apply]
    rw [hsm, hs, Matrix.smul_mulVec, Matrix.sum_mulVec] at h
    rw [h, Matrix.map_sub _ (map_sub j), Matrix.sub_mulVec, hsm, Matrix.smul_mulVec, Matrix.map_one _ (map_zero j) (map_one j),
      Matrix.one_mulVec]
  refine ⟨fun R' _ j x hx => ?_, fun k _ j i hi => ?_⟩
  · refine ⟨fun i => (E i).map j *ᵥ x, fun i c => ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, ← hmul, hrE, hsm, Matrix.smul_mulVec]
    · have hu : IsUnit (j (l - l')) := (sub_ne_zero.mpr hll).isUnit.map j
      have h := hrel R' j x
      rw [hx, ← sub_smul, ← map_sub] at h
      exact (hu.smul_left_cancel.mp h).symm
  · have hj : ∀ z : ℂ, z ≠ 0 → j z ≠ 0 := fun z hz => (hz.isUnit.map j).ne_zero
    have hK : (⨅ c, LinearMap.ker (Matrix.mulVecLin ((ρ c).map j) - j (χ i c) • LinearMap.id) :
        Submodule k (Fin g → k)) = LinearMap.range (Matrix.mulVecLin ((E i).map j)) := by
      ext y
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, LinearMap.mem_range]
      constructor
      · intro hy
        refine ⟨y, ?_⟩
        have hz : ∀ i', i' ≠ i → (E i').map j *ᵥ y = 0 := by
          intro i' hne
          obtain ⟨c, hc⟩ := hsep i' i hne
          have h1 : (E i').map j *ᵥ ((ρ c).map j *ᵥ y) = j (χ i' c) • ((E i').map j *ᵥ y) := by
            rw [Matrix.mulVec_mulVec, ← hmul, hEr, hsm, Matrix.smul_mulVec]
          rw [hy c, Matrix.mulVec_smul] at h1
          have h2 : (j (χ i' c) - j (χ i c)) • ((E i').map j *ᵥ y) = 0 := by
            rw [sub_smul, ← h1, sub_self]
          rw [← map_sub] at h2
          exact (smul_eq_zero.mp h2).resolve_left (hj _ (sub_ne_zero.mpr hc))
        have h := hrel k j y
        rw [hy ω, hi, ← sub_smul, ← map_sub,
          Finset.sum_eq_single i (fun b _ hb => hz b hb) (by simp)] at h
        exact smul_right_injective _ (hj _ (sub_ne_zero.mpr hll)) h
      · rintro ⟨z, rfl⟩ c
        rw [Matrix.mulVec_mulVec, ← hmul, hrE, hsm, Matrix.smul_mulVec]
    rw [hK]
    have hPP : (E i).map j * (E i).map j = (E i).map j := by rw [← hmul, hidem]
    have he : IsIdempotentElem (Matrix.mulVecLin ((E i).map j)) := by
      unfold IsIdempotentElem
      rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, hPP]
    have h1 := (LinearMap.IsIdempotentElem.isProj_range _ he).trace
    rw [← Matrix.toLin'_apply', LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin g)),
      LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin'] at h1
    have htj : ((E i).map j).trace = j (E i).trace := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [Matrix.trace, map_sum]
    rw [htj, htr, map_natCast] at h1
    haveI : CharZero k := (RingHom.charZero_iff j.injective).1 inferInstance
    exact_mod_cast h1.symm

end GlobalTheory.SpecBC
end
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory

theorem isSemisimpleRing_of_posForm_adjoint_closed :
    ∀ (r : ℕ) (Q : Matrix (Fin r) (Fin r) ℂ) (S : Subalgebra ℂ (Matrix (Fin r) (Fin r) ℂ)), Q.IsHermitian →
      (∀ z : Fin r → ℂ, z ≠ 0 → 0 < (star z ⬝ᵥ (Q *ᵥ z)).re) →
      (∀ x ∈ S, ∃ y ∈ S, Q * y = xᴴ * Q) → IsSemisimpleRing S := by
  intro r Q S hQ hpos hadj
  have hnd : ∀ w : Fin r → ℂ, star w ⬝ᵥ (Q *ᵥ w) = 0 → w = 0 := by
    intro w hw
    by_contra hne
    have := hpos w hne
    rw [hw] at this
    simp at this
  have key : ∀ (b : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ),
      star (b *ᵥ w) ⬝ᵥ (Q *ᵥ (b *ᵥ w)) = star w ⬝ᵥ ((bᴴ * Q * b) *ᵥ w) := by
    intro b w
    simp only [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have step : ∀ b : Matrix (Fin r) (Fin r) ℂ, Q * b = bᴴ * Q →
      ∀ w : Fin r → ℂ, (b * b) *ᵥ w = 0 → b *ᵥ w = 0 := by
    intro b hb w hw
    apply hnd
    rw [key, show bᴴ * Q * b = Q * (b * b) by rw [← hb, Matrix.mul_assoc], ← Matrix.mulVec_mulVec, hw,
      Matrix.mulVec_zero, dotProduct_zero]
  haveI : IsArtinianRing S := IsArtinianRing.of_finite ℂ _
  rw [IsArtinianRing.isSemisimpleRing_iff_jacobson, eq_bot_iff]
  intro x hx
  rw [Ideal.mem_bot]
  obtain ⟨y, hyS, hy⟩ := hadj x.1 x.2
  let y' : S := ⟨y, hyS⟩
  have hyx : y' * x ∈ Ring.jacobson S := Ideal.mul_mem_left _ _ hx
  obtain ⟨n, hn⟩ : IsNilpotent (Ring.jacobson S) := IsSemiprimaryRing.isNilpotent
  have h1 : (y' * x) ^ n = 0 := by
    have := Ideal.pow_mem_pow hyx n
    rw [hn] at this
    simpa using this
  have h2 : (y * x.1) ^ n = 0 := by simpa [y'] using congrArg Subtype.val h1
  have hsa : Q * (y * x.1) = (y * x.1)ᴴ * Q := by
    have e1 : yᴴ * Q = Q * x.1 := by
      have := congrArg Matrix.conjTranspose hy
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQ.eq,
        Matrix.conjTranspose_conjTranspose] at this
      exact this
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hy]
  have hz : ∀ m : ℕ, (y * x.1) ^ (m + 1) = 0 → y * x.1 = 0 := by
    intro m
    induction m with
    | zero => intro h; simpa using h
    | succ m ih =>
      intro hm
      apply ih
      rw [Matrix.ext_iff_mulVec]
      intro v
      have e2 : ((y * x.1) * (y * x.1)) *ᵥ ((y * x.1) ^ m *ᵥ v) = 0 := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, ← pow_succ', ← pow_succ', hm, Matrix.zero_mulVec]
      rw [Matrix.zero_mulVec, pow_succ', ← Matrix.mulVec_mulVec]
      exact step _ hsa _ e2
  have ha : y * x.1 = 0 := hz n (by rw [pow_succ, h2, zero_mul])
  apply Subtype.ext
  rw [Matrix.ext_iff_mulVec]
  intro w
  rw [ZeroMemClass.coe_zero, Matrix.zero_mulVec]
  apply hnd
  rw [key, ← hy, Matrix.mul_assoc, ha, Matrix.mul_zero, Matrix.zero_mulVec, dotProduct_zero]

end GlobalTheory
end

section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.exists_algHom_lift_residuePoint_finite_flat : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Flat O A] (c : A →ₐ[O] IsLocalRing.ResidueField O), ∃ x : A →ₐ[O] O, ∀ a, IsLocalRing.residue O (x a) = c a := by
  first | exact @GlobalTheory.ResiduePointLift.exists_algHom_lift | exact GlobalTheory.ResiduePointLift.exists_algHom_lift | (intros; apply GlobalTheory.ResiduePointLift.exists_algHom_lift <;> assumption)
end
