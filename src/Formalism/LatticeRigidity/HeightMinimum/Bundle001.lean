module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.Algebra.DirectSum.LinearMap
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.PID
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

@[expose] public section

section

open MeasureTheory Metric Module

namespace Formalism.SA.P

theorem card_le_of_separated {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {α : Type*} (S : Finset α) (g : α → E) (lam R : ℝ)
    (hlam : 0 < lam) (hR : 0 ≤ R)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → lam ≤ ‖g x - g y‖)
    (hbd : ∀ x ∈ S, ‖g x‖ ≤ R) :
    (S.card : ℝ) ≤ (1 + 2 * R / lam) ^ finrank ℝ E := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  set μ : Measure E := Measure.addHaar with hμ
  have hr : 0 < lam / 2 := by positivity
  have hR2 : 0 < R + lam / 2 := by positivity
  have hdisj : Set.PairwiseDisjoint (↑S : Set α) (fun x => ball (g x) (lam / 2)) := by
    intro x hx y hy hxy
    refine Set.disjoint_left.mpr ?_
    intro z hz1 hz2
    simp only [mem_ball, dist_eq_norm] at hz1 hz2
    have h1 := hsep x hx y hy hxy
    have h2 : ‖g x - g y‖ < lam := by
      calc ‖g x - g y‖ = ‖(z - g y) - (z - g x)‖ := by congr 1; abel
        _ ≤ ‖z - g y‖ + ‖z - g x‖ := norm_sub_le _ _
        _ < lam / 2 + lam / 2 := add_lt_add hz2 hz1
        _ = lam := by ring
    linarith
  have hsub : (⋃ x ∈ S, ball (g x) (lam / 2)) ⊆ ball (0 : E) (R + lam / 2) := by
    intro z hz
    simp only [Set.mem_iUnion] at hz
    obtain ⟨x, hx, hz⟩ := hz
    simp only [mem_ball, dist_eq_norm, sub_zero] at hz ⊢
    calc ‖z‖ = ‖(z - g x) + g x‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - g x‖ + ‖g x‖ := norm_add_le _ _
      _ < lam / 2 + R := add_lt_add_of_lt_of_le hz (hbd x hx)
      _ = R + lam / 2 := by ring
  have hball : ∀ c : E, ∀ r : ℝ, 0 < r →
      μ (ball c r) = ENNReal.ofReal (r ^ finrank ℝ E) * μ (ball 0 1) :=
    fun c r hr' => Measure.addHaar_ball_of_pos μ c hr'
  have hb1 : ∀ x, μ (ball (g x) (lam / 2)) =
      ENNReal.ofReal ((lam / 2) ^ finrank ℝ E) * μ (ball 0 1) := fun x => hball _ _ hr
  have hV0 : μ (ball (0 : E) 1) ≠ 0 := (measure_ball_pos μ (0 : E) one_pos).ne'
  have hVtop : μ (ball (0 : E) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have key : (S.card : ENNReal) * ENNReal.ofReal ((lam / 2) ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((R + lam / 2) ^ finrank ℝ E) * μ (ball 0 1) := by
    calc (S.card : ENNReal) * ENNReal.ofReal ((lam / 2) ^ finrank ℝ E) * μ (ball 0 1)
        = ∑ x ∈ S, μ (ball (g x) (lam / 2)) := by
          simp only [hb1, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ = μ (⋃ x ∈ S, ball (g x) (lam / 2)) :=
          (measure_biUnion_finset hdisj (fun x _ => measurableSet_ball)).symm
      _ ≤ μ (ball 0 (R + lam / 2)) := measure_mono hsub
      _ = _ := hball 0 _ hR2
  have key2 : (S.card : ENNReal) * ENNReal.ofReal ((lam / 2) ^ finrank ℝ E) ≤
      ENNReal.ofReal ((R + lam / 2) ^ finrank ℝ E) := by
    exact (ENNReal.mul_le_mul_iff_left hV0 hVtop).mp key
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at key2
  have key3 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp key2
  have hpos : 0 < (lam / 2) ^ finrank ℝ E := pow_pos hr _
  have hq : 1 + 2 * R / lam = (R + lam / 2) / (lam / 2) := by
    first
    | (field_simp; done)
    | (field_simp; ring)
  rw [hq, div_pow, le_div_iff₀ hpos]
  exact key3

end Formalism.SA.P
end

section

namespace Formalism.SA.P

open Matrix Polynomial
open scoped ComplexOrder

section TracePow

variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem finite_eig (f : Module.End K V) : {μ | f.maxGenEigenspace μ ≠ ⊥}.Finite := by
  first
  | exact WellFoundedGT.finite_ne_bot_of_iSupIndep (Module.End.independent_maxGenEigenspace f)
  | exact CompleteLattice.WellFoundedGT.finite_ne_bot_of_iSupIndep
      (Module.End.independent_maxGenEigenspace f)
  | exact CompleteLattice.WellFoundedGT.finite_ne_bot_of_independent
      (Module.End.independent_maxGenEigenspace f)
  | exact CompleteLattice.WellFounded.finite_ne_bot_of_independent wellFounded_gt
      (Module.End.independent_maxGenEigenspace f)

theorem trace_pow_restrict_maxGen (f : Module.End K V) (μ : K) (j : ℕ) :
    LinearMap.trace K _ ((f ^ j).restrict
        (Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ)) =
      (Module.finrank K (f.maxGenEigenspace μ) : K) * μ ^ j := by
  have h1 : Set.MapsTo f (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) :=
    Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ
  have hpow : ∀ m : ℕ, ∀ z : f.maxGenEigenspace μ,
      (((f.restrict h1) ^ m) z : V) = (f ^ m) z := by
    intro m
    induction m with
    | zero => intro z; simp
    | succ m ih =>
      intro z
      first
      | rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ih]
      rfl
  have hg : (f ^ j).restrict
      (Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ) =
      (f.restrict h1) ^ j :=
    LinearMap.ext fun z => Subtype.ext (by rw [hpow]; rfl)
  rw [hg]
  have hxy : IsNilpotent (f.restrict h1 -
      algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) := by
    convert Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap f μ using 1
    refine LinearMap.ext fun z => Subtype.ext ?_
    first
    | rfl
  generalize f.restrict h1 = x at hxy ⊢
  have hc : Commute x (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) :=
    (Algebra.commutes μ x).symm
  have hnil : IsNilpotent
      (x ^ j - (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) ^ j) := by
    rw [← hc.geom_sum₂_mul]
    have hcomm : Commute (∑ i ∈ Finset.range j, x ^ i *
        (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) ^ (j - 1 - i))
        (x - algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) := by
      refine Commute.sub_right ?_ ?_
      · first
        | exact Commute.sum_left _ _ _ fun i _ =>
            ((Commute.refl x).pow_left i).mul_left (hc.symm.pow_left _)
        | exact Commute.sum_left fun i _ =>
            ((Commute.refl x).pow_left i).mul_left (hc.symm.pow_left _)
      · first
        | exact Commute.sum_left _ _ _ fun i _ =>
            (hc.pow_left i).mul_left ((Commute.refl _).pow_left _)
        | exact Commute.sum_left fun i _ =>
            (hc.pow_left i).mul_left ((Commute.refl _).pow_left _)
    first
    | exact hcomm.isNilpotent_mul_left hxy
  have h0 : LinearMap.trace K _ (x ^ j -
      (algebraMap K (Module.End K (f.maxGenEigenspace μ)) μ) ^ j) = 0 := by
    first
    | exact (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, ← map_pow (algebraMap K (Module.End K (f.maxGenEigenspace μ))),
    Algebra.algebraMap_eq_smul_one, map_smul, LinearMap.trace_one, smul_eq_mul, mul_comm]

theorem trace_pow_eq_sum (f : Module.End K V) (j : ℕ) :
    LinearMap.trace K V (f ^ j) = ∑ μ ∈ (finite_eig f).toFinset,
      (Module.finrank K (f.maxGenEigenspace μ) : K) * μ ^ j := by
  classical
  have htop : ⨆ μ ∈ (finite_eig f).toFinset, f.maxGenEigenspace μ = ⊤ := by
    refine eq_top_iff.mpr ?_
    first
    | rw [← Module.End.iSup_maxGenEigenspace_eq_top f]
    refine iSup_le fun μ => ?_
    by_cases hμ : f.maxGenEigenspace μ = ⊥
    · rw [hμ]; exact bot_le
    · exact le_iSup₂_of_le (f := fun μ (_ : μ ∈ (finite_eig f).toFinset) => f.maxGenEigenspace μ)
        μ (by simpa using hμ) le_rfl
  have hind : iSupIndep (fun μ : (finite_eig f).toFinset => f.maxGenEigenspace (μ : K)) := by
    first
    | exact (Module.End.independent_maxGenEigenspace f).comp Subtype.val_injective
  have hmap : ∀ μ : K, Set.MapsTo (f ^ j) (f.maxGenEigenspace μ) (f.maxGenEigenspace μ) :=
    fun μ => Module.End.mapsTo_maxGenEigenspace_of_comm ((Commute.refl f).pow_right j) μ
  have key := LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup _ hind hmap ⊤ htop.symm
  have htr := LinearMap.trace_restrict_eq_of_forall_mem (⊤ : Submodule K V) (f ^ j)
    (fun x => (Submodule.mem_top : (f ^ j) x ∈ (⊤ : Submodule K V)))
  exact htr.symm.trans (key.trans (Finset.sum_congr rfl fun μ _ => trace_pow_restrict_maxGen f μ j))

end TracePow

section Lattice

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

end Lattice

end Formalism.SA.P
end
