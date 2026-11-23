module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle084
public import Mathlib.Data.Matrix.Mul
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle086
public import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailBoundStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle037
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle085
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle047
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle039
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
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
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle080
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals.FubiniLevi
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle011
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle001

@[expose] public section

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem proj_diag_ne_zero_iff (z : (Σ k, ι k) → ℂ) (k : K) (i : ι k) :
    SncRes.proj z ⟨k, (i, i)⟩ ≠ 0 ↔ z ⟨k, i⟩ ≠ 0 := by
  simp only [SncRes.proj]
  constructor
  · intro h h0
    apply h
    simp [h0]
  · intro h
    have hn : (0 : ℝ) < ‖z ⟨k, i⟩‖ := norm_pos_iff.2 h
    have hpos : (0 : ℝ) < ∑ j, ‖z ⟨k, j⟩‖ ^ 2 := by
      refine lt_of_lt_of_le (pow_pos hn 2) ?_
      exact Finset.single_le_sum (f := fun j => ‖z ⟨k, j⟩‖ ^ 2)
        (fun j _ => by positivity) (Finset.mem_univ i)
    have hden : ((∑ j, ‖z ⟨k, j⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hpos.ne'
    exact div_ne_zero (mul_ne_zero h ((map_ne_zero _).2 h)) hden

theorem isOpen_alt_bis (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (p : (k : K) → ι k) :
    IsOpen (SncRes.src P p) := by
  have h : SncRes.src P p = ⋂ k, {x : SncRes.Pts P | x.1 ⟨k, (p k, p k)⟩ ≠ 0} := by
    ext x
    simp only [SncRes.src, Set.mem_ofPred_eq, Set.mem_iInter]
    refine forall_congr' fun k => ?_
    rw [← SncRes.proj_rep x]
    exact (proj_diag_ne_zero_iff _ k (p k)).symm
  rw [h]
  refine isOpen_iInter_of_finite fun k => ?_
  have hc : Continuous fun x : SncRes.Pts P => x.1 ⟨k, (p k, p k)⟩ :=
    (continuous_apply _).comp continuous_subtype_val
  exact isOpen_ne_fun hc continuous_const

theorem chart_coord_ratio : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ∀ p' : (k : K) → ι k, (∀ k, eval (SncRes.coord P p x) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) → ∃ O : Set (SncRes.Pts P), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src P p ∧ ∃ (q : MvPolynomial (Σ k, ι k) ℂ) (F : Fin (Fintype.card (Σ k, ι k)) → MvPolynomial (Σ k, ι k) ℂ), ∀ y ∈ O, (∀ k, eval (SncRes.coord P p y) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) ∧ eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) q ≠ 0 ∧ ∀ l, SncRes.coord P p y l * eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) q = eval (ReciprocityTheory.AnForm.R.affCoord p' fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) (F l) := by
  intro K _ ι _ P _ p x hx p' hp'
  classical
  have key : ∀ y ∈ SncRes.src P p,
      ((∀ k, eval (SncRes.coord P p y) (SncRes.lift p ⟨k, p' k⟩) ≠ 0) ↔ y ∈ SncRes.src P p') := by
    intro y hy
    simp only [SncRes.eval_lift p y hy, ReciprocityTheory.AnForm.R.affCoord]
    constructor
    · intro h k h0
      exact h k (by simp [h0])
    · intro h k
      exact div_ne_zero (h k) (hy k)
  refine ⟨SncRes.src P p ∩ SncRes.src P p', (isOpen_alt_bis P p).inter (isOpen_alt_bis P p'),
    ⟨hx, (key x hx).1 hp'⟩, Set.inter_subset_left, ∏ k, X ⟨k, p k⟩,
    fun l => X ((Fintype.equivFin (Σ k, ι k)).symm l) *
      ∏ k ∈ Finset.univ.erase ((Fintype.equivFin (Σ k, ι k)).symm l).1, X ⟨k, p k⟩, ?_⟩
  rintro y ⟨hy, hy'⟩
  have hw : (fun q => eval (SncRes.coord P p y) (SncRes.lift p q)) =
      ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) := funext (SncRes.eval_lift p y hy)
  simp only [hw]
  have hone : ∀ k, ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨k, p k⟩ = 1 := fun k => by
    simp [ReciprocityTheory.AnForm.R.affCoord, hy k]
  have hne : ∀ k, ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨k, p' k⟩ ≠ 0 := fun k =>
    div_ne_zero (hy' k) (hy k)
  have ha : ∀ k, ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨k, p k⟩ ≠ 0 := by
    intro k
    have : ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨k, p k⟩ =
        1 / ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨k, p' k⟩ := by
      rw [← hone k]; rfl
    rw [this]
    exact div_ne_zero one_ne_zero (hne k)
  refine ⟨(key y hy).2 hy', ?_, fun l => ?_⟩
  · rw [map_prod]
    simp only [eval_X]
    exact Finset.prod_ne_zero_iff.2 fun k _ => ha k
  · set q := (Fintype.equivFin (Σ k, ι k)).symm l with hq
    have hcoord : SncRes.coord P p y l = ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) q := rfl
    rw [map_mul, map_prod, map_prod, hcoord]
    simp only [eval_X]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun k => ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨k, p k⟩)
      (Finset.mem_univ q.1), ← mul_assoc]
    congr 1
    have h1 : ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) ⟨q.1, p q.1⟩ =
        1 / ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨q.1, p' q.1⟩ := by
      rw [← hone q.1]; rfl
    have h2 : ReciprocityTheory.AnForm.R.affCoord p' (ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y)) q =
        ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) q /
          ReciprocityTheory.AnForm.R.affCoord p (SncRes.rep y) ⟨q.1, p' q.1⟩ := rfl
    rw [h1, h2, mul_one_div]

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.ChartInv
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.AnForm.R

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sameOrbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext q
  simp only
  rw [inv_mul_cancel_left₀ (hc q.1)]

theorem sameOrbit_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') :
    SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, hd, rfl⟩ := h'
  refine ⟨fun k => c k * d k, fun k => mul_ne_zero (hc k) (hd k), ?_⟩
  funext q
  simp only
  ring

theorem proj_eq_of_sameOrbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : proj z = proj z' := by
  obtain ⟨c, hc, rfl⟩ := h
  funext ⟨k, i, j⟩
  simp only [proj]
  have hN : (∑ l, ‖c k * z' ⟨k, l⟩‖ ^ 2 : ℝ) = ‖c k‖ ^ 2 * ∑ l, ‖z' ⟨k, l⟩‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [norm_mul, mul_pow]
  have hcc : c k * starRingEnd ℂ (c k) ≠ 0 :=
    mul_ne_zero (hc k) ((map_ne_zero _).2 (hc k))
  rw [hN, map_mul]
  push_cast
  rw [← Complex.mul_conj', show c k * z' ⟨k, i⟩ * (starRingEnd ℂ (c k) * starRingEnd ℂ (z' ⟨k, j⟩)) =
    (c k * starRingEnd ℂ (c k)) * (z' ⟨k, i⟩ * starRingEnd ℂ (z' ⟨k, j⟩)) by ring]
  exact mul_div_mul_left _ _ hcc

theorem blockNorm_ne_zero {z : (Σ k, ι k) → ℂ} {k : K} {j : ι k} (hj : z ⟨k, j⟩ ≠ 0) :
    ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
  have h1 : 0 < ‖z ⟨k, j⟩‖ ^ 2 := by positivity
  have h2 : ‖z ⟨k, j⟩‖ ^ 2 ≤ ∑ l, ‖z ⟨k, l⟩‖ ^ 2 :=
    Finset.single_le_sum (f := fun l => ‖z ⟨k, l⟩‖ ^ 2) (fun l _ => by positivity) (Finset.mem_univ j)
  exact Complex.ofReal_ne_zero.2 (lt_of_lt_of_le h1 h2).ne'

theorem sameOrbit_of_proj_eq {z z' : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hz' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (h : proj z = proj z') : SameOrbit z z' := by
  have key : ∀ k, ∃ c : ℂ, c ≠ 0 ∧ ∀ i, z ⟨k, i⟩ = c * z' ⟨k, i⟩ := by
    intro k
    obtain ⟨j, hj⟩ := hz k
    obtain ⟨j', hj'⟩ := hz' k
    have hN := blockNorm_ne_zero hj
    have hN' := blockNorm_ne_zero hj'
    have hp : ∀ a b, z ⟨k, a⟩ * starRingEnd ℂ (z ⟨k, b⟩) / ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) =
        z' ⟨k, a⟩ * starRingEnd ℂ (z' ⟨k, b⟩) / ((∑ l, ‖z' ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) :=
      fun a b => congrFun h ⟨k, a, b⟩
    have hcj : starRingEnd ℂ (z ⟨k, j⟩) ≠ 0 := (map_ne_zero _).2 hj
    have hw : z' ⟨k, j⟩ ≠ 0 := by
      intro h0
      have := hp j j
      rw [h0, zero_mul, zero_div, div_eq_zero_iff] at this
      rcases this with h1 | h1
      · exact (mul_ne_zero hj hcj) h1
      · exact hN h1
    have hcw : starRingEnd ℂ (z' ⟨k, j⟩) ≠ 0 := (map_ne_zero _).2 hw
    refine ⟨starRingEnd ℂ (z' ⟨k, j⟩) * ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) /
      (((∑ l, ‖z' ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) * starRingEnd ℂ (z ⟨k, j⟩)),
      div_ne_zero (mul_ne_zero hcw hN) (mul_ne_zero hN' hcj), fun i => ?_⟩
    have := hp i j
    rw [div_eq_div_iff hN hN'] at this
    field_simp
    linear_combination this
  choose c hc hci using key
  exact ⟨c, hc, funext fun q => hci q.1 q.2⟩

theorem lift_vec {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k) (x : Pts P)
    (hx : x ∈ src P p) :
    (fun q => eval (coord P p x) (lift p q)) = affCoord p (rep x) :=
  funext (eval_lift p x hx)

theorem orbit_rep_lift {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (p : (k : K) → ι k) (x : Pts P)
    (hx : x ∈ src P p) :
    SameOrbit (rep x) (fun q => eval (coord P p x) (lift p q)) := by
  rw [lift_vec p x hx]
  exact sameOrbit_affCoord p (rep x) hx

theorem lift_mem_conePts {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) :
    (fun q => eval (coord P p x) (lift p q)) ∈ conePts P := by
  rw [lift_vec p x hx]
  exact (conePts_of_chartIdeal hP p _
    ((mem_conePts_iff_chartIdeal hP p (rep x) hx).1 (rep_mem x))).1

theorem isMultiHomogIdeal_sup {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)}
    (hP : IsMultiHomogIdeal P) (hD : IsMultiHomogIdeal D) : IsMultiHomogIdeal (P ⊔ D) := by
  obtain ⟨S, hS, rfl⟩ := hP
  obtain ⟨T, hT, rfl⟩ := hD
  refine ⟨S ∪ T, ?_, (Ideal.span_union S T).symm⟩
  rintro f (hf | hf)
  · exact hS f hf
  · exact hT f hf

theorem zero_bd_iff {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P)
    (hD : IsMultiHomogIdeal D) (p : (k : K) → ι k) (x : Pts P) (hx : x ∈ src P p) :
    (∀ h ∈ bd P D p, eval (coord P p x) h = 0) ↔
      (fun q => eval (coord P p x) (lift p q)) ∈ conePts D := by
  have hmem := lift_mem_conePts hP p x hx
  rw [lift_vec p x hx] at hmem ⊢
  have hone : ∀ k, affCoord p (rep x) ⟨k, p k⟩ = 1 := fun k => by
    simp [affCoord, hx k]
  constructor
  · intro h
    have hz : ∀ f ∈ chartIdeal (P ⊔ D) p, eval (affCoord p (rep x)) f = 0 := by
      intro f hf
      rw [← eval_renC]
      exact h _ (Ideal.le_radical (Ideal.mem_map_of_mem _ hf))
    have := (conePts_of_chartIdeal (isMultiHomogIdeal_sup hP hD) p _ hz).1
    exact ⟨this.1, fun f hf => this.2 f (Ideal.mem_sup_right hf)⟩
  · intro hDm g hg
    have hle : chartIdeal (P ⊔ D) p ≤ RingHom.ker (eval (affCoord p (rep x))) := by
      refine sup_le (sup_le (fun f hf => hmem.2 f hf) (fun f hf => hDm.2 f hf)) ?_
      rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      show eval _ _ = 0
      simp [hone k]
    obtain ⟨n, hn⟩ := hg
    have h0 := renPt_zero (chartIdeal (P ⊔ D) p) (affCoord p (rep x)) (fun f hf => hle hf) _ hn
    rw [map_pow] at h0
    exact eq_zero_of_pow_eq_zero h0

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.chart_lifts_package : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)), ReciprocityTheory.AnForm.R.IsMultiHomogIdeal P → ReciprocityTheory.AnForm.R.IsMultiHomogIdeal D → (∀ x : SncRes.Pts P, ∃ p : (k : K) → ι k, x ∈ SncRes.src P p) ∧ (∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) ∈ ReciprocityTheory.AnForm.R.conePts P) ∧ (∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p ∩ SncRes.src P p', ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) (fun q => eval (SncRes.coord P p' x) (SncRes.lift p' q))) ∧ (∀ z ∈ ReciprocityTheory.AnForm.R.conePts P, ∃ p : (k : K) → ι k, ∃ x ∈ SncRes.src P p, ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) z) ∧ (∀ p p' : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ∀ x' ∈ SncRes.src P p', ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) (fun q => eval (SncRes.coord P p' x') (SncRes.lift p' q)) → x = x') ∧ ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src P p, ((∀ h ∈ SncRes.bd P D p, eval (SncRes.coord P p x) h = 0) ↔ (fun q => eval (SncRes.coord P p x) (SncRes.lift p q)) ∈ ReciprocityTheory.AnForm.R.conePts D) := by
  intro K _ ι _ P D hP hD
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨p, hp, -⟩ := ReciprocityTheory.AnForm.R.exists_chart (rep x) (rep_mem x).1
    exact ⟨p, hp⟩
  · exact fun p x hx => SncRes.lift_mem_conePts hP p x hx
  · intro p p' x hx
    exact SncRes.sameOrbit_trans (SncRes.sameOrbit_symm (SncRes.orbit_rep_lift p x hx.1))
      (SncRes.orbit_rep_lift p' x hx.2)
  · intro z hz
    obtain ⟨p, hp, -⟩ := ReciprocityTheory.AnForm.R.exists_chart z hz.1
    let x : SncRes.Pts P := ⟨SncRes.proj z, z, hz, rfl⟩
    have hrz : ReciprocityTheory.AnForm.R.SameOrbit (SncRes.rep x) z :=
      SncRes.sameOrbit_of_proj_eq (SncRes.rep_mem x).1 hz.1 (SncRes.proj_rep x)
    have hx : x ∈ SncRes.src P p := by
      obtain ⟨c, hc, he⟩ := hrz
      intro k
      rw [he]
      exact mul_ne_zero (hc k) (hp k)
    exact ⟨p, x, hx, SncRes.sameOrbit_trans
      (SncRes.sameOrbit_symm (SncRes.orbit_rep_lift p x hx)) hrz⟩
  · intro p p' x hx x' hx' h
    have h1 : ReciprocityTheory.AnForm.R.SameOrbit (SncRes.rep x) (SncRes.rep x') :=
      SncRes.sameOrbit_trans (SncRes.orbit_rep_lift p x hx)
        (SncRes.sameOrbit_trans h (SncRes.sameOrbit_symm (SncRes.orbit_rep_lift p' x' hx')))
    apply Subtype.ext
    rw [← SncRes.proj_rep x, ← SncRes.proj_rep x']
    exact SncRes.proj_eq_of_sameOrbit h1
  · exact fun p x hx => SncRes.zero_bd_iff hP hD p x hx
end
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem _root_.GlobalTheory.T.exists_continuous_change_of_frame : ∀ (n g m : ℕ) (M f : (Fin n → ℂ) → Fin m → Fin g → ℂ) (T₀ : Matrix (Fin m) (Fin m) ℂ), (∀ i, ContinuousAt (fun z => M z i) 0) → (∀ i, ContinuousAt (fun z => f z i) 0) → LinearIndependent ℂ (M 0) → (∀ i, f 0 i = ∑ j, T₀ j i • M 0 j) → (∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, f z i ∈ Submodule.span ℂ (Set.range (M z))) → ∃ T : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ, ContinuousAt T 0 ∧ T 0 = T₀ ∧ ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, f z i = ∑ j, T z j i • M z j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SolveCoeff.coeff_continuous | exact GlobalTheory.CompanionTheory.Ar.SolveCoeff.coeff_continuous | (intros; apply GlobalTheory.CompanionTheory.Ar.SolveCoeff.coeff_continuous <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem _root_.GlobalTheory.T.gram_det_pos_of_semidefinite_transversal : ∀ (g : ℕ) (Hb : Matrix (Fin g) (Fin g) ℂ) (U : Submodule ℂ (Fin g → ℂ)) (k : ℕ) (q : Fin k → Fin g → ℂ), Hb.IsHermitian → (∀ v : Fin g → ℂ, 0 ≤ (v ⬝ᵥ Hb *ᵥ star v).re ∧ ((v ⬝ᵥ Hb *ᵥ star v).re = 0 → v ∈ U)) → (∀ l : Fin k → ℂ, ∑ c, l c • q c ∈ U → l = 0) → 0 < (Matrix.of fun c c' => q c' ⬝ᵥ Hb *ᵥ star (q c)).det.re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef.gram_det_re_pos | exact GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef.gram_det_re_pos | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit.GramSemidef.gram_det_re_pos <;> assumption)
end

section

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem _root_.GlobalTheory.T.exists_int_preimage_of_orthogonal_kernel : ∀ (g : ℕ) (S : Matrix (Fin g) (Fin g) ℤ), Sᵀ = S → ∀ u : Fin g → ℤ, (∀ v : Fin g → ℤ, S *ᵥ v = 0 → u ⬝ᵥ v = 0) → ∃ (N : ℤ) (c : Fin g → ℤ), N ≠ 0 ∧ N • u = S *ᵥ c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IntegralKernel.exists_smul_eq_mulVec | exact GlobalTheory.CompanionTheory.Ar.IntegralKernel.exists_smul_eq_mulVec | (intros; apply GlobalTheory.CompanionTheory.Ar.IntegralKernel.exists_smul_eq_mulVec <;> assumption)
end

section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.tail_bound_statement_holds : TailBoundStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.tailBound_holds | exact GlobalTheory.CompanionTheory.Ar.Giv.tailBound_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.tailBound_holds <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem _root_.GlobalTheory.CompanionTheory.Relay.generic_degree_of_projection_and_fibre_dim : PFCoordStatement → FibreDimStatement → GenDegStatement := by
  first | exact @PositivityTheory.HtPt.Aig.genDeg | exact PositivityTheory.HtPt.Aig.genDeg
end

section

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Giv

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
open GroundTheory.Heights₂.Heights.HilbertSamuel GroundTheory.Heights₂.Heights.HilbertSamuel.EmbeddingWeight

section SlopeTestRemainingChoices

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

noncomputable def conjugateProjection {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) where
  toFun w := star (Ψ (star w))
  map_add' a b := by simp only [star_add, map_add (f := _)]
  map_smul' c w := by
    simp only [star_smul, map_smul, RingHom.id_apply, star_star]

theorem conjugateProjection_star {e : ℕ} (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (w : ((k : K) → ι k) → ℂ) : conjugateProjection Ψ (star w) = star (Ψ w) := by
  change star (Ψ (star (star w))) = _
  rw [star_star]

theorem isSectionOn_one_of_degree_zero {P : Ideal (MRing ι)} {d : ℕ} {A : HermLine ι}
    (hP : IsArithVar P d) (hA : A.a = 0) : IsSectionOn P A 1 := by
  refine ⟨0, fun k => by simp [hA], ?_, ?_⟩
  · intro m hm k
    have hm0 : m = 0 := by
      classical
      have := MvPolynomial.support_one (R := ℤ) (σ := Σ k, ι k) ▸ hm
      simpa using this
    simp [hm0]
  · exact (Ideal.ne_top_iff_one P).1 hP.2.1.1.ne_top


open Classical in
theorem logNorm_one_eq_indicator {Ω F : Type} [Field Ω] [Field F] [Algebra F Ω] {y : (Σ k, ι k) → Ω}
    {P : Ideal (MRing ι)} {tg : F →+* ℂ} {B : HermLine ι}
    (huniq : ∀ z ∈ mcPts P, ∃! s : F →+* ℂ, LiesOver y s z)
    (hB : ∀ z ∈ mcPts P, ∀ s : F →+* ℂ, LiesOver y s z → B.h z = if s = tg then Real.exp (-1) else 1) :
    ∀ z ∈ mcPts P, logNorm B 1 z = ({z | LiesOver y tg z}.indicator fun _ => (1 : ℝ)) z := by
  classical
  intro z hz
  obtain ⟨s, hs, hs'⟩ := huniq z hz
  have hone : ‖eval z (map (Int.castRingHom ℂ) (1 : MRing ι))‖ = 1 := by simp
  unfold logNorm
  rw [hone, hB z hz s hs]
  by_cases hst : s = tg
  · subst hst
    rw [Set.indicator_of_mem (show z ∈ {z | LiesOver y s z} from hs), if_pos rfl, one_div,
      Real.log_inv, Real.log_exp, neg_neg]
  · rw [Set.indicator_of_notMem (fun h => hst (hs' tg h).symm), if_neg hst]
    simp

end SlopeTestRemainingChoices

theorem conjugate_pieces_same_mass :
    ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (sg : F →+* ℂ), IsArithVar (mCoordIdeal y) (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsConjInvariantH (L j)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y (ComplexEmbedding.conjugate sg) z}.indicator fun _ => (1 : ℝ)) = ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) := by
  intro hRes K _ ι _ Ω _ F _ _ _ y D L sg hP hL hC huniq
  classical
  have hpos : ∀ tg s : F →+* ℂ, 0 < (if s = tg then Real.exp (-1) else (1 : ℝ)) := by
    intro tg s
    split_ifs
    · exact Real.exp_pos _
    · exact one_pos
  obtain ⟨B, hBa, hBs, hB⟩ := exists_smooth_weight_const_near_embeddings K ι Ω F y
    (fun s => if s = sg then Real.exp (-1) else 1) (hpos sg) huniq
  obtain ⟨B', hBa', hBs', hB'⟩ := exists_smooth_weight_const_near_embeddings K ι Ω F y
    (fun s => if s = ComplexEmbedding.conjugate sg then Real.exp (-1) else 1)
    (hpos (ComplexEmbedding.conjugate sg)) huniq
  have hBv : ∀ z ∈ mcPts (mCoordIdeal y), ∀ s : F →+* ℂ, LiesOver y s z →
      B.h z = if s = sg then Real.exp (-1) else 1 := fun z hz s hs => (hB z hz s hs).self_of_nhds
  have hBv' : ∀ z ∈ mcPts (mCoordIdeal y), ∀ s : F →+* ℂ, LiesOver y s z →
      B'.h z = if s = ComplexEmbedding.conjugate sg then Real.exp (-1) else 1 :=
    fun z hz s hs => (hB' z hz s hs).self_of_nhds
  rw [← GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts (mCoordIdeal y)
      (fun _ _ _ => rfl) (logNorm_one_eq_indicator huniq hBv'),
    ← GroundTheory.Heights₂.Heights.Inter.DiagRAux.ptsIntegral_congr_mcPts (mCoordIdeal y)
      (fun _ _ _ => rfl) (logNorm_one_eq_indicator huniq hBv)]
  by_cases hex : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (D + 1) → ℂ), IsGoodProj (mCoordIdeal y) Ψ
  · obtain ⟨Ψ, hΨ⟩ := hex
    have hstar : ∀ z ∈ mcPts (mCoordIdeal y), B'.h (star z) = B.h z := by
      intro z hz
      obtain ⟨s, hs, -⟩ := huniq z hz
      have hzc : star z ∈ mcPts (mCoordIdeal y) := conjVec_mem_mcPts hz
      have hsc : LiesOver y (ComplexEmbedding.conjugate s) (star z) := liesOver_conjVec hs
      have hiff : ComplexEmbedding.conjugate s = ComplexEmbedding.conjugate sg ↔ s = sg :=
        ⟨fun h => by simpa using congrArg ComplexEmbedding.conjugate h, fun h => by rw [h]⟩
      rw [hBv' _ hzc _ hsc, hBv z hz s hs]
      simp only [hiff]
    obtain ⟨hΨ', hI⟩ := GlobalTheory.T.points_integral_conjugation_symmetry K ι (mCoordIdeal y) D Ψ (conjugateProjection Ψ) L B B' hP hΨ
      (conjugateProjection_star Ψ) hL hC hBa hBs hBa' hBs' hstar
    rw [ptsIntegral_eq_at hRes resBridge hP hΨ' hL hBs' (isSectionOn_one_of_degree_zero hP hBa'),
      ptsIntegral_eq_at hRes resBridge hP hΨ hL hBs (isSectionOn_one_of_degree_zero hP hBa), hI]
  · unfold ptsIntegral
    rw [dite_eq_right hex, dite_eq_right hex]

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField

theorem _root_.GlobalTheory.T.sum_over_embeddings_unit_invariance : ArithIntersectionSystemStatement → PtsIntegrableStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (L : Fin D → HermLine ι) (θ : (𝓞 F)ˣ), IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, IsSmoothHerm (L j)) → (∀ z ∈ mcPts (mCoordIdeal y), ∃! s : F →+* ℂ, LiesOver y s z) → ∑ sg : F →+* ℂ, Real.log ‖sg ((θ : 𝓞 F) : F)‖ * ptsIntegral (mCoordIdeal y) (pot L) ({z | LiesOver y sg z}.indicator fun _ => (1 : ℝ)) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.sum_log_unit_mul_mass_eq_zero | exact GlobalTheory.CompanionTheory.Ar.Giv.sum_log_unit_mul_mass_eq_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.sum_log_unit_mul_mass_eq_zero <;> assumption)
end
