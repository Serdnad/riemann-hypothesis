module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle002
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PolarDec
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.PolarHyp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle005
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Function.JacobianOneDim

@[expose] public section

section

noncomputable section

namespace PI.RhsWLim.W

open PI.RhsWLim

theorem constVal_of_unimodW_orbitPush (hU : UnimodW) (hO : OrbitPush) : ConstVal :=
  constVal_of_polarHyp rhsTest transW hU hO polarHyp

theorem constVal_of_orbit (hO : OrbitPush) : ConstVal :=
  constVal_of_unimodW_orbitPush unimodW hO

end PI.RhsWLim.W
end
end

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W

variable {k r : ℕ}

instance : T2Space (HU.Gp k r) := inferInstanceAs (T2Space {x : Mt k r // x ∈ HU.amb k r})

instance : LocallyCompactSpace (HU.Gp k r) :=
  show LocallyCompactSpace {x : Mt k r // x ∈ HU.amb k r} from
    HU.amb_closed.isClosedEmbedding_subtypeVal.locallyCompactSpace

def stabH (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) : Subgroup (HU.Gp k r) where
  carrier := {g | Matrix.of (HU.inc g) *ᵥ z' = z'}
  mul_mem' {a b} ha hb := by
    show (Matrix.of (HU.inc a) * Matrix.of (HU.inc b) : Mat k r) *ᵥ z' = z'
    rw [← Matrix.mulVec_mulVec]
    rw [show Matrix.of (HU.inc b) *ᵥ z' = z' from hb]
    exact ha
  one_mem' := by
    show (1 : Mat k r) *ᵥ z' = z'
    exact Matrix.one_mulVec z'
  inv_mem' {a} ha := by
    show (Matrix.of (HU.inc a) : Mat k r)⁻¹ *ᵥ z' = z'
    exact inv_fix (HU.uwb_unit (HU.inc_mem a)) ha

theorem continuous_orbV_inc (z' : Fin (2 * r + k + 1) → ℂ) :
    Continuous (fun g : HU.Gp k r => orbV k r z' (HU.inc g)) := (orbV_cont z').comp HU.inc_cont

theorem stabH_closed (z' : Fin (2 * r + k + 1) → ℂ) : IsClosed ((stabH k r z' : Subgroup (HU.Gp k r)) : Set (HU.Gp k r)) :=
  isClosed_eq (continuous_orbV_inc z') continuous_const

def jH (z' : Fin (2 * r + k + 1) → ℂ) (h : stabH k r z') : Mt k r := HU.inc h.1

theorem jH_memb (z' : Fin (2 * r + k + 1) → ℂ) : MeasurableEmbedding (jH (k := k) (r := r) z') :=
  HU.inc_memb.comp (MeasurableEmbedding.subtype_coe (stabH_closed z').measurableSet)

theorem jH_mem (z' : Fin (2 * r + k + 1) → ℂ) (h : stabH k r z') : Matrix.of (jH z' h) ∈ UWset k r z' :=
  ⟨(HU.inc_mem h.1).1, (HU.inc_mem h.1).2, h.2⟩

theorem range_jH (z' : Fin (2 * r + k + 1) → ℂ) :
    range (jH (k := k) (r := r) z') = {x | Matrix.of x ∈ UWset k r z'} := by
  ext x
  constructor
  · rintro ⟨h, rfl⟩
    exact jH_mem z' h
  · intro hx
    exact ⟨⟨⟨x, ⟨hx.1, hx.2.1⟩⟩, hx.2.2⟩, rfl⟩

theorem map_jH {z' : Fin (2 * r + k + 1) → ℂ} {μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z') μW') :
    (μW'.comap (jH z')).map (jH z') = μW' := by
  rw [(jH_memb z').map_comap, range_jH]
  exact Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hW.2.2.1)

theorem nuH_left {z' : Fin (2 * r + k + 1) → ℂ} {μW' : Measure (Mt k r)} (hW : IsHaarOn (UWset k r z') μW') :
    (μW'.comap (jH z')).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  have hg : Measurable (fun h : stabH k r z' => g * h) := (continuous_const_mul g).measurable
  have e : (jH z' ∘ fun h : stabH k r z' => g * h) = lmulM (Matrix.of (jH z' g)) ∘ jH z' := funext fun h => rfl
  calc (μW'.comap (jH z')).map (fun h => g * h)
      = (((μW'.comap (jH z')).map (fun h => g * h)).map (jH z')).comap (jH z') := ((jH_memb z').comap_map _).symm
    _ = (((μW'.comap (jH z')).map (jH z')).map (lmulM (Matrix.of (jH z' g)))).comap (jH z') := by
        rw [Measure.map_map (jH_memb z').measurable hg, e,
          ← Measure.map_map (HU.lmulM_cont _).measurable (jH_memb z').measurable]
    _ = ((μW'.comap (jH z')).map (jH z')).comap (jH z') := by
        rw [map_jH hW, hW.2.2.2 _ (jH_mem z' g)]
    _ = μW'.comap (jH z') := (jH_memb z').comap_map _

theorem pull_right {z' : Fin (2 * r + k + 1) → ℂ} (ν : Measure (Mt k r))
    (hc : ν {x | Matrix.of x ∉ UWb k r} = 0) (hr : ∀ b ∈ UWset k r z', ν.map (rmulM b) = ν)
    (g : stabH k r z') : (HU.pull ν).map (· * (g : HU.Gp k r)) = HU.pull ν := by
  have hg : Measurable (fun h : HU.Gp k r => h * (g : HU.Gp k r)) := (continuous_mul_const _).measurable
  have e : (HU.inc ∘ fun h : HU.Gp k r => h * (g : HU.Gp k r)) = rmulM (Matrix.of (jH z' g)) ∘ HU.inc :=
    funext fun h => rfl
  calc (HU.pull ν).map (· * (g : HU.Gp k r))
      = (((HU.pull ν).map (· * (g : HU.Gp k r))).map HU.inc).comap HU.inc := (HU.inc_memb.comap_map _).symm
    _ = (((HU.pull ν).map HU.inc).map (rmulM (Matrix.of (jH z' g)))).comap HU.inc := by
        rw [Measure.map_map HU.inc_memb.measurable hg, e,
          ← Measure.map_map (rmulM_cont _).measurable HU.inc_memb.measurable]
    _ = ((HU.pull ν).map HU.inc).comap HU.inc := by
        rw [HU.map_pull ν hc, hr _ (jH_mem z' g)]
    _ = HU.pull ν := HU.inc_memb.comap_map _

theorem orb_fib (z' : Fin (2 * r + k + 1) → ℂ) (g g' : HU.Gp k r) :
    orbV k r z' (HU.inc g) = orbV k r z' (HU.inc g') ↔ g⁻¹ * g' ∈ stabH k r z' := by
  have hu := HU.uwb_unit (HU.inc_mem g)
  show (Matrix.of (HU.inc g) : Mat k r) *ᵥ z' = Matrix.of (HU.inc g') *ᵥ z' ↔
    ((Matrix.of (HU.inc g) : Mat k r)⁻¹ * Matrix.of (HU.inc g')) *ᵥ z' = z'
  constructor
  · intro h
    rw [← Matrix.mulVec_mulVec, ← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  · intro h
    conv_lhs => rw [← h]
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem descUniq : DescUniq := by
  intro k r z' μW' hW hfin ν₁ ν₂ hσ₁ hσ₂ hc₁ hc₂ hr₁ hr₂ hm
  have : SigmaFinite μW' := hW.1
  have hl := nuH_left hW
  have hmass : (μW'.comap (jH z')) univ = μW' univ := by
    conv_rhs => rw [← map_jH hW]
    rw [Measure.map_apply (jH_memb z').measurable MeasurableSet.univ, preimage_univ]
  have h0 : (μW'.comap (jH z')) univ ≠ 0 := by
    rw [hmass]
    exact fun h => hW.2.1 (Measure.measure_univ_eq_zero.1 h)
  have hf : (μW'.comap (jH z')) univ ≠ ⊤ := by rw [hmass]; exact hfin
  have : SigmaFinite (HU.pull ν₁) := HU.pull_sigmaFinite ν₁
  have : SigmaFinite (HU.pull ν₂) := HU.pull_sigmaFinite ν₂
  have hpm : ∀ ν : Measure (Mt k r), ν {x | Matrix.of x ∉ UWb k r} = 0 →
      (HU.pull ν).map (fun g => orbV k r z' (HU.inc g)) = ν.map (orbV k r z') := by
    intro ν hc
    have e : (fun g : HU.Gp k r => orbV k r z' (HU.inc g)) = orbV k r z' ∘ HU.inc := rfl
    rw [e, ← Measure.map_map (orbV_cont z').measurable HU.inc_memb.measurable, HU.map_pull ν hc]
  have key := desc_uniq (stabH k r z') (stabH_closed z') (μW'.comap (jH z')) h0 hf
    (fun g => orbV k r z' (HU.inc g)) (continuous_orbV_inc z') (orb_fib z') (HU.pull ν₁) (HU.pull ν₂)
    (pull_right ν₁ hc₁ hr₁) (pull_right ν₂ hc₂ hr₂) (by rw [hpm ν₁ hc₁, hpm ν₂ hc₂, hm])
  rw [← HU.map_pull ν₁ hc₁, ← HU.map_pull ν₂ hc₂, key]

theorem rhsWInv_of_orb (hO : OrbInv) : RhsWInv := rhsWInv_of descUniq rInvNu hO

end PI.RhsWLim.W.RI
end
end

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

variable {k : ℕ}

theorem radial {T' : ℝ} (hT' : 0 < T') (E : Set ((Fin k → ℂ) × ℂ)) (hE : MeasurableSet E) (y : Fin k → ℂ)
    (θ : ℝ) :
    ∫⁻ R in Set.Ioi (0 : ℝ), ENNReal.ofReal R *
        (coneSh k T' E).indicator 1 (y, (R : ℂ) * Complex.exp (θ * Complex.I)) =
      ∫⁻ t in Set.Ioo (1 : ℝ) 2, ENNReal.ofReal (T' * t) * E.indicator 1 (hq k T' (t⁻¹ • y) θ) := by
  set a := ∑ i, Complex.normSq (y i) with ha_def
  have ha : 0 ≤ a := Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  have hS := measurableSet_coneSh hT' hE
  set g : ℝ → ℝ≥0∞ := fun R => ENNReal.ofReal R *
    (coneSh k T' E).indicator 1 (y, (R : ℂ) * Complex.exp (θ * Complex.I)) with hgdef
  have hsupp : ((Set.Ioi (0 : ℝ)).indicator g).support ⊆ phiR a T' '' Set.Ioo 1 2 := by
    intro R hR
    rw [Function.mem_support] at hR
    have hR0 : R ∈ Set.Ioi (0 : ℝ) := by
      by_contra h
      exact hR (Set.indicator_of_notMem h _)
    rw [Set.indicator_of_mem hR0] at hR
    have hR0' : 0 < R := hR0
    have hmem : (y, (R : ℂ) * Complex.exp (θ * Complex.I)) ∈ coneSh k T' E := by
      by_contra h
      apply hR
      simp only [hgdef, Set.indicator_of_notMem h, mul_zero]
    rw [coneSh_eq hT'] at hmem
    obtain ⟨hneg, h1, h2, -⟩ := hmem
    refine ⟨tau k T' (y, (R : ℂ) * Complex.exp (θ * Complex.I)), ⟨h1, h2⟩, ?_⟩
    have hqv : qf k (y, (R : ℂ) * Complex.exp (θ * Complex.I)) = a - R ^ 2 := by
      unfold qf
      simp only
      rw [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_eq_norm_sq (Complex.exp _),
        Complex.norm_exp_ofReal_mul_I, ← ha_def]
      ring
    have htau2 : tau k T' (y, (R : ℂ) * Complex.exp (θ * Complex.I)) ^ 2 = (R ^ 2 - a) / T' := by
      unfold tau
      rw [Real.sq_sqrt (div_nonneg (by linarith) hT'.le), hqv]
      ring
    unfold phiR
    rw [htau2, div_mul_cancel₀ _ hT'.ne', show a + (R ^ 2 - a) = R ^ 2 by ring, Real.sqrt_sq hR0'.le]
  rw [← lintegral_indicator measurableSet_Ioi, ← setLIntegral_eq_of_support_subset hsupp]
  have hpos : ∀ t : ℝ, 0 < t → 0 < a + t ^ 2 * T' := fun t ht =>
    add_pos_of_nonneg_of_pos ha (mul_pos (pow_pos ht 2) hT')
  have hderiv : ∀ t ∈ Set.Ioo (1 : ℝ) 2, HasDerivWithinAt (phiR a T')
      (2 * t * T' / (2 * Real.sqrt (a + t ^ 2 * T'))) (Set.Ioo 1 2) t := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have h1 : HasDerivAt (fun t => a + t ^ 2 * T') (2 * t * T') t := by
      have := ((hasDerivAt_pow 2 t).mul_const T').const_add a
      exact this.congr_deriv (by ring)
    exact (h1.sqrt (hpos t ht0).ne').hasDerivWithinAt
  have hinj : Set.InjOn (phiR a T') (Set.Ioo 1 2) := by
    intro t1 h1 t2 h2 he
    have h10 : 0 < t1 := by linarith [h1.1]
    have h20 : 0 < t2 := by linarith [h2.1]
    unfold phiR at he
    rw [Real.sqrt_inj (hpos t1 h10).le (hpos t2 h20).le] at he
    have e2 : t1 ^ 2 = t2 ^ 2 := mul_right_cancel₀ hT'.ne' (by linarith)
    exact (pow_left_inj₀ h10.le h20.le two_ne_zero).1 e2
  rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hderiv hinj]
  refine setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
  have ht0 : 0 < t := by linarith [ht.1]
  have hφpos : 0 < Real.sqrt (a + t ^ 2 * T') := Real.sqrt_pos.2 (hpos t ht0)
  have hφ : phiR a T' t = Real.sqrt (a + t ^ 2 * T') := rfl
  rw [Set.indicator_of_mem (show phiR a T' t ∈ Set.Ioi (0 : ℝ) from hφ ▸ hφpos)]
  have hm := slice_mem hT' E y θ t ht0
  have hfac : ENNReal.ofReal |2 * t * T' / (2 * Real.sqrt (a + t ^ 2 * T'))| *
      ENNReal.ofReal (phiR a T' t) = ENNReal.ofReal (T' * t) := by
    rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (div_pos (mul_pos (mul_pos two_pos ht0) hT')
      (mul_pos two_pos hφpos)), hφ]
    congr 1
    field_simp
  by_cases hE' : hq k T' (t⁻¹ • y) θ ∈ E
  · rw [Set.indicator_of_mem hE']
    simp only [hgdef]
    rw [Set.indicator_of_mem (hm.2 ⟨ht.1, ht.2, hE'⟩)]
    simp only [Pi.one_apply, mul_one]
    exact hfac
  · rw [Set.indicator_of_notMem hE']
    simp only [hgdef]
    rw [Set.indicator_of_notMem (fun h => hE' (hm.1 h).2.2)]
    simp

end PI.RhsWLim.W
end
end

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix Set
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros

def UnimodK : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μ : Measure (Mt k r)), IsHaarOn (UWset k r z) μ → μ Set.univ ≠ ⊤ →
    ∀ b ∈ UWset k r z, μ.map (rmulM b) = μ

def FibTrans : Prop :=
  ∀ (k r : ℕ) (z v v' : Fin (2 * r + k + 1) → ℂ), inWb k r z → inWb k r v → inWb k r v' → 0 < Tz k r z →
    herm (Hpk k r) v v = herm (Hpk k r) v' v' → herm (Hpk k r) v z = herm (Hpk k r) v' z →
      ∃ u ∈ UWset k r z, u *ᵥ v = v'

def HypQ : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' →
    ∃ Q : Measure (Fin (2 * r + k + 1) → ℂ), SigmaFinite Q ∧ (∀ s ∈ UWb k r, Q.map (fun v => s *ᵥ v) = Q) ∧
      Q {v | ¬ (inWb k r v ∧ herm (Hpk k r) v v = herm (Hpk k r) z' z')} = 0 ∧
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ g : ℂ → ℝ≥0∞, Measurable g →
        ∫⁻ v, g (herm (Hpk k r) v z) ∂Q = c * ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * g ζ

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

def Gf (μW : Measure (Mt k r)) (F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞) (v : Fin (2 * r + k + 1) → ℂ) : ℝ≥0∞ :=
  ∫⁻ h, F (Matrix.of h *ᵥ v) ∂μW

theorem cont_act : Continuous (fun p : (Fin (2 * r + k + 1) → ℂ) × Mt k r => (Matrix.of p.2 : Mat k r) *ᵥ p.1) :=
  Continuous.matrix_mulVec (continuous_snd (X := Fin (2 * r + k + 1) → ℂ) (Y := Mat k r)) continuous_fst

theorem meas_Gf [SFinite μW] {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) : Measurable (Gf μW F) :=
  (hF.comp cont_act.measurable).lintegral_prod_right'

theorem cont_herm (w : Fin (2 * r + k + 1) → ℂ) : Continuous (fun v => herm (Hpk k r) v w) :=
  continuous_const.dotProduct (continuous_const.matrix_mulVec continuous_id)

theorem herm_both {n : ℕ} (H g : Matrix (Fin n) (Fin n) ℂ) (hg : gᴴ * H * g = H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem inWb_Em (u : Fin (k + 1) → ℂ) : inWb k r (MB.Em k r *ᵥ u) := by
  intro i hi
  simp only [Matrix.mulVec, dotProduct, MB.Em]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [if_neg, zero_mul]
  intro h
  rw [h] at hi
  have := m.isLt
  simp only [wI] at hi
  omega

theorem inWb_emb (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hz' : inWb k r z') : inWb k r (embWb k r μ *ᵥ z') := by
  rw [← inWb_eq hz', Matrix.mulVec_mulVec, emb_mul_Em, ← Matrix.mulVec_mulVec]
  exact inWb_Em _

theorem rhs_orb (hd : WbData k r z z' μW μW' a a' μsec) (F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞) :
    rhsW k r z z' μW μW' μsec (fun x => F (orbV k r z' x)) = ENNReal.ofReal a' *
      ∫⁻ ζ, ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ) * Gf μW F (embWb k r (μsec ζ) *ᵥ z') := by
  unfold rhsW
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun ζ => ?_
  have inner : ∀ h : Mt k r, ∫⁻ h', F (orbV k r z'
      (fun i j => (Matrix.of h * embWb k r (μsec ζ) * (Matrix.of h')⁻¹) i j)) ∂μW' =
        ENNReal.ofReal a' * F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z')) := by
    intro h
    have hae : ∀ᵐ h' ∂μW', Matrix.of h' ∈ UWset k r z' := by
      rw [ae_iff]
      exact hd.haarW'.2.2.1
    calc ∫⁻ h', F (orbV k r z' (fun i j => (Matrix.of h * embWb k r (μsec ζ) * (Matrix.of h')⁻¹) i j)) ∂μW'
        = ∫⁻ h', F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z')) ∂μW' := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with h' hh'
          show F ((Matrix.of h * embWb k r (μsec ζ) * (Matrix.of h')⁻¹) *ᵥ z') =
            F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z'))
          rw [← Matrix.mulVec_mulVec, inv_fix (HU.isUnit_of_uh hh'.1) hh'.2.2, ← Matrix.mulVec_mulVec]
      _ = F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z')) * μW' Set.univ := lintegral_const _
      _ = ENNReal.ofReal a' * F (Matrix.of h *ᵥ (embWb k r (μsec ζ) *ᵥ z')) := by rw [hd.massW', mul_comm]
  simp_rw [inner]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  unfold Gf
  ring

theorem avg_Q (Q : Measure (Fin (2 * r + k + 1) → ℂ)) [SigmaFinite Q] (hQ : ∀ s ∈ UWb k r, Q.map (fun v => s *ᵥ v) = Q)
    (hW : IsHaarOn (UWset k r z) μW) {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ v, Gf μW F v ∂Q = μW Set.univ * ∫⁻ v, F v ∂Q := by
  have := hW.1
  unfold Gf
  rw [lintegral_lintegral_swap (μ := Q) (ν := μW) (f := fun v (h : Mt k r) => F (Matrix.of h *ᵥ v))
    (hF.comp cont_act.measurable).aemeasurable]
  have hae : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z := by
    rw [ae_iff]
    exact hW.2.2.1
  have e : ∀ᵐ h ∂μW, ∫⁻ v, F (Matrix.of h *ᵥ v) ∂Q = ∫⁻ v, F v ∂Q := by
    filter_upwards [hae] with h hh
    have hmv : Measurable (fun v : Fin (2 * r + k + 1) → ℂ => (Matrix.of h : Mat k r) *ᵥ v) :=
      (continuous_const.matrix_mulVec continuous_id).measurable
    rw [← lintegral_map hF hmv, hQ _ ⟨hh.1, hh.2.1⟩]
  rw [lintegral_congr_ae e, lintegral_const, mul_comm]

theorem Gf_fib (hU : UnimodK) (hT : FibTrans) (hW : IsHaarOn (UWset k r z) μW) (hfin : μW Set.univ ≠ ⊤)
    (hz : inWb k r z) (hTz : 0 < Tz k r z) {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F)
    {v v' : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hv' : inWb k r v')
    (h1 : herm (Hpk k r) v v = herm (Hpk k r) v' v') (h2 : herm (Hpk k r) v z = herm (Hpk k r) v' z) :
    Gf μW F v = Gf μW F v' := by
  obtain ⟨u, hu, huv⟩ := hT k r z v' v hz hv' hv hTz h1.symm h2.symm
  have hm : Measurable (fun y : Mt k r => F (Matrix.of y *ᵥ v')) :=
    hF.comp ((cont_act (k := k) (r := r)).comp (Continuous.prodMk continuous_const continuous_id)).measurable
  unfold Gf
  calc ∫⁻ h, F (Matrix.of h *ᵥ v) ∂μW = ∫⁻ h, (fun y : Mt k r => F (Matrix.of y *ᵥ v')) (rmulM u h) ∂μW := by
        refine lintegral_congr fun h => ?_
        show F (Matrix.of h *ᵥ v) = F ((Matrix.of h * u) *ᵥ v')
        rw [← Matrix.mulVec_mulVec, huv]
    _ = ∫⁻ y, F (Matrix.of y *ᵥ v') ∂(μW.map (rmulM u)) := (lintegral_map hm (rmulM_cont u).measurable).symm
    _ = ∫⁻ h, F (Matrix.of h *ᵥ v') ∂μW := by rw [hU k r z μW hW hfin u hu]

end PI.RhsWLim.W.RI
end
end
