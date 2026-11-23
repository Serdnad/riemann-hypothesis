module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.Bundle006
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.HaarUniq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.OrbitPushI
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightedLimitGauge.RhsHaar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Norm.Transitivity

@[expose] public section

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim HU

variable {m : ℕ}

def realE (X : Matrix (Fin m) (Fin m) ℂ) : EuclideanSpace ℝ (Fin m × Fin m × Bool) :=
  (WithLp.equiv 2 _).symm (realifyFun X)

theorem realE_apply (X : Matrix (Fin m) (Fin m) ℂ) (p : Fin m × Fin m × Bool) :
    realE X p = realifyFun X p := rfl

theorem unr_realE (X : Matrix (Fin m) (Fin m) ℂ) : unrealify (realE X) = X := by
  funext i j
  simp only [unrealify, realE_apply, realifyFun]
  simp

theorem realE_unr (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) : realE (unrealify x) = x := by
  ext ⟨i, j, b⟩
  rw [realE_apply]
  cases b <;> simp [realifyFun, unrealify]

theorem unr_add (x y : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (x + y) = unrealify x + unrealify y := by
  funext i j
  apply Complex.ext <;> simp [unrealify]

theorem unr_smul (c : ℝ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    unrealify (c • x) = (c : ℂ) • unrealify x := by
  funext i j
  apply Complex.ext <;> simp [unrealify]

theorem realE_add (X Y : Matrix (Fin m) (Fin m) ℂ) : realE (X + Y) = realE X + realE Y := by
  ext ⟨i, j, b⟩
  cases b <;> simp [realE_apply, realifyFun]

theorem realE_smul (c : ℝ) (X : Matrix (Fin m) (Fin m) ℂ) : realE ((c : ℂ) • X) = c • realE X := by
  ext ⟨i, j, b⟩
  cases b <;> simp [realE_apply, realifyFun]

def conjL (q : Matrix (Fin m) (Fin m) ℂ) :
    EuclideanSpace ℝ (Fin m × Fin m × Bool) →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun x := realE (q * unrealify x * q⁻¹)
  map_add' x y := by rw [unr_add, Matrix.mul_add, Matrix.add_mul, realE_add]
  map_smul' c x := by
    rw [unr_smul, Matrix.mul_smul, Matrix.smul_mul, realE_smul]; rfl

theorem conjL_apply (q : Matrix (Fin m) (Fin m) ℂ) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    conjL q x = realE (q * unrealify x * q⁻¹) := rfl

theorem norm_realE (X : Matrix (Fin m) (Fin m) ℂ) :
    ‖realE X‖ = Real.sqrt (∑ i, ∑ j, Complex.normSq (X i j)) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp only [realE_apply, realifyFun, Real.norm_eq_abs, sq_abs, if_true, Bool.false_eq_true, if_false,
    Complex.normSq_apply]
  ring

theorem frob_trace (X : Matrix (Fin m) (Fin m) ℂ) :
    ((∑ i, ∑ j, Complex.normSq (X i j) : ℝ) : ℂ) = (X * Xᴴ).trace := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.mul_conj]

theorem frob_conj (q X : Matrix (Fin m) (Fin m) ℂ) (hq : qᴴ * q = 1) :
    ∑ i, ∑ j, Complex.normSq ((q * X * q⁻¹) i j) = ∑ i, ∑ j, Complex.normSq (X i j) := by
  have hqi : q⁻¹ = qᴴ := Matrix.inv_eq_left_inv hq
  apply Complex.ofReal_injective
  rw [frob_trace, frob_trace, hqi]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc (q * X * qᴴ * (q * (Xᴴ * qᴴ))).trace = (q * (X * (qᴴ * q) * Xᴴ) * qᴴ).trace := by
        simp only [Matrix.mul_assoc]
    _ = (X * Xᴴ * (qᴴ * q)).trace := by
        rw [hq, Matrix.mul_one, Matrix.mul_one, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hq, Matrix.one_mul]
    _ = (X * Xᴴ).trace := by rw [hq, Matrix.mul_one]

theorem conj_lieOf {k r : ℕ} (q : Mat k r) (hq : q ∈ UWb k r) (X : Mat k r) (hX : X ∈ lieOf (UWb k r)) :
    q * X * q⁻¹ ∈ lieOf (UWb k r) := by
  intro t
  have hu := uwb_unit hq
  have e : (t : ℂ) • (q * X * q⁻¹) = q * ((t : ℂ) • X) * q⁻¹ := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det q).2 hu)]
  exact uwb_mul (uwb_mul hq (hX t)) (uwb_inv hq)

theorem ballConj : BallConj := by
  intro k r ρ q hq hqu x hx
  have hu := uwb_unit hq
  obtain ⟨v, hv, hvx⟩ := hx

  have hmap : Submodule.map (conjL q) (lieE (UWb k r)) ≤ lieE (UWb k r) := by
    rw [lieE, Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨_, ⟨X, hX, rfl⟩, rfl⟩
    refine ⟨q * X * q⁻¹, conj_lieOf q hq X hX, ?_⟩
    show realE (q * X * q⁻¹) = conjL q (realE X)
    rw [conjL_apply, unr_realE]
  have hmem : conjL q (v : EuclideanSpace ℝ _) ∈ lieE (UWb k r) :=
    hmap ⟨v, v.2, rfl⟩
  refine ⟨⟨conjL q v, hmem⟩, ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right] at hv ⊢
    show ‖conjL q (v : EuclideanSpace ℝ _)‖ < ρ
    rw [conjL_apply, norm_realE, frob_conj q _ hqu, ← norm_realE, realE_unr]
    exact hv
  · have hx' : (Matrix.of x : Mat k r) * q = NormedSpace.exp (unrealify (v : EuclideanSpace ℝ _)) := by
      have := congrArg (fun f : Mt k r => (Matrix.of f : Mat k r)) hvx
      exact this.symm
    show (fun i j => NormedSpace.exp (unrealify (conjL q (v : EuclideanSpace ℝ _))) i j) =
      q * Matrix.of x
    rw [conjL_apply, unr_realE, Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det q).2 hu), ← hx']
    funext i j
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

end PI.RhsWLim.W
end
end

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def wEquiv (k : ℕ) : ((Fin k → ℂ) × ℂ) ≃ₗ[ℂ] (Fin (k + 1) → ℂ) where
  toFun := toW k
  invFun := ofW k
  map_add' p q := by
    funext j
    unfold toW
    by_cases h : j.val < k
    · simp only [dif_pos h, Prod.fst_add, Pi.add_apply]
    · simp only [dif_neg h, Prod.snd_add, Pi.add_apply]
  map_smul' c p := by
    funext j
    unfold toW
    by_cases h : j.val < k
    · simp only [dif_pos h, Prod.smul_fst, Pi.smul_apply, RingHom.id_apply]
    · simp only [dif_neg h, Prod.smul_snd, Pi.smul_apply, RingHom.id_apply]
  left_inv := ofW_toW
  right_inv := toW_ofW

def blkLin (k : ℕ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : ((Fin k → ℂ) × ℂ) →ₗ[ℂ] ((Fin k → ℂ) × ℂ) :=
  (((wEquiv k).symm : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] ((Fin k → ℂ) × ℂ)) : (Fin (k + 1) → ℂ) →ₗ[ℂ] ((Fin k → ℂ) × ℂ)) ∘ₗ
    Matrix.toLin' μ ∘ₗ (((wEquiv k).symm.symm : ((Fin k → ℂ) × ℂ) ≃ₗ[ℂ] (Fin (k + 1) → ℂ)) :
      ((Fin k → ℂ) × ℂ) →ₗ[ℂ] (Fin (k + 1) → ℂ))

theorem blkLin_apply {k : ℕ} (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (p : (Fin k → ℂ) × ℂ) :
    blkLin k μ p = blkAct k μ p := by
  simp [blkLin, blkAct, wEquiv, Matrix.toLin'_apply]

theorem det_blkLin {k : ℕ} (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : LinearMap.det (blkLin k μ) = μ.det := by
  unfold blkLin
  rw [LinearMap.det_conj, LinearMap.det_toLin']

theorem normSq_det_hb {k : ℕ} {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μᴴ * Hb k * μ = Hb k) :
    Complex.normSq μ.det = 1 := by
  have h := congrArg Matrix.det hμ
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h
  have hb : (Hb k).det ≠ 0 := by
    unfold Hb
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun j _ => by split_ifs <;> norm_num
  have h2 : star μ.det * μ.det = 1 := by
    have e : (star μ.det * μ.det) * (Hb k).det = 1 * (Hb k).det := by
      rw [show (star μ.det * μ.det) * (Hb k).det = star μ.det * (Hb k).det * μ.det by ring, h, one_mul]
    exact mul_right_cancel₀ hb e
  have h3 : (Complex.normSq μ.det : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact h2
  exact_mod_cast h3

theorem lebInvB : LebInvB := by
  intro k μ hμ
  have h1 : (volume : Measure ℂ).IsAddHaarMeasure := inferInstance
  have h2 : (volume : Measure (Fin k → ℂ)).IsAddHaarMeasure := inferInstance
  have h3 : (volume : Measure ((Fin k → ℂ) × ℂ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  set f : ((Fin k → ℂ) × ℂ) →ₗ[ℝ] ((Fin k → ℂ) × ℂ) := (blkLin k μ).restrictScalars ℝ with hfdef
  have hdet : LinearMap.det f = 1 := by
    rw [hfdef, LinearMap.det_restrictScalars, det_blkLin, Algebra.norm_complex_apply, normSq_det_hb hμ]
  have hf : blkAct k μ = ⇑f := by
    funext p
    rw [hfdef, LinearMap.coe_restrictScalars, blkLin_apply]
  rw [hf, Measure.map_linearMap_addHaar_eq_smul_addHaar (μ := (volume : Measure ((Fin k → ℂ) × ℂ)))
    (by rw [hdet]; norm_num), hdet]
  simp

end PI.RhsWLim.W
end
end

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W

open PI.RhsWLim

def hq (k : ℕ) (T' : ℝ) (y : Fin k → ℂ) (θ : ℝ) : (Fin k → ℂ) × ℂ :=
  (y, (Real.sqrt (∑ i, Complex.normSq (y i) + T') : ℂ) * Complex.exp (θ * Complex.I))

def hqI (k : ℕ) (T' : ℝ) (E : Set ((Fin k → ℂ) × ℂ)) : ℝ≥0∞ :=
  ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, ∫⁻ y, E.indicator 1 (hq k T' y θ)

def HypTh : Prop :=
  ∀ (k : ℕ) (T' : ℝ), 0 < T' → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
    ∀ E, MeasurableSet E → hypM k T' E = c * hqI k T' E

def ConeVol : Prop :=
  ∀ (k : ℕ) (T' : ℝ), 0 < T' → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
    ∀ E, MeasurableSet E → volume (coneSh k T' E) = c * hqI k T' E

theorem coneForm_of (hH : HypTh) (hV : ConeVol) : ConeForm := by
  intro k T' hT'
  obtain ⟨c1, h10, h1t, h1⟩ := hH k T' hT'
  obtain ⟨c2, h20, h2t, h2⟩ := hV k T' hT'
  refine ⟨c1 / c2, ENNReal.div_pos h10 h2t |>.ne', ENNReal.div_ne_top h1t h20, fun E hE => ?_⟩
  rw [h1 E hE, h2 E hE, ← mul_assoc, ENNReal.div_mul_cancel h20 h2t]

end PI.RhsWLim.W
end
end

section

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace PI.RhsWLim.W.RI

open PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.ZetaZeros

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μW μW' : Measure (Mt k r)} {a a' : ℝ}
  {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}

def orbV (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (x : Mt k r) : Fin (2 * r + k + 1) → ℂ := Matrix.of x *ᵥ z'

def rmulM (b : Mat k r) (x : Mt k r) : Mt k r := fun i j => (Matrix.of x * b) i j

def DescUniq : Prop :=
  ∀ (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (μW' : Measure (Mt k r)), IsHaarOn (UWset k r z') μW' →
    μW' Set.univ ≠ ⊤ → ∀ ν₁ ν₂ : Measure (Mt k r), SigmaFinite ν₁ → SigmaFinite ν₂ →
    ν₁ {x | Matrix.of x ∉ UWb k r} = 0 → ν₂ {x | Matrix.of x ∉ UWb k r} = 0 →
    (∀ b ∈ UWset k r z', ν₁.map (rmulM b) = ν₁) → (∀ b ∈ UWset k r z', ν₂.map (rmulM b) = ν₂) →
    ν₁.map (orbV k r z') = ν₂.map (orbV k r z') → ν₁ = ν₂

def RInvNu : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∀ b ∈ UWset k r z',
      (nuR k r z z' μW μW' μsec).map (rmulM b) = nuR k r z z' μW μW' μsec

def OrbInv : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μW μW' : Measure (Mt k r)) (a a' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    WbData k r z z' μW μW' a a' μsec → ∀ s ∈ UWb k r, ∀ F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞, Measurable F →
      rhsW k r z z' μW μW' μsec (fun x => F (s *ᵥ orbV k r z' x)) =
        rhsW k r z z' μW μW' μsec (fun x => F (orbV k r z' x))

theorem orbV_cont (z' : Fin (2 * r + k + 1) → ℂ) : Continuous (orbV k r z') := by
  unfold orbV
  exact Continuous.matrix_mulVec (continuous_id' (X := Mt k r)) continuous_const

theorem rmulM_cont (b : Mat k r) : Continuous (rmulM b : Mt k r → Mt k r) := by
  unfold rmulM
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact (Continuous.matrix_mul (continuous_id' (X := Mt k r)) continuous_const).matrix_elem i j

def lmulE (s : Mat k r) (hs : IsUnit s.det) : Mt k r ≃ᵐ Mt k r where
  toFun := lmulM s
  invFun := lmulM s⁻¹
  left_inv x := Matrix.nonsing_inv_mul_cancel_left (A := s) (Matrix.of x) hs
  right_inv x := Matrix.mul_nonsing_inv_cancel_left (A := s) (Matrix.of x) hs
  measurable_toFun := (HU.lmulM_cont s).measurable
  measurable_invFun := (HU.lmulM_cont s⁻¹).measurable

theorem nu_conc (hD : WbData k r z z' μW μW' a a' μsec) :
    nuR k r z z' μW μW' μsec {x | Matrix.of x ∉ UWb k r} = 0 := by
  have := hD.haarW.1
  have := hD.haarW'.1
  rw [nuR, Measure.map_apply (meas_chartF hD.sec) (s := {x : Mt k r | Matrix.of x ∉ UWb k r})
    HU.amb_closed.isOpen_compl.measurableSet]
  apply measure_mono_null _ (src_null hD)
  intro q hq hg
  exact hq (mem_chart hD hg)

theorem rhsWInv_of (hD : DescUniq) (hR : RInvNu) (hO : OrbInv) : RhsWInv := by
  intro k r z z' μW μW' a a' μsec hd s hs φ hφ
  have := hd.haarW.1
  have := hd.haarW'.1
  have hσ : SigmaFinite (nuR k r z z' μW μW' μsec) := nu_sigmaFinite hd
  have hl : Measurable (lmulM s : Mt k r → Mt k r) := (HU.lmulM_cont s).measurable
  have hσ1 : SigmaFinite ((nuR k r z z' μW μW' μsec).map (lmulM s)) :=
    (lmulE s (HU.uwb_unit hs)).sigmaFinite_map
  have hC1 : ((nuR k r z z' μW μW' μsec).map (lmulM s)) {x | Matrix.of x ∉ UWb k r} = 0 := by
    rw [Measure.map_apply hl (s := {x : Mt k r | Matrix.of x ∉ UWb k r})
      HU.amb_closed.isOpen_compl.measurableSet]
    apply measure_mono_null _ (nu_conc hd)
    intro x hx hx'
    exact hx (HU.uwb_mul hs hx')
  have hR1 : ∀ b ∈ UWset k r z', ((nuR k r z z' μW μW' μsec).map (lmulM s)).map (rmulM b) =
      (nuR k r z z' μW μW' μsec).map (lmulM s) := by
    intro b hb
    have hr : Measurable (rmulM b : Mt k r → Mt k r) := (rmulM_cont b).measurable
    have e : rmulM b ∘ lmulM s = lmulM s ∘ rmulM b := by
      funext x
      show (s * Matrix.of x * b : Mat k r) = s * (Matrix.of x * b)
      exact Matrix.mul_assoc _ _ _
    rw [Measure.map_map hr hl, e, ← Measure.map_map hl hr, hR k r z z' μW μW' a a' μsec hd b hb]
  have hO1 : ((nuR k r z z' μW μW' μsec).map (lmulM s)).map (orbV k r z') =
      (nuR k r z z' μW μW' μsec).map (orbV k r z') := by
    have ho : Measurable (orbV k r z') := (orbV_cont z').measurable
    ext A hA
    rw [Measure.map_map ho hl, Measure.map_apply (ho.comp hl) hA, Measure.map_apply ho hA,
      ← lintegral_indicator_one ((ho.comp hl) hA), ← lintegral_indicator_one (ho hA)]
    have e1 : ((orbV k r z' ∘ lmulM s) ⁻¹' A).indicator (1 : Mt k r → ℝ≥0∞) =
        fun x => A.indicator 1 (s *ᵥ orbV k r z' x) := by
      funext x
      show ((orbV k r z' ∘ lmulM s) ⁻¹' A).indicator 1 x = A.indicator 1 (s *ᵥ (Matrix.of x *ᵥ z'))
      rw [Matrix.mulVec_mulVec]
      rfl
    have e2 : (orbV k r z' ⁻¹' A).indicator (1 : Mt k r → ℝ≥0∞) = fun x => A.indicator 1 (orbV k r z' x) := by
      funext x
      rfl
    have hF : Measurable (A.indicator (1 : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞)) := measurable_one.indicator hA
    rw [e1, e2, ← repr hd (fun x => A.indicator 1 (s *ᵥ orbV k r z' x))
        (hF.comp ((continuous_const.matrix_mulVec continuous_id).measurable.comp ho)),
      ← repr hd (fun x => A.indicator 1 (orbV k r z' x)) (hF.comp ho), hO k r z z' μW μW' a a' μsec hd s hs _ hF]
  have key := hD k r z' μW' hd.haarW' (by rw [hd.massW']; exact ENNReal.ofReal_ne_top) _ _ hσ1 hσ hC1
    (nu_conc hd) hR1 (hR k r z z' μW μW' a a' μsec hd) hO1
  rw [repr hd (fun x => φ (lmulM s x)) (hφ.comp hl), repr hd _ hφ, ← lintegral_map hφ hl, key]

end PI.RhsWLim.W.RI
end
end
