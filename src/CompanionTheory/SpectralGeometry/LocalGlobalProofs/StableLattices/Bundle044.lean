module

public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.DecompositionOfTrace
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSecondOrder.HasDerivAtDOf
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle039
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.HaarExists
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.KeepsMul
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ParabolicSubgroupEquality
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.Bundle001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle041
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle042
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

theorem _root_.GlobalTheory.T.tensHom' : TensHom := by
  first | exact @GlobalTheory.CompanionTheory.ZuckTensHom.tensHom | exact GlobalTheory.CompanionTheory.ZuckTensHom.tensHom | (intros; apply GlobalTheory.CompanionTheory.ZuckTensHom.tensHom <;> assumption)
end

section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

theorem _root_.GlobalTheory.T.DecompositionOfTrace : DecOfTrace := by
  first | exact @GlobalTheory.CompanionTheory.ZuckDecOfTrace.decOfTrace | exact GlobalTheory.CompanionTheory.ZuckDecOfTrace.decOfTrace | (intros; apply GlobalTheory.CompanionTheory.ZuckDecOfTrace.decOfTrace <;> assumption)
end

section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.ZuckStdD

theorem dR_std (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (vr k r false).dR X = X := by
  ext c d
  exact (PI.ComplexConjugateDerivative.exp_entry X c d).deriv

theorem dR_dual (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    (vr k r true).dR X = -Xᵀ := by
  ext c d
  have h := (PI.ComplexConjugateDerivative.exp_entry (-X) d c).deriv
  have e : (fun t : ℝ => (vr k r true).ρ (NormedSpace.exp ((t : ℂ) • X)) c d) =
      fun t : ℝ => (NormedSpace.exp ((t : ℂ) • (-X))) d c := by
    funext t
    rw [smul_neg, Matrix.exp_neg]
    simp [dualM]
  show deriv (fun t : ℝ => (vr k r true).ρ (NormedSpace.exp ((t : ℂ) • X)) c d) 0 = _
  rw [e, h]
  rfl

theorem reH_add_imH (k r : ℕ) (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    reH k r Y + Complex.I • imH k r Y = Y := by
  unfold reH imH
  have hI : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by
    have := Complex.I_ne_zero
    field_simp
  rw [smul_smul, hI, ← smul_add]
  have : ∀ Z : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Y + Z + (Y - Z) = (2 : ℂ) • Y := by
    intro Z; rw [two_smul]; abel
  rw [this, smul_smul]
  norm_num

theorem stdD : StdD := by
  intro k r Y
  constructor
  · unfold FRep.dC
    rw [dR_std, dR_std]
    exact reH_add_imH k r Y
  · unfold FRep.dC
    rw [dR_dual, dR_dual]
    conv_rhs => rw [← reH_add_imH k r Y]
    rw [Matrix.transpose_add, Matrix.transpose_smul, neg_add, smul_neg]

end GlobalTheory.CompanionTheory.ZuckStdD
end

section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.WedgeDeriv

theorem hasDerivAt_det {m : ℕ} (A : ℝ → Matrix (Fin m) (Fin m) ℂ) (A' : Matrix (Fin m) (Fin m) ℂ)
    (h : ∀ i j, HasDerivAt (fun t => A t i j) (A' i j) 0) :
    HasDerivAt (fun t => (A t).det) (∑ j, ∑ i, adjugate (A 0) j i * A' i j) 0 := by
  have h1 : HasDerivAt (fun t => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i)
      (∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ j, (∏ i ∈ univ.erase j, A 0 (σ i) i) • A' (σ j) j) 0 := by
    refine HasDerivAt.fun_sum fun σ _ => HasDerivAt.const_mul _ ?_
    exact HasDerivAt.fun_finsetProd (f := fun i t => A t (σ i) i) fun i _ => h _ _
  have h2 : ∀ j, ∑ i, adjugate (A 0) j i * A' i j = ((A 0).updateCol j fun i => A' i j).det := by
    intro j
    rw [← cramer_apply, cramer_eq_adjugate_mulVec]
    rfl
  simp only [h2, Matrix.det_apply']
  convert h1 using 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [← Finset.prod_erase_mul _ _ (mem_univ j), updateCol_self, smul_eq_mul]
  congr 1
  exact Finset.prod_congr rfl fun i hi => updateCol_ne (ne_of_mem_erase hi)

theorem det_one_submatrix {m n : ℕ} (f g : Fin m → Fin n) (hf : StrictMono f) (hg : StrictMono g) :
    ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix f g).det = if univ.image f = univ.image g then 1 else 0 := by
  split_ifs with h
  · have : f = g := by
      refine (hf.range_inj hg).1 ?_
      have := congrArg (fun s : Finset (Fin n) => (s : Set (Fin n))) h
      simpa using this
    subst this
    rw [submatrix_one _ hf.injective, det_one]
  · have : ∃ i, f i ∉ univ.image g := by
      by_contra hc
      push Not at hc
      apply h
      refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
      · obtain ⟨i, _, rfl⟩ := mem_image.1 hx
        exact hc i
      · rw [card_image_of_injective _ hf.injective, card_image_of_injective _ hg.injective]
    obtain ⟨i, hi⟩ := this
    refine det_eq_zero_of_row_eq_zero i fun j => ?_
    rw [submatrix_apply, one_apply_ne]
    intro he
    exact hi (mem_image.2 ⟨j, mem_univ _, he.symm⟩)

theorem card_filter_lt {m n : ℕ} (f : Fin m → Fin n) (hf : StrictMono f) (i : Fin m) :
    (((univ.image f).erase (f i)).filter fun c => c < f i).card = i := by
  have : (((univ.image f).erase (f i)).filter fun c => c < f i) = (Iio i).image f := by
    ext x
    simp only [mem_filter, mem_erase, mem_image, mem_univ, true_and, mem_Iio]
    constructor
    · rintro ⟨⟨_, j, rfl⟩, h⟩
      exact ⟨j, hf.lt_iff_lt.1 h, rfl⟩
    · rintro ⟨j, h, rfl⟩
      exact ⟨⟨(hf h).ne, j, rfl⟩, hf h⟩
  rw [this, card_image_of_injective _ hf.injective, Fin.card_Iio]

theorem image_succAbove {m n : ℕ} (f : Fin (m + 1) → Fin n) (hf : StrictMono f) (i : Fin (m + 1)) :
    univ.image (f ∘ i.succAbove) = (univ.image f).erase (f i) := by
  ext x
  simp only [mem_erase, mem_image, mem_univ, true_and, Function.comp]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨fun h => Fin.succAbove_ne _ _ (hf.injective h), _, rfl⟩
  · rintro ⟨h, j, rfl⟩
    obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq (x := j) (y := i) (fun e => h (by rw [e]))
    exact ⟨l, rfl⟩

theorem sum_adj {m n : ℕ} (f g : Fin m → Fin n) (hf : StrictMono f) (hg : StrictMono g) (a b : Fin n) :
    ∑ j, ∑ i, adjugate ((1 : Matrix (Fin n) (Fin n) ℂ).submatrix f g) j i *
      (Matrix.single a b (1 : ℂ)) (f i) (g j) =
    if b ∈ univ.image g ∧ a ∉ (univ.image g).erase b ∧ univ.image f = insert a ((univ.image g).erase b) then
      (-1) ^ (((univ.image g).erase b).filter fun c => c < a).card *
        (-1) ^ (((univ.image g).erase b).filter fun c => c < b).card else 0 := by
  by_cases hb : b ∈ univ.image g
  swap
  · rw [if_neg (fun h => hb h.1)]
    refine sum_eq_zero fun j _ => sum_eq_zero fun i _ => ?_
    rw [single_apply_of_ne, mul_zero]
    rintro ⟨_, rfl⟩
    exact hb (mem_image_of_mem _ (mem_univ _))
  by_cases ha : a ∈ univ.image f
  swap
  · rw [if_neg (by rintro ⟨_, _, h⟩; exact ha (h ▸ mem_insert_self _ _))]
    refine sum_eq_zero fun j _ => sum_eq_zero fun i _ => ?_
    rw [single_apply_of_ne, mul_zero]
    rintro ⟨rfl, _⟩
    exact ha (mem_image_of_mem _ (mem_univ _))
  obtain ⟨j, _, rfl⟩ := mem_image.1 hb
  obtain ⟨i, _, rfl⟩ := mem_image.1 ha
  rw [sum_eq_single j, sum_eq_single i, single_apply_same, mul_one]
  · obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := i.pos; omega⟩
    rw [adjugate_fin_succ_eq_det_submatrix, submatrix_submatrix,
      det_one_submatrix _ _ (hf.comp (Fin.strictMono_succAbove i)) (hg.comp (Fin.strictMono_succAbove j)),
      image_succAbove f hf, image_succAbove g hg]
    by_cases h : (univ.image f).erase (f i) = (univ.image g).erase (g j)
    · rw [if_pos h, if_pos, card_filter_lt g hg, ← h, card_filter_lt f hf, mul_one, pow_add]
      refine ⟨hb, ?_, ?_⟩
      · rw [← h]; exact notMem_erase _ _
      · rw [← h, insert_erase ha]
    · rw [if_neg h, if_neg, mul_zero]
      rintro ⟨_, h1, h2⟩
      apply h
      rw [h2, erase_insert h1]
  · intro i' _ hi
    rw [single_apply_of_ne, mul_zero]
    exact fun h => hi (hf.injective h.1).symm
  · simp
  · intro j' _ hj
    refine sum_eq_zero fun i _ => ?_
    rw [single_apply_of_ne, mul_zero]
    exact fun h => hj (hg.injective h.2).symm
  · simp

theorem dR_wedge (k r m : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (J J' : Sub (2 * r + k + 1) m) :
    (wedge k r m).dR X J J' = ∑ j, ∑ i, adjugate ((1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ).submatrix (J.1.orderEmbOfFin J.2)
      (J'.1.orderEmbOfFin J'.2)) j i * X (J.1.orderEmbOfFin J.2 i) (J'.1.orderEmbOfFin J'.2 j) := by
  have h := hasDerivAt_det (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)).submatrix (J.1.orderEmbOfFin J.2)
      (J'.1.orderEmbOfFin J'.2)) (X.submatrix (J.1.orderEmbOfFin J.2) (J'.1.orderEmbOfFin J'.2))
      fun i j => PI.ComplexConjugateDerivative.exp_entry X _ _
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, submatrix_apply] at h
  exact h.deriv

theorem reH_add_imH (k r : ℕ) (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : reH k r Y + Complex.I • imH k r Y = Y := by
  have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  rw [reH, imH, smul_smul, this, ← smul_add]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  ring

theorem dC_wedge_single : ∀ (k r m : ℕ) (a b : Fin (2 * r + k + 1)) (J J' : Sub (2 * r + k + 1) m), (wedge k r m).dC (Matrix.single a b 1) J J' = if b ∈ J'.1 ∧ a ∉ J'.1.erase b ∧ J.1 = insert a (J'.1.erase b) then (-1) ^ ((J'.1.erase b).filter fun c => c < a).card * (-1) ^ ((J'.1.erase b).filter fun c => c < b).card else 0 := by
  intro k r m a b J J'
  have h := sum_adj _ _ (J.1.orderEmbOfFin J.2).strictMono (J'.1.orderEmbOfFin J'.2).strictMono a b
  rw [Finset.image_orderEmbOfFin_univ, Finset.image_orderEmbOfFin_univ] at h
  rw [← h, FRep.dC, Matrix.add_apply, Matrix.smul_apply, dR_wedge, dR_wedge, smul_eq_mul, mul_sum,
    ← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← reH_add_imH k r (Matrix.single a b 1)]
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.WedgeDeriv
end

section


theorem _root_.GlobalTheory.T.OmegaScalar : CompanionTheory.RgExh.Hk.OmScal := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.omScal | exact GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.omScal | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.omScal <;> assumption)
end

section

noncomputable section

open Finset MeasureTheory Matrix
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.PathGrowth

open _root_.CompanionTheory.RgExh _root_.CompanionTheory.RgExh.Dec _root_.CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def Lev (ε : Fin n → Bool) (m : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  (Continuous fun g : S7.UJ ε => f (S7.toM g)) ∧ LevelF ε f (-(m : ℝ))

theorem hs_nonneg (h : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ Formalism.REAL.hs h :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem row_le_hs (h : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : ∑ i, ‖h j i‖ ^ 2 ≤ Formalism.REAL.hs h :=
  Finset.single_le_sum (f := fun a => ∑ i, ‖h a i‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)

theorem row_cs (h : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) (a : Fin n → ℂ) :
    ‖∑ i, h j i * a i‖ ^ 2 ≤ Formalism.REAL.hs h * ∑ i, ‖a i‖ ^ 2 := by
  have h1 : ‖∑ i, h j i * a i‖ ≤ ∑ i, ‖h j i‖ * ‖a i‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun _ _ => norm_mul _ _))
  have h2 : (∑ i, ‖h j i‖ * ‖a i‖) ^ 2 ≤ (∑ i, ‖h j i‖ ^ 2) * ∑ i, ‖a i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ‖∑ i, h j i * a i‖ ^ 2 ≤ (∑ i, ‖h j i‖ * ‖a i‖) ^ 2 := by gcongr
    _ ≤ (∑ i, ‖h j i‖ ^ 2) * ∑ i, ‖a i‖ ^ 2 := h2
    _ ≤ Formalism.REAL.hs h * ∑ i, ‖a i‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (row_le_hs h j) (Finset.sum_nonneg fun _ _ => by positivity)

theorem row_bound (h : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) (a : Fin n → ℂ) (m : ℕ) :
    ‖∑ i, h j i * a i‖ ^ 2 * Formalism.REAL.hs h ^ (-((m + 1 : ℕ) : ℝ)) ≤
      ∑ i, ‖a i‖ ^ 2 * Formalism.REAL.hs h ^ (-(m : ℝ)) := by
  have hs0 := hs_nonneg h
  have hT : 0 ≤ ∑ i, ‖a i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hcs := row_cs h j a
  rw [← Finset.sum_mul]
  rcases hs0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul] at hcs
    have hz : ‖∑ i, h j i * a i‖ ^ 2 = 0 := le_antisymm hcs (by positivity)
    rw [hz, zero_mul]
    exact mul_nonneg hT (Real.rpow_nonneg hs0 _)
  · have e : Formalism.REAL.hs h ^ (-((m + 1 : ℕ) : ℝ)) = Formalism.REAL.hs h ^ (-(m : ℝ)) * (Formalism.REAL.hs h)⁻¹ := by
      rw [Nat.cast_add, Nat.cast_one, neg_add, Real.rpow_add hpos, Real.rpow_neg_one]
    rw [e]
    calc ‖∑ i, h j i * a i‖ ^ 2 * (Formalism.REAL.hs h ^ (-(m : ℝ)) * (Formalism.REAL.hs h)⁻¹)
        ≤ (Formalism.REAL.hs h * ∑ i, ‖a i‖ ^ 2) * (Formalism.REAL.hs h ^ (-(m : ℝ)) * (Formalism.REAL.hs h)⁻¹) :=
          mul_le_mul_of_nonneg_right hcs (by positivity)
      _ = (∑ i, ‖a i‖ ^ 2) * Formalism.REAL.hs h ^ (-(m : ℝ)) := by
          field_simp

theorem enorm_sq_mul (x : ℂ) (r : ℝ) :
    ‖x‖ₑ ^ 2 * ENNReal.ofReal r = ENNReal.ofReal (‖x‖ ^ 2 * r) := by
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem continuous_hs (ε : Fin n → Bool) : Continuous fun g : S7.UJ ε => Formalism.REAL.hs (S7.toM g) := by
  unfold Formalism.REAL.hs
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  exact (((S7.continuous_toM ε).matrix_elem i j).norm).pow 2

theorem measurable_term (ε : Fin n → Bool) {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (s : ℝ)
    (hf : Continuous fun g : S7.UJ ε => f (S7.toM g)) :
    Measurable fun g : S7.UJ ε => ‖f (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ s) :=
  (hf.measurable.enorm.pow_const 2).mul
    (ENNReal.measurable_ofReal.comp ((continuous_hs ε).measurable.pow_const s))

theorem lev_row (ε : Fin n → Bool) (m : ℕ) (f : Fin n → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hf : ∀ i, Lev ε m (f i)) (j : Fin n) : Lev ε (m + 1) fun g => ∑ i, g j i * f i g := by
  refine ⟨continuous_finsetSum _ fun i _ =>
    ((S7.continuous_toM ε).matrix_elem j i).mul (hf i).1, ?_⟩
  unfold LevelF
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) (b := ∫⁻ g : S7.UJ ε, ∑ i,
    ‖f i (S7.toM g)‖ₑ ^ 2 * ENNReal.ofReal (Formalism.REAL.hs (S7.toM g) ^ (-(m : ℝ))) ∂Measure.haar) ?_
  · have hr := fun k : ℝ => Real.rpow_nonneg (hs_nonneg (S7.toM g)) k
    simp only [enorm_sq_mul]
    rw [← ENNReal.ofReal_sum_of_nonneg fun _ _ => mul_nonneg (by positivity) (hr _)]
    exact ENNReal.ofReal_le_ofReal (row_bound _ j _ m)
  · rw [lintegral_finsetSum _ fun i _ => measurable_term ε _ (hf i).1]
    exact ENNReal.sum_lt_top.2 fun i _ => (hf i).2

theorem level_zero_of_memLp (ε : Fin n → Bool) (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)) :
    ∫⁻ g : S7.UJ ε, ‖F (S7.toM g)‖ₑ ^ 2 ∂Measure.haar < ⊤ := by
  let μ : Measure (S7.UJ ε) := Formalism.REAL.muG ε
  haveI : μ.IsHaarMeasure := Formalism.REAL.instIsHaarMuG n ε
  have h' : MemLp (fun g : S7.UJ ε => F (S7.toM g)) 2 μ := h
  have h2 : ∫⁻ g : S7.UJ ε, ‖F (S7.toM g)‖ₑ ^ 2 ∂μ < ⊤ := by
    simpa only [ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top
        (p := 2) two_ne_zero ENNReal.ofNat_ne_top h'.eLpNorm_lt_top
  rw [Measure.isMulLeftInvariant_eq_smul (Measure.haar : Measure (S7.UJ ε)) μ, lintegral_smul_measure]
  exact ENNReal.mul_lt_top (by simp) h2

theorem lev_base (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (D : Submodule ℂ H) (ξ : H)
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (hsq : Formalism.MainNotions.S.IsSqIntOn ε σ) (u : D) :
    Lev ε 0 (baseCoef σ D ξ u) := by
  constructor
  · have h1 : Continuous fun g : S7.UJ ε => σ (S7.toM g) (u : H) :=
      (hσ.2.2 (u : H)).comp_continuous (S7.continuous_toM ε) fun g => g.2
    exact continuous_const.inner h1
  · unfold LevelF
    have := level_zero_of_memLp ε (baseCoef σ D ξ u) (hsq (u : H) ξ)
    simpa using this

theorem lev_path (ε : Fin n → Bool) : ∀ (ss : List (Fin n)) (X : GMod n)
    (c : X.V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (χ : Fin n → ℂ) (js : List (Fin n)) (m : ℕ),
    (∀ u, Lev ε m (c u)) → ∀ u, Lev ε (m + ss.length) (pathCoef X c χ ss js u)
  | [], _, _, _, _, _, h, u => h u
  | s :: ss, X, c, χ, js, m, h, u => by
    have key := lev_path ε ss (step X (χ s)) (stepCoef X (χ s) c (js.headD s)) (χ + Pi.single s 1) js.tail (m + 1)
      (fun w => lev_row ε m (fun i => c ((show stepSub X (χ s) from w).1 i)) (fun i => h _) (js.headD s)) u
    rw [show m + (s :: ss).length = m + 1 + ss.length by simp only [List.length_cons]; omega]
    exact key

theorem growth : Growth := by
  intro n ε H _ _ _ σ D E hK χ ss hσ hsq
  refine ⟨(ss.length : ℝ), fun i u => ?_⟩
  have key := lev_path ε ss ⟨D, E, hK.gl⟩ (baseCoef σ D (i.1 : H)) χ i.2 0
    (fun u => lev_base ε σ D _ hσ hsq u) u
  rw [zero_add] at key
  exact key.2

end GlobalTheory.CompanionTheory.PathGrowth
end
end

section

noncomputable section

open Matrix
open CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag

namespace GlobalTheory.CompanionTheory.UGeo

theorem mem_KG_of_mem_maxK {n : ℕ} {ε : Fin n → Bool} {k : S7.UJ ε} (hk : k ∈ GlobalTheory.FlagMeas.maxK ε) :
    k ∈ S7.KG ε := by
  have h1 : (Formalism.MainNotions.S.uMat k)ᴴ * Formalism.MainNotions.S.uMat k = 1 := hk
  have h2 : Formalism.MainNotions.S.uMat k * (Formalism.MainNotions.S.uMat k)ᴴ = 1 := mul_eq_one_comm.1 h1
  have h3 : (Formalism.MainNotions.S.uMat k)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat k = Formalism.REAL.Jm ε :=
    GlobalTheory.RealIwasawa.uMat_form k
  have h4 : Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat k = Formalism.MainNotions.S.uMat k * Formalism.REAL.Jm ε := by
    calc Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat k
        = (Formalism.MainNotions.S.uMat k * (Formalism.MainNotions.S.uMat k)ᴴ) * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat k := by
          rw [h2, Matrix.one_mul]
      _ = Formalism.MainNotions.S.uMat k * ((Formalism.MainNotions.S.uMat k)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat k) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.MainNotions.S.uMat k * Formalism.REAL.Jm ε := by rw [h3]
  refine ⟨Unitary.mem_iff.2 ⟨h1, h2⟩, ?_⟩
  exact h4.symm

theorem exists_psub_mul_maxK {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsGrad ε A)
    (g : Formalism.REAL.UJ ε) : ∃ p : Formalism.REAL.UJ ε, p ∈ PSub ε A ∧ ∃ k ∈ GlobalTheory.FlagMeas.maxK ε, g = p * k := by
  obtain ⟨k, hk, hp⟩ := GlobalTheory.RealIwasawa.exists_stab_mul_compact (isoFlag hA) g
  obtain ⟨m, hm, hu⟩ := GlobalTheory.RealIwasawa.exists_unip_mul_levi (isoFlag hA) _ hp
  exact ⟨g * k⁻¹, (psubEq n ε A hA _).2 ⟨_, hu, m, hm, by group⟩, k, hk, by group⟩

theorem iwasawa_psub : ∀ (n : ℕ) (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ), IsGrad ε A →
    ∀ g : S7.UJ ε, ∃ (x : PSub ε A) (k : S7.KG ε), g = (x : S7.UJ ε) * (k : S7.UJ ε) := by
  intro n ε A hA g
  obtain ⟨p, hp, k, hk, e⟩ := exists_psub_mul_maxK (A := A) hA g
  exact ⟨⟨p, hp⟩, ⟨k, mem_KG_of_mem_maxK hk⟩, e⟩

end GlobalTheory.CompanionTheory.UGeo
end
end

section


theorem _root_.GlobalTheory.T.rgExh_flagFacts : CompanionTheory.RgExh.Dec.N.S.FlagFacts := by
  first | exact @GlobalTheory.CompanionTheory.GradFlag.flagFacts | exact GlobalTheory.CompanionTheory.GradFlag.flagFacts | (intros; apply GlobalTheory.CompanionTheory.GradFlag.flagFacts <;> assumption)
end

section


theorem _root_.GlobalTheory.T.NilpotentOdeFirst : CompanionTheory.RgExh.Dec.N.OdeA := by
  first | exact @GlobalTheory.CompanionTheory.OdeRoots.odeA | exact GlobalTheory.CompanionTheory.OdeRoots.odeA | (intros; apply GlobalTheory.CompanionTheory.OdeRoots.odeA <;> assumption)
end

section


theorem _root_.GlobalTheory.T.NilpotentRightRule : CompanionTheory.RgExh.Dec.N.RightRule := by
  first | exact @GlobalTheory.CompanionTheory.RightRule.rightRule | exact GlobalTheory.CompanionTheory.RightRule.rightRule | (intros; apply GlobalTheory.CompanionTheory.RightRule.rightRule <;> assumption)
end

section


theorem _root_.GlobalTheory.T.InitialStatement : CompanionTheory.RgExh.Dec.N.S.StartOf := by
  first | exact @GlobalTheory.CompanionTheory.RgStart.startOf | exact GlobalTheory.CompanionTheory.RgStart.startOf | (intros; apply GlobalTheory.CompanionTheory.RgStart.startOf <;> assumption)
end
