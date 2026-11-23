module

public import GroundTheory.AutomorphicForms.GL2Classical.Adelic
public import GroundTheory.AutomorphicForms.GL2Classical.Iwasawa
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.NumberTheory.ModularForms.SlashActions

@[expose] public section

section

open NumberField IsDedekindDomain Matrix Set Filter Topology
open UpperHalfPlane hiding I I_re I_im
open scoped NumberField.AdeleRing MatrixGroups

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm GroundTheory.Global

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem realPart_orthogonal {x : AdelicGL ℚ 2} (hx : x ∈ Reduction.maxCompact) :
    realPart x 0 0 ^ 2 + realPart x 0 1 ^ 2 = 1 ∧ realPart x 1 0 ^ 2 + realPart x 1 1 ^ 2 = 1 ∧
      realPart x 0 0 * realPart x 1 0 + realPart x 0 1 * realPart x 1 1 = 0 := by
  set w0 : InfinitePlace ℚ := default
  have hw0 := RationalIdeles.isReal_infinitePlace w0
  have hn := (Reduction.mem_maxCompact.1 hx).1 w0
  rw [Reduction.mem_archCompact] at hn
  set M : Matrix (Fin 2) (Fin 2) w0.Completion :=
    ((Reduction.infAt w0 x : GL (Fin 2) w0.Completion) : Matrix (Fin 2) (Fin 2) w0.Completion)
  set e := InfinitePlace.Completion.ringEquivRealOfIsReal hw0
  have hE : ∀ a b, realPart x a b = e (M a b) := fun a b => rfl
  have hEn : ∀ z, ‖e z‖ = ‖z‖ := fun z =>
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw0).norm_map_of_map_zero
      (map_zero _) z
  have key : ∀ y0 y1 : ℝ, (y0 * realPart x 0 0 + y1 * realPart x 1 0) ^ 2 +
      (y0 * realPart x 0 1 + y1 * realPart x 1 1) ^ 2 = y0 ^ 2 + y1 ^ 2 := by
    intro y0 y1
    have h := hn ![e.symm y0, e.symm y1]
    simp only [Reduction.euclidNorm, Fin.sum_univ_two, Matrix.vecMul, dotProduct,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h
    have hy : ∀ (y : ℝ) (z : w0.Completion), ‖e.symm y * z‖ = |y| * ‖e z‖ := by
      intro y z
      rw [norm_mul, hEn, ← hEn (e.symm y), RingEquiv.apply_symm_apply, Real.norm_eq_abs]
    have hsum : ∀ j : Fin 2, ‖e.symm y0 * M 0 j + e.symm y1 * M 1 j‖ =
        |y0 * realPart x 0 j + y1 * realPart x 1 j| := by
      intro j
      rw [← hEn, map_add (f := _), map_mul, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply,
        hE, hE, Real.norm_eq_abs]
    have hy0 : ‖e.symm y0‖ = |y0| := by rw [← hEn, RingEquiv.apply_symm_apply, Real.norm_eq_abs]
    have hy1 : ‖e.symm y1‖ = |y1| := by rw [← hEn, RingEquiv.apply_symm_apply, Real.norm_eq_abs]
    rw [hsum 0, hsum 1, hy0, hy1, sq_abs, sq_abs, sq_abs, sq_abs] at h
    have := congrArg (· ^ 2) h
    rwa [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at this
  have k10 := key 1 0
  have k01 := key 0 1
  have k11 := key 1 1
  refine ⟨by linear_combination k10, by linear_combination k01, ?_⟩
  linear_combination (k11 - k10 - k01) / 2


end GL2Classical

end

end GroundTheory.Automorphic
end

section

open NumberField Matrix CongruenceSubgroup UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

variable {N : ℕ} (k : ℤ)

theorem σ_of_det_pos {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) (z : ℂ) : σ h z = z := by
  rw [σ, if_pos hpos]
  rfl

theorem denom_mul_of_det_pos (g : GL (Fin 2) ℝ) {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) (z : ℍ) :
    denom (g * h) z = denom g ((h • z : ℍ) : ℂ) * denom h z := by
  rw [denom_cocycle_σ, σ_of_det_pos hpos]

theorem sqrt_div_normSq {a : ℝ} (w : ℂ) :
    Real.sqrt (a / Complex.normSq w) = Real.sqrt a / ‖w‖ := by
  rw [Real.sqrt_div' _ (Complex.normSq_nonneg w), Complex.normSq_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg w)]

theorem div_norm_zpow_neg (w : ℂ) : (w / (‖w‖ : ℂ)) ^ (-k) = w ^ (-k) * (‖w‖ : ℂ) ^ k := by
  rw [div_eq_mul_inv, mul_zpow, _root_.inv_zpow', neg_neg]

def archLift (f : ℍ → ℂ) (h : GL (Fin 2) ℝ) : ℂ :=
  (Real.sqrt h.det.val : ℂ) ^ k * f (h • I) * denom h (I : ℂ) ^ (-k)

theorem archLift_mul_kGL (f : ℍ → ℂ) {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val) (w : ℂ)
    (hw : w ≠ 0) :
    archLift k f (h * kGL w hw) = (w / (‖w‖ : ℂ)) ^ (-k) * archLift k f h := by
  have hdet : (h * kGL w hw).det.val = h.det.val * Complex.normSq w := by
    rw [map_mul, Units.val_mul, det_kGL]
  have hsq : Real.sqrt (h.det.val * Complex.normSq w) = Real.sqrt h.det.val * ‖w‖ := by
    rw [Real.sqrt_mul hpos.le, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg w)]
  rw [archLift, archLift, hdet, hsq, mul_smul, kGL_smul_I, denom_mul_of_det_pos _ (det_kGL_pos w hw),
    kGL_smul_I, denom_kGL, div_norm_zpow_neg, Complex.ofReal_mul, mul_zpow, mul_zpow]
  ring

theorem archLift_borelGL (f : ℍ → ℂ) (z : ℍ) :
    archLift k f (borelGL z) = (Real.sqrt z.im : ℂ) ^ k * f z := by
  rw [archLift, det_borelGL, borelGL_smul_I, denom_borelGL, _root_.one_zpow, mul_one]

variable (N) [NeZero N]

def decompGL (g : AdelicGL ℚ 2) : GL (Fin 2) ℝ :=
  Classical.choose (Classical.choose_spec (exists_decomposition N g))

theorem decompGL_spec (g : AdelicGL ℚ 2) :
    0 < (decompGL N g).det.val ∧ ∃ γ : GL (Fin 2) ℚ, ∃ u ∈ Gamma0Level N,
      g = diagonal ℚ 2 γ * realEmb (decompGL N g) * finEmb ℚ 2 u :=
  ⟨(Classical.choose_spec (Classical.choose_spec (exists_decomposition N g))).1,
    Classical.choose (exists_decomposition N g),
    (Classical.choose_spec (Classical.choose_spec (exists_decomposition N g))).2⟩

variable {N k}

variable (N k)

variable {N k}

variable (k)

variable {k}

variable (N k)

variable {N k}

end GL2Classical

end

end GroundTheory.Automorphic
end
