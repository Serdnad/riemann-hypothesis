module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section

section

namespace GlobalTheory.CompanionTheory.Strip

theorem strip_open_real_discs (n : ℕ) (X : Fin n → ℝ) :
    IsOpen {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} ∧
    (∀ t : ℝ, (t : ℂ) ∈ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4}) ∧
    ∀ z ∈ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4}, ∃ (t ρ : ℝ), 0 < ρ ∧
      z ∈ Metric.ball (t : ℂ) ρ ∧
      Metric.ball (t : ℂ) ρ ⊆ {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} := by
  set S := {z : ℂ | ∀ j, |z.im * X j| < Real.pi / 4} with hS
  have hpi : 0 < Real.pi / 4 := by positivity
  refine ⟨?_, ?_, ?_⟩
  · have h : S = ⋂ j, {z : ℂ | |z.im * X j| < Real.pi / 4} := by
      ext z
      simp [hS]
    rw [h]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
  · intro t
    simp [hS, hpi]
  · intro z hz
    have hopen : IsOpen {r : ℝ | ∀ j, r * |X j| < Real.pi / 4} := by
      have h : {r : ℝ | ∀ j, r * |X j| < Real.pi / 4} = ⋂ j, {r : ℝ | r * |X j| < Real.pi / 4} := by
        ext r
        simp
      rw [h]
      exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
    have hmem : |z.im| ∈ {r : ℝ | ∀ j, r * |X j| < Real.pi / 4} := by
      intro j
      have h := hz j
      rwa [abs_mul] at h
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen _ hmem
    refine ⟨z.re, |z.im| + ε / 2, by positivity, ?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq]
      have h : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
        apply Complex.ext <;> simp
      rw [h, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      linarith
    · intro w hw j
      rw [Metric.mem_ball, Complex.dist_eq] at hw
      have him : |w.im| < |z.im| + ε / 2 := by
        have h1 : |(w - (z.re : ℂ)).im| ≤ ‖w - (z.re : ℂ)‖ := Complex.abs_im_le_norm _
        simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h1
        linarith
      have hρ : (|z.im| + ε / 2) * |X j| < Real.pi / 4 := by
        have hin : |z.im| + ε / 2 ∈ Metric.ball |z.im| ε := by
          rw [Metric.mem_ball, Real.dist_eq, show |z.im| + ε / 2 - |z.im| = ε / 2 by ring,
            abs_of_pos (by positivity)]
          linarith
        exact hball hin j
      show |w.im * X j| < Real.pi / 4
      rw [abs_mul]
      calc |w.im| * |X j| ≤ (|z.im| + ε / 2) * |X j| :=
            mul_le_mul_of_nonneg_right him.le (abs_nonneg _)
        _ < Real.pi / 4 := hρ

end GlobalTheory.CompanionTheory.Strip
end

section

open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.AdmGL

variable {ι : Type} [Fintype ι] [DecidableEq ι] {a n : ℕ}

def atPlace (M : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) : Matrix (Fin a) (Fin a) ℂ :=
  M.map fun x => x w

def blk (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.reindex e e (blockDiagonal (atPlace M))

def unblk (e : Fin a × ι ≃ Fin n) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin a) (Fin a) (ι → ℂ) :=
  Matrix.of fun p q w => g (e (p, w)) (e (q, w))

def blkG (e : Fin a × ι ≃ Fin n) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  blk e '' {M | IsUnit M}

theorem blk_apply (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) (i j : Fin n) :
    blk e M i j = if (e.symm i).2 = (e.symm j).2 then M (e.symm i).1 (e.symm j).1 (e.symm i).2 else 0 := by
  rw [GlobalTheory.CompanionTheory.AdmGL.blk, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.blockDiagonal_apply,
    GlobalTheory.CompanionTheory.AdmGL.atPlace, Matrix.map_apply]

@[simp] theorem unblk_blk (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    unblk e (blk e M) = M := by
  ext p q w
  simp [unblk, blk_apply]

theorem blk_injective (e : Fin a × ι ≃ Fin n) : Function.Injective (blk e) := by
  intro M N h
  rw [← GlobalTheory.CompanionTheory.AdmGL.unblk_blk e M, h, GlobalTheory.CompanionTheory.AdmGL.unblk_blk]

@[simp] theorem blk_one (e : Fin a × ι ≃ Fin n) : blk e 1 = 1 := by
  ext i j
  rw [GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  by_cases h : i = j
  · subst h
    simp
  · have h' : e.symm i ≠ e.symm j := fun h'' => h (e.symm.injective h'')
    rw [Matrix.one_apply_ne h]
    by_cases h2 : (e.symm i).2 = (e.symm j).2
    · have h1 : (e.symm i).1 ≠ (e.symm j).1 := fun h1 => h' (Prod.ext h1 h2)
      rw [if_pos h2, Matrix.one_apply_ne h1, Pi.zero_apply]
    · rw [if_neg h2]

theorem atPlace_mul (M N : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) :
    atPlace (M * N) w = atPlace M w * atPlace N w := by
  ext p q
  simp [atPlace, Matrix.mul_apply, Finset.sum_apply]

@[simp] theorem blk_mul (e : Fin a × ι ≃ Fin n) (M N : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    blk e (M * N) = blk e M * blk e N := by
  have h : GlobalTheory.CompanionTheory.AdmGL.atPlace (M * N) = fun w => GlobalTheory.CompanionTheory.AdmGL.atPlace M w * GlobalTheory.CompanionTheory.AdmGL.atPlace N w :=
    funext (GlobalTheory.CompanionTheory.AdmGL.atPlace_mul M N)
  simp only [GlobalTheory.CompanionTheory.AdmGL.blk, Matrix.reindex_apply]
  rw [h, Matrix.blockDiagonal_mul]
  exact (Matrix.submatrix_mul_equiv _ _ _ e.symm _).symm

@[simp] theorem blk_add (e : Fin a × ι ≃ Fin n) (M N : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    blk e (M + N) = blk e M + blk e N := by
  ext i j
  rw [Matrix.add_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply,
    GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  split_ifs <;> simp

@[simp] theorem blk_smul (e : Fin a × ι ≃ Fin n) (c : ℂ) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    blk e (c • M) = c • blk e M := by
  ext i j
  rw [Matrix.smul_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  split_ifs <;> simp

@[simp] theorem blk_conjTranspose (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    blk e Mᴴ = (blk e M)ᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply, GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  by_cases h : (e.symm i).2 = (e.symm j).2
  · rw [if_pos h, if_pos h.symm, Matrix.conjTranspose_apply, Pi.star_apply, h]
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

theorem continuous_blk (e : Fin a × ι ≃ Fin n) : Continuous (blk e) := by
  apply continuous_matrix
  intro i j
  simp only [GlobalTheory.CompanionTheory.AdmGL.blk_apply]
  by_cases h : (e.symm i).2 = (e.symm j).2
  · simp only [if_pos h]
    exact (continuous_apply _).comp (continuous_id.matrix_elem _ _)
  · simp only [if_neg h]
    exact continuous_const

theorem continuous_unblk (e : Fin a × ι ≃ Fin n) : Continuous (unblk e) := by
  apply continuous_matrix
  intro p q
  apply continuous_pi
  intro w
  simp only [GlobalTheory.CompanionTheory.AdmGL.unblk, Matrix.of_apply]
  exact continuous_id.matrix_elem _ _

theorem det_apply_place (M : Matrix (Fin a) (Fin a) (ι → ℂ)) (w : ι) : M.det w = (atPlace M w).det :=
  RingHom.map_det (Pi.evalRingHom (fun _ : ι => ℂ) w) M

theorem det_blk (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    (blk e M).det = ∏ w, (atPlace M w).det := by
  rw [blk, Matrix.det_reindex_self, Matrix.det_blockDiagonal]

theorem isUnit_blk_iff (e : Fin a × ι ≃ Fin n) (M : Matrix (Fin a) (Fin a) (ι → ℂ)) :
    IsUnit (blk e M) ↔ IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.isUnit_iff_isUnit_det, GlobalTheory.CompanionTheory.AdmGL.det_blk, Pi.isUnit_iff]
  simp [isUnit_iff_ne_zero, GlobalTheory.CompanionTheory.AdmGL.det_apply_place, Finset.prod_ne_zero_iff]

theorem mem_blkG_iff (e : Fin a × ι ≃ Fin n) {g : Matrix (Fin n) (Fin n) ℂ} :
    g ∈ blkG e ↔ IsUnit g ∧ blk e (unblk e g) = g := by
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact ⟨(GlobalTheory.CompanionTheory.AdmGL.isUnit_blk_iff e M).2 hM, by rw [GlobalTheory.CompanionTheory.AdmGL.unblk_blk]⟩
  · rintro ⟨hg, hg'⟩
    refine ⟨GlobalTheory.CompanionTheory.AdmGL.unblk e g, ?_, hg'⟩
    rw [← hg'] at hg
    exact (GlobalTheory.CompanionTheory.AdmGL.isUnit_blk_iff e _).1 hg

end GlobalTheory.CompanionTheory.AdmGL

end
end

section

open MeasureTheory
open scoped Matrix FourierTransform InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.FourierMat

noncomputable def entries (m n : ℕ) :
    (Fin m → Fin n → ℂ) ≃L[ℝ] EuclideanSpace ℂ (Fin m × Fin n) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u => WithLp.toLp 2 (fun p => u p.1 p.2)
      invFun := fun x a j => x (a, j)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem entries_apply (m n : ℕ) (u : Fin m → Fin n → ℂ) (p : Fin m × Fin n) :
    entries m n u p = u p.1 p.2 := rfl

theorem pairing {m n : ℕ} {s : ℂ} (hs : s ≠ 0) (w : EuclideanSpace ℂ (Fin m × Fin n))
    (v : Fin m → Fin n → ℂ) :
    (s * Matrix.trace ((Matrix.of fun a j => -(w (a, j)) / conj s)ᴴ * Matrix.of v)).re =
      -(⟪entries m n v, w⟫_ℝ) := by
  have key : s * Matrix.trace ((Matrix.of fun a j => -(w (a, j)) / conj s)ᴴ * Matrix.of v)
      = -(∑ a, ∑ j, conj (w (a, j)) * v a j) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply]
    rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_div₀, star_neg, Complex.star_def, Complex.conj_conj]
    field_simp
  rw [key, PiLp.inner_apply, Fintype.sum_prod_type, Complex.neg_re, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.inner]
  simp only [entries_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem fourier_uniqueness : ∀ (m n : ℕ) (s : ℂ), s ≠ 0 → ∀ g : (Fin m → Fin n → ℂ) → ℂ,
    Continuous g → Integrable g →
    (∀ u : Fin m → Fin n → ℂ, ∫ v, Complex.exp (2 * Real.pi * Complex.I *
      ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * g v = 0) → g = 0 := by
  intro m n s hs g hgc hgi hF
  have hemb : MeasurableEmbedding (entries m n) := (entries m n).toHomeomorph.measurableEmbedding
  have hC : (volume : Measure ℂ).IsAddHaarMeasure := inferInstance
  have hV1 : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ => volume)
  have hV2 : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure (fun _ => volume)
  have : (Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ))).IsAddHaarMeasure :=
    (entries m n).isAddHaarMeasure_map volume
  have hμ := Measure.isAddLeftInvariant_eq_smul
    (Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ)))
    (volume : Measure (EuclideanSpace ℂ (Fin m × Fin n)))
  have hcpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
    (Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ)))
    (volume : Measure (EuclideanSpace ℂ (Fin m × Fin n)))
  have hcomp : (fun x => g ((entries m n).symm x)) ∘ (entries m n) = g := by
    funext v
    simp
  have hGmap : Integrable (fun x => g ((entries m n).symm x))
      (Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ))) :=
    hemb.integrable_map_iff.mpr (by rw [hcomp]; exact hgi)
  rw [hμ, ← Measure.coe_nnreal_smul] at hGmap
  have hGi : Integrable (fun x => g ((entries m n).symm x))
      (volume : Measure (EuclideanSpace ℂ (Fin m × Fin n))) :=
    (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hcpos.ne') ENNReal.coe_ne_top).mp hGmap
  have hGc : Continuous (fun x => g ((entries m n).symm x)) :=
    hgc.comp (entries m n).symm.continuous
  have hFG : FourierTransform.fourier (fun x => g ((entries m n).symm x)) = 0 := by
    funext w
    rw [Real.fourier_eq', Pi.zero_apply]
    have h0 := hF (fun a j => -(w (a, j)) / conj s)
    have h1 : ∫ x, Complex.exp (↑(-2 * Real.pi * ⟪x, w⟫_ℝ) * Complex.I) • g ((entries m n).symm x)
        ∂(Measure.map (entries m n) (volume : Measure (Fin m → Fin n → ℂ))) = 0 := by
      rw [hemb.integral_map]
      refine Eq.trans ?_ h0
      congr 1
      funext v
      rw [pairing hs w v]
      simp only [ContinuousLinearEquiv.symm_apply_apply, smul_eq_mul]
      congr 2
      push_cast
      ring
    rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_zero] at h1
    exact h1.resolve_left (by exact_mod_cast hcpos.ne')
  have hinv := Continuous.fourierInv_fourier_eq hGc hGi
    (by rw [hFG]; exact integrable_zero _ _ _)
  rw [hFG] at hinv
  funext v
  have hx := congrFun hinv ((entries m n) v)
  rw [Real.fourierInv_eq'] at hx
  simp only [Pi.zero_apply, smul_zero, integral_zero, ContinuousLinearEquiv.symm_apply_apply] at hx
  rw [Pi.zero_apply]
  exact hx.symm

end GlobalTheory.CompanionTheory.FourierMat
end

section

open MeasureTheory Set

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

theorem integrable_of_summable_quotient_periodic :
    ∀ (G H : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] (ν : Measure G) [ν.IsAddHaarMeasure] (U : AddSubgroup G),
    IsOpen (U : Set G) → IsCompact (U : Set G) → ∀ ι : H →+ G, (∀ g, ∃ h, g - ι h ∈ U) →
    ∀ f : G → ℂ, (∀ g, ∀ u ∈ U, f (g + u) = f g) →
    Summable (fun x : H ⧸ U.comap ι => ‖f (ι (Quotient.out x))‖) → Integrable f ν := by
  intro G H _ _ _ _ _ _ _ ν _ U hUo hUc ι hι f hf hs
  let r : H ⧸ U.comap ι → G := fun x => ι (Quotient.out x)
  let c : H ⧸ U.comap ι → Set G := fun x => (fun g => g - r x) ⁻¹' (U : Set G)
  have hcopen : ∀ x, IsOpen (c x) := fun x => hUo.preimage (by fun_prop)
  have hcov : ⋃ x, c x = univ := by
    refine eq_univ_of_forall fun g => mem_iUnion.2 ?_
    obtain ⟨h, hh⟩ := hι g
    refine ⟨(QuotientAddGroup.mk h : H ⧸ U.comap ι), ?_⟩
    have h1 : -h + Quotient.out (QuotientAddGroup.mk h : H ⧸ U.comap ι) ∈ U.comap ι :=
      QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _).symm
    have h2 : ι (-h + Quotient.out (QuotientAddGroup.mk h : H ⧸ U.comap ι)) ∈ U := h1
    have h3 := U.sub_mem hh h2
    have h4 : g - ι h - ι (-h + Quotient.out (QuotientAddGroup.mk h : H ⧸ U.comap ι))
        = g - r (QuotientAddGroup.mk h : H ⧸ U.comap ι) := by
      simp only [r, map_add (f := _), map_neg]; abel
    change g - r _ ∈ U
    rwa [h4] at h3
  have hdisj : Pairwise (Function.onFun Disjoint c) := by
    intro x y hxy
    refine Set.disjoint_left.2 fun g hgx hgy => hxy ?_
    have hgx' : g - r x ∈ U := hgx
    have hgy' : g - r y ∈ U := hgy
    have h1 : ι (-Quotient.out x + Quotient.out y) ∈ U := by
      have h3 := U.sub_mem hgx' hgy'
      have h4 : g - r x - (g - r y) = ι (-Quotient.out x + Quotient.out y) := by
        simp only [r, map_add (f := _), map_neg]; abel
      rwa [h4] at h3
    have h2 : (QuotientAddGroup.mk (Quotient.out x) : H ⧸ U.comap ι) = QuotientAddGroup.mk (Quotient.out y) :=
      QuotientAddGroup.eq.2 h1
    rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at h2
  have hne : ∀ x, (c x).Nonempty := fun x => ⟨r x, by
    change r x - r x ∈ U
    simp⟩
  have hcount : Countable (H ⧸ U.comap ι) := by
    have hinj : Function.Injective c := by
      intro x y hxy
      by_contra hne'
      obtain ⟨g, hg⟩ := hne x
      exact Set.disjoint_left.1 (hdisj hne') hg (hxy ▸ hg)
    have hpd : (range c).PairwiseDisjoint id := by
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
      exact hdisj (fun h => hxy (by rw [h]))
    have := hpd.countable_of_isOpen (by rintro _ ⟨x, rfl⟩; exact hcopen x)
      (by rintro _ ⟨x, rfl⟩; exact hne x)
    have := this.to_subtype
    exact Function.Injective.countable (f := Set.rangeFactorization c)
      (fun x y h => hinj (congrArg Subtype.val h))
  have hconst : ∀ x, ∀ g ∈ c x, f g = f (r x) := by
    intro x g hg
    have := hf (r x) (g - r x) hg
    rw [← this]; congr 1; abel
  have hcont : Continuous f := by
    refine IsLocallyConstant.continuous ?_
    refine (IsLocallyConstant.iff_exists_open f).2 fun g => ?_
    refine ⟨(fun y => y - g) ⁻¹' (U : Set G), hUo.preimage (by fun_prop), by simp, ?_⟩
    intro y hy
    have := hf g (y - g) hy
    rw [← this]; congr 1; abel
  have hmeas : ∀ x, ν (c x) = ν (U : Set G) := by
    intro x
    have : c x = (fun g => g + (- r x)) ⁻¹' (U : Set G) := by
      ext g; simp [c, sub_eq_add_neg]
    rw [this, measure_preimage_add_right]
  have hUfin : ν (U : Set G) < ⊤ := hUc.measure_lt_top
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have hsum : ∑' x, ‖f (r x)‖ₑ < ⊤ := by
    have h1 : ∑' x, ‖f (r x)‖ₑ = ∑' x, ENNReal.ofReal ‖f (r x)‖ := by
      simp [ofReal_norm_eq_enorm]
    rw [h1]
    exact hs.tsum_ofReal_lt_top
  have hint : ∫⁻ g, ‖f g‖ₑ ∂ν = (∑' x, ‖f (r x)‖ₑ) * ν (U : Set G) := by
    calc ∫⁻ g, ‖f g‖ₑ ∂ν = ∫⁻ g in ⋃ x, c x, ‖f g‖ₑ ∂ν := by rw [hcov, Measure.restrict_univ]
      _ = ∑' x, ∫⁻ g in c x, ‖f g‖ₑ ∂ν :=
          lintegral_iUnion (fun x => (hcopen x).measurableSet) hdisj _
      _ = ∑' x, ‖f (r x)‖ₑ * ν (U : Set G) := by
          refine tsum_congr fun x => ?_
          rw [setLIntegral_congr_fun (hcopen x).measurableSet
            (g := fun _ => ‖f (r x)‖ₑ) (fun g hg => by simp only [hconst x g hg]),
            setLIntegral_const, hmeas]
      _ = (∑' x, ‖f (r x)‖ₑ) * ν (U : Set G) := ENNReal.tsum_mul_right
  change ∫⁻ g, ‖f g‖ₑ ∂ν < ⊤
  rw [hint]
  exact ENNReal.mul_lt_top hsum hUfin

end GlobalTheory.CompanionTheory.SiegelND.Integ
end

section

namespace GlobalTheory.CompanionTheory.Casselman

theorem lt_one_of_inv_mul_sqrt_mul_rpow_two_lt_one :
    ∀ (δ r : ℝ), 0 < δ → 0 ≤ r → δ⁻¹ * (Real.sqrt δ * r) ^ (2 : ℝ) < 1 → r < 1 := by
  intro δ r hδ hr h
  have h2 : (Real.sqrt δ * r) ^ (2 : ℝ) = δ * r ^ 2 := by
    rw [Real.rpow_two, mul_pow, Real.sq_sqrt hδ.le]
  rw [h2, ← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul] at h
  nlinarith

end GlobalTheory.CompanionTheory.Casselman
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0

open scoped Matrix

variable {P ι : Type}

def qR0 [Fintype ι] (A : P → Matrix ι ι ℝ) (x : P → ι → ℝ) : P → ℝ :=
  fun w => (1 / 2 : ℝ) * (x w ⬝ᵥ (A w *ᵥ x w))

def gaussR [Fintype P] [Fintype ι] (Pm : P → Matrix ι ι ℝ) (x : P → ι → ℝ) : ℝ :=
  Real.exp (-Real.pi * ∑ w, x w ⬝ᵥ (Pm w *ᵥ x w))

def boxR [Fintype ι] (t : P → ℝ) : Set (P → ι → ℝ) :=
  {x | ∀ w, ‖x w‖ ≤ t w}

def coreR [Fintype ι] (δ R : ℝ) : Set (P → ι → ℝ) :=
  {x | ∀ w, δ ≤ ‖x w‖ ∧ ‖x w‖ ≤ R}

end GlobalTheory.CompanionTheory.WeilSiegel.Inf0
end
end
