module

public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle107
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle097
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Mathlib.Algebra.Group.End
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle080
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle006
public import Mathlib.Order.WellFounded
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.Bundle001

@[expose] public section

section

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.WeakConv

section General

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] (μ : Measure G) (π : G → (H →L[ℂ] H))

def IsWeakInt (e : G → ℂ) (T : H →L[ℂ] H) : Prop :=
  Integrable e μ ∧ ∀ x y : H, ⟪x, T y⟫_ℂ = ∫ g, e g * ⟪x, π g y⟫_ℂ ∂μ

variable {μ π}

private theorem integrable_mul_of_bounded {α : Type*} [MeasurableSpace α] {ν : Measure α}
    {f c : α → ℂ} (hf : Integrable f ν) (hc : AEStronglyMeasurable c ν) (C : ℝ)
    (hb : ∀ a, ‖c a‖ ≤ C) : Integrable (fun a => f a * c a) ν := by
  refine Integrable.mono' (hf.norm.mul_const C) (hf.aestronglyMeasurable.mul hc) (ae_of_all _ fun a => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (hb a) (norm_nonneg _)


omit [Group G] [IsTopologicalGroup G] [SecondCountableTopology G] [CompleteSpace H] in
theorem integrable_mul_coeff (hn : ∀ g y, ‖π g y‖ = ‖y‖) (hc : ∀ y, Continuous fun g => π g y)
    {e : G → ℂ} (he : Integrable e μ) (x y : H) :
    Integrable (fun g => e g * ⟪x, π g y⟫_ℂ) μ := by
  have hcm : Continuous fun g => ⟪x, π g y⟫_ℂ := continuous_const.inner (hc y)
  refine integrable_mul_of_bounded he hcm.aestronglyMeasurable (‖x‖ * ‖y‖) fun g => ?_
  calc ‖⟪x, π g y⟫_ℂ‖ ≤ ‖x‖ * ‖π g y‖ := norm_inner_le_norm _ _
    _ = ‖x‖ * ‖y‖ := by rw [hn]


omit [Group G] [IsTopologicalGroup G] [SecondCountableTopology G] [TopologicalSpace G] [BorelSpace G] in
theorem IsWeakInt.inner_comp {e : G → ℂ} {T : H →L[ℂ] H} (h : IsWeakInt μ π e T) (A : H →L[ℂ] H)
    (x y : H) : ⟪x, A (T y)⟫_ℂ = ∫ g, e g * ⟪x, A (π g y)⟫_ℂ ∂μ := by
  rw [← ContinuousLinearMap.adjoint_inner_left, h.2]
  simp_rw [ContinuousLinearMap.adjoint_inner_left]

theorem IsWeakInt.conv [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (hm : ∀ g h, π (g * h) = (π g).comp (π h))
    (hn : ∀ g y, ‖π g y‖ = ‖y‖) (hc : ∀ y, Continuous fun g => π g y)
    {e e' : G → ℂ} {T T' : H →L[ℂ] H} (h : IsWeakInt μ π e T) (h' : IsWeakInt μ π e' T') :
    IsWeakInt μ π (fun k => ∫ g, e g * e' (g⁻¹ * k) ∂μ) (T.comp T') := by
  have hP : Integrable (fun z : G × G => e z.1 * e' (z.1⁻¹ * z.2)) (μ.prod μ) := by
    have h0 : Integrable (fun z : G × G => e z.1 * e' z.2) (μ.prod μ) := h.1.mul_prod h'.1
    exact ((measurePreserving_prod_inv_mul μ μ).integrable_comp h0.aestronglyMeasurable).2 h0
  refine ⟨hP.integral_prod_right, fun x y => ?_⟩
  have hcm : Continuous fun k => ⟪x, π k y⟫_ℂ := continuous_const.inner (hc y)
  have hcm2 : Measurable fun z : G × G => ⟪x, π z.2 y⟫_ℂ := hcm.measurable.comp measurable_snd
  have hQ : Integrable (fun z : G × G => e z.1 * e' (z.1⁻¹ * z.2) * ⟪x, π z.2 y⟫_ℂ) (μ.prod μ) := by
    refine integrable_mul_of_bounded hP hcm2.aestronglyMeasurable (‖x‖ * ‖y‖) fun z => ?_
    calc ‖⟪x, π z.2 y⟫_ℂ‖ ≤ ‖x‖ * ‖π z.2 y‖ := norm_inner_le_norm _ _
      _ = ‖x‖ * ‖y‖ := by rw [hn]
  have hin : ∀ g, ⟪x, π g (T' y)⟫_ℂ = ∫ k, e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ ∂μ := by
    intro g
    rw [h'.inner_comp (π g) x y]
    refine (integral_mul_left_eq_self _ g⁻¹).symm.trans ?_
    congr 1
    ext k
    have hk : π g (π (g⁻¹ * k) y) = π k y := by
      rw [← ContinuousLinearMap.comp_apply, ← hm, mul_inv_cancel_left]
    simp only [hk]
  calc ⟪x, (T.comp T') y⟫_ℂ = ∫ g, e g * ⟪x, π g (T' y)⟫_ℂ ∂μ := h.2 x (T' y)
    _ = ∫ g, ∫ k, e g * e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ ∂μ ∂μ := by
        congr 1
        ext g
        rw [hin, ← integral_const_mul]
        congr 1
        ext k
        ring
    _ = ∫ k, ∫ g, e g * e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ ∂μ ∂μ :=
        integral_integral_swap (f := fun g k => e g * e' (g⁻¹ * k) * ⟪x, π k y⟫_ℂ) hQ
    _ = ∫ k, (∫ g, e g * e' (g⁻¹ * k) ∂μ) * ⟪x, π k y⟫_ℂ ∂μ := by
        congr 1
        ext k
        rw [integral_mul_const]

end General

theorem rightConv_unique_add_smul_mul_comm : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund)), I.IsFundDom (I.muA μf) fund → I.IsRightReg μf fund R → (∀ e T T', I.IsRConvF μf fund R e T → I.IsRConvF μf fund R e T' → T = T') ∧ (∀ e e' T T', I.IsRConvF μf fund R e T → I.IsRConvF μf fund R e' T' → I.IsRConvF μf fund R (e + e') (T + T')) ∧ (∀ (c : ℂ) e T, I.IsRConvF μf fund R e T → I.IsRConvF μf fund R (c • e) (c • T)) ∧ (∀ e e' T T', Continuous e → Continuous e' → I.IsRConvF μf fund R e T → I.IsRConvF μf fund R e' T' → I.IsRConvF μf fund R (I.convF μf e e') (T.comp T')) ∧ ∀ e T (x : I.Ginf), I.IsRConvF μf fund R e T → T.comp (R (x, 1)) = (R (x, 1)).comp T := by
  intro I μf hH hS fund R hfund hR
  obtain ⟨-, hmul, hn, hc⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous I μf fund hfund R hR
  have := GlobalTheory.CongTop.secondCountable_finiteAdelicPoints I
  have hm' : ∀ g h : I.Gf, R (1, g * h) = (R (1, g)).comp (R (1, h)) := by
    intro g h
    rw [← hmul, Prod.mk_mul_mk, one_mul]
  have hn' : ∀ (g : I.Gf) (F : I.L2 μf fund), ‖R (1, g) F‖ = ‖F‖ := fun g F => hn _ F
  have hc' : ∀ F : I.L2 μf fund, Continuous fun g : I.Gf => R (1, g) F := fun F =>
    Continuous.comp (g := fun x : I.GA => R x F) (f := fun g : I.Gf => ((1 : I.Ginf), g)) (hc F)
      (continuous_const.prodMk continuous_id)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e T T' h h'
    refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun z => ?_
    rw [h.2, h'.2]
  · intro e e' T T' h h'
    refine ⟨h.1.add h'.1, fun z y => ?_⟩
    have i1 := integrable_mul_coeff (μ := μf) (π := fun g : I.Gf => R (1, g)) hn' hc' h.1 z y
    have i2 := integrable_mul_coeff (μ := μf) (π := fun g : I.Gf => R (1, g)) hn' hc' h'.1 z y
    rw [ContinuousLinearMap.add_apply, inner_add_right, h.2, h'.2, ← integral_add i1 i2]
    congr 1
    ext g
    simp only [Pi.add_apply]
    ring
  · intro c e T h
    refine ⟨h.1.smul c, fun z y => ?_⟩
    rw [ContinuousLinearMap.smul_apply, inner_smul_right, h.2, ← integral_const_mul]
    congr 1
    ext g
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro e e' T T' _ _ h h'
    exact IsWeakInt.conv (μ := μf) (π := fun g : I.Gf => R (1, g)) hm' hn' hc' h h'
  · intro e T x h
    refine ContinuousLinearMap.ext fun y => ext_inner_left ℂ fun z => ?_
    have hcomm : ∀ g : I.Gf, R (1, g) (R (x, 1) y) = R (x, 1) (R (1, g) y) := by
      intro g
      have key : R ((1, g) * (x, 1)) = R ((x, 1) * (1, g)) := by
        congr 1
        simp
      rw [hmul, hmul] at key
      exact congrArg (fun A : I.L2 μf fund →L[ℂ] I.L2 μf fund => A y) key
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h.2 z (R (x, 1) y),
      IsWeakInt.inner_comp (μ := μf) (π := fun g : I.Gf => R (1, g)) h (R (x, 1)) z y]
    simp only [hcomm]

end GlobalTheory.WeakConv
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.BlockDiagEmb

section
variable {n : ℕ} {σ ι : Type} [Fintype σ] {π : σ → ι} {m : ι → ℕ}

def blk (T : ∀ s, Matrix (Fin n) (Fin (m (π s))) ℂ) (k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑ s, T s * k (π s) * (T s)ᴴ

variable {T : ∀ s, Matrix (Fin n) (Fin (m (π s))) ℂ}

theorem frame_mul_blk (h1 : ∀ s, (T s)ᴴ * T s = 1) (h0 : ∀ s t, s ≠ t → (T s)ᴴ * T t = 0)
    (k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) (s : σ) :
    (T s)ᴴ * blk T k = k (π s) * (T s)ᴴ := by
  unfold blk
  rw [Matrix.mul_sum, Finset.sum_eq_single s]
  · rw [Matrix.mul_assoc (T s), ← Matrix.mul_assoc, h1, Matrix.one_mul]
  · intro t _ hts
    rw [Matrix.mul_assoc (T t), ← Matrix.mul_assoc, h0 s t hts.symm, Matrix.zero_mul]
  · simp

theorem blk_mul (h1 : ∀ s, (T s)ᴴ * T s = 1) (h0 : ∀ s t, s ≠ t → (T s)ᴴ * T t = 0)
    (k l : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    blk T k * blk T l = blk T (fun i => k i * l i) := by
  conv_lhs => rw [blk, Matrix.sum_mul]
  unfold blk
  refine Finset.sum_congr rfl fun s _ => ?_
  have := frame_mul_blk h1 h0 l s
  unfold blk at this
  rw [Matrix.mul_assoc, this]
  simp only [Matrix.mul_assoc]

theorem blk_one (hs : ∑ s, T s * (T s)ᴴ = 1) : blk T (fun _ => 1) = 1 := by
  simpa [blk] using hs

theorem blk_conjTranspose (k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    (blk T k)ᴴ = blk T (fun i => (k i)ᴴ) := by
  simp [blk, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem blk_sub (k l : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    blk T k - blk T l = blk T (fun i => k i - l i) := by
  simp [blk, Matrix.mul_sub, Matrix.sub_mul, Finset.sum_sub_distrib]

theorem blk_trace (h1 : ∀ s, (T s)ᴴ * T s = 1) (k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    (blk T k).trace = ∑ s, (k (π s)).trace := by
  unfold blk
  rw [Matrix.trace_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem hs_eq_trace {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) :
    Formalism.REAL.hs X = (X * Xᴴ).trace.re := by
  simp only [Formalism.REAL.hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem blk_hs (h1 : ∀ s, (T s)ᴴ * T s = 1) (h0 : ∀ s t, s ≠ t → (T s)ᴴ * T t = 0)
    (k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ) :
    Formalism.REAL.hs (blk T k) = ∑ s, Formalism.REAL.hs (k (π s)) := by
  rw [hs_eq_trace, blk_conjTranspose, blk_mul h1 h0, blk_trace h1, Complex.re_sum]
  simp only [hs_eq_trace]

theorem continuous_blk : Continuous (blk T) := by
  unfold blk
  refine continuous_finsetSum _ fun s _ => ?_
  exact (continuous_const.matrix_mul (continuous_apply (π s))).matrix_mul continuous_const

end

theorem unitary_of_allPos {N : ℕ} (g : Formalism.REAL.UJ (allPos N)) : (uMat g)ᴴ * uMat g = 1 := by
  have h : (uMat g)ᴴ * Formalism.REAL.Jm (allPos N) * uMat g = Formalism.REAL.Jm (allPos N) := g.2
  have hJ : Formalism.REAL.Jm (allPos N) = 1 := by simp [Formalism.REAL.Jm, allPos]
  simpa [hJ] using h

theorem uMat_mul' {n : ℕ} {ε : Fin n → Bool} (g h : Formalism.REAL.UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_one' {n : ℕ} {ε : Fin n → Bool} : uMat (1 : Formalism.REAL.UJ ε) = 1 := rfl

theorem continuous_uMat {n : ℕ} {ε : Fin n → Bool} : Continuous (fun g : Formalism.REAL.UJ ε => uMat g) :=
  Units.continuous_val.comp continuous_subtype_val

theorem exists_blockDiag_hom : ∀ (n : ℕ) (ε : Fin n → Bool) (σ ι : Type) [Fintype σ] [Fintype ι] (π : σ → ι) (m : ι → ℕ) (T : ∀ s, Matrix (Fin n) (Fin (m (π s))) ℂ), Function.Surjective π → (∀ s, (T s)ᴴ * T s = 1) → (∀ s t, s ≠ t → (T s)ᴴ * T t = 0) → ∑ s, T s * (T s)ᴴ = 1 → (∀ k : ∀ i, Matrix (Fin (m i)) (Fin (m i)) ℂ, Formalism.REAL.Jm ε * ∑ s, T s * k (π s) * (T s)ᴴ = (∑ s, T s * k (π s) * (T s)ᴴ) * Formalism.REAL.Jm ε) → ∃ Φ : (∀ i, Formalism.REAL.UJ (allPos (m i))) →* Formalism.REAL.UJ ε, Continuous Φ ∧ Function.Injective Φ ∧ (∀ g, uMat (Φ g) = ∑ s, T s * uMat (g (π s)) * (T s)ᴴ) ∧ ∀ g, Formalism.REAL.hs (uMat (Φ g) - 1) = ∑ s, Formalism.REAL.hs (uMat (g (π s)) - 1) := by
  intro n ε σ ι _ _ π m T hπ h1 h0 hs hJ
  let f : (∀ i, Formalism.REAL.UJ (allPos (m i))) →* Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun g => blk T (fun i => uMat (g i))
      map_one' := by simp only [Pi.one_apply, uMat_one']; exact blk_one hs
      map_mul' := fun g h => by simp only [Pi.mul_apply, uMat_mul']; exact (blk_mul h1 h0 _ _).symm }
  have hfe : ∀ g, f g = blk T (fun i => uMat (g i)) := fun g => rfl
  clear_value f
  have hf : Continuous f := by
    have h : Continuous (fun (g : ∀ i, Formalism.REAL.UJ (allPos (m i))) => fun i => uMat (g i)) :=
      continuous_pi fun i => continuous_uMat.comp (continuous_apply i)
    have h2 := (continuous_blk (T := T)).comp h
    exact h2.congr fun g => (hfe g).symm
  have hmem : ∀ g, f.toHomUnits g ∈ Formalism.REAL.UJ ε := by
    intro g
    show (f g)ᴴ * Formalism.REAL.Jm ε * f g = Formalism.REAL.Jm ε
    rw [hfe]
    have hJ' : ∀ k, Formalism.REAL.Jm ε * blk T k = blk T k * Formalism.REAL.Jm ε := hJ
    have := hJ' (fun i => uMat (g i))
    rw [Matrix.mul_assoc, this, ← Matrix.mul_assoc, blk_conjTranspose, blk_mul h1 h0]
    simp only [unitary_of_allPos]
    rw [blk_one hs, Matrix.one_mul]
  refine ⟨f.toHomUnits.codRestrict _ hmem, ?_, ?_, fun g => hfe g, fun g => ?_⟩
  · have hu : Continuous f.toHomUnits :=
      Units.continuous_iff.2 ⟨hf, hf.comp continuous_inv⟩
    exact hu.subtype_mk hmem
  · intro g h hgh
    have e : blk T (fun i => uMat (g i)) = blk T (fun i => uMat (h i)) := by
      rw [← hfe, ← hfe]
      exact congrArg (fun x : Formalism.REAL.UJ ε => uMat x) hgh
    funext i
    obtain ⟨s, rfl⟩ := hπ i
    have e2 := frame_mul_blk h1 h0 (fun i => uMat (g i)) s
    rw [e, frame_mul_blk h1 h0] at e2
    have e3 := congrArg (· * T s) e2
    simp only [Matrix.mul_assoc, h1, Matrix.mul_one] at e3
    exact Subtype.ext (Units.ext e3.symm)
  · show Formalism.REAL.hs (f g - 1) = _
    rw [hfe, ← blk_one (T := T) hs, blk_sub, blk_hs h1 h0]

end GlobalTheory.BlockDiagEmb
end
end

section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FormalDegreeDatum

theorem inUJ_of_cayley {n : ℕ} (ε : Fin n → Bool) (P Q G : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P)
    (h1 : Pᴴ * Formalism.REAL.Jm ε * P = G) (h2 : Qᴴ * Formalism.REAL.Jm ε * Q = G) :
    Formalism.REAL.inUJ ε (Q * P⁻¹) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  unfold Formalism.REAL.inUJ
  have : (Q * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (Q * P⁻¹) = (P⁻¹)ᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * P⁻¹ := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [this, h2, ← h1]
  have : (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * P⁻¹) := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [this, hPP]; simp

theorem fdeg_of_conj {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Measure (Formalism.REAL.UJ ε)) [μ.IsMulLeftInvariant]
    (σ₀ σ₁ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (a : Formalism.REAL.UJ ε)
    (hc : ∀ g : Formalism.REAL.UJ ε, σ₀ (umat g) = σ₁ (umat (a * g * a⁻¹)))
    (hu : IsURepOn (UJset ε) σ₁) (d : ℝ) (hd : IsFdeg μ σ₀ d) (w : H) (hw : w ≠ 0) :
    ‖w‖ ^ 4 / ∫ g, ‖inner ℂ w (σ₁ (umat g) w)‖ ^ 2 ∂μ = d := by
  have hmem : ∀ g : Formalism.REAL.UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hmul : ∀ g h : Formalism.REAL.UJ ε, σ₁ (umat (g * h)) w = σ₁ (umat g) (σ₁ (umat h) w) := by
    intro g h
    have := hu.1.2 _ (hmem g) _ (hmem h)
    have e : umat (g * h) = umat g * umat h := rfl
    rw [e, this]; rfl
  have hv : ‖σ₁ (umat a) w‖ = ‖w‖ := hu.2.1 _ (hmem a) w
  set v := σ₁ (umat a) w with hvdef
  have h1 : ∫ g, ‖inner ℂ w (σ₁ (umat g) w)‖ ^ 2 ∂μ = ∫ g, ‖coefOn σ₀ v w g‖ ^ 2 ∂μ := by
    rw [← integral_mul_left_eq_self (fun g : Formalism.REAL.UJ ε => ‖inner ℂ w (σ₁ (umat g) w)‖ ^ 2) a]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [coefOn, hc, hvdef, ← hmul]
    rw [inv_mul_cancel_right]
  have h2 := (hd.2 v w v w).2
  have h3 : ∀ g : Formalism.REAL.UJ ε, coefOn σ₀ v w g * star (coefOn σ₀ v w g) =
      ((‖coefOn σ₀ v w g‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [h3] at h2
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hv] at h2
  have h4 : ∫ g, ‖coefOn σ₀ v w g‖ ^ 2 ∂μ = ‖w‖ ^ 2 * ‖w‖ ^ 2 / d := by
    apply Complex.ofReal_injective
    rw [h2]
    simp
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.2 hw
  have hd0 : d ≠ 0 := hd.1.ne'
  rw [h1, h4]
  field_simp

end GlobalTheory.FormalDegreeDatum
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory

theorem shuffle_first_block_upper (a n : ℕ) (σ : Equiv.Perm (Fin n))
    (h : ∀ i j : Fin n, (i : ℕ) < a → a ≤ (j : ℕ) → (σ j : ℕ) ≠ σ i + 1)
    (i : Fin n) (hi : (i : ℕ) < a) (k : ℕ) :
    ∀ j : Fin n, (σ j : ℕ) = σ i + k → (j : ℕ) < a := by
  induction k with
  | zero =>
    intro j hj
    have : σ j = σ i := Fin.ext (by simpa using hj)
    rw [σ.injective this]; exact hi
  | succ k ih =>
    intro j hj
    have hlt : (σ i : ℕ) + k < n := by have := (σ j).isLt; omega
    have h1 : ((σ (σ.symm ⟨σ i + k, hlt⟩) : Fin n) : ℕ) = σ i + k := by simp
    have h2 := ih _ h1
    by_contra hc
    exact h _ j h2 (not_lt.mp hc) (by omega)

theorem shuffle_noDescent_iff_open :
    ∀ (a b n : ℕ) (σ : Equiv.Perm (Fin n)), n = a + b → (∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) → ((∀ i j : Fin n, (i : ℕ) < a → a ≤ (j : ℕ) → (σ j : ℕ) ≠ σ i + 1) ↔ ∀ j : Fin n, (σ j : ℕ) = if (j : ℕ) < a then b + j else j - a) := by
  intro a b n σ hn hmono
  constructor
  · intro h
    have hup : ∀ i j : Fin n, (i : ℕ) < a → a ≤ (j : ℕ) → σ j < σ i := by
      intro i j hi hj
      by_contra hc
      have hc' : (σ i : ℕ) ≤ σ j := not_lt.mp hc
      have := shuffle_first_block_upper a n σ h i hi (σ j - σ i) j (by omega)
      omega
    let ρ : Fin n → Fin n := fun k =>
      ⟨if (k : ℕ) < b then a + k else k - b, by have := k.isLt; split_ifs <;> omega⟩
    have hρ : ∀ k, (ρ k : ℕ) = if (k : ℕ) < b then a + k else k - b := fun _ => rfl
    have hs : StrictMono (fun k => σ (ρ k)) := by
      intro k l hkl
      have hkl' : (k : ℕ) < l := hkl
      have hk := hρ k
      have hl := hρ l
      have hl2 := l.isLt
      show σ (ρ k) < σ (ρ l)
      by_cases h1 : (k : ℕ) < b
      · by_cases h2 : (l : ℕ) < b
        · rw [if_pos h1] at hk; rw [if_pos h2] at hl
          exact hmono _ _ (Fin.lt_def.mpr (by omega)) (Or.inr (by omega))
        · rw [if_pos h1] at hk; rw [if_neg h2] at hl
          exact hup _ _ (by omega) (by omega)
      · have h2 : ¬ (l : ℕ) < b := by omega
        rw [if_neg h1] at hk; rw [if_neg h2] at hl
        exact hmono _ _ (Fin.lt_def.mpr (by omega)) (Or.inl (by omega))
    have hid : ∀ k, σ (ρ k) = k := fun k =>
      le_antisymm (hs.dual.le_apply (x := OrderDual.toDual k)) hs.le_apply
    intro j
    have hj := j.isLt
    let k : Fin n := ⟨if (j : ℕ) < a then b + j else j - a, by split_ifs <;> omega⟩
    have hk : (k : ℕ) = if (j : ℕ) < a then b + j else j - a := rfl
    have hjk : ρ k = j := by
      apply Fin.ext
      rw [hρ, hk]
      split_ifs <;> omega
    rw [← hk, ← hid k, hjk]
  · intro h i j hi hj
    have h1 := h i
    have h2 := h j
    have := j.isLt
    rw [if_pos hi] at h1
    rw [if_neg (by omega)] at h2
    omega

end GlobalTheory
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.initial_lengths_product_moment_le : ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r l : ℕ) (hl : l ≤ r + 1) (len : Fin (r + 1) → Ω → ℝ) (Ph : Ω → ℝ) (A Rr : ℝ), (∀ a, AEMeasurable (len a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 < len a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν = 1 → 0 ≤ A → 1 ≤ Rr → (∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (len 0 x ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (A ^ q)) → (∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal ((len a.succ x / len a.castSucc x) ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * q))) → ∫⁻ x, ENNReal.ofReal ((∏ a : Fin l, len (Fin.castLE hl a) x ^ 2) * Ph x) ∂ν ≤ ENNReal.ofReal ((A * Rr ^ (2 * r)) ^ l) := by
  first | exact @GlobalTheory.MomentHolder.initial_product_moment_le | exact GlobalTheory.MomentHolder.initial_product_moment_le | (intros; apply GlobalTheory.MomentHolder.initial_product_moment_le <;> assumption)
end
