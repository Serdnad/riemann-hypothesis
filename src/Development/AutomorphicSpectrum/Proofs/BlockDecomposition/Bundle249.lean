module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle232
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle233
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusCurve
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusFirstAssumption
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle221
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle235
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle003
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle234
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle045
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GelfandOperatorsCommute
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle227
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.PresSobA

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.SobGL.HaarDom

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

abbrev CLof (E F : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] : Type :=
  E →L[ℝ] F

def expC (X : Mat n) (t : ℝ) : G n := (Matrix.isUnit_exp (t • X)).unit

theorem expC_val (X : Mat n) (t : ℝ) : (expC X t).val = NormedSpace.exp (t • X) := rfl

theorem expC_zero (X : Mat n) : expC X 0 = 1 := by
  apply Units.ext
  simp [expC_val]

def IsTest (φ : Mat n → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ GLs n

section Mol

variable [MeasurableSpace (G n)] (μ : Measure (G n))

def Mol {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (φ : Mat n → ℝ) (x : G n → V) (z : Mat n) : V :=
  ∫ u : G n, φ (z * (u⁻¹ : G n).val) • x u ∂μ

variable [BorelSpace (G n)] [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def lT (y : G n) : Lp V 2 μ →L[ℂ] Lp V 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun z : G n => y⁻¹ * z) (measurePreserving_mul_left μ y⁻¹)).toContinuousLinearMap

def lConv (φ : Mat n → ℝ) (x : Lp V 2 μ) : Lp V 2 μ := ∫ y : G n, φ y.val • lT μ V y x ∂μ

variable {V}

theorem lT_coe (y : G n) (x : Lp V 2 μ) : lT μ V y x =ᵐ[μ] fun z => x (y⁻¹ * z) :=
  Lp.coeFn_compMeasurePreserving x (measurePreserving_mul_left μ y⁻¹)

theorem rR_coe (hU : Unimod) (h : G n) (x : Lp V 2 μ) : rR μ V h x =ᵐ[μ] fun z => x (z * h) := by
  haveI := (hU n μ).1
  have hm : MeasurePreserving (fun y : G n => y * h) μ μ := measurePreserving_mul_right μ h
  have : rR μ V h x = Lp.compMeasurePreserving (fun y : G n => y * h) hm x := by
    simp only [rR, dif_pos hm]
    rfl
  rw [this]
  exact Lp.coeFn_compMeasurePreserving x hm

theorem cls_of_ae {f : Mat n → V} {x : Lp V 2 μ} (h : (fun y : G n => f y.val) =ᵐ[μ] x) :
    MemLp (fun y : G n => f y.val) 2 μ ∧ cls μ f = x := by
  have hm : MemLp (fun y : G n => f y.val) 2 μ := (memLp_congr_ae h).2 (Lp.memLp x)
  refine ⟨hm, ?_⟩
  simp only [cls, dif_pos hm]
  exact Lp.ext (hm.coeFn_toLp.trans h)

theorem coe_cls {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) :
    (cls μ f : G n → V) =ᵐ[μ] fun y => f y.val := by
  simp only [cls, dif_pos h]
  exact h.coeFn_toLp

end Mol

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage this

section Words

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_congr {f f' : Mat n → V} (h : ∀ z ∈ GLs n, f z = f' z) (X : Mat n) :
    ∀ z ∈ GLs n, Rd X f z = Rd X f' z := by
  intro z hz
  have : f =ᶠ[𝓝 z] f' := Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hz) h
  simp only [Rd, this.fderiv_eq]

theorem Rw_append (w w' : List (Bool × Fin n × Fin n)) (f : Mat n → V) :
    Rw (w ++ w') f = Rw w (Rw w' f) := by
  induction w with
  | nil => rfl
  | cons p w ih => simp only [List.cons_append, Rw, ih]

end Words

end GlobalTheory.CompanionTheory.PresSobA
end
end

section


theorem _root_.GlobalTheory.T.friedrichs_extension_facts : PositivityTheory.RgBcC.Fc.Friedrichs := by
  first | exact @GlobalTheory.CompanionTheory.FriedrichsFc.friedrichs | exact GlobalTheory.CompanionTheory.FriedrichsFc.friedrichs | (intros; apply GlobalTheory.CompanionTheory.FriedrichsFc.friedrichs <;> assumption)
end

section


theorem _root_.GlobalTheory.T.compact_sobolev_embedding : PositivityTheory.RgBcC.Fc.CptSob := by
  first | exact @GlobalTheory.CompanionTheory.CptSobProof.cptSob | exact GlobalTheory.CompanionTheory.CptSobProof.cptSob | (intros; apply GlobalTheory.CompanionTheory.CptSobProof.cptSob <;> assumption)
end

section


theorem _root_.GlobalTheory.T.dense_domain_facts : PositivityTheory.RgBcC.Fc.DenseD := by
  first | exact @GlobalTheory.CompanionTheory.DenseCpt.denseD | exact GlobalTheory.CompanionTheory.DenseCpt.denseD | (intros; apply GlobalTheory.CompanionTheory.DenseCpt.denseD <;> assumption)
end

section


theorem _root_.GlobalTheory.T.functional_calculus_curve : PositivityTheory.RgBcC.Fc.Fcurve := by
  first | exact @GlobalTheory.CompanionTheory.WaveCurve.fcurve | exact GlobalTheory.CompanionTheory.WaveCurve.fcurve | (intros; apply GlobalTheory.CompanionTheory.WaveCurve.fcurve <;> assumption)
end

section


theorem _root_.GlobalTheory.T.functional_calculus_first_assumption : PositivityTheory.RgBcC.Fc.Asm1 := by
  first | exact @GlobalTheory.CompanionTheory.WaveFc.Asm.asm1 | exact GlobalTheory.CompanionTheory.WaveFc.Asm.asm1 | (intros; apply GlobalTheory.CompanionTheory.WaveFc.Asm.asm1 <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.SobGL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.length_continuous_proper_sublevel : ∀ n : ℕ, ContinuousOn (lg (n := n)) (GLs n) ∧ ∀ R : ℝ, IsCompact {y : G n | lg y.val ≤ R} := by
  first | exact @GlobalTheory.CompanionTheory.SobGL.lg_continuousOn_and_isCompact | exact GlobalTheory.CompanionTheory.SobGL.lg_continuousOn_and_isCompact | (intros; apply GlobalTheory.CompanionTheory.SobGL.lg_continuousOn_and_isCompact <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

theorem rd_skew_eq_const {n : ℕ} (E : KMod n) (Y : Mat n) (hY : Yᴴ = -Y) :
    ∃ B : E.V →L[ℂ] E.V, ∀ f ∈ CE E, ∀ g ∈ GLs n, Rd Y f g = B (f g) := by
  obtain ⟨c, hc, c0, cadd, cd⟩ := GlobalTheory.T.skew_hermitian_unitary_flow Y hY
  haveI : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hinv : ∀ t, (c t)⁻¹ = c (-t) := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← cadd, add_neg_cancel, c0])
  let Φ : ℝ → (E.V →L[ℂ] E.V) := fun t => E.ρ (c (-t))
  have hΦc : Continuous Φ := E.cont.comp (hc.comp continuous_neg)
  have hΦ0 : Φ 0 = 1 := by simp only [Φ, neg_zero, c0, map_one]
  have hΦa : ∀ s t, Φ (s + t) = Φ s * Φ t := fun s t => by
    simp only [Φ, neg_add, cadd, map_mul]
  obtain ⟨B, hB⟩ := GlobalTheory.T.continuous_one_param_differentiable Φ hΦc hΦ0 hΦa
  refine ⟨B, fun f hf g hg => ?_⟩
  have hk : ∀ t, f (g * (c t).1) = Φ t (f g) := fun t => by
    rw [hf.2 g hg (c t), hinv]
  have h1 : HasDerivAt (fun t => Φ t (f g)) (B (f g)) 0 :=
    ((ContinuousLinearMap.apply ℂ E.V (f g)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hB
  let L : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ g)
  have h2 : HasDerivAt (fun t => g * (c t).1) (g * Y) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 cd
  have hd : DifferentiableAt ℝ f g :=
    (hf.1.contDiffAt (isOpen_GLs.mem_nhds hg)).differentiableAt (by simp)
  have h3 : HasFDerivAt f (fderiv ℝ f g) (g * (c 0).1) := by
    simpa [c0] using hd.hasFDerivAt
  have h4 : HasDerivAt (fun t => f (g * (c t).1)) (fderiv ℝ f g (g * Y)) 0 :=
    h3.comp_hasDerivAt 0 h2
  have h5 : (fun t => f (g * (c t).1)) = fun t => Φ t (f g) := funext hk
  rw [h5] at h4
  exact h4.unique h1

end GlobalTheory.CompanionTheory.WaveSpd
end

section

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.HbBasis

open PositivityTheory.RgTw (Mat hb)
open PositivityTheory.RgBcC
open PositivityTheory.RgBcC.LfSt

variable {n : ℕ}

theorem sum_single_one : ∑ a : Fin n, (Matrix.single a a (1 : ℂ) : Mat n) = 1 := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.single_apply]
  by_cases h : i = j
  · subst h
    simp
  · rw [Matrix.one_apply_ne h]
    refine Finset.sum_eq_zero fun x _ => if_neg fun hx => h (hx.1.symm.trans hx.2)

theorem sqrt_two_inv_sq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 :=
  GlobalTheory.CompanionTheory.TopClass.sqrt_two_inv_sq

theorem hb_mul_self (a b : Fin n) :
    (hb (a, b) : Mat n) * hb (a, b) = (1 / 2 : ℂ) • (Matrix.single a a 1 + Matrix.single b b 1) := by
  have hs := sqrt_two_inv_sq
  by_cases h : a = b
  · subst h
    have : (hb (a, a) : Mat n) = Matrix.single a a 1 := by simp [hb]
    rw [this, Matrix.single_mul_single_same, ← two_smul ℂ, smul_smul]
    norm_num
  · have hne : b ≠ a := fun e => h e.symm
    by_cases h' : a < b
    · have : (hb (a, b) : Mat n) = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) • (Matrix.single a b 1 + Matrix.single b a 1) := by
        simp [hb, h, h']
      rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hs]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne _ _ _ _ hne, Matrix.single_mul_single_of_ne _ _ _ _ h]
      simp [add_comm]
    · have : (hb (a, b) : Mat n) =
          (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I) • (Matrix.single a b 1 - Matrix.single b a 1) := by
        simp [hb, h, h']
      have hc : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I) * (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * Complex.I) = -(1 / 2) := by
        calc _ = (((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹) * (Complex.I * Complex.I) := by ring
          _ = _ := by rw [hs, Complex.I_mul_I]; ring
      rw [this, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hc]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne _ _ _ _ hne, Matrix.single_mul_single_of_ne _ _ _ _ h]
      simp only [mul_one, sub_zero, zero_sub, neg_smul, smul_neg, smul_sub, smul_add]
      abel

theorem sum_hb_mul_self : ∑ p, (hb p : Mat n) * hb p = (n : ℂ) • 1 := by
  rw [Fintype.sum_prod_type]
  simp only [hb_mul_self, ← Finset.smul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, sum_single_one]
  rw [← Nat.cast_smul_eq_nsmul ℂ n (1 : Mat n), ← two_smul ℂ, smul_smul, smul_smul]
  norm_num

theorem coords_one (p : Fin n × Fin n) : ((coords (1 : Mat n) p : ℝ) : ℂ) = (hb p : Mat n).trace := by
  have := GlobalTheory.CompanionTheory.ConeLin.re_trace (1 : Mat n) (by simp) p
  simpa [coords] using this

theorem hOf_coords {H : Mat n} (hH : H.IsHermitian) : hOf (coords H) = H :=
  GlobalTheory.CompanionTheory.ConeLin.hOf_re H hH

theorem coords_hOf (v : Fin n × Fin n → ℝ) : coords (hOf v) = v := by
  funext q
  have : (hOf v * hb q).trace = (v q : ℂ) := by
    classical
    simp [hOf, Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul,
      GlobalTheory.CompanionTheory.TopClass.trace_hb_mul_hb]
  simp [coords, this]

theorem hOf_isHermitian (v : Fin n × Fin n → ℝ) : (hOf v).IsHermitian :=
  GlobalTheory.CompanionTheory.ConeLin.hOf_herm v

theorem sum_trace_smul_hb : ∑ p, (hb p : Mat n).trace • hb p = 1 := by
  have h := hOf_coords (H := (1 : Mat n)) Matrix.isHermitian_one
  simpa only [hOf, coords_one] using h

theorem oPt_mem_cone : oPt n ∈ cone n := by
  show (hOf (coords (1 : Mat n))).PosDef
  rw [hOf_coords Matrix.isHermitian_one]
  exact Matrix.PosDef.one

theorem hbFacts : HbFacts := fun _ =>
  ⟨GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose, GlobalTheory.CompanionTheory.TopClass.trace_hb_mul_hb, fun _ hH => hOf_coords hH,
    coords_hOf, hOf_isHermitian, sum_hb_mul_self, sum_trace_smul_hb, oPt_mem_cone⟩

end GlobalTheory.CompanionTheory.HbBasis
end
end

section


theorem _root_.GlobalTheory.T.length_function_compact : PositivityTheory.RgBcC.VC.LgCpt := by
  first | exact @GlobalTheory.CompanionTheory.LgBound.lgCpt | exact GlobalTheory.CompanionTheory.LgBound.lgCpt | (intros; apply GlobalTheory.CompanionTheory.LgBound.lgCpt <;> assumption)
end

section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise
open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.congruence_action_determinant : ∀ (n : ℕ) (g : Mat n), g.det ≠ 0 → ∃ T : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ), (∀ v, hOf (T v) = g * hOf v * gᴴ) ∧ LinearMap.det T = ‖g.det‖ ^ (2 * n) := by
  first | exact @GlobalTheory.CompanionTheory.ConeLin.cone_lin | exact GlobalTheory.CompanionTheory.ConeLin.cone_lin | (intros; apply GlobalTheory.CompanionTheory.ConeLin.cone_lin <;> assumption)
end

section


theorem _root_.GlobalTheory.T.gelfand_operators_commute : PositivityTheory.RgBcC.GelComm := by
  first | exact @GlobalTheory.CompanionTheory.GelC.gelComm | exact GlobalTheory.CompanionTheory.GelC.gelComm | (intros; apply GlobalTheory.CompanionTheory.GelC.gelComm <;> assumption)
end
