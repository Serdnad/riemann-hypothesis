module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle048
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle052
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.LocalDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle034
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle001
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.PsiApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle033
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem integrable_gauss_one : Integrable (fun s : ℝ => Real.exp (-s ^ 2)) := by
  simpa using integrable_exp_neg_mul_sq (b := 1) one_pos

theorem integral_gauss_one : ∫ s : ℝ, Real.exp (-s ^ 2) = Real.sqrt Real.pi := by
  simpa using integral_gaussian 1

theorem integrable_gauss_prod :
    Integrable (fun y : ℝ × ℝ => Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) :=
  Integrable.mul_prod integrable_gauss_one integrable_gauss_one

theorem integral_gauss_prod :
    ∫ y : ℝ × ℝ, Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2) = Real.pi := by
  rw [Measure.volume_eq_prod, integral_prod_mul (fun s : ℝ => Real.exp (-s ^ 2)) (fun s : ℝ => Real.exp (-s ^ 2)),
    integral_gauss_one, Real.mul_self_sqrt Real.pi_pos.le]

theorem re_dot_pt (x y t : ℝ × ℝ) : (dot (pt x y) t).re = rdot x t := by
  simp [dot, pt, rdot, Complex.mul_re]

theorem norm_phi_le : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (G : ℂ × ℂ → X) (x : ℝ × ℝ) (M : ℝ),
    (∀ y : ℝ × ℝ, ‖G (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) →
    ∀ t : ℝ × ℝ, ‖phi G x t‖ ≤ M * Real.pi * Real.exp (-rdot x t) := by
  intro X _ _ G x M hG t
  have hb : ∀ y : ℝ × ℝ, ‖Complex.exp (-dot (pt x y) t) • G (pt x y)‖ ≤
      M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) := by
    intro y
    rw [norm_smul, Complex.norm_exp, Complex.neg_re, re_dot_pt]
    calc Real.exp (-rdot x t) * ‖G (pt x y)‖
        ≤ Real.exp (-rdot x t) * (M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) :=
          mul_le_mul_of_nonneg_left (hG y) (Real.exp_pos _).le
      _ = M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) := by
          rw [neg_add, Real.exp_add]; ring
  unfold phi
  calc ‖∫ y : ℝ × ℝ, Complex.exp (-dot (pt x y) t) • G (pt x y)‖
      ≤ ∫ y : ℝ × ℝ, M * Real.exp (-rdot x t) * (Real.exp (-y.1 ^ 2) * Real.exp (-y.2 ^ 2)) :=
        norm_integral_le_of_norm_le (Integrable.const_mul integrable_gauss_prod _) (Eventually.of_forall hb)
    _ = M * Real.pi * Real.exp (-rdot x t) := by
        rw [integral_const_mul, integral_gauss_prod]; ring

end GlobalTheory.CompanionTheory.TubeFourier
end

section

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier

theorem integrable_exp_neg_mul_abs_alt {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-c * |x|)) :=
  _root_.UpperTheory.Reformulated.B.Yha4.main hc

theorem integrable_exp_neg_mul_abs_add {c : ℝ} (hc : 0 < c) (M : ℝ) :
    Integrable (fun t : ℝ × ℝ => M * Real.exp (-c * (|t.1| + |t.2|))) := by
  have h := (integrable_exp_neg_mul_abs_alt hc).mul_prod (integrable_exp_neg_mul_abs_alt hc)
  refine (h.const_mul M).congr (Eventually.of_forall fun t => ?_)
  simp only [mul_add, Real.exp_add]

theorem norm_cexp_dot (l : ℂ × ℂ) (t : ℝ × ℝ) :
    ‖Complex.exp (dot l t)‖ = Real.exp (rdot (l.1.re, l.2.re) t) := by
  rw [Complex.norm_exp]
  simp [dot, rdot]

theorem inv_continuous_joint : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type)
    [TopologicalSpace T] [FirstCountableTopology T] (φ : ℝ × ℝ → T → X), ExpDecay φ →
    Continuous (fun p : (ℝ × ℝ) × T => φ p.1 p.2) →
    Continuous (fun y : (ℂ × ℂ) × T => inv (fun t => φ t y.2) y.1) := by
  intro X _ _ T _ _ φ hD hφ
  rw [continuous_iff_continuousAt]
  rintro ⟨l₀, g₀⟩
  obtain ⟨ε, hε, U, hU, M, hM⟩ := hD (l₀.1.re, l₀.2.re) g₀
  have hcont : ∀ g : T, Continuous fun t : ℝ × ℝ => φ t g := fun g =>
    hφ.comp (Continuous.prodMk continuous_id continuous_const)
  have hdot : ∀ t : ℝ × ℝ, Continuous fun l : ℂ × ℂ => Complex.exp (dot l t) := fun t => by
    unfold dot
    fun_prop
  have hdot' : ∀ l : ℂ × ℂ, Continuous fun t : ℝ × ℝ => Complex.exp (dot l t) := fun l => by
    unfold dot
    have h1 : Continuous fun t : ℝ × ℝ => ((t.1 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp continuous_fst
    have h2 : Continuous fun t : ℝ × ℝ => ((t.2 : ℝ) : ℂ) :=
      Complex.continuous_ofReal.comp continuous_snd
    fun_prop
  have hnear : ∀ᶠ y : (ℂ × ℂ) × T in 𝓝 (l₀, g₀),
      |y.1.1.re - l₀.1.re| ≤ ε ∧ |y.1.2.re - l₀.2.re| ≤ ε ∧ y.2 ∈ U := by
    have c1 : Continuous fun y : (ℂ × ℂ) × T => |y.1.1.re - l₀.1.re| := by fun_prop
    have c2 : Continuous fun y : (ℂ × ℂ) × T => |y.1.2.re - l₀.2.re| := by fun_prop
    have e1 : ∀ᶠ y : (ℂ × ℂ) × T in 𝓝 (l₀, g₀), |y.1.1.re - l₀.1.re| < ε :=
      c1.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
    have e2 : ∀ᶠ y : (ℂ × ℂ) × T in 𝓝 (l₀, g₀), |y.1.2.re - l₀.2.re| < ε :=
      c2.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
    have e3 : ∀ᶠ y : (ℂ × ℂ) × T in 𝓝 (l₀, g₀), y.2 ∈ U :=
      continuous_snd.continuousAt.eventually (p := (· ∈ U)) hU
    filter_upwards [e1, e2, e3] with y a b c using ⟨a.le, b.le, c⟩
  have key : ContinuousAt (fun y : (ℂ × ℂ) × T =>
      ∫ t : ℝ × ℝ, Complex.exp (dot y.1 t) • φ t y.2) (l₀, g₀) := by
    refine continuousAt_of_dominated (bound := fun t => M * Real.exp (-ε * (|t.1| + |t.2|)))
      (Eventually.of_forall fun y => ((hdot' y.1).smul (hcont y.2)).aestronglyMeasurable)
      ?_ (integrable_exp_neg_mul_abs_add hε M)
      (Eventually.of_forall fun t => ?_)
    · filter_upwards [hnear] with y hy
      refine Eventually.of_forall fun t => ?_
      have hb := hM (y.1.1.re, y.1.2.re) hy.1 hy.2.1 y.2 hy.2.2 t
      rw [norm_smul, norm_cexp_dot]
      have hp := Real.exp_pos (rdot (y.1.1.re, y.1.2.re) t)
      calc Real.exp (rdot (y.1.1.re, y.1.2.re) t) * ‖φ t y.2‖
          ≤ Real.exp (rdot (y.1.1.re, y.1.2.re) t) *
            (M * Real.exp (-rdot (y.1.1.re, y.1.2.re) t) * Real.exp (-ε * (|t.1| + |t.2|))) := by
            gcongr
        _ = M * (Real.exp (rdot (y.1.1.re, y.1.2.re) t) * Real.exp (-rdot (y.1.1.re, y.1.2.re) t)) *
            Real.exp (-ε * (|t.1| + |t.2|)) := by ring
        _ = M * Real.exp (-ε * (|t.1| + |t.2|)) := by
            rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    · have h1 : Continuous fun y : (ℂ × ℂ) × T => Complex.exp (dot y.1 t) :=
        (hdot t).comp continuous_fst
      have h2 : Continuous fun y : (ℂ × ℂ) × T => φ t y.2 :=
        hφ.comp (Continuous.prodMk continuous_const continuous_snd)
      exact (h1.smul h2).continuousAt
  exact continuousAt_const.smul key

end GlobalTheory.CompanionTheory.TubeFourier
end
end

section

noncomputable section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
open scoped FourierTransform

namespace GlobalTheory.CompanionTheory.TubeFourier

def planeCoord : EuclideanSpace ℝ (Fin 2) ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).symm.trans MeasurableEquiv.finTwoArrow

theorem planeCoord_apply (v : EuclideanSpace ℝ (Fin 2)) : planeCoord v = (v 0, v 1) := rfl

theorem continuous_planeCoord : Continuous planeCoord := by
  rw [show (planeCoord : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ) = fun v => (v 0, v 1) from funext planeCoord_apply]
  fun_prop

theorem measurePreserving_planeCoord : MeasurePreserving planeCoord volume volume := by
  exact (volume_preserving_finTwoArrow ℝ).comp (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2))

theorem inner_eq_rdot (v w : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ v w = rdot (planeCoord v) (planeCoord w) := by
  rw [planeCoord_apply, planeCoord_apply]
  simp [rdot, PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

theorem fourier_comp_planeCoord {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (h : ℝ × ℝ → X) (w : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (fun v => h (planeCoord v)) w =
      ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y ((2 * Real.pi) • planeCoord w) : ℝ) : ℂ))) • h y := by
  rw [Real.fourier_eq', ← measurePreserving_planeCoord.integral_comp'
    (fun y : ℝ × ℝ => Complex.exp (-(Complex.I * ((rdot y ((2 * Real.pi) • planeCoord w) : ℝ) : ℂ))) • h y)]
  congr 1
  ext v
  rw [inner_eq_rdot]
  congr 2
  simp only [rdot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  push_cast
  ring

theorem fourier_inversion_prod : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (h : ℝ × ℝ → X), Continuous h → Integrable h → Integrable (fun t : ℝ × ℝ => ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • h y) → ∀ y : ℝ × ℝ, h y = (((2 * Real.pi) ^ 2 : ℂ)⁻¹) • ∫ t : ℝ × ℝ, Complex.exp (Complex.I * ((rdot y t : ℝ) : ℂ)) • ∫ y' : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y' t : ℝ) : ℂ))) • h y' := by
  intro X _ _ _ h hc hi hT y
  set T : ℝ × ℝ → X := fun t => ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • h y with hTdef
  set f : EuclideanSpace ℝ (Fin 2) → X := fun v => h (planeCoord v) with hf
  have hfc : Continuous f := hc.comp continuous_planeCoord
  have hfi : Integrable f :=
    (measurePreserving_planeCoord.integrable_comp_emb planeCoord.measurableEmbedding).mpr hi
  have hFf : ∀ w, 𝓕 f w = T ((2 * Real.pi) • planeCoord w) := fun w => fourier_comp_planeCoord h w
  have hFi : Integrable (𝓕 f) := by
    rw [show 𝓕 f = fun w => T ((2 * Real.pi) • planeCoord w) from funext hFf]
    have h1 : Integrable (fun t : ℝ × ℝ => T ((2 * Real.pi) • t)) := hT.comp_smul (by positivity)
    exact (measurePreserving_planeCoord.integrable_comp_emb planeCoord.measurableEmbedding).mpr h1
  have hinv := congrFun (hfc.fourierInv_fourier_eq hfi hFi) (planeCoord.symm y)
  have hsub := Measure.integral_comp_smul (μ := (volume : Measure (ℝ × ℝ)))
    (f := fun t => Complex.exp (Complex.I * ((rdot y t : ℝ) : ℂ)) • T t) (R := 2 * Real.pi)
  have hrank : Module.finrank ℝ (ℝ × ℝ) = 2 := by simp
  rw [hrank] at hsub
  have hlhs : 𝓕⁻ (𝓕 f) (planeCoord.symm y) = ∫ s : ℝ × ℝ,
      (fun t => Complex.exp (Complex.I * ((rdot y t : ℝ) : ℂ)) • T t) ((2 * Real.pi) • s) := by
    rw [Real.fourierInv_eq', ← measurePreserving_planeCoord.integral_comp'
      (fun s : ℝ × ℝ => (fun t => Complex.exp (Complex.I * ((rdot y t : ℝ) : ℂ)) • T t) ((2 * Real.pi) • s))]
    congr 1
    ext w
    simp only [hFf, inner_eq_rdot, MeasurableEquiv.apply_symm_apply]
    congr 2
    simp only [rdot, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    push_cast
    ring
  rw [hinv] at hlhs
  have hy : h y = f (planeCoord.symm y) := by simp [hf]
  rw [hy, hlhs, hsub, abs_of_pos (by positivity), ← Complex.coe_smul]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.TubeFourier
end
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

namespace GlobalTheory.CompanionTheory.SiegLoc.NuDiag

private theorem card_range_vecMul_mul_mul_eq_of_mul_eq_one {Q : Type} [CommRing Q] {n : ℕ}
    (H P P' G G' : Matrix (Fin n) (Fin n) Q) (hP : P' * P = 1) (hG : G * G' = 1) :
    Nat.card (Set.range fun z : Fin n → Q => Matrix.vecMul z (P * H * G)) =
      Nat.card (Set.range fun x : Fin n → Q => Matrix.vecMul x H) := by
  have hinj : Function.Injective fun y : Fin n → Q => Matrix.vecMul y G := by
    intro y₁ y₂ hy
    have h := congrArg (fun v => Matrix.vecMul v G') hy
    simpa only [Matrix.vecMul_vecMul, hG, Matrix.vecMul_one] using h
  have hrange : (Set.range fun z : Fin n → Q => Matrix.vecMul z (P * H * G)) =
      (fun y => Matrix.vecMul y G) '' Set.range fun x : Fin n → Q => Matrix.vecMul x H := by
    ext v
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨Matrix.vecMul (Matrix.vecMul z P) H, ⟨Matrix.vecMul z P, rfl⟩,
        by simp only [Matrix.vecMul_vecMul]⟩
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨Matrix.vecMul x P', by
        simp only [Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hP, Matrix.one_mul]⟩
  rw [hrange, Nat.card_image_of_injective hinj]

theorem cT_mul' {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} (a b : Matrix (Fin n) (Fin n) R) :
    cT σ (a * b) = cT σ b * cT σ a := by
  simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one' {R : Type} [CommRing R] (σ : R →+* R) {n : ℕ} :
    cT σ (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp only [PositivityTheory.PfSWUS.Loc.cT, Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem red_mul' {R : Type} [CommRing R] (ϖ : R) (k : ℕ) {n : ℕ} (a b : Matrix (Fin n) (Fin n) R) :
    red ϖ k (a * b) = red ϖ k a * red ϖ k b := by
  simp only [PositivityTheory.PfSWUS.Loc.red, Matrix.map_mul]

theorem red_one' {R : Type} [CommRing R] (ϖ : R) (k : ℕ) {n : ℕ} :
    red ϖ k (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp only [PositivityTheory.PfSWUS.Loc.red]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem card_range_vecMul_diagonal {A : Type} [CommRing A] {n : ℕ} (e : Fin n → A) :
    Nat.card (Set.range fun z : Fin n → A => Matrix.vecMul z (Matrix.diagonal e)) =
      ∏ i : Fin n, Nat.card (Set.range fun w : A => w * e i) := by
  have hset : (Set.range fun z : Fin n → A => Matrix.vecMul z (Matrix.diagonal e)) =
      Set.pi Set.univ (fun i => Set.range fun w : A => w * e i) := by
    ext v
    simp only [Set.mem_range, Set.mem_univ_pi]
    constructor
    · rintro ⟨z, rfl⟩ i
      exact ⟨z i, by rw [Matrix.vecMul_diagonal]⟩
    · intro hv
      choose z hz using hv
      exact ⟨z, funext fun i => by rw [Matrix.vecMul_diagonal, hz i]⟩
  rw [hset, Nat.card_congr (Equiv.Set.univPi _), Nat.card_pi]

theorem nuAt_eq_prod : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R), σ ϖ = ϖ → (∀ a, σ (σ a) = a) → ∀ (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (n : ℕ) (h g g' : Matrix (Fin n) (Fin n) R) (d : Fin n → R), g * g' = 1 → g' * g = 1 → cT σ g * h * g = Matrix.diagonal d → nuAt ϖ (red ϖ k h) = ∏ i : Fin n, Nat.card (Set.range fun w : R ⧸ lev ϖ k => w * Ideal.Quotient.mk (lev ϖ k) (d i)) := by
  intro R _ σ ϖ _ _ k _ n h g g' d hgg' hg'g hdiag
  have hP : PositivityTheory.PfSWUS.Loc.red ϖ k (PositivityTheory.PfSWUS.Loc.cT σ g') *
      PositivityTheory.PfSWUS.Loc.red ϖ k (PositivityTheory.PfSWUS.Loc.cT σ g) = 1 := by
    rw [← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', ← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.cT_mul', hgg',
      GlobalTheory.CompanionTheory.SiegLoc.NuDiag.cT_one', GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_one']
  have hG : PositivityTheory.PfSWUS.Loc.red ϖ k g * PositivityTheory.PfSWUS.Loc.red ϖ k g' = 1 := by
    rw [← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', hgg', GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_one']
  have hD : PositivityTheory.PfSWUS.Loc.red ϖ k (PositivityTheory.PfSWUS.Loc.cT σ g) * PositivityTheory.PfSWUS.Loc.red ϖ k h *
      PositivityTheory.PfSWUS.Loc.red ϖ k g =
        Matrix.diagonal fun i => Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) (d i) := by
    rw [← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', ← GlobalTheory.CompanionTheory.SiegLoc.NuDiag.red_mul', hdiag]
    simp only [PositivityTheory.PfSWUS.Loc.red]
    exact Matrix.diagonal_map (map_zero _)
  unfold PositivityTheory.PfSWUS.Loc.nuAt
  refine Eq.trans ?_ (GlobalTheory.CompanionTheory.SiegLoc.NuDiag.card_range_vecMul_diagonal
    (fun i => Ideal.Quotient.mk (PositivityTheory.PfSWUS.Loc.lev ϖ k) (d i)))
  rw [← hD]
  exact (card_range_vecMul_mul_mul_eq_of_mul_eq_one _ _ _ _ _ hP hG).symm

end GlobalTheory.CompanionTheory.SiegLoc.NuDiag
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.absolutely_closed_polynomial_splits : ∀ {S : Type} [CommRing S] , Aic (S := S) → ∀ P : Polynomial S, P.Monic → ∃ s : Multiset S, P = (s.map fun b => Polynomial.X - Polynomial.C b).prod := by
  first | exact @GlobalTheory.CompanionTheory.MonicSplit.monic_splits | exact GlobalTheory.CompanionTheory.MonicSplit.monic_splits | (intros; apply GlobalTheory.CompanionTheory.MonicSplit.monic_splits <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.localization_preserves_closedness : ∀ {S : Type} [CommRing S] (ϖ : S), (Val ϖ → Loc S ∧ Loc (Localization.Away ϖ)) ∧ (Aic S → Aic (Localization.Away ϖ)) := by
  first | exact @GlobalTheory.CompanionTheory.LocAic.main | exact GlobalTheory.CompanionTheory.LocAic.main | (intros; apply GlobalTheory.CompanionTheory.LocAic.main <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.newton_polygon_slope_existence : ∀ {S : Type} [CommRing S] (ϖ : S), Dich ϖ → Roots ϖ → ∀ (q : ℕ → S) (d M : ℕ), 0 < d → q d = 1 → q 0 ∣ ϖ ^ M → ∃ c : S, (∀ i, 1 ≤ i → i ≤ d → q 0 ∣ q i * c ^ i) ∧ ∃ i, 1 ≤ i ∧ i ≤ d ∧ q i * c ^ i ∣ q 0 := by
  first | exact @GlobalTheory.CompanionTheory.NewtonSlope.first_slope | exact GlobalTheory.CompanionTheory.NewtonSlope.first_slope | (intros; apply GlobalTheory.CompanionTheory.NewtonSlope.first_slope <;> assumption)
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.CompDich

theorem one_sub_mem_compI {S : Type} [CommRing S] {P : Ideal S} (hP : P.IsPrime) {e : S}
    (he : IsIdempotentElem e) (heP : e ∉ P) : 1 - e ∈ compI P := by
  refine Ideal.subset_span ⟨he.one_sub, ?_⟩
  have h0 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
  have h1 : e * (1 - e) ∈ P := by rw [h0]; exact P.zero_mem
  exact (hP.mem_or_mem h1).resolve_left heP

theorem dich_comp : ∀ {S : Type} [CommRing S] (ϖ : S) (P : Ideal S), P.IsPrime →
    (Val ϖ → Dich (Ideal.Quotient.mk (compI P) ϖ)) ∧
    (ϖ ∈ nonZeroDivisors S → Ideal.Quotient.mk (compI P) ϖ ∈ nonZeroDivisors (S ⧸ compI P)) := by
  intro S _ ϖ P hP
  refine ⟨fun hV => ?_, fun hϖ => ?_⟩
  · rintro f g ⟨N, hN⟩
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective f
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective g
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 hN
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    have h1 : ϖ ^ N - (a * f + b * g) ∈ compI P := by
      rw [← Ideal.Quotient.eq]
      simpa only [map_add (f := _), map_mul, map_pow] using hab.symm
    obtain ⟨e, he, heP, hez⟩ := (GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff P hP _).1 h1
    have hc := one_sub_mem_compI hP he heP
    have hee : e * e = e := he
    have hff : Ideal.Quotient.mk (compI P) (e * f + (1 - e)) = Ideal.Quotient.mk (compI P) f := by
      rw [Ideal.Quotient.eq]
      have h2 : e * f + (1 - e) - f = (1 - f) * (1 - e) := by ring
      rw [h2]
      exact Ideal.mul_mem_left _ _ hc
    have hmem : ϖ ^ N ∈ Ideal.span {e * f + (1 - e), g} := by
      refine Ideal.mem_span_pair.2 ⟨a * e + (1 - e) * ϖ ^ N, b * e, ?_⟩
      linear_combination (a * f - a - ϖ ^ N * f + ϖ ^ N) * hee - hez
    obtain ⟨e1, he1, h2, h3⟩ := hV (e * f + (1 - e)) g ⟨N, hmem⟩
    rw [Ideal.mem_span_singleton] at h2 h3
    by_cases h : e1 ∈ P
    · right
      have h0 : Ideal.Quotient.mk (compI P) e1 = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span ⟨he1, h⟩)
      obtain ⟨c, hc'⟩ := h3
      refine ⟨Ideal.Quotient.mk (compI P) c, ?_⟩
      rw [← hff, ← map_mul, ← hc', map_mul, map_sub, h0, map_one, sub_zero, one_mul]
    · left
      have h0 : Ideal.Quotient.mk (compI P) (1 - e1) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (one_sub_mem_compI hP he1 h)
      have h1' : Ideal.Quotient.mk (compI P) e1 = 1 := by
        rw [map_sub, map_one] at h0
        exact (sub_eq_zero.1 h0).symm
      obtain ⟨c, hc'⟩ := h2
      refine ⟨Ideal.Quotient.mk (compI P) c, ?_⟩
      rw [← hff, ← map_mul, ← hc', map_mul, h1', one_mul]
  · refine mem_nonZeroDivisors_iff_right.2 fun x hx => ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : x * ϖ ∈ compI P := Ideal.Quotient.eq_zero_iff_mem.1 (by rwa [map_mul])
    obtain ⟨e, he, heP, hez⟩ := (GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff P hP _).1 h1
    have h2 : e * x = 0 :=
      (mul_right_mem_nonZeroDivisors_eq_zero_iff hϖ).1 (by rw [mul_assoc]; exact hez)
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff P hP x).2 ⟨e, he, heP, h2⟩)

end GlobalTheory.CompanionTheory.CompDich
end

section

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

theorem _root_.GlobalTheory.T.mem_idempotent_complement_iff : ∀ {S : Type} [CommRing S] (P : Ideal S), P.IsPrime → ∀ x : S, x ∈ compI P ↔ ∃ e, IsIdempotentElem e ∧ e ∉ P ∧ e * x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff | exact GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff | (intros; apply GlobalTheory.CompanionTheory.CompIdeal.mem_compI_iff <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.GlobalTheory.T.algebraic_over_torus_of_integral : ∀ {K R : Type} [Field K] [CommRing R] [IsDomain R] [Algebra K R] {d : ℕ} (t : Fin d → Rˣ), (∀ r : R, IsIntegral (torusS K t Finset.univ) r) → Algebra.IsAlgebraic (Algebra.adjoin K (Set.range fun k => (t k : R))) R := by
  first | exact @GlobalTheory.CompanionTheory.GeoTorus.isAlgebraic_of_integral_torusS | exact GlobalTheory.CompanionTheory.GeoTorus.isAlgebraic_of_integral_torusS | (intros; apply GlobalTheory.CompanionTheory.GeoTorus.isAlgebraic_of_integral_torusS <;> assumption)
end

section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

theorem _root_.GlobalTheory.T.trace_pairing_galois_equivariant : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ (σA : A →+* A) (σC : C₀ →+* C₀) (gT : A ⊗[W] L →+ A ⊗[W] L), (∀ a y, gT (a ⊗ₜ y) = σA a ⊗ₜ y) → (∀ a, σC (c a) = c (σA a)) → (∀ x, σC (k x) = k x) → ∀ (f : Module.Dual K₀ (K₀ ⊗[W] L)) (z : A ⊗[W] L), T c k hk f (gT z) = σC (T c k hk f z) := by
  first | exact @GlobalTheory.CompanionTheory.FrobPairing.T_gal | exact GlobalTheory.CompanionTheory.FrobPairing.T_gal | (intros; apply GlobalTheory.CompanionTheory.FrobPairing.T_gal <;> assumption)
end

section

open TensorProduct CrystallineSemistableComparison.Pb.Psi

theorem _root_.GlobalTheory.T.trace_pairing_smul_left : ∀ {W A C₀ : Type} [CommRing W] [CommRing A] [CommRing C₀] [Algebra W A] {K₀ : Type} [Field K₀] [Algebra W K₀] {L : Type 1} [AddCommGroup L] [Module W L] (c : A →+* C₀) (k : K₀ →+* C₀) (hk : ∀ w : W, k (algebraMap W K₀ w) = c (algebraMap W A w)), ∀ (f : Module.Dual K₀ (K₀ ⊗[W] L)) (a : A) (z : A ⊗[W] L), T c k hk f (a • z) = c a * T c k hk f z := by
  first | exact @GlobalTheory.CompanionTheory.FrobPairing.T_smul | exact GlobalTheory.CompanionTheory.FrobPairing.T_smul | (intros; apply GlobalTheory.CompanionTheory.FrobPairing.T_smul <;> assumption)
end
