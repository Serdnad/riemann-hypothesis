module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import GroundTheory.GlobalFields.TateThesis.Bundle001
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SchwartzBilinear.ExistsEquivInnerOfNondegenerate
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle004
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle007
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Instances.Matrix
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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

@[expose] public section

section

open scoped Matrix SchwartzMap

theorem _root_.GlobalTheory.T.schwartz_linear_change : ∀ (m n : ℕ) (c : ℂ) (a : Matrix (Fin n) (Fin n) ℂ), IsUnit a.det → ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ⇑ψ = fun u => c * φ (Matrix.of u * a) := by
  first | exact @GlobalTheory.CompanionTheory.KlocopSw.exists_schwartz_rightMul | exact GlobalTheory.CompanionTheory.KlocopSw.exists_schwartz_rightMul | (intros; apply GlobalTheory.CompanionTheory.KlocopSw.exists_schwartz_rightMul <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.PolyGaussSchwartz

variable {m n : ℕ}

def coord (k : Fin m × Fin n × Bool) (u : Fin m → Fin n → ℂ) : ℂ :=
  if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1

def entryL (a : Fin m) (i : Fin n) : (Fin m → Fin n → ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) i).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => Fin n → ℂ) a)

theorem coord_temperate (k : Fin m × Fin n × Bool) :
    Function.HasTemperateGrowth (coord k) := by
  obtain ⟨a, i, b⟩ := k
  cases b
  · exact (entryL a i).hasTemperateGrowth
  · exact ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (entryL a i)).hasTemperateGrowth

theorem eval_temperate (P : MvPolynomial (Fin m × Fin n × Bool) ℂ) :
    Function.HasTemperateGrowth (fun u => MvPolynomial.eval (fun k => coord k u) P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : (fun u : Fin m → Fin n → ℂ =>
        MvPolynomial.eval (fun k => coord k u) (MvPolynomial.C a)) = fun _ => a := by
      funext u; simp
    rw [this]; exact Function.HasTemperateGrowth.const a
  | add p q hp hq =>
    have : (fun u : Fin m → Fin n → ℂ => MvPolynomial.eval (fun k => coord k u) (p + q)) =
        fun u => MvPolynomial.eval (fun k => coord k u) p +
          MvPolynomial.eval (fun k => coord k u) q := by
      funext u; simp
    rw [this]; exact hp.add hq
  | mul_X p k hp =>
    have : (fun u : Fin m → Fin n → ℂ =>
        MvPolynomial.eval (fun k => coord k u) (p * MvPolynomial.X k)) =
        fun u => MvPolynomial.eval (fun k => coord k u) p * coord k u := by
      funext u; simp
    rw [this]; exact hp.mul (coord_temperate k)

def toEuclid (m n : ℕ) : (Fin m → Fin n → ℂ) ≃L[ℝ] PiLp 2 (fun _ : Fin m × Fin n => ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    (((LinearEquiv.curry ℝ ℂ (Fin m) (Fin n)).symm.trans
      (WithLp.linearEquiv 2 ℝ (Fin m × Fin n → ℂ)).symm).trans
      (LinearEquiv.smulOfNeZero ℝ _ (√2) (by positivity)))

theorem norm_toEuclid_sq (u : Fin m → Fin n → ℂ) :
    ‖toEuclid m n u‖ ^ 2 = 2 * ∑ a, ∑ i, ‖u a i‖ ^ 2 := by
  have h : toEuclid m n u = (√2 : ℝ) • (WithLp.toLp 2 (fun p : Fin m × Fin n => u p.1 p.2) :
      PiLp 2 (fun _ : Fin m × Fin n => ℂ)) := rfl
  rw [h, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by positivity),
    PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]

theorem exists_gauss : ∃ g : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u,
    g u = Complex.exp (-(2 * Real.pi * ∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ)) := by
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (toEuclid m n)
    (GroundTheory.Global.gaussianSchwartz (PiLp 2 (fun _ : Fin m × Fin n => ℂ))), fun u => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, norm_toEuclid_sq, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

theorem exists_schwartz_poly_mul_gauss (m n : ℕ) (P : MvPolynomial (Fin m × Fin n × Bool) ℂ) :
    ∃ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
      ⇑φ = fun u => MvPolynomial.eval (fun k => if k.2.2 then star (u k.1 k.2.1) else u k.1 k.2.1) P *
        Complex.exp (-(2 * Real.pi * ∑ a, ∑ i, ‖u a i‖ ^ 2 : ℝ)) := by
  obtain ⟨g, hg⟩ := exists_gauss (m := m) (n := n)
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u => MvPolynomial.eval (fun k => coord k u) P) g, ?_⟩
  funext u
  rw [SchwartzMap.smulLeftCLM_apply_apply (eval_temperate P), hg, smul_eq_mul]
  rfl

end GlobalTheory.CompanionTheory.PolyGaussSchwartz
end
end

section

open scoped Matrix SchwartzMap FourierTransform RealInnerProductSpace
open MeasureTheory

namespace GlobalTheory.CompanionTheory.FourierMatrix

theorem exists_schwartz_bilinear_transform {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    [μ.IsAddHaarMeasure] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hB : ∀ u, (∀ v, B u v = 0) → u = 0)
    (φ : 𝓢(V, ℂ)) :
    ∃ ψ : 𝓢(V, ℂ), ⇑ψ = fun u =>
      ∫ v, Complex.exp (2 * Real.pi * Complex.I * ((B u v : ℝ) : ℂ)) * φ v ∂μ :=
  _root_.UpperTheory.Reformulated.B.P6.r12b.GlobalTheory.CompanionTheory.FourierMatrix.exists_schwartz_bilinear_transform μ B hB φ

theorem trace_conjTranspose_mul (m n : ℕ) (u v : Fin m → Fin n → ℂ) :
    Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v) = ∑ j, ∑ i, star (u i j) * v i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]

noncomputable def traceForm (m n : ℕ) (s : ℂ) :
    (Fin m → Fin n → ℂ) →ₗ[ℝ] (Fin m → Fin n → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun u v => (s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re)
    (by
      intro a b c
      simp only [trace_conjTranspose_mul, Pi.add_apply, star_add, add_mul,
        Finset.sum_add_distrib, mul_add, Complex.add_re])
    (by
      intro r a b
      have : ∑ j, ∑ i, star ((r • a) i j) * b i j
          = (r : ℂ) * ∑ j, ∑ i, star (a i j) * b i j := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        simp [Complex.real_smul, mul_assoc]
      rw [trace_conjTranspose_mul, trace_conjTranspose_mul, this, mul_left_comm,
        Complex.re_ofReal_mul, smul_eq_mul])
    (by
      intro a b c
      simp only [trace_conjTranspose_mul, Pi.add_apply, mul_add,
        Finset.sum_add_distrib, Complex.add_re])
    (by
      intro r a b
      have : ∑ j, ∑ i, star (a i j) * (r • b) i j
          = (r : ℂ) * ∑ j, ∑ i, star (a i j) * b i j := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.smul_apply, Complex.real_smul]
        ring
      rw [trace_conjTranspose_mul, trace_conjTranspose_mul, this, mul_left_comm,
        Complex.re_ofReal_mul, smul_eq_mul])

theorem traceForm_apply (m n : ℕ) (s : ℂ) (u v : Fin m → Fin n → ℂ) :
    traceForm m n s u v = (s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re := rfl

theorem traceForm_nondegenerate (m n : ℕ) (s : ℂ) (hs : s ≠ 0) (u : Fin m → Fin n → ℂ)
    (h : ∀ v, traceForm m n s u v = 0) : u = 0 := by
  have h0 := h (fun i j => star s * u i j)
  rw [traceForm_apply, trace_conjTranspose_mul] at h0
  have h1 : s * ∑ j, ∑ i, star (u i j) * (star s * u i j)
      = ((Complex.normSq s * ∑ j, ∑ i, Complex.normSq (u i j) : ℝ) : ℂ) := by
    push_cast
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring
  rw [h1, Complex.ofReal_re] at h0
  have hsn : Complex.normSq s ≠ 0 := by simpa [Complex.normSq_eq_zero] using hs
  have h2 : ∑ j, ∑ i, Complex.normSq (u i j) = 0 := by
    rcases mul_eq_zero.mp h0 with h3 | h3
    · exact absurd h3 hsn
    · exact h3
  funext i j
  have h3 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (u i j))).mp h2 j
    (Finset.mem_univ j)
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => Complex.normSq_nonneg (u i j))).mp h3 i (Finset.mem_univ i)
  simpa [Complex.normSq_eq_zero] using h4

theorem exists_schwartz_trace_transform :
    ∀ (m n : ℕ) (C s : ℂ), s ≠ 0 → ∀ φ : SchwartzMap (Fin m → Fin n → ℂ) ℂ,
      ∃ ψ : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ⇑ψ = fun u => C * ∫ v : Fin m → Fin n → ℂ,
        Complex.exp (2 * Real.pi * Complex.I *
          ((s * Matrix.trace ((Matrix.of u)ᴴ * Matrix.of v)).re : ℂ)) * φ v := by
  intro m n C s hs φ
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Fin n → ℂ)) :=
    Measure.pi.isAddHaarMeasure _
  haveI : Measure.IsAddHaarMeasure (volume : Measure (Fin m → Fin n → ℂ)) :=
    Measure.pi.isAddHaarMeasure _
  obtain ⟨ψ, hψ⟩ := exists_schwartz_bilinear_transform (volume : Measure (Fin m → Fin n → ℂ))
    (traceForm m n s) (traceForm_nondegenerate m n s hs) φ
  refine ⟨C • ψ, ?_⟩
  funext u
  simp only [SchwartzMap.smul_apply, hψ, smul_eq_mul, traceForm_apply]

end GlobalTheory.CompanionTheory.FourierMatrix
end

section

open Matrix Topology Filter

theorem _root_.GlobalTheory.T.lie_algebra_function_calculus : ∀ {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ), Matrix.diagonal (fun i => (h i : ℂ)) ∈ 𝔤 → (∀ X ∈ 𝔤, ∀ Y ∈ 𝔤, X * Y - Y * X ∈ 𝔤) → ∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤 := by
  first | exact @GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise | exact GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise | (intros; apply GlobalTheory.CompanionTheory.AdProj.mem_of_entrywise <;> assumption)
end

section

open Matrix Topology Filter

theorem _root_.GlobalTheory.T.exists_maximal_abelian_hermitian : ∀ {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)), ∃ 𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ), 𝔞 ≤ 𝔤 ∧ (∀ A ∈ 𝔞, Aᴴ = A) ∧ (∀ A ∈ 𝔞, ∀ B ∈ 𝔞, A * B = B * A) ∧ ∀ Y ∈ 𝔤, Yᴴ = Y → (∀ A ∈ 𝔞, Y * A = A * Y) → Y ∈ 𝔞 := by
  first | exact @GlobalTheory.CompanionTheory.HermitianCommuting.exists_maximal_commuting_hermitian_subspace | exact GlobalTheory.CompanionTheory.HermitianCommuting.exists_maximal_commuting_hermitian_subspace | (intros; apply GlobalTheory.CompanionTheory.HermitianCommuting.exists_maximal_commuting_hermitian_subspace <;> assumption)
end

section

open Matrix Topology Filter

theorem _root_.GlobalTheory.T.exists_regular_element_abelian : ∀ {n : ℕ} (𝔞 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (U : Matrix (Fin n) (Fin n) ℂ), ∃ H ∈ 𝔞, ∀ i j, (Uᴴ * H * U) i i = (Uᴴ * H * U) j j → ∀ A ∈ 𝔞, (Uᴴ * A * U) i i = (Uᴴ * A * U) j j := by
  first | exact @GlobalTheory.CompanionTheory.IwaGen.exists_regular_point | exact GlobalTheory.CompanionTheory.IwaGen.exists_regular_point | (intros; apply GlobalTheory.CompanionTheory.IwaGen.exists_regular_point <;> assumption)
end

section

open Matrix Topology Filter

theorem _root_.GlobalTheory.T.exists_skewHermitian_add_blockTriangular : ∀ {n : ℕ} (𝔤 : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (h : Fin n → ℝ), Antitone h → (∀ (f : ℝ → ℝ), ∀ X ∈ 𝔤, (Matrix.of fun i j => (f (h i - h j) : ℂ) * X i j) ∈ 𝔤) → (∀ X ∈ 𝔤, Xᴴ ∈ 𝔤) → (∀ Y ∈ 𝔤, Yᴴ = Y → Matrix.diagonal (fun i => (h i : ℂ)) * Y = Y * Matrix.diagonal (fun i => (h i : ℂ)) → Y.IsDiag) → ∀ X ∈ 𝔤, ∃ A ∈ 𝔤, ∃ B ∈ 𝔤, X = A + B ∧ Aᴴ = -A ∧ B.BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.IwasawaGen.skew_add_upper | exact GlobalTheory.CompanionTheory.IwasawaGen.skew_add_upper | (intros; apply GlobalTheory.CompanionTheory.IwasawaGen.skew_add_upper <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.fundamental_domain_fourier_unfolding : ∀ {A X Y : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A] (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A) [Countable Λ] (𝓖 : Set A) (_ : IsAddFundamentalDomain Λ 𝓖 lam) (_ : lam 𝓖 = 1) [Countable X] (c : X → Y) (y0 : Y) (F : X → A → ℂ) (F0 : A → ℂ) (ch : A → ℂ) (_ : ∀ q, AEStronglyMeasurable (F q) lam) (_ : AEStronglyMeasurable ch lam) (_ : ∀ b, ‖ch b‖ = 1) (_ : ∀ a b, ch (a + b) = ch a * ch b) (_ : ∀ l : Λ, ch l = 1) (M : ℝ) (_ : ∀ b, Summable (fun q => ‖F q b‖) ∧ ∑' q, ‖F q b‖ ≤ M) (τ : Λ → X ≃ X) (_ : ∀ (l : Λ) q b, F q ((l : A) + b) = F (τ l q) b) (_ : ∀ (l : Λ) q, c (τ l q) = c q) (e : Λ → X) (_ : Function.Injective e) (_ : ∀ q, c q = y0 ↔ q ∈ Set.range e) (_ : ∀ (l : Λ) b, F (e l) b = F0 ((l : A) + b)) (_ : ∀ y, y ≠ y0 → ∃ ν, ch ν ≠ 1 ∧ ∀ q, c q = y → ∀ b, F q (ν + b) = F q b), Integrable F0 lam ∧ ∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam = ∫ b, F0 b * ch b ∂lam := by
  first | exact @GlobalTheory.CompanionTheory.UnfoldAbs.unfold_abs | exact GlobalTheory.CompanionTheory.UnfoldAbs.unfold_abs | (intros; apply GlobalTheory.CompanionTheory.UnfoldAbs.unfold_abs <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.haar_measure_split_exact_sequence : ∀ {A A' : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A'] [LocallyCompactSpace A'] [T2Space A'] [SecondCountableTopology A'] [MeasurableSpace A'] [BorelSpace A'] (π : A →+ A') (s : A' →+ A), Continuous π → Continuous s → (∀ x, π (s x) = x) → ∀ (Γ : AddSubgroup A) (Γ' : AddSubgroup A'), Countable Γ → Countable Γ' → (∀ γ ∈ Γ, π γ ∈ Γ') → (∀ γ ∈ Γ', s γ ∈ Γ) → ∀ (lam : Measure A) (lam' : Measure A'), lam.IsAddHaarMeasure → lam'.IsAddHaarMeasure → ∀ (𝓖 : Set A) (𝓖' : Set A'), IsAddFundamentalDomain Γ 𝓖 lam → lam 𝓖 = 1 → IsAddFundamentalDomain Γ' 𝓖' lam' → lam' 𝓖' = 1 → ∀ G : A' → ℂ, Continuous G → (∀ γ ∈ Γ', ∀ x, G (γ + x) = G x) → ∫ x in 𝓖, G (π x) ∂lam = ∫ x in 𝓖', G x ∂lam' := by
  first | exact @GlobalTheory.CompanionTheory.FiberInt.integral_comp_eq | exact GlobalTheory.CompanionTheory.FiberInt.integral_comp_eq | (intros; apply GlobalTheory.CompanionTheory.FiberInt.integral_comp_eq <;> assumption)
end

section

open MeasureTheory

theorem _root_.GlobalTheory.T.fourier_inversion_invariant_matrix : ∀ (A : Type) [CommRing A] [MeasurableSpace A] (ν : Measure A) [SigmaFinite ν] (ψ : AddChar A ℂ) (ι : Type) [Fintype ι] [DecidableEq ι] (Bm : Matrix ι ι A), Bm.IsSymm → MeasurableEmbedding (fun x : ι → A => Bm.mulVec x) → (Measure.pi fun _ : ι => ν).map (fun x => Bm.mulVec x) = (Measure.pi fun _ : ι => ν) → ∀ (t f : A → ℂ), (∀ y, f y = ∫ x, t x * ψ (x * y) ∂ν) → Integrable f ν → (∀ z, ∫ b, f b * ψ (b * z) ∂ν = t (-z)) → (∀ y, ∫ x : ι → A, (∏ i, t (x i)) * ψ (dotProduct x (Bm.mulVec y)) ∂(Measure.pi fun _ : ι => ν) = ∏ i, f (Bm.mulVec y i)) ∧ Integrable (fun y : ι → A => ∏ i, f (Bm.mulVec y i)) (Measure.pi fun _ : ι => ν) ∧ ∀ z : ι → A, ∫ y : ι → A, (∏ i, f (Bm.mulVec y i)) * ψ (dotProduct y (Bm.mulVec z)) ∂(Measure.pi fun _ : ι => ν) = ∏ i, t (-(z i)) := by
  first | exact @GlobalTheory.CompanionTheory.BigCell.fourier_prod_symm_preserving | exact GlobalTheory.CompanionTheory.BigCell.fourier_prod_symm_preserving | (intros; apply GlobalTheory.CompanionTheory.BigCell.fourier_prod_symm_preserving <;> assumption)
end

section

open MeasureTheory
open scoped ENNReal NNReal Topology

theorem _root_.GlobalTheory.T.lintegral_uniform_near_parameter : ∀ (X P : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace P] [FirstCountableTopology P] (N : ℕ) (e : X ≃+ (Fin N → ℝ)), Continuous e → ∀ (c : P) (m0 : Measure X) (A : P → X →+ X), (∀ s, Continuous (A s)) → (∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x))) → ∀ δ : ℝ, 0 < δ → (∀ᶠ s in nhds c, ∀ x, δ * ‖e x‖ ≤ ‖e (A s x)‖) → ∫⁻ x, ENNReal.ofReal ((1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ))) ∂m0 ≠ ⊤ → ∀ (u : (Fin N → ℝ) → ℂ) (C : ℝ), Continuous u → (∀ y, ‖u y‖ ≤ C * (1 + ‖y‖) ^ (-((N + 1 : ℕ) : ℝ))) → (∀ᶠ s in nhds c, Integrable (fun x => u (e (A s x))) m0) ∧ ContinuousAt (fun s => ∫ x, u (e (A s x)) ∂m0) c := by
  first | exact @GlobalTheory.CompanionTheory.FibSch.integral_comp_additive_continuousAt | exact GlobalTheory.CompanionTheory.FibSch.integral_comp_additive_continuousAt | (intros; apply GlobalTheory.CompanionTheory.FibSch.integral_comp_additive_continuousAt <;> assumption)
end

section

open Matrix Topology Filter

theorem _root_.GlobalTheory.T.exp_block_triangular : ∀ {n : ℕ} (U Y : Matrix (Fin n) (Fin n) ℂ), U ∈ Matrix.unitaryGroup (Fin n) ℂ → (Uᴴ * Y * U).BlockTriangular id → (Uᴴ * NormedSpace.exp Y * U).BlockTriangular id := by
  first | exact @GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_conj_exp | exact GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_conj_exp | (intros; apply GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_conj_exp <;> assumption)
end
