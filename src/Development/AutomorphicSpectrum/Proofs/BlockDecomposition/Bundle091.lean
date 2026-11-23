module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle032
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle048
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle068
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle069
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.FiniteDimensionalHcSpace
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
public import Mathlib.Analysis.Calculus.ParametricIntegral

@[expose] public section

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

theorem _root_.GlobalTheory.T.matrix_gauss_sum_congr_invariance : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ), (∀ a, σ (σ a) = a) → ∀ (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (χ : AddChar (R ⧸ lev ϖ k) ℂ) (m n : ℕ) (h D g g' : Matrix (Fin n) (Fin n) R) (S E p p' : Matrix (Fin m) (Fin m) R), g * g' = 1 → g' * g = 1 → p * p' = 1 → p' * p = 1 → cT σ g * h * g = D → cT σ p * S * p = E → (∑ x : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), χ (Matrix.trace (red ϖ k h * (cT (barσ σ ϖ hf k) x * red ϖ k S * x)))) = ∑ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), χ (Matrix.trace (red ϖ k D * (cT (barσ σ ϖ hf k) y * red ϖ k E * y))) := by
  first | exact @GlobalTheory.CompanionTheory.SiegCov.gauss_cov | exact GlobalTheory.CompanionTheory.SiegCov.gauss_cov | (intros; apply GlobalTheory.CompanionTheory.SiegCov.gauss_cov <;> assumption)
end

section

open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.SiegLoc Filter Topology

theorem _root_.GlobalTheory.T.matrix_gauss_sum_diagonal_factor : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (hf : σ ϖ = ϖ) (k : ℕ) [Fintype (R ⧸ lev ϖ k)] (χ : AddChar (R ⧸ lev ϖ k) ℂ) (m n : ℕ) (D : Fin n → R) (E : Fin m → R), (∑ y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k), χ (Matrix.trace (red ϖ k (Matrix.diagonal D) * (cT (barσ σ ϖ hf k) y * red ϖ k (Matrix.diagonal E) * y)))) = ∏ i : Fin n, ∏ l : Fin m, ∑ w : R ⧸ lev ϖ k, χ (Ideal.Quotient.mk (lev ϖ k) (E l * D i) * (barσ σ ϖ hf k w * w)) := by
  first | exact @GlobalTheory.CompanionTheory.GaussProd.gauss_prod | exact GlobalTheory.CompanionTheory.GaussProd.gauss_prod | (intros; apply GlobalTheory.CompanionTheory.GaussProd.gauss_prod <;> assumption)
end

section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

namespace GlobalTheory.CompanionTheory.TubeFourier.InvLine

theorem integrable_exp_neg_abs_plane {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ × ℝ => Real.exp (-c * |t.1|) * Real.exp (-c * |t.2|)) :=
  (integrable_exp_neg_mul_abs hc).mul_prod (integrable_exp_neg_mul_abs hc)

theorem dot_add_smul (p v : ℂ × ℂ) (τ : ℂ) (t : ℝ × ℝ) :
    dot (p + τ • v) t = dot p t + τ * dot v t := by
  simp [dot]
  ring

theorem norm_cexp_dot (l : ℂ × ℂ) (t : ℝ × ℝ) :
    ‖Complex.exp (dot l t)‖ = Real.exp (rdot (l.1.re, l.2.re) t) := by
  rw [Complex.norm_exp]
  simp [dot, rdot]

theorem norm_dot_le (v : ℂ × ℂ) (t : ℝ × ℝ) :
    ‖dot v t‖ ≤ (‖v.1‖ + ‖v.2‖) * (|t.1| + |t.2|) := by
  have h1 : ‖dot v t‖ ≤ ‖v.1‖ * |t.1| + ‖v.2‖ * |t.2| := by
    refine (norm_add_le _ _).trans ?_
    simp [norm_mul]
  have := norm_nonneg v.1
  have := norm_nonneg v.2
  have := abs_nonneg t.1
  have := abs_nonneg t.2
  nlinarith [mul_nonneg (norm_nonneg v.1) (abs_nonneg t.2), mul_nonneg (norm_nonneg v.2) (abs_nonneg t.1)]

theorem le_two_div_mul_exp {ε s : ℝ} (hε : 0 < ε) : s ≤ 2 / ε * Real.exp (ε / 2 * s) := by
  have h := Real.add_one_le_exp (ε / 2 * s)
  have h2 : s = 2 / ε * (ε / 2 * s) := by field_simp
  have h3 : ε / 2 * s ≤ Real.exp (ε / 2 * s) := by linarith
  calc s = 2 / ε * (ε / 2 * s) := h2
    _ ≤ _ := by gcongr

theorem inv_differentiable_line : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (T : Type) [TopologicalSpace T] (φ : ℝ × ℝ → T → X), ExpDecay φ → (∀ g : T, Continuous fun t => φ t g) → ∀ (g : T) (p v : ℂ × ℂ), Differentiable ℂ (fun τ : ℂ => inv (fun t => φ t g) (p + τ • v)) := by
  intro X _ _ _ T _ φ hφ hc g p v τ₀
  obtain ⟨ε, hε, U, hU, M, hM⟩ := hφ ((p + τ₀ • v).1.re, (p + τ₀ • v).2.re) g
  have hgU : g ∈ U := mem_of_mem_nhds hU
  have hA : 0 < ‖v.1‖ + ‖v.2‖ + 1 := by positivity
  have hr : 0 < ε / (‖v.1‖ + ‖v.2‖ + 1) := div_pos hε hA
  have hre : ∀ τ ∈ Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)), ∀ w : ℂ, ‖w‖ ≤ ‖v.1‖ + ‖v.2‖ + 1 →
      ∀ q : ℂ, |(q + τ * w).re - (q + τ₀ * w).re| ≤ ε := by
    intro τ hτ w hw q
    have h1 : (q + τ * w).re - (q + τ₀ * w).re = ((τ - τ₀) * w).re := by
      simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im]
      ring
    rw [h1]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul]
    have h2 : ‖τ - τ₀‖ ≤ ε / (‖v.1‖ + ‖v.2‖ + 1) := by
      have := Metric.mem_ball.1 hτ
      rw [dist_eq_norm] at this
      exact this.le
    calc ‖τ - τ₀‖ * ‖w‖ ≤ ε / (‖v.1‖ + ‖v.2‖ + 1) * (‖v.1‖ + ‖v.2‖ + 1) := by gcongr
      _ = ε := by field_simp
  have key : ∀ τ ∈ Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)), ∀ t : ℝ × ℝ,
      ‖φ t g‖ ≤ M * Real.exp (-rdot ((p + τ • v).1.re, (p + τ • v).2.re) t)
        * Real.exp (-ε * (|t.1| + |t.2|)) := by
    intro τ hτ t
    refine hM _ ?_ ?_ g hgU t
    · exact hre τ hτ v.1 (by linarith [norm_nonneg v.2]) p.1
    · exact hre τ hτ v.2 (by linarith [norm_nonneg v.1]) p.2
  have hFn : ∀ τ ∈ Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)), ∀ t : ℝ × ℝ,
      ‖Complex.exp (dot (p + τ • v) t) • φ t g‖ ≤ |M| * Real.exp (-ε * (|t.1| + |t.2|)) := by
    intro τ hτ t
    rw [norm_smul, norm_cexp_dot]
    have h1 := key τ hτ t
    have h2 := Real.exp_pos (rdot ((p + τ • v).1.re, (p + τ • v).2.re) t)
    calc _ ≤ Real.exp (rdot ((p + τ • v).1.re, (p + τ • v).2.re) t) *
          (M * Real.exp (-rdot ((p + τ • v).1.re, (p + τ • v).2.re) t)
            * Real.exp (-ε * (|t.1| + |t.2|))) := by gcongr
      _ = M * Real.exp (-ε * (|t.1| + |t.2|)) := by
        rw [Real.exp_neg]
        field_simp
      _ ≤ _ := by gcongr; exact le_abs_self M
  have hcont : ∀ τ : ℂ, Continuous fun t : ℝ × ℝ => Complex.exp (dot (p + τ • v) t) • φ t g := by
    intro τ
    refine Continuous.smul ?_ (hc g)
    simp only [dot]
    fun_prop
  have hdotc : Continuous fun t : ℝ × ℝ => dot v t := by
    unfold dot
    fun_prop
  have hint : Integrable (fun t : ℝ × ℝ => Complex.exp (dot (p + τ₀ • v) t) • φ t g) :=
    (integrable_and_norm_integral_le X (fun t => φ t g) (p + τ₀ • v) ε M hε (hc g)
      (fun t => hM _ (by simp [hε.le]) (by simp [hε.le]) g hgU t)).1
  have hbound : Integrable (fun t : ℝ × ℝ => ((‖v.1‖ + ‖v.2‖) * (2 / ε) * |M|) *
      (Real.exp (-(ε / 2) * |t.1|) * Real.exp (-(ε / 2) * |t.2|))) :=
    (integrable_exp_neg_abs_plane (half_pos hε)).const_mul _
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (ℝ × ℝ)))
    (F := fun (τ : ℂ) (t : ℝ × ℝ) => Complex.exp (dot (p + τ • v) t) • φ t g)
    (F' := fun (τ : ℂ) (t : ℝ × ℝ) => dot v t • (Complex.exp (dot (p + τ • v) t) • φ t g))
    (x₀ := τ₀) (s := Metric.ball τ₀ (ε / (‖v.1‖ + ‖v.2‖ + 1)))
    (bound := fun t : ℝ × ℝ => ((‖v.1‖ + ‖v.2‖) * (2 / ε) * |M|) *
      (Real.exp (-(ε / 2) * |t.1|) * Real.exp (-(ε / 2) * |t.2|)))
    (Metric.ball_mem_nhds _ hr)
    (Eventually.of_forall fun τ => (hcont τ).aestronglyMeasurable)
    hint
    (Continuous.aestronglyMeasurable (Continuous.smul hdotc (hcont τ₀)))
    (ae_of_all _ fun t τ hτ => by
      rw [norm_smul]
      have h1 := norm_dot_le v t
      have h2 := hFn τ hτ t
      have h3 := le_two_div_mul_exp (s := |t.1| + |t.2|) hε
      have h4 : Real.exp (-(ε / 2) * |t.1|) * Real.exp (-(ε / 2) * |t.2|)
          = Real.exp (-(ε / 2) * (|t.1| + |t.2|)) := by
        rw [← Real.exp_add]; congr 1; ring
      have h5 : Real.exp (ε / 2 * (|t.1| + |t.2|)) * Real.exp (-ε * (|t.1| + |t.2|))
          = Real.exp (-(ε / 2) * (|t.1| + |t.2|)) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [h4, ← h5]
      calc _ ≤ ((‖v.1‖ + ‖v.2‖) * (2 / ε * Real.exp (ε / 2 * (|t.1| + |t.2|)))) *
            (|M| * Real.exp (-ε * (|t.1| + |t.2|))) := by
            refine mul_le_mul (h1.trans ?_) h2 (norm_nonneg _) (by positivity)
            gcongr
        _ = _ := by ring)
    hbound
    (ae_of_all _ fun t τ _ => by
      have h1 : HasDerivAt (fun τ : ℂ => Complex.exp (dot (p + τ • v) t))
          (Complex.exp (dot (p + τ • v) t) * dot v t) τ := by
        have h2 : HasDerivAt (fun τ : ℂ => dot p t + τ * dot v t) (dot v t) τ := by
          simpa using ((hasDerivAt_id τ).mul_const (dot v t)).const_add (dot p t)
        have h3 := h2.cexp
        simp only [← dot_add_smul] at h3
        exact h3
      have h4 := h1.smul_const (φ t g)
      rw [smul_smul, mul_comm]
      exact h4)
  exact (hd.2.differentiableAt).const_smul (((2 * Real.pi) ^ 2 : ℂ)⁻¹)

end GlobalTheory.CompanionTheory.TubeFourier.InvLine
end

section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

theorem _root_.GlobalTheory.T.gaussian_tube_transform_continuous : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T] [FirstCountableTopology T] (G : T → ℂ × ℂ → X) (x : ℝ × ℝ), Continuous (fun p : (ℝ × ℝ) × T => G p.2 (pt x p.1)) → (∀ g : T, ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ g' ∈ U, ∀ y : ℝ × ℝ, ‖G g' (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) → Continuous (fun p : (ℝ × ℝ) × T => phi (G p.2) x p.1) := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.phi_joint_continuous | exact GlobalTheory.CompanionTheory.TubeFourier.phi_joint_continuous | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.phi_joint_continuous <;> assumption)
end

section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

theorem _root_.GlobalTheory.T.fourier_inversion_real_plane : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (h : ℝ × ℝ → X), Continuous h → Integrable h → Integrable (fun t : ℝ × ℝ => ∫ y : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y t : ℝ) : ℂ))) • h y) → ∀ y : ℝ × ℝ, h y = (((2 * Real.pi) ^ 2 : ℂ)⁻¹) • ∫ t : ℝ × ℝ, Complex.exp (Complex.I * ((rdot y t : ℝ) : ℂ)) • ∫ y' : ℝ × ℝ, Complex.exp (-(Complex.I * ((rdot y' t : ℝ) : ℂ))) • h y' := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.fourier_inversion_prod | exact GlobalTheory.CompanionTheory.TubeFourier.fourier_inversion_prod | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.fourier_inversion_prod <;> assumption)
end

section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

theorem _root_.GlobalTheory.T.gaussian_tube_transform_bound : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (G : ℂ × ℂ → X) (x : ℝ × ℝ) (M : ℝ), (∀ y : ℝ × ℝ, ‖G (pt x y)‖ ≤ M * Real.exp (-(y.1 ^ 2 + y.2 ^ 2))) → ∀ t : ℝ × ℝ, ‖phi G x t‖ ≤ M * Real.pi * Real.exp (-rdot x t) := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.norm_phi_le | exact GlobalTheory.CompanionTheory.TubeFourier.norm_phi_le | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.norm_phi_le <;> assumption)
end

section

open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier

theorem _root_.GlobalTheory.T.inverse_transform_continuous : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (T : Type) [TopologicalSpace T] [FirstCountableTopology T] (φ : ℝ × ℝ → T → X), ExpDecay φ → Continuous (fun p : (ℝ × ℝ) × T => φ p.1 p.2) → Continuous (fun y : (ℂ × ℂ) × T => inv (fun t => φ t y.2) y.1) := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.inv_continuous_joint | exact GlobalTheory.CompanionTheory.TubeFourier.inv_continuous_joint | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.inv_continuous_joint <;> assumption)
end

section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep

theorem isPat_colGe (d j : ℕ) : IsPat (colGe d j) := by
  refine ⟨fun i h => lt_irrefl _ h.1, ?_⟩
  intro a b c hab hbc
  exact ⟨hab.1.trans hbc.1, hbc.2⟩

def colGeSplit (d j : ℕ) (hj : j < d) :
    Fin j ⊕ {p : Fin d × Fin d // colGe d (j + 1) p.1 p.2} →
      {p : Fin d × Fin d // colGe d j p.1 p.2}
  | Sum.inl i => ⟨(⟨i.1, i.2.trans hj⟩, ⟨j, hj⟩), by
      refine ⟨?_, le_refl _⟩
      exact Fin.mk_lt_mk.2 i.2⟩
  | Sum.inr p => ⟨p.1, p.2.1, Nat.le_of_succ_le p.2.2⟩

theorem colGeSplit_bijective (d j : ℕ) (hj : j < d) : Function.Bijective (colGeSplit d j hj) := by
  constructor
  · rintro (a | a) (b | b) h
    · have h1 := congrArg (fun x => (x.1.1 : Fin d).1) h
      simp only [colGeSplit] at h1
      exact congrArg Sum.inl (Fin.ext h1)
    · have h1 := congrArg (fun x => (x.1.2 : Fin d).1) h
      simp only [colGeSplit] at h1
      have := b.2.2
      omega
    · have h1 := congrArg (fun x => (x.1.2 : Fin d).1) h
      simp only [colGeSplit] at h1
      have := a.2.2
      omega
    · have h1 := congrArg (fun x => x.1) h
      simp only [colGeSplit] at h1
      exact congrArg Sum.inr (Subtype.ext h1)
  · rintro ⟨⟨i, l⟩, hil, hjl⟩
    by_cases e : (l : ℕ) = j
    · have hi : (i : ℕ) < j := by
        have : (i : ℕ) < l := hil
        omega
      refine ⟨Sum.inl ⟨i, hi⟩, ?_⟩
      apply Subtype.ext
      simp only [colGeSplit]
      exact Prod.ext rfl (Fin.ext e.symm)
    · have hl : j + 1 ≤ (l : ℕ) := by
        have : j ≤ (l : ℕ) := hjl
        omega
      exact ⟨Sum.inr ⟨(i, l), hil, hl⟩, rfl⟩

theorem natCard_colGe (d j : ℕ) (hj : j < d) :
    Nat.card {p : Fin d × Fin d // colGe d j p.1 p.2} =
      j + Nat.card {p : Fin d × Fin d // colGe d (j + 1) p.1 p.2} := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (colGeSplit_bijective d j hj)), Nat.card_sum,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem ncard_patSet_colGe (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (hj : j < d) :
    (patSet (K := K) (colGe d j)).ncard =
      Fintype.card K ^ j * (patSet (K := K) (colGe d (j + 1))).ncard := by
  classical
  have card_colGe (k : ℕ) :
      (patSet (K := K) (colGe d k)).ncard =
        Fintype.card K ^ Nat.card {p : Fin d × Fin d // colGe d k p.1 p.2} := by
    let A (f : {p : Fin d × Fin d // colGe d k p.1 p.2} → K) : Matrix (Fin d) (Fin d) K :=
      fun i l => if i = l then 1 else if h : colGe d k i l then f ⟨(i, l), h⟩ else 0
    have hunit (f) : IsUnit (A f).det := by
      have htri : (A f).IsUpperTriangular := by
        intro i l h
        change l < i at h
        have hnot : ¬ colGe d k i l := fun hcol => (not_lt_of_gt h) hcol.1
        simp [A, ne_of_gt h, hnot]
      rw [Matrix.det_of_isUpperTriangular htri]
      simp [A]
    let e : patSet (K := K) (colGe d k) ≃ ({p : Fin d × Fin d // colGe d k p.1 p.2} → K) :=
      { toFun := fun u p => (u.val : Matrix (Fin d) (Fin d) K) p.1.1 p.1.2
        invFun := fun f => ⟨Matrix.nonsingInvUnit (A f) (hunit f), by
          intro i l
          change (i = l → A f i l = 1) ∧ (i ≠ l → ¬ colGe d k i l → A f i l = 0)
          exact ⟨fun h => by simp [A, h], fun h hcol => by simp [A, h, hcol]⟩⟩
        left_inv := fun u => by
          apply Subtype.ext
          apply Units.ext
          ext i l
          change A (fun p => (u.val : Matrix (Fin d) (Fin d) K) p.1.1 p.1.2) i l =
            (u.val : Matrix (Fin d) (Fin d) K) i l
          have hu := u.property i l
          by_cases hil : i = l
          · simpa only [A, ite_eq_left hil] using (hu.1 hil).symm
          · by_cases hcol : colGe d k i l
            · simp [A, hil, hcol]
            · simp [A, hil, hcol, hu.2 hil hcol]
        right_inv := fun f => by
          funext p
          change A f p.1.1 p.1.2 = f p
          have hil : p.1.1 ≠ p.1.2 := ne_of_lt p.2.1
          simp [A, hil, p.2] }
    rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := K)]
  rw [card_colGe j, card_colGe (j + 1), natCard_colGe d j hj, pow_add]

end GlobalTheory.CompanionTheory.TyFin.ColStep
end
end

section

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def colEntries {d j : ℕ} (hj : j < d) (u : GL (Fin d) K) : Fin j → K :=
  fun i => (u : Matrix (Fin d) (Fin d) K) ⟨i, i.2.trans hj⟩ ⟨j, hj⟩

theorem sum_dite_col {d j : ℕ} (hj : j < d) (r : Fin j → K) (M : Matrix (Fin d) (Fin d) K) :
    ∑ i : Fin d, ∑ l : Fin d, (if h : (l : ℕ) = j ∧ (i : ℕ) < j then r ⟨i, h.2⟩ else 0) * M i l =
      ∑ i : Fin j, r i * M ⟨i, i.2.trans hj⟩ ⟨j, hj⟩ := by
  have inner : ∀ i : Fin d, ∑ l : Fin d, (if h : (l : ℕ) = j ∧ (i : ℕ) < j then r ⟨i, h.2⟩ else 0) * M i l =
      if h : (i : ℕ) < j then r ⟨i, h⟩ * M i ⟨j, hj⟩ else 0 := by
    intro i
    rw [Finset.sum_eq_single ⟨j, hj⟩]
    · by_cases h : (i : ℕ) < j
      · rw [dif_pos ⟨rfl, h⟩, dif_pos h]
      · rw [dite_eq_right (fun h' => h h'.2), dite_eq_right h, zero_mul]
    · intro l _ hl
      have hl' : ¬ ((l : ℕ) = j ∧ (i : ℕ) < j) := fun h => hl (Fin.ext h.1)
      rw [dite_eq_right hl', zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp only [inner]
  rw [show (∑ i : Fin d, if h : (i : ℕ) < j then r ⟨i, h⟩ * M i ⟨j, hj⟩ else 0) =
      ∑ i ∈ (Finset.univ : Finset (Fin j)).map (Fin.castLEEmb hj.le),
        (if h : (i : ℕ) < j then r ⟨i, h⟩ * M i ⟨j, hj⟩ else 0) from ?_]
  · rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.castLEEmb_apply, Fin.val_castLE, dif_pos i.2]
    rfl
  · symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hij : ¬ (i : ℕ) < j := by
      intro h
      apply hi
      exact Finset.mem_map.mpr ⟨⟨i, h⟩, Finset.mem_univ _, Fin.ext rfl⟩
    rw [dite_eq_right hij]

theorem patChar_colGeR {d j : ℕ} (hj : j < d) (r : Fin j → K) (ψ₀ : AddChar K ℂ) (u : GL (Fin d) K) :
    patChar (colGeR K d j r) ψ₀ u =
      patChar (colGeE K d (j + 1)) ψ₀ u * ψ₀ (∑ i, r i * colEntries hj u i) := by
  unfold patChar
  rw [← AddChar.map_add_eq_mul]
  congr 1
  rw [show (∑ i, r i * colEntries hj u i) =
      ∑ i : Fin j, r i * (u : Matrix (Fin d) (Fin d) K) ⟨i, i.2.trans hj⟩ ⟨j, hj⟩ from rfl,
    ← sum_dite_col hj r (u : Matrix (Fin d) (Fin d) K), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  unfold colGeR
  ring

theorem mem_patSet_succ_iff {d j : ℕ} (hj : j < d) (u : GL (Fin d) K) :
    u ∈ patSet (K := K) (colGe d (j + 1)) ↔ u ∈ patSet (K := K) (colGe d j) ∧ colEntries hj u = 0 := by
  simp only [patSet, Set.mem_setOf_eq, colGe]
  constructor
  · intro h
    refine ⟨fun i l => ⟨(h i l).1, fun hne hn => (h i l).2 hne (fun hc => hn ⟨hc.1, by
      have h2 := hc.2; omega⟩)⟩, ?_⟩
    funext i
    have hi2 := i.2
    have hi : (⟨i, i.2.trans hj⟩ : Fin d) ≠ ⟨j, hj⟩ := by
      intro h'
      have h3 := congrArg Fin.val h'
      simp only [Fin.val_mk] at h3
      omega
    exact (h _ _).2 hi (fun hc => by
      have h2 := hc.2
      simp only [Fin.val_mk] at h2
      omega)
  · rintro ⟨h, hc⟩ i l
    refine ⟨(h i l).1, fun hne hn => ?_⟩
    by_cases hlj : (l : ℕ) = j ∧ i < l
    · have h3 : (i : ℕ) < l := hlj.2
      have hij : (i : ℕ) < j := by omega
      have h4 := congrFun hc ⟨i, hij⟩
      have hl : l = ⟨j, hj⟩ := Fin.ext hlj.1
      subst hl
      exact h4
    · apply (h i l).2 hne
      rintro ⟨h1, h2⟩
      apply hn
      refine ⟨h1, ?_⟩
      have h5 : (l : ℕ) ≠ j := fun h3 => hlj ⟨h3, h1⟩
      omega

theorem wh_colGe_succ_eq_sum (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ)
    (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ) (hj : j < d)
    (hc : (patSet (K := K) (colGe d j)).ncard = Fintype.card K ^ j * (patSet (K := K) (colGe d (j + 1))).ncard)
    (ho : ∀ x : Fin j → K, (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) =
      if x = 0 then (Fintype.card K : ℂ) ^ j else 0) :
    wh (colGe d (j + 1)) (colGeE K d (j + 1)) ψ₀ χ =
      ∑ r : Fin j → K, wh (colGe d j) (colGeR K d j r) ψ₀ χ := by
  classical
  have hq : (Fintype.card K : ℂ) ^ j ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hN : ((patSet (K := K) (colGe d j)).ncard : ℂ)⁻¹ * (Fintype.card K : ℂ) ^ j =
      ((patSet (K := K) (colGe d (j + 1))).ncard : ℂ)⁻¹ := by
    rw [hc, Nat.cast_mul, Nat.cast_pow, mul_inv, mul_comm (((Fintype.card K : ℂ) ^ j)⁻¹), mul_assoc,
      inv_mul_cancel₀ hq, mul_one]
  have hu : ∀ u : GL (Fin d) K, (∑ r : Fin j → K, if u ∈ patSet (K := K) (colGe d j) then
      (patChar (colGeR K d j r) ψ₀ u)⁻¹ * χ u else 0) =
      (Fintype.card K : ℂ) ^ j * (if u ∈ patSet (K := K) (colGe d (j + 1)) then
        (patChar (colGeE K d (j + 1)) ψ₀ u)⁻¹ * χ u else 0) := by
    intro u
    by_cases hP : u ∈ patSet (K := K) (colGe d j)
    · rw [Finset.sum_congr rfl (fun r _ => if_pos hP)]
      simp only [patChar_colGeR hj, mul_inv]
      rw [show (∑ r : Fin j → K, (patChar (colGeE K d (j + 1)) ψ₀ u)⁻¹ *
          (ψ₀ (∑ i, r i * colEntries hj u i))⁻¹ * χ u) =
          ((patChar (colGeE K d (j + 1)) ψ₀ u)⁻¹ * χ u) *
            ∑ r : Fin j → K, (ψ₀ (∑ i, r i * colEntries hj u i))⁻¹ by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring]
      rw [ho (colEntries hj u)]
      by_cases hx : colEntries hj u = 0
      · have hmem : u ∈ patSet (K := K) (colGe d (j + 1)) := (mem_patSet_succ_iff hj u).mpr ⟨hP, hx⟩
        rw [if_pos hx, if_pos hmem]
        ring
      · have hmem : u ∉ patSet (K := K) (colGe d (j + 1)) := fun h => hx ((mem_patSet_succ_iff hj u).mp h).2
        rw [if_neg hx, if_neg hmem]
        ring
    · have hmem : u ∉ patSet (K := K) (colGe d (j + 1)) := fun h => hP ((mem_patSet_succ_iff hj u).mp h).1
      rw [if_neg hmem, mul_zero]
      exact Finset.sum_eq_zero (fun r _ => if_neg hP)
  unfold wh
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [hu]
  rw [← Finset.mul_sum, ← mul_assoc, hN]

end GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier
end
end
