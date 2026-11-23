module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import ReciprocityTheory.L2DbarEstimates.Bundle001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle696
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle691
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle672
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle700
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle030
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle658
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle698
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantPeriodMarkingUniversalCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle702
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle699
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle667
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.InnerProductSpace.OfNorm
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle206
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle102
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Mathlib.Topology.Sheaves.Presheaf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle532

@[expose] public section

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix
open scoped ComplexOrder


theorem _root_.GlobalTheory.T.chernCurvature_modelGram_conjugateEmbedding : ∀ {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w ξ η : ReciprocityTheory.L2DbarEstimates.V n), (1 - (Z w)ᴴ * Z w).PosDef → curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w ξ η = -((1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z ξ)ᵀ := by
  first | exact @GlobalTheory.PointChern.curv_modelGram_tauBar | exact GlobalTheory.PointChern.curv_modelGram_tauBar | (intros; apply GlobalTheory.PointChern.curv_modelGram_tauBar <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame


theorem _root_.GlobalTheory.T.card_cmTypeEmbeddingsFixingRoot_eq_half_finrank : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), Fintype.card (GlobalTheory.AllWt.Psi H) = Module.finrank ℚ E / 2 := by
  first | exact @GlobalTheory.CMTypeCard.card_psi_eq_half | exact GlobalTheory.CMTypeCard.card_psi_eq_half | (intros; apply GlobalTheory.CMTypeCard.card_psi_eq_half <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShFam.Hor.LogCh.PerExt

theorem logExp_add_single {n a : ℕ} (s : Fin n → ℂ) (j : Fin n) (hj : (j : ℕ) < a) :
    logExp a (s + Pi.single j (2 * Real.pi * Complex.I)) = logExp a s := by
  funext k
  simp only [logExp, Pi.add_apply]
  by_cases hk : k = j
  · subst hk
    simp [hj, Complex.exp_add]
  · simp [Pi.single_apply, hk]

theorem mem_logDom_add_single {n a : ℕ} {s : Fin n → ℂ} (hs : s ∈ logDom n a) (j : Fin n) (hj : (j : ℕ) < a) :
    s + Pi.single j (2 * Real.pi * Complex.I) ∈ logDom n a := by
  intro k
  have := hs k
  by_cases hk : k = j
  · subst hk
    simp only [if_pos hj] at this ⊢
    simpa using this
  · simpa [Pi.single_apply, hk] using this

theorem quad_single {R : Type} [CommRing R] {g : ℕ} (M : Matrix (Fin g) (Fin g) R) (i : Fin g) :
    dotProduct (Pi.single i 1) (M.mulVec (Pi.single i 1)) = M i i := by
  simp [Matrix.mulVec_single, single_dotProduct]

theorem quad_add {R : Type} [CommRing R] {g : ℕ} (M : Matrix (Fin g) (Fin g) R) (i j : Fin g) :
    dotProduct (Pi.single i 1 + Pi.single j 1) (M.mulVec (Pi.single i 1 + Pi.single j 1)) =
      M i i + M i j + M j i + M j j := by
  simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add, Matrix.mulVec_single, single_dotProduct]
  simp
  ring

theorem cast_single {g : ℕ} (i : Fin g) : (fun l => ((Pi.single i (1 : ℤ) : Fin g → ℤ) l : ℂ)) = Pi.single i 1 := by
  funext l
  by_cases h : l = i
  · subst h; simp
  · simp [Pi.single_apply, h]

theorem cast_single_add {g : ℕ} (i j : Fin g) :
    (fun l => (((Pi.single i (1 : ℤ) + Pi.single j 1 : Fin g → ℤ)) l : ℂ)) = Pi.single i 1 + Pi.single j 1 := by
  funext l
  by_cases h1 : l = i <;> by_cases h2 : l = j <;> simp [Pi.single_apply, h1, h2]

theorem periodMatrix_extension : ∀ (n a g : ℕ) (ha : a ≤ n) (ρ₁ : ℝ) (τ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < ρ₁ → ρ₁ ≤ 1 → (∀ i j, DifferentiableOn ℂ (fun s => τ s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁}) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → (τ s).IsSymm ∧ ((τ s).map Complex.im).PosDef) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → ∀ k : Fin a, τ (s + Pi.single (Fin.castLE ha k) (2 * Real.pi * Complex.I)) = τ s + (B k).map (Int.cast : ℤ → ℂ)) → (∀ k, ((B k).map (Int.cast : ℤ → ℝ)).PosSemidef) ∧ ∃ τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ, (∀ i j, DifferentiableOn ℂ (fun z => τ₀ z i j) (Metric.ball 0 ρ₁)) ∧ (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, (τ₀ z).IsSymm) ∧ ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → τ s = τ₀ (logExp a s) + ∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ) := by
  intro n a g ha ρ₁ τ B hρ hρ1 hdiff hsym hmon

  have hs₀ : ∃ s₀, s₀ ∈ logDom n a ∧ logExp a s₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ := by
    refine ⟨fun k => if (k : ℕ) < a then ((Real.log (ρ₁ / 2) : ℝ) : ℂ) else 0, ?_, ?_⟩
    · intro k
      by_cases hk : (k : ℕ) < a
      · simp only [if_pos hk, Complex.ofReal_re]
        exact Real.log_neg (by positivity) (by linarith)
      · simp [hk]
    · rw [mem_ball_zero_iff, pi_norm_lt_iff hρ]
      intro k
      by_cases hk : (k : ℕ) < a
      · simp only [logExp, if_pos hk]
        rw [← Complex.ofReal_exp, Real.exp_log (by positivity), Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        linarith
      · simp [logExp, hk, hρ]
  obtain ⟨s₀, hs₀D, hs₀B⟩ := hs₀

  have hBsym : ∀ k, (B k).IsSymm := by
    intro k
    have hj : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp
    have h1 := hmon s₀ hs₀D hs₀B k
    have h2 := (hsym _ (mem_logDom_add_single hs₀D _ hj) (by rw [logExp_add_single _ _ hj]; exact hs₀B)).1
    have h3 := (hsym s₀ hs₀D hs₀B).1
    rw [h1] at h2
    refine Matrix.IsSymm.ext fun i j => ?_
    have e1 := congrFun (congrFun h2 i) j
    have e2 := congrFun (congrFun h3 i) j
    simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.map_apply] at e1 e2
    have : ((B k j i : ℤ) : ℂ) = B k i j := by rw [e2] at e1; exact add_left_cancel e1
    exact_mod_cast this
  have hnn := GlobalTheory.T.monodromy_matrix_dotProduct_nonneg_integral n a g ha ρ₁ τ B hρ hρ1 hdiff hsym hmon
  refine ⟨fun k => GlobalTheory.T.posSemidef_real_of_int_quadForm_nonneg g (B k) (hBsym k) (hnn k), ?_⟩
  have hF : ∀ v : Fin g → ℤ, ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F (Metric.ball 0 ρ₁) ∧
      ∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ →
        dotProduct (fun i => (v i : ℂ)) ((τ s).mulVec (fun i => (v i : ℂ))) -
          ∑ k, s (Fin.castLE ha k) * ((dotProduct v ((B k).mulVec v) : ℤ) : ℂ) / (2 * Real.pi * Complex.I) =
            F (logExp a s) :=
    fun v => GlobalTheory.T.periodQuadForm_extends_holomorphic_punctPolydisc n a g ha ρ₁ τ B v hρ hρ1 hdiff hsym hmon (fun k => hnn k v)
  choose F hFd hFe using hF
  let e : Fin g → Fin g → ℤ := fun i => Pi.single i 1
  refine ⟨fun z => Matrix.of fun i j => if i = j then F (e i) z else (F (e i + e j) z - F (e i) z - F (e j) z) / 2,
    fun i j => ?_, fun z _ => ?_, fun s hs hsB => ?_⟩
  · simp only [Matrix.of_apply]
    by_cases hij : i = j
    · simp only [if_pos hij]; exact hFd _
    · simp only [if_neg hij]
      have h1 := hFd (e i + e j)
      have h2 := hFd (e i)
      have h3 := hFd (e j)
      fun_prop
  · refine Matrix.IsSymm.ext fun i j => ?_
    simp only [Matrix.of_apply]
    by_cases hij : i = j
    · subst hij; rfl
    · rw [if_neg (Ne.symm hij), if_neg hij, add_comm (e j)]
      ring
  · refine Matrix.ext fun i j => ?_
    beta_reduce
    rw [Matrix.add_apply, Matrix.of_apply, Matrix.sum_apply]
    have hsm : ∀ k, ((s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)) i j =
        s (Fin.castLE ha k) / (2 * Real.pi * Complex.I) * ((B k i j : ℤ) : ℂ) := fun k => rfl
    rw [Finset.sum_congr rfl fun k _ => hsm k]
    set c : ℂ := 2 * Real.pi * Complex.I
    have hi := hFe (e i) s hs hsB
    have hj := hFe (e j) s hs hsB
    simp only [e, cast_single, quad_single] at hi hj
    have hsum1 : ∀ l, ∑ k, s (Fin.castLE ha k) * ((B k l l : ℤ) : ℂ) / c = ∑ k, s (Fin.castLE ha k) / c * ((B k l l : ℤ) : ℂ) :=
      fun l => Finset.sum_congr rfl fun k _ => by ring
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      have hee : F (e i) (logExp a s) = F (Pi.single i 1) (logExp a s) := rfl
      rw [hee, ← hi, hsum1 i]
      ring
    · simp only [if_neg hij]
      have hp := hFe (e i + e j) s hs hsB
      simp only [e, cast_single_add, quad_add] at hp
      have hsi : (τ s) j i = (τ s) i j := ((hsym s hs hsB).1.apply i j)
      have hbi : ∀ k, B k j i = B k i j := fun k => (hBsym k).apply i j
      have hsum2 : ∑ k, s (Fin.castLE ha k) * ((B k i i + B k i j + B k j i + B k j j : ℤ) : ℂ) / c =
          ∑ k, s (Fin.castLE ha k) * ((B k i i : ℤ) : ℂ) / c + 2 * ∑ k, s (Fin.castLE ha k) / c * ((B k i j : ℤ) : ℂ) +
            ∑ k, s (Fin.castLE ha k) * ((B k j j : ℤ) : ℂ) / c := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hbi k]; push_cast; ring
      rw [hsum2] at hp
      rw [← hp, ← hi, ← hj, hsi]
      ring

end GlobalTheory.ShFam.Hor.LogCh.PerExt
end
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.eqOn_ball_of_eqOn_punctPolydiscCoveringExp_image : ∀ (n a : ℕ) (ρ₁ : ℝ) (X : Type) [TopologicalSpace X] [T2Space X] (f h : (Fin n → ℂ) → X), ρ₁ ≤ 1 → ContinuousOn f (Metric.ball 0 ρ₁) → ContinuousOn h (Metric.ball 0 ρ₁) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) ρ₁ → f (logExp a s) = h (logExp a s)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ₁, f z = h z := by
  first | exact @GlobalTheory.eq_on_ball_of_eq_on_logExp_image | exact GlobalTheory.eq_on_ball_of_eq_on_logExp_image | (intros; apply GlobalTheory.eq_on_ball_of_eq_on_logExp_image <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem posDef_im_on_ball_of_logExp : ∀ (n a : ℕ) (J : Type) [Fintype J] [DecidableEq J] (Δ : (Fin n → ℂ) → Matrix J J ℂ), (∀ i j, DifferentiableOn ℂ (fun z => Δ z i j) (Metric.ball 0 1)) → (∀ s ∈ logDom n a, ((Δ (logExp a s)).map Complex.im).PosDef) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ((Δ z).map Complex.im).PosDef := by
  intro n a J _ _ Δ hΔ hpos z hz
  set U := Metric.ball (0 : Fin n → ℂ) 1 with hU
  have hcont : ∀ i j, ContinuousOn (fun w => Δ w i j) U := fun i j => (hΔ i j).continuousOn
  have hM : ContinuousOn (fun w => (Δ w).map Complex.im) U := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    exact Complex.continuous_im.comp_continuousOn (hcont i j)
  have hMT : ContinuousOn (fun w => ((Δ w).map Complex.im)ᵀ) U := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
    exact Complex.continuous_im.comp_continuousOn (hcont j i)
  have hsymm : ((Δ z).map Complex.im)ᵀ = (Δ z).map Complex.im := by
    refine eq_on_ball_of_eq_on_logExp_image n a 1 (Matrix J J ℝ)
      (fun w => ((Δ w).map Complex.im)ᵀ) (fun w => (Δ w).map Complex.im) le_rfl hMT hM ?_ z hz
    intro s hs _
    have h1 := (hpos s hs).1
    unfold Matrix.IsHermitian at h1
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hsymm
  intro x hx
  set q : (Fin n → ℂ) → ℂ := fun w => ∑ i, ∑ j, (x i : ℂ) * Δ w i j * (x j : ℂ) with hq
  have hqim : ∀ w, (q w).im = star x ⬝ᵥ ((Δ w).map Complex.im *ᵥ x) := by
    intro w
    simp [q, dotProduct, mulVec, Complex.im_sum, Complex.mul_im, Finset.mul_sum, mul_comm,
      mul_left_comm, mul_assoc]
  have hqd : DifferentiableOn ℂ q U := by
    rw [hq]
    apply DifferentiableOn.fun_sum
    intro i _
    apply DifferentiableOn.fun_sum
    intro j _
    exact ((hΔ i j).const_mul (x i : ℂ)).mul_const (x j : ℂ)
  have hqpos : ∀ s ∈ logDom n a, 0 < (q (logExp a s)).im := by
    intro s hs
    rw [hqim]
    exact (hpos s hs).dotProduct_mulVec_pos hx
  have hqc : ContinuousOn (fun w => (q w).im) U :=
    Complex.continuous_im.comp_continuousOn hqd.continuousOn
  have hnn : ∀ w ∈ U, 0 ≤ (q w).im := by
    intro w hw
    have := eq_on_ball_of_eq_on_logExp_image n a 1 ℝ (fun w => min (q w).im 0) (fun _ => 0)
      le_rfl ((continuous_id.min continuous_const).comp_continuousOn hqc) continuousOn_const
      (fun s hs _ => min_eq_right (hqpos s hs).le) w hw
    exact (min_eq_right_iff.1 this)
  rw [← hqim]
  rcases (hnn z hz).lt_or_eq with h | h0
  · exact h
  exfalso
  set F : (Fin n → ℂ) → ℂ := fun w => Complex.exp (Complex.I * q w) with hF
  have hFn : ∀ w, ‖F w‖ = Real.exp (-(q w).im) := by
    intro w
    simp [F, Complex.norm_exp, Complex.I_mul_re]
  have hFd : DifferentiableOn ℂ F U := (hqd.const_mul Complex.I).cexp
  have hmax : IsMaxOn (norm ∘ F) U z := by
    intro w hw
    simp only [Set.mem_setOf_eq, Function.comp, hFn, ← h0, neg_zero]
    exact Real.exp_le_exp.2 (by linarith [hnn w hw])
  have heq := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball (0 : Fin n → ℂ) 1).isPreconnected
    Metric.isOpen_ball hFd hz hmax
  obtain ⟨s, hs⟩ := (GlobalTheory.ShFam.Hor.Mark.nonempty_logDom : (logDom n a).Nonempty)
  have hmem : logExp a s ∈ U := GlobalTheory.ShFam.Hor.Mark.logExp_mem hs
  have h2 := congrArg norm (heq hmem)
  simp only [Function.const_apply, hFn, ← h0, neg_zero] at h2
  have h3 : (q (logExp a s)).im = 0 := by
    have := Real.exp_injective h2
    linarith
  exact (hqpos s hs).ne' h3

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodFrame

theorem combMat_mul_left {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε : Matrix (Fin g) (Fin r) ℚ)
    (b : Matrix (Fin g) (Fin g) ℚ) :
    combMat l (b * ε) = combMat l ε * bᵀ.map (Rat.cast : ℚ → ℂ) := by
  have h := combMat_add_mul l ε 0 bᵀ
  have h0 : combMat l (0 : Matrix (Fin g) (Fin r) ℚ) = 0 := by
    ext k j; simp [combMat]
  rwa [h0, zero_add, zero_add, Matrix.transpose_transpose] at h

theorem combMat_add {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ) :
    combMat l (ε + φ) = combMat l ε + combMat l φ := by
  ext k j
  simp [combMat, add_mul, Finset.sum_add_distrib]

theorem isUnit_det_combMat_on_ball : ∀ (n a g r₀ r : ℕ) (ha : a ≤ n) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (c : Matrix (Fin r₀) (Fin r) ℤ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (gm dl : Matrix (Fin r₀) (Fin g) ℚ) (rk D : ℕ) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ), 0 < D → AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ j : Fin g, ∃ i, ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, ζ z i = Pi.single j 1) → (∀ s ∈ logDom n a, ∀ i, ζ (logExp a s) i = ∑ j, c i j • lam s j) → c.map (Int.cast : ℤ → ℚ) = gm * (α * c.map (Int.cast : ℤ → ℚ)) + dl * φ → (∀ m (j : Fin g), j.val < rk → dl m j = 0) → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → (∀ i j, DifferentiableOn ℂ (fun z => τ₀ z i j) (Metric.ball 0 1)) → (∀ k (j l : Fin g), (rk ≤ j.val ∨ rk ≤ l.val) → B k j l = 0) → (∀ s ∈ logDom n a, logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1 → GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s = τ₀ (logExp a s) + ∑ k, (s (Fin.castLE ha k) / (2 * Real.pi * Complex.I)) • (B k).map (Int.cast : ℤ → ℂ)) → ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ z) α).det := by
  intro n a g r₀ r ha ζ lam c α φ gm dl rk D τ₀ B hD hζ hstd hlam hc hdl hP hτ hB hper z hz
  choose I hI using hstd
  let sel : Matrix (Fin g) (Fin r₀) ℚ := Matrix.of fun j i => if i = I j then 1 else 0
  let Dl : Matrix (Fin g) (Fin g) ℂ := (sel * dl)ᵀ.map (Rat.cast : ℚ → ℂ)
  let G : Matrix (Fin g) (Fin g) ℂ := (sel * gm)ᵀ.map (Rat.cast : ℚ → ℂ)
  have hsel : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, combMat (ζ z) sel = 1 := by
    intro z hz
    ext k j
    have h1 : combMat (ζ z) sel k j = ζ z (I j) k := by
      simp only [combMat, sel, Matrix.of_apply]
      rw [Finset.sum_eq_single (I j)]
      · simp
      · intro i _ hi; simp [hi]
      · simp
    rw [h1, hI j z hz, Matrix.one_apply, Pi.single_apply]
  have hBD : ∀ k, (B k).map (Int.cast : ℤ → ℂ) * Dl = 0 := by
    intro k
    ext i j
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.zero_apply, Dl, Matrix.transpose_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l.val < rk
    · simp [hdl _ l hl]
    · simp [hB k i l (Or.inr (not_lt.mp hl))]
  have hDc : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hPc : ContinuousOn (fun z => combMat (ζ z) α) (Metric.ball (0 : Fin n → ℂ) 1) := by
    refine continuousOn_pi.2 fun k => continuousOn_pi.2 fun i => ?_
    simp only [combMat, Matrix.of_apply]
    refine continuousOn_finsetSum _ fun m _ => continuousOn_const.mul ?_
    exact continuousOn_pi.1 (continuousOn_pi.1 hζ.continuousOn m) k
  have hτc : ContinuousOn τ₀ (Metric.ball (0 : Fin n → ℂ) 1) :=
    continuousOn_pi.2 fun k => continuousOn_pi.2 fun i => (hτ k i).continuousOn
  have hQ : Continuous (fun p : Matrix (Fin g) (Fin g) ℂ × Matrix (Fin g) (Fin g) ℂ =>
      p.1 * (G + (D : ℂ)⁻¹ • (p.2 * Dl))) := by fun_prop
  have hQc : ContinuousOn (fun z => combMat (ζ z) α * (G + (D : ℂ)⁻¹ • (τ₀ z * Dl)))
      (Metric.ball (0 : Fin n → ℂ) 1) := by
    have h := hQ.comp_continuousOn (hPc.prodMk hτc)
    simpa only [Function.comp_def] using h
  have key := GlobalTheory.eq_on_ball_of_eq_on_logExp_image n a 1 (Matrix (Fin g) (Fin g) ℂ)
    (fun z => combMat (ζ z) α * (G + (D : ℂ)⁻¹ • (τ₀ z * Dl))) (fun _ => 1) le_rfl
    hQc continuousOn_const (by
      intro s hs hb
      have h1 := hsel _ hb
      rw [combMat_comb _ _ c sel (hlam s hs), hc, Matrix.mul_add, ← Matrix.mul_assoc sel gm, ← Matrix.mul_assoc sel dl,
        combMat_add, combMat_mul_left, combMat_mul_left, ← combMat_comb _ _ c α (hlam s hs)] at h1
      have h2 := congrArg (fun T => T * Dl) (hper s hs hb)
      simp only [perTau, Matrix.add_mul, Matrix.sum_mul, Matrix.smul_mul, hBD, smul_zero, Finset.sum_const_zero,
        add_zero] at h2
      rw [← h2, smul_smul, inv_mul_cancel₀ hDc, one_smul, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ (hP s hs), Matrix.one_mul]
      exact h1) z hz
  exact Matrix.isUnit_det_of_right_inverse key

end GlobalTheory.PeriodFrame
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.differentiableOn_rationalFrame_periodMatrix_logCover : ∀ (n a g r₀ r : ℕ) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ) (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ), AnalyticOnNhd ℂ ζ (Metric.ball 0 1) → (∀ (j : Fin r) (k : Fin g), DifferentiableOn ℂ (fun s => lam s j k) (logDom n a)) → (∀ s ∈ logDom n a, IsUnit (GlobalTheory.PeriodFrame.combMat (ζ (logExp a s)) α).det) → (∀ i j, DifferentiableOn ℂ (fun z => GlobalTheory.PeriodFrame.combMat (ζ z) α i j) (Metric.ball 0 1)) ∧ ∀ i j, DifferentiableOn ℂ (fun s => GlobalTheory.PeriodFrame.perTau a ζ lam α φ D s i j) {s | s ∈ logDom n a ∧ logExp a s ∈ Metric.ball (0 : Fin n → ℂ) 1} := by
  first | exact @GlobalTheory.PeriodFrame.differentiableOn_combMat_perTau | exact GlobalTheory.PeriodFrame.differentiableOn_combMat_perTau | (intros; apply GlobalTheory.PeriodFrame.differentiableOn_combMat_perTau <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology
open GlobalTheory.ShFam.Hor GlobalTheory.CxPts
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.riemannRelations_rationalCombinationFrame : ∀ (g r : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (M : Matrix (Fin r) (Fin r) ℤ) (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ), 0 < D → Hm.IsHermitian → (∀ u : Fin g → ℂ, u ≠ 0 → 0 < (hermForm Hm u u).re) → LinearIndependent ℝ l → (∀ i j, (hermForm Hm (l i) (l j)).im = M i j) → ε * M.map (Int.cast : ℤ → ℚ) * εᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * φᵀ = 0 → φ * M.map (Int.cast : ℤ → ℚ) * εᵀ = 1 → IsUnit (GlobalTheory.PeriodFrame.combMat l ε).det ∧ ((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).IsSymm ∧ (((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).map Complex.im).PosDef ∧ (GlobalTheory.PeriodFrame.combMat l ε)ᵀ * Hm * (GlobalTheory.PeriodFrame.combMat l ε)ᵀᴴ = ((D : ℝ) : ℂ) • ((((D : ℂ) • ((GlobalTheory.PeriodFrame.combMat l ε)⁻¹ * GlobalTheory.PeriodFrame.combMat l φ)).map Complex.im).map Complex.ofReal)⁻¹ := by
  first | exact @GlobalTheory.PeriodFrame.riemann_relations_frame | exact GlobalTheory.PeriodFrame.riemann_relations_frame | (intros; apply GlobalTheory.PeriodFrame.riemann_relations_frame <;> assumption)
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarKey

theorem ell_eq_of_inRCone {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {γ : Fin m → LinearMap.BilinForm ℤ X} {N : ℕ} {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ}
    (hlin : φ.LinearOn γ) (hsw : StrictWith bar φ N ℓ γ) {β : LinearMap.BilinForm ℤ X} (hβ : InRCone γ β) :
    (ℓ β : ℝ) = N * φ.evalZ β := by
  obtain ⟨c, hc, hsum⟩ := hβ
  have h1 : ∑ i : Fin (m + 1), (Fin.cons (-1) c : Fin (m + 1) → ℝ) i •
      toReal ((LinearMap.id : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X)
        ((Fin.cons β γ : Fin (m + 1) → LinearMap.BilinForm ℤ X) i)) = 0 := by
    simp [Fin.sum_univ_succ, hsum]
  have h2 := sum_mul_eq_zero_of_sum_toReal (j := LinearMap.id) (fun _ _ h => h) ℓ h1
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ] at h2
  have h3 : φ.evalZ β = ∑ i, c i * φ.evalZ (γ i) := by
    rw [← evalR_toReal, hsum]; exact (linearOn_iff φ γ).1 hlin c hc
  have h4 : (ℓ β : ℝ) = ∑ i, c i * ℓ (γ i) := by simp at h2; linarith
  rw [h4, h3, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hsw.1 i]; ring

end GlobalTheory.PolFan.StarKey
end
