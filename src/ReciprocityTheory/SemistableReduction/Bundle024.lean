module

public import ReciprocityTheory.SemistableReduction.Bundle001
public import ReciprocityTheory.SemistableReduction.Bundle002
public import ReciprocityTheory.SemistableReduction.Bundle023
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
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
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import ReciprocityTheory.SemistableReduction.Bundle021
public import ReciprocityTheory.SemistableReduction.Bundle003
public import ReciprocityTheory.SemistableReduction.Bundle008
public import ReciprocityTheory.SemistableReduction.Bundle017
public import ReciprocityTheory.SemistableReduction.ApproxGraphB
public import ReciprocityTheory.SemistableReduction.Bundle020
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Real Function

theorem torusMean_holds : TorusMeanBasicStatement ∧ TorusCoeffStatement := by
  classical
  refine ⟨fun ι _ => ⟨fun f _ => tm_int f, fun f g hf hg => ?_, fun s c => ?_⟩,
    fun ι _ f i k hk hext => ?_⟩
  · show ∫ θ, tmLog (f * g) θ ∂(torusProb ι) =
      ∫ θ, tmLog f θ ∂(torusProb ι) + ∫ θ, tmLog g θ ∂(torusProb ι)
    rw [← integral_add (tm_int f) (tm_int g)]
    apply integral_congr_ae
    filter_upwards [tm_ae_ne f hf, tm_ae_ne g hg] with θ h1 h2
    simp only [tmLog, map_mul, norm_mul]
    exact Real.log_mul (norm_ne_zero_iff.mpr h1) (norm_ne_zero_iff.mpr h2)
  · have hm : ∀ θ, tmLog (MvPolynomial.monomial s c) θ = Real.log ‖c‖ := by
      intro θ
      simp [tmLog, MvPolynomial.eval_monomial, Finsupp.prod, norm_prod, norm_pow,
        norm_torusPoint]
    show ∫ θ, tmLog (MvPolynomial.monomial s c) θ ∂(torusProb ι) = Real.log ‖c‖
    simp_rw [hm]
    simp
  · show ∫ θ, tmLog (coeffIn i k f) θ ∂(torusProb ι) ≤ ∫ θ, tmLog f θ ∂(torusProb ι)
    have hFi : Integrable (tmLog f ∘ tmUpd i) ((torusProb ι).prod unitIntervalMeasure) :=
      (tm_integrable_comp i (measurable_tmLog f).aestronglyMeasurable).mpr (tm_int f)
    rw [tm_integral_comp i (measurable_tmLog f).aestronglyMeasurable,
      integral_prod (fun p => tmLog f (tmUpd i p)) hFi]
    refine integral_mono_ae (tm_int _) hFi.integral_prod_left ?_
    filter_upwards [tm_ae_ne _ hk] with θ hθ
    show tmLog (coeffIn i k f) θ ≤ ∫ t, tmLog f (update θ i t) ∂unitIntervalMeasure
    simp_rw [tmLog_update]
    rw [integral_log_circ]
    have hc : (tmSlice i (torusPoint θ) f).coeff k = MvPolynomial.eval (torusPoint θ) (coeffIn i k f) :=
      tmSlice_coeff i _ f k
    have hk' : (tmSlice i (torusPoint θ) f).coeff k ≠ 0 := hc ▸ hθ
    show Real.log ‖MvPolynomial.eval (torusPoint θ) (coeffIn i k f)‖ ≤ _
    rw [← hc]
    rcases hext with htop | hbot
    · exact log_norm_coeff_top_le _ k hk' fun k' hk'' => by
        rw [tmSlice_coeff, htop k' hk'', map_zero]
    · exact log_norm_coeff_bot_le _ k hk' fun k' hk'' => by
        rw [tmSlice_coeff, hbot k' hk'', map_zero]

end ReciprocityTheory.MultiplicativeHeights
end
end

section

namespace ReciprocityTheory.MultiplicativeHeights

open ApproximationGraph in
theorem approxGraph_holds : ApproxGraphStatement := by
  intro r p μ ρ X _ hμ hρ hρ1 hX
  exact ⟨fun w hw => approxGraph_one X hμ hρ hρ1 hX w hw,
    fun y hy hy0 => approxGraph_two X hμ hρ hρ1 hX y hy hy0,
    fun v y hy hvy => approxGraph_three X hμ hρ hρ1 hX v y hy hvy⟩

end ReciprocityTheory.MultiplicativeHeights
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

def matLin {K : Type} [Field K] [NumberField K] {r : ℕ} (Q : Matrix (Fin r) (Fin r) K) :
    (Fin r → K) →ₗ[𝓞 K] (Fin r → K) :=
  (Matrix.mulVecLin Q).restrictScalars (𝓞 K)

theorem matLin_apply {K : Type} [Field K] [NumberField K] {r : ℕ}
    (Q : Matrix (Fin r) (Fin r) K) (x : Fin r → K) : matLin Q x = Q *ᵥ x := rfl

theorem matLin_injective {K : Type} [Field K] [NumberField K] {r : ℕ}
    (Q : Matrix (Fin r) (Fin r) K) (hQ : Q.det ≠ 0) : Function.Injective (matLin Q) := by
  intro x y hxy
  rw [matLin_apply, matLin_apply] at hxy
  have hu : IsUnit Q := (Matrix.isUnit_iff_isUnit_det Q).2 (isUnit_iff_ne_zero.2 hQ)
  exact (Matrix.mulVec_injective_iff_isUnit.2 hu) hxy

theorem span_mulVec {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (Q : Matrix (Fin r) (Fin r) K) (b : Fin k → Fin r → K) :
    Submodule.span (𝓞 K) (Set.range fun i => Q *ᵥ b i) =
      (Submodule.span (𝓞 K) (Set.range b)).map (matLin Q) := by
  rw [Submodule.map_span, ← Set.range_comp]
  rfl

theorem latDeg_transport {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (D : (K →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (Q : Matrix (Fin r) (Fin r) K) (hQ : Q.det ≠ 0)
    (B : Submodule (𝓞 K) (Fin r → K)) (b : Fin k → Fin r → K) :
    latDeg (fun σ => (Q.map σ)ᴴ * D σ * Q.map σ) B b =
      latDeg D (B.map (matLin Q)) (fun i => Q *ᵥ b i) := by
  unfold latDeg
  have hinj : Function.Injective (matLin Q) := matLin_injective Q hQ
  have h1 : (Submodule.span (𝓞 K) (Set.range fun i => Q *ᵥ b i)).toAddSubgroup.relIndex
      (B.map (matLin Q)).toAddSubgroup =
      (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex B.toAddSubgroup := by
    rw [span_mulVec, Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup]
    exact AddSubgroup.relIndex_map_map_of_injective _ _ hinj
  have hemb : ∀ (σ : K →+* ℂ) (x : Fin r → K), embVec σ (Q *ᵥ x) = Q.map σ *ᵥ embVec σ x := by
    intro σ x
    funext a
    exact RingHom.map_mulVec σ Q x a
  have h2 : ∀ σ : K →+* ℂ, gramC ((Q.map σ)ᴴ * D σ * Q.map σ) σ b = gramC (D σ) σ (fun i => Q *ᵥ b i) := by
    intro σ
    ext i j
    simp only [gramC, Matrix.of_apply, hemb]
    simp only [← Matrix.mulVec_mulVec, Matrix.star_mulVec, Matrix.dotProduct_mulVec]
  rw [h1]
  simp only [h2]

theorem kBasisIn_map {K : Type} [Field K] [NumberField K] {r k : ℕ}
    (Q : Matrix (Fin r) (Fin r) K) (hQ : Q.det ≠ 0) (B : Submodule (𝓞 K) (Fin r → K))
    (b : Fin k → Fin r → K) (hb : IsKBasisIn B b) :
    IsKBasisIn (B.map (matLin Q)) (fun i => Q *ᵥ b i) := by
  obtain ⟨h1, h2, h3⟩ := hb
  have hinj : Function.Injective (Matrix.mulVecLin Q) := fun x y h => matLin_injective Q hQ h
  refine ⟨fun i => ⟨b i, h1 i, rfl⟩, ?_, ?_⟩
  · have e : (fun i => Q *ᵥ b i) = (Matrix.mulVecLin Q) ∘ b := rfl
    rw [e]
    exact h2.map' _ (LinearMap.ker_eq_bot.2 hinj)
  · rintro x ⟨y, hy, rfl⟩
    have h4 := Submodule.mem_map_of_mem (f := Matrix.mulVecLin Q) (h3 y hy)
    rw [Submodule.map_span, ← Set.range_comp] at h4
    exact h4

def formM {K : Type} [Field K] {r : ℕ} (c : K →+* K) (M : Matrix (Fin r) (Fin r) K)
    (x y : Fin r → K) : K :=
  (fun a => c (x a)) ⬝ᵥ (M *ᵥ y)

theorem hermForm_h_eq {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (x y : Fin r → K) : S.h x y = formM S.c S.G x y := by
  unfold HermForm.h formM
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem formM_change {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (x y : Fin r → K) :
    formM S.c ((P.map S.c)ᵀ * S.G * P) x y = S.h (P *ᵥ x) (P *ᵥ y) := by
  rw [hermForm_h_eq]
  unfold formM
  have e1 : (fun a => S.c ((P *ᵥ x) a)) = (P.map S.c) *ᵥ (fun a => S.c (x a)) := by
    funext a
    exact RingHom.map_mulVec S.c P x a
  rw [e1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem formM_witt {K : Type} [Field K] {r : ℕ} (c : K →+* K) (m : ℕ) (g : Fin r → K)
    (x y : Fin r → K) :
    formM c (wittMat r m g) x y = ∑ a, c (x a) * (wVal r m g a * y (wPart r m a)) := by
  unfold formM
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  have ha := a.isLt
  by_cases h : (a : ℕ) < m ∨ r ≤ (a : ℕ) + m
  · have hw : wVal r m g a = 1 := if_pos h
    have hp : wPart r m a = Fin.rev a := if_pos h
    rw [hw, hp, one_mul, Finset.sum_eq_single (Fin.rev a)]
    · rw [wittMat, Matrix.of_apply, if_pos, one_mul]
      rw [Fin.val_rev]
      omega
    · intro j _ hj
      rw [wittMat, Matrix.of_apply, if_neg, if_neg, zero_mul]
      · rintro ⟨rfl, h2, h3⟩
        omega
      · rintro ⟨h1, -⟩
        apply hj
        ext
        rw [Fin.val_rev]
        omega
    · simp
  · have hw : wVal r m g a = g a := if_neg h
    have hp : wPart r m a = a := if_neg h
    rw [hw, hp, Finset.sum_eq_single a]
    · rw [wittMat, Matrix.of_apply, if_neg, if_pos ⟨rfl, by omega, by omega⟩]
      omega
    · intro j _ hj
      rw [wittMat, Matrix.of_apply, if_neg, if_neg, zero_mul]
      · rintro ⟨rfl, -⟩
        exact hj rfl
      · have hj' := j.isLt
        omega
    · simp

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end

section

noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiPt

open Matrix NumberField ComplexConjugate
open scoped ComplexOrder

theorem herm_cGP {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (a b : Fin r) :
    S.c (((P.map S.c)ᵀ * S.G * P) a b) = ((P.map S.c)ᵀ * S.G * P) b a := by

  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
  S.c_invol, S.G_herm, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem g_fix {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (m : ℕ) (g : Fin r → K)
    (hJ : (P.map S.c)ᵀ * S.G * P = wittMat r m g) (i : Fin r) (h1 : m ≤ (i : ℕ))
    (h2 : (i : ℕ) + m < r) : S.c (g i) = g i := by
  have h := herm_cGP S P i i
  rw [hJ] at h
  simpa [wittMat, Matrix.of_apply, not_lt.2 h1, h1, h2] using h

theorem exists_adapted_majorant {K : Type} [Field K] [NumberField K] {r : ℕ} (S : HermForm K r)
    (P : Matrix (Fin r) (Fin r) K) (m : ℕ) (g : Fin r → K) (dd : Fin r → ℝ)
    (hP : P.det ≠ 0) (h2m : 2 * m ≤ r) (hJ : (P.map S.c)ᵀ * S.G * P = wittMat r m g)
    (hdd : ∀ i, 0 < dd i) (hg : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → g i ≠ 0) :
    ∃ M : Majorant S, ∀ σ,
      M.H σ = ((P⁻¹).map σ)ᴴ * diagMet (adMet r m g dd) σ * (P⁻¹).map σ := by
  classical
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.2 hP
  have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
  have hG : S.G = ((P⁻¹).map S.c)ᵀ * wittMat r m g * P⁻¹ := by
    rw [← hJ]
    have h1 : ((P⁻¹).map S.c)ᵀ * (P.map S.c)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hPP,
        Matrix.map_one _ (map_zero S.c) (map_one S.c), Matrix.transpose_one]
    calc S.G = ((P⁻¹).map S.c)ᵀ * (P.map S.c)ᵀ * S.G * (P * P⁻¹) := by
          rw [h1, hPP, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]

  have key : ∀ σ : K →+* ℂ,
      let A := (P⁻¹).map σ
      let D := diagMet (adMet r m g dd) σ
      (Aᴴ * D * A).PosDef ∧ Aᴴ * D * A * (S.G.map σ)⁻¹ * (Aᴴ * D * A) = S.G.map σ := by
    intro σ A D
    set Ai := P.map σ with hAi
    have e1 : A * Ai = 1 := by
      simp only [A, Ai]
      rw [← Matrix.map_mul, hPP', Matrix.map_one _ (map_zero σ) (map_one σ)]
    have e2 : Ai * A = 1 := by
      simp only [A, Ai]
      rw [← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero σ) (map_one σ)]
    have e3 : Aiᴴ * Aᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e1, Matrix.conjTranspose_one]
    have e4 : Aᴴ * Aiᴴ = 1 := by rw [← Matrix.conjTranspose_mul, e2, Matrix.conjTranspose_one]
    have hpos : ∀ i, 0 < adMet r m g dd σ i := adMet_pos r m g dd hdd hg σ
    let Dinv : Matrix (Fin r) (Fin r) ℂ :=
      diagonal fun i => (((adMet r m g dd σ i : ℝ) : ℂ))⁻¹
    have e5 : D * Dinv = 1 := by
      simp only [D, Dinv, diagMet, Matrix.diagonal_mul_diagonal]
      rw [← Matrix.diagonal_one]
      congr 1
      funext i
      have : ((adMet r m g dd σ i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hpos i).ne'
      exact mul_inv_cancel₀ this
    have hGσ : S.G.map σ = Aᴴ * (wittMat r m g).map σ * A := by
      rw [hG, Matrix.map_mul, Matrix.map_mul]
      congr 2
      ext a b
      simp [A, Matrix.conjTranspose_apply, S.c_emb]
    have hreal : ∀ i : Fin r, m ≤ (i : ℕ) → (i : ℕ) + m < r → conj (σ (g i)) = σ (g i) := by
      intro i h1 h2
      rw [← S.c_emb, g_fix S P m g hJ i h1 h2]
    have hKey : (wittMat r m g).map σ * Dinv * (wittMat r m g).map σ = D := by
      rw [wittMat_map_mul]
      simp only [D, diagMet]
      congr 1
      funext i
      exact wVal_adMet r m g dd h2m hg σ hreal i
    set Y := S.G.map σ with hY
    set Jσ := (wittMat r m g).map σ with hJσ
    set H := Aᴴ * D * A with hH
    set Hinv := Ai * Dinv * Aiᴴ with hHinv
    have hHH : H * Hinv = 1 := by
      calc H * Hinv = Aᴴ * D * (A * Ai) * Dinv * Aiᴴ := by simp only [H, Hinv, Matrix.mul_assoc]
        _ = Aᴴ * (D * Dinv) * Aiᴴ := by rw [e1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = 1 := by rw [e5, Matrix.mul_one, e4]
    have hHH' : Hinv * H = 1 := mul_eq_one_comm.1 hHH
    have hYHY : Y * Hinv * Y = H := by
      rw [hGσ]
      calc Aᴴ * Jσ * A * Hinv * (Aᴴ * Jσ * A)
          = Aᴴ * Jσ * (A * Ai) * Dinv * (Aiᴴ * Aᴴ) * Jσ * A := by
            simp only [Hinv, Matrix.mul_assoc]
        _ = Aᴴ * (Jσ * Dinv * Jσ) * A := by
            rw [e1, e3, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = H := by rw [hKey]
    have hYinv : Y⁻¹ = Hinv * Y * Hinv := by
      apply Matrix.inv_eq_left_inv
      calc Hinv * Y * Hinv * Y = Hinv * (Y * Hinv * Y) := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hYHY, hHH']
    refine ⟨?_, ?_⟩
    · have hD : D.PosDef := by
        simp only [D, diagMet]
        exact Matrix.posDef_diagonal_iff.2 fun i => by exact_mod_cast hpos i
      have hAu : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2
        (Matrix.isUnit_det_of_right_inverse e1)
      exact hD.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hAu)
    · rw [hYinv]
      calc H * (Hinv * Y * Hinv) * H = (H * Hinv) * Y * (Hinv * H) := by
            simp only [Matrix.mul_assoc]
        _ = Y := by rw [hHH, hHH', Matrix.one_mul, Matrix.mul_one]
  refine ⟨⟨fun σ => ((P⁻¹).map σ)ᴴ * diagMet (adMet r m g dd) σ * (P⁻¹).map σ,
    fun σ => (key σ).1, fun σ => (key σ).2, ?_⟩, fun σ => rfl⟩
  intro σ
  have hmap : (P⁻¹).map ((starRingEnd ℂ).comp σ) = ((P⁻¹).map σ).map (starRingEnd ℂ) := by
    rw [Matrix.map_map]
    rfl
  have hDc : diagMet (adMet r m g dd) ((starRingEnd ℂ).comp σ) =
      (diagMet (adMet r m g dd) σ).map (starRingEnd ℂ) := by
    simp only [diagMet, adMet_conj]
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact (Complex.conj_ofReal (adMet r m g dd σ i)).symm
  show ((P⁻¹).map ((starRingEnd ℂ).comp σ))ᴴ * diagMet (adMet r m g dd) ((starRingEnd ℂ).comp σ) *
      (P⁻¹).map ((starRingEnd ℂ).comp σ) =
    (((P⁻¹).map σ)ᴴ * diagMet (adMet r m g dd) σ * (P⁻¹).map σ).map (starRingEnd ℂ)
  rw [hmap, hDc, Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map]
  intro x
  simp

end ReciprocityTheory.MultiplicativeHeights.SemiPt
end
end
