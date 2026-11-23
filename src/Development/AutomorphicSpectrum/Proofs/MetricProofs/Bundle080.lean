module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle113
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Assembly
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle004
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PPuncturedExpOrder
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PRiemannExtensionSlices
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle002
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import Mathlib.Algebra.MvPolynomial.Funext
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle019
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle075
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle063
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle068
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle070
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle065
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle064
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle061
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle053
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.PosSemidefOfIntQuadNonneg
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
import ReciprocityTheory.AnalyticForms.LeviForms.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.MinorAny

theorem minorIJ_map {R S : Type} [CommRing R] [CommRing S] {N : ℕ} (f : R →+* S)
    (A : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (A.map f) I J = f (minorIJ A I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]
    rfl
  · exact (map_zero f).symm

def gap {N : ℕ} {Ω : Type} [Field Ω] (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω)
    (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)) (S : Type) [CommRing S] [Algebra Ω S]
    (h : Matrix (Fin N) (Fin N) S) : S :=
  algebraMap Ω S c₀ * ∑ I, algebraMap Ω S (coef I) * minorIJ (T.map (algebraMap Ω S) * h) I J -
    algebraMap Ω S c₁ * ∑ I, algebraMap Ω S (u I) * minorIJ h I J

theorem gap_map {N : ℕ} {Ω : Type} [Field Ω] (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω)
    (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)) {S S' : Type} [CommRing S] [Algebra Ω S]
    [CommRing S'] [Algebra Ω S'] (f : S →ₐ[Ω] S') (h : Matrix (Fin N) (Fin N) S) :
    f (gap T c₀ c₁ coef u J S h) = gap T c₀ c₁ coef u J S' (h.map f.toRingHom) := by
  have hm : ∀ (M : Matrix (Fin N) (Fin N) S) (I J : Finset (Fin N)),
      f (minorIJ M I J) = minorIJ (M.map f.toRingHom) I J :=
    fun M I J => (minorIJ_map f.toRingHom M I J).symm
  have hT : (T.map (algebraMap Ω S) * h).map f.toRingHom = T.map (algebraMap Ω S') * h.map f.toRingHom := by
    rw [Matrix.map_mul, Matrix.map_map]
    congr 1
    congr 1
    funext x
    exact f.commutes x

  simp only [gap, map_sub, map_mul, map_sum, AlgHom.commutes, hm, hT]

theorem minor_any : ∀ (Ω : Type) [Field Ω] [Infinite Ω] (N j : ℕ) (T : Matrix (Fin N) (Fin N) Ω) (c₀ c₁ : Ω) (coef u : Finset (Fin N) → Ω) (J : Finset (Fin N)), (∀ h : Matrix (Fin N) (Fin N) Ω, IsBlockDiag j h → c₀ * ∑ I, coef I * minorIJ (T * h) I J = c₁ * ∑ I, u I * minorIJ h I J) → ∀ (S : Type) [CommRing S] [Algebra Ω S] (h : Matrix (Fin N) (Fin N) S), IsBlockDiag j h → algebraMap Ω S c₀ * ∑ I, algebraMap Ω S (coef I) * minorIJ (T.map (algebraMap Ω S) * h) I J = algebraMap Ω S c₁ * ∑ I, algebraMap Ω S (u I) * minorIJ h I J := by
  intro Ω _ _ N j T c₀ c₁ coef u J hyp S _ _ h hh
  have hT : T.map (algebraMap Ω Ω) = T := Matrix.ext fun _ _ => rfl
  have key : ∀ M : Matrix (Fin N) (Fin N) Ω, IsBlockDiag j M → gap T c₀ c₁ coef u J Ω M = 0 := by
    intro M hM
    simp only [gap, hT]
    exact sub_eq_zero.mpr (hyp M hM)
  let G : Matrix (Fin N) (Fin N) (MvPolynomial (Fin N × Fin N) Ω) :=
    Matrix.of fun a b => if ((a : ℕ) < N - j ↔ (b : ℕ) < N - j) then X (a, b) else 0
  have hP : gap T c₀ c₁ coef u J (MvPolynomial (Fin N × Fin N) Ω) G = 0 := by
    apply MvPolynomial.funext
    intro x
    show aeval x (gap T c₀ c₁ coef u J (MvPolynomial (Fin N × Fin N) Ω) G) = aeval x 0
    rw [map_zero, gap_map]
    apply key
    intro a b hab
    simp only [G, Matrix.map_apply, Matrix.of_apply, if_neg hab, map_zero]
  have hG : G.map (aeval (fun p : Fin N × Fin N => h p.1 p.2)).toRingHom = h := by
    ext a b
    simp only [G, Matrix.map_apply, Matrix.of_apply]
    split_ifs with hab
    · simp [aeval_X]
    · rw [map_zero]
      exact (hh a b hab).symm
  have hz := congrArg (aeval (fun p : Fin N × Fin N => h p.1 p.2)) hP
  rw [gap_map, hG, map_zero] at hz
  simp only [gap] at hz
  exact sub_eq_zero.mp hz

end GlobalTheory.CompanionTheory.Ar.PB.MinorAny
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ]

def tauAt (ha : a ≤ n) (T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ)
    (w : Fin n → ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  T0 (expCover a w) + ∑ j, (w (Fin.castLE ha j) / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))

structure IsChart (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ)
    (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ) : Prop where
  form : ∀ i j, L.E (bas (.inl i)) (bas (.inl j)) = 0 ∧ L.E (bas (.inr i)) (bas (.inr j)) = 0 ∧
    L.E (bas (.inl i)) (bas (.inr j)) = if i = j then -1 else 0
  A_cont : ContinuousOn A (Metric.ball 0 1)
  A_det : (A 0).det ≠ 0
  T_cont : ContinuousOn T0 (Metric.ball 0 1)
  B_psd : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef
  c_pos : 0 < c
  ρ_pos : 0 < ρ
  ρ_le : ρ ≤ 1
  im_lower : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ l : Fin a → ℂ,
    (∀ j, Complex.exp (l j) = z (Fin.castLE L.a_le j)) →
    ((T0 z + ∑ j, (l j / (2 * Real.pi * Complex.I)) • (B j).map (fun x : ℤ => (x : ℂ))).map
      Complex.im - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef
  sym : ∀ w ∈ logCover L.a_le, (tauAt L.a_le T0 B w)ᵀ = tauAt L.a_le T0 B w
  im_pos : ∀ w ∈ logCover L.a_le, ((tauAt L.a_le T0 B w).map Complex.im).PosDef
  per : ∀ w ∈ logCover L.a_le, ∀ x, L.P w x =
    (A (expCover a w))ᵀ *ᵥ (cst (uCo bas x) + tauAt L.a_le T0 B w *ᵥ cst (vCo bas x))

theorem exists_isChart (L : Flat.LogPeriods n a g Λ) : ∃ bas A T0 B c ρ, IsChart L bas A T0 B c ρ := by
  obtain ⟨bas, Q, A, T0, hE, hAd, hA0, hT0, hBpsd, hPa, hPb⟩ := GlobalTheory.T.symplectic_polydisc_period_basis n a g Λ L
  obtain ⟨ρ₁, c, C₁, hρ₁, hρ₁1, hc, hb⟩ :=
    (ImTauBounds.cond RiemannExtensionSlices.proof PuncturedExpOrder.proof LogCoverDescent.proof) n a g Q
  have hAc : ContinuousOn A (Metric.ball 0 1) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hAd i j).continuousOn
  have hTc : ContinuousOn T0 (Metric.ball 0 1) :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => (hT0.1 i j).continuousOn
  have hQa : Q.a_le = L.a_le := rfl
  have hτ : ∀ w ∈ logCover L.a_le, Q.τ w = tauAt L.a_le T0 Q.B w := by
    intro w hw
    have h := hT0.2 w hw
    simp only [PeriodPolydisc.tau0] at h
    simp only [tauAt]
    rw [← h]
    exact (sub_add_cancel _ _).symm
  refine ⟨bas, A, T0, Q.B, c, ρ₁, hE, hAc, hA0, hTc, hBpsd, hc, hρ₁, hρ₁1.le, ?_, ?_, ?_, ?_⟩
  · intro z hz l hl
    have hz1 : ∀ k, ‖z k‖ < 1 := fun k =>
      lt_of_le_of_lt (norm_le_pi_norm z k)
        (lt_trans (by simpa [dist_zero_right] using hz) hρ₁1)
    let w : Fin n → ℂ := fun k => if h : k.val < a then l ⟨k.val, h⟩ else z k
    have hwj : ∀ j : Fin a, w (Fin.castLE L.a_le j) = l j := by
      intro j
      have hj : (Fin.castLE L.a_le j).val < a := j.2
      simp [w, hj]
    have hexp : expCover a w = z := by
      funext k
      by_cases hk : k.val < a
      · have := hl ⟨k.val, hk⟩
        simp only [expCover, hk, if_true, w, dif_pos]
        rw [this]
        rfl
      · simp [expCover, hk, w]
    have hw : w ∈ logCover L.a_le := by
      refine ⟨fun i => ?_, fun k hk => ?_⟩
      · rw [hwj]
        have h1 : ‖Complex.exp (l i)‖ < 1 := by rw [hl i]; exact hz1 _
        rw [Complex.norm_exp] at h1
        exact Real.exp_lt_one_iff.1 h1
      · have hk' : ¬ k.val < a := not_lt.2 hk
        simp only [w, hk', dif_neg, not_false_eq_true]
        exact hz1 k
    have h1 := (hb w hw (by rw [hexp]; exact Metric.ball_subset_closedBall hz)).1
    rw [hτ w hw] at h1
    simp only [tauAt, hexp, hwj] at h1
    exact h1
  · intro w hw
    rw [← hτ w hw]
    exact Q.symm w hw
  · intro w hw
    rw [← hτ w hw]
    exact Q.im_posDef w hw
  · intro w hw x
    rw [← hτ w hw]
    exact per_coords bas (L.P w) (Q.τ w) (A (expCover a w)) (Q.symm w hw) (hPa w hw) (hPb w hw) x

def chartS (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (x : Λ)
    (z : Fin n → ℂ) : Fin g → ℂ :=
  (A z)ᵀ *ᵥ (cst (uCo bas x) + T0 z *ᵥ cst (vCo bas x))

def chartW (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) : Submodule ℤ Λ :=
  LinearMap.ker ((∑ j, B j).mulVecLin ∘ₗ vCo bas)

def chartPer (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) : chartW bas B →+ (Fin g → ℂ) :=
  AddMonoidHom.mk' (fun x => chartS bas A T0 (x : Λ) 0) (fun x y => by
    simp only [chartS, Submodule.coe_add, map_add (f := _), cst_add, mulVec_add]
    abel_nf)

def IsKerProj (S : Matrix (Fin g) (Fin g) ℤ) (Pr : Matrix (Fin g) (Fin g) ℝ) : Prop :=
  Pr * Pr = Pr ∧ Prᵀ = Pr ∧ ∀ v : Fin g → ℝ, S.map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 ↔ Pr *ᵥ v = v

def compInv (Pr Y : Matrix (Fin g) (Fin g) ℝ) : Matrix (Fin g) (Fin g) ℝ :=
  Pr * (Pr * Y * Pr + (1 - Pr))⁻¹ * Pr

def chartQ (Pr : Matrix (Fin g) (Fin g) ℝ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (z : Fin n → ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  (A z)⁻¹ * (compInv Pr ((T0 z).map Complex.im)).map (fun x : ℝ => (x : ℂ)) * ((A z)ᴴ)⁻¹

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.GramPot

variable {N : ℕ}

theorem mul_selM_apply {m : Type} (A : Matrix m (Fin N) ℂ) (S : Finset (Fin N)) (a : m) (b : Fin S.card) :
    (A * selM S) a b = A a (S.orderEmbOfFin rfl b) := by
  rw [Matrix.mul_apply]
  simp [selM, Matrix.of_apply]

theorem selM_conjTranspose_mul_mul (A : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) :
    (selM S)ᴴ * A * selM S = A.submatrix (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl) := by
  ext a b
  rw [mul_selM_apply, Matrix.mul_apply]
  simp [selM, Matrix.conjTranspose_apply, Matrix.of_apply, apply_ite]

theorem det_selM (A : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) :
    ((selM S)ᴴ * A * selM S).det = minorIJ A S S := by
  rw [selM_conjTranspose_mul_mul, minorIJ, dite_eq_left rfl]

theorem selM_transpose (S : Finset (Fin N)) (b : Fin S.card) :
    (selM S)ᵀ b = Pi.basisFun ℂ (Fin N) (S.orderEmbOfFin rfl b) := by
  ext a
  simp [selM, Matrix.transpose_apply, Matrix.of_apply, Pi.single_apply]

theorem linearIndependent_selM (S : Finset (Fin N)) : LinearIndependent ℂ (selM S)ᵀ := by
  have h := (Pi.basisFun ℂ (Fin N)).linearIndependent.comp _ (S.orderEmbOfFin rfl).injective
  have e : (selM S)ᵀ = (Pi.basisFun ℂ (Fin N)) ∘ (S.orderEmbOfFin rfl) := funext fun b => selM_transpose S b
  rw [e]
  exact h

theorem linearIndependent_mul_selM {h : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) (S : Finset (Fin N)) :
    LinearIndependent ℂ (h * selM S)ᵀ := by
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 hd.isUnit
  have hi : Function.Injective h.mulVecLin := Matrix.mulVec_injective_of_isUnit hu
  have := (linearIndependent_selM S).map' h.mulVecLin (LinearMap.ker_eq_bot.2 hi)
  have e : (h * selM S)ᵀ = h.mulVecLin ∘ (selM S)ᵀ := by
    funext b
    ext a
    rfl
  rw [e]
  exact this

theorem minor_pos {G : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (S : Finset (Fin N)) :
    0 < minorIJ G S S := by
  rw [minorIJ, dite_eq_left rfl]
  exact (hG.submatrix (S.orderEmbOfFin rfl).injective).det_pos

theorem log_re_mul {a b : ℂ} (ha : 0 < a) (hb : 0 < b) :
    Real.log (a * b).re = Real.log a.re + Real.log b.re := by
  have ha' := Complex.lt_def.1 ha
  have hb' := Complex.lt_def.1 hb
  have hi : a.im = 0 := ha'.2.symm
  rw [Complex.mul_re, hi, zero_mul, sub_zero]
  exact Real.log_mul ha'.1.ne' hb'.1.ne'

theorem gram_mul_selM (G h : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) :
    ((h * selM S)ᴴ * G * (h * selM S)).det = minorIJ (hᴴ * G * h) S S := by
  rw [← det_selM, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem blockPot_eq_gram (N j : ℕ) (i : Fin N) (G h : Matrix (Fin N) (Fin N) ℂ) :
    (∀ S : Finset (Fin N), LinearIndependent ℂ (selM S)ᵀ) ∧
    (h.det ≠ 0 → ∀ S : Finset (Fin N), LinearIndependent ℂ (h * selM S)ᵀ) ∧
    (G.PosDef → blockPot j i G h = (1 / 2) * ((if j ≤ (i : ℕ) + 1 then Real.log ((selM (wIdx N j))ᴴ * G * selM (wIdx N j)).det.re else 0) + (if (i : ℕ) + 1 = N then Real.log ((selM (omIdx N j))ᴴ * G * selM (omIdx N j)).det.re else 0) + (if IsProperStep N j i then Real.log ((h * selM (stepCols N j i))ᴴ * G * (h * selM (stepCols N j i))).det.re else 0))) := by
  refine ⟨linearIndependent_selM, fun hd S => linearIndependent_mul_selM hd S, fun hG => ?_⟩
  simp only [det_selM, gram_mul_selM, blockPot, detFac]
  have hW := minor_pos hG (wIdx N j)
  have hO := minor_pos hG (omIdx N j)
  split_ifs <;>
    simp only [one_mul, mul_one, Complex.one_re, Real.log_one, log_re_mul hW hO] <;> ring

end GlobalTheory.CompanionTheory.Ar.PB.StepW.GramPot
end
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart

theorem differentiableOn_prod' {n : ℕ} {U : Set (Fin n → ℂ)} {ι : Type} (u : Finset ι) {f : ι → (Fin n → ℂ) → ℂ}
    (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) U) : DifferentiableOn ℂ (fun t => ∏ i ∈ u, f i t) U :=
  _root_.UpperTheory.Reformulated.B.Yhd5.main u h

theorem differentiableOn_det' {n m : ℕ} {U : Set (Fin n → ℂ)} {M : (Fin n → ℂ) → Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ a b, DifferentiableOn ℂ (fun t => M t a b) U) : DifferentiableOn ℂ (fun t => (M t).det) U := by
  simp only [Matrix.det_apply]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  refine DifferentiableOn.const_smul ?_ _
  exact differentiableOn_prod' _ fun i _ => h _ _

theorem chart_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (A₀ : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ), C.IsAdapted (F.R 0) A₀ → ∃ (Z : (Fin n → ℂ) → Fin n → ℂ) (G : (Fin n → ℂ) → ℂ), DifferentiableOn ℂ Z (ballDom F.q) ∧ DifferentiableOn ℂ G (ballDom F.q) ∧ (∀ t ∈ ballDom F.q, ∀ A, C.IsAdapted (F.R t) A → Z t = moebBall F.q (fun τ => C.cinv (A₀ τ) τ * A τ) 0) ∧ ∀ t ∈ ballDom F.q, ballPot F.q (Z t) = ballPot F.q t + (G t).re := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C A₀ h₀
  obtain ⟨hUo, hUc, hU0⟩ := GlobalTheory.T.ball_domain_open_convex_zero Ψ j j' n F.q
  have hunit : ∀ τ, (A₀ τ)ᴴ * C.sgr τ * A₀ τ = sgI j j' := h₀.unit
  have hex : ∀ t, ∃ A, t ∈ ballDom F.q → C.IsAdapted (F.R t) A := fun t => by
    by_cases ht : t ∈ ballDom F.q
    · obtain ⟨A, hA⟩ := GlobalTheory.T.exists_adapted_frame_bis E Ψ j j' n g Λ F C (F.R t) (F.form_eq t) (F.sig t ht)
      exact ⟨A, fun _ => hA⟩
    · exact ⟨A₀, fun h => absurd h ht⟩
  choose Ad hAd using hex

  let dV : Ψ → Fin j' → (Fin n → ℂ) → Fin g → ℂ :=
    fun τ b t => C.pPart (F.R t) τ (A₀ τ *ᵥ Sum.elim 0 (Pi.single b 1))
  let aV : Ψ → Fin j → (Fin n → ℂ) → Fin g → ℂ :=
    fun τ i t => C.pPart (F.R t) τ (A₀ τ *ᵥ Sum.elim (Pi.single i 1) 0)
  let Wm : (Fin n → ℂ) → Ψ → Matrix (Fin j') (Fin j) ℂ := fun t τ => moebW (C.cinv (A₀ τ) τ * Ad t τ) 0
  have hgA := fun t (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (hA : C.IsAdapted (F.R t) A) =>
    GlobalTheory.T.adapted_frame_hermitian_product E Ψ j j' n g Λ F C (F.R t) A (GlobalTheory.T.period_extension_imaginary_form E Ψ j j' n g Λ F C (F.R t) (F.form_eq t)) hA
  have hpt := fun t (ht : t ∈ ballDom F.q) τ =>
    GlobalTheory.T.adapted_frame_ball_coordinate E Ψ j j' n g Λ F C (F.R t) (Ad t) A₀ τ (Wm t τ) (GlobalTheory.T.signature_unitary_blocks_invertible j j') (hgA t (Ad t) (hAd t ht) τ) (hAd t ht) (hunit τ) rfl

  have hgram : ∀ t ∈ ballDom F.q, ∀ τ, IsUnit (F.R t |>.gram fun b => dV τ b t).det := by
    intro t ht τ
    have h := (hpt t ht τ).2.1
    have hc : ((2 * C.c : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (mul_pos two_pos C.c_pos).ne'
    have h2 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h2
    exact isUnit_iff_ne_zero.2 (left_ne_zero_of_mul (h2 ▸ pow_ne_zero _ hc))
  have hind : ∀ t ∈ ballDom F.q, ∀ τ, LinearIndependent ℂ (fun b => dV τ b t) := fun t ht τ =>
    GlobalTheory.T.linearIndependent_of_gram_det_unit E g Λ (F.R t) j' _ (hgram t ht τ)

  have hrel : ∀ t, ∀ τ (W : Matrix (Fin j') (Fin j) ℂ),
      (∀ v : Fin j → ℂ, C.pPart (F.R t) τ (A₀ τ *ᵥ Sum.elim v (W *ᵥ v)) = 0) → ∀ i,
      -aV τ i t = ∑ b, W b i • dV τ b t := by
    intro t τ W hW i
    have h := hW (Pi.single i 1)
    rw [pPart_elim] at h
    have hWv : ∀ b, (W *ᵥ Pi.single i 1) b = W b i := by
      intro b; simp
    simp only [hWv, Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] at h
    exact (eq_neg_of_add_eq_zero_right h).symm ▸ by simp [aV, dV]

  have huniq : ∀ t ∈ ballDom F.q, ∀ τ (W W' : Matrix (Fin j') (Fin j) ℂ),
      (∀ v : Fin j → ℂ, C.pPart (F.R t) τ (A₀ τ *ᵥ Sum.elim v (W *ᵥ v)) = 0) →
      (∀ v : Fin j → ℂ, C.pPart (F.R t) τ (A₀ τ *ᵥ Sum.elim v (W' *ᵥ v)) = 0) → W = W' := by
    intro t ht τ W W' hW hW'
    ext b i
    have h1 := hrel t τ W hW i
    have h2 := hrel t τ W' hW' i
    have h3 : ∑ b, (W b i - W' b i) • dV τ b t = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, ← h1, ← h2, sub_self]
    have := Fintype.linearIndependent_iff.1 (hind t ht τ) _ h3 b
    exact sub_eq_zero.1 this

  have hdV : ∀ τ b, DifferentiableOn ℂ (dV τ b) (ballDom F.q) := fun τ b =>
    GlobalTheory.T.holomorphic_eigen_projection_on_ball E Ψ j j' n g Λ F C τ _
  have haV : ∀ τ i, DifferentiableOn ℂ (aV τ i) (ballDom F.q) := fun τ i =>
    GlobalTheory.T.holomorphic_eigen_projection_on_ball E Ψ j j' n g Λ F C τ _

  have hWd : ∀ τ i, DifferentiableOn ℂ (fun t b => Wm t τ b i) (ballDom F.q) := fun τ i =>
    GlobalTheory.T.holomorphic_coefficients_in_frame n j' g _ (fun b => dV τ b) (fun t => -aV τ i t) (fun t b => Wm t τ b i) hUo (hdV τ) (haV τ i).neg
      (fun t ht => hind t ht τ) (fun t ht => hrel t τ _ (hpt t ht τ).1 i)

  have hY : ∀ t τ b, ∃ c : Fin j' → ℂ, t ∈ ballDom F.q → dV τ b t = ∑ i, c i • F.b τ i t := by
    intro t τ b
    by_cases ht : t ∈ ballDom F.q
    · have hm : dV τ b t ∈ Submodule.span ℂ (Set.range fun i => F.b τ i t) := by
        rw [((F.frames.2 t ht τ).2)]
        exact GlobalTheory.T.eigen_projection_in_eigenspace E Ψ j j' n g Λ F C (F.R t) τ _
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hm
      exact ⟨c, fun _ => hc.symm⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose Yc hYc using hY
  let Ym : (Fin n → ℂ) → Ψ → Matrix (Fin j') (Fin j') ℂ := fun t τ => Matrix.of fun c b => Yc t τ b c
  have hYd : ∀ τ b, DifferentiableOn ℂ (fun t => Yc t τ b) (ballDom F.q) := fun τ b =>
    GlobalTheory.T.holomorphic_coefficients_in_frame n j' g _ (F.b τ) (dV τ b) (fun t => Yc t τ b) hUo (F.frames.1 τ) (hdV τ b)
      (fun t ht => (F.frames.2 t ht τ).1) (fun t ht => hYc t τ b ht)

  have hloc := fun t (ht : t ∈ ballDom F.q) τ =>
    GlobalTheory.T.gram_det_change_of_basis_alt E g Λ (F.R t) j' (fun i => F.b τ i t) (fun b => dV τ b t) (Ym t τ) (1 - Wm t τ * (Wm t τ)ᴴ) (2 * C.c)
      (mul_pos two_pos C.c_pos) (fun b => hYc t τ b ht) (hpt t ht τ).2.1 (hpt t ht τ).2.2

  let Pf : (Fin n → ℂ) → ℂ := fun t => ∏ τ, (Ym t τ).det
  have hPd : DifferentiableOn ℂ Pf (ballDom F.q) := by
    refine differentiableOn_prod' _ fun τ _ => differentiableOn_det' fun a b => ?_
    exact (differentiableOn_pi.1 (hYd τ b)) a
  have hP0 : ∀ t ∈ ballDom F.q, Pf t ≠ 0 := fun t ht =>
    Finset.prod_ne_zero_iff.2 fun τ _ => (hloc t ht τ).1
  obtain ⟨G₀, hG₀a, hG₀⟩ := GroundTheory.Heights₂.Heights.Regular.exists_analytic_log hUo hUc ⟨0, hU0⟩
    (ReciprocityTheory.AnForm.Osgood.osgood n _ Pf hUo hPd) hP0
  have hG₀d : DifferentiableOn ℂ G₀ (ballDom F.q) := hG₀a.differentiableOn
  refine ⟨fun t => ballPt F.q (Wm t), fun t => 2 * G₀ t - ((Fintype.card Ψ * j' * Real.log (2 * C.c) : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · refine differentiableOn_pi.2 fun k => ?_
    exact (differentiableOn_pi.1 (hWd _ _)) _
  · exact (hG₀d.const_mul 2).sub_const _
  · intro t ht A hA
    have hb0 : ∀ τ, ballMat F.q 0 τ = 0 := fun τ => by ext a b; simp [ballMat]
    have : (fun τ => Wm t τ) = fun τ => moebW (C.cinv (A₀ τ) τ * A τ) ((ballMat F.q 0 τ)ᵀ) := by
      funext τ
      rw [hb0, Matrix.transpose_zero]
      exact huniq t ht τ _ _ (hpt t ht τ).1
        (GlobalTheory.T.adapted_frame_ball_coordinate E Ψ j j' n g Λ F C (F.R t) A A₀ τ _ (GlobalTheory.T.signature_unitary_blocks_invertible j j') (hgA t A hA τ) hA (hunit τ) rfl).1
    simp only [moebBall]
    exact congrArg (ballPt F.q) this
  · intro t ht
    have hre : (G₀ t).re = ∑ τ, Real.log ‖(Ym t τ).det‖ := by
      have h1 : ‖Pf t‖ = Real.exp (G₀ t).re := by rw [← hG₀ t ht, Complex.norm_exp]
      have h2 : Real.log ‖Pf t‖ = (G₀ t).re := by rw [h1, Real.log_exp]
      rw [← h2, norm_prod, Real.log_prod]
      intro τ _
      exact norm_ne_zero_iff.2 (hloc t ht τ).1
    rw [GlobalTheory.T.ball_potential_formula, ← F.logDet_eq t ht]
    simp only [RiemLat.logDet, ← Finset.sum_neg_distrib]
    simp only [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, Complex.ofReal_re, zero_mul, sub_zero, hre]
    rw [Finset.sum_congr rfl fun τ _ => (hloc t ht τ).2]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Finset.mul_sum]
    ring

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart
end
end
