module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle119
import Formalism.FormalDegreeBessel.FinalG
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameEntries
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle082
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LeftDerivativeCurves
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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

@[expose] public section

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace SD

theorem hasDeriv_form {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) {γ : ℝ → Matrix (Fin n) (Fin n) ℂ}
    {g γ' : Matrix (Fin n) (Fin n) ℂ} (h0 : γ 0 = g) (h : ∀ a b, HasDerivAt (fun t => γ t a b) (γ' a b) 0)
    (i j : Fin n) :
    HasDerivAt (fun t => ((γ t)ᴴ * H * γ t) i j) ((γ'ᴴ * H * g + gᴴ * H * γ') i j) 0 := by
  have hγ : ∀ a b, γ 0 a b = g a b := fun a b => by rw [h0]
  have key : ∀ a b, HasDerivAt (fun t => star (γ t a i) * H a b * γ t b j)
      (star (γ' a i) * H a b * g b j + star (g a i) * H a b * γ' b j) 0 := by
    intro a b
    have h1 : HasDerivAt (fun t => star (γ t a i) * H a b * γ t b j)
        (star (γ' a i) * H a b * γ 0 b j + star (γ 0 a i) * H a b * γ' b j) 0 :=
      (((h a i).star).mul_const (H a b)).mul (h b j)
    rw [hγ a i, hγ b j] at h1
    exact h1
  have hs := HasDerivAt.sum (u := Finset.univ) fun b _ =>
    HasDerivAt.sum (u := Finset.univ) fun a _ => key a b
  simp only [Finset.sum_fn] at hs
  have e1 : (fun t => ((γ t)ᴴ * H * γ t) i j) =
      fun t => ∑ b, ∑ a, star (γ t a i) * H a b * γ t b j := by
    funext t
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  have e2 : (γ'ᴴ * H * g + gᴴ * H * γ') i j =
      ∑ b, ∑ a, (star (γ' a i) * H a b * g b j + star (g a i) * H a b * γ' b j) := by
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
      Finset.sum_add_distrib]
  rw [e1, e2]
  exact hs

variable {k r : ℕ}

theorem lie_of_curve {μ : ℂ → Q.Mx k r} {ζ : ℂ} {D : ℂ →L[ℝ] Q.Mx k r} (hD : HasFDerivAt μ D ζ)
    (hG : ∀ᶠ w in 𝓝 ζ, μ w ∈ Q.Glev k r (Fin.last r)) (v : ℂ) :
    Q.inLieLev k r (Fin.last r) ((μ ζ)⁻¹ * D v) := by
  have hℓ : HasDerivAt (fun t : ℝ => ζ + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add ζ
  have hγ : HasDerivAt (fun t : ℝ => μ (ζ + t • v)) (D v) 0 := by
    have hD' : HasFDerivAt μ D (ζ + (0 : ℝ) • v) := by simpa using hD
    exact hD'.comp_hasDerivAt (0 : ℝ) hℓ
  have hent : ∀ a b, HasDerivAt (fun t : ℝ => μ (ζ + t • v) a b) (D v a b) 0 := by
    intro a b
    exact hasDerivAt_pi.1 (hasDerivAt_pi.1 hγ a) b
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), μ (ζ + t • v) ∈ Q.Glev k r (Fin.last r) := by
    have ht : Tendsto (fun t : ℝ => ζ + t • v) (𝓝 0) (𝓝 ζ) := by
      simpa using hℓ.continuousAt.tendsto
    exact ht.eventually hG
  have hU : (μ ζ)ᴴ * Hpk k r * μ ζ = Hpk k r := hG.self_of_nhds.1
  have hder : (D v)ᴴ * Hpk k r * μ ζ + (μ ζ)ᴴ * Hpk k r * D v = 0 := by
    ext i j
    have h1 := hasDeriv_form (Hpk k r) (γ := fun t : ℝ => μ (ζ + t • v)) (g := μ ζ) (γ' := D v)
      (by simp) hent i j
    have h2 : HasDerivAt (fun t : ℝ => ((μ (ζ + t • v))ᴴ * Hpk k r * μ (ζ + t • v)) i j) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (Hpk k r i j)).congr_of_eventuallyEq (hev.mono fun t ht => by
        show ((μ (ζ + t • v))ᴴ * Hpk k r * μ (ζ + t • v)) i j = Hpk k r i j
        rw [show (μ (ζ + t • v))ᴴ * Hpk k r * μ (ζ + t • v) = Hpk k r from ht.1])
    exact h1.unique h2
  have hH : (Hpk k r).det ≠ 0 := by
    have h1 := congrArg Matrix.det (Formalism.QuantumDeterminants.hpkFacts k r).2.1
    rw [Matrix.det_mul, Matrix.det_one] at h1
    intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hdet : IsUnit (μ ζ).det := by
    have h2 := congrArg Matrix.det hU
    rw [Matrix.det_mul, Matrix.det_mul] at h2
    refine isUnit_iff_ne_zero.2 fun h0 => hH ?_
    rw [h0, mul_zero] at h2
    exact h2.symm
  have hgi : μ ζ * (μ ζ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have e1 : ((μ ζ)⁻¹)ᴴ * Hpk k r = Hpk k r * μ ζ := by
    calc ((μ ζ)⁻¹)ᴴ * Hpk k r = ((μ ζ)⁻¹)ᴴ * ((μ ζ)ᴴ * Hpk k r * μ ζ) := by rw [hU]
      _ = (μ ζ * (μ ζ)⁻¹)ᴴ * Hpk k r * μ ζ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = Hpk k r * μ ζ := by rw [hgi, Matrix.conjTranspose_one, Matrix.one_mul]
  have e2 : Hpk k r * (μ ζ)⁻¹ = (μ ζ)ᴴ * Hpk k r := by
    calc Hpk k r * (μ ζ)⁻¹ = (μ ζ)ᴴ * Hpk k r * μ ζ * (μ ζ)⁻¹ := by rw [hU]
      _ = (μ ζ)ᴴ * Hpk k r := by rw [Matrix.mul_assoc, hgi, Matrix.mul_one]
  have hvec : ∀ w : Fin (2 * r + k + 1) → ℂ, (∀ᶠ t in 𝓝 (0 : ℝ), μ (ζ + t • v) *ᵥ w = w) →
      D v *ᵥ w = 0 := by
    intro w hw
    funext q
    have hd : HasDerivAt (fun t : ℝ => (μ (ζ + t • v) *ᵥ w) q) ((D v *ᵥ w) q) 0 := by
      simp only [Matrix.mulVec, dotProduct]
      first
      | exact HasDerivAt.sum fun p _ => (hent q p).mul_const (w p)
      | exact HasDerivAt.fun_sum fun p _ => (hent q p).mul_const (w p)
    have hc : HasDerivAt (fun t : ℝ => (μ (ζ + t • v) *ᵥ w) q) 0 0 :=
      (hasDerivAt_const (0 : ℝ) (w q)).congr_of_eventuallyEq (hw.mono fun t ht => by
        show (μ (ζ + t • v) *ᵥ w) q = w q
        rw [ht])
    exact hd.unique hc
  unfold Q.inLieLev
  refine ⟨?_, fun a ha => ⟨?_, ?_⟩⟩
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc (Hpk k r), e2,
      ← Matrix.mul_assoc]
    exact hder
  · rw [← Matrix.mulVec_mulVec, hvec _ (hev.mono fun t ht => (ht.2 a ha).1), Matrix.mulVec_zero]
  · rw [← Matrix.mulVec_mulVec, hvec _ (hev.mono fun t ht => (ht.2 a ha).2), Matrix.mulVec_zero]

end SD

theorem section_derivative_holds : SecDeriv := by
  intro k r z z' hk hz hz' hT hT' ζ hζ
  have hsec := TheSec.theSection_isSection k r z z' hk hz hz' hT hT'
  have hA : IsOpen {w : ℂ | Tz k r z * Tz k r z' < Complex.normSq w} :=
    isOpen_lt continuous_const Complex.continuous_normSq
  have hcd : ContDiffOn ℝ ∞ (mu0 k r z z') {w : ℂ | Tz k r z * Tz k r z' < Complex.normSq w} :=
    NFRadRedA.muZ_contDiffOn hsec
  have hdiff : DifferentiableAt ℝ (mu0 k r z z') ζ :=
    (hcd.differentiableOn (by simp)).differentiableAt (hA.mem_nhds hζ)
  obtain ⟨D, hD⟩ : ∃ D : ℂ →L[ℝ] Q.Mx k r, HasFDerivAt (mu0 k r z z') D ζ := ⟨_, hdiff.hasFDerivAt⟩
  have hG : ∀ᶠ w in 𝓝 ζ, mu0 k r z z' w ∈ Q.Glev k r (Fin.last r) := by
    filter_upwards [hA.mem_nhds hζ] with w hw
    exact NFRadRedA.uwb_glev (NFRadRedA.muZ_uwb hsec hw)
  have hg : mu0 k r z z' ζ ∈ Q.Glev k r (Fin.last r) := hG.self_of_nhds
  have hX := SD.lie_of_curve hD hG
  have hrow : ∀ i, HasFDerivAt (fun w => mu0 k r z z' w i) ((ContinuousLinearMap.proj i).comp D) ζ :=
    hasFDerivAt_pi'.1 hD
  have hent : ∀ i j v, fderiv ℝ (fun w => mu0 k r z z' w i j) ζ v = D v i j := by
    intro i j v
    have h := (hasFDerivAt_pi'.1 (hrow i)) j
    rw [h.fderiv]
    rfl
  have hs1 : D ((1 / 2 : ℝ) • (1 : ℂ)) = (1 / 2 : ℝ) • D 1 := map_smul D _ _
  have hs2 : D ((-(1 / 2) : ℝ) • Complex.I) = (-(1 / 2) : ℝ) • D Complex.I := map_smul D _ _
  have hs3 : D ((1 / 2 : ℝ) • Complex.I) = (1 / 2 : ℝ) • D Complex.I := map_smul D _ _
  have e1 : etaZ k r z z' ζ = (mu0 k r z z' ζ)⁻¹ * D ((1 / 2 : ℝ) • (1 : ℂ)) +
      Complex.I • ((mu0 k r z z' ζ)⁻¹ * D ((-(1 / 2) : ℝ) • Complex.I)) := by
    unfold etaZ
    rw [← Matrix.mul_smul, ← Matrix.mul_add, hs1, hs2]
    congr 1
    ext i j
    simp only [Matrix.of_apply, NF.dZ, hent, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  have e2 : etaZb k r z z' ζ = (mu0 k r z z' ζ)⁻¹ * D ((1 / 2 : ℝ) • (1 : ℂ)) +
      Complex.I • ((mu0 k r z z' ζ)⁻¹ * D ((1 / 2 : ℝ) • Complex.I)) := by
    unfold etaZb
    rw [← Matrix.mul_smul, ← Matrix.mul_add, hs1, hs3]
    congr 1
    ext i j
    simp only [Matrix.of_apply, NF.dZb, hent, Matrix.add_apply, Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    ring
  obtain ⟨p1, p2⟩ := Qx5.hpart_unique (hX ((1 / 2 : ℝ) • (1 : ℂ))) (hX ((-(1 / 2) : ℝ) • Complex.I))
  obtain ⟨q1, q2⟩ := Qx5.hpart_unique (hX ((1 / 2 : ℝ) • (1 : ℂ))) (hX ((1 / 2 : ℝ) • Complex.I))
  rw [← e1] at p1 p2
  rw [← e2] at q1 q2
  have hmem : mu0 k r z z' ζ ∈ Q.Glev k r (Fin.last r) ∩ Dp k r z z' := by
    refine ⟨hg, ?_⟩
    show 0 < Complex.normSq (Q.zetaL k r z z' (Fin.last r) (NF.muZ k r (TheSec.theSection k r z z') ζ)) -
      Tz k r z * Tz k r z'
    rw [NFRadRedA.zeta_muZ hz hz' hsec hζ]
    linarith
  refine ⟨⟨by rw [p1]; exact hX _, by rw [p2]; exact hX _⟩, ⟨by rw [q1]; exact hX _, by rw [q2]; exact hX _⟩, hmem, ?_⟩
  intro E _ _ F hF
  obtain ⟨U, F', hU, hgU, hFc, he⟩ := hF _ hmem
  have hd : DifferentiableAt ℝ F' (mu0 k r z z' ζ) :=
    (hFc.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hgU)
  have hR : ∀ v, RdV ((mu0 k r z z' ζ)⁻¹ * D v) F (mu0 k r z z' ζ) = fderiv ℝ F' (mu0 k r z z' ζ) (D v) := by
    intro v
    have h := (Qx2.hasDeriv_ext hU hgU hg (hX v) hd he).deriv
    rw [← Matrix.mul_assoc, FrameEntries.mul_inv_uh hg.1, Matrix.one_mul] at h
    exact h
  have hC : HasFDerivAt (fun w => F (mu0 k r z z' w)) ((fderiv ℝ F' (mu0 k r z z' ζ)).comp D) ζ := by
    refine (hd.hasFDerivAt.comp ζ hD).congr_of_eventuallyEq ?_
    filter_upwards [hG, hD.continuousAt.preimage_mem_nhds (hU.mem_nhds hgU)] with w h1 h2
    exact he _ h2 h1
  constructor
  · unfold Rc dZV
    rw [p1, p2, hR, hR, hC.fderiv, hs1, hs2]
    simp only [ContinuousLinearMap.comp_apply, map_smul]
    rw [← Complex.coe_smul, ← Complex.coe_smul]
    push_cast
    module
  · unfold Rc dZbV
    rw [q1, q2, hR, hR, hC.fderiv, hs1, hs3]
    simp only [ContinuousLinearMap.comp_apply, map_smul]
    rw [← Complex.coe_smul, ← Complex.coe_smul]
    push_cast
    module

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

theorem rdV_leftCov {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp]
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} (hπ : IsCRepOn (UWset k r z) π) (hc : ContinuousOn π (UWset k r z))
    {D : Set (Q.Mx k r)} {F : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hF : ∀ h ∈ UWset k r z, ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, F (h * g) = (π h).comp (F g))
    {μ : Q.Mx k r} (hμ : μ ∈ Q.Glev k r (Fin.last r) ∩ D) {X : Q.Mx k r} (hX : P.QrD.InLieW k r z X) :
    RdV (μ⁻¹ * X * μ) F μ = (P.QrD.dOp π X).comp (F μ) := by
  have hU : μᴴ * Hpk k r * μ = Hpk k r := hμ.1.1
  have hdet : IsUnit μ.det := by
    apply Matrix.isUnit_det_of_left_inverse (B := Hpk k r * μᴴ * Hpk k r)
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc μᴴ, hU, Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  have hμu : IsUnit μ := (Matrix.isUnit_iff_isUnit_det μ).mpr hdet
  have key : ∀ t : ℝ, F (μ * NormedSpace.exp ((t : ℂ) • (μ⁻¹ * X * μ))) =
      (π (NormedSpace.exp ((t : ℂ) • X))).comp (F μ) := by
    intro t
    rw [show (t : ℂ) • (μ⁻¹ * X * μ) = μ⁻¹ * ((t : ℂ) • X) * μ by rw [Matrix.mul_smul, Matrix.smul_mul],
      Matrix.exp_conj' μ _ hμu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
    exact hF _ (Formalism.FourierDecayAlt.P.QrD.exp_uw hX t) μ hμ
  unfold Formalism.REAL.RdV
  simp only [key]
  let L : (Wp →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp) :=
    ((ContinuousLinearMap.compL ℂ Wq Wp Wp).flip (F μ)).restrictScalars ℝ
  have hL : ∀ A, L A = A.comp (F μ) := fun A => rfl
  have hd : HasDerivAt (fun t : ℝ => L (π (NormedSpace.exp ((t : ℂ) • X)))) (L (P.QrD.dOp π X)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 (Formalism.FourierDecayAlt.P.QrD.dOp_hasDeriv hπ hc hX)
  simp only [hL] at hd
  exact hd.deriv

theorem left_covariance_holds : LeftCov := by
  intro k r z Wp Wq _ _ _ _ _ _ π hπ hc _ D F _ _ _ hF μ hμ B hB
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [P.LeftDerivativeCurves.hpart1_conj hμ.1.1]
    exact P.LeftDerivativeCurves.lie_conj hμ.1 hB.1.1
  · rw [P.LeftDerivativeCurves.hpart2_conj hμ.1.1]
    exact P.LeftDerivativeCurves.lie_conj hμ.1 hB.2.1
  · unfold Rc P.QrD.ecOp
    rw [P.LeftDerivativeCurves.hpart1_conj hμ.1.1, P.LeftDerivativeCurves.hpart2_conj hμ.1.1, rdV_leftCov hπ hc hF hμ hB.1,
      rdV_leftCov hπ hc hF hμ hB.2]
    ext v
    simp

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc

open Formalism.FourierDecayAlt.P.B2x3 Formalism.FourierDecayAlt.P.SettingConstruction Formalism.FourierDecayAlt.P.TheSec Formalism.FourierDecayAlt.B2

noncomputable section

set_option linter.unusedSimpArgs false

variable {k : ℕ}

def Su (k : ℕ) (i j : Fin (k + 1)) : Mb k := Matrix.single i j 1

lemma Su_mul (i j j' m : Fin (k + 1)) : Su k i j * Su k j' m = if j = j' then Su k i m else 0 := by
  unfold Su
  split_ifs with h
  · subst h
    rw [Matrix.single_mul_single_same, mul_one]
  · rw [Matrix.single_mul_single_of_ne _ _ _ _ h]

def nuG (k : ℕ) (v s w : ℂ) : Mb k :=
  1 + (v - 1) • Su k 0 0 + s • (Su k 0 (Fin.last k) + Su k (Fin.last k) 0) + (w - 1) • Su k (Fin.last k) (Fin.last k)

lemma nu_eq (w s : ℂ) : nu k w s = nuG k (star w) s w := by
  unfold nu nuG Su
  simp only [Matrix.single_eq_single_vecMulVec_single, Matrix.add_vecMulVec, Matrix.smul_vecMulVec]
  module

lemma dnu_eq (a b c : ℂ) : dnu k a b c =
    a • Su k 0 0 + b • (Su k 0 (Fin.last k) + Su k (Fin.last k) 0) + c • Su k (Fin.last k) (Fin.last k) := rfl

lemma nuG_mul (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w : ℂ) (hw : w * v - s * s = 1) :
    nuG k v s w * nuG k w (-s) v = 1 := by
  simp only [nuG, mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, Su_mul, h0, h0.symm, if_true,
    if_false, smul_zero, add_zero, zero_add]
  linear_combination (norm := module) hw • (Su k 0 0 + Su k (Fin.last k) (Fin.last k))

lemma conj_corner_matrix_unit (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w : ℂ) :
    nuG k w (-s) v * Su k 0 0 * nuG k v s w = (w * v) • Su k 0 0 + (w * s) • Su k 0 (Fin.last k) -
      (s * v) • Su k (Fin.last k) 0 - (s * s) • Su k (Fin.last k) (Fin.last k) := by
  simp only [nuG, mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, Su_mul, h0, h0.symm, if_true,
    if_false, smul_zero, add_zero, zero_add]
  module

lemma conj0m (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w : ℂ) (m : Fin (k + 1)) (hm0 : m ≠ 0) (hml : m ≠ Fin.last k) :
    nuG k w (-s) v * Su k 0 m * nuG k v s w = w • Su k 0 m - s • Su k (Fin.last k) m := by
  simp only [nuG, mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, Su_mul, h0, h0.symm, hm0, hml,
    hm0.symm, hml.symm, if_true, if_false, smul_zero, add_zero, zero_add]
  module

lemma conjm0 (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w : ℂ) (m : Fin (k + 1)) (hm0 : m ≠ 0) (hml : m ≠ Fin.last k) :
    nuG k w (-s) v * Su k m 0 * nuG k v s w = v • Su k m 0 + s • Su k m (Fin.last k) := by
  simp only [nuG, mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, Su_mul, h0, h0.symm, hm0, hml,
    hm0.symm, hml.symm, if_true, if_false, smul_zero, add_zero, zero_add]
  module

lemma nuI_dnu (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w a b c : ℂ) :
    nuG k w (-s) v * dnu k a b c = (w * a - s * b) • Su k 0 0 + (w * b - s * c) • Su k 0 (Fin.last k) +
      (-s * a + v * b) • Su k (Fin.last k) 0 + (-s * b + v * c) • Su k (Fin.last k) (Fin.last k) := by
  simp only [nuG, dnu_eq, mul_add, add_mul, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, Su_mul, h0, h0.symm, if_true,
    if_false, smul_zero, add_zero, zero_add]
  module

lemma unit0l (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w c p : ℂ) (hs : s ≠ 0) (hc : c ≠ 0) (hv : v ≠ 0)
    (hw : w * v - s * s = 1) (hp : 2 * s * p = -c * v) :
    Su k 0 (Fin.last k) = (-(v / (2 * s))) • Su k 0 0 + nuG k w (-s) v * ((v / (2 * s)) • Su k 0 0) * nuG k v s w +
      (-(s / c)) • (nuG k w (-s) v * dnu k 0 p (-c)) := by
  have hw' : w = (1 + s * s) / v := by field_simp; linear_combination hw
  have hp' : p = -c * v / (2 * s) := by field_simp; linear_combination hp
  subst hw' hp'
  rw [Matrix.mul_smul, Matrix.smul_mul, conj_corner_matrix_unit h0, nuI_dnu h0]
  match_scalars <;> field_simp <;> ring

lemma unitl0 (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w c q : ℂ) (hs : s ≠ 0) (hc : c ≠ 0) (hv : v ≠ 0)
    (hw : w * v - s * s = 1) (hq : 2 * s * q = -c * w) :
    Su k (Fin.last k) 0 = (w / (2 * s)) • Su k 0 0 + nuG k w (-s) v * ((-(w / (2 * s))) • Su k 0 0) * nuG k v s w +
      (-(s / c)) • (nuG k w (-s) v * dnu k (-c) q 0) := by
  have hw' : w = (1 + s * s) / v := by field_simp; linear_combination hw
  subst hw'
  have hq' : q = -c * ((1 + s * s) / v) / (2 * s) := by field_simp; field_simp at hq; linear_combination hq
  subst hq'
  rw [Matrix.mul_smul, Matrix.smul_mul, conj_corner_matrix_unit h0, nuI_dnu h0]
  match_scalars <;> field_simp <;> ring

lemma unitll (h0 : (0 : Fin (k + 1)) ≠ Fin.last k) (v s w c p q : ℂ) (hs : s ≠ 0) (hc : c ≠ 0) (hv : v ≠ 0)
    (hw : w * v - s * s = 1) (hp : 2 * s * p = -c * v) (hq : 2 * s * q = -c * w) :
    Su k (Fin.last k) (Fin.last k) = nuG k w (-s) v * Su k 0 0 * nuG k v s w +
      (-(w / c)) • (nuG k w (-s) v * dnu k 0 p (-c)) + (v / c) • (nuG k w (-s) v * dnu k (-c) q 0) := by
  have hw' : w = (1 + s * s) / v := by field_simp; linear_combination hw
  subst hw'
  have hp' : p = -c * v / (2 * s) := by field_simp; linear_combination hp
  have hq' : q = -c * ((1 + s * s) / v) / (2 * s) := by field_simp; field_simp at hq; linear_combination hq
  subst hp' hq'
  rw [conj_corner_matrix_unit h0, nuI_dnu h0, nuI_dnu h0]
  match_scalars <;> field_simp <;> ring

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP.Dc
end

section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

theorem rdV_rightCov {k r : ℕ} {z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} (hπ : IsCRepOn (UWset k r z') π') (hc : ContinuousOn π' (UWset k r z'))
    {D : Set (Q.Mx k r)} {F : Q.Mx k r → (Wq →L[ℂ] Wp)}
    (hF : ∀ h ∈ UWset k r z', ∀ g ∈ Q.Glev k r (Fin.last r) ∩ D, F (g * h) = (F g).comp (π' h))
    {g : Q.Mx k r} (hg : g ∈ Q.Glev k r (Fin.last r) ∩ D) {X : Q.Mx k r} (hX : P.QrD.InLieW k r z' X) :
    RdV X F g = (F g).comp (P.QrD.dOp π' X) := by
  have key : ∀ t : ℝ, F (g * NormedSpace.exp ((t : ℂ) • X)) = (F g).comp (π' (NormedSpace.exp ((t : ℂ) • X))) :=
    fun t => hF _ (Formalism.FourierDecayAlt.P.QrD.exp_uw hX t) g hg
  unfold Formalism.REAL.RdV
  simp only [key]
  let L : (Wq →L[ℂ] Wq) →L[ℝ] (Wq →L[ℂ] Wp) :=
    (ContinuousLinearMap.compL ℂ Wq Wq Wp (F g)).restrictScalars ℝ
  have hL : ∀ A, L A = (F g).comp A := fun A => rfl
  have hd : HasDerivAt (fun t : ℝ => L (π' (NormedSpace.exp ((t : ℂ) • X)))) (L (P.QrD.dOp π' X)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt 0 (Formalism.FourierDecayAlt.P.QrD.dOp_hasDeriv hπ hc hX)
  simp only [hL] at hd
  exact hd.deriv

theorem right_covariance_holds : RightCov := by
  intro k r z' Wp Wq _ _ _ _ _ _ π' hπ hc _ D F _ _ _ hF g hg A hA
  refine ⟨⟨hA.1.1, hA.2.1⟩, ?_⟩
  unfold Rc P.QrD.ecOp
  rw [rdV_rightCov hπ hc hF hg hA.1, rdV_rightCov hπ hc hF hg hA.2]
  ext v
  simp

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end

section

open Matrix
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem radial_coefficient_smoothness : RcSmooth := by
  intro k r E _ _ D f f' _ hf hf' Z hZ
  refine ⟨?_, ?_, ?_⟩
  · exact Qx2.smooth_add (Qx2.rd_smooth hf hZ.1) (Qx2.smooth_smul (Qx2.rd_smooth hf hZ.2) Complex.I)
  · intro a g hg
    have e : (fun x => a • f x + f' x) = fun x => f' x + a • f x := by
      funext x
      exact add_comm _ _
    show RdV _ (fun x => a • f x + f' x) g + Complex.I • RdV _ (fun x => a • f x + f' x) g =
      a • (RdV _ f g + Complex.I • RdV _ f g) + (RdV _ f' g + Complex.I • RdV _ f' g)
    rw [e, Qx2.rd_lin hf' hf a hg hZ.1, Qx2.rd_lin hf' hf a hg hZ.2, smul_add, smul_add, smul_comm Complex.I a]
    abel
  · intro E' _ _ L g hg
    show RdV _ (fun x => L (f x)) g + Complex.I • RdV _ (fun x => L (f x)) g = L (RdV _ f g + Complex.I • RdV _ f g)
    have e1 : RdV (hpart1 (Hpk k r) Z) (fun y => L (f y)) g = L (RdV _ f g) := Qx5.ntw_rd L hZ.1 f hf g hg
    have e2 : RdV (hpart2 (Hpk k r) Z) (fun y => L (f y)) g = L (RdV _ f g) := Qx5.ntw_rd L hZ.2 f hf g hg
    rw [e1, e2, map_add (f := _), map_smul]

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.PR.CP
end
