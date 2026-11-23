module

public import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.BesselIntg
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle060
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle052
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle034
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.SigmaFiniteAmplitudes.SigmaFiniteOfUnfold
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

attribute [local instance] Formalism.FourierDecayAlt.P.B7.properFD

theorem norm_psi_one (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : ‖psi k r z c g‖ = 1 :=
  Formalism.FourierDecayAlt.P.S3dx6.norm_psi z c g

theorem norm_Psi_le (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) {p : PairSp k r} (hp : InPair L p) (x : Mt k r) :
    ‖Psi L w0 v v' ξ ξ' γ p x‖ ≤ ‖ξ‖ * ‖ξ'‖ *
      (‖⟪v, L.σ ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of x) w0⟫_ℂ‖ *
        ‖⟪v', L.σ ((Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ * Matrix.of x) w0⟫_ℂ‖) := by
  rw [Psi_eq, norm_smul, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, norm_mul, norm_mul,
    norm_mul, norm_star, norm_star, norm_psi_one, norm_psi_one,
    Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary L.hz'.2 L.hπ' _ hp.2.2.1, Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_unitary L.hz.2 L.hπ _ hp.1]
  nlinarith [norm_nonneg ξ, norm_nonneg ξ',
    norm_nonneg ⟪v, L.σ ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of x) w0⟫_ℂ,
    norm_nonneg ⟪v', L.σ ((Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ * Matrix.of x) w0⟫_ℂ]

theorem prod_coef_le {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    (hNI : Formalism.FourierDecayAlt.ThreeDimData.NormInv) {a b C1 C2 : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (v v' w0 : H)
    (hC1 : ∀ g ∈ UH (Hpk k r), ‖⟪v, σ g w0⟫_ℂ‖ ≤ C1 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (hC2 : ∀ g ∈ UH (Hpk k r), ‖⟪v', σ g w0⟫_ℂ‖ ≤ C2 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    {M y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hM : M ∈ UH (Hpk k r)) (hy : y ∈ UH (Hpk k r)) :
    ‖⟪v, σ (M * y) w0⟫_ℂ‖ * ‖⟪v', σ y w0⟫_ℂ‖ ≤
      (|C1| * |C2|) * (Formalism.FourierDecayAlt.B.gN y ^ (b - a) * Formalism.FourierDecayAlt.B.gN M ^ (-b)) := by
  have hMy : M * y ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hM hy
  have hMi : M⁻¹ ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hM
  have h1 := hC1 _ hMy
  have h2 := hC2 _ hy
  have hn1 : 0 ≤ Formalism.FourierDecayAlt.B.gN (M * y) ^ (-a) := Real.rpow_nonneg (Formalism.FourierDecayAlt.P.S3dx6.gN_nonneg _) _
  have hn2 : 0 ≤ Formalism.FourierDecayAlt.B.gN y ^ (-a) := Real.rpow_nonneg (Formalism.FourierDecayAlt.P.S3dx6.gN_nonneg _) _
  have hinv : Formalism.FourierDecayAlt.B.gN (M * y) = Formalism.FourierDecayAlt.B.gN (y⁻¹ * M⁻¹) := by
    rw [← Matrix.mul_inv_rev, ((hNI k r).2 _ hMy).1]
  have hconv := Formalism.FourierDecayAlt.P.S3dx6.conv_pt hNI hb hab hy hMi
  rw [((hNI k r).2 _ hM).1] at hconv
  calc ‖⟪v, σ (M * y) w0⟫_ℂ‖ * ‖⟪v', σ y w0⟫_ℂ‖
      ≤ (|C1| * Formalism.FourierDecayAlt.B.gN (M * y) ^ (-a)) * (|C2| * Formalism.FourierDecayAlt.B.gN y ^ (-a)) :=
        mul_le_mul (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hn1))
          (h2.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hn2)) (norm_nonneg _)
          (mul_nonneg (abs_nonneg _) hn1)
    _ = (|C1| * |C2|) * (Formalism.FourierDecayAlt.B.gN y ^ (-a) * Formalism.FourierDecayAlt.B.gN (y⁻¹ * M⁻¹) ^ (-a)) := by
        rw [hinv]; ring
    _ ≤ (|C1| * |C2|) * (Formalism.FourierDecayAlt.B.gN y ^ (b - a) * Formalism.FourierDecayAlt.B.gN M ^ (-b)) :=
        mul_le_mul_of_nonneg_left hconv (mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem meas_gN_rpow (e : ℝ) : Measurable fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ e :=
  (Formalism.FourierDecayAlt.P.S3dx6.gN_mt_cont (k := k) (r := r)).measurable.pow_const e

theorem lint_G_bound (L : LocBessel k r) {μG : Measure (Mt k r)}
    (hμG : PI.BesselPeriodGGP.IsHaarOn (UH (Hpk k r)) μG) (hNI : Formalism.FourierDecayAlt.ThreeDimData.NormInv)
    {a b C1 C2 : ℝ} (hb : 0 ≤ b) (hab : b ≤ a)
    (hI : Integrable (fun x : Mt k r => Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - a)) μG)
    (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    (hC1 : ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤ C1 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    (hC2 : ∀ g ∈ UH (Hpk k r), ‖⟪v', L.σ g w0⟫_ℂ‖ ≤ C2 * Formalism.FourierDecayAlt.B.gN g ^ (-a))
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r))
    {p : PairSp k r} (hp : InPair L p) :
    ∫⁻ x, ‖Psi L w0 v v' ξ ξ' γ p x‖ₑ ∂μG ≤
      ENNReal.ofReal (‖ξ‖ * ‖ξ'‖ * (|C1| * |C2|) * (∫ x, Formalism.FourierDecayAlt.B.gN (Matrix.of x) ^ (b - a) ∂μG) *
        Formalism.MainNotions.S.Pv.AmpDD.pairMaj γ b p) := by
  have hp0 := hp
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  have hhU := uh_of_uw hh
  have hnU := uh_of_n hn
  have hh'U := uh_of_uw hh'
  have hn'U := uh_of_n hn'
  have hhi := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hhU
  have hni := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hnU
  have hh'i := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hh'U
  have hn'i := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hn'U
  set A := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ with hA
  set B := (Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ with hB
  set M := (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of p.2.2 * Matrix.of p.2.1 with hM
  have hAU : A ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hhi hni) hγ
  have hBU : B ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hh'i hn'i
  have hMU : M ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hAU hn'U) hh'U
  have hMB : M * B = A := by
    rw [hM, hB, hA]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Matrix.of p.2.1) (Matrix.of p.2.1)⁻¹, (Formalism.FourierDecayAlt.P.S3dx6.unit_of_uh hh'U).1,
      Matrix.one_mul, (Formalism.FourierDecayAlt.P.S3dx6.unit_of_uh hn'U).1, Matrix.mul_one]
  have hlm : Measurable (lmulM (k := k) (r := r) B) :=
    Formalism.FourierDecayAlt.P.B7.meas_mulM (f := fun _ => ((B : Matrix _ _ ℂ) : Mt k r)) measurable_const measurable_id
  have hmp : MeasurePreserving (lmulM (k := k) (r := r) B) μG μG := ⟨hlm, hμG.2.2.2 B hBU⟩
  set K1 : ℝ := ‖ξ‖ * ‖ξ'‖ * (|C1| * |C2|) * Formalism.FourierDecayAlt.B.gN M ^ (-b) with hK1
  have hpt : ∀ᵐ x ∂μG, ‖Psi L w0 v v' ξ ξ' γ p x‖ₑ ≤
      ENNReal.ofReal (K1 * Formalism.FourierDecayAlt.B.gN (Matrix.of (lmulM B x)) ^ (b - a)) := by
    filter_upwards [ae_mem_sk hμG] with x hx
    have hBx : B * Matrix.of x ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hBU hx
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    have e1 : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of x = M * (B * Matrix.of x) := by
      rw [← Matrix.mul_assoc, hMB]
    calc ‖Psi L w0 v v' ξ ξ' γ p x‖
        ≤ ‖ξ‖ * ‖ξ'‖ * (‖⟪v, L.σ ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * γ * Matrix.of x) w0⟫_ℂ‖ *
          ‖⟪v', L.σ ((Matrix.of p.2.1)⁻¹ * (Matrix.of p.2.2)⁻¹ * Matrix.of x) w0⟫_ℂ‖) := norm_Psi_le L w0 v v' ξ ξ' γ hp0 x
      _ = ‖ξ‖ * ‖ξ'‖ * (‖⟪v, L.σ (M * (B * Matrix.of x)) w0⟫_ℂ‖ * ‖⟪v', L.σ (B * Matrix.of x) w0⟫_ℂ‖) := by
          rw [e1]
      _ ≤ ‖ξ‖ * ‖ξ'‖ * ((|C1| * |C2|) * (Formalism.FourierDecayAlt.B.gN (B * Matrix.of x) ^ (b - a) * Formalism.FourierDecayAlt.B.gN M ^ (-b))) :=
          mul_le_mul_of_nonneg_left (prod_coef_le hNI hb hab v v' w0 hC1 hC2 hMU hBx)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = K1 * Formalism.FourierDecayAlt.B.gN (Matrix.of (lmulM B x)) ^ (b - a) := by
          rw [hK1]; show _ = _ * Formalism.FourierDecayAlt.B.gN (B * Matrix.of x) ^ (b - a); ring
  have hK1n : 0 ≤ K1 := by
    rw [hK1]
    have := Real.rpow_nonneg (Formalism.FourierDecayAlt.P.S3dx6.gN_nonneg M) (-b)
    positivity
  have hf : Measurable fun y : Mt k r => ENNReal.ofReal (K1 * Formalism.FourierDecayAlt.B.gN (Matrix.of y) ^ (b - a)) :=
    ENNReal.measurable_ofReal.comp ((meas_gN_rpow (b - a)).const_mul K1)
  calc ∫⁻ x, ‖Psi L w0 v v' ξ ξ' γ p x‖ₑ ∂μG
      ≤ ∫⁻ x, ENNReal.ofReal (K1 * Formalism.FourierDecayAlt.B.gN (Matrix.of (lmulM B x)) ^ (b - a)) ∂μG := lintegral_mono_ae hpt
    _ = ∫⁻ y, ENNReal.ofReal (K1 * Formalism.FourierDecayAlt.B.gN (Matrix.of y) ^ (b - a)) ∂μG := by
        rw [← lintegral_map hf hlm, hmp.map_eq]
    _ = ENNReal.ofReal (∫ y, K1 * Formalism.FourierDecayAlt.B.gN (Matrix.of y) ^ (b - a) ∂μG) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hI.const_mul K1)]
        exact Filter.Eventually.of_forall fun y =>
          mul_nonneg hK1n (Real.rpow_nonneg (Formalism.FourierDecayAlt.P.S3dx6.gN_nonneg _) _)
    _ = _ := by
        rw [integral_const_mul, hK1]
        unfold Formalism.MainNotions.S.Pv.AmpDD.pairMaj
        rw [← hM]
        ring_nf

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end

section

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace Formalism.MainNotions.S.Pv.AmpDDPf

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

theorem inPair_stab (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {p : PairSp k r} (hp : InPair L p) {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ RStab k r γ) : InPair L (stabAct γ a p) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  exact ⟨h1, WeylGroupFacts.mem_n_mul ha.1 h2, h3, WeylGroupFacts.mem_n_mul ha.2 h4⟩

theorem inPair_of_stab (L : LocBessel k r) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {p : PairSp k r} {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ RStab k r γ) (hp : InPair L (stabAct γ a p)) : InPair L p := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have key : ∀ b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, b ∈ Nset k r →
      ∀ m : Mt k r, b * of m ∈ Nset k r → of m ∈ Nset k r := by
    intro b hb m hm
    have hu : IsUnit b.det := WeylGroupFacts.isUnit_of_uh hb.1
    have : of m = b⁻¹ * (b * of m) := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    rw [this]
    exact WeylGroupFacts.mem_n_mul (WeylGroupFacts.mem_n_inv hb) hm
  exact ⟨h1, key a ha.1 _ h2, h3, key _ ha.2 _ h4⟩

private theorem psi_mul_of_mem_Nset (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (c : ℂ)
    {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ Nset k r) (hh : h ∈ Nset k r) :
    psi k r z c (g * h) = psi k r z c g * psi k r z c h := by
  unfold psi
  rw [WeylGroupFacts.ell_mul z hz ((WeylGroupFacts.nset_iff _).1 hg).2 ((WeylGroupFacts.nset_iff _).1 hh).2, mul_add,
    Complex.add_re, Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem psi_mul_star_psi_eq_one (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    psi k r z c g * star (psi k r z c g) = 1 := by
  have h : ‖psi k r z c g‖ = 1 := by
    unfold psi
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [show star (psi k r z c g) = (starRingEnd ℂ) (psi k r z c g) from rfl, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, h]
  simp

theorem Psi_stab (L : LocBessel k r) (w0 v v' : L.Hs) (ξ : L.Wp) (ξ' : L.Wq)
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) (hrel : IsRelStab L γ)
    {p : PairSp k r} (hp : InPair L p) {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ RStab k r γ) (x : Mt k r) :
    Psi L w0 v v' ξ ξ' γ (stabAct γ a p) x =
      Psi L w0 v v' ξ ξ' γ p (Matrix.of.symm (γ⁻¹ * a⁻¹ * γ * Matrix.of x)) := by
  obtain ⟨h1, h2, h3, h4⟩ := hp
  have hγu : IsUnit γ.det := WeylGroupFacts.isUnit_of_uh hγ
  have e : ∀ M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, (of fun i j => M i j) = M :=
    fun M => rfl
  rw [Psi_eq, Psi_eq]
  simp only [stabAct, e, Equiv.apply_symm_apply]
  have m1 : (of p.1.1)⁻¹ * (a * of p.1.2)⁻¹ * γ * of x =
      (of p.1.1)⁻¹ * (of p.1.2)⁻¹ * γ * (γ⁻¹ * a⁻¹ * γ * of x) := by
    rw [Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc γ γ⁻¹, Matrix.mul_nonsing_inv _ hγu, Matrix.one_mul]
  have m2 : (of p.2.1)⁻¹ * (γ⁻¹ * a * γ * of p.2.2)⁻¹ * of x =
      (of p.2.1)⁻¹ * (of p.2.2)⁻¹ * (γ⁻¹ * a⁻¹ * γ * of x) := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_inv_rev,
      Matrix.nonsing_inv_nonsing_inv _ hγu]
    simp only [Matrix.mul_assoc]
  have hc : psi k r L.z L.c (a * of p.1.2) * star (psi k r L.z' L.c (γ⁻¹ * a * γ * of p.2.2)) =
      psi k r L.z L.c (of p.1.2) * star (psi k r L.z' L.c (of p.2.2)) := by
    rw [psi_mul_of_mem_Nset L.z L.hz.1 L.c ha.1 h2, psi_mul_of_mem_Nset L.z' L.hz'.1 L.c ha.2 h4, star_mul',
      hrel a ha]
    calc psi k r L.z' L.c (γ⁻¹ * a * γ) * psi k r L.z L.c (of p.1.2) *
          (star (psi k r L.z' L.c (γ⁻¹ * a * γ)) * star (psi k r L.z' L.c (of p.2.2)))
        = (psi k r L.z' L.c (γ⁻¹ * a * γ) * star (psi k r L.z' L.c (γ⁻¹ * a * γ))) *
          (psi k r L.z L.c (of p.1.2) * star (psi k r L.z' L.c (of p.2.2))) := by ring
      _ = _ := by rw [psi_mul_star_psi_eq_one, one_mul]
  rw [m1, m2, hc]

end Formalism.MainNotions.S.Pv.AmpDDPf
end
end
