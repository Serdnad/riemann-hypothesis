module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle167
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsUnitaryMulTriangular
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle241
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle252
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle170
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle254
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle257
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
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
public import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle253
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem qs_lin (a b : ℕ → ℂ) (x y : ℂ) (ha : PolyB a) (hb : PolyB b) (τ : ℍ) :
    qs (x • a + y • b) τ = x * qs a τ + y * qs b τ := by
  have sa : Summable fun n : ℕ => a n * cexp (2 * π * Complex.I * n * τ) :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).1 τ).of_norm
  have sb : Summable fun n : ℕ => b n * cexp (2 * π * Complex.I * n * τ) :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb).1 τ).of_norm
  unfold qs
  rw [← tsum_mul_left, ← tsum_mul_left, ← (sa.mul_left x).tsum_add (sb.mul_left y)]
  congr 1; funext n; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem pet_linear : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ), 1 ≤ k → 0 < L' → N ∣ L' → Wt L ρ → (∀ (h a b : ℕ → ℂ) (x y : ℂ), CF k L' (ch ε) h → PolyB a → PolyB b → pet k ρ (qs h) (qs (x • a + y • b)) = x * pet k ρ (qs h) (qs a) + y * pet k ρ (qs h) (qs b)) ∧ ∀ (h h' a : ℕ → ℂ) (x y : ℂ), CF k L' (ch ε) h → CF k L' (ch ε) h' → PolyB a → pet k ρ (fun τ => x * qs h τ + y * qs h' τ) (qs a) = conj x * pet k ρ (qs h) (qs a) + conj y * pet k ρ (qs h') (qs a) := by
  intro k L L' N ε ρ hk hL' hN hW
  have intg : ∀ h a : ℕ → ℂ, CF k L' (ch ε) h → PolyB a →
      Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * qs a τ * (τ.im : ℂ) ^ k)) := by
    intro h a hh ha
    exact GlobalTheory.T.integrable_petersson_integrand_moderateGrowth k L L' N ε h ρ (qs a) hk hL' hN hW hh
      (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous a ha).2.aestronglyMeasurable (GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth a ha)
  refine ⟨?_, ?_⟩
  · intro h a b x y hh ha hb
    unfold pet
    have e : (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * qs (x • a + y • b) τ * (τ.im : ℂ) ^ k)) =
        fun τ => x * ((ρ τ : ℂ) * (conj (qs h τ) * qs a τ * (τ.im : ℂ) ^ k)) +
          y * ((ρ τ : ℂ) * (conj (qs h τ) * qs b τ * (τ.im : ℂ) ^ k)) := by
      funext τ; rw [qs_lin a b x y ha hb τ]; ring
    rw [e, integral_add ((intg h a hh ha).const_mul x) ((intg h b hh hb).const_mul y),
      integral_const_mul, integral_const_mul]
  · intro h h' a x y hh hh' ha
    unfold pet
    have e : (fun τ : ℍ => (ρ τ : ℂ) * (conj (x * qs h τ + y * qs h' τ) * qs a τ * (τ.im : ℂ) ^ k)) =
        fun τ => conj x * ((ρ τ : ℂ) * (conj (qs h τ) * qs a τ * (τ.im : ℂ) ^ k)) +
          conj y * ((ρ τ : ℂ) * (conj (qs h' τ) * qs a τ * (τ.im : ℂ) ^ k)) := by
      funext τ; simp only [map_add (f := _), map_mul]; ring
    rw [e, integral_add ((intg h a hh ha).const_mul _) ((intg h' a hh' ha).const_mul _),
      integral_const_mul, integral_const_mul]

end GlobalTheory.EisM
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.PetPos

theorem volume_isOpenPosMeasure : (volume : Measure ℍ).IsOpenPosMeasure := by
  have h0 : (volume.comap UpperHalfPlane.coe : Measure ℍ).IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap _ UpperHalfPlane.isOpenEmbedding_coe
  have hm : Continuous fun z : ℍ => (NNReal.mk z.im z.im_pos.le : NNReal) :=
    UpperHalfPlane.continuous_im.subtype_mk _
  have hc : Continuous fun z : ℍ => ((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) :=
    (continuous_const.div₀ hm (fun x => NNReal.ne_iff.mp x.im_ne_zero)).pow 2
  refine ⟨fun U hU hne => ?_⟩
  rw [UpperHalfPlane.volume_def, withDensity_apply _ hU.measurableSet]
  refine ne_of_gt ?_
  have hmeas : Measurable fun z : ℍ =>
      (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ENNReal) :=
    (ENNReal.continuous_coe.comp hc).measurable
  rw [setLIntegral_pos_iff hmeas]
  have hsupp : Function.support (fun z : ℍ =>
      (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ENNReal)) = Set.univ := by
    ext z
    simp [z.im_ne_zero]
  rw [hsupp, Set.univ_inter]
  exact hU.measure_pos _ hne

theorem norm_ch_eq_one {L N : ℕ} (ε : DirichletCharacter ℂ N) (hNL : N ∣ L) (γ : SL(2, ℤ))
    (hγ : (L : ℤ) ∣ γ 1 0) : ‖ch ε (γ 1 1)‖ = 1 := by
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hNL) hγ
  have h1 : ((γ 1 1 : ℤ) : ZMod N) * ((γ 0 0 : ℤ) : ZMod N) = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod N) hdet
    push_cast at h
    rw [hc, mul_zero, sub_zero] at h
    rw [mul_comm]
    exact h
  obtain ⟨u, hu⟩ := IsUnit.of_mul_eq_one _ h1
  show ‖ε ((γ 1 1 : ℤ) : ZMod N)‖ = 1
  rw [← hu]
  exact DirichletCharacter.unit_norm_eq_one ε u

theorem norm_sq_mul_im_pow_smul {k L N : ℕ} (ε : DirichletCharacter ℂ N) (hNL : N ∣ L) {f : ℍ → ℂ}
    (hf : Inv k L (ch ε) f) (γ : SL(2, ℤ)) (hγ : (L : ℤ) ∣ γ 1 0) (τ : ℍ) :
    ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k = ‖f τ‖ ^ 2 * τ.im ^ k := by
  have hD : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← ModularGroup.denom_apply]
    exact UpperHalfPlane.denom_ne_zero _ _
  have hpos : 0 < ‖((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)‖ := norm_pos_iff.mpr hD
  rw [hf γ hγ τ, ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply, norm_mul, norm_mul,
    norm_ch_eq_one ε hNL γ hγ, one_mul, norm_pow, div_pow, Complex.normSq_eq_norm_sq]
  field_simp
  ring

theorem pet_self_ne_zero : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L →
    Wt L ρ → CF k L (ch ε) h → h ≠ 0 → pet k ρ (qs h) (qs h) ≠ 0 := by
  intro k L N ε ρ h hk hL hN hW hCF hh
  haveI : (volume : Measure ℍ).IsOpenPosMeasure := volume_isOpenPosMeasure
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) :=
    inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  have hP : PolyB h := hCF.1.1
  have hInv : Inv k L (ch ε) (qs h) := hCF.1.2
  have hqc : Continuous (qs h) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hP).2
  set Φ : ℍ → ℝ := fun τ => ‖qs h τ‖ ^ 2 * τ.im ^ k with hΦ
  set G : ℍ → ℝ := fun τ => ρ τ * Φ τ with hG
  have hΦc : Continuous Φ := (hqc.norm.pow 2).mul (UpperHalfPlane.continuous_im.pow k)
  have hGnn : 0 ≤ G := fun τ => mul_nonneg (hW.nonneg τ) (by positivity)
  have heq : (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * qs h τ * (τ.im : ℂ) ^ k)) =
      fun τ => ((G τ : ℝ) : ℂ) := by
    funext τ
    rw [Complex.conj_mul']
    simp only [hG, hΦ]
    push_cast
    ring
  have hint := GlobalTheory.T.integrable_petersson_integrand_moderateGrowth k L L N ε h ρ (qs h) hk hL hN hW hCF hqc.aestronglyMeasurable
    (GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth h hP)
  rw [heq] at hint
  have hGi : Integrable G := by
    have := hint.re
    simpa using this
  intro hzero
  have hpet : pet k ρ (qs h) (qs h) = ((∫ τ, G τ : ℝ) : ℂ) := by
    unfold pet
    rw [heq, integral_complex_ofReal]
  rw [hpet, Complex.ofReal_eq_zero, integral_eq_zero_iff_of_nonneg hGnn hGi] at hzero
  have hmp : ∀ γ : SL(2, ℤ), MeasurePreserving (fun z : ℍ => γ • z) volume volume := by
    intro γ
    have hm := measurePreserving_smul ((γ : GL (Fin 2) ℝ)) (volume : Measure ℍ)
    convert hm using 1
    ext z
    simp
  have hall : ∀ᵐ τ ∂(volume : Measure ℍ), ∀ γ : Gamma0 L, G ((γ : SL(2, ℤ)) • τ) = 0 := by
    rw [ae_all_iff]
    intro γ
    have h1 := (hmp (γ : SL(2, ℤ))).quasiMeasurePreserving.ae_eq_comp hzero
    filter_upwards [h1] with τ hτ
    simpa using hτ
  have hΦ0 : Φ =ᵐ[volume] 0 := by
    filter_upwards [hall] with τ hτ
    have hterm : ∀ γ : Gamma0 L, Φ τ * ρ ((γ : SL(2, ℤ)) • τ) = 0 := by
      intro γ
      have hγL : (L : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp γ.2)
      have hinv := norm_sq_mul_im_pow_smul ε hN hInv (γ : SL(2, ℤ)) hγL τ
      have h2 := hτ γ
      simp only [hG, hΦ] at h2 ⊢
      rw [hinv] at h2
      rw [mul_comm]
      exact h2
    have hs := (hW.sum τ).mul_left (Φ τ)
    simp only [hterm, mul_one] at hs
    exact hs.unique hasSum_zero
  have hΦz : Φ = 0 := (Continuous.ae_eq_iff_eq volume hΦc continuous_const).mp hΦ0
  apply hh
  have hq0 : qs h = qs 0 := by
    funext τ
    have h3 := congrFun hΦz τ
    simp only [hΦ, Pi.zero_apply] at h3
    have him : τ.im ^ k ≠ 0 := pow_ne_zero _ τ.im_ne_zero
    have h4 : ‖qs h τ‖ ^ 2 = 0 := (mul_eq_zero.mp h3).resolve_right him
    have h5 : qs h τ = 0 := by simpa using h4
    rw [h5]
    simp [qs]
  exact GlobalTheory.T.qExpansionFunction_injective_of_polynomialGrowth h 0 hP ⟨0, 0, fun n => by simp⟩ hq0

end GlobalTheory.EisM.PetPos
end

section

noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix

namespace GlobalTheory.KZ.BettiB

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def BtN (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (n : ℕ) (b : X.Fn l)
    (c : Gam N l → MvPolynomial (Fin 2) (ZMod (l ^ n))) : Prop :=
  ∀ u : Fin 2 → ℤ_[l], ∃ χ : SL(2, ℤ) → ZMod (l ^ n), H3.Kum X l n (b u) χ ∧ ∃ M : ℕ, 0 < M ∧
    ∀ δ : Gam N l, (δ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M →
      MvPolynomial.eval (fun i => PadicInt.toZModPow n (u i)) (c δ) = χ δ

def BtZ (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (b : X.Fn l) (c : Gam N l → MvPolynomial (Fin 2) ℤ_[l]) : Prop :=
  ∀ n : ℕ, BtN X N l n b (fun δ => MvPolynomial.map (PadicInt.toZModPow n) (c δ))

def Z1 (N l w : ℕ) [Fact l.Prime] : Submodule ℤ_[l] (Gam N l → MvPolynomial (Fin 2) ℤ_[l]) where
  carrier := {c | (∀ γ, (c γ).IsHomogeneous w) ∧
    ∀ γ δ : Gam N l, c (γ * δ) = slP ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (c γ) + c δ}
  add_mem' := by
    rintro c c' ⟨h1, h2⟩ ⟨h1', h2'⟩
    refine ⟨fun γ => (h1 γ).add (h1' γ), fun γ δ => ?_⟩
    simp only [Pi.add_apply, h2, h2', map_add (f := _)]; abel
  zero_mem' := ⟨fun γ => MvPolynomial.isHomogeneous_zero _ _ _, fun γ δ => by simp⟩
  smul_mem' := by
    rintro r c ⟨h1, h2⟩
    refine ⟨fun γ => ?_, fun γ δ => ?_⟩
    · simpa [MvPolynomial.smul_eq_C_mul] using (MvPolynomial.isHomogeneous_C _ r).mul (h1 γ)
    · simp only [Pi.smul_apply, h2, map_smul, smul_add]

theorem hs_codiscrete_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  apply _root_.GlobalTheory.KZ.codiscreteWithin_Hs_neBot <;> assumption

theorem btZ_zero (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] : BtZ X N l 0 0 := by
  intro n u
  refine ⟨0, ⟨1, fun _ => 1, fun _ => 1, 1, one_pos, ?_, ?_, ?_⟩, 1, one_pos, fun δ _ => by simp⟩
  · simp [Tower.cls]
  · apply H3.isRoot_one
    haveI := hs_codiscrete_neBot
    exact one_ne_zero
  · intro δ _ z _; simp

end GlobalTheory.KZ.BettiB
end
end

section

open GlobalTheory.DualWeyl MvPolynomial NumberField
open Formalism.GradedWeylDivisibility (rowAct rowW rowNu)
open Formalism.REAL (fockF)
open scoped Matrix ComplexConjugate InnerProductSpace

noncomputable section

namespace GlobalTheory.DualWeylFock

variable {N : ℕ} {la : Fin N → ℕ}

theorem fock_smul_left {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) : fockF (c • f) g = c * fockF f g := by
  rw [Formalism.REAL.fischerInner_eq_sum_of_subset _ _ f.support support_smul, fockF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_smul, smul_eq_mul]
  ring

def fockLeft {σ : Type} (g : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun f := fockF f g
  map_add' f f' := Formalism.REAL.fischerInner_add_left f f' g
  map_smul' c f := fock_smul_left c f g

theorem extremal_rowWeight (hla : Antitone la) : IsWeightedHomogeneous (rowW N N) (extremal la ℂ) la := by
  have hnu : rowNu (r := N) la = la := by
    funext b
    simp [rowNu]
  have := Formalism.GradedWeylDivisibility.hwRowWeight ℂ N N le_rfl la hla
  rwa [hnu] at this

theorem evalAt_one_of_ne {μ : Fin N → ℕ} (hμ : μ ≠ la) {q : Pol N ℂ} (hq : q ∈ nabla la ℂ)
    (hw : IsWeightedHomogeneous (rowW N N) q μ) : evalAt 1 q = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hμ
  let t : Fin N → ℂ := fun b => if b = a then 2 else 1
  have hprod : ∀ e : Fin N → ℕ, ∏ b, t b ^ e b = 2 ^ e a := by
    intro e
    rw [Finset.prod_eq_single a]
    · simp [t]
    · intro b _ hb; simp [t, hb]
    · simp
  have h1 := evalAt_rowAct 1 (Matrix.diagonal t) q
  have h2 := evalAt_colAct 1 (Matrix.diagonal t) q
  rw [Formalism.GradedWeylDivisibility.rowActDiagWeight ℂ N N t μ _ hw, hprod, Matrix.mul_one, map_smul, smul_eq_mul] at h1
  rw [colAct_of_mem hq _ (Matrix.blockTriangular_diagonal t), Matrix.one_mul, map_smul, smul_eq_mul] at h2
  simp only [diagChar, Matrix.diagonal_apply_eq] at h2
  rw [hprod] at h2
  have hne : (2 : ℂ) ^ μ a - 2 ^ la a ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have h' : (2 : ℕ) ^ μ a = 2 ^ la a := by exact_mod_cast h
    exact ha (Nat.pow_right_injective le_rfl h')
  have : ((2 : ℂ) ^ μ a - 2 ^ la a) * evalAt 1 q = 0 := by rw [sub_mul, h1, h2, sub_self]
  exact (mul_eq_zero.mp this).resolve_left hne

theorem fock_extremal (hla : Antitone la) {f : Pol N ℂ} (hf : f ∈ nabla la ℂ) :
    fockF f (extremal la ℂ) = evalAt 1 f * fockF (extremal la ℂ) (extremal la ℂ) := by
  have hfin := weightedHomogeneousComponent_finsupp (w := rowW N N) f
  have hsum := sum_weightedHomogeneousComponent (rowW N N) f
  rw [finsum_eq_sum _ hfin] at hsum

  rw [← hsum, Formalism.REAL.fischerInner_sum_left, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hmem := Formalism.GradedWeylDivisibility.dualWeylRowGraded ℂ N N la μ f hf
  have hw' := weightedHomogeneousComponent_isWeightedHomogeneous (w := rowW N N) μ f
  by_cases hμ : μ = la
  · subst hμ
    conv_lhs => rw [GlobalTheory.T.dualWeyl_eq_evalAt_one_smul_extremal_of_rowWeight ℂ N μ hla _ hmem hw']
    rw [fock_smul_left]
  · rw [evalAt_one_of_ne hμ hmem hw', zero_mul]
    exact Formalism.GradedWeylDivisibility.fockWeightOrth _ _ _ μ la _ _ hμ hw' (extremal_rowWeight hla)

theorem exists_form_eq (ψ : Pol N ℂ →ₗ[ℂ] ℂ) : ∃ h ∈ nabla la ℂ, ∀ f ∈ nabla la ℂ, form la f h = ψ f := by
  have : CompleteSpace (Space la) := FiniteDimensional.complete ℂ _
  let φ : Space la →ₗ[ℂ] ℂ := ψ ∘ₗ (nabla la ℂ).subtype ∘ₗ (toSpace la).symm.toLinearMap
  let v : Space la := (InnerProductSpace.toDual ℂ (Space la)).symm (LinearMap.toContinuousLinearMap φ)
  refine ⟨((toSpace la).symm v).1, ((toSpace la).symm v).2, fun f hf => ?_⟩
  have h1 : ⟪v, toSpace la ⟨f, hf⟩⟫_ℂ = φ (toSpace la ⟨f, hf⟩) := InnerProductSpace.toDual_symm_apply
  exact h1

theorem form_eq_fock_div (N : ℕ) (la : Fin N → ℕ) (hla : Antitone la) :
    ∀ f ∈ nabla la ℂ, ∀ f' ∈ nabla la ℂ,
      form la f f' = fockF f f' / fockF (extremal la ℂ) (extremal la ℂ) := by
  intro f hf f' hf'
  obtain ⟨hre, him⟩ := Formalism.GradedWeylDivisibility.fockPos _ (extremal la ℂ) extremal_ne_zero
  set c := fockF (extremal la ℂ) (extremal la ℂ) with hc
  have hc0 : c ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have hcc : conj c = c := Complex.conj_eq_iff_im.mpr him
  obtain ⟨h, hh, H⟩ := exists_form_eq (la := la) (c⁻¹ • fockLeft f')
  have H' : ∀ g ∈ nabla la ℂ, form la g h = fockF g f' / c := fun g hg => by
    rw [H g hg, div_eq_inv_mul]; rfl
  have hE := extremal_mem (R := ℂ) hla
  have key : h = f' := by
    rw [← sub_eq_zero]
    refine eq_zero_of_evalAt_unitary (Submodule.sub_mem _ hh hf') fun u => ?_
    have hst : ∀ (g : Matrix (Fin N) (Fin N) ℂ), ∀ p ∈ nabla la ℂ, rowAct ℂ g p ∈ nabla la ℂ :=
      fun g p hp => Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N la g p hp
    have h1 := H' _ (hst (u.1)ᴴ _ hE)
    have h2 : rowAct ℂ u.1 (rowAct ℂ (u.1)ᴴ (extremal la ℂ)) = extremal la ℂ := by
      have h3 : (u.1)ᴴ * u.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp u.2
      rw [← AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowActMul ℂ N N, h3, Formalism.GradedWeylDivisibility.ldlat_rowAct_one]
      rfl
    rw [← form_rowAct u, h2, Formalism.GradedWeylDivisibility.fockRowAdj, Matrix.conjTranspose_conjTranspose, ← conj_form,
      (GlobalTheory.T.dualWeyl_extremal_reproducing_normSq_one N la hla).1 _ (hst _ _ hh), Formalism.GradedWeylDivisibility.fockHerm, fock_extremal hla (hst _ _ hf'),
      evalAt_rowAct, evalAt_rowAct, Matrix.mul_one, ← hc, ← starRingEnd_apply, map_mul, hcc,
      mul_div_cancel_right₀ _ hc0] at h1
    rw [map_sub, sub_eq_zero]
    exact (starRingEnd ℂ).injective h1
  rw [← H' f hf, key]

end GlobalTheory.DualWeylFock
end
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.algebraicTaylor_torsionTranslate_evenTheta : ∀ Λ : AddSubgroup ℂ, IsLat Λ → (∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (sgStar Λ))) → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ x, InRationalLattice Λ x → AlgEnt (U1 Λ x (GL3Theta.th0 Λ t₀)) ∧ ∀ ω ∈ Λ, ∃ κ ∈ Qbar, κ ≠ 0 ∧ ∀ z, U1 Λ (x + ω) (GL3Theta.th0 Λ t₀) z = κ * U1 Λ x (GL3Theta.th0 Λ t₀) z := by
  first | exact @GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt | exact GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt | (intros; apply GlobalTheory.EvenThetaTorsion.algebraicTaylor_torsionTranslate_evenTheta_alt <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.thetaTranslateProduct_sigmaStarPow_lattice_law : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, 2 * t₀ ∈ Λ → ∀ (y : ℂ) (N : ℕ), (N : ℂ) * y ∈ Λ → ∀ ω ∈ Λ, ∀ z : ℂ, (U1 Λ y (GL3Theta.th0 Λ t₀) ((N : ℂ) * (z + ω)) * GL3Theta.th0 Λ t₀ ((N : ℂ) * (z + ω))) * sgStar Λ z ^ (2 * N ^ 2) = (U1 Λ y (GL3Theta.th0 Λ t₀) ((N : ℂ) * z) * GL3Theta.th0 Λ t₀ ((N : ℂ) * z)) * sgStar Λ (z + ω) ^ (2 * N ^ 2) := by
  first | exact @GlobalTheory.ThetaLaw.pull_law | exact GlobalTheory.ThetaLaw.pull_law | (intros; apply GlobalTheory.ThetaLaw.pull_law <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.U1_add_mul_U1_sub_at_zero_eq_wpF_sub : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P Q : ℂ, P ∉ Λ → Q ∉ Λ → U1 Λ (P + Q) (sgStar Λ) 0 * U1 Λ (P - Q) (sgStar Λ) 0 = (wpF Λ Q - wpF Λ P) * U1 Λ P (sgStar Λ) 0 ^ 2 * U1 Λ Q (sgStar Λ) 0 ^ 2 := by
  first | exact @GlobalTheory.translate_modifiedSigma_add_mul_sub_at_zero | exact GlobalTheory.translate_modifiedSigma_add_mul_sub_at_zero | (intros; apply GlobalTheory.translate_modifiedSigma_add_mul_sub_at_zero <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.padicComplex_integral_of_sq_integral_odd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ H : PowerSeries ℂ_[p], PowerSeries.constantCoeff H = 1 → IntSer (H ^ 2) → IntSer H := by
  first | exact @GlobalTheory.EvenTheta.intSer_of_sq_main | exact GlobalTheory.EvenTheta.intSer_of_sq_main | (intros; apply GlobalTheory.EvenTheta.intSer_of_sq_main <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.powerSeries_supNorm_mul_padicComplex : ∀ (p : ℕ) [Fact p.Prime] (f g : PowerSeries ℂ_[p]) (c : ℝ), BddSer f → BddSer g → (∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ c) → ∀ i j, ‖PowerSeries.coeff i f‖ * ‖PowerSeries.coeff j g‖ ≤ c := by
  first | exact @GlobalTheory.EvenTheta.sup_norm_mul_padicComplex | exact GlobalTheory.EvenTheta.sup_norm_mul_padicComplex | (intros; apply GlobalTheory.EvenTheta.sup_norm_mul_padicComplex <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

theorem _root_.GlobalTheory.T.torsion_parallelogramLaw_periodic_vanish : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ (N : ℕ), 0 < N → ∀ M : ℂ → ℝ,
    (∀ t ∈ Λ, M t = 0) → (∀ t ω : ℂ, (N : ℂ) * t ∈ Λ → ω ∈ Λ → M (t + ω) = M t) →
    (∀ P Q : ℂ, (N : ℂ) * P ∈ Λ → (N : ℂ) * Q ∈ Λ → Q ∉ Λ → M (P + Q) + M (P - Q) = 2 * M P + 2 * M Q) →
    ∀ t : ℂ, (N : ℂ) * t ∈ Λ → M t = 0 := by
  first | exact @GlobalTheory.torsion_parallelogram_vanish | exact GlobalTheory.torsion_parallelogram_vanish | (intros; apply GlobalTheory.torsion_parallelogram_vanish <;> assumption)
end

section

open scoped BigOperators

theorem _root_.GlobalTheory.T.powerSeriesCoeffNormLeOne_root_coprime_padic : ∀ (p : ℕ) [Fact p.Prime] (N : ℕ), 0 < N → Nat.Coprime N p →
    ∀ s : PowerSeries ℂ_[p], PowerSeries.constantCoeff s = 1 →
      GlobalTheory.EvenTheta.IntSer (s ^ N) → GlobalTheory.EvenTheta.IntSer s := by
  first | exact @GlobalTheory.RootInt.intSer_root | exact GlobalTheory.RootInt.intSer_root | (intros; apply GlobalTheory.RootInt.intSer_root <;> assumption)
end

section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.th0_zero_even_sq_zeros_and_periodicity : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → Differentiable ℂ (GL3Theta.th0 Λ t₀) ∧ GL3Theta.th0 Λ t₀ 0 = 1 ∧ (∀ z, GL3Theta.th0 Λ t₀ (-z) = GL3Theta.th0 Λ t₀ z) ∧ (∀ z, GL3Theta.th0 Λ t₀ z ^ 2 = sqTh Λ t₀ z) ∧ (∀ z, GL3Theta.th0 Λ t₀ z = 0 ↔ z + t₀ ∈ Λ) ∧ ∀ ω ∈ Λ, ω / 2 + t₀ ∉ Λ → ∀ z, U1 Λ ω (GL3Theta.th0 Λ t₀) z = GL3Theta.th0 Λ t₀ z := by
  first | exact @GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties | exact GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties | (intros; apply GlobalTheory.EvenTheta.evenThetaTwoTorsion_basic_properties <;> assumption)
end
