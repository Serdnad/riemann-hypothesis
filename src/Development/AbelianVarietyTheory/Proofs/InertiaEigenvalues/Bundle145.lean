module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle123
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSelfDualOfDualSubgroups
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle061
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Sl2PresentationRelations
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle125
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormPowLeNormFactorial
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PowerSeriesVecReduceModUMulVec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle126
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle127
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle057
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle128
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
public import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle100

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.WeilSmooth

def lS {k : Type} [CommRing k] (u : k) : SpecialLinearGroup (Fin 2) k :=
  ⟨!![1, 0; u, 1], by simp [Matrix.det_fin_two]⟩

theorem sl_ext {k : Type} [CommRing k] {A B : SpecialLinearGroup (Fin 2) k}
    (h : (A : Matrix (Fin 2) (Fin 2) k) = B) : A = B := Subtype.ext h

theorem lS_eq {k : Type} [CommRing k] (u : k) : lS u = (wS k)⁻¹ * nS (-u) * wS k := by
  apply sl_ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lS, nS, wS, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem mid_eq {k : Type} [CommRing k] (a a' t t' : k) (ha : a * a' = 1) (ht : t * t' = 1) :
    ((nS ((a - 1) * t') * lS t * nS ((a' - 1) * t') * lS (-(t * a)) : SpecialLinearGroup (Fin 2) k) :
      Matrix (Fin 2) (Fin 2) k) = !![a, 0; 0, a'] := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lS, nS, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (a-1)*ht - t*a*((a-1)*(a'-1)*t'*ht + t'*ha)
  · linear_combination (a-1)*(a'-1)*t' * ht + t' * ha
  · linear_combination (-t*a*(a'-1))*ht - t*ha
  · linear_combination (a'-1)*ht

theorem decomp {k : Type} [CommRing k] (g : SpecialLinearGroup (Fin 2) k) (a' t t' : k)
    (ha : (g : Matrix (Fin 2) (Fin 2) k) 0 0 * a' = 1) (ht : t * t' = 1) :
    g = lS ((g : Matrix (Fin 2) (Fin 2) k) 1 0 * a') * (nS (((g : Matrix (Fin 2) (Fin 2) k) 0 0 - 1) * t') * lS t *
      nS ((a' - 1) * t') * lS (-(t * (g : Matrix (Fin 2) (Fin 2) k) 0 0))) *
      nS ((g : Matrix (Fin 2) (Fin 2) k) 0 1 * a') := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) k) 0 0 * (g : Matrix (Fin 2) (Fin 2) k) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) k) 0 1 * (g : Matrix (Fin 2) (Fin 2) k) 1 0 = 1 := by
    have := g.2; rw [Matrix.det_fin_two] at this; exact this
  apply sl_ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, mid_eq _ _ _ _ ha ht]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lS, nS, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination -((g : Matrix (Fin 2) (Fin 2) k) 0 1) * ha
  · linear_combination -((g : Matrix (Fin 2) (Fin 2) k) 1 0) * ha
  · linear_combination -((g : Matrix (Fin 2) (Fin 2) k) 1 0 * (g : Matrix (Fin 2) (Fin 2) k) 0 1 * a' +
      (g : Matrix (Fin 2) (Fin 2) k) 1 1) * ha + a' * hdet

end GlobalTheory.WeilSmooth

noncomputable section
namespace GlobalTheory.WeilSmooth
open GlobalTheory.JR

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem nl_cont [Unram F E] (A : Et F E) : Continuous A.NL ∧ A.NL 0 = 0 := GlobalTheory.T.continuous_etaleHermitianPair_norm_and_map_zero F E A
theorem inv_cont (A : Et F E) : (∀ᶠ a in 𝓝 (1 : A.K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : A.K) :=
  GlobalTheory.T.etaleHermitianPair_eventually_isUnit_continuousAt_inverse F E A

theorem fix_n [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (x : A.K) (ω : A.K → ℂ)
    (μ : Measure A.L) (γ : ℂ) (W : SpecialLinearGroup (Fin 2) A.K → (A.L → ℂ) → A.L → ℂ)
    (hW : A.IsWeil ψ x ω μ γ W) (f : A.L → ℂ) (hf : IsTest f) :
    ∀ᶠ z in 𝓝 (0 : A.K), W (nS z) f = f := by
  have htr : Continuous (Algebra.trace F A.K) := IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun p : A.K × A.L => ‖Algebra.trace F A.K (p.1 * x * A.NL p.2)‖ :=
    (htr.comp ((continuous_fst.mul continuous_const).mul ((nl_cont A).1.comp continuous_snd))).norm
  have hK : IsCompact (tsupport f) := hf.2
  have hev : ∀ᶠ z in 𝓝 (0 : A.K), ∀ y ∈ tsupport f, ‖Algebra.trace F A.K (z * x * A.NL y)‖ < 1 := by
    refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
    have h0 : ‖Algebra.trace F A.K ((0 : A.K) * x * A.NL y)‖ < 1 := by simp
    exact hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds h0)
  filter_upwards [hev] with z hz
  funext y
  rw [(hW.2 f hf).1 z y]
  by_cases hy : y ∈ tsupport f
  · rw [Et.psiK, hψ.1 _ (hz y hy).le, one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hy, mul_zero]

theorem fix_l [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) (x : A.K) (ω : A.K → ℂ)
    (μ : Measure A.L) (γ : ℂ) (W : SpecialLinearGroup (Fin 2) A.K → (A.L → ℂ) → A.L → ℂ)
    (hW : A.IsWeil ψ x ω μ γ W) (f : A.L → ℂ) (hf : IsTest f) :
    ∀ᶠ u in 𝓝 (0 : A.K), W (lS u) f = f := by
  have h1 := fix_n A ψ hψ x ω μ γ W hW (W (wS A.K) f) (hW.1.1 _ _ hf)
  have h2 : Tendsto (fun u : A.K => -u) (𝓝 0) (𝓝 0) := by simpa using (continuous_neg.tendsto (0 : A.K))
  filter_upwards [h2.eventually h1] with u hu
  have hwf := hW.1.1 (wS A.K) f hf
  calc W (lS u) f = W ((wS A.K)⁻¹ * nS (-u) * wS A.K) f := by rw [lS_eq]
    _ = W (wS A.K)⁻¹ (W (nS (-u)) (W (wS A.K) f)) := by
        rw [hW.1.2.2.1 _ _ _ hf, hW.1.2.2.1 _ _ _ hwf]
    _ = W ((wS A.K)⁻¹ * wS A.K) f := by rw [hu, hW.1.2.2.1 _ _ _ hf]
    _ = f := by rw [inv_mul_cancel, hW.1.2.1 _ hf]

theorem jx_mem_induced : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L) (γ : ℂ) W, A.IsWeil ψ x A.etaK μ γ W → ∀ φ, IsTest φ → A.InI (fun g => W g φ 0) ∧ (φ ≠ 0 → γ ≠ 0) := by
  intro F E _ _ _ _ _ A ψ hψ x μ γ W hW φ hφ
  obtain ⟨⟨htest, hone, hmul, hlin⟩, hact⟩ := id hW
  have ht0 : IsTest (0 : A.L → ℂ) := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  have h0 : ∀ g, W g 0 = 0 := by
    intro g
    have := hlin g (-1) 0 0 ht0 ht0
    simpa using this
  have hfix : ∀ g h, W h φ = φ → W (g * h) φ = W g φ := fun g h hh => by rw [hmul _ _ _ hφ, hh]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hn := fix_n A ψ hψ x A.etaK μ γ W hW φ hφ
    have hl := fix_l A ψ hψ x A.etaK μ γ W hW φ hφ
    obtain ⟨hunit, hinv⟩ := inv_cont A
    have hQ : ∀ᶠ u in 𝓝 (0 : A.K), ∀ᶠ v in 𝓝 u, W (lS v) φ = φ := hl.eventually_nhds
    haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
    have hcm : Continuous (algebraMap F A.K) := continuous_algebraMap F A.K
    have hQ2 : ∀ᶠ c in 𝓝 (0 : F), (∀ᶠ v in 𝓝 (algebraMap F A.K c), W (lS v) φ = φ) ∧
        ∀ᶠ v in 𝓝 (-algebraMap F A.K c), W (lS v) φ = φ := by
      have e1 : Tendsto (algebraMap F A.K) (𝓝 0) (𝓝 0) := by simpa using hcm.tendsto 0
      have e2 : Tendsto (fun c => -algebraMap F A.K c) (𝓝 0) (𝓝 0) := by simpa using (hcm.tendsto 0).neg
      exact (e1.eventually hQ).and (e2.eventually hQ)
    haveI := NormedField.nhdsNE_neBot (0 : F)
    obtain ⟨c, ⟨hc1, hc2⟩, hc0⟩ := ((hQ2.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : {y : F | y ≠ 0} ∈ 𝓝[≠] (0 : F))).exists
    set t := algebraMap F A.K c with ht_def
    set t' := algebraMap F A.K c⁻¹ with ht'_def
    have htt : t * t' = 1 := by rw [ht_def, ht'_def, ← map_mul, mul_inv_cancel₀ hc0, map_one]
    have hq1 : Tendsto (fun q : A.K × A.K × A.K => q.1) (𝓝 (0, 0, 0)) (𝓝 0) :=
      continuous_fst.tendsto ((0 : A.K), (0 : A.K), (0 : A.K))
    have ha : Tendsto (fun q : A.K × A.K × A.K => 1 + q.1) (𝓝 (0, 0, 0)) (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : A.K))).add hq1
    have hi : Tendsto (fun q : A.K × A.K × A.K => Ring.inverse (1 + q.1)) (𝓝 (0, 0, 0)) (𝓝 1) := by
      have := hinv.tendsto.comp ha
      rw [Ring.inverse_one] at this
      exact this
    have hq2 : Tendsto (fun q : A.K × A.K × A.K => q.2.1) (𝓝 (0, 0, 0)) (𝓝 0) :=
      (continuous_fst.comp continuous_snd).tendsto ((0 : A.K), (0 : A.K), (0 : A.K))
    have hq3 : Tendsto (fun q : A.K × A.K × A.K => q.2.2) (𝓝 (0, 0, 0)) (𝓝 0) :=
      (continuous_snd.comp continuous_snd).tendsto ((0 : A.K), (0 : A.K), (0 : A.K))
    have key : ∀ᶠ q : A.K × A.K × A.K in 𝓝 (0, 0, 0), IsUnit (1 + q.1) ∧
        W (lS (q.2.2 * Ring.inverse (1 + q.1))) φ = φ ∧ W (nS (q.1 * t')) φ = φ ∧
        W (nS ((Ring.inverse (1 + q.1) - 1) * t')) φ = φ ∧ W (lS (-(t * (1 + q.1)))) φ = φ ∧
        W (nS (q.2.1 * Ring.inverse (1 + q.1))) φ = φ := by
      have f1 : Tendsto (fun q : A.K × A.K × A.K => q.2.2 * Ring.inverse (1 + q.1)) (𝓝 (0, 0, 0)) (𝓝 0) := by
        simpa using hq3.mul hi
      have f2 : Tendsto (fun q : A.K × A.K × A.K => q.1 * t') (𝓝 (0, 0, 0)) (𝓝 0) := by
        simpa using hq1.mul_const t'
      have f3 : Tendsto (fun q : A.K × A.K × A.K => (Ring.inverse (1 + q.1) - 1) * t') (𝓝 (0, 0, 0)) (𝓝 0) := by
        simpa using (hi.sub_const 1).mul_const t'
      have f4 : Tendsto (fun q : A.K × A.K × A.K => -(t * (1 + q.1))) (𝓝 (0, 0, 0)) (𝓝 (-t)) := by
        simpa using (ha.const_mul t).neg
      have f5 : Tendsto (fun q : A.K × A.K × A.K => q.2.1 * Ring.inverse (1 + q.1)) (𝓝 (0, 0, 0)) (𝓝 0) := by
        simpa using hq2.mul hi
      exact (ha.eventually hunit).and ((f1.eventually hl).and ((f2.eventually hn).and ((f3.eventually hn).and
        ((f4.eventually hc2).and (f5.eventually hn)))))
    rw [nhds_prod_eq, nhds_prod_eq] at key
    obtain ⟨p1, hp1, p2, hp2, h12⟩ := eventually_prod_iff.1 key
    obtain ⟨p3, hp3, p4, hp4, h34⟩ := eventually_prod_iff.1 hp2
    refine ⟨{e | p1 e ∧ p3 e ∧ p4 e}, hp1.and (hp3.and hp4), ?_⟩
    intro g k hk
    have e00 : ((k : Matrix (Fin 2) (Fin 2) A.K) - 1) 0 0 = (k : Matrix (Fin 2) (Fin 2) A.K) 0 0 - 1 := by simp
    have e01 : ((k : Matrix (Fin 2) (Fin 2) A.K) - 1) 0 1 = (k : Matrix (Fin 2) (Fin 2) A.K) 0 1 := by simp
    have e10 : ((k : Matrix (Fin 2) (Fin 2) A.K) - 1) 1 0 = (k : Matrix (Fin 2) (Fin 2) A.K) 1 0 := by simp
    have k1 := (hk 0 0).1
    have k2 := (hk 0 1).2.1
    have k3 := (hk 1 0).2.2
    rw [e00] at k1
    rw [e01] at k2
    rw [e10] at k3
    obtain ⟨hu, hP1, hP2, hP3, hP4, hP5⟩ := h12 k1 (h34 k2 k3)
    have h1a : (1 : A.K) + ((k : Matrix (Fin 2) (Fin 2) A.K) 0 0 - 1) = (k : Matrix (Fin 2) (Fin 2) A.K) 0 0 := by ring
    simp only [h1a] at hu hP1 hP2 hP3 hP4 hP5
    have hdec := decomp k (Ring.inverse ((k : Matrix (Fin 2) (Fin 2) A.K) 0 0)) t t'
      (Ring.mul_inverse_cancel _ hu) htt
    have hk : W k φ = φ := by
      rw [hdec, hfix _ _ hP5, hfix _ _ ?_, hP1]
      rw [hfix _ _ hP4, hfix _ _ hP3, hfix _ _ hc1.self_of_nhds, hP2]
    show W (g * k) φ 0 = W g φ 0
    rw [hfix _ _ hk]
  · intro z s g
    have hg := htest g φ hφ
    show W (nS z * mS s * g) φ 0 = A.etaK s * (A.absK s : ℂ) * W g φ 0
    rw [hmul _ _ _ hφ, hmul _ _ _ hg, (hact _ (htest _ _ hg)).1 z 0, (hact _ hg).2.1 s 0, smul_zero,
      (nl_cont A).2]
    simp [Et.psiK]
  · intro hne hγ
    apply hne
    have hw : W (wS A.K) φ = 0 := funext fun y => by rw [(hact φ hφ).2.2 y, hγ, zero_mul]; rfl
    calc φ = W 1 φ := (hone φ hφ).symm
      _ = W ((wS A.K)⁻¹ * wS A.K) φ := by rw [inv_mul_cancel]
      _ = 0 := by rw [hmul _ _ _ hφ, hw, h0]

end GlobalTheory.WeilSmooth
end
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.SelfDualUniq

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]

theorem fourB_nnsmul (μ : Measure V) (c : NNReal) (B : V → V → ℂ) (f : V → ℂ) (y : V) :
    fourB (c • μ) B f y = ((c : ℝ) : ℂ) * fourB μ B f y := by
  simp only [fourB, integral_smul_nnreal_measure]
  rw [NNReal.smul_def, Complex.real_smul]

theorem fourB_const_mul (μ : Measure V) (a : ℂ) (B : V → V → ℂ) (g : V → ℂ) (y : V) :
    fourB μ B (fun z => a * g z) y = a * fourB μ B g y := by
  simp only [fourB, mul_assoc]
  exact integral_const_mul a _

theorem selfDual_unique [IsTopologicalAddGroup V] [T2Space V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [BorelSpace V] {B : V → V → ℂ} {μ ν : Measure V}
    (hμ : SelfDual μ B) (hν : SelfDual ν B) (f : V → ℂ) (hf : IsTest f) (h0 : f 0 ≠ 0) : ν = μ := by
  obtain ⟨hμH, hμI⟩ := hμ
  obtain ⟨hνH, hνI⟩ := hν
  have hc := Measure.isAddLeftInvariant_eq_smul ν μ
  set c := Measure.addHaarScalarFactor ν μ
  have key := hνI f hf 0
  rw [hc] at key
  have e : fourB (c • μ) B f = fun y => ((c : ℝ) : ℂ) * fourB μ B f y := funext (fourB_nnsmul μ c B f)
  rw [e, fourB_nnsmul, fourB_const_mul, hμI f hf 0, neg_zero] at key
  have hsq : (((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) - 1) * f 0 = 0 := by linear_combination key
  have h1 : ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) = 1 := by
    have := (mul_eq_zero.1 hsq).resolve_right h0
    linear_combination this
  have h2 : (c : ℝ) * (c : ℝ) = 1 := by exact_mod_cast h1
  have h3 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
  have h4 : c = 1 := by exact_mod_cast h3
  rw [hc, h4, one_smul]

end GlobalTheory.JR.SelfDualUniq

namespace GlobalTheory.JR.SelfDualUniq

theorem isTest_fourB {F : Type} [NontriviallyNormedField F] [IsUltrametricDist F] [LocallyCompactSpace F]
    (ψ : AddChar F ℂ) (hψ : IsStdChar ψ)
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V]
    [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V) (hs : β.IsSymm) (hn : β.Nondegenerate)
    (μ : Measure V) [μ.IsAddHaarMeasure] (f : V → ℂ) (hf : IsTest f) :
    IsTest (fourB μ (fun x y => ψ (β x y)) f) := by
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F V
  obtain ⟨-, hl⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ V β hs hn
  obtain ⟨U, hU, hUinv⟩ := AbsInv.exists_nhds_invariant hf
  obtain ⟨M, N, hMU, -, -, -, hNc, hN, -⟩ := hl U hU
  have hβ : Continuous (fun p : V × V => β p.1 p.2) :=
    IsModuleTopology.continuous_bilinear_of_finite_left β
  have hev : ∀ᶠ w in 𝓝 (0 : V), ∀ x ∈ tsupport f, ψ (β x w) = 1 := by
    refine hf.2.isCompact.eventually_forall_of_forall_eventually fun x _ => ?_
    have hc : Continuous (fun z : V × V => β z.2 z.1) := hβ.comp continuous_swap
    have ho : IsOpen {z : V × V | ‖β z.2 z.1‖ < 1} := isOpen_lt (continuous_norm.comp hc) continuous_const
    have hmem : ((0 : V), x) ∈ {z : V × V | ‖β z.2 z.1‖ < 1} := by simp
    filter_upwards [ho.mem_nhds hmem] with z hz
    exact hψ.1 _ hz.le
  constructor
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro y
    have hev' : ∀ᶠ y' in 𝓝 y, ∀ x ∈ tsupport f, ψ (β x (y' - y)) = 1 := by
      have ht : Tendsto (fun y' : V => y' - y) (𝓝 y) (𝓝 0) := by
        have h := (continuous_sub_right y).tendsto y
        rwa [sub_self] at h
      exact ht.eventually hev
    filter_upwards [hev'] with y' hy'
    simp only [fourB]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport f
    · have : β x y' = β x y + β x (y' - y) := by simp
      simp only [this, AddChar.map_add_eq_mul, hy' x hx, mul_one]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · refine HasCompactSupport.intro hNc fun y hy => ?_
    have : ¬ ∀ x ∈ M, ψ (β x y) = 1 := fun h => hy ((hN y).2 h)
    push_neg at this
    obtain ⟨m, hm, hne⟩ := this
    refine AbsInv.integral_eq_zero_of_translate μ _ m _ hne fun x => ?_
    simp only [map_add (f := _), LinearMap.add_apply, AddChar.map_add_eq_mul, hUinv M hMU x m hm]
    ring

theorem selfDual_exists_unique_isTest : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V] [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (β : LinearMap.BilinForm F V), β.IsSymm → β.Nondegenerate → (∃! μ : Measure V, SelfDual μ (fun x y => ψ (β x y))) ∧ ∀ μ : Measure V, μ.IsAddHaarMeasure → ∀ f, IsTest f → IsTest (fourB μ (fun x y => ψ (β x y)) f) := by
  intro F E _ _ _ _ hU ψ hψ V _ _ _ _ _ _ _ β hs hn
  haveI := hU.ultraF
  haveI := hU.lcF
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F V
  obtain ⟨-, hl⟩ := GlobalTheory.JR.exists_small_dual_lattices F ψ hψ V β hs hn
  obtain ⟨M, N, -, hMo, hMc, -, -, -, -⟩ := hl Set.univ Filter.univ_mem
  have hM1 : IsClopen (M : Set V) := ⟨AddSubgroup.isClosed_of_isOpen M hMo, hMo⟩
  set f : V → ℂ := ⇑(LocallyConstant.charFn ℂ hM1) with hfdef
  have hf : IsTest f := ⟨(LocallyConstant.charFn ℂ hM1).isLocallyConstant,
    HasCompactSupport.intro hMc fun x hx => by simp [f, LocallyConstant.coe_charFn, hx]⟩
  have hf0 : f 0 ≠ 0 := by simp [f, LocallyConstant.coe_charFn, M.zero_mem]
  refine ⟨?_, fun μ hμ g hg => isTest_fourB ψ hψ V β hs hn μ g hg⟩
  obtain ⟨μ, hμ⟩ := EtMeas.exists_selfDual F ψ hψ V β hs hn
  exact ⟨μ, hμ, fun ν hν => selfDual_unique hμ hν f hf hf0⟩

end GlobalTheory.JR.SelfDualUniq
end
end

section

open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.exists_hom_specialLinearGroup_of_relations : ∀ (K : Type) [CommRing K], IsField K → ∀ (M : Type) [Monoid M] (n : K → M) (m : Kˣ → M) (t : M), n 0 = 1 → (∀ a b, n (a + b) = n a * n b) → m 1 = 1 → (∀ a b, m (a * b) = m a * m b) → (∀ s z, m s * n z = n ((s : K) ^ 2 * z) * m s) → t * t = m (-1) → (∀ s, t * m s = m s⁻¹ * t) → (∀ u : Kˣ, t * n u * t = n (-((u⁻¹ : Kˣ) : K)) * m (-u⁻¹) * t * n (-((u⁻¹ : Kˣ) : K))) → ∃ ρ : SpecialLinearGroup (Fin 2) K →* M, (∀ z, ρ (nS z) = n z) ∧ (∀ s, ρ (mS s) = m s) ∧ ρ (wS K) = t := by
  first | exact @GlobalTheory.BruhatRep.exists_hom_of_bruhat | exact GlobalTheory.BruhatRep.exists_hom_of_bruhat | (intros; apply GlobalTheory.BruhatRep.exists_hom_of_bruhat <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.idempotent_decomposition_of_integrality : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] [IsUltrametricDist F] (A : Et F E), (∀ (k : Type) [Field k] [Algebra F k] [FiniteDimensional F k] (y : k), y ≠ 0 → IsIntegral (NormedField.valuation (K := F)).integer y ∨ IsIntegral (NormedField.valuation (K := F)).integer y⁻¹) → ∃ (m : ℕ) (f : Fin m → A.K), (∀ i, f i * f i = f i) ∧ (∀ i j, i ≠ j → f i * f j = 0) ∧ ∑ i, f i = 1 ∧ (∀ i (c : F), 1 < ‖c‖ → algebraMap F A.K c * f i ∉ A.OK) ∧ ∀ i (y : A.K), f i * y ∉ A.OK → ∃ w ∈ A.OK, w * (f i * y) = f i := by
  first | exact @GlobalTheory.JR.Et.Idem.main | exact GlobalTheory.JR.Et.Idem.main | (intros; apply GlobalTheory.JR.Et.Idem.main <;> assumption)
end

section

namespace GlobalTheory.NatCastNormLtOne

theorem norm_natCast_lt_one {l : ℕ} [Fact (Nat.Prime l)] {K : Type} [NormedField K]
    [NormedAlgebra ℚ_[l] K] : ‖(l : K)‖ < 1 := by
  have h : (l : K) = algebraMap ℚ_[l] K (l : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem exists_pow_mul_norm_le {K : Type} [NormedField K] {x : K} (hx : ‖x‖ < 1) (a : K) :
    ∃ n : ℕ, ‖x ^ n * a‖ ≤ 1 := by
  have h : Filter.Tendsto (fun n : ℕ => ‖x‖ ^ n * ‖a‖) Filter.atTop (nhds (0 * ‖a‖)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg x) hx).mul_const _
  rw [zero_mul] at h
  obtain ⟨n, hn⟩ := (h.eventually (gt_mem_nhds (zero_lt_one' ℝ))).exists
  exact ⟨n, by rw [norm_mul, norm_pow]; exact hn.le⟩

theorem exists_pow_smul_mem {l : ℕ} [hl : Fact (Nat.Prime l)] {O K : Type} [CommRing O]
    [NormedField K] [Algebra O K] [GlobalTheory.BK.IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
    {V : Type} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (T : Submodule O V) (hT : Submodule.span K (T : Set V) = ⊤) (v : V) :
    ∃ n : ℕ, (l : K) ^ n • v ∈ T := by
  have hpow : ∀ (k : ℕ) (w : V), w ∈ T → (l : K) ^ k • w ∈ T := by
    intro k w hw
    have h : (l : K) ^ k = algebraMap O K ((l : O) ^ k) := by simp
    rw [h, algebraMap_smul]
    exact T.smul_mem _ hw
  have hv : v ∈ Submodule.span K (T : Set V) := by rw [hT]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := hy
    refine ⟨n + m, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]; exact hpow _ _ hn
    · rw [pow_add, mul_smul]; exact hpow _ _ hm
  | smul a x _ hx =>
    obtain ⟨n, hn⟩ := hx
    obtain ⟨m, hm⟩ := exists_pow_mul_norm_le (norm_natCast_lt_one (l := l) (K := K)) a
    obtain ⟨b, hb⟩ := (GlobalTheory.BK.IsUnitBall.mem_range_iff (O := O) ((l : K) ^ m * a)).2 hm
    refine ⟨m + n, ?_⟩
    have h : (l : K) ^ (m + n) • a • x = b • ((l : K) ^ n • x) := by
      rw [← algebraMap_smul K b, hb, smul_smul, smul_smul]
      congr 1
      ring
    rw [h]
    exact T.smul_mem _ hn

theorem main : ∀ {l : ℕ} [hl : Fact (Nat.Prime l)] {O K : Type} [inst : CommRing O]
    [inst_1 : NormedField K] [inst_2 : Algebra O K] [GlobalTheory.BK.IsUnitBall O K]
    [inst_4 : NormedAlgebra ℚ_[l] K] {G : Type} [inst_5 : Group G] [inst_6 : TopologicalSpace G]
    (T : Formalism.BasicNotions.LocLat G ℚ_[l] K O) (v : Formalism.BasicNotions.LocLat.V T),
    ∃ (n : ℕ), (↑l : K) ^ n • v ∈ Formalism.WeaklyAdmissibleFiltrations.Lattice.T (Formalism.BasicNotions.LocLat.L T) := by
  intro l _ O K _ _ _ _ _ G _ _ T v
  exact exists_pow_smul_mem T.L.T T.L.span v

end GlobalTheory.NatCastNormLtOne
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.exists_X_pow_smul_eq_prime_pow_smul_phiModule : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι), ∀ (n : ℕ), ∀ w ∈ P.MM, ∃ w' ∈ P.MM, (X : K⟦X⟧) ^ (e * l ^ (n + 1)) • w = (l : K) ^ (l ^ n) • w' := by
  first | exact @GlobalTheory.BK.PhiMod.exists_X_pow_smul_eq_l_pow_smul | exact GlobalTheory.BK.PhiMod.exists_X_pow_smul_eq_l_pow_smul | (intros; apply GlobalTheory.BK.PhiMod.exists_X_pow_smul_eq_l_pow_smul <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.mem_prime_pow_lattice_of_X_pow_smul_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (P : PhiMod O K l e a ι) (n b : ℕ) (w z : Vec K a ι), w ∈ P.L → z ∈ P.L → ((X : K⟦X⟧) ^ e) ^ n • w = (l : K) ^ b • z → ∃ z' ∈ P.L, w = (l : K) ^ b • z' := by
  first | exact @GlobalTheory.CokerL.mem_lpow_L_of_vpow_smul | exact GlobalTheory.CokerL.mem_lpow_L_of_vpow_smul | (intros; apply GlobalTheory.CokerL.mem_lpow_L_of_vpow_smul <;> assumption)
end

section

open PowerSeries GlobalTheory.BK

theorem _root_.GlobalTheory.T.X_pow_smul_mem_prime_pow_add_filtration_phiModule : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (P : PhiMod O K l e a ι), ∀ (j : ℕ), j ≤ l → ∀ w ∈ P.MM, ∃ s ∈ P.MM, ∃ f ∈ P.FilMM j, (X : K⟦X⟧) ^ (e * l) • w = (l : K) ^ (l - j) • s + f := by
  first | exact @GlobalTheory.BK.X_pow_smul_mem_l_pow_MM_add_FilMM | exact GlobalTheory.BK.X_pow_smul_mem_l_pow_MM_add_FilMM | (intros; apply GlobalTheory.BK.X_pow_smul_mem_l_pow_MM_add_FilMM <;> assumption)
end

section


theorem _root_.GlobalTheory.T.isSupercuspidal_comp_generalLinearGroupMapOfFieldEquiv : ∀ {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] (i : k ≃+* k'), Continuous i.symm → ∀ {n : Type} [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V), GlobalTheory.SmGL.IsCuspidal π → GlobalTheory.SmGL.IsCuspidal (π.comp (Matrix.GeneralLinearGroup.map (n := n) i.symm.toRingHom)) := by
  first | exact @GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap | exact GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap | (intros; apply GlobalTheory.LocGL.isCuspidal_comp_generalLinearGroupMap <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.jacquetRallisHankelDet_ne_zero_of_lift : ∀ (k : Type) [Field k] (r : ℕ) (Z : Gl r k) (μ l : k), Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 := by
  first | exact @GlobalTheory.JR.Step.delta_lift_ne | exact GlobalTheory.JR.Step.delta_lift_ne | (intros; apply GlobalTheory.JR.Step.delta_lift_ne <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.unitary_orbit_normal_form_unit_invariant : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (X : Hn (r + 1) F E) (a : Inv (r + 1) F), HasInv X a → ‖a.2.1 0‖ = 1 → ∃ (g : Matrix.unitaryGroup (Fin (r + 1)) E) (X' : Hn r F E) (ν : E), ν * star ν = algebraMap F E (a.2.1 0) ∧ actU g X = GlobalTheory.JR.Step.liftH X' ν a.2.2 := by
  first | exact @GlobalTheory.JR.Step.uNormal | exact GlobalTheory.JR.Step.uNormal | (intros; apply GlobalTheory.JR.Step.uNormal <;> assumption)
end
