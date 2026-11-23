module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.EnergyAbs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory
open scoped InnerProductSpace ComplexConjugate ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

section General

variable {α β : Type} [MeasurableSpace α] [MeasurableSpace β]

private theorem norm_eq_of_inner_self_eq_inner_self_lemma {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {a b : E} (h : ⟪a, a⟫_ℂ = ⟪b, b⟫_ℂ) : ‖a‖ = ‖b‖ := by
  have h2 : ‖a‖ ^ 2 = ‖b‖ ^ 2 := by
    have h' := h
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h'
    exact_mod_cast h'
  nlinarith [norm_nonneg a, norm_nonneg b]

end General

section Main

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable {HH : Type} [NormedAddCommGroup HH] [InnerProductSpace ℂ HH] [CompleteSpace HH]
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def gvec (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (x : G) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ V) => HH) :=
  WithLp.toLp 2 (fun i => ⟪W x, stdOrthonormalBasis ℂ V i⟫_ℂ • σ x w)

def Fk (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (z z' q : G) : ℂ :=
  ⟪W (q * z'), W z⟫_ℂ * ⟪σ z w, σ (q * z') w⟫_ℂ

theorem fol_rep_norm {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (x : G) (a : HH) : ‖σ x a‖ = ‖a‖ := by
  obtain ⟨-, -, hin, -⟩ := id hσ
  exact norm_eq_of_inner_self_eq_inner_self_lemma (hin x a a)

theorem fol_rep_mul {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (x y : G) (a : HH) :
    σ (x * y) a = σ x (σ y a) := by
  obtain ⟨-, hmul, -, -⟩ := id hσ
  calc σ (x * y) a = (σ x * σ y) a := by rw [hmul x y]
    _ = σ x (σ y a) := rfl

theorem W_inner_trans {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    {s : G} (hs : s ∈ S) (x y : G) : ⟪W (s * x), W (s * y)⟫_ℂ = ⟪W x, W y⟫_ℂ := by
  rw [hWeq s hs x, hWeq s hs y, hτu s hs]

theorem W_norm_trans {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    {s : G} (hs : s ∈ S) (x : G) : ‖W (s * x)‖ = ‖W x‖ :=
  norm_eq_of_inner_self_eq_inner_self_lemma (W_inner_trans hWeq hτu hs x x)

theorem gvec_continuous {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} (hWc : Continuous W) :
    Continuous (gvec σ w W) := by
  obtain ⟨-, -, -, hσc⟩ := id hσ
  have hi : ∀ i : Fin (Module.finrank ℂ V),
      Continuous fun x => ⟪W x, stdOrthonormalBasis ℂ V i⟫_ℂ • σ x w :=
    fun i => (hWc.inner continuous_const).smul (hσc w)
  show Continuous fun x =>
    (WithLp.toLp 2 (fun i => ⟪W x, stdOrthonormalBasis ℂ V i⟫_ℂ • σ x w) :
      PiLp 2 (fun _ : Fin (Module.finrank ℂ V) => HH))
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi hi)

theorem gvec_norm {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {w : HH} (hw : ‖w‖ = 1) (W : G → V) (x : G) :
    ‖gvec σ w W x‖ = ‖W x‖ := by
  have hn : ‖σ x w‖ = 1 := by rw [(fol_rep_norm hσ), hw]
  have key : ∑ i, ‖⟪W x, stdOrthonormalBasis ℂ V i⟫_ℂ‖ ^ 2 = ‖W x‖ ^ 2 := by
    exact (stdOrthonormalBasis ℂ V).sum_sq_norm_inner_left (W x)
  have hs : ‖gvec σ w W x‖ ^ 2 = ‖W x‖ ^ 2 := by
    rw [← key]
    rw [PiLp.norm_sq_eq_of_L2]
    exact Finset.sum_congr rfl fun i _ => by simp [gvec, norm_smul, hn]
  nlinarith [norm_nonneg (gvec σ w W x), norm_nonneg (W x)]

theorem gvec_inner (σ : G → (HH →L[ℂ] HH)) (w : HH) (W : G → V) (x y : G) :
    ⟪gvec σ w W x, gvec σ w W y⟫_ℂ = ⟪W y, W x⟫_ℂ * ⟪σ x w, σ y w⟫_ℂ := by
  have hb : ∑ i, ⟪W y, stdOrthonormalBasis ℂ V i⟫_ℂ * ⟪stdOrthonormalBasis ℂ V i, W x⟫_ℂ = ⟪W y, W x⟫_ℂ := by
    exact (stdOrthonormalBasis ℂ V).sum_inner_mul_inner (W y) (W x)
  rw [← hb, Finset.sum_mul]
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [gvec, PiLp.toLp_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

theorem Fk_continuous {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {W : G → V} (hWc : Continuous W)
    {X : Type} [TopologicalSpace X] {a b c : X → G} (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
    Continuous (fun x => Fk σ w W (a x) (b x) (c x)) := by
  obtain ⟨-, -, -, hσc⟩ := id hσ
  have hcb : Continuous fun x => c x * b x := hc.mul hb
  have h1 : Continuous fun x => W (c x * b x) := hWc.comp hcb
  have h2 : Continuous fun x => W (a x) := hWc.comp ha
  have h3 : Continuous fun x => σ (a x) w := (hσc w).comp ha
  have h4 : Continuous fun x => σ (c x * b x) w := (hσc w).comp hcb
  show Continuous fun x => ⟪W (c x * b x), W (a x)⟫_ℂ * ⟪σ (a x) w, σ (c x * b x) w⟫_ℂ
  exact (h1.inner h2).mul (h3.inner h4)

theorem Fk_bound {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) {w : HH} (hw : ‖w‖ = 1) {S : Set G}
    {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (z z' : G) {q : G} (hq : q ∈ S) : ‖Fk σ w W z z' q‖ ≤ ‖W z‖ * ‖W z'‖ := by
  have h1 : ‖⟪W (q * z'), W z⟫_ℂ‖ ≤ ‖W z‖ * ‖W z'‖ := by
    calc ‖⟪W (q * z'), W z⟫_ℂ‖ ≤ ‖W (q * z')‖ * ‖W z‖ := norm_inner_le_norm _ _
      _ = ‖W z‖ * ‖W z'‖ := by rw [W_norm_trans hWeq hτu hq z', mul_comm]
  have h2 : ‖⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ 1 := by
    calc ‖⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ ‖σ z w‖ * ‖σ (q * z') w‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [(fol_rep_norm hσ), (fol_rep_norm hσ), hw, mul_one]
  show ‖⟪W (q * z'), W z⟫_ℂ * ⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ ‖W z‖ * ‖W z'‖
  rw [norm_mul]
  calc ‖⟪W (q * z'), W z⟫_ℂ‖ * ‖⟪σ z w, σ (q * z') w⟫_ℂ‖ ≤ (‖W z‖ * ‖W z'‖) * 1 :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = ‖W z‖ * ‖W z'‖ := mul_one _

theorem kF {σ : G → (HH →L[ℂ] HH)} (hσ : IsUnitRep σ) (w : HH) {S : Set G} {τ : G → (V →L[ℂ] V)} {W : G → V}
    (hSinv : ∀ a ∈ S, a⁻¹ ∈ S)
    (hWeq : ∀ s ∈ S, ∀ x, W (s * x) = τ s (W x)) (hτu : ∀ s ∈ S, ∀ a b, ⟪τ s a, τ s b⟫_ℂ = ⟪a, b⟫_ℂ)
    (z z' : G) {s t : G} (hs : s ∈ S) :
    ⟪W (t⁻¹ * z'), W (s⁻¹ * z)⟫_ℂ * ⟪σ (s⁻¹ * z) w, σ (t⁻¹ * z') w⟫_ℂ = Fk σ w W z z' (s * t⁻¹) := by
  obtain ⟨-, -, hin, -⟩ := id hσ
  have e1 : ⟪W (t⁻¹ * z'), W (s⁻¹ * z)⟫_ℂ = ⟪W (s * t⁻¹ * z'), W z⟫_ℂ := by
    rw [← W_inner_trans hWeq hτu hs (t⁻¹ * z') (s⁻¹ * z), mul_assoc, mul_inv_cancel_left]
  have e2 : ⟪σ (s⁻¹ * z) w, σ (t⁻¹ * z') w⟫_ℂ = ⟪σ z w, σ (s * t⁻¹ * z') w⟫_ℂ := by
    rw [← hin s (σ (s⁻¹ * z) w) (σ (t⁻¹ * z') w), ← (fol_rep_mul hσ), ← (fol_rep_mul hσ), mul_inv_cancel_left,
      mul_assoc]
  rw [e1, e2]
  rfl

end Main

end Formalism.L2.S.Pv.EnergyAbs
end
end

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.S.Pv.EnergyAbs

open Formalism.L2.SG.Pf.EnergyAbs

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]

def cnt (μS : Measure G) (Ω : Set G) (q : G) : ℝ≥0∞ := μS {t | t ∈ Ω ∧ q * t ∈ Ω}

theorem cnt_measurable {μS : Measure G} [SFinite μS] {Ω : Set G} (hΩ : MeasurableSet Ω) :
    Measurable (cnt μS Ω) := by
  have hT : MeasurableSet {p : G × G | p.2 ∈ Ω ∧ p.1 * p.2 ∈ Ω} :=
    (measurable_snd hΩ).inter ((measurable_fst.mul measurable_snd) hΩ)
  exact measurable_measure_prodMk_left hT

theorem cnt_le (μS : Measure G) (Ω : Set G) (q : G) : cnt μS Ω q ≤ μS Ω := measure_mono fun t ht => ht.1

theorem conv_map {S : Set G} {μS : Measure G} [SFinite μS] (hS : IsHaarSub S μS) {Ω : Set G}
    (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S) :
    ((μS.restrict Ω).prod (μS.restrict Ω)).map (fun p : G × G => p.1 * p.2⁻¹) = μS.withDensity (cnt μS Ω) := by
  classical
  obtain ⟨-, -, -, -, -, -, -, -, -, hright, -⟩ := hS
  have hg : Measurable (fun p : G × G => p.1 * p.2⁻¹) := measurable_fst.mul measurable_snd.inv
  ext A hA
  rw [Measure.map_apply hg hA, withDensity_apply _ hA]
  set P : Set (G × G) := {p | p.1 ∈ A ∧ p.2 ∈ Ω ∧ p.1 * p.2 ∈ Ω} with hPdef
  have hP : MeasurableSet P :=
    (measurable_fst hA).inter ((measurable_snd hΩm).inter ((measurable_fst.mul measurable_snd) hΩm))
  have h1 : (μS.prod μS) P = ∫⁻ q in A, cnt μS Ω q ∂μS := by
    rw [Measure.prod_apply hP, ← lintegral_indicator hA]
    refine lintegral_congr fun q => ?_
    rw [Set.indicator_apply]
    by_cases hq : q ∈ A
    · rw [if_pos hq]
      unfold cnt
      congr 1
      ext t
      simp [hPdef, hq]
    · rw [if_neg hq]
      have hempty : Prod.mk q ⁻¹' P = ∅ := by
        ext t
        simp [hPdef, hq]
      rw [hempty, measure_empty]
  have h2 : (μS.prod μS) P =
      ((μS.restrict Ω).prod (μS.restrict Ω)) ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) := by
    rw [Measure.prod_apply_symm hP, Measure.prod_apply_symm (hg hA), ← lintegral_indicator hΩm]
    refine lintegral_congr fun t => ?_
    rw [Set.indicator_apply]
    by_cases ht : t ∈ Ω
    · rw [if_pos ht]
      have hBt : MeasurableSet
          ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A)) :=
        (measurable_mul_const t⁻¹) hA
      rw [Measure.restrict_apply hBt]
      have hmt := hright t (hΩS ht)
      calc μS ((fun x => (x, t)) ⁻¹' P)
          = μS ((fun x => x * t) ⁻¹'
              ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) ∩ Ω)) := by
            congr 1
            ext q
            simp [hPdef, ht]
        _ = (μS.map (fun x => x * t))
              ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) ∩ Ω) :=
            (Measure.map_apply (measurable_mul_const t) (hBt.inter hΩm)).symm
        _ = μS ((fun x => (x, t)) ⁻¹' ((fun p : G × G => p.1 * p.2⁻¹) ⁻¹' A) ∩ Ω) := by
            rw [hmt]
    · rw [if_neg ht]
      have hempty : (fun x => (x, t)) ⁻¹' P = ∅ := by
        ext q
        simp [hPdef, ht]
      rw [hempty, measure_empty]
  exact h2.symm.trans h1

theorem conv_integral {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {S : Set G} {μS : Measure G} [SFinite μS]
    (hS : IsHaarSub S μS) {Ω : Set G} (hΩm : MeasurableSet Ω) (hΩS : Ω ⊆ S) (hfin : μS Ω < ⊤) (f : G → E)
    (hf : StronglyMeasurable f)
    (hint : Integrable (fun p : G × G => f (p.1 * p.2⁻¹)) ((μS.restrict Ω).prod (μS.restrict Ω))) :
    ∫ s in Ω, ∫ t in Ω, f (s * t⁻¹) ∂μS ∂μS = ∫ q, (cnt μS Ω q).toReal • f q ∂μS := by
  have hg : Measurable (fun p : G × G => p.1 * p.2⁻¹) := measurable_fst.mul measurable_snd.inv
  have hI : Integrable (fun p : G × G => f (p.1 * p.2⁻¹)) ((μS.restrict Ω).prod (μS.restrict Ω)) := by
    assumption
  have h1 : ∫ s in Ω, ∫ t in Ω, f (s * t⁻¹) ∂μS ∂μS
      = ∫ p, f (p.1 * p.2⁻¹) ∂((μS.restrict Ω).prod (μS.restrict Ω)) :=
    (integral_prod (fun p : G × G => f (p.1 * p.2⁻¹)) hI).symm
  have h2 : ∫ p, f (p.1 * p.2⁻¹) ∂((μS.restrict Ω).prod (μS.restrict Ω))
      = ∫ q, f q ∂(((μS.restrict Ω).prod (μS.restrict Ω)).map (fun p : G × G => p.1 * p.2⁻¹)) :=
    (integral_map_of_stronglyMeasurable hg hf).symm
  rw [h1, h2, conv_map hS hΩm hΩS]
  exact integral_withDensity_eq_integral_toReal_smul (cnt_measurable hΩm)
    (ae_of_all _ fun q => (cnt_le μS Ω q).trans_lt hfin) f

end Formalism.L2.S.Pv.EnergyAbs
end
end

section

set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Measure Filter Topology
open scoped ENNReal

namespace Formalism.L2.S.Pv.FolnerT

open Formalism.L2.SG.Pf.EnergyAbs

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

theorem isHaarSub_comap (Φ : G ≃* H) (hΦ : Continuous Φ) (hΦ' : Continuous Φ.symm) {S : Set H} {μ : Measure H}
    (hμ : IsHaarSub S μ) : IsHaarSub (Φ ⁻¹' S) (μ.map Φ.symm) := by
  obtain ⟨hC, h1, hm, hi, hσ, h0, hc, hl, hK, hr, hinv⟩ := hμ
  have hs : Measurable Φ.symm := hΦ'.measurable
  let E : G ≃ₜ H := { Φ.toEquiv with continuous_toFun := hΦ, continuous_invFun := hΦ' }
  let M : G ≃ᵐ H := E.toMeasurableEquiv
  have hmap : ∀ A : Set G, (μ.map Φ.symm) A = μ (Φ.symm ⁻¹' A) := fun A => by
    exact MeasurableEquiv.map_apply M.symm A
  refine ⟨hC.preimage hΦ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Φ 1 ∈ S
    rw [map_one]
    exact h1
  · intro a ha b hb
    show Φ (a * b) ∈ S
    rw [map_mul]
    exact hm _ ha _ hb
  · intro a ha
    show Φ a⁻¹ ∈ S
    rw [map_inv]
    exact hi _ ha
  · haveI := hσ
    show SigmaFinite (μ.map M.symm)
    first
      | exact M.symm.sigmaFinite_map
      | exact MeasurableEquiv.sigmaFinite_map M.symm
      | (refine SigmaFinite.of_map _ M.measurable.aemeasurable ?_
         rw [Measure.map_map M.measurable M.symm.measurable, M.self_comp_symm, Measure.map_id]
         exact hσ)
  · intro h
    exact h0 ((Measure.map_eq_zero_iff hs.aemeasurable).1 h)
  · rw [hmap]
    convert hc using 2
    ext x
    simp
  · intro s hsS
    rw [Measure.map_map (continuous_const_mul s).measurable hs]
    have e1 : (fun x => s * x) ∘ ⇑Φ.symm = ⇑Φ.symm ∘ (fun y => Φ s * y) := by
      funext y
      simp
    rw [e1, ← Measure.map_map hs (continuous_const_mul (Φ s)).measurable, hl _ hsS]
  · intro K hKc
    rw [hmap]
    exact hK _ ((E.symm.isCompact_preimage).2 hKc)
  · intro s hsS
    rw [Measure.map_map (continuous_mul_const s).measurable hs]
    have e1 : (fun x => x * s) ∘ ⇑Φ.symm = ⇑Φ.symm ∘ (fun y => y * Φ s) := by
      funext y
      simp
    rw [e1, ← Measure.map_map hs (continuous_mul_const (Φ s)).measurable, hr _ hsS]
  · rw [Measure.map_map continuous_inv.measurable hs]
    have e1 : (fun x : G => x⁻¹) ∘ ⇑Φ.symm = ⇑Φ.symm ∘ (fun y => y⁻¹) := by
      funext y
      simp
    rw [e1, ← Measure.map_map hs continuous_inv.measurable, hinv]

theorem isFolner_of_equiv (Φ : G ≃* H) (hΦ : Continuous Φ) (hΦ' : Continuous Φ.symm) {S : Set H} {μ : Measure H}
    (hμ : IsHaarSub S μ) (hF : IsFolner (Φ ⁻¹' S) (μ.map Φ.symm)) : IsFolner S μ := by
  have hs : Measurable Φ.symm := hΦ'.measurable
  let E : G ≃ₜ H := { Φ.toEquiv with continuous_toFun := hΦ, continuous_invFun := hΦ' }
  let M : G ≃ᵐ H := E.toMeasurableEquiv
  have hmap : ∀ A : Set G, (μ.map Φ.symm) A = μ (Φ.symm ⁻¹' A) := fun A => by
    exact MeasurableEquiv.map_apply M.symm A
  intro K hK hKS ε hε
  obtain ⟨Ω, hΩm, hΩS, hpos, hfin, hle⟩ :=
    hF (Φ ⁻¹' K) ((E.isCompact_preimage).2 hK) (Set.preimage_mono hKS) ε hε
  refine ⟨Φ.symm ⁻¹' Ω, hs hΩm, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have := hΩS hx
    simpa using this
  · rw [← hmap]
    exact hpos
  · rw [← hmap]
    exact hfin
  · have hset : {t | t ∈ ⇑Φ.symm ⁻¹' Ω ∧ ∀ k ∈ K, k * t ∈ ⇑Φ.symm ⁻¹' Ω} =
        ⇑Φ.symm ⁻¹' {t | t ∈ Ω ∧ ∀ k ∈ ⇑Φ ⁻¹' K, k * t ∈ Ω} := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun k hk => ?_⟩
        have := h2 (Φ k) hk
        rwa [MulEquiv.symm_apply_apply] at this
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun k hk => ?_⟩
        exact h2 (Φ.symm k) (by simpa using hk)
    rw [hset, ← hmap, ← hmap]
    exact hle

end Formalism.L2.S.Pv.FolnerT
end
end
