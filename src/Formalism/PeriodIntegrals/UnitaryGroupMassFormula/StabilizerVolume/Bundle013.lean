module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle010
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVCos
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.FibDis
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.FibGlue
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.ExStabU
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle012
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace PI.VolStabS

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW

theorem eq_one_of_pow (z : ℂ) (hz : ‖z‖ = 1) (h : ∀ k : ℕ, 1 / 2 < (z ^ (2 ^ k)).re) : z = 1 := by
  apply PI.VolStabSW.VolAAW.eq_one_of_pow <;> assumption

variable {F : Type} [Field F] [NumberField F]

theorem psiV_nsmul (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) (y : Fv F v) :
    psiV F ψ v (n • y) = psiV F ψ v y ^ n := by
  induction n with
  | zero =>
    simp only [zero_smul, pow_zero, psiV]
    have : pairA F 0 (singleV F v 0) = 0 := by
      have h := singleV_add (F := F) v 0 0
      rw [add_zero] at h
      have h0 : singleV F v 0 = 0 := by
        have := congrArg (fun x => x - singleV F v 0) h
        exact (by simpa using this : (0 : Af F) = singleV F v 0).symm
      rw [h0]
      rfl
    rw [this, AddChar.map_zero_eq_one]
  | succ n ih => rw [succ_nsmul, psiV_add, ih, pow_succ]

theorem ev_triv (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∀ᶠ v in cofinite, ∀ y ∈ v.adicCompletionIntegers F, psiV F ψ v y = 1 := by
  apply PI.VolStabSW.VolAAW.ev_triv <;> assumption

def CondExact : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ᶠ v in cofinite, ∀ t : Fv F v,
      (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (s * t) = 1) → t ∈ v.adicCompletionIntegers F

theorem condAA_of (hE : CondExact) : CondAA := by
  intro F _ _ ψ hψ
  filter_upwards [hE F ψ hψ, ev_triv ψ hψ] with v h1 h2
  intro t
  refine ⟨h1 t, fun ht s hs => h2 _ (mul_mem hs ht)⟩

end VolAAW

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology Set Filter

section Cos

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}

theorem hasDens_zero : HasDens μ f ι ν (fun _ => 0) (fun _ => 0) :=
  ⟨integrable_zero _ _ _, continuous_const, fun S _ => by simp⟩

theorem HasDens.add [IsFiniteMeasureOnCompacts ν] {φ₁ φ₂ : V → ℝ} {g₁ g₂ : X → ℝ}
    (h₁ : HasDens μ f ι ν φ₁ g₁) (h₂ : HasDens μ f ι ν φ₂ g₂) :
    HasDens μ f ι ν (fun v => φ₁ v + φ₂ v) (fun b => g₁ b + g₂ b) := by
  refine ⟨h₁.1.add h₂.1, h₁.2.1.add h₂.2.1, fun S hS => ?_⟩
  rw [integral_add h₁.1.integrableOn h₂.1.integrableOn, h₁.2.2 S hS, h₂.2.2 S hS,
    integral_add (h₁.2.1.continuousOn.integrableOn_compact hS)
      (h₂.2.1.continuousOn.integrableOn_compact hS)]

theorem hasDens_sum [IsFiniteMeasureOnCompacts ν] {κ : Type} (φ : κ → V → ℝ) (g : κ → X → ℝ) :
    ∀ T : Finset κ, (∀ i ∈ T, HasDens μ f ι ν (φ i) (g i)) →
      HasDens μ f ι ν (fun v => ∑ i ∈ T, φ i v) (fun b => ∑ i ∈ T, g i b) := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty => intro _; simpa using (hasDens_zero (μ := μ) (f := f) (ι := ι) (ν := ν))
  | insert i T hi ih =>
    intro h
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

def DensCosB (B : AddSubgroup V → Prop) (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X)
    (U : Set V) : Prop :=
  ∀ x ∈ U, ∃ N ∈ 𝓝 (0 : V), ∀ y, y - x ∈ N → ∀ Λ : AddSubgroup V, B Λ → IsOpen (Λ : Set V) →
    IsCompact (Λ : Set V) → (Λ : Set V) ⊆ N → ∃ g : X → ℝ, Continuous g ∧
      ∀ S : Set X, IsCompact S →
        ∫ v in f ⁻¹' (ι '' S), {z | z - y ∈ Λ}.indicator (fun _ => (1 : ℝ)) v ∂μ =
          ∫ b in S, g b ∂ν


omit [IsTopologicalAddGroup V] in
def IsCOBasis (B : AddSubgroup V → Prop) : Prop :=
  ∀ N ∈ 𝓝 (0 : V), ∃ Λ : AddSubgroup V, B Λ ∧ IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧
    (Λ : Set V) ⊆ N

omit [MeasurableSpace V] [OpensMeasurableSpace V] in
theorem isCompact_cos (Λ : AddSubgroup V) (hΛc : IsCompact (Λ : Set V)) (y : V) :
    IsCompact {z | z - y ∈ Λ} := by
  have : {z | z - y ∈ Λ} = (fun w => w + y) '' (Λ : Set V) := by
    ext z
    constructor
    · intro hz
      exact ⟨z - y, hz, sub_add_cancel z y⟩
    · rintro ⟨w, hw, rfl⟩
      show w + y - y ∈ Λ
      rwa [add_sub_cancel_right]
  rw [this]
  exact hΛc.image (continuous_id.add continuous_const)

theorem integrable_cos [IsFiniteMeasureOnCompacts μ] (Λ : AddSubgroup V)
    (hΛo : IsOpen (Λ : Set V)) (hΛc : IsCompact (Λ : Set V)) (y : V) :
    Integrable ({z | z - y ∈ Λ}.indicator fun _ => (1 : ℝ)) μ := by
  have hm : MeasurableSet {z : V | z - y ∈ Λ} :=
    (hΛo.preimage (continuous_id.sub continuous_const)).measurableSet
  rw [integrable_indicator_iff hm]
  exact integrableOn_const (isCompact_cos Λ hΛc y).measure_lt_top.ne

theorem densLC_of_cosB [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] (U : Set V)
    (B : AddSubgroup V → Prop) (hB : IsCOBasis B) (h : DensCosB B μ f ι ν U) :
    DensOn (IsLCcOn U) μ f ι ν := by
  apply PI.VolStabSW.densLC_of_cosB <;> assumption

end Cos

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS.DiscreteGroups

open MeasureTheory Topology Set Filter PI.VolStabS PI.VolStabS.Glue
open scoped ENNReal

section

variable {V : Type} [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V]
  [SecondCountableTopology V]

theorem cover (U : Set V) (hU : IsOpen U) : ∃ W : ℕ → Set V,
    (∀ n, IsOpen (W n) ∧ IsCompact (closure (W n)) ∧ closure (W n) ⊆ U) ∧ ⋃ n, W n = U := by
  apply PI.VolStabSW.DiscreteGroups.cover <;> assumption

theorem approx (O : Set V) (hO : IsOpen O) : ∃ φ : ℕ → V → ℝ,
    (∀ k, Continuous (φ k) ∧ HasCompactSupport (φ k) ∧ tsupport (φ k) ⊆ O) ∧
    (∀ k x, 0 ≤ φ k x ∧ φ k x ≤ 1) ∧ (∀ x, Monotone fun k => φ k x) ∧
    ∀ x, ⨆ k, ENNReal.ofReal (φ k x) = O.indicator 1 x := by
  apply PI.VolStabSW.DiscreteGroups.approx <;> assumption

variable {X Y : Type} [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
  {μ : Measure V} {ν : Measure X} [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν]
  {f : V → Y} {ι : X → Y} {U : Set V} {fib : X → Measure V}
  (hf : Continuous f) (hι : IsClosedEmbedding ι) (hr : ∀ v, f v ∈ Set.range ι) (hU : IsOpen U)
  (h0 : ∀ b, fib b (f ⁻¹' {ι b} ∩ U)ᶜ = 0) (h2 : ∀ b K, IsCompact K → K ⊆ U → fib b K < ⊤)
  (h3 : ∀ φ : V → ℝ, IsCcOn U φ → (∀ b, Integrable φ (fib b)) ∧
        Continuous (fun b => ∫ v, φ v ∂(fib b)) ∧
        ∀ S : Set X, IsCompact S → ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, ∫ v, φ v ∂(fib b) ∂ν)

include hf hι hr hU h0 h2 h3

theorem cc_case (ψ : V → ℝ) (hψ : IsCcOn U ψ) (h0ψ : ∀ v, 0 ≤ ψ v) :
    ∫⁻ v, ENNReal.ofReal (ψ v) ∂μ = ∫⁻ b, ∫⁻ v, ENNReal.ofReal (ψ v) ∂(fib b) ∂ν := by
  obtain ⟨hint, hcont, hS⟩ := h3 ψ hψ
  set S : Set X := ι ⁻¹' (f '' tsupport ψ) with hSdef
  have hSc : IsCompact S := hι.isCompact_preimage (hψ.2.1.image hf)
  have hsub : tsupport ψ ⊆ f ⁻¹' (ι '' S) := by
    intro v hv
    obtain ⟨s, hs⟩ := hr v
    exact ⟨s, ⟨v, hv, hs.symm⟩, hs⟩
  have hzero : ∀ b ∉ S, ∫ v, ψ v ∂(fib b) = 0 := by
    intro b hb
    apply integral_eq_zero_of_ae
    have hae : ∀ᵐ v ∂(fib b), v ∉ (f ⁻¹' {ι b} ∩ U)ᶜ := measure_eq_zero_iff_ae_notMem.1 (h0 b)
    filter_upwards [hae] with v hv
    simp only [mem_compl_iff, not_not] at hv
    exact (eq_or_ne (ψ v) 0).resolve_right fun hne => hb ⟨v, subset_tsupport _ hne, hv.1⟩
  have e1 : ∫ v in f ⁻¹' (ι '' S), ψ v ∂μ = ∫ v, ψ v ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun v hv =>
      image_eq_zero_of_notMem_tsupport fun h => hv (hsub h)
  have e2 : ∫ b in S, (∫ v, ψ v ∂(fib b)) ∂ν = ∫ b, (∫ v, ψ v ∂(fib b)) ∂ν :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun b hb => hzero b hb
  have hG : Integrable (fun b => ∫ v, ψ v ∂(fib b)) ν :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro' hSc hSc.isClosed hzero)
  have hi : Integrable ψ μ := hψ.1.integrable_of_hasCompactSupport hψ.2.1
  calc ∫⁻ v, ENNReal.ofReal (ψ v) ∂μ = ENNReal.ofReal (∫ v, ψ v ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ h0ψ)).symm
    _ = ENNReal.ofReal (∫ b, (∫ v, ψ v ∂(fib b)) ∂ν) := by rw [← e1, hS S hSc, e2]
    _ = ∫⁻ b, ENNReal.ofReal (∫ v, ψ v ∂(fib b)) ∂ν :=
        ofReal_integral_eq_lintegral_ofReal hG
          (ae_of_all _ fun b => integral_nonneg fun v => h0ψ v)
    _ = ∫⁻ b, ∫⁻ v, ENNReal.ofReal (ψ v) ∂(fib b) ∂ν :=
        lintegral_congr fun b => ofReal_integral_eq_lintegral_ofReal (hint b) (ae_of_all _ h0ψ)

theorem open_case (O : Set V) (hO : IsOpen O) (hOU : O ⊆ U) :
    Measurable (fun b => fib b O) ∧ μ O = ∫⁻ b, fib b O ∂ν := by
  obtain ⟨φ, hφ, h01, hmono, hlim⟩ := approx O hO
  have hcc : ∀ k, IsCcOn U (φ k) := fun k => ⟨(hφ k).1, (hφ k).2.1, (hφ k).2.2.trans hOU⟩
  have hmeas : ∀ k, Measurable fun v => ENNReal.ofReal (φ k v) :=
    fun k => ENNReal.measurable_ofReal.comp (hφ k).1.measurable
  have hmon : Monotone fun k v => ENNReal.ofReal (φ k v) :=
    fun i j hij v => ENNReal.ofReal_le_ofReal (hmono v hij)
  have hfibO : ∀ b, fib b O = ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) := by
    intro b
    rw [← lintegral_iSup hmeas hmon]
    simp_rw [hlim]
    rw [lintegral_indicator_one hO.measurableSet]
  have hk : ∀ k, Measurable fun b => ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) := by
    intro k
    have : (fun b => ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b)) =
        fun b => ENNReal.ofReal (∫ v, φ k v ∂(fib b)) :=
      funext fun b => (ofReal_integral_eq_lintegral_ofReal ((h3 _ (hcc k)).1 b)
        (ae_of_all _ fun v => (h01 k v).1)).symm
    rw [this]
    exact ENNReal.measurable_ofReal.comp (h3 _ (hcc k)).2.1.measurable
  have hmonb : Monotone fun k b => ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) :=
    fun i j hij b => lintegral_mono fun v => ENNReal.ofReal_le_ofReal (hmono v hij)
  refine ⟨?_, ?_⟩
  · simp_rw [hfibO]
    exact Measurable.iSup hk
  · calc μ O = ∫⁻ v, O.indicator 1 v ∂μ := (lintegral_indicator_one hO.measurableSet).symm
      _ = ∫⁻ v, ⨆ k, ENNReal.ofReal (φ k v) ∂μ := by simp_rw [hlim]
      _ = ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂μ := lintegral_iSup hmeas hmon
      _ = ⨆ k, ∫⁻ b, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) ∂ν := by
          congr 1; funext k
          exact cc_case hf hι hr hU h0 h2 h3 (φ k) (hcc k) fun v => (h01 k v).1
      _ = ∫⁻ b, ⨆ k, ∫⁻ v, ENNReal.ofReal (φ k v) ∂(fib b) ∂ν := (lintegral_iSup hk hmonb).symm
      _ = ∫⁻ b, fib b O ∂ν := by simp_rw [hfibO]

theorem null_compl (b : X) : fib b Uᶜ = 0 :=
  measure_mono_null (compl_subset_compl.2 inter_subset_right) (h0 b)

theorem meas_fib : ∀ A, MeasurableSet A → Measurable fun b => fib b A := by
  obtain ⟨W, hW, hWU⟩ := cover U hU
  have hWsub : ∀ n, W n ⊆ U := fun n => subset_closure.trans (hW n).2.2
  have hfin : ∀ b n, fib b (W n) ≠ ⊤ := fun b n =>
    (lt_of_le_of_lt (measure_mono subset_closure) (h2 b _ (hW n).2.1 (hW n).2.2)).ne
  have hP : ∀ n, ∀ A, MeasurableSet A → Measurable fun b => fib b (A ∩ W n) := by
    intro n
    refine MeasurableSpace.induction_on_inter
      (C := fun A _ => Measurable fun b => fib b (A ∩ W n)) (s := {s : Set V | IsOpen s})
      BorelSpace.measurable_eq isPiSystem_isOpen ?_ ?_ ?_ ?_
    · simp only [empty_inter, measure_empty]; exact measurable_const
    · intro t ht
      exact (open_case hf hι hr hU h0 h2 h3 (t ∩ W n) ((ht : IsOpen t).inter (hW n).1)
        (inter_subset_right.trans (hWsub n))).1
    · intro t htm IH
      have e : ∀ b, fib b (tᶜ ∩ W n) = fib b (W n) - fib b (t ∩ W n) := by
        intro b
        rw [← measure_diff inter_subset_right (htm.inter (hW n).1.measurableSet).nullMeasurableSet
          ((measure_mono inter_subset_right).trans_lt (lt_top_iff_ne_top.2 (hfin b n))).ne]
        congr 1
        ext x
        simp only [mem_inter_iff, mem_compl_iff, mem_diff]
        tauto
      simp_rw [e]
      exact (open_case hf hι hr hU h0 h2 h3 (W n) (hW n).1 (hWsub n)).1.sub IH
    · intro g hd hgm IH
      have e : ∀ b, fib b ((⋃ i, g i) ∩ W n) = ∑' i, fib b (g i ∩ W n) := by
        intro b
        rw [iUnion_inter, measure_iUnion (fun i j hij => (hd hij).mono inter_subset_left
          inter_subset_left) (fun i => (hgm i).inter (hW n).1.measurableSet)]
      simp_rw [e]
      exact Measurable.tsum IH
  intro A hA
  have hD : ∀ n, MeasurableSet (disjointed W n) :=
    MeasurableSet.disjointed fun n => (hW n).1.measurableSet
  have e : ∀ b, fib b A = ∑' n, fib b (A ∩ disjointed W n) := by
    intro b
    rw [← measure_inter_add_diff A hU.measurableSet,
      measure_mono_null (show A \ U ⊆ Uᶜ from fun x hx => hx.2) (null_compl hf hι hr hU h0 h2 h3 b),
      add_zero,
      ← hWU, ← iUnion_disjointed, inter_iUnion,
      measure_iUnion (fun i j hij => ((disjoint_disjointed W) hij).mono inter_subset_right
        inter_subset_right) (fun n => hA.inter (hD n))]
  simp_rw [e]
  refine Measurable.tsum fun n => ?_
  have := hP n (A ∩ disjointed W n) (hA.inter (hD n))
  simpa only [inter_eq_left.2 (inter_subset_right.trans (disjointed_subset W n))] using this

end

theorem disintStep_holds : DisintStep := by
  apply PI.VolStabSW.DiscreteGroups.disintStep_holds <;> assumption

theorem fibOfDens_holds : FibOfDens := fibOfDens_of disintStep_holds

end PI.VolStabS.DiscreteGroups
end
end

section

noncomputable section

namespace PI.VolStabS

theorem exStab_of_orb (hO : OrbTup) (hI : NuInv) (hF : NuFin) (hN : NuNeZero) : ExStab :=
  exStab_of_U secCtblW_holds lcscPolish_holds hO hI hF hN

end PI.VolStabS
end
end

section

noncomputable section

namespace PI.VolStabS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology
open scoped TensorProduct

def TensNA : Prop := InCtx fun F E _ _ _ _ _ _σ M _J a _X0 _hT =>
  ∀ v : HeightOneSpectrum (𝓞 F), HasCOSub (Fin a → Fin M → Fv F v ⊗[F] E)

def DensVLC : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    ∀ μv, SdW F E σ M J (Fv F v) (psiV F ψ v) a μv →
    ∀ νv, SdHerm F E σ (Fv F v) (psiV F ψ v) a νv →
      DensOn (IsLCcOn {X | LinearIndependent (Fv F v ⊗[F] E) X}) μv (gramR (Fv F v) σ J)
        Subtype.val νv

theorem densV_of (hT : TensAll) (hNA : TensNA) (hLC : DensVLC) : DensV := by
  intro F E _ _ _ _ _ σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν
  obtain ⟨t1, t2, t3, t4, _t5, _t6, t7⟩ := (hT F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet).2 v
  have := hμ.1
  have := hν.1
  have : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : BorelSpace (HermR (Fv F v) σ a) := ⟨rfl⟩
  have : LocallyCompactSpace (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin a → Fin a → Fv F v ⊗[F] E))
  have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
  have : LocallyCompactSpace (HermR (Fv F v) σ a) :=
    t4.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : IsTopologicalAddGroup (Fv F v ⊗[F] E) :=
    IsModuleTopology.topologicalAddGroup (Fv F v) (Fv F v ⊗[F] E)
  exact (densAll_iff _ _ _ _ _).2 (densApprox_lc μv _ _ νv _ t7
    (hNA F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet v)
    (hLC F E σ hCM M J hJ ha hc a h1 h2 X0 hT0 hdet ψ hψ v μv hμ νv hν))

end PI.VolStabS
end
end
