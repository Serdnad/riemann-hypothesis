module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

section

open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.UnfoldAbs

theorem hasSum_integral_of_norm_bound {A Z : Type} [MeasurableSpace A] (μ : Measure A)
    [IsFiniteMeasure μ] [Countable Z] (G : Z → A → ℂ)
    (hm : ∀ q, AEStronglyMeasurable (G q) μ) (M : ℝ)
    (hb : ∀ b, Summable (fun q => ‖G q b‖) ∧ ∑' q, ‖G q b‖ ≤ M) :
    HasSum (fun q => ∫ b, G q b ∂μ) (∫ b, ∑' q, G q b ∂μ) := by
  have hbd : ∀ q b, ‖G q b‖ ≤ M := fun q b =>
    ((hb b).1.le_tsum q (fun _ _ => norm_nonneg _)).trans (hb b).2
  have hint : ∀ q, Integrable (G q) μ := fun q =>
    Integrable.of_bound (hm q) M (ae_of_all _ (hbd q))
  refine hasSum_integral_of_summable_integral_norm hint ?_
  refine summable_of_sum_le (c := ∫ _, M ∂μ)
    (fun q => integral_nonneg fun _ => norm_nonneg _) ?_
  intro s
  rw [← MeasureTheory.integral_finsetSum s (fun q _ => (hint q).norm)]
  exact integral_mono (MeasureTheory.integrable_finsetSum _ fun q _ => (hint q).norm) (integrable_const _)
    (fun b => ((hb b).1.sum_le_tsum s (fun _ _ => norm_nonneg _)).trans (hb b).2)

theorem setIntegral_eq_zero_of_translate {A : Type} [AddCommGroup A] [MeasurableSpace A]
    [MeasurableAdd A] (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A)
    [Countable Λ] (𝓖 : Set A) (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (Ψ : A → ℂ) (ν : A) (z : ℂ)
    (hz : z ≠ 1) (hΛ : ∀ (l : Λ) b, Ψ ((l : A) + b) = Ψ b) (hν : ∀ b, Ψ (ν + b) = z * Ψ b) :
    ∫ b in 𝓖, Ψ b ∂lam = 0 := by
  have h2 : IsAddFundamentalDomain Λ (ν +ᵥ 𝓖) lam := h𝓖.vadd_of_comm ν
  have e1 : ∫ b in 𝓖, Ψ b ∂lam = ∫ b in (ν +ᵥ 𝓖), Ψ b ∂lam :=
    h𝓖.setIntegral_eq h2 (fun g x => hΛ g x)
  have hpre : (fun x => ν + x) ⁻¹' (ν +ᵥ 𝓖) = 𝓖 := by
    ext x
    simp [Set.mem_vadd_set_iff_neg_vadd_mem]
  have e2 : ∫ b in (ν +ᵥ 𝓖), Ψ b ∂lam = ∫ b in 𝓖, Ψ (ν + b) ∂lam := by
    have := (measurePreserving_add_left lam ν).setIntegral_preimage_emb
      (MeasurableEquiv.addLeft ν).measurableEmbedding Ψ (ν +ᵥ 𝓖)
    rw [hpre] at this
    exact this.symm
  have e3 : ∫ b in 𝓖, Ψ (ν + b) ∂lam = z * ∫ b in 𝓖, Ψ b ∂lam := by
    simp_rw [hν]
    exact integral_const_mul _ _
  have e4 : (1 - z) * ∫ b in 𝓖, Ψ b ∂lam = 0 := by
    have : ∫ b in 𝓖, Ψ b ∂lam = z * ∫ b in 𝓖, Ψ b ∂lam := by rw [← e3, ← e2, ← e1]
    linear_combination this
  exact (mul_eq_zero.mp e4).resolve_left (sub_ne_zero.mpr (Ne.symm hz))

theorem integrable_of_lattice_bound {A : Type} [AddCommGroup A] [MeasurableSpace A]
    [MeasurableAdd A] (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A)
    [Countable Λ] (𝓖 : Set A) (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (h1 : lam 𝓖 = 1)
    (F0 : A → ℂ) (hm : AEStronglyMeasurable F0 lam) (M : ℝ)
    (hb : ∀ b, Summable (fun l : Λ => ‖F0 ((l : A) + b)‖) ∧ ∑' l : Λ, ‖F0 ((l : A) + b)‖ ≤ M) :
    Integrable F0 lam := by
  refine ⟨hm, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have e : ∫⁻ b, ‖F0 b‖ₑ ∂lam = ∑' l : Λ, ∫⁻ b in 𝓖, ‖F0 ((l : A) + b)‖ₑ ∂lam :=
    h𝓖.lintegral_eq_tsum'' _
  have hmeas : ∀ l : Λ, AEMeasurable (fun b => ‖F0 ((l : A) + b)‖ₑ) (lam.restrict 𝓖) := fun l =>
    ((hm.comp_measurePreserving (measurePreserving_add_left lam (l : A))).enorm).restrict
  rw [e, ← lintegral_tsum hmeas]
  calc ∫⁻ b in 𝓖, ∑' l : Λ, ‖F0 ((l : A) + b)‖ₑ ∂lam
      ≤ ∫⁻ _ in 𝓖, ENNReal.ofReal M ∂lam := by
        refine lintegral_mono (fun b => ?_)
        simp_rw [← ofReal_norm_eq_enorm]
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hb b).1]
        exact ENNReal.ofReal_le_ofReal (hb b).2
    _ < ⊤ := by simp [h1]

theorem unfold_abs : ∀ {A X Y : Type} [AddCommGroup A] [MeasurableSpace A] [MeasurableAdd A]
    (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A) [Countable Λ] (𝓖 : Set A)
    (_ : IsAddFundamentalDomain Λ 𝓖 lam) (_ : lam 𝓖 = 1) [Countable X] (c : X → Y) (y0 : Y)
    (F : X → A → ℂ) (F0 : A → ℂ) (ch : A → ℂ) (_ : ∀ q, AEStronglyMeasurable (F q) lam)
    (_ : AEStronglyMeasurable ch lam) (_ : ∀ b, ‖ch b‖ = 1)
    (_ : ∀ a b, ch (a + b) = ch a * ch b) (_ : ∀ l : Λ, ch l = 1) (M : ℝ)
    (_ : ∀ b, Summable (fun q => ‖F q b‖) ∧ ∑' q, ‖F q b‖ ≤ M) (τ : Λ → X ≃ X)
    (_ : ∀ (l : Λ) q b, F q ((l : A) + b) = F (τ l q) b) (_ : ∀ (l : Λ) q, c (τ l q) = c q)
    (e : Λ → X) (_ : Function.Injective e) (_ : ∀ q, c q = y0 ↔ q ∈ Set.range e)
    (_ : ∀ (l : Λ) b, F (e l) b = F0 ((l : A) + b))
    (_ : ∀ y, y ≠ y0 → ∃ ν, ch ν ≠ 1 ∧ ∀ q, c q = y → ∀ b, F q (ν + b) = F q b),
    Integrable F0 lam ∧ ∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam = ∫ b, F0 b * ch b ∂lam := by
  intro A X Y _ _ _ lam _ Λ _ 𝓖 h𝓖 h1 _ c y0 F F0 ch hF hch hnorm hmul hΛ M hb τ hτ hcτ e he hfib
    hF0 hν
  haveI : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by simp [h1]⟩

  have hsub : ∀ {Z : Type} (j : Z → X), Function.Injective j → ∀ b,
      Summable (fun z => ‖F (j z) b‖) ∧ ∑' z, ‖F (j z) b‖ ≤ M := by
    intro Z j hj b
    refine ⟨(hb b).1.comp_injective hj, ?_⟩
    exact (tsum_comp_le_tsum_of_inj (hb b).1 (fun _ => norm_nonneg _) hj).trans (hb b).2
  have key : ∀ {Z : Type} [Countable Z] (j : Z → X), Function.Injective j →
      HasSum (fun z => ∫ b in 𝓖, F (j z) b * ch b ∂lam)
        (∫ b in 𝓖, (∑' z, F (j z) b) * ch b ∂lam) := by
    intro Z _ j hj
    have := hasSum_integral_of_norm_bound (lam.restrict 𝓖) (fun z b => F (j z) b * ch b)
      (fun z => ((hF (j z)).mul hch).restrict) M (fun b => by
        simpa [hnorm] using hsub j hj b)
    simpa only [tsum_mul_right] using this

  have hF0e : F0 = F (e 0) := by
    funext b
    have := hF0 0 b
    simpa using this.symm
  have hint0 : Integrable F0 lam := by
    refine integrable_of_lattice_bound lam Λ 𝓖 h𝓖 h1 F0 (hF0e ▸ hF (e 0)) M (fun b => ?_)
    simpa only [hF0] using hsub e he b
  refine ⟨hint0, ?_⟩

  have hT := key (Z := X) id Function.injective_id
  simp only [id] at hT
  have hsig := (Equiv.sigmaFiberEquiv c).hasSum_iff.mpr hT
  have hg : HasSum (fun y => ∫ b in 𝓖, (∑' z : {x // c x = y}, F z b) * ch b ∂lam)
      (∫ b in 𝓖, (∑' q, F q b) * ch b ∂lam) :=
    hsig.sigma (fun y => key (Z := {x // c x = y}) Subtype.val Subtype.val_injective)

  have hzero : ∀ y, y ≠ y0 → ∫ b in 𝓖, (∑' z : {x // c x = y}, F z b) * ch b ∂lam = 0 := by
    intro y hy
    obtain ⟨ν, hν1, hνq⟩ := hν y hy
    refine setIntegral_eq_zero_of_translate lam Λ 𝓖 h𝓖 _ ν (ch ν) hν1 (fun l b => ?_) (fun b => ?_)
    · have hs : ∑' z : {x // c x = y}, F z ((l : A) + b) = ∑' z : {x // c x = y}, F z b := by
        calc ∑' z : {x // c x = y}, F z ((l : A) + b)
            = ∑' z : {x // c x = y}, F (τ l z) b := tsum_congr fun z => hτ l z b
          _ = ∑' z : {x // c x = y}, F z b :=
            ((τ l).subtypeEquiv (p := fun x => c x = y) (q := fun x => c x = y)
              (fun a => by rw [hcτ])).tsum_eq (fun z : {x // c x = y} => F z b)
      rw [hs, hmul, hΛ, one_mul]
    · have hs : ∑' z : {x // c x = y}, F z (ν + b) = ∑' z : {x // c x = y}, F z b :=
        tsum_congr fun z => hνq z z.2 b
      rw [hs, hmul]
      ring
  have hT' := hg.unique (hasSum_single y0 (fun y hy => hzero y hy))
  rw [hT']

  let ee : Λ ≃ {x // c x = y0} := Equiv.ofBijective
    (fun l => ⟨e l, (hfib _).2 ⟨l, rfl⟩⟩)
    ⟨fun a b h => he (congrArg Subtype.val h), fun q => by
      obtain ⟨l, hl⟩ := (hfib q).1 q.2
      exact ⟨l, Subtype.ext hl⟩⟩
  have hsum : ∀ b, ∑' z : {x // c x = y0}, F z b = ∑' l : Λ, F (e l) b := fun b =>
    (ee.tsum_eq (fun z => F z b)).symm
  simp_rw [hsum]
  rw [← (key e he).tsum_eq]
  have hint1 : Integrable (fun b => F0 b * ch b) lam :=
    hint0.mono (hint0.aestronglyMeasurable.mul hch) (ae_of_all _ fun b => by simp [hnorm])
  rw [h𝓖.integral_eq_tsum'' _ hint1]
  refine tsum_congr fun l => ?_
  refine integral_congr_ae (ae_of_all _ fun b => ?_)
  change F (e l) b * ch b = F0 ((l : A) + b) * ch ((l : A) + b)
  rw [hF0, hmul, hΛ, one_mul]

end GlobalTheory.CompanionTheory.UnfoldAbs
end

section

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.FiberInt

variable {A A' : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A'] [LocallyCompactSpace A']
  [T2Space A'] [SecondCountableTopology A'] [MeasurableSpace A'] [BorelSpace A']

noncomputable def periodized (π : A →+ A') (Γ' : AddSubgroup A') (lam : Measure A) (𝓖 : Set A) :
    Measure A' :=
  Measure.sum fun γ : Γ' => ((lam.restrict 𝓖).map π).map ((γ : A') + ·)

theorem lintegral_periodized {π : A →+ A'} (hπ : Measurable π) {Γ' : AddSubgroup A'} [Countable Γ']
    (lam : Measure A) (𝓖 : Set A) {f : A' → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂(periodized π Γ' lam 𝓖) = ∫⁻ x in 𝓖, ∑' γ : Γ', f ((γ : A') + π x) ∂lam := by
  rw [show periodized π Γ' lam 𝓖 = Measure.sum (fun γ : Γ' => ((lam.restrict 𝓖).map π).map ((γ : A') + ·)) from rfl, lintegral_sum_measure,
    lintegral_tsum]
  · refine tsum_congr fun γ => ?_
    rw [lintegral_map hf (measurable_const_add _), lintegral_map _ hπ]
    exact hf.comp (measurable_const_add _)
  · intro γ
    exact (hf.comp ((measurable_const_add _).comp hπ)).aemeasurable

theorem periodized_invariant {π : A →+ A'} (hπ : Measurable π) {s : A' →+ A}
    (hs : ∀ x, π (s x) = x) {Γ : AddSubgroup A} {Γ' : AddSubgroup A'} [Countable Γ] [Countable Γ']
    (hΓ : ∀ γ ∈ Γ, π γ ∈ Γ') {lam : Measure A} [lam.IsAddHaarMeasure] {𝓖 : Set A}
    (hG : IsAddFundamentalDomain Γ 𝓖 lam) :
    (periodized π Γ' lam 𝓖).IsAddLeftInvariant := by
  constructor
  intro c
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_const_add c),
    lintegral_periodized hπ lam 𝓖 (f := fun y => f (c + y)) (hf.comp (measurable_const_add c)),
    lintegral_periodized hπ lam 𝓖 hf]
  have key : ∀ x : A, ∑' γ : Γ', f (c + ((γ : A') + π x)) = ∑' γ : Γ', f ((γ : A') + π (s c + x)) := by
    intro x
    refine tsum_congr fun γ => ?_
    rw [map_add (f := _), hs]
    congr 1
    abel
  simp_rw [key]
  have hemb : MeasurableEmbedding (fun x : A => s c + x) :=
    (MeasurableEquiv.addLeft (s c)).measurableEmbedding
  rw [(measurePreserving_add_left lam (s c)).setLIntegral_comp_emb hemb
    (fun x => ∑' γ : Γ', f ((γ : A') + π x)) 𝓖]
  have hG' : IsAddFundamentalDomain Γ ((fun x : A => s c + x) '' 𝓖) lam := hG.vadd_of_comm (s c)
  refine hG'.setLIntegral_eq hG _ ?_
  intro g x
  show ∑' γ : Γ', f ((γ : A') + π ((g : A) + x)) = ∑' γ : Γ', f ((γ : A') + π x)
  rw [← (Equiv.addRight (⟨π g, hΓ g g.2⟩ : Γ')).tsum_eq (fun γ : Γ' => f ((γ : A') + π x))]
  refine tsum_congr fun γ => ?_
  simp only [Equiv.coe_addRight, AddSubgroup.coe_add, map_add (f := _), add_assoc]

instance {π : A →+ A'} {Γ' : AddSubgroup A'} [Countable Γ'] {lam : Measure A} [SFinite lam]
    {𝓖 : Set A} : SFinite (periodized π Γ' lam 𝓖) := by
  unfold periodized; infer_instance

theorem measure_preimage_inter_eq {π : A →+ A'} (hπ : Measurable π) {s : A' →+ A}
    (hs : ∀ x, π (s x) = x) {Γ : AddSubgroup A} {Γ' : AddSubgroup A'} [Countable Γ] [Countable Γ']
    (hΓ : ∀ γ ∈ Γ, π γ ∈ Γ') {lam : Measure A} {lam' : Measure A'} [lam.IsAddHaarMeasure]
    [lam'.IsAddHaarMeasure] {𝓖 : Set A} {𝓖' : Set A'}
    (hG : IsAddFundamentalDomain Γ 𝓖 lam) (h1 : lam 𝓖 = 1)
    (hG' : IsAddFundamentalDomain Γ' 𝓖' lam') (h1' : lam' 𝓖' = 1)
    {S : Set A'} (hS : MeasurableSet S) (hinv : ∀ γ ∈ Γ', ∀ x, γ + x ∈ S ↔ x ∈ S) :
    lam (π ⁻¹' S ∩ 𝓖) = lam' (S ∩ 𝓖') := by
  obtain ⟨P, hPdef⟩ : ∃ P, P = periodized π Γ' lam 𝓖 := ⟨_, rfl⟩
  obtain ⟨ν, hνdef⟩ : ∃ ν, ν = Measure.map π (lam.restrict 𝓖) := ⟨_, rfl⟩
  have hPsum : P = Measure.sum fun γ : Γ' => ν.map ((γ : A') + ·) := by rw [hPdef, hνdef]; rfl
  have : P.IsAddLeftInvariant := by rw [hPdef]; exact periodized_invariant hπ hs hΓ hG
  have : SFinite P := by rw [hPdef]; infer_instance
  have : lam'.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure lam'
  have : lam'.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular lam'
  obtain ⟨M, hMdef⟩ : ∃ M, M = toMeasurable lam' 𝓖' := ⟨_, rfl⟩
  have hMm : MeasurableSet M := by rw [hMdef]; exact measurableSet_toMeasurable lam' 𝓖'
  have hMae : M =ᵐ[lam'] 𝓖' := by rw [hMdef]; exact hG'.nullMeasurableSet.toMeasurable_ae_eq
  have hM1 : lam' M = 1 := by rw [hMdef, measure_toMeasurable, h1']
  have hne : lam' ≠ 0 := fun h => by simp [h] at h1'
  have hPac : P ≪ lam' := absolutelyContinuous_of_isAddLeftInvariant P lam' hne
  have hνP : ν ≤ P := by
    have h0 := Measure.le_sum (fun γ : Γ' => Measure.map (fun y : A' => (γ : A') + y) ν) 0
    simp only [AddSubgroup.coe_zero, zero_add, Measure.map_id'] at h0
    rw [hPsum]
    exact h0
  have hνac : ν ≪ lam' := by
    intro t ht
    exact le_antisymm ((Measure.le_iff'.1 hνP t).trans (hPac ht).le) zero_le
  have claim : ∀ T : Set A', MeasurableSet T → (∀ γ ∈ Γ', ∀ x, γ + x ∈ T ↔ x ∈ T) →
      lam (π ⁻¹' T ∩ 𝓖) = P (T ∩ M) := by
    intro T hT hTinv
    have e1 : lam (π ⁻¹' T ∩ 𝓖) = ν T := by
      rw [hνdef, Measure.map_apply hπ hT, Measure.restrict_apply (hπ hT)]
    rw [e1, hG'.measure_eq_tsum_of_ac hνac T, hPsum, Measure.sum_apply _ (hT.inter hMm)]
    conv_lhs => rw [← (Equiv.neg Γ').tsum_eq]
    refine tsum_congr fun γ => ?_
    rw [Measure.map_apply (measurable_const_add _) (hT.inter hMm)]
    have hpre : (fun x => (γ : A') + x) ⁻¹' (T ∩ M) = T ∩ (fun x => (γ : A') + x) ⁻¹' M := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, hTinv γ γ.2 x]
    have hset : (fun x => (γ : A') + x) ⁻¹' 𝓖' = (Equiv.neg Γ') γ +ᵥ 𝓖' := by
      ext x
      rw [Set.mem_preimage, Set.mem_vadd_set_iff_neg_vadd_mem]
      simp [AddSubgroup.vadd_def]
    have hae : (fun x => (γ : A') + x) ⁻¹' M =ᵐ[lam'] (fun x => (γ : A') + x) ⁻¹' 𝓖' :=
      (measurePreserving_add_left lam' (γ : A')).quasiMeasurePreserving.preimage_ae_eq hMae
    rw [hpre, ← hset]
    exact measure_congr (.inter .rfl (hae.filter_mono hνac.ae_le).symm)
  have hPt : ∀ t, MeasurableSet t → P t = P M * lam' t := by
    intro t ht
    have h := measure_add_lintegral_eq lam' P hMm (t.indicator 1) (measurable_one.indicator ht)
    rw [hM1, one_mul, lintegral_indicator_one ht] at h
    rw [h]
    have hc : ∀ x : A', P ((fun z => z + x) ⁻¹' M) = P M := fun x => by
      simp_rw [add_comm _ x]
      exact measure_preimage_add P x M
    simp_rw [hc]
    rw [lintegral_const_mul (P M) (f := fun x => t.indicator 1 (-x))
      ((measurable_one.indicator ht).comp measurable_neg),
      lintegral_neg_eq_self (t.indicator 1), lintegral_indicator_one ht]
  have hU := claim Set.univ MeasurableSet.univ (fun _ _ _ => by simp)
  rw [Set.preimage_univ, Set.univ_inter, h1, Set.univ_inter] at hU
  rw [claim S hS hinv, hPt _ (hS.inter hMm), ← hU, one_mul]
  exact measure_congr (.inter .rfl hMae)

theorem integral_comp_eq : ∀ {A A' : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [LocallyCompactSpace A] [T2Space A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A'] [LocallyCompactSpace A'] [T2Space A'] [SecondCountableTopology A'] [MeasurableSpace A'] [BorelSpace A'] (π : A →+ A') (s : A' →+ A), Continuous π → Continuous s → (∀ x, π (s x) = x) → ∀ (Γ : AddSubgroup A) (Γ' : AddSubgroup A'), Countable Γ → Countable Γ' → (∀ γ ∈ Γ, π γ ∈ Γ') → (∀ γ ∈ Γ', s γ ∈ Γ) → ∀ (lam : Measure A) (lam' : Measure A'), lam.IsAddHaarMeasure → lam'.IsAddHaarMeasure → ∀ (𝓖 : Set A) (𝓖' : Set A'), IsAddFundamentalDomain Γ 𝓖 lam → lam 𝓖 = 1 → IsAddFundamentalDomain Γ' 𝓖' lam' → lam' 𝓖' = 1 → ∀ G : A' → ℂ, Continuous G → (∀ γ ∈ Γ', ∀ x, G (γ + x) = G x) → ∫ x in 𝓖, G (π x) ∂lam = ∫ x in 𝓖', G x ∂lam' := by
  intro A A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ π s hπc _ hs Γ Γ' hΓc hΓ'c hΓ _ lam lam' hlam hlam' 𝓖 𝓖' hG h1 hG' h1' G hGc hGinv
  have := hΓc
  have := hΓ'c
  have := hlam
  have := hlam'
  have hπ : Measurable π := hπc.measurable
  have hGm : Measurable G := hGc.measurable
  have key : Measure.map G (Measure.map π (lam.restrict 𝓖)) = Measure.map G (lam'.restrict 𝓖') := by
    ext B hB
    have hinvB : ∀ γ ∈ Γ', ∀ x, γ + x ∈ G ⁻¹' B ↔ x ∈ G ⁻¹' B := fun γ hγ x => by
      simp only [Set.mem_preimage, hGinv γ hγ x]
    rw [Measure.map_apply hGm hB, Measure.map_apply hGm hB, Measure.map_apply hπ (hGm hB),
      Measure.restrict_apply (hπ (hGm hB)), Measure.restrict_apply (hGm hB)]
    exact measure_preimage_inter_eq hπ hs hΓ hG h1 hG' h1' (hGm hB) hinvB
  calc ∫ x in 𝓖, G (π x) ∂lam = ∫ y, G y ∂(Measure.map π (lam.restrict 𝓖)) :=
        (integral_map hπ.aemeasurable hGc.aestronglyMeasurable).symm
    _ = ∫ z, z ∂(Measure.map G (Measure.map π (lam.restrict 𝓖))) :=
        (integral_map hGm.aemeasurable aestronglyMeasurable_id).symm
    _ = ∫ z, z ∂(Measure.map G (lam'.restrict 𝓖')) := by rw [key]
    _ = ∫ x in 𝓖', G x ∂lam' := integral_map hGm.aemeasurable aestronglyMeasurable_id

end GlobalTheory.CompanionTheory.FiberInt
end

section

open scoped Matrix
open MeasureTheory

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

def PosOn {n : ℕ} (ε : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) (S : Submodule ℂ (Fin n → ℂ)) : Prop :=
  ∀ w ∈ S, w ≠ 0 → 0 < ε * (star w ⬝ᵥ Z.mulVec w).re

def NonnegOn {n : ℕ} (ε : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) (S : Submodule ℂ (Fin n → ℂ)) : Prop :=
  ∀ w ∈ S, 0 ≤ ε * (star w ⬝ᵥ Z.mulVec w).re

theorem integrable_of_mul_unimodular {α : Type} [MeasurableSpace α] (μ : Measure α) (a b : α → ℂ)
    (hi : Integrable (fun x => a x * b x) μ) (hb : AEStronglyMeasurable b μ) (hb1 : ∀ x, ‖b x‖ = 1) :
    Integrable a μ := by
  have hfun : a = fun x => (a x * b x) * star (b x) := by
    funext x
    rw [mul_assoc, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hb1]
    simp
  have hmeas : AEStronglyMeasurable a μ := by
    rw [hfun]
    exact hi.1.mul hb.star
  refine hi.mono hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, hb1, mul_one]

theorem vanish_abs {X : Type} [TopologicalSpace X] [FirstCountableTopology X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure] (e : X → X → ℂ)
    (he : ∀ z, Continuous fun v => e v z) (he' : ∀ v, Continuous fun z => e v z)
    (hen : ∀ a b, ‖e a b‖ = 1) (J : X → ℂ) (hJ : Integrable J μ) (N : Set X) (hN : IsOpen N)
    (hb : ∀ N' : Set X, IsOpen N' → N' ⊆ N → ∀ z₁ ∈ N', ∃ Φ : X → ℂ, Continuous Φ ∧ Integrable Φ μ ∧
      (∀ z, 0 ≤ (Φ z).re ∧ (Φ z).im = 0) ∧ (∀ z, z ∉ N' → Φ z = 0) ∧ 0 < (Φ z₁).re ∧
      ∫ z, (∫ v, J v * e v z ∂μ) * Φ z ∂μ = 0) (z₀ : X) (hz : z₀ ∈ closure N) :
    ∫ v, J v * e v z₀ ∂μ = 0 := by
  have hbd : ∀ z, ‖∫ v, J v * e v z ∂μ‖ ≤ ∫ v, ‖J v‖ ∂μ := by
    intro z
    calc ‖∫ v, J v * e v z ∂μ‖ ≤ ∫ v, ‖J v * e v z‖ ∂μ := norm_integral_le_integral_norm _
      _ = ∫ v, ‖J v‖ ∂μ := by
        congr 1
        ext v
        rw [norm_mul, hen, mul_one]
  have hFc : Continuous fun z => ∫ v, J v * e v z ∂μ := by
    refine continuous_of_dominated (F := fun z v => J v * e v z) (bound := fun v => ‖J v‖)
      (fun z => hJ.1.mul (he z).aestronglyMeasurable) (fun z => Filter.Eventually.of_forall
        fun v => by rw [norm_mul, hen, mul_one]) hJ.norm
      (Filter.Eventually.of_forall fun v => continuous_const.mul (he' v))
  set F : X → ℂ := fun z => ∫ v, J v * e v z ∂μ with hFdef
  have hzero : ∀ z₁ ∈ N, F z₁ = 0 := by
    intro z₁ hz₁
    by_contra hc
    set c := F z₁ with hcdef
    let G : X → ℝ := fun z => (starRingEnd ℂ c * F z).re
    have hGc : Continuous G := Complex.continuous_re.comp (continuous_const.mul hFc)
    have hG1 : 0 < G z₁ := by
      show 0 < (starRingEnd ℂ c * c).re
      rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
      exact Complex.normSq_pos.mpr hc
    have hN'o : IsOpen (N ∩ {z | 0 < G z}) := hN.inter (isOpen_lt continuous_const hGc)
    obtain ⟨Φ, hΦc, hΦi, hΦpos, hΦsupp, hΦ1, hint⟩ :=
      hb _ hN'o Set.inter_subset_left z₁ ⟨hz₁, hG1⟩
    have hint' : ∫ z, F z * Φ z ∂μ = 0 := hint
    have hFΦi : Integrable (fun z => F z * Φ z) μ := by
      refine Integrable.mono (hΦi.norm.const_mul (∫ v, ‖J v‖ ∂μ))
        (hFc.aestronglyMeasurable.mul hΦi.1) (Filter.Eventually.of_forall fun z => ?_)
      rw [norm_mul, Real.norm_eq_abs, abs_mul, abs_norm,
        abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact mul_le_mul_of_nonneg_right (hbd z) (norm_nonneg _)
    let H : X → ℝ := fun z => (starRingEnd ℂ c * (F z * Φ z)).re
    have hHeq : ∀ z, H z = G z * (Φ z).re := by
      intro z
      simp only [H, G]
      rw [← mul_assoc, Complex.mul_re, (hΦpos z).2, mul_zero, sub_zero]
    have hHnn : ∀ z, 0 ≤ H z := by
      intro z
      rw [hHeq]
      by_cases hz : z ∈ N ∩ {z | 0 < G z}
      · exact mul_nonneg hz.2.le (hΦpos z).1
      · rw [hΦsupp z hz]
        simp
    have hHc : Continuous H := Complex.continuous_re.comp (continuous_const.mul (hFc.mul hΦc))
    have hHi : Integrable H μ := (hFΦi.const_mul (starRingEnd ℂ c)).re
    have hHpos : 0 < ∫ z, H z ∂μ := by
      rw [integral_pos_iff_support_of_nonneg (fun z => hHnn z) hHi]
      apply hHc.isOpen_support.measure_pos μ
      refine ⟨z₁, ?_⟩
      rw [Function.mem_support, hHeq]
      exact (mul_pos hG1 hΦ1).ne'
    have hHzero : ∫ z, H z ∂μ = 0 := by
      have h : ∫ z, H z ∂μ = (∫ z, starRingEnd ℂ c * (F z * Φ z) ∂μ).re :=
        integral_re (hFΦi.const_mul _)
      rw [h, integral_const_mul, hint', mul_zero, Complex.zero_re]
    linarith
  exact closure_minimal (s := N) (t := {z | F z = 0})
    (fun z hz => hzero z hz) (isClosed_eq hFc continuous_const) hz

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
end
end

section

open Matrix Topology Filter

namespace GlobalTheory.CompanionTheory.Unitary.ExpUpper


open scoped Matrix.Norms.L2Operator in
theorem blockTriangular_exp {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : T.BlockTriangular id) : (NormedSpace.exp T).BlockTriangular id := by
  have hmem : ∀ k : ℕ, ((k.factorial : ℂ)⁻¹ • T ^ k) ∈ Matrix.blockTriangularSubalgebra ℂ ℂ id := fun k =>
    Subalgebra.smul_mem _ (Subalgebra.pow_mem _ ((Matrix.mem_blockTriangularSubalgebra).mpr hT) k) _

  refine (isClosed_setOfPred_blockTriangular (b := id)).mem_of_tendsto
    (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) (x := T)) (Filter.Eventually.of_forall fun s => ?_)
  exact (Matrix.mem_blockTriangularSubalgebra).mp (Subalgebra.sum_mem _ fun k _ => hmem k)

theorem blockTriangular_conj_exp {n : ℕ} (U Y : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (h : (Uᴴ * Y * U).BlockTriangular id) :
    (Uᴴ * NormedSpace.exp Y * U).BlockTriangular id := by
  have hUU : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hUU' : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have hunit : IsUnit U := ⟨⟨U, Uᴴ, hUU', hUU⟩, rfl⟩
  have hinv : U⁻¹ = Uᴴ := Matrix.inv_eq_left_inv hUU
  rw [← hinv, ← Matrix.exp_conj' U Y hunit]
  exact GlobalTheory.CompanionTheory.Unitary.ExpUpper.blockTriangular_exp _ (hinv ▸ h)

end GlobalTheory.CompanionTheory.Unitary.ExpUpper
end
