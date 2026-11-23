module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle334
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle322
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle326
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle357
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsQuotHeightMulExpInfLe
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle344
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.XiAtPenultimateEqXiCpl1
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle369
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle353
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelJCharacterEqMemberOffPlaces
public import Formalism.LocalToGlobal.KernelLattices.Bundle004
public import Formalism.LocalToGlobal.KernelLattices.Bundle003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle367
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle370
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

theorem IsKerSys.mul_decay_le {D : D7} {θ : InfF D} {V W : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M]
    {κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)} (hκ : IsKerSys θ V W κ) {F : GA D V → ℂ} (hF : IsRapidDecay θ V F) :
    ∃ N : ℕ, ∀ f, ∃ C : ℝ, 0 ≤ C ∧ ∀ g h, ‖κ f g h * F g‖ ≤ C * (height θ W h : ℝ) ^ N := by
  obtain ⟨N, hN⟩ := hκ.growth
  obtain ⟨C', hC'⟩ := hF N
  refine ⟨N, fun f => ?_⟩
  obtain ⟨C, hC⟩ := hN f
  refine ⟨|C| * 2 ^ N * |C'|, by positivity, fun g h => ?_⟩
  obtain ⟨γ, hγ, hle⟩ := exists_height_le (θ := θ) g
  have h1 : (height θ V (γ * g) : ℝ) ≤ 2 * (quotHeight θ V g : ℝ) := by exact_mod_cast hle
  have h2 : ‖κ f g h‖ ≤ |C| * (2 * (quotHeight θ V g : ℝ) * (height θ W h : ℝ)) ^ N := by
    have := hκ.left f γ hγ 1 (one_mem _) g h
    rw [one_mul] at this
    rw [← this]
    exact (hC _ _).trans (mul_le_mul (le_abs_self _)
      (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h1 (NNReal.coe_nonneg _)) N)
      (by positivity) (abs_nonneg _))
  calc ‖κ f g h * F g‖ = ‖κ f g h‖ * ‖F g‖ := norm_mul _ _
    _ ≤ |C| * (2 * (quotHeight θ V g : ℝ) * (height θ W h : ℝ)) ^ N * ‖F g‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = |C| * 2 ^ N * (‖F g‖ * (quotHeight θ V g : ℝ) ^ N) * (height θ W h : ℝ) ^ N := by
        rw [mul_pow, mul_pow]; ring
    _ ≤ |C| * 2 ^ N * |C'| * (height θ W h : ℝ) ^ N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((hC' g).trans (le_abs_self _)) (by positivity))
          (by positivity)

theorem lift_conv_cont_growth_deriv : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)), IsKerSys θ V W κ → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ F ∈ Decay θ V, (∀ f h, IntegrableOn (fun g => κ f g h * F g) 𝓕 μ) ∧ (∀ f, Continuous fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) ∧ (∃ N : ℕ, ∀ f, ∃ C : ℝ, ∀ h, ‖∫ g in 𝓕, κ f g h * F g ∂μ‖ ≤ C * (height θ W h : ℝ) ^ N) ∧ ∀ τ, ∀ X ∈ lieAt W τ, ∀ f f', (∀ g h, HasDerivAt (fun t : ℝ => κ f g (h * oneP θ W τ X t)) (κ f' g h) 0) → ∀ h, HasDerivAt (fun t : ℝ => ∫ g in 𝓕, κ f g (h * oneP θ W τ X t) * F g ∂μ) (∫ g in 𝓕, κ f' g h * F g ∂μ) 0 := by
  intro D θ hθ V W M _ _ κ hκ μ 𝓕 hQ F hF
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : SecondCountableTopology (GA D V) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  have : SecondCountableTopology (GA D W) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W).2.1
  have : IsTopologicalGroup (GA D W) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W).2.2.2.2.1
  have hfin : μ 𝓕 ≠ ⊤ := (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V μ 𝓕 hQ).2
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin
  obtain ⟨hc, hd⟩ : Continuous F ∧ IsRapidDecay θ V F := hF.2.2 [] (by simp)
  obtain ⟨N, hN⟩ := hκ.mul_decay_le hd
  have hm : ∀ f h, AEStronglyMeasurable (fun g => κ f g h * F g) (μ.restrict 𝓕) := fun f h =>
    (((hκ.cont f).comp (Continuous.prodMk_left h)).mul hc).aestronglyMeasurable
  have hint : ∀ f h, IntegrableOn (fun g => κ f g h * F g) 𝓕 μ := fun f h => by
    obtain ⟨C, -, hC⟩ := hN f
    exact Measure.integrableOn_of_bounded hfin
      (((hκ.cont f).comp (Continuous.prodMk_left h)).mul hc).aestronglyMeasurable (.of_forall fun g => hC g h)
  have hloc : ∀ f h₀, ∃ B : ℝ, ∀ᶠ h in 𝓝 h₀, ∀ g, ‖κ f g h * F g‖ ≤ B := fun f h₀ => by
    obtain ⟨C, h0, hC⟩ := hN f
    obtain ⟨B, hB⟩ := GlobalTheory.Mem.LiftHeight.height_locally_bounded D θ hθ W h₀
    exact ⟨C * B ^ N, hB.mono fun h hh g => (hC g h).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) hh N) h0)⟩
  refine ⟨hint, fun f => continuous_iff_continuousAt.2 fun h₀ => ?_, ⟨N, fun f => ?_⟩, fun τ X hX f f' hder h => ?_⟩
  · obtain ⟨B, hB⟩ := hloc f h₀
    exact continuousAt_of_dominated (bound := fun _ => B) (.of_forall (hm f)) (hB.mono fun h hh => .of_forall hh)
      (integrable_const B) (.of_forall fun g =>
        (((hκ.cont f).comp (Continuous.prodMk_right g)).mul continuous_const).continuousAt)
  · obtain ⟨C, -, hC⟩ := hN f
    refine ⟨C * (μ.restrict 𝓕).real Set.univ, fun h => ?_⟩
    refine (norm_integral_le_of_norm_le_const (.of_forall fun g => hC g h)).trans_eq ?_
    ring
  · obtain ⟨B, hB⟩ := hloc f' h
    have hco : Filter.Tendsto (fun t : ℝ => h * oneP θ W τ X t) (𝓝 0) (𝓝 h) := by
      have := (continuous_const (y := h).mul (continuous_oneP hθ hX)).tendsto 0
      rw [Pi.mul_apply, oneP_zero hθ, mul_one] at this
      exact this
    have := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (x₀ := (0 : ℝ))
      (F := fun t g => κ f g (h * oneP θ W τ X t) * F g) (F' := fun t g => κ f' g (h * oneP θ W τ X t) * F g)
      (bound := fun _ => B) (hco.eventually hB) (.of_forall fun t => hm f _) (hint f _) (hm f' _)
      (.of_forall fun g t ht => ht g) (integrable_const B)
      (.of_forall fun g t _ => (hasDerivAt_oneP hθ hX (φ := κ f g) (φ' := κ f' g) (hder g) h t).mul_const (F g))).2
    simpa only [oneP_zero hθ, mul_one] using this

end GlobalTheory.Mem.Lift

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.IntByParts

theorem setIntegral_mul_right {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    {Φ : G → ℂ} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (a : G) :
    ∫ g in 𝓕, Φ (g * a) ∂μ = ∫ g in 𝓕, Φ g ∂μ := by
  have hm : MeasurePreserving (fun g : G => g * a) μ μ := measurePreserving_mul_right μ a
  have h' : IsFundamentalDomain Γ ((fun g : G => g * a) ⁻¹' 𝓕) μ :=
    h.preimage_of_equiv hm.quasiMeasurePreserving Function.bijective_id fun γ g => mul_assoc _ _ _
  rw [← hm.setIntegral_preimage_emb (measurableEmbedding_mulRight a) Φ 𝓕]
  exact h.setIntegral_eq h' (f := fun g => Φ (g * a)) fun γ g => by
    change Φ ((γ : G) * g * a) = _
    rw [mul_assoc, hΦ _ γ.2]

theorem setIntegral_deriv_eq_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (Γ : Subgroup G) [Countable Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {𝓕 : Set G} (h : IsFundamentalDomain Γ 𝓕 μ)
    (hfin : μ 𝓕 ≠ ⊤) {Φ Φ' : G → ℂ} (hΦ : ∀ γ ∈ Γ, ∀ g, Φ (γ * g) = Φ g) (hc : Continuous Φ) (hc' : Continuous Φ')
    {B B' : ℝ} (hB : ∀ g, ‖Φ g‖ ≤ B) (hB' : ∀ g, ‖Φ' g‖ ≤ B') {a : ℝ → G} (h0 : a 0 = 1)
    (hd : ∀ g t, HasDerivAt (fun s : ℝ => Φ (g * a s)) (Φ' (g * a t)) t) : ∫ g in 𝓕, Φ' g ∂μ = 0 := by
  haveI : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (𝕜 := ℝ) (x₀ := 0)
    (F := fun t g => Φ (g * a t)) (F' := fun t g => Φ' (g * a t)) (s := Set.univ) (bound := fun _ => B')
    Filter.univ_mem
    (.of_forall fun t => (hc.comp (continuous_mul_const _)).measurable.aestronglyMeasurable)
    (Integrable.of_bound (hc.comp (continuous_mul_const _)).measurable.aestronglyMeasurable B
      (.of_forall fun g => hB _))
    (hc'.comp (continuous_mul_const _)).measurable.aestronglyMeasurable
    (.of_forall fun g t _ => hB' _) (integrable_const _) (.of_forall fun g t _ => hd g t)
  have h2 := key.2
  simp only [setIntegral_mul_right Γ μ h hΦ, h0, mul_one] at h2
  exact h2.unique (hasDerivAt_const _ _)

variable {D : D7} {θ : InfF D} {V : HSp D}

theorem mul_cont_bounded {φ F : GA D V → ℂ} (hφ : IsMod θ V φ) (hF : F ∈ Decay θ V) :
    Continuous (fun g => φ g * F g) ∧ ∃ B : ℝ, ∀ g, ‖φ g * F g‖ ≤ B := by
  obtain ⟨c1, N, C, hC⟩ := hφ.2.2 [] (by simp)
  obtain ⟨c2, hr⟩ := hF.2.2 [] (by simp)
  obtain ⟨B, hB⟩ := IsRapidDecay.mul_bounded (φ := F) (ψ := φ) hr hφ.2.1 hC
  exact ⟨Continuous.mul c1 c2, B, fun g => by rw [norm_mul]; exact hB g⟩

theorem integral_Rder_mul : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ τ, ∀ X ∈ lieAt V τ, ∀ φ F, IsMod θ V φ → F ∈ Decay θ V → IntegrableOn (fun g => φ g * F g) 𝓕 μ ∧ ∫ g in 𝓕, Rder θ V τ X φ g * F g ∂μ = -∫ g in 𝓕, φ g * Rder θ V τ X F g ∂μ := by
  intro D θ hθ V μ 𝓕 hq τ X hX φ F hφ hF
  obtain ⟨-, -, -, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hfin := (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V μ 𝓕 hq).2
  haveI := hq.1
  haveI := (GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hq.1).1
  have int : ∀ {φ F : GA D V → ℂ}, IsMod θ V φ → F ∈ Decay θ V → IntegrableOn (fun g => φ g * F g) 𝓕 μ := by
    intro φ F hφ hF
    obtain ⟨c, B, hB⟩ := mul_cont_bounded hφ hF
    exact Measure.integrableOn_of_bounded (M := B) hfin c.measurable.aestronglyMeasurable (.of_forall hB)
  refine ⟨int hφ hF, ?_⟩
  obtain ⟨c0, B0, hB0⟩ := mul_cont_bounded hφ hF
  obtain ⟨c1, B1, hB1⟩ := mul_cont_bounded (hφ.rder hX) hF
  obtain ⟨c2, B2, hB2⟩ := mul_cont_bounded hφ (Rder_mem_Decay hF hX)
  have key := setIntegral_deriv_eq_zero (GQ V) μ hq.2 hfin (Φ := fun g => φ g * F g)
    (Φ' := fun g => Rder θ V τ X φ g * F g + φ g * Rder θ V τ X F g)
    (fun γ hγ g => by simp only [hφ.2.1 γ hγ, hF.2.1 γ hγ]) c0 (c1.add c2) hB0
    (fun g => (norm_add_le _ _).trans (add_le_add (hB1 g) (hB2 g))) (oneP_zero (V := V) (τ := τ) (X := X) hθ)
    fun g t => (hasDerivAt_oneP hθ hX (hasDerivAt_Rder hφ.1 hX) g t).mul
      (hasDerivAt_oneP hθ hX (hasDerivAt_Rder hF.1 hX) g t)
  rw [integral_add (int (hφ.rder hX) hF) (int hφ (Rder_mem_Decay hF hX))] at key
  exact eq_neg_of_add_eq_zero_left key

end GlobalTheory.Mem.IntByParts

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.CuspDeriv

theorem continuous_deriv_of_bounded {G : Type} [TopologicalSpace G] {f f₁ f₂ : G → ℝ → ℂ}
    (hf : ∀ t, Continuous fun g => f g t) (h₁ : ∀ g t, HasDerivAt (f g) (f₁ g t) t)
    (h₂ : ∀ g t, HasDerivAt (f₁ g) (f₂ g t) t) {B : ℝ} (hB : ∀ g t, ‖f₂ g t‖ ≤ B) : Continuous fun g => f₁ g 0 := by
  refine continuous_iff_continuousAt.2 fun g₀ => Metric.tendsto_nhds.2 fun ε hε => ?_
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB g₀ 0)
  obtain ⟨h, h0, hh⟩ : ∃ h : ℝ, 0 < h ∧ (B + B) * h < ε :=
    ⟨ε / (B + B + 1), by positivity, by rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]; linarith⟩
  have hc : Continuous fun g => ‖f g h - f g₀ h‖ + ‖f g 0 - f g₀ 0‖ + (B + B) * h * h :=
    ((((hf h).sub continuous_const).norm).add ((hf 0).sub continuous_const).norm).add continuous_const
  have := (hc.tendsto g₀).eventually_lt_const (u := h * ε) (by simp only [sub_self, norm_zero, zero_add]; nlinarith)
  filter_upwards [this] with g hg
  have key := mul_norm_deriv_le (f := fun t => f g t - f g₀ t) (f₁ := fun t => f₁ g t - f₁ g₀ t)
    (f₂ := fun t => f₂ g t - f₂ g₀ t) (fun t => (h₁ g t).sub (h₁ g₀ t)) (fun t => (h₂ g t).sub (h₂ g₀ t)) h0.le
    (B := B + B) fun t _ => (norm_sub_le _ _).trans (add_le_add (hB g t) (hB g₀ t))
  rw [dist_eq_norm]
  exact lt_of_mul_lt_mul_left (key.trans_lt hg) h0.le

theorem cuspForm_mem_decay : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D), ∀ F,
    IsCuspForm θ V F → F ∈ Decay θ V := by
  intro hP D θ hθ V F ⟨ha, hc⟩
  have : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hd : ∀ l, (∀ p ∈ l, p.2 ∈ lieAt V p.1) → IsRapidDecay θ V (word θ V l F) :=
    isRapidDecay_foldr_Rder hP hθ ha.toIsAutFun ha.smooth ha.growth hc
  refine ⟨ha.smooth, ha.left, fun l hl => ⟨?_, hd l hl⟩⟩
  induction l with
  | nil => exact ha.cont
  | cons p l ih =>
    have hp := hl p (by simp)
    have hl' : ∀ q ∈ l, q.2 ∈ lieAt V q.1 := fun q hq => hl q (by simp [hq])
    have hs : word θ V l F ∈ SmFun θ V :=
      (linOnSm_foldr (θ := θ) (fun p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ => Rder θ V p.1 p.2) l
        fun q hq => linOnSm_Rder (hl' q hq)).mem F ha.smooth
    obtain ⟨B, hB⟩ := (hd (p :: p :: l) (List.forall_mem_cons.2 ⟨hp, hl⟩)).bounded
    have := continuous_deriv_of_bounded (f := fun g t => word θ V l F (g * oneP θ V p.1 p.2 t))
      (fun t => (ih hl').comp (continuous_mul_const _)) (hasDerivAt_oneP hθ hp (hasDerivAt_Rder hs hp))
      (hasDerivAt_oneP hθ hp (hasDerivAt_Rder (Rder_mem hs hp) hp)) fun g t => hB _
    simp only [oneP_zero hθ, mul_one] at this
    exact this

end GlobalTheory.Mem.CuspDeriv

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

theorem _root_.GlobalTheory.T.exists_couplingCoset_with_given_reduction : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, QE sel (mu : Chr X.F X.E X.K) = ∅ → (∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2) → ∀ (q : PtAt R sel mu cst u j) (d : DecoSet (E := X.E) (n := R.N j) (ST := Pr.vT u) (SG := Pr.vGs)), ∃ q' : PtAt R sel mu cst u j, q'.1.1.deco = d ∧ MemChart.bar q' = MemChart.bar q := by
  exact @GlobalTheory.Mem.Col2.MemChart.CosetLift.exists_ptAt_bar_eq
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.pointDeterminant_eq_normOneClass_of_level : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (n : ℕ) (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (p : DecoF H.E n ST SG Q) (y k : GL (Fin n) (AfE H.F H.E)) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)), LevOk H SG SQ → IsPtOf (host_cmData R H) (y * k) (extTo SQ p) → k ∈ Formalism.L2.Herm.UstdAf (host_cmData R H) n → Formalism.L2.Herm.Carries k (stdLat H.E n) (stdLat H.E n) → (∀ P ∈ uSG SG SQ, Formalism.UG.bc (Formalism.UG.prV (E := H.E) (P.under (𝓞 H.F))) k = 1) → Matrix.GeneralLinearGroup.det x.1 = Matrix.GeneralLinearGroup.det y → detPt H SQ p = u1Dt H SQ x := by
  first | exact @GlobalTheory.Mem.Col2.FullDt.detPt_eq_u1Dt_of_level | exact GlobalTheory.Mem.Col2.FullDt.detPt_eq_u1Dt_of_level | (intros; apply GlobalTheory.Mem.Col2.FullDt.detPt_eq_u1Dt_of_level <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.rationalNormOne_class_eq_finiteAdelic_det_class : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SQ : Finset (HeightOneSpectrum (𝓞 H.E))) (z : unitary H.E) (x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H)), Matrix.GeneralLinearGroup.det x.1 = Formalism.L2.Herm.unitaryOneRationalAdele H.F z → e1Q H SQ z = u1Dt H SQ x := by
  first | exact @GlobalTheory.Mem.Col2.FullDt.e1Q_eq_u1Dt_of_det_eq | exact GlobalTheory.Mem.Col2.FullDt.e1Q_eq_u1Dt_of_det_eq | (intros; apply GlobalTheory.Mem.Col2.FullDt.e1Q_eq_u1Dt_of_det_eq <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.FullDt ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.isOpen_ker_normOneFiniteAdeleDetClass : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (SG SQ : Finset (HeightOneSpectrum (𝓞 H.E))), LevOk H SG SQ → letI := Formalism.BasicNotions.tensTopL (F := H.F) (E := H.E) (Formalism.L2.Herm.Af H.F); IsOpen {x : Formalism.L2.Herm.unitaryOneFiniteAdeles (host_cmData R H) | u1Dt H SQ x = 1} := by
  first | exact @GlobalTheory.Mem.Col2.FullDt.isOpen_ker_u1Dt | exact GlobalTheory.Mem.Col2.FullDt.isOpen_ker_u1Dt | (intros; apply GlobalTheory.Mem.Col2.FullDt.isOpen_ker_u1Dt <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_levelJ_character_eq_member_off_places : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (Ch0 : B.Word → ℕ → Type) (chOf0 : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch0 u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch0 u) (chOf0 u)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (h1 : 1 ≤ B.R.m - 1) (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u a).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u a (B.R.m - 1) c.1))) (g : Ch → Ch0 u (B.R.m - 1)), (∀ v, v ∈ Q ↔ I.UnderQ a v) → (∀ u, I.StdF l Z u (F u)) → (∀ u j v h, (F u).glevJ.fr j v h = 1) → I.ReadsK l Z u a (B.R.m - 1) (Nat.sub_le _ _) chOf K → (∀ β, ∀ v, v ∉ Q → (K β).lev.Uloc v = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.Uloc v) → (∀ β (κ : (K β).lev.U) (κ' : ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = ((F u).ch (B.R.m - 1) h1 (succ_pred_m B.R) (g β)).lev.chi κ') → ∀ J : TwLevJ I l Z F Q u a chOf K, ∃ χ : J.levJ.U →* ℂˣ, (∀ β (κ : J.levJ.U) (κ' : (K β).lev.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (K β).lev.chi κ' = χ κ) ∧ ∀ (κ : J.levJ.U) (κ' : (F u).levJ.U), κ'.1 = reGL (rankN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) _ κ.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → χ κ = (F u).levJ.chi κ' := by
  first | exact @GlobalTheory.Mem.Col2.TC.twLevJ_exists_chi_off | exact GlobalTheory.Mem.Col2.TC.twLevJ_exists_chi_off | (intros; apply GlobalTheory.Mem.Col2.TC.twLevJ_exists_chi_off <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem k_pins_of_fields {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : G.Inst (I.rec7 l Z) L} {Gl : G.LatInst (I.rec7 l Z)} {K : G.Consts} {Y : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX} (t : KerEntTied ex) (hOk : I.Ok) (hP : TC.Pins B X)
    (hX : t.X = B.fields) (hseam : HEq t.seam (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G)) (hPr : HEq t.Pr (B.primes X))
    (hCh : HEq t.Ch I.Ch) (hsel : HEq t.sel I.sel) (hSS : t.S = I.S) (hword : HEq t.word fun u : B.Word => u)
    (htup : HEq t.tup I.tup) (hcst : HEq t.cst I.cst) (hglob : HEq t.glob I.glob) (hO : I.StdO l Z Y.Qp t.O)
    (hpi : ex.errX.piT = X.piT) : t.ChTie ∧ t.MemSideU ∧ t.MtTwTie ∧ ∀ a, (t.cst a).sharp = true := by
  have hU : t.MemSideU := by
    intro u
    refine ⟨?_, ?_, ?_⟩
    · show (t.O u I.mu0).mt = _
      rw [hO.mt u I.mu0, hOk.trueColumnChoices_heckeChar_reference_eq_one, tildeQ_one]
      funext j
      split_ifs
      · exact mul_one _
      · rfl
    · intro i c
      show (t.O u I.mu0).dt i c = _
      rw [hO.dt u I.mu0 i c]
      rfl
    · rw [hpi]
      exact memLatAt_std I hOk hP l Z u (t.memObj u) fun i c => hO.lat u I.mu0 i c
  have hPi : t.PiSide := by
    clear hU hO hglob hcst htup hSS hsel hCh
    cases t
    dsimp only at *
    subst hX
    cases hseam
    cases hPr
    cases hword
    intro u
    rw [hpi]
    rfl
  have hC : t.Ch.Ok ∧ MuValTie t.Ch t.glob ∧ ∀ a, (t.cst a).sharp = true := by
    clear hU hPi
    cases t
    dsimp only at *
    subst hX
    cases hPr
    cases hCh
    cases hsel
    subst hSS
    cases htup
    cases hcst
    cases hglob
    exact ⟨hOk.ch_ok, fun j v h => hOk.ch_tied.muVal j v h, fun a => hOk.sharp a⟩
  have hM : t.MtTwTie := by
    clear hU hPi hC
    cases t
    dsimp only at *
    subst hX
    cases hseam
    subst hSS
    cases htup
    refine ⟨(QuotientGroup.mk' (KDq B.host I.SQ)).comp (finIdele (afIso B.host.F B.host.E)), ⟨fun y => ?_, fun k z hz => ?_⟩,
      fun μ _ _ => ⟨tildeQ B.host I.SQ (I.xi μ), fun x => ?_, fun u => ?_⟩⟩
    · obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective (show DtQ B.host I.SQ from y)
      refine ⟨finAf B.host.F B.host.E a, ?_⟩
      exact mk_eq_of_snd_eq B.host I.SQ (afIso_finAf B.host.F B.host.E a)
    · have hz' : (show B.host.E from z.1) * B.host.conj (k : B.host.E) = k := hz
      show (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) (ratId B.host.F B.host.E k)) : DtQ B.host I.SQ) = e1Q B.host I.SQ z
      rw [← isUnitaryPointsMap_unitaryRationalPointsFiner B.host I.SQ k z hz']
      refine mk_eq_of_snd_eq B.host I.SQ ?_
      show afIso B.host.F B.host.E ((k : B.host.E) ⊗ₜ[B.host.F] 1) = _
      rw [afIso_tmul_one]
      rfl
    · have hk : KDq B.host I.SQ ≤ ((I.xi μ).1.comp (finPartI B.host.E)).ker :=
        (KDq_anti B.host (I.Q_subset_SQ μ)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hOk).2.2 μ).1
      show tildeQ B.host I.SQ (I.xi μ) (QuotientGroup.mk (finIdele (afIso B.host.F B.host.E) x)) = _
      rw [tildeQ_mk B.host I.SQ hk, finPartI_eq_self fun _ => rfl]
      exact Units.ext ((hOk.xi_reads μ).apply _ x rfl)
    · rw [hO.mt u μ]
      rfl
  exact ⟨⟨hC.1, hC.2.1, hPi, fun u _ => hU u⟩, hU, hM, hC.2.2⟩

theorem k_pins_tie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKerTie l Z t → ex.errX.piT = X.piT → t.ChTie ∧ t.MemSideU ∧ t.MtTwTie ∧ ∀ a, (t.cst a).sharp = true := by
  intro B X I hOk hP l Z L hT Gi Gl K Y cX ex t hS hpi
  exact k_pins_of_fields I l Z t hOk hP hS.X_eq hS.seam hS.Pr hS.Ch hS.sel hS.S hS.word hS.tup hS.cst hS.glob hS.O hpi

end GlobalTheory.Mem.Col2.TC

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_haar_fundamentalDomain_isometryTransport : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (S : HSp D) (μ : Measure (WO S V')) (𝓕 : Set (WO S V')), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL V' S) 𝓕 μ → ∃ (ν : Measure (WO S V)) (𝓖 : Set (WO S V)), ν.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratL V S) 𝓖 ν ∧ ∀ u : WO S V → ENNReal, ∫⁻ w in 𝓕, u ((I.phi S).symm w) ∂μ = ∫⁻ w in 𝓖, u w ∂ν := by
  first | exact @GlobalTheory.Mem.Isom.haar_fd_phi | exact GlobalTheory.Mem.Isom.haar_fd_phi | (intros; apply GlobalTheory.Mem.Isom.haar_fd_phi <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isCuspidal_isometryTransport_hermitian : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (φ : GA D V → ℂ), IsCuspFun V φ → IsCuspFun V' (I.tr φ) := by
  first | exact @GlobalTheory.Mem.Isom.isCuspFun_tr | exact GlobalTheory.Mem.Isom.isCuspFun_tr | (intros; apply GlobalTheory.Mem.Isom.isCuspFun_tr <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix Formalism.IndefR.Datum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.normInf_isometryConj_le_const_mul : ∀ (D : D7) (V V' : HSp D) (I : GlobalTheory.Mem.Isom.IsoMat V V') (θ : InfF D), IsInfFam θ → ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GA D V, normInf θ V' (I.kap g) ≤ C * normInf θ V g := by
  first | exact @GlobalTheory.Mem.Isom.normInf_kap_le | exact GlobalTheory.Mem.Isom.normInf_kap_le | (intros; apply GlobalTheory.Mem.Isom.normInf_kap_le <;> assumption)
end
