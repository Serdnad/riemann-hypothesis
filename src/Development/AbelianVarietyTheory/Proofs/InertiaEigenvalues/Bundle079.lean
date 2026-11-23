module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle015
public import Mathlib.MeasureTheory.Measure.Haar.Extension
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle016
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle013
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Field.ProperSpace
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Separation.Connected
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

section

open MeasureTheory

theorem _root_.GlobalTheory.T.tsum_setIntegral_prod_eq_zero_of_inner' : ∀ {G X : Type} [MeasurableSpace G], Countable X → ∀ (ν : Measure G), SFinite ν → ∀ (𝓖 : Set G) (H : X → G × G → ℂ), (∀ x, AEStronglyMeasurable (H x) (ν.prod ν)) → ∫⁻ g₁ in 𝓖, ∫⁻ g₂ in 𝓖, ∑' x, ‖H x (g₁, g₂)‖ₑ ∂ν ∂ν ≠ ⊤ → (∀ g₂, ∑' x, ∫⁻ g₁ in 𝓖, ‖H x (g₁, g₂)‖ₑ ∂ν ≠ ⊤ → ∑' x, ∫ g₁ in 𝓖, H x (g₁, g₂) ∂ν = 0) → ∑' x, ∫ p in 𝓖 ×ˢ 𝓖, H x p ∂(ν.prod ν) = 0 := by
  first | exact @GlobalTheory.tsum_setIntegral_prod_eq_zero_of_inner | exact GlobalTheory.tsum_setIntegral_prod_eq_zero_of_inner | (intros; apply GlobalTheory.tsum_setIntegral_prod_eq_zero_of_inner <;> assumption)
end

section

open GlobalTheory.JR MeasureTheory Filter Topology

namespace GlobalTheory.JR


open TopologicalGroup in
theorem integral_inducedMeasure_complex {A B C : Type} [Group A] [Group B] [Group C]
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [IsTopologicalGroup A]
    [IsTopologicalGroup B] [IsTopologicalGroup C] [T2Space B] [LocallyCompactSpace B]
    [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B] [MeasurableSpace C]
    [BorelSpace C] {φ : A →* B} {ψ : B →* C} (H : IsSES φ ψ) (ν : Measure A) [ν.IsHaarMeasure]
    (μC : Measure C) [μC.IsHaarMeasure] (F : CompactlySupportedContinuousMap B ℂ) :
    ∫ b, F b ∂(H.inducedMeasure ν μC) = ∫ c, H.pushforward ν F c ∂μC := by
  have key : ∀ L : ℂ →L[ℝ] ℝ, L (∫ b, F b ∂(H.inducedMeasure ν μC))
      = L (∫ c, H.pushforward ν F c ∂μC) := by
    intro L
    let G : CompactlySupportedContinuousMap B ℝ :=
      ⟨⟨fun b => L (F b), L.continuous.comp F.continuous⟩,
        F.hasCompactSupport.comp_left (g := L) (map_zero L)⟩
    rw [← L.integral_comp_comm F.integrable,
      ← L.integral_comp_comm (H.pushforward ν F).integrable]
    have h1 := H.integral_inducedMeasure ν μC G
    rw [IsSES.integrate_apply] at h1
    refine h1.trans ?_
    congr with c
    rw [IsSES.pushforward_def, IsSES.pushforward_def,
      ← L.integral_comp_comm (H.pullback F _).integrable]
    simp only [IsSES.pullback_def]
    rfl
  exact Complex.ext (key Complex.reCLM) (key Complex.imCLM)

theorem exists_haar_quotient_integral_formula : ∀ (A B C : Type) [Group A] [Group B] [Group C] [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [IsTopologicalGroup A] [IsTopologicalGroup B] [IsTopologicalGroup C] [T2Space B] [LocallyCompactSpace B] [SecondCountableTopology B] [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B] [MeasurableSpace C] [BorelSpace C] (φ : A →* B) (ψ : B →* C), TopologicalGroup.IsSES φ ψ → ∀ (μB : Measure B) (μC : Measure C), μB.IsHaarMeasure → μC.IsHaarMeasure → ∃ ν : Measure A, ν.IsHaarMeasure ∧ ∀ f : B → ℂ, Continuous f → HasCompactSupport f → ∀ s : C → B, (∀ c, ψ (s c) = c) → ∫ b, f b ∂μB = ∫ c, ∫ a, f (s c * φ a) ∂ν ∂μC := by
  intro A B C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ ψ H μB μC hB hC
  have : LocallyCompactSpace A := H.isClosedEmbedding.locallyCompactSpace
  let ν0 : Measure A := Measure.haar
  set μ := H.inducedMeasure ν0 μC with hμ
  have hsm := Measure.isMulLeftInvariant_eq_smul μB μ
  have hpos := Measure.haarScalarFactor_pos_of_isHaarMeasure μB μ
  set k := Measure.haarScalarFactor μB μ with hk
  refine ⟨k • ν0, Measure.IsHaarMeasure.nnreal_smul ν0 hpos.ne', ?_⟩
  intro f hf hfc s hs
  let F : CompactlySupportedContinuousMap B ℂ := ⟨⟨f, hf⟩, hfc⟩
  have h := integral_inducedMeasure_complex H ν0 μC F
  rw [hsm, integral_smul_nnreal_measure]
  simp_rw [integral_smul_nnreal_measure, NNReal.smul_def]
  rw [integral_smul]
  congr 1
  refine h.trans ?_
  congr with c
  conv_lhs => rw [← hs c]
  rw [H.pushforward_apply_apply]
  simp only [TopologicalGroup.IsSES.pullback_def]
  rfl

end GlobalTheory.JR
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

theorem _root_.GlobalTheory.T.exists_mixedSpace_norm_sign_character : ∀ (K : Type) [Field K] [NumberField K] (ε : ℂ), ε * ε = 1 → ∃ φ : mixedSpace K → ℂ, (∀ x y, φ (x * y) = φ x * φ y) ∧ (∀ (t : ℝ) x, 0 < t → φ (t • x) = φ x) ∧ ContDiffOn ℝ ∞ φ {x | mixedEmbedding.norm x ≠ 0} ∧ (∀ x, mixedEmbedding.norm x ≠ 0 → ‖φ x‖ = 1) ∧ ∀ β : 𝓞 K, β ≠ 0 → φ (mixedEmbedding K β) = if 0 < Algebra.norm ℤ β then 1 else ε := by
  first | exact @GlobalTheory.NormSign.exists_normSign | exact GlobalTheory.NormSign.exists_normSign | (intros; apply GlobalTheory.NormSign.exists_normSign <;> assumption)
end

section


theorem _root_.GlobalTheory.T.eulerInverse_powerSeries_eval_one : ∀ {ι : Type} [Fintype ι] (c : ℕ → ℂ), (Summable fun d => ‖c d‖) → ∀ (Q : ι → ℂ),
    PowerSeries.mk c * ∏ p, (1 - PowerSeries.C (Q p) * PowerSeries.X) = 1 →
    (∏ p, (1 - Q p)) ≠ 0 ∧ HasSum c (∏ p, (1 - Q p))⁻¹ := by
  exact @GlobalTheory.JSW.eulerInverse_eval_one
end

section


theorem _root_.GlobalTheory.T.schur_isotypic_splitting_inner_product : ∀ {G W H : Type} [Group G] [AddCommGroup W] [Module ℂ W] [Nontrivial W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (act : G →* Module.End ℂ H), (∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0) → ∀ (ρ : G →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ g, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ x : H, ∃ q ∈ Submodule.span ℂ {q | ∃ (φ : W →ₗ[ℂ] H) (w : W), (∀ g w', φ (ρ g w') = act g (φ w')) ∧ q = φ w}, ∃ E : Submodule ℂ H, (∀ g, ∀ e ∈ E, act g e ∈ E) ∧ (∀ φ : H →ₗ[ℂ] W, (∀ g, ∀ e ∈ E, φ (act g e) = ρ g (φ e)) → ∀ e ∈ E, φ e = 0) ∧ x - q ∈ E := by
  first | exact @GlobalTheory.schur_isotypic_splitting | exact GlobalTheory.schur_isotypic_splitting | (intros; apply GlobalTheory.schur_isotypic_splitting <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.CutOff

theorem exists_isClopen_isCompact_superset {R : Type} [TopologicalSpace R] [LocallyCompactSpace R]
    [T2Space R] [TotallyDisconnectedSpace R] {Z : Set R} (hZ : IsCompact Z) :
    ∃ U : Set R, IsClopen U ∧ IsCompact U ∧ Z ⊆ U := by
  classical
  have h : ∀ z : R, ∃ V : Set R, IsClopen V ∧ IsCompact V ∧ z ∈ V := by
    intro z
    obtain ⟨K, hK, hKz⟩ := exists_compact_mem_nhds z
    obtain ⟨V, hV, hzV, hVK⟩ := isTopologicalBasis_isClopen.mem_nhds_iff.1 hKz
    exact ⟨V, hV, hK.of_isClosed_subset hV.isClosed hVK, hzV⟩
  choose V hVc hVk hzV using h
  obtain ⟨t, -, ht⟩ := hZ.elim_nhds_subcover V (fun z _ => (hVc z).isOpen.mem_nhds (hzV z))
  exact ⟨⋃ z ∈ t, V z, isClopen_biUnion_finset fun z _ => hVc z,
    t.isCompact_biUnion fun z _ => hVk z, ht⟩

theorem exists_nhds_one_mul_mem_iff {R : Type} [Group R] [TopologicalSpace R]
    [IsTopologicalGroup R] {U : Set R} (hUo : IsOpen U) (hUk : IsCompact U) :
    ∃ W ∈ 𝓝 (1 : R), ∀ w ∈ W, ∀ x, w * x ∈ U ↔ x ∈ U := by
  open scoped Pointwise in
  obtain ⟨V, hV, hVU⟩ := compact_open_separated_mul_left hUk hUo subset_rfl
  refine ⟨V ∩ V⁻¹, inter_mem hV (inv_mem_nhds_one R hV), ?_⟩
  rintro w ⟨hw, hw'⟩ x
  constructor
  · intro h
    have : w⁻¹ * (w * x) ∈ U := hVU (Set.mul_mem_mul (Set.mem_inv.1 hw') h)
    simpa using this
  · intro h
    exact hVU (Set.mul_mem_mul hw h)

theorem isLocallyConstant_indicator_one {R : Type} [TopologicalSpace R] {U : Set R}
    (hU : IsClopen U) : IsLocallyConstant (U.indicator (fun _ => (1 : ℝ))) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hx : x ∈ U
  · filter_upwards [hU.isOpen.mem_nhds hx] with y hy
    simp [hx, hy]
  · filter_upwards [hU.isClosed.isOpen_compl.mem_nhds hx] with y hy
    simp [hx, Set.notMem_compl_iff.not.1 (by simpa using hy)]

theorem exists_cutoff : ∀ (R S : Type) [Group R] [TopologicalSpace R] [IsTopologicalGroup R] [LocallyCompactSpace R] [T2Space R] [TotallyDisconnectedSpace R] [Group S] [TopologicalSpace S] [IsTopologicalGroup S] [MeasurableSpace S] [BorelSpace S] (i : S →* R), Topology.IsClosedEmbedding i → ∀ (ν : Measure S) [ν.IsHaarMeasure] (Z : Set R), IsCompact Z → ∃ α : R → ℝ, IsLocallyConstant α ∧ HasCompactSupport α ∧ (∀ g, 0 ≤ α g) ∧ ∀ z ∈ Z, ∀ s₀ : S, ∫ s, α (z * i s₀ * i s) ∂ν = 1 := by
  intro R S _ _ _ _ _ _ _ _ _ _ _ i hi ν _ Z hZ
  classical
  obtain ⟨U, hUc, hUk, hZU⟩ := exists_isClopen_isCompact_superset hZ
  obtain ⟨W, hW, hWU⟩ := exists_nhds_one_mul_mem_iff hUc.isOpen hUk
  set β : R → ℝ := U.indicator (fun _ => (1 : ℝ)) with hβ
  have hβlc : IsLocallyConstant β := isLocallyConstant_indicator_one hUc
  have hβc : Continuous β := hβlc.continuous
  have hβ0 : ∀ x, 0 ≤ β x := fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x
  set F : R → ℝ := fun g => ∫ s, β (g * i s) ∂ν with hF
  have hFinv : ∀ g t, F (g * i t) = F g := by
    intro g t
    have := integral_mul_left_eq_self (μ := ν) (fun s => β (g * i s)) t
    simpa [hF, mul_assoc, map_mul] using this
  have hβmul : ∀ w ∈ W, ∀ x, β (w * x) = β x := by
    intro w hw x
    simp [hβ, Set.indicator, hWU w hw x]
  have hFW : ∀ w ∈ W, ∀ g, F (w * g) = F g := by
    intro w hw g
    simp only [hF, mul_assoc, hβmul w hw]
  have hFlc : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    have hc : Tendsto (fun y => y * g⁻¹) (𝓝 g) (𝓝 1) := by
      simpa using (continuous_mul_const g⁻¹).tendsto g
    filter_upwards [hc hW] with y hy
    have := hFW _ hy g
    rwa [inv_mul_cancel_right] at this
  have hFpos : ∀ g ∈ U, 0 < F g := by
    intro g hg
    have hcont : Continuous (fun s => β (g * i s)) :=
      hβc.comp (continuous_const.mul hi.continuous)
    have hKc : IsCompact (i ⁻¹' ((Homeomorph.mulLeft g) ⁻¹' U)) :=
      hi.isCompact_preimage ((Homeomorph.mulLeft g).isCompact_preimage.2 hUk)
    have hKcl : IsClosed (i ⁻¹' ((Homeomorph.mulLeft g) ⁻¹' U)) :=
      (hUc.isClosed.preimage (Homeomorph.mulLeft g).continuous).preimage hi.continuous
    have hsupp : HasCompactSupport (fun s => β (g * i s)) := by
      refine HasCompactSupport.intro' hKc hKcl fun x hx => ?_
      have hx' : g * i x ∉ U := hx
      simp [hβ, hx']
    exact hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hsupp
      (fun s => hβ0 _) (by simp [hβ, hg])
  refine ⟨fun g => β g / F g, ?_, ?_, ?_, ?_⟩
  · exact IsLocallyConstant.comp₂ hβlc hFlc (· / ·)
  · refine HasCompactSupport.intro hUk fun x hx => ?_
    simp [hβ, hx]
  · intro g
    exact div_nonneg (hβ0 g) (integral_nonneg fun s => hβ0 _)
  · intro z hz s₀
    have h1 : ∫ s, β (z * i s₀ * i s) / F (z * i s₀ * i s) ∂ν
        = ∫ s, β (z * i s) / F (z * i s) ∂ν := by
      have := integral_mul_left_eq_self (μ := ν) (fun s => β (z * i s) / F (z * i s)) s₀
      simpa [mul_assoc, map_mul] using this
    rw [h1]
    have h2 : ∀ s, β (z * i s) / F (z * i s) = β (z * i s) / F z := fun s => by rw [hFinv]
    simp_rw [h2]
    rw [integral_div]
    exact div_self (hFpos z (hZU hz)).ne'

end GlobalTheory.CutOff
end

section


theorem _root_.GlobalTheory.T.norm_mul_apply_le_of_ultrametric : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (A B : Matrix n n E) (a b : ℝ), 0 ≤ a → 0 ≤ b → (∀ i j, ‖A i j‖ ≤ a) → (∀ i j, ‖B i j‖ ≤ b) → ∀ i j, ‖(A * B) i j‖ ≤ a * b := by
  first | exact @GlobalTheory.matrix_mul_entry_norm_le_ultrametric | exact GlobalTheory.matrix_mul_entry_norm_le_ultrametric | (intros; apply GlobalTheory.matrix_mul_entry_norm_le_ultrametric <;> assumption)
end

section


theorem _root_.GlobalTheory.T.ultrametric_matrix_inv_near_one : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (X Z : Matrix n n E) (t : ℝ), 0 ≤ t → t < 1 → Z * X = 1 → (∀ i j, ‖(X - 1) i j‖ ≤ t) → ∀ i j, ‖(Z - 1) i j‖ ≤ t := by
  first | exact @GlobalTheory.matrix_inv_near_one | exact GlobalTheory.matrix_inv_near_one | (intros; apply GlobalTheory.matrix_inv_near_one <;> assumption)
end

section


theorem _root_.GlobalTheory.T.norm_one_add_pow_sub_one_sub_smul_le_sq : ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n] (Y : Matrix n n E) (t : ℝ), 0 ≤ t → t ≤ 1 → (∀ i j, ‖Y i j‖ ≤ t) → ∀ (m : ℕ) i j, ‖((1 + Y) ^ m - 1 - (m : E) • Y) i j‖ ≤ t ^ 2 := by
  first | exact @GlobalTheory.matrix_one_add_pow_sub_entry_le | exact GlobalTheory.matrix_one_add_pow_sub_entry_le | (intros; apply GlobalTheory.matrix_one_add_pow_sub_entry_le <;> assumption)
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

open Set Pointwise Metric

namespace GlobalTheory.HaarNullSub

theorem addHaar_submodule_eq_zero (F : Type) [NontriviallyNormedField F] [LocallyCompactSpace F]
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V] [TopologicalSpace V]
    [IsModuleTopology F V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V)
    (hμ : μ.IsAddHaarMeasure) (s : Submodule F V) (hs : s ≠ ⊤) : μ (s : Set V) = 0 := by
  haveI := hμ
  haveI : ProperSpace F := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd F V
  haveI : ContinuousSMul F V := inferInstance

  let e₀ : V ≃ₗ[F] (Fin (Module.finrank F V) → F) := (Module.finBasis F V).equivFun
  have hc : Continuous e₀ := IsModuleTopology.continuous_of_linearMap e₀.toLinearMap
  have hc' : Continuous e₀.symm := IsModuleTopology.continuous_of_linearMap e₀.symm.toLinearMap
  let h : V ≃ₜ (Fin (Module.finrank F V) → F) :=
    { e₀.toEquiv with continuous_toFun := hc, continuous_invFun := hc' }

  have hcl : IsClosed (s : Set V) := by
    have h1 : IsClosed ((s.map e₀.toLinearMap : Submodule F _) : Set (Fin (Module.finrank F V) → F)) :=
      Submodule.closed_of_finiteDimensional _
    have h2 : (s : Set V) = h ⁻¹' ((s.map e₀.toLinearMap : Submodule F _) : Set _) := by
      ext v
      simp [h, Submodule.mem_map]
    rw [h2]; exact h1.preimage h.continuous

  obtain ⟨x, hx⟩ : ∃ x, x ∉ s := by
    simpa only [Submodule.eq_top_iff', not_exists, Ne, not_forall] using hs
  obtain ⟨c, c0, c1⟩ := NormedField.exists_norm_lt_one F
  let u : ℕ → V := fun n => c ^ n • x
  have hu : Tendsto u atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => c ^ n) atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one c1
    simpa [u] using this.smul_const x
  have hC : IsCompact (insert 0 (range u)) := hu.isCompact_insert_range

  have hdisj : ∀ A ⊆ (s : Set V), Pairwise (Function.onFun Disjoint fun n => {u n} + A) := by
    intro A hA m n hmn
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨_, rfl, a, ha, rfl⟩ ⟨_, rfl, b, hb, hab⟩
    apply hx
    have hne : c ^ m - c ^ n ≠ 0 := by
      intro h0
      apply hmn
      have : ‖c‖ ^ m = ‖c‖ ^ n := by rw [← norm_pow, ← norm_pow, sub_eq_zero.mp h0]
      exact pow_right_injective₀ c0 (ne_of_lt c1) this.symm |>.symm
    have hmem : (c ^ m - c ^ n) • x ∈ s := by
      have : (c ^ m - c ^ n) • x = b - a := by
        simp only [u] at hab
        rw [sub_smul, show c ^ m • x = c ^ n • x + b - a by rw [hab]; abel]; abel
      rw [this]; exact s.sub_mem (hA hb) (hA ha)
    exact (Submodule.smul_mem_iff s hne).mp hmem

  have key : ∀ R : ℝ, μ ((s : Set V) ∩ h ⁻¹' closedBall 0 R) = 0 := by
    intro R
    set A := (s : Set V) ∩ h ⁻¹' closedBall 0 R with hAdef
    have hAc : IsCompact A := by
      have hK : IsCompact (h ⁻¹' closedBall 0 R) := by
        rw [← h.image_symm]
        exact (isCompact_closedBall (0 : Fin (Module.finrank F V) → F) R).image h.symm.continuous
      exact hK.inter_left hcl
    have hAm : MeasurableSet A := hcl.measurableSet.inter (isClosed_closedBall.preimage h.continuous).measurableSet
    by_contra hne
    apply lt_irrefl (⊤ : ENNReal)
    calc
      (⊤ : ENNReal) = ∑' _ : ℕ, μ A := (ENNReal.tsum_const_eq_top_of_ne_zero hne).symm
      _ = ∑' n : ℕ, μ ({u n} + A) := by
        congr 1; ext1 n; simp only [image_add_left, measure_preimage_add, singleton_add]
      _ = μ (⋃ n, {u n} + A) := Eq.symm <| measure_iUnion (hdisj A inter_subset_left) fun n => by
        simpa only [image_add_left, singleton_add] using (measurable_const_add (-u n)) hAm
      _ ≤ μ (insert 0 (range u) + A) := by
        apply measure_mono
        refine iUnion_subset fun n => add_subset_add ?_ Subset.rfl
        exact singleton_subset_iff.mpr (mem_insert_of_mem _ (mem_range_self n))
      _ < ⊤ := (hC.add hAc).measure_lt_top
  rw [← nonpos_iff_eq_zero]
  calc
    μ (s : Set V) ≤ ∑' n : ℕ, μ ((s : Set V) ∩ h ⁻¹' closedBall 0 n) := by
      conv_lhs => rw [← inter_univ (s : Set V), ← preimage_univ (f := h), ← iUnion_closedBall_nat 0,
        preimage_iUnion, inter_iUnion]
      exact measure_iUnion_le _
    _ = 0 := by simp only [key, tsum_zero]

end GlobalTheory.HaarNullSub
end

section

open Polynomial

theorem _root_.GlobalTheory.T.ultrametric_norm_hasSum_sub_finset_sum_le : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) (f : ι → K) (s : K) (I : Finset ι) (ε : ℝ), 0 ≤ ε → HasSum f s → (∀ i, i ∉ I → ‖f i‖ ≤ ε) → ‖s - ∑ i ∈ I, f i‖ ≤ ε := by
  first | exact @GlobalTheory.norm_hasSum_sub_finset_sum_le | exact GlobalTheory.norm_hasSum_sub_finset_sum_le | (intros; apply GlobalTheory.norm_hasSum_sub_finset_sum_le <;> assumption)
end

section

open Polynomial

theorem _root_.GlobalTheory.T.norm_eq_of_hasSum_of_dominant_term : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (ι : Type) (f : ι → K) (s : K) (i₀ : ι), HasSum f s → (∀ i, i ≠ i₀ → ‖f i‖ < ‖f i₀‖) → ‖s‖ = ‖f i₀‖ := by
  first | exact @GlobalTheory.norm_hasSum_eq_of_dominant | exact GlobalTheory.norm_hasSum_eq_of_dominant | (intros; apply GlobalTheory.norm_hasSum_eq_of_dominant <;> assumption)
end
