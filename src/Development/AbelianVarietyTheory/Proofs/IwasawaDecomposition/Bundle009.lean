module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Aesop.Main
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
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
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

section

open MeasureTheory
open scoped InnerProductSpace

namespace GlobalTheory.SchurOrthOnSubgroup

theorem setIntegral_subgroup_mul_left {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (Ω : Subgroup G) (hΩ : MeasurableSet (Ω : Set G))
    (f : G → ℂ) {h : G} (hh : h ∈ Ω) :
    ∫ g in (Ω : Set G), f (h * g) ∂ν = ∫ g in (Ω : Set G), f g ∂ν := by
  rw [← integral_indicator hΩ, ← integral_indicator hΩ]
  have : (Ω : Set G).indicator (fun g => f (h * g)) = fun g => (Ω : Set G).indicator f (h * g) := by
    funext g
    by_cases hg : g ∈ Ω
    · have hg' : h * g ∈ Ω := Ω.mul_mem hh hg
      simp [Set.indicator_of_mem, hg, hg']
    · have hg' : h * g ∉ Ω := fun H => hg ((Ω.mul_mem_cancel_left hh).1 H)
      simp [Set.indicator_of_notMem, hg, hg']
  rw [this, integral_mul_left_eq_self]

variable {G : Type} [Group G] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]

theorem rep_apply_inv_apply (ρ : G →* Module.End ℂ W) (g : G) (v : W) : ρ g (ρ g⁻¹ v) = v := by
  show (ρ g * ρ g⁻¹) v = v
  rw [← map_mul, mul_inv_cancel, map_one]; rfl

theorem inner_rep_inv (ρ : G →* Module.End ℂ W) (hU : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (g : G) (x y : W) : ⟪ρ g⁻¹ x, y⟫_ℂ = ⟪x, ρ g y⟫_ℂ := by
  rw [← hU g (ρ g⁻¹ x) y, rep_apply_inv_apply]

theorem inner_rep_inv' (ρ : G →* Module.End ℂ W) (hU : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (g : G) (x y : W) : ⟪x, ρ g⁻¹ y⟫_ℂ = ⟪ρ g x, y⟫_ℂ := by
  rw [← hU g x (ρ g⁻¹ y), rep_apply_inv_apply]

theorem norm_rep (ρ : G →* Module.End ℂ W) (hU : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (g : G) (v : W) : ‖ρ g v‖ = ‖v‖ := by
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, hU]

end GlobalTheory.SchurOrthOnSubgroup

namespace GlobalTheory.SchurOrthOnSubgroup

theorem schur_orthogonality {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
    (ν : Measure G) [ν.IsMulLeftInvariant] (Ω : Subgroup G) (hΩ : MeasurableSet (Ω : Set G))
    (hν : ν (Ω : Set G) = 1) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (ρ : G →* Module.End ℂ W)
    (hU : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hM : ∀ x y : W, Measurable fun g => ⟪x, ρ g y⟫_ℂ)
    (hirr : ∀ U : Submodule ℂ W, (∀ g ∈ Ω, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤)
    (a a' x x' : W) :
    IntegrableOn (fun g => star ⟪a, ρ g⁻¹ x⟫_ℂ * ⟪a', ρ g⁻¹ x'⟫_ℂ) Ω ν ∧
      (Module.finrank ℂ W : ℂ) * ∫ g in (Ω : Set G), star ⟪a, ρ g⁻¹ x⟫_ℂ * ⟪a', ρ g⁻¹ x'⟫_ℂ ∂ν
        = ⟪a', a⟫_ℂ * ⟪x, x'⟫_ℂ := by

  set F : W → W → G → ℂ := fun y y' g => star ⟪a, ρ g⁻¹ y⟫_ℂ * ⟪a', ρ g⁻¹ y'⟫_ℂ with hF
  have hfin : ν (Ω : Set G) < ⊤ := by rw [hν]; exact ENNReal.one_lt_top
  have hint : ∀ y y', IntegrableOn (F y y') Ω ν := by
    intro y y'
    have hmeas : Measurable (F y y') := by
      have h1 : Measurable fun g : G => ⟪a, ρ g⁻¹ y⟫_ℂ := (hM a y).comp measurable_inv
      have h2 : Measurable fun g : G => ⟪a', ρ g⁻¹ y'⟫_ℂ := (hM a' y').comp measurable_inv
      exact (continuous_star.measurable.comp h1).mul h2
    refine Integrable.mono' (g := fun _ => (‖a‖ * ‖y‖) * (‖a'‖ * ‖y'‖)) ?_
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    · exact integrableOn_const hfin.ne
    · simp only [hF, norm_mul, norm_star]
      gcongr
      · exact (norm_inner_le_norm _ _).trans (by rw [norm_rep ρ hU])
      · exact (norm_inner_le_norm _ _).trans (by rw [norm_rep ρ hU])
  refine ⟨hint x x', ?_⟩

  set B : W → W → ℂ := fun y y' => ∫ g in (Ω : Set G), F y y' g ∂ν with hB
  let b := stdOrthonormalBasis ℂ W
  have hBadd : ∀ y y1 y2, B y (y1 + y2) = B y y1 + B y y2 := by
    intro y y1 y2
    simp only [hB]
    rw [← integral_add (hint y y1) (hint y y2)]
    congr 1; funext g
    simp only [hF, map_add (f := _), inner_add_right, mul_add]
  have hBsmul : ∀ y (c : ℂ) y', B y (c • y') = c * B y y' := by
    intro y c y'
    simp only [hB]
    rw [← integral_const_mul]
    congr 1; funext g
    simp only [hF, map_smul, inner_smul_right]; ring
  have hBexp : ∀ y y', B y y' = ∑ i, ⟪y, b i⟫_ℂ * B (b i) y' := by
    intro y y'
    simp only [hB]
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ (fun i _ => (hint (b i) y').const_mul _)]
    congr 1; funext g
    simp only [hF]
    have hs : ∀ z, star ⟪a, ρ g⁻¹ z⟫_ℂ = ⟪z, ρ g a⟫_ℂ := by
      intro z
      rw [inner_rep_inv' ρ hU]
      exact inner_conj_symm _ _
    simp_rw [hs, ← mul_assoc, ← Finset.sum_mul]
    rw [b.sum_inner_mul_inner]
  have hBinv : ∀ h ∈ Ω, ∀ y y', B (ρ h y) (ρ h y') = B y y' := by
    intro h hh y y'
    simp only [hB]
    rw [← setIntegral_subgroup_mul_left ν Ω hΩ (F y y') (Ω.inv_mem hh)]
    congr 1; funext g
    have hg : ∀ z, ρ g⁻¹ (ρ h z) = ρ (h⁻¹ * g)⁻¹ z := by
      intro z
      rw [mul_inv_rev, inv_inv, map_mul]; rfl
    simp only [hF, hg]

  let T : W →ₗ[ℂ] W :=
    { toFun := fun y' => ∑ i, B (b i) y' • b i
      map_add' := by
        intro y1 y2
        simp only [hBadd, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c y'
        simp only [hBsmul, mul_smul, RingHom.id_apply, Finset.smul_sum] }
  have hT : ∀ y y', ⟪y, T y'⟫_ℂ = B y y' := by
    intro y y'
    rw [hBexp y y']
    simp only [T, LinearMap.coe_mk, AddHom.coe_mk, inner_sum, inner_smul_right]
    congr 1; funext i; ring
  have hcomm : ∀ h ∈ Ω, ∀ v, T (ρ h v) = ρ h (T v) := by
    intro h hh v
    apply ext_inner_left ℂ
    intro y
    rw [hT, ← inner_rep_inv ρ hU, hT]
    conv_lhs => rw [← rep_apply_inv_apply ρ h y]
    exact hBinv h hh _ _
  have hsum : ∑ i, B (b i) (b i) = ⟪a', a⟫_ℂ := by
    simp only [hB]
    rw [← integral_finsetSum _ (fun i _ => hint (b i) (b i))]
    have : ∀ g, ∑ i, F (b i) (b i) g = ⟪a', a⟫_ℂ := by
      intro g
      simp only [hF]
      have hs : ∀ z, star ⟪a, ρ g⁻¹ z⟫_ℂ = ⟪z, ρ g a⟫_ℂ := by
        intro z
        rw [inner_rep_inv' ρ hU]
        exact inner_conj_symm _ _
      simp_rw [hs, inner_rep_inv' ρ hU]
      simp_rw [mul_comm (⟪b _, ρ g a⟫_ℂ)]
      rw [b.sum_inner_mul_inner, hU]
    simp_rw [this]
    rw [setIntegral_const, Measure.real, hν]
    simp
  rcases subsingleton_or_nontrivial W with hW | hW
  · have ha : a = 0 := Subsingleton.elim _ _
    simp [Module.finrank_zero_of_subsingleton, ha]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T : Module.End ℂ W)
  have hU' : Module.End.eigenspace (T : Module.End ℂ W) c = ⊤ := by
    rcases hirr (Module.End.eigenspace (T : Module.End ℂ W) c) (by
      intro g hg
      rintro _ ⟨v, hv, rfl⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hv
      rw [Module.End.mem_eigenspace_iff, hcomm g hg, hv, map_smul]) with h0 | h0
    · exfalso
      obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
      have : v ∈ Module.End.eigenspace (T : Module.End ℂ W) c := hv.1
      rw [h0, Submodule.mem_bot] at this
      exact hv.2 this
    · exact h0
  have hTc : ∀ v, T v = c • v := fun v =>
    Module.End.mem_eigenspace_iff.1 (hU' ▸ Submodule.mem_top)
  have hBc : ∀ y y', B y y' = c * ⟪y, y'⟫_ℂ := by
    intro y y'
    rw [← hT, hTc, inner_smul_right]
  have hnc : (Module.finrank ℂ W : ℂ) * c = ⟪a', a⟫_ℂ := by
    rw [← hsum]
    have h1 : ∀ i, ⟪b i, b i⟫_ℂ = 1 := fun i => by
      simpa using orthonormal_iff_ite.1 b.orthonormal i i
    simp only [hBc, h1, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  show (Module.finrank ℂ W : ℂ) * B x x' = _
  rw [hBc, ← mul_assoc, hnc]

end GlobalTheory.SchurOrthOnSubgroup
end

section

open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory


open MeasureTheory Filter Topology in
open scoped ContDiff in
theorem _root_.GlobalTheory.contDiff_of_continuous_oneParameter (A : Type) [NormedRing A] [NormedAlgebra ℝ A]
    [CompleteSpace A] (T : ℝ → A) (hT : Continuous T) (h0 : T 0 = 1)
    (hadd : ∀ s t, T (s + t) = T s * T t) : ContDiff ℝ ∞ T := by
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → A, G = fun x => ∫ s in (0:ℝ)..x, T s := ⟨_, rfl⟩
  have hG : ∀ x, HasDerivAt G (T x) x := fun x => by
    rw [hGdef]; exact (hT.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hG0 : G 0 = 0 := by rw [hGdef]; exact intervalIntegral.integral_same
  have hlim : Tendsto (fun δ : ℝ => δ⁻¹ • G δ) (𝓝[≠] 0) (𝓝 1) := by
    have h := hasDerivAt_iff_tendsto_slope.mp (hG 0)
    rw [h0] at h
    refine h.congr' (Eventually.of_forall fun δ => ?_)
    simp [slope_def_module, hG0]
  obtain ⟨δ, hδu, hδ0⟩ :=
    ((hlim.eventually (Units.isOpen.mem_nhds isUnit_one)).and self_mem_nhdsWithin).exists
  have hδ : δ ≠ 0 := hδ0
  have hu : IsUnit (G δ) := by
    have e : G δ = algebraMap ℝ A δ * (δ⁻¹ • G δ) := by
      rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hδ, one_smul]
    rw [e]
    exact ((Ne.isUnit hδ).map (algebraMap ℝ A)).mul hδu
  have key : ∀ t, T t * G δ = G (t + δ) - G t := by
    intro t
    have h1 := (ContinuousLinearMap.mul ℝ A (T t)).intervalIntegral_comp_comm
      (hT.intervalIntegrable (μ := volume) 0 δ)
    simp only [ContinuousLinearMap.mul_apply'] at h1
    rw [hGdef]
    dsimp only
    rw [← h1, intervalIntegral.integral_interval_sub_left (hT.intervalIntegrable (μ := volume) _ _)
      (hT.intervalIntegrable (μ := volume) _ _)]
    simp_rw [← hadd]
    rw [intervalIntegral.integral_comp_add_left (fun x => T x) t, add_zero]
  have hform : T = fun t => (G (t + δ) - G t) * ↑hu.unit⁻¹ := by
    funext t
    rw [← key, mul_assoc, IsUnit.mul_val_inv, mul_one]
  rw [contDiff_infty]
  intro n
  induction n with
  | zero => exact contDiff_zero.mpr hT
  | succ n ih =>
    have hGn : ContDiff ℝ (n + 1 : ℕ) G := by
      rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_deriv]
      refine ⟨fun x => (hG x).differentiableAt, by simp, ?_⟩
      rwa [show deriv G = T from funext fun x => (hG x).deriv]
    rw [hform]
    exact ((hGn.comp (contDiff_id.add contDiff_const)).sub hGn).mul contDiff_const

end GlobalTheory
end

section

open MeasureTheory Metric Set
open scoped ContDiff

namespace GlobalTheory.SetIntegralSmoothness

theorem hasFDerivAt_setIntegral {X P E : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {a : X → E} (ha : Continuous a) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) (p₀ : P) :
    HasFDerivAt (fun p : P => ∫ x in K, Ψ (p, a x) ∂μ)
      (∫ x in K, (fderiv ℝ Ψ (p₀, a x)).comp (ContinuousLinearMap.inl ℝ P E) ∂μ) p₀ := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hΨ1 : ContDiff ℝ 1 Ψ := hΨ.of_le (by exact_mod_cast le_top)
  have hdΨ : Continuous (fderiv ℝ Ψ) := hΨ1.continuous_fderiv one_ne_zero
  have hS : IsCompact (closedBall p₀ 1 ×ˢ (a '' K)) := (isCompact_closedBall p₀ 1).prod (hK.image ha)
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hdΨ.continuousOn
  have hcont : ∀ p : P, Continuous fun x : X => Ψ (p, a x) :=
    fun p => hΨ.continuous.comp (continuous_const.prodMk ha)
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := μ.restrict K) (x₀ := p₀)
    (F := fun p x => Ψ (p, a x)) (F' := fun p x => (fderiv ℝ Ψ (p, a x)).comp (ContinuousLinearMap.inl ℝ P E))
    (bound := fun _ => C * ‖ContinuousLinearMap.inl ℝ P E‖)
    (closedBall_mem_nhds p₀ one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun p =>
      (hcont p).continuousOn.aestronglyMeasurable_of_isCompact hK hKm
  · exact (hcont p₀).continuousOn.integrableOn_compact hK
  · exact ((hdΨ.comp (continuous_const.prodMk ha)).clm_comp continuous_const).continuousOn.aestronglyMeasurable_of_isCompact hK hKm
  · refine (ae_restrict_iff' hKm).mpr (Filter.Eventually.of_forall fun x hx p hp => ?_)
    calc ‖(fderiv ℝ Ψ (p, a x)).comp (ContinuousLinearMap.inl ℝ P E)‖
        ≤ ‖fderiv ℝ Ψ (p, a x)‖ * ‖ContinuousLinearMap.inl ℝ P E‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ C * ‖ContinuousLinearMap.inl ℝ P E‖ :=
        mul_le_mul_of_nonneg_right (hC _ ⟨hp, mem_image_of_mem a hx⟩) (norm_nonneg _)
  · exact integrableOn_const hK.measure_ne_top
  · exact Filter.Eventually.of_forall fun x p _ =>
      ((hΨ1.differentiable one_ne_zero) (p, a x)).hasFDerivAt.comp p (hasFDerivAt_prodMk_left p (a x))

theorem contDiff_setIntegral {X P E : Type} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure X) [IsFiniteMeasureOnCompacts μ] {K : Set X} (hK : IsCompact K)
    {a : X → E} (ha : Continuous a) (m : ℕ) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (Ψ : P × E → F) (hΨ : ContDiff ℝ ∞ Ψ) :
    ContDiff ℝ (m : WithTop ℕ∞) (fun p : P => ∫ x in K, Ψ (p, a x) ∂μ) := by
  induction m generalizing F with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.mpr fun p₀ =>
      (hasFDerivAt_setIntegral μ hK ha Ψ hΨ p₀).continuousAt
  | succ m IH =>
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by norm_cast,
      contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun p => ∫ x in K, (fderiv ℝ Ψ (p, a x)).comp (ContinuousLinearMap.inl ℝ P E) ∂μ, ?_,
      fun p₀ => hasFDerivAt_setIntegral μ hK ha Ψ hΨ p₀⟩
    have hΨ' : ContDiff ℝ ∞ fun q : P × E => (fderiv ℝ Ψ q).comp (ContinuousLinearMap.inl ℝ P E) :=
      (hΨ.fderiv_right (m := ∞) (by simp)).clm_comp contDiff_const
    exact IH (fun q : P × E => (fderiv ℝ Ψ q).comp (ContinuousLinearMap.inl ℝ P E)) hΨ'

end GlobalTheory.SetIntegralSmoothness
end

section

noncomputable section

open Filter Topology MeasureTheory

namespace GlobalTheory.LocWeil.DerComm

theorem _root_.GlobalTheory.LocWeil.DerComm.differentiableAt_oneParameter {A : Type} [NormedRing A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (φ : ℝ → A) (hc : Continuous φ) (h0 : φ 0 = 1)
    (hm : ∀ s t : ℝ, φ (s + t) = φ s * φ t) : DifferentiableAt ℝ φ 0 := by
  have hφ := hc
  have hadd := hm
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > (0 : ℝ), ∀ s : ℝ, |s| ≤ δ → ‖1 - φ s‖ ≤ 1 / 2 := by
    obtain ⟨ε, hε, h⟩ := Metric.continuousAt_iff.mp hφ.continuousAt (1 / 2) (by norm_num)
    refine ⟨ε / 2, by positivity, fun s hs => ?_⟩
    have hs' : dist s 0 < ε := by
      rw [Real.dist_eq, sub_zero]; linarith
    have := h hs'
    rw [dist_eq_norm, h0, norm_sub_rev] at this
    exact this.le
  set E : A := δ⁻¹ • ∫ s in (0 : ℝ)..δ, (1 - φ s) with hE
  have hEn : ‖E‖ < 1 := by
    have hI : ‖∫ s in (0 : ℝ)..δ, (1 - φ s)‖ ≤ 1 / 2 * |δ - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro s hs
      rw [Set.uIoc_of_le hδ.le] at hs
      apply hball
      rw [abs_le]; constructor <;> linarith [hs.1, hs.2]
    rw [sub_zero, abs_of_pos hδ] at hI
    rw [hE, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hδ]
    calc δ⁻¹ * ‖∫ s in (0 : ℝ)..δ, (1 - φ s)‖ ≤ δ⁻¹ * (1 / 2 * δ) := by gcongr
      _ < 1 := by field_simp; norm_num
  set G : ℝ → A := fun x => ∫ s in (0 : ℝ)..x, φ s with hG
  have hint : ∀ t : ℝ, φ t * (1 - E) = δ⁻¹ • (G (t + δ) - G t) := by
    intro t
    have hC : 1 - E = δ⁻¹ • ∫ s in (0 : ℝ)..δ, φ s := by
      rw [hE, intervalIntegral.integral_sub intervalIntegrable_const (hφ.intervalIntegrable _ _),
        intervalIntegral.integral_const, smul_sub, sub_zero, smul_smul, inv_mul_cancel₀ hδ.ne',
        one_smul, sub_sub_cancel]
    rw [hC, mul_smul_comm, hG,
      intervalIntegral.integral_interval_sub_left (hφ.intervalIntegrable _ _)
        (hφ.intervalIntegrable _ _)]
    congr 1
    have key := (ContinuousLinearMap.mul ℝ A (φ t)).intervalIntegral_comp_comm
      (hφ.intervalIntegrable (μ := MeasureTheory.volume) 0 δ)
    simp only [ContinuousLinearMap.mul_apply'] at key
    rw [← key]
    simp_rw [← hadd]
    rw [intervalIntegral.integral_comp_add_left (fun s => φ s) t]
    simp [add_comm]
  set u : Aˣ := Units.oneSub E hEn with hu
  have hrep : φ = fun t => (δ⁻¹ • (G (t + δ) - G t)) * ↑u⁻¹ := by
    funext t
    rw [← hint t]
    have : (1 - E : A) = ↑u := by rw [hu, Units.val_oneSub]
    rw [this, Units.mul_inv_cancel_right]
  have hGd : ∀ x : ℝ, DifferentiableAt ℝ G x := fun x =>
    (hφ.integral_hasStrictDerivAt 0 x).hasDerivAt.differentiableAt
  rw [hrep]
  have h1 : DifferentiableAt ℝ (fun t => G (t + δ)) 0 :=
    (hGd (0 + δ)).comp (0 : ℝ) (differentiableAt_id.add_const δ)
  have h2 : DifferentiableAt ℝ (fun t => δ⁻¹ • (G (t + δ) - G t)) 0 :=
    by
      have h3 := (h1.sub (hGd 0)).const_smul δ⁻¹
      exact h3
  exact h2.mul_const _

section Alg

variable {S U : Type} [AddCommGroup S] [Module ℂ S]

variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]

variable (β : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) {ι : Type} [Fintype ι] (b b' : ι → U)

variable {β b b'}

variable {d : U →ₗ[ℝ] Module.End ℂ S} {κ : ℂ} {Y : U →ₗ[ℝ] U}

section Main

variable {Γ I : Type} [Group Γ] (ω : Γ →* Module.End ℂ S) (G : Γ →* (U →L[ℝ] U)) (ev : I → S →ₗ[ℂ] ℂ) {f : S}
  {N : Submodule ℂ S}
  (hβ : ∀ x, (∀ y, β x y = 0) → x = 0) (hs : ∀ x y, β y x = -β x y) (hκ : κ ≠ 0)
  (hd : ∀ u v, d u * d v - d v * d u = (κ * (β u v : ℝ)) • (1 : Module.End ℂ S))
  (hω : ∀ q u, ω q * d u = d (G q u) * ω q) (hG : ∀ q x y, β (G q x) (G q y) = β x y)
  (hN : ∀ Φ, Φ ∈ N ↔ ∃ a ∈ Algebra.adjoin ℂ (Set.range d), a f = Φ)
  (hvac : ∀ B ∈ Algebra.adjoin ℂ (Set.range d), (∀ u, B (d u f) = d u (B f)) → ∃ c : ℂ, B f = c • f)
  (hev : ∀ Φ Ψ, (∀ w, ev w Φ = ev w Ψ) → Φ = Ψ)
  (hline : ∀ w u, ∃ ℓ : ℝ → S →ₗ[ℂ] ℂ, ℓ 0 = ev w ∧ (∀ Ψ s, HasDerivAt (fun s => ℓ s Ψ) (ℓ s (d u Ψ)) s) ∧
    ∀ s, ∃ (c : ℂ) (w' : I), ∀ Ψ, ℓ s Ψ = c * ev w' Ψ)

end Main

end Alg

end GlobalTheory.LocWeil.DerComm

end
end
