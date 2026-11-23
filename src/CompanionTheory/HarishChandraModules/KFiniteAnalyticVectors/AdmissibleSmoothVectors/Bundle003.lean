module

public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle002
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle001
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

@[expose] public section

section

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.admitted

section

variable {K : Type} [Group K] [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {μ : Measure K} [IsFiniteMeasure μ]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : K →* (H →L[ℂ] H)}

theorem integrable_cont {F : Type} [NormedAddCommGroup F] {f : K → F} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem exists_avg (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (hc : ∀ v, Continuous fun x => σ x v) {e : K → ℂ}
    (he : Continuous e) : ∃ E : H →L[ℂ] H, ∀ u, E u = ∫ k, e k • σ k u ∂μ := by
  let L : H →ₗ[ℂ] H :=
    { toFun := fun u => ∫ k, e k • σ k u ∂μ
      map_add' := fun u w => by
        simp only [map_add (f := _), smul_add]
        exact integral_add (integrable_cont (he.smul (hc u))) (integrable_cont (he.smul (hc w)))
      map_smul' := fun c u => by
        simp only [map_smul, RingHom.id_apply, smul_comm _ c]
        exact integral_smul _ _ }
  refine ⟨L.mkContinuous (∫ k, ‖e k‖ ∂μ) fun u => ?_, fun u => rfl⟩
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_smul, hiso]
  exact integral_mul_const _ _

end

theorem exists_averaging_operator : ExistsAvg := by
  intro K _ _ _ _ _ _ _ _ μ _ _ H _ _ _ σ hiso hc S _ hS v hv
  have hcoef : ∀ a b : H, Continuous fun x => ⟪σ x a, b⟫_ℂ := fun a b => (hc a).inner continuous_const
  have hint : ∀ b : H, Integrable (fun x => ⟪σ x v, b⟫_ℂ • σ x v) μ := fun b =>
    integrable_cont ((hcoef v b).smul (hc v))
  have hScl : CompleteSpace S := FiniteDimensional.complete ℂ S

  let L : H →ₗ[ℂ] H :=
    { toFun := fun b => ∫ x, ⟪σ x v, b⟫_ℂ • σ x v ∂μ
      map_add' := fun a b => by
        simp only [inner_add_right, add_smul]
        exact integral_add (hint a) (hint b)
      map_smul' := fun c b => by
        simp only [inner_smul_right, RingHom.id_apply, mul_smul]
        exact integral_smul _ _ }
  have hinner : ∀ w b, ⟪w, L b⟫_ℂ = ∫ x, ⟪σ x v, b⟫_ℂ * ⟪w, σ x v⟫_ℂ ∂μ := by
    intro w b
    change ⟪w, ∫ x, ⟪σ x v, b⟫_ℂ • σ x v ∂μ⟫_ℂ = _
    rw [← integral_inner (hint b)]
    simp only [inner_smul_right]
  have hLS : ∀ b, L b ∈ S := by
    intro b
    rw [← Submodule.orthogonal_orthogonal S, Submodule.mem_orthogonal]
    intro w hw
    rw [hinner]
    have : ∀ x, ⟪w, σ x v⟫_ℂ = 0 := fun x => Submodule.inner_left_of_mem_orthogonal (hS x v hv) hw
    simp [this]
  have hzero : ∀ w, ⟪w, L w⟫_ℂ = 0 → ⟪w, v⟫_ℂ = 0 := by
    intro w hw
    rw [hinner] at hw
    have e1 : ∀ x, ⟪σ x v, w⟫_ℂ * ⟪w, σ x v⟫_ℂ = ((‖⟪σ x v, w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro x
      rw [← inner_conj_symm w, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [e1] at hw
    rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at hw
    have hcont : Continuous fun x => ‖⟪σ x v, w⟫_ℂ‖ ^ 2 := (hcoef v w).norm.pow 2
    have h1 := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) (integrable_cont hcont)).1 hw
    have h2 : ‖⟪σ 1 v, w⟫_ℂ‖ ^ 2 = 0 := congrFun ((hcont.ae_eq_iff_eq μ continuous_const).1 h1) 1
    simp only [map_one, ContinuousLinearMap.one_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, norm_eq_zero] at h2
    exact inner_eq_zero_symm.1 h2
  set R : Submodule ℂ H := S.map L with hR
  have hRc : CompleteSpace R := FiniteDimensional.complete ℂ R
  have hvR : v ∈ R := by
    set w := v - R.starProjection v with hw
    have hwo : w ∈ Rᗮ := R.sub_starProjection_mem_orthogonal v
    have hp : R.starProjection v ∈ R := R.starProjection_apply_mem v
    have hRS : R ≤ S := by rintro _ ⟨b, -, rfl⟩; exact hLS b
    have hwS : w ∈ S := S.sub_mem hv (hRS hp)
    have h1 : ⟪w, v⟫_ℂ = 0 := hzero w (Submodule.inner_left_of_mem_orthogonal (K := R) (Submodule.mem_map_of_mem hwS) hwo)
    have h2 : ⟪w, R.starProjection v⟫_ℂ = 0 := Submodule.inner_left_of_mem_orthogonal hp hwo
    have h3 : ⟪w, w⟫_ℂ = 0 := by
      conv_lhs => rw [hw, inner_sub_right, ← hw]
      rw [h1, h2, sub_zero]
    rw [inner_self_eq_zero, hw, sub_eq_zero] at h3
    rw [h3]; exact hp
  obtain ⟨b, -, hb⟩ := hvR
  obtain ⟨E, hE⟩ := exists_avg (μ := μ) hiso hc (hcoef v b)
  refine ⟨fun x => ⟪σ x v, b⟫_ℂ, E, hcoef v b, ?_, hE, by rw [hE]; exact hb⟩
  let B := Module.finBasis ℂ S
  refine ⟨fun i x => ⟪σ x (B i), b⟫_ℂ, fun i => hcoef _ b, fun k => ?_⟩
  refine ⟨fun i => (starRingEnd ℂ) (B.repr ⟨σ k⁻¹ v, hS _ v hv⟩ i), fun x => ?_⟩
  have e1 : σ k⁻¹ v = ∑ i, B.repr ⟨σ k⁻¹ v, hS _ v hv⟩ i • (B i : H) := by
    have := congrArg Subtype.val (B.sum_repr ⟨σ k⁻¹ v, hS _ v hv⟩)
    rw [Submodule.coe_sum] at this
    exact this.symm
  show ⟪σ (x * k⁻¹) v, b⟫_ℂ = _
  rw [map_mul, ContinuousLinearMap.mul_apply]
  conv_lhs => rw [e1]

  simp only [map_sum, map_smul, sum_inner, inner_smul_left]

end CompanionTheory.D.gk.admitted
end
end

section

noncomputable section

namespace CompanionTheory.D.gk.admitted

theorem std_eq_zero {A : Type} [Ring A] [Algebra ℂ A] [Module.Finite ℂ A] {M : ℕ} (hM : Module.finrank ℂ A < M)
    (b : Fin M → A) :
    ∑ π : Equiv.Perm (Fin M), ((Equiv.Perm.sign π : ℤ) : A) * (List.ofFn fun i => b (π i)).prod = 0 := by
  have hdep : ¬ LinearIndependent ℂ b := fun h => by
    have := h.fintype_card_le_finrank
    rw [Fintype.card_fin] at this
    omega
  have h := (MultilinearMap.alternatization (MultilinearMap.mkPiAlgebraFin ℂ M A)).map_linearDependent b hdep
  rw [MultilinearMap.alternatization_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [MultilinearMap.domDomCongr_apply, MultilinearMap.mkPiAlgebraFin_apply, Units.smul_def, zsmul_eq_mul]

theorem small_irreducible_representation : SmallPI := by
  intro V _ _ W Y _ hYW E hE M hM a ha w hw
  let b : Fin M → Module.End ℂ Y := fun i =>
    (E * a i).restrict (p := Y) (q := Y) fun y hy => hE _ (ha i y (hYW hy))
  have hb : ∀ l : List (Fin M), word E (l.map a) w = (((l.map b).prod ⟨E w, hE w hw⟩ : Y) : V) := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih =>
      rw [List.map_cons, word_cons, Module.End.mul_apply, ih, List.map_cons, List.prod_cons, Module.End.mul_apply]
      rfl
  have hdim : Module.finrank ℂ (Module.End ℂ Y) < M := by
    rw [Module.finrank_linearMap, ← sq]; exact hM
  have h0 := congrArg (fun T : Module.End ℂ Y => ((T ⟨E w, hE w hw⟩ : Y) : V)) (std_eq_zero hdim b)
  simp only [LinearMap.sum_apply, Submodule.coe_sum, LinearMap.zero_apply, Submodule.coe_zero] at h0
  rw [← h0, stdPoly, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun π _ => ?_
  have e1 : (List.ofFn fun i => a (π i)) = (List.ofFn π).map a := by rw [List.map_ofFn]; rfl
  have e2 : (List.ofFn fun i => b (π i)) = (List.ofFn π).map b := by rw [List.map_ofFn]; rfl
  rw [e1, e2, Module.End.mul_apply, Module.End.mul_apply, hb, Module.End.intCast_apply, Module.End.intCast_apply,
    Submodule.coe_smul_of_tower]

end CompanionTheory.D.gk.admitted
end
end

section

open MeasureTheory Matrix Topology Set Filter
open scoped ContDiff

noncomputable section

namespace CompanionTheory.D.gk.admitted

open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Gard

theorem contDiff_integral_comp {P Q E α : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace α] [T2Space α] [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasureOnCompacts μ] (Φ : P × Q → E) (hΦ : ContDiff ℝ ∞ Φ) (q : α → Q)
    (hq : Continuous q)
    (hsupp : ∀ y₀ : P, ∃ U ∈ 𝓝 y₀, ∃ C : Set α, IsCompact C ∧ ∀ y ∈ U, ∀ a ∉ C, Φ (y, q a) = 0) :
    ContDiff ℝ ∞ fun y => ∫ a, Φ (y, q a) ∂μ := by
  refine GroundTheory.Automorphic.contDiff_integral_of_iteratedFDeriv (μ := μ) (fun y a => Φ (y, q a))
    (fun a => hΦ.comp (contDiff_id.prodMk contDiff_const)) (fun k => ?_) hsupp
  have h : Continuous fun p : P × α => (p.1, q p.2) := continuous_fst.prodMk (hq.comp continuous_snd)
  exact (continuous_iter_partial Φ hΦ k).comp h

variable {n : ℕ} {ε : Fin n → Bool}

theorem toM_mul (x y : UJ ε) : toM (x * y) = toM x * toM y := rfl

theorem toM_one : toM (1 : UJ ε) = 1 := rfl

theorem emb_toM : IsClosedEmbedding (toM : UJ ε → Matrix (Fin n) (Fin n) ℂ) := (isClosedEmbeddingMatrix n ε).1

theorem toM_mem (x : UJ ε) : toM x ∈ UJset ε := x.2

theorem exists_toM {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : ∃ x : UJ ε, toM x = g := by
  have : g ∈ Set.range (coeMatrixAlt ε) := by rw [range_coeMatrix]; exact hg
  exact this

theorem inUJ_of_mem_Kset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : inUJ ε k := by
  have h1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
  unfold inUJ
  rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem toM_inv_of_unitary {k : UJ ε} (hk : toM k ∈ Matrix.unitaryGroup (Fin n) ℂ) : toM k⁻¹ = (toM k)ᴴ :=
  Units.inv_eq_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff.1 hk)

theorem contDiff_Phi {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : Matrix (Fin n) (Fin n) ℂ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => f (p.2.1 * p.1) • p.2.2 := by
  have h1 : ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => (p.2.1, p.1) :=
    contDiff_snd.fst.prodMk contDiff_fst
  have h2 : ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => p.2.1 * p.1 := by
    have := contDiff_mul.comp h1
    simpa only [Function.comp_def] using this
  have h3 : ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => f (p.2.1 * p.1) :=
    hf.comp h2
  exact h3.smul contDiff_snd.snd

theorem supp_local {f : Matrix (Fin n) (Fin n) ℂ → ℝ} {S : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hS : IsCompact S) (hd : ∀ B ∈ S, B.det ≠ 0) (hfS : ∀ y, f y ≠ 0 → y ∈ S) (g₀ : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U ∈ 𝓝 g₀, ∃ C : Set (UJ ε), IsCompact C ∧ ∀ g ∈ U, ∀ x ∉ C, f (toM x⁻¹ * g) = 0 := by
  refine ⟨Metric.closedBall g₀ 1, Metric.closedBall_mem_nhds _ one_pos, _,
    emb_toM.isCompact_preimage (isCompact_mul_inv (isCompact_closedBall g₀ 1) hS hd), fun g hg x hx => ?_⟩
  by_contra h
  have hB := hfS _ h
  refine hx ⟨(g, toM x⁻¹ * g), ⟨hg, hB⟩, ?_⟩
  have hu : IsUnit (toM x⁻¹ * g).det := isUnit_iff_ne_zero.2 (hd _ hB)
  have e : g = toM x * (toM x⁻¹ * g) := by
    rw [← Matrix.mul_assoc, ← toM_mul, mul_inv_cancel, toM_one, Matrix.one_mul]
  show g * (toM x⁻¹ * g)⁻¹ = toM x
  calc g * (toM x⁻¹ * g)⁻¹ = toM x * (toM x⁻¹ * g) * (toM x⁻¹ * g)⁻¹ := by rw [← e]
    _ = toM x := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem contDiff_avg {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (v : UJ ε → H) (hv : Continuous v) {f : Matrix (Fin n) (Fin n) ℂ → ℝ} {S : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hf : ContDiff ℝ ∞ f) (hS : IsCompact S) (hd : ∀ B ∈ S, B.det ≠ 0) (hfS : ∀ y, f y ≠ 0 → y ∈ S) :
    ContDiff ℝ ∞ fun g : Matrix (Fin n) (Fin n) ℂ => ∫ x : UJ ε, f (toM x⁻¹ * g) • v x ∂(muG ε) := by
  have hq : Continuous fun x : UJ ε => (toM x⁻¹, v x) := (emb_toM.continuous.comp continuous_inv).prodMk hv
  have key := contDiff_integral_comp (muG ε) _ (contDiff_Phi (H := H) hf) _ hq fun g₀ => by
    obtain ⟨U, hU, C, hC, h⟩ := supp_local (ε := ε) hS hd hfS g₀
    refine ⟨U, hU, C, hC, fun g hg x hx => ?_⟩
    simp only [h g hg x hx, zero_smul]
  simpa only using key

end Gard


open Gard in
theorem garding_finite_smooth_vectors : GardingFin := by
  open scoped Pointwise in
  intro n ε H _ _ _ σ hσ Y _ hY v hv
  obtain ⟨⟨h1, hm⟩, hiso, hcont⟩ := hσ
  let ρ : UJ ε → H →L[ℂ] H := fun x => σ (toM x)
  have hρ : ∀ u, Continuous fun x => ρ x u := fun u =>
    (hcont u).comp_continuous emb_toM.continuous toM_mem
  have hmul : ∀ x y u, ρ (x * y) u = ρ x (ρ y u) := fun x y u => by
    simp only [ρ, toM_mul, hm _ (toM_mem x) _ (toM_mem y), ContinuousLinearMap.comp_apply]
  have hρ1 : ∀ u, ρ 1 u = u := fun u => by simp only [ρ, toM_one, h1, one_apply_eq_self]
  obtain ⟨V, hV, hclose⟩ := exists_nhds_close ρ hρ hρ1 Y
  have hVi : V⁻¹ ∈ 𝓝 (1 : UJ ε) := inv_mem_nhds_one _ hV
  rw [emb_toM.isInducing.nhds_eq_comap, mem_comap] at hVi
  obtain ⟨W, hW, hWV⟩ := hVi
  have hD : {y : Matrix (Fin n) (Fin n) ℂ | y.det ≠ 0} ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ) :=
    (isOpen_ne_fun continuous_id.matrix_det continuous_const).mem_nhds (by simp)
  obtain ⟨f, S, hf, hf0, hf1, hS, hSW, hfS, hfk⟩ := exists_bump (inter_mem hW hD)
  let w : UJ ε → ℝ := fun x => f (toM x⁻¹)
  have hw : Continuous w := hf.continuous.comp (emb_toM.continuous.comp continuous_inv)
  have hc : HasCompactSupport w := by
    refine HasCompactSupport.intro (emb_toM.isCompact_preimage hS).inv fun x hx => ?_
    by_contra h
    exact hx (hfS _ h)
  have h0 : 0 ≤ w := fun x => hf0 _
  have hw1 : w 1 ≠ 0 := by simpa only [w, inv_one, toM_one] using hf1
  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring (muG ε) ρ hρ (fun x u => hiso _ (toM_mem x) u) hw hc
  have hTK : ∀ k ∈ Kset ε, ∀ u, T (σ k u) = σ k (T u) := by
    intro k hk u
    obtain ⟨k', rfl⟩ := exists_toM (inUJ_of_mem_Kset hk)
    rw [hT, hT]
    refine T_comm (muG ε) ρ hρ hmul hw hc h0 hw1 k' (fun x => ?_) u
    simp only [w, _root_.mul_inv_rev, inv_inv]
    rw [← mul_assoc, toM_mul, toM_mul, toM_inv_of_unitary hk.1, hfk _ hk.1]
  have hinj : ∀ y ∈ Y, T y = 0 → y = 0 := by
    intro y hy hTy
    rw [hT] at hTy
    refine eq_zero_of_alt_alt (muG ε) ρ hρ hw hc h0 hw1 y (fun x hx => hclose x ?_ y hy) hTy
    have : x⁻¹ ∈ V⁻¹ := hWV (hSW (hfS _ hx)).1
    simpa using this
  obtain ⟨u, rfl⟩ := exists_preimage Y T (hY T hTK) hinj v hv
  intro g₀ _
  refine ⟨univ, fun g => ∫ x : UJ ε, f (toM x⁻¹ * g) • ρ x u ∂(muG ε), isOpen_univ, mem_univ _,
    (contDiff_avg (fun x => ρ x u) (hρ u) hf hS (fun B hB => (hSW hB).2) hfS).contDiffOn, fun g _ hg => ?_⟩
  obtain ⟨g', rfl⟩ := exists_toM (ε := ε) hg
  show ρ g' (T u) = _
  rw [hT, apply_alt (muG ε) ρ hρ hmul hw hc]
  simp only [w, _root_.mul_inv_rev, inv_inv, toM_mul]

end CompanionTheory.D.gk.admitted
end
end
