module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ContinuousAevalMvPolynomial
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.RingTheory.Etale.Basic
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOpenPartialHomeomorphAnalytic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Basic.Complex.Basic
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
public import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Mathlib.Topology.Instances.Matrix
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
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Lemma
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.Bundle001
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Complex Matrix Filter Topology
open GlobalTheory.AffinePoints
open scoped BigOperators Real GlobalTheory.AffinePoints

namespace GlobalTheory


open AffinePoints in
theorem exists_testFunctions_subset_of_mem_nhds {A : Type*} [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] {e : A →ₐ[ℂ] ℂ} {U : Set (A →ₐ[ℂ] ℂ)} (hU : U ∈ 𝓝 e) :
    ∃ (n : ℕ) (f : Fin n → A) (ε : ℝ), 0 < ε ∧
      ∀ x : A →ₐ[ℂ] ℂ, (∀ k, ‖x (f k) - e (f k)‖ < ε) → x ∈ U := by
  obtain ⟨n, p, hp⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹Algebra.FiniteType ℂ A›
  rw [(isClosedEmbedding_coords (C := ℂ) p hp).isInducing.nhds_eq_comap, mem_comap] at hU
  obtain ⟨V, hV, hVU⟩ := hU
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨n, fun k => p (MvPolynomial.X k), ε, hε, fun x hx => hVU (hb ?_)⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro k
  rw [dist_eq_norm]
  exact hx k


open AffinePoints in
theorem exists_holomorphic_section_of_etale :
    (∀ (g : ℕ) (A : Type) [CommRing A] [Algebra ℂ A] [Algebra (MvPolynomial (Fin g) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin g) ℂ) A] [Algebra.Etale (MvPolynomial (Fin g) ℂ) A] (e : A →ₐ[ℂ] ℂ), (∀ i, e (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = 0) → ∃ (W : Set (Fin g → ℂ)) (σ : (Fin g → ℂ) → (A →ₐ[ℂ] ℂ)) (n : ℕ) (f : Fin n → A) (ε : ℝ), IsOpen W ∧ 0 ∈ W ∧ σ 0 = e ∧ 0 < ε ∧ (∀ a, DifferentiableOn ℂ (fun w => σ w a) W) ∧ (∀ w ∈ W, ∀ i, σ w (algebraMap (MvPolynomial (Fin g) ℂ) A (MvPolynomial.X i)) = w i) ∧ ∀ x : A →ₐ[ℂ] ℂ, (∀ k, ‖x (f k) - e (f k)‖ < ε) → ∃ w ∈ W, x = σ w) := by
  intro g A _ _ _ _ _ e he
  let φ : MvPolynomial (Fin g) ℂ →ₐ[ℂ] A := IsScalarTower.toAlgHom ℂ _ A
  have hφ : φ.Etale := RingHom.etale_algebraMap.2 inferInstance
  have : Algebra.FiniteType ℂ A :=
    Algebra.FiniteType.trans (S := MvPolynomial (Fin g) ℂ) inferInstance inferInstance
  obtain ⟨c, hc, hcφ, han⟩ := exists_chart_of_etale φ hφ e
  have h0 : c e = 0 := by rw [hcφ]; ext i; exact he i
  obtain ⟨n, f, ε, hε, hf⟩ := exists_testFunctions_subset_of_mem_nhds (c.open_source.mem_nhds hc)
  refine ⟨c.target, c.symm, n, f, ε, c.open_target, h0 ▸ c.map_source hc, ?_, hε,
    fun a => (han a).differentiableOn, fun w hw i => ?_, fun x hx => ?_⟩
  · rw [← h0, c.left_inv hc]
  · have := c.right_inv hw
    rw [hcφ] at this
    exact congrFun this i
  · exact ⟨c x, c.map_source (hf x hx), (c.left_inv (hf x hx)).symm⟩

end GlobalTheory
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

theorem isReduced_scheme_of_smooth_of_isIntegrallyClosed (T : Type) [CommRing T] [IsDomain T]
    [IsIntegrallyClosed T] {X : Scheme.{0}} (f : X ⟶ Sp T) [Smooth f] :
    AlgebraicGeometry.IsReduced X := by
  have hT : GlobalTheory.IsNormalScheme (Sp T) := inferInstance
  have hX : GlobalTheory.IsNormalScheme X := (isNormalScheme_iff X).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth f ((isNormalScheme_iff _).mp hT))
  infer_instance

theorem isReduced_of_smooth_complex :
    (∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ), Smooth p → IsReduced X) :=
  fun _ p _ ↦ isReduced_scheme_of_smooth_of_isIntegrallyClosed ℂ p

end GlobalTheory
end

section

open Complex Matrix ReciprocityTheory.PTheta

noncomputable section

namespace GlobalTheory

variable {ι : Type*} [Fintype ι]

open Complex Matrix in
variable {ι : Type*} [Fintype ι] in
private lemma im_quadForm_pos_of_mem_thetaDomain {τ : Matrix ι ι ℂ} (hτ : τ ∈ _root_.ReciprocityTheory.PTheta.ThetaDomain ι)
    (x : ι → ℝ) (hx : x ≠ 0) : 0 < x ⬝ᵥ τ.map Complex.im *ᵥ x := by
  have h : ((τ.map Complex.im) + (τ.map Complex.im).transpose).PosDef := by
    unfold _root_.ReciprocityTheory.PTheta.ThetaDomain at hτ
    exact hτ
  have h1 : x ⬝ᵥ (τ.map Complex.im)ᵀ *ᵥ x = x ⬝ᵥ τ.map Complex.im *ᵥ x := by
    rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
  have h2 := h.dotProduct_mulVec_pos hx
  rw [add_mulVec, dotProduct_add, star_trivial, h1] at h2
  linarith

open Complex Matrix in
variable {ι : Type*} [Fintype ι] in
private lemma exists_uniform_im_quadForm_lower_bound_on_compact {K : Set ((ι → ℂ) × (ι → ι → ℂ))}
    (hK : IsCompact K) (hKd : ∀ p ∈ K, Matrix.of p.2 ∈ _root_.ReciprocityTheory.PTheta.ThetaDomain ι) :
    ∃ c > 0, ∀ p ∈ K, ∀ x : ι → ℝ,
      c * x ⬝ᵥ x ≤ x ⬝ᵥ (Matrix.of p.2).map Complex.im *ᵥ x := by
  classical
  set g : ((ι → ℂ) × (ι → ι → ℂ)) × (ι → ℝ) → ℝ :=
    fun q => q.2 ⬝ᵥ (Matrix.of q.1.2).map Complex.im *ᵥ q.2 with hg_def
  have hg : Continuous g := by
    simp only [hg_def, dotProduct, mulVec, Matrix.map_apply, Matrix.of_apply]
    fun_prop
  have hS : IsCompact (K ×ˢ Metric.sphere (0 : ι → ℝ) 1) := hK.prod (isCompact_sphere 0 1)
  rcases (K ×ˢ Metric.sphere (0 : ι → ℝ) 1).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun p hp x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    · exfalso
      have hmem : (p, ‖x‖⁻¹ • x) ∈ K ×ˢ Metric.sphere (0 : ι → ℝ) 1 :=
        ⟨hp, by simp [norm_smul, hx]⟩
      rw [he] at hmem
      exact hmem
  · obtain ⟨q, hq, hmin⟩ := hS.exists_isMinOn hne hg.continuousOn
    have hq0 : q.2 ≠ 0 := by
      intro h
      have := hq.2
      simp [h] at this
    have hm : 0 < g q := im_quadForm_pos_of_mem_thetaDomain (hKd q.1 hq.1) q.2 hq0
    refine ⟨g q / (Fintype.card ι + 1), by positivity, fun p hp x => ?_⟩
    by_cases hx : x = 0
    · subst hx; simp
    have ht : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have h1 : g q ≤ g (p, ‖x‖⁻¹ • x) := hmin ⟨hp, by simp [norm_smul, ht.ne']⟩
    have h2 : g (p, ‖x‖⁻¹ • x) =
        ‖x‖⁻¹ ^ 2 * (x ⬝ᵥ (Matrix.of p.2).map Complex.im *ᵥ x) := by
      simp only [hg_def, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      ring
    have h3 : x ⬝ᵥ x ≤ Fintype.card ι * ‖x‖ ^ 2 := by
      simp only [dotProduct]
      calc ∑ i, x i * x i ≤ ∑ _i : ι, ‖x‖ ^ 2 := Finset.sum_le_sum fun i _ => by
            have := norm_le_pi_norm x i
            rw [Real.norm_eq_abs] at this
            nlinarith [abs_nonneg (x i), abs_mul_abs_self (x i)]
        _ = _ := by simp
    set Q := x ⬝ᵥ (Matrix.of p.2).map Complex.im *ᵥ x
    have h4 : g q * ‖x‖ ^ 2 ≤ Q := by
      rw [h2] at h1
      calc g q * ‖x‖ ^ 2 ≤ ‖x‖⁻¹ ^ 2 * Q * ‖x‖ ^ 2 := by gcongr
        _ = Q := by field_simp
    have hxx : 0 ≤ x ⬝ᵥ x := by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
    calc g q / (Fintype.card ι + 1) * (x ⬝ᵥ x)
        ≤ g q / (Fintype.card ι + 1) * (Fintype.card ι * ‖x‖ ^ 2) := by gcongr
      _ ≤ g q * ‖x‖ ^ 2 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [mul_nonneg hm.le (sq_nonneg ‖x‖)]
      _ ≤ Q := h4


open Complex Matrix in
variable {ι : Type*} [Fintype ι] in
theorem _root_.GlobalTheory.thetaMTest_holds : _root_.ReciprocityTheory.PTheta.ThetaMTestStatement := by
  unfold _root_.ReciprocityTheory.PTheta.ThetaMTestStatement
  intro ι _ a K hK hKd
  obtain ⟨c, hc, hcK⟩ := exists_uniform_im_quadForm_lower_bound_on_compact hK hKd
  obtain ⟨S, hS⟩ := hK.exists_bound_of_continuousOn (f := fun p => p.1) continuous_fst.continuousOn
  refine ⟨_root_.GlobalTheory.riemannThetaBound a c S, _root_.GlobalTheory.summable_riemannThetaBound a hc S,
    fun b p hp l => ?_⟩
  exact _root_.GlobalTheory.norm_riemannThetaTerm_le a b (hcK p hp)
    (fun i => (_root_.GlobalTheory.abs_im_apply_le_norm p.1 i).trans (hS p hp)) l


open Complex Matrix in
variable {ι : Type*} [Fintype ι] in
theorem _root_.GlobalTheory.thetaSummable_holds : _root_.ReciprocityTheory.PTheta.ThetaSummableStatement := by
  have hM := _root_.GlobalTheory.thetaMTest_holds
  unfold _root_.ReciprocityTheory.PTheta.ThetaMTestStatement at hM
  unfold _root_.ReciprocityTheory.PTheta.ThetaSummableStatement
  intro ι _ a b z τ hτ
  obtain ⟨u, hu, hbound⟩ := hM ι a {(z, (τ : ι → ι → ℂ))} isCompact_singleton
    (fun p hp => by
      obtain rfl : p = (z, (τ : ι → ι → ℂ)) := hp
      exact hτ)
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun l => hbound b _ (Set.mem_singleton _) l) hu


open Complex Matrix in
variable {ι : Type*} [Fintype ι] in
theorem _root_.GlobalTheory.thetaMTest_and_thetaSummable : _root_.ReciprocityTheory.PTheta.ThetaMTestStatement ∧ _root_.ReciprocityTheory.PTheta.ThetaSummableStatement :=
  ⟨_root_.GlobalTheory.thetaMTest_holds, _root_.GlobalTheory.thetaSummable_holds⟩

end GlobalTheory
end
end

section

open ReciprocityTheory.PTheta

namespace GlobalTheory

theorem differentiable_thetaTerm_prod {ι : Type} [Fintype ι] (a b : ι → ℝ) (l : ι → ℤ) :
    Differentiable ℂ
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => thetaTerm a b p.1 (Matrix.of p.2) l) := by
  unfold thetaTerm eC
  simp only [dotProduct, Matrix.mulVec, shiftVec, ofRealVec, Pi.add_apply, Matrix.of_apply]
  fun_prop

theorem differentiableOn_theta_prod_of_normal {ι : Type} [Fintype ι] (a b : ι → ℝ)
    {U : Set ((ι → ℂ) × (ι → ι → ℂ))} (hU : IsOpen U)
    (hle : ∀ K ⊆ U, IsCompact K → ∃ u : (ι → ℤ) → ℝ, Summable u ∧
      ∀ l, ∀ p ∈ K, ‖thetaTerm a b p.1 (Matrix.of p.2) l‖ ≤ u l) :
    DifferentiableOn ℂ
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => theta a b p.1 (Matrix.of p.2)) U := by
  intro c hc
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU c hc
  have hK : Metric.closedBall c (ε / 2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨u, hu, hbd⟩ := hle _ hK (isCompact_closedBall c (ε / 2))
  have hr : (0 : ℝ) < ε / 4 := by positivity
  have hlim : TendstoUniformlyOn
      (fun s : Finset (ι → ℤ) => fun p : (ι → ℂ) × (ι → ι → ℂ) =>
        ∑ l ∈ s, thetaTerm a b p.1 (Matrix.of p.2) l)
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => theta a b p.1 (Matrix.of p.2)) Filter.atTop
      (Metric.ball c (2 * (ε / 4))) := by
    have h := tendstoUniformlyOn_tsum hu (fun l p hp => hbd l p hp)
    refine h.mono ?_
    intro p hp
    exact Metric.ball_subset_closedBall (by simpa [show 2 * (ε / 4) = ε / 2 by ring] using hp)
  have hF : ∀ᶠ s : Finset (ι → ℤ) in Filter.atTop, DifferentiableOn ℂ
      (fun p : (ι → ℂ) × (ι → ι → ℂ) => ∑ l ∈ s, thetaTerm a b p.1 (Matrix.of p.2) l)
      (Metric.ball c (2 * (ε / 4))) :=
    Filter.Eventually.of_forall fun s => by
      have h := Differentiable.sum (u := s) fun l _ => differentiable_thetaTerm_prod a b l
      have e : (fun p : (ι → ℂ) × (ι → ι → ℂ) => ∑ l ∈ s, thetaTerm a b p.1 (Matrix.of p.2) l) =
          ∑ l ∈ s, fun p : (ι → ℂ) × (ι → ι → ℂ) => thetaTerm a b p.1 (Matrix.of p.2) l := by
        funext p
        rw [Finset.sum_apply]
      rw [e]
      exact h.differentiableOn
  have hd := (GlobalTheory.SCV.tendstoUniformlyOn_fderiv_ball hlim hF).1
  exact (hd.differentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableWithinAt

theorem thetaHolo_of_domainOpen_of_mTest (hopen : DomainOpenStatement)
    (hM : ThetaMTestStatement) : ThetaHoloStatement := by
  intro ι _ a b
  refine differentiableOn_theta_prod_of_normal a b ((hopen ι).preimage continuous_snd) ?_
  intro K hKU hK
  obtain ⟨u, hu, hbd⟩ := hM ι a K hK (fun p hp => hKU hp)
  exact ⟨u, hu, fun l p hp => hbd b p hp l⟩

end GlobalTheory
end

section

open Complex Matrix Filter Topology ReciprocityTheory.PTheta

namespace GlobalTheory

variable {ι : Type*} [Fintype ι]

theorem siegelH_subset_thetaDomain : SiegelH ι ⊆ ThetaDomain ι := by
  intro τ hτ
  obtain ⟨hs, hp⟩ := hτ
  have ht : (τ.map Complex.im)ᵀ = τ.map Complex.im := by
    rw [← Matrix.transpose_map, hs.eq]
  show (τ.map Complex.im + (τ.map Complex.im)ᵀ).PosDef
  rw [ht]
  exact hp.add hp

theorem isOpen_thetaDomain : IsOpen (ThetaDomain ι) := by
  set S : Matrix ι ι ℂ → Matrix ι ι ℝ :=
    fun τ => τ.map Complex.im + (τ.map Complex.im)ᵀ with hS
  have hherm : ∀ τ, (S τ).IsHermitian := by
    intro τ
    ext i j
    simp [hS, add_comm]
  have hscale : ∀ τ (c : ℝ) (x : ι → ℝ),
      (c • x) ⬝ᵥ (S τ *ᵥ (c • x)) = c * c * (x ⬝ᵥ (S τ *ᵥ x)) := by
    intro τ c x
    simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
    ring
  have key : ∀ τ, τ ∈ ThetaDomain ι ↔
      ∀ x ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < x ⬝ᵥ (S τ *ᵥ x) := by
    intro τ
    change (S τ).PosDef ↔ _
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    simp only [star_trivial]
    constructor
    · rintro ⟨-, h⟩ x hx
      apply h
      rintro rfl
      simp at hx
    · intro h
      refine ⟨hherm τ, fun x hx => ?_⟩
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hy : ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by
        rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ hn.ne']
      have h1 := h _ hy
      rw [hscale] at h1
      by_contra hle
      have : ‖x‖⁻¹ * ‖x‖⁻¹ * (x ⬝ᵥ (S τ *ᵥ x)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) (not_lt.mp hle)
      linarith
  have hcont : Continuous fun p : Matrix ι ι ℂ × (ι → ℝ) => p.2 ⬝ᵥ (S p.1 *ᵥ p.2) := by
    have hm : Continuous fun p : Matrix ι ι ℂ × (ι → ℝ) => p.1.map Complex.im :=
      continuous_fst.matrix_map Complex.continuous_im
    exact continuous_snd.dotProduct ((hm.add hm.matrix_transpose).matrix_mulVec continuous_snd)
  rw [isOpen_iff_eventually]
  intro τ₀ h₀
  have hev : ∀ᶠ τ in 𝓝 τ₀, ∀ x ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < x ⬝ᵥ (S τ *ᵥ x) := by
    refine (isCompact_sphere (0 : ι → ℝ) 1).eventually_forall_of_forall_eventually
      (P := fun τ x => 0 < x ⬝ᵥ (S τ *ᵥ x)) fun x hx => ?_
    exact (hcont.continuousAt (x := (τ₀, x))).eventually (lt_mem_nhds ((key τ₀).1 h₀ x hx))
  filter_upwards [hev] with τ hτ
  exact (key τ).2 hτ

theorem siegelSubDomain_and_domainOpen : SiegelSubDomainStatement ∧ DomainOpenStatement := by
  refine ⟨fun κ _ => siegelH_subset_thetaDomain, fun κ _ => ?_⟩
  exact isOpen_thetaDomain

end GlobalTheory
end
