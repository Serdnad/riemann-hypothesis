module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle084
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle085
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelOpenMapping
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle083
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle046
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle063
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle065
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle088
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Nullstellensatz
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem UniformiserGradientIndependent.proof (hjac : NormalCurveJacobian.Statement)
    (hdvr : NormalCurvePointDVR.Statement) : UniformiserGradientIndependent.Statement := by
  intro σ _ I w t hI hic hdim hw ht
  obtain ⟨k, f, -, hk, hfI, hli, -, -⟩ := hjac σ I w hI hic hdim hw
  obtain ⟨_, _⟩ := hdvr σ I w hI hic hdim hw
  refine ⟨k, f, hk, hfI, hli.finCons fun hmem ↦ ?_⟩
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
  set φ := algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) with hφ
  have hfw : ∀ j, eval w (f j) = 0 := fun j ↦ hw (f j) (hfI j)
  have htw : eval w t = 0 := by
    by_contra h
    exact ht.not_isUnit (isUnit_algebraMap_pointLocalRing I w t h)
  set p := t - ∑ j, C (c j) * f j with hp
  have hpm : p ∈ RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ) := by
    simp [hp, RingHom.mem_ker, htw, hfw]
  have hpg : GradientAtPoint.grad w p = 0 := by

    rw [hp, map_sub, map_sum]
    simp_rw [GradientAtPoint.grad_mul_of_eval_eq_zero w _ _ (hfw _), eval_C]
    have hg : ∀ q, GradientAtPoint.grad w q = fun i ↦ eval w (pderiv i q) :=
      fun q ↦ funext (GradientAtPoint.grad_apply w q)
    simp_rw [hg]
    exact sub_eq_zero.2 hc.symm
  have hp2 := GradientAtPoint.mem_sq_of_grad_eq_zero w hpm hpg
  have hφf : ∀ j, φ (f j) = 0 := fun j ↦
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ (hfI j))
  have hφt : φ t = φ p := by simp [hp, hφf]
  have hmax : Ideal.map φ (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)) ≤
      IsLocalRing.maximalIdeal (pointLocalRing I w) := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hu ↦ pointLocalRing_eval_ne_zero_of_isUnit I w hw g hu (RingHom.mem_ker.1 hg)
  have ht2 : φ t ∈ IsLocalRing.maximalIdeal (pointLocalRing I w) ^ 2 := by
    rw [hφt]
    exact Ideal.pow_right_mono hmax 2 (Ideal.map_pow φ _ 2 ▸ Ideal.mem_map_of_mem φ hp2)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 ht, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton'] at ht2
  obtain ⟨a, ha⟩ := ht2
  have h1 : φ t * (a * φ t) = φ t * 1 := by rw [mul_one]; nth_rewrite 3 [← ha]; ring
  exact ht.not_isUnit
    (IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact mul_left_cancel₀ ht.ne_zero h1))

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

theorem NormalCurveBranchOrder.proof (hdvr : NormalCurvePointDVR.Statement)
    (hsz : UniformiserBranchSimpleZero.Statement) : NormalCurveBranchOrder.Statement := by
  intro n J M w r φ hJ hdim hr hdiff hinj hmaps hw0 g
  have hdim' : ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal) = (1 : ℕ) := by
    rw [M.ringKrullDim_eq, hdim]
  have hwZ : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal := hw0 ▸ hmaps (Metric.mem_ball_self hr)
  obtain ⟨hdom, hD⟩ := hdvr _ M.ideal w M.isPrime M.isIntegrallyClosed hdim' hwZ
  have hnear : ∀ q ∈ M.ideal, ∀ᶠ τ in 𝓝 (0 : ℂ), eval (φ fun _ ↦ τ) q = 0 := by
    refine fun q hq ↦ Filter.eventually_of_mem (Metric.ball_mem_nhds 0 hr) fun τ hτ ↦ hmaps ?_ q hq
    rw [mem_ball_zero_iff] at hτ ⊢
    exact lt_of_le_of_lt (pi_norm_const_le τ) hτ
  have hat0 : ∀ q, eval (φ fun _ ↦ (0 : ℂ)) q = eval w q := fun q ↦ by rw [← hw0]; rfl
  have han := fun q ↦ analyticAt_eval_disc hr hdiff q
  have hne0 : ∀ q, eval w q ≠ 0 → ∀ᶠ τ in 𝓝 (0 : ℂ), eval (φ fun _ ↦ τ) q ≠ 0 :=
    fun q hq ↦ (han q).continuousAt.eventually_ne (by simpa [hat0] using hq)
  have hord0 : ∀ q, eval w q ≠ 0 → analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) q) 0 = 0 :=
    fun q hq ↦ analyticOrderAt_eq_zero.2 (Or.inr (by simpa [hat0] using hq))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (pointLocalRing M.ideal w)
  obtain ⟨t, s₀, hs₀, hts⟩ := pointLocalRing_exists_mul_eq M.ideal w ϖ
  have hassoc : Associated ϖ (algebraMap _ (pointLocalRing M.ideal w) t) :=
    ⟨(isUnit_algebraMap_pointLocalRing _ w s₀ hs₀).unit, hts⟩
  have ht := hassoc.irreducible hϖ
  have ht1 := hsz _ M.ideal w t r φ M.isPrime M.isIntegrallyClosed hdim' ht hr hdiff hinj hmaps hw0
  by_cases hg : algebraMap _ (pointLocalRing M.ideal w) g = 0
  · rw [hg, ord_zero_eq_top_of_dvr, eq_comm, analyticOrderAt_eq_top]
    obtain ⟨s, hs, hsg⟩ := pointLocalRing_exists_mul_mem M.ideal w g hg
    filter_upwards [hnear _ hsg, hne0 s hs] with τ h1 h2
    rw [map_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left h2
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.associated_pow_irreducible hg ht
  obtain ⟨a, s, hs, has⟩ := pointLocalRing_exists_mul_eq M.ideal w (v : pointLocalRing M.ideal w)
  have ha : eval w a ≠ 0 := pointLocalRing_eval_ne_zero_of_isUnit M.ideal w hwZ a
    (by rw [← has]; exact v.isUnit.mul (isUnit_algebraMap_pointLocalRing _ w s hs))
  have hrel : algebraMap _ (pointLocalRing M.ideal w) (g * a - t ^ e * s) = 0 := by
    rw [map_sub, map_mul, map_mul, map_pow, ← has, ← hv]
    ring
  obtain ⟨s', hs', hmem⟩ := pointLocalRing_exists_mul_mem M.ideal w _ hrel
  have heq : (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g * eval (φ fun _ ↦ τ) a) =ᶠ[𝓝 0]
      (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t ^ e * eval (φ fun _ ↦ τ) s) := by
    filter_upwards [hnear _ hmem, hne0 s' hs'] with τ h1 h2
    simp only [map_mul, map_sub, map_pow] at h1
    exact sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left h2)
  have hL : analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g * eval (φ fun _ ↦ τ) a) 0 =
      analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) 0 +
        analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) a) 0 :=
    analyticOrderAt_mul (han g) (han a)
  have hR : analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t ^ e * eval (φ fun _ ↦ τ) s) 0 =
      e • analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) t) 0 +
        analyticOrderAt (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) s) 0 := by
    rw [← analyticOrderAt_pow (han t)]
    exact analyticOrderAt_mul ((han t).pow e) (han s)
  have hc := analyticOrderAt_congr heq
  rw [hL, hR, ht1, hord0 a ha, hord0 s hs, add_zero, add_zero] at hc
  rw [hc, ← Ring.ord_mul_of_isUnit_right v.isUnit, hv, ord_pow_irreducible_of_dvr ht]
  simp

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

theorem ModelLocalizationMaximalPoint.proof : ModelLocalizationMaximalPoint.Statement := by
  intro n J q M P hP
  let A := MvPolynomial (Fin n) ℂ
  let R' := MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ M.ideal
  let L := Localization (normalModelSubmonoid M q)
  let ι : A →+* MvPolynomial (Fin n ⊕ Fin M.m) ℂ :=
    (rename Sum.inl : MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n ⊕ Fin M.m) ℂ).toRingHom
  let φ : A →+* R' := (Ideal.Quotient.mk M.ideal).comp ι
  let _ : Algebra A R' := φ.toAlgebra
  have hφ : ∀ f : A, algebraMap A R' f = Ideal.Quotient.mk M.ideal (rename Sum.inl f) := fun _ ↦ rfl

  have hint : Algebra.IsIntegral A R' := by
    constructor
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction p using MvPolynomial.induction_on with
    | C c =>
      have h : algebraMap A R' (C c) = Ideal.Quotient.mk M.ideal (C c) := by rw [hφ, rename_C]
      exact h ▸ isIntegral_algebraMap
    | add p r hp hr => rw [map_add (f := _)]; exact hp.add hr
    | mul_X p s hp =>
      rw [map_mul]
      refine hp.mul ?_
      cases s with
      | inl i =>
        have h : algebraMap A R' (X i) = Ideal.Quotient.mk M.ideal (X (Sum.inl i)) := by rw [hφ, rename_X]
        exact h ▸ isIntegral_algebraMap
      | inr i =>
        obtain ⟨F, hmon, hF⟩ := M.integral i
        refine ⟨F, hmon, ?_⟩
        rw [RingHom.algebraMap_toAlgebra, show φ = (Ideal.Quotient.mk M.ideal).comp ι from rfl,
          ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]
        exact hF

  let m : Ideal A := RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)
  have hm : m.IsMaximal := RingHom.ker_isMaximal_of_surjective _ fun c ↦ ⟨C c, eval_C c⟩
  let Q : Ideal R' := P.comap (algebraMap R' L)
  have hQm : Q.comap (algebraMap A R') ≤ m := by
    intro f hf
    by_contra hfm
    have hS : algebraMap A R' f ∈ normalModelSubmonoid M q := Submonoid.mem_map_of_mem _ hfm
    exact hP.ne_top (Ideal.eq_top_of_isUnit_mem _ hf (IsLocalization.map_units L ⟨_, hS⟩))

  obtain ⟨Q', hQQ', hQ'prime, hQ'm⟩ := Ideal.exists_ideal_over_prime_of_isIntegral m Q hQm
  have hdisj : Disjoint (normalModelSubmonoid M q : Set R') Q' := by
    rw [Set.disjoint_left]
    rintro _ ⟨f, hf, rfl⟩ hfQ
    apply hf
    have h : f ∈ Q'.comap (algebraMap A R') := hfQ
    change f ∈ Ideal.under A Q' at h
    rw [hQ'm] at h
    exact h
  have hPQ' : P = Q'.map (algebraMap R' L) := by
    have hne : Q'.map (algebraMap R' L) ≠ ⊤ :=
      (IsLocalization.isPrime_of_isPrime_disjoint (normalModelSubmonoid M q) L Q' hQ'prime hdisj).ne_top
    refine hP.eq_of_le hne ?_
    rw [← IsLocalization.map_under (normalModelSubmonoid M q) L P]
    exact Ideal.map_mono hQQ'
  have hQeq : P.comap (algebraMap R' L) = Q' := by
    rw [hPQ']
    exact IsLocalization.under_map_of_isPrime_disjoint (normalModelSubmonoid M q) L hQ'prime hdisj
  have hQ'max : Q'.IsMaximal := by
    letI : Q'.IsPrime := hQ'prime
    exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under Q' (hQ'm ▸ hm)

  let N := P.comap ((algebraMap R' L).comp (Ideal.Quotient.mk M.ideal))
  have hNmax : N.IsMaximal := by
    show (P.comap ((algebraMap R' L).comp (Ideal.Quotient.mk M.ideal))).IsMaximal
    rw [← Ideal.comap_comap, hQeq]
    exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨w, hw⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal ℂ hNmax
  have key : ∀ p, p ∈ N ↔ eval w p = 0 := fun p ↦ by
    rw [hw, mem_vanishingIdeal_singleton_iff]
    exact Iff.rfl
  refine ⟨w, fun p hp ↦ (key p).1 ?_, ?_, ?_⟩
  · show algebraMap R' L (Ideal.Quotient.mk M.ideal p) ∈ P
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero]
    exact P.zero_mem
  · funext i
    have h1 : X i - C (q i) ∈ m := by
      show eval q (X i - C (q i)) = 0
      rw [map_sub, eval_X, eval_C, sub_self]
    rw [← hQ'm, ← hQeq] at h1
    have h2 := (key (rename Sum.inl (X i - C (q i)))).1 h1
    simp only [map_sub, rename_X, rename_C, eval_X, eval_C] at h2
    exact sub_eq_zero.1 h2
  · ext p
    rw [RingHom.mem_ker]
    exact key p

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem eventually_const_mem_ball_one {r : ℝ} (hr : 0 < r) :
    ∀ᶠ τ in 𝓝 (0 : ℂ), (fun _ : Fin 1 ↦ τ) ∈ Metric.ball (0 : Fin 1 → ℂ) r := by
  have hc : Continuous (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) := continuous_pi fun _ ↦ continuous_id
  exact hc.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds (0 : Fin 1 → ℂ) hr)

theorem analyticAt_comp_const_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    {φ : (Fin 1 → ℂ) → E} {r : ℝ} (hr : 0 < r) (hφ : DifferentiableOn ℂ φ (Metric.ball 0 r)) :
    AnalyticAt ℂ (fun τ : ℂ ↦ φ (fun _ ↦ τ)) 0 := by
  have hc : Differentiable ℂ (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) :=
    differentiable_pi.2 fun _ ↦ differentiable_id
  exact DifferentiableOn.analyticAt (s := (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) ⁻¹' Metric.ball 0 r)
    (hφ.comp hc.differentiableOn fun _ h ↦ h) (eventually_const_mem_ball_one hr)

theorem analyticAt_eval_of_analyticAt_zero {n : ℕ} {F : ℂ → Fin n → ℂ} (hF : AnalyticAt ℂ F 0)
    (p : MvPolynomial (Fin n) ℂ) : AnalyticAt ℂ (fun τ ↦ eval (F τ) p) 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq => simp only [map_add (f := _)]; exact hp.add hq
  | mul_X p i hp => simp only [map_mul, eval_X]; exact hp.mul (analyticAt_pi_iff.mp hF i)

theorem branchOrder_ne_top_of_not_mem (hB : BranchOffHypersurface.Statement) {n : ℕ}
    {J : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ} (γ : VarBranch J 1 q) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ)) {b : MvPolynomial (Fin n) ℂ} (hb : b ∉ J) :
    branchOrder γ b ≠ ⊤ := by
  intro htop
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff_ball.1 (analyticOrderAt_eq_top.1 htop)
  have hU : Metric.ball (0 : Fin 1 → ℂ) (min ε γ.radius) ⊆ Metric.ball 0 γ.radius :=
    Metric.ball_subset_ball (min_le_right _ _)
  obtain ⟨t, ht, hne⟩ := hB n 1 J b _ γ.toFun hJ hdim hb Metric.isOpen_ball
    ⟨0, Metric.mem_ball_self (lt_min hε γ.radius_pos)⟩ (γ.differentiableOn.mono hU) (γ.injOn.mono hU)
    fun t ht ↦ γ.mapsTo (hU ht)
  have ht0 : (fun _ : Fin 1 ↦ t 0) = t := funext fun i ↦ by rw [Subsingleton.elim i 0]
  apply hne
  rw [← ht0]
  apply hεb
  rw [Metric.mem_ball, dist_zero_right] at ht ⊢
  exact lt_of_le_of_lt (norm_le_pi_norm t 0) (lt_of_lt_of_le ht (min_le_left _ _))

theorem SameOrdersLiftCentre.proof (hB : BranchOffHypersurface.Statement) : SameOrdersLiftCentre.Statement := by
  intro n J q M γ γ' Γ Γ' hJ hdim hΓd hΓ hΓ'd hΓ' hord
  funext s
  rcases s with j | i
  · have e := congrFun (hΓ 0 (Metric.mem_ball_self γ.radius_pos)).2 j
    have e' := congrFun (hΓ' 0 (Metric.mem_ball_self γ'.radius_pos)).2 j
    simp only [firstCoords] at e e'
    rw [e, e', γ.map_zero, γ'.map_zero]
  obtain ⟨a, b, hb, hab⟩ := M.birational i

  have key : ∀ (c : VarBranch J 1 q) (L : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ),
      DifferentiableOn ℂ L (Metric.ball 0 c.radius) →
      (∀ τ ∈ Metric.ball 0 c.radius, L τ ∈ zeroSetIn M.ideal ∧ firstCoords (L τ) = c.toFun τ) → ∀ l : ℂ,
      branchOrder c (a - C l * b) =
        branchOrder c b + analyticOrderAt (fun τ : ℂ ↦ L (fun _ ↦ τ) (Sum.inr i) - l) 0 := by
    intro c L hLd hL l
    have hLa : AnalyticAt ℂ (fun τ : ℂ ↦ L (fun _ ↦ τ) (Sum.inr i) - l) 0 :=
      ((analyticAt_pi_iff.mp (analyticAt_comp_const_one c.radius_pos hLd)) (Sum.inr i)).sub analyticAt_const
    have hBa := analyticAt_eval_of_analyticAt_zero (analyticAt_comp_const_one c.radius_pos c.differentiableOn) b
    rw [branchOrder, branchOrder, ← analyticOrderAt_mul hBa hLa]
    apply analyticOrderAt_congr
    filter_upwards [eventually_const_mem_ball_one c.radius_pos] with τ hτ
    have h := (hL _ hτ).1 _ hab
    simp only [eval_sub, eval_mul, eval_X, eval_rename] at h
    change eval (firstCoords (L fun _ ↦ τ)) b * _ - eval (firstCoords (L fun _ ↦ τ)) a = 0 at h
    rw [(hL _ hτ).2] at h
    simp only [eval_sub, eval_mul, eval_C, Pi.mul_apply]
    linear_combination -h
  set l := Γ 0 (Sum.inr i)
  have k1 := key γ Γ hΓd hΓ l
  have k2 := key γ' Γ' hΓ'd hΓ' l
  rw [← hord, ← hord] at k2
  have heq := WithTop.add_left_cancel (branchOrder_ne_top_of_not_mem hB γ hJ hdim hb) (k1.symm.trans k2)
  have hGa : AnalyticAt ℂ (fun τ : ℂ ↦ Γ (fun _ ↦ τ) (Sum.inr i) - l) 0 :=
    ((analyticAt_pi_iff.mp (analyticAt_comp_const_one γ.radius_pos hΓd)) (Sum.inr i)).sub analyticAt_const
  have hG'a : AnalyticAt ℂ (fun τ : ℂ ↦ Γ' (fun _ ↦ τ) (Sum.inr i) - l) 0 :=
    ((analyticAt_pi_iff.mp (analyticAt_comp_const_one γ'.radius_pos hΓ'd)) (Sum.inr i)).sub analyticAt_const
  have hz : analyticOrderAt (fun τ : ℂ ↦ Γ (fun _ ↦ τ) (Sum.inr i) - l) 0 ≠ 0 :=
    hGa.analyticOrderAt_ne_zero.2 (sub_self _)
  rw [heq] at hz
  exact (sub_eq_zero.1 (hG'a.analyticOrderAt_ne_zero.1 hz)).symm

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

theorem BranchPlace.proof (h₁ : BranchInComponent.Statement) (h₂ : PrimeBranchPlace.Statement)
    (h₃ : MinimalPrimePlace.Statement) : BranchPlace.Statement := by
  intro n I q c hrad hdim
  obtain ⟨J, hJ, hmaps⟩ := h₁ n I 1 q c
  have hJp : J.IsPrime := hJ.1.1
  have hIJ : I ≤ J := hJ.1.2

  let c' : VarBranch J 1 q :=
    { radius := c.radius, radius_pos := c.radius_pos, toFun := c.toFun, differentiableOn := c.differentiableOn,
      injOn := c.injOn, map_zero := c.map_zero, mapsTo := hmaps }

  have hJq : J ≤ RingHom.ker (eval q) := by
    intro g hg
    have h0 := hmaps (Metric.mem_ball_self c.radius_pos) g hg
    rw [c.map_zero] at h0
    exact RingHom.mem_ker.2 h0

  have hdimJ : ringKrullDim (curveLocalRing J q) ≤ 1 := by
    have hle : I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) ≤
        J.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) :=
      Ideal.map_mono hIJ
    rw [← hdim]
    exact ringKrullDim_le_of_surjective
      (Ideal.Quotient.factor hle : curveLocalRing I q →+* curveLocalRing J q) (Ideal.Quotient.factor_surjective hle)
  obtain ⟨P', hP'⟩ := h₂ n J q c' hJp hdimJ
  obtain ⟨P, hP⟩ := h₃ n I J q hrad hJ hJq P'
  exact ⟨P, fun f ↦ (hP f).trans (hP' f)⟩

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem PlaceHasBranch.proof (h₁ : PlaceBranchExists.Statement) (h₂ : PuncturedBranchInOneBranch.Statement)
    (h₃ : PuncturedBranchSameOrder.Statement) : PlaceHasBranch.Statement := by
  intro n I q m c hrad hdim hcov hdisj P
  obtain ⟨N, hN, hNc⟩ := hcov
  obtain ⟨ν, hν⟩ := h₁ n I q hrad hdim P
  have hnorm : ∀ τ : ℂ, ‖(fun _ ↦ τ : Fin 1 → ℂ)‖ = ‖τ‖ := fun τ ↦ by simp [pi_norm_const]

  have hcont : ContinuousAt (fun τ : ℂ ↦ ν.toFun (fun _ ↦ τ)) 0 := by
    have h0 : ContinuousAt ν.toFun (fun _ ↦ (0 : ℂ)) :=
      ν.differentiableOn.continuousOn.continuousAt
        (Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_zero_right, hnorm] using ν.radius_pos))
    exact h0.comp (continuous_pi fun _ ↦ continuous_id).continuousAt
  have hq : ν.toFun (fun _ ↦ (0 : ℂ)) = q := ν.map_zero
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), ν.toFun (fun _ ↦ τ) ∈ N := hcont.preimage_mem_nhds (by rw [hq]; exact hN)
  obtain ⟨ε, hε, hεN⟩ := Metric.eventually_nhds_iff.1 hev

  have hin : ∀ τ : ℂ, 0 < ‖τ‖ → ‖τ‖ < min ε ν.radius → ν.toFun (fun _ ↦ τ) ∈ ⋃ b, (c b).image := by
    intro τ _ hτ
    refine hNc ⟨ν.mapsTo ?_, hεN ?_⟩
    · rw [Metric.mem_ball, dist_zero_right, hnorm]
      exact hτ.trans_le (min_le_right _ _)
    · rw [dist_zero_right]
      exact hτ.trans_le (min_le_left _ _)
  obtain ⟨b, ρ', hρ', hb⟩ := h₂ n I q m c ν (min ε ν.radius) hrad hdim (lt_min hε ν.radius_pos) hin hdisj
  exact ⟨b, fun f ↦ (hν f).trans (h₃ n I q (c b) ν ρ' hrad hdim hρ' hb f).symm⟩

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def PrimeGermProjectionStep.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (P : Ideal (holGerms w)), P.IsPrime → P ≠ ⊥ →
    (∀ (τ : Type) [Fintype τ], Fintype.card τ < Fintype.card σ →
      ∀ (v : τ → ℂ) (Q : Ideal (holGerms v)), Q.IsPrime →
        ∃ (d : ℕ) (B : (τ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection v Q B) →
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w P A

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end
