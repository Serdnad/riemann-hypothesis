module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Maps
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Convex.Contractible
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodD
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.SwapLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace LocRingFrac

set_option linter.unusedSectionVars false

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem isMultiHomog_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm k
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm k

theorem isMultiHomog_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

end LocRingFrac

theorem LocRingFrac.proof : LocRingFrac.Statement := by
  intro K _ ι _ P W _ hW _ y hy
  have h1 : (1 : MRing ι) ∉ W := fun h => hW.ne_top ((Ideal.eq_top_iff_one _).mpr h)
  induction hy using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨u, v, a, hv, hvW, hu, hva, rfl⟩ := hx
    exact ⟨u, v, a, hu, hva, hvW, IsLocalization.mk'_spec _ _ _⟩
  | zero => exact ⟨0, 1, 0, isMultiHomog_zero 0, AvoidRing.isMultiHomog_one, h1, by simp⟩
  | one => exact ⟨1, 1, 0, AvoidRing.isMultiHomog_one, AvoidRing.isMultiHomog_one, h1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, v, a, hu, hv, hvW, e⟩ := hx
    obtain ⟨u', v', a', hu', hv', hvW', e'⟩ := hy
    refine ⟨u * v' + u' * v, v * v', a + a',
      isMultiHomog_add (AvoidRing.isMultiHomog_mul hu hv')
        (by rw [add_comm]; exact AvoidRing.isMultiHomog_mul hu' hv),
      AvoidRing.isMultiHomog_mul hv hv', fun h => (hW.mem_or_mem h).elim hvW hvW', ?_⟩
    simp only [RingHom.map_mul, RingHom.map_add]
    rw [← e, ← e']
    ring
  | neg x _ hx =>
    obtain ⟨u, v, a, hu, hv, hvW, e⟩ := hx
    exact ⟨-u, v, a, isMultiHomog_neg hu, hv, hvW, by
      simp only [RingHom.map_neg]
      rw [← e]
      ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨u, v, a, hu, hv, hvW, e⟩ := hx
    obtain ⟨u', v', a', hu', hv', hvW', e'⟩ := hy
    refine ⟨u * u', v * v', a + a', AvoidRing.isMultiHomog_mul hu hu', AvoidRing.isMultiHomog_mul hv hv',
      fun h => (hW.mem_or_mem h).elim hvW hvW', ?_⟩
    rw [map_mul, map_mul, map_mul, map_mul, ← e, ← e']
    ring

end

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem pointFormRank_holds.exists_surj_coords {σ : Type*} {n : ℕ} (ℓ : σ → (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hℓ : ∀ x, (∀ s, ℓ s x = 0) → x = 0) :
    ∀ m, m ≤ n → ∃ q : Fin m → σ, Function.Surjective (fun x : Fin n → ℂ => fun j => ℓ (q j) x) := by
  intro m
  induction m with
  | zero => intro _; exact ⟨Fin.elim0, fun t => ⟨0, funext fun j => j.elim0⟩⟩
  | succ m ih =>
    intro hm
    obtain ⟨q, hq⟩ := ih (by omega)
    let Φ : (Fin n → ℂ) →ₗ[ℂ] (Fin m → ℂ) := LinearMap.pi fun j => ℓ (q j)
    have hrank := LinearMap.finrank_range_add_finrank_ker Φ
    have hle : Module.finrank ℂ (LinearMap.range Φ) ≤ m := by
      simpa using Submodule.finrank_le (LinearMap.range Φ)
    have hpos : 0 < Module.finrank ℂ (LinearMap.ker Φ) := by
      rw [Module.finrank_fin_fun] at hrank; omega
    obtain ⟨⟨x, hxk⟩, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    have hx : x ≠ 0 := fun h => hx0 (Subtype.ext h)
    have hΦx : ∀ j, ℓ (q j) x = 0 := fun j => congr_fun (LinearMap.mem_ker.mp hxk) j
    obtain ⟨s, hs⟩ : ∃ s, ℓ s x ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (hℓ x h)
    refine ⟨Fin.snoc q s, fun t => ?_⟩
    obtain ⟨x0, hx0'⟩ := hq (Fin.init t)
    refine ⟨x0 + ((t (Fin.last m) - ℓ s x0) / ℓ s x) • x, funext fun j => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.snoc_last, map_add (f := _), map_smul, smul_eq_mul]
      rw [div_mul_cancel₀ _ hs]
      ring
    · simp only [Fin.snoc_castSucc, map_add (f := _), map_smul, hΦx, smul_eq_mul, mul_zero, add_zero]
      exact congr_fun hx0' j

theorem pointFormRank_holds.eq_zero_of_eventually_eval {d : ℕ} (f : MvPolynomial (Fin d) ℂ) (a : Fin d → ℂ)
    (h : ∀ᶠ z in 𝓝 a, eval z f = 0) : f = 0 := by
  have han : AnalyticOnNhd ℂ (fun z => eval z f) Set.univ := AnalyticOnNhd.eval_mvPolynomial f
  have h0 := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ a) h
  exact MvPolynomial.funext fun z => by simpa using h0 (Set.mem_univ z)

theorem pointFormRank_holds.proof (hA : RatioAlgDep.Statement) : pointFormRank_holds.Statement := by
  intro K _ ι _ Q d n F y hQ hdn hF hev
  classical
  have hy : F y ∈ mcPts Q := hev.self_of_nhds
  choose c hc using hy.1
  have hcomp : ∀ p, AnalyticAt ℂ (fun y' => F y' p) y := analyticAt_pi_iff.mp hF
  have hDy : ∀ p : Σ k, ι k, F y ⟨p.1, c p.1⟩ ≠ 0 := fun p => hc p.1
  set r : (Σ k, ι k) → (Fin n → ℂ) → ℂ := fun p y' => F y' p / F y' ⟨p.1, c p.1⟩ with hr_def
  have hr : ∀ p, AnalyticAt ℂ (r p) y := fun p => (hcomp p).div (hcomp _) (hDy p)
  have hnear : ∀ᶠ y' in 𝓝 y, ∀ k, F y' ⟨k, c k⟩ ≠ 0 :=
    Filter.eventually_all.mpr fun k => (hcomp ⟨k, c k⟩).continuousAt.eventually_ne (hc k)
  set F' := fderiv ℂ F y with hF'_def
  have hF' : HasFDerivAt F F' y := hF.differentiableAt.hasFDerivAt
  set ℓ : (Σ k, ι k) → (Fin n → ℂ) →L[ℂ] ℂ := fun p => fderiv ℂ (r p) y with hℓ_def
  have hℓ : ∀ p, HasFDerivAt (r p) (ℓ p) y := fun p => (hr p).differentiableAt.hasFDerivAt
  have hprod : ∀ p, HasFDerivAt (fun y' => r p y' * F y' ⟨p.1, c p.1⟩)
      (r p y • (ContinuousLinearMap.proj ⟨p.1, c p.1⟩).comp F' + F y ⟨p.1, c p.1⟩ • ℓ p) y :=
    fun p => (hℓ p).mul (hasFDerivAt_pi'.mp hF' _)
  have heq : ∀ p, (fun y' => F y' p) =ᶠ[𝓝 y] fun y' => r p y' * F y' ⟨p.1, c p.1⟩ :=
    fun p => hnear.mono fun y' hy' => (div_mul_cancel₀ _ (hy' p.1)).symm
  have hderiv : ∀ p, (ContinuousLinearMap.proj p).comp F' =
      r p y • (ContinuousLinearMap.proj ⟨p.1, c p.1⟩).comp F' + F y ⟨p.1, c p.1⟩ • ℓ p :=
    fun p => (hasFDerivAt_pi'.mp hF' p).unique ((hprod p).congr_of_eventuallyEq (heq p))
  by_contra hno
  push Not at hno
  have hinj : ∀ x, (∀ p, ℓ p x = 0) → x = 0 := by
    intro x hx
    by_contra hx0
    refine hno x hx0 (fun k => F' x ⟨k, c k⟩ / F y ⟨k, c k⟩) ?_
    funext p
    have h1 := congrArg (fun L => L x) (hderiv p)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, FunLike.coe_add, Pi.add_apply,
      FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, hx p, mul_zero, add_zero] at h1
    rw [h1, bsmul, hr_def]
    ring
  obtain ⟨q, hq⟩ := pointFormRank_holds.exists_surj_coords (fun p => (ℓ p).toLinearMap)
    (fun x hx => hinj x (by simpa using hx)) d hdn
  have hg : HasStrictFDerivAt (fun y' j => r (q j) y') (ContinuousLinearMap.pi fun j => ℓ (q j)) y :=
    hasStrictFDerivAt_pi.mpr fun j => (hr (q j)).hasStrictFDerivAt
  have hrange : (ContinuousLinearMap.pi fun j => ℓ (q j) : (Fin n → ℂ) →L[ℂ] (Fin d → ℂ)).range = ⊤ := by
    refine LinearMap.range_eq_top.mpr fun t => ?_
    obtain ⟨x, hx⟩ := hq t
    exact ⟨x, hx⟩
  have hmap := hg.map_nhds_eq_of_surj hrange
  obtain ⟨f, hf0, hfz⟩ := hA K ι Q d c q hQ
  have hev' : ∀ᶠ y' in 𝓝 y, eval (fun j => r (q j) y') (map (Int.castRingHom ℂ) f) = 0 := by
    filter_upwards [hev, hnear] with y' hy' hy'c
    exact hfz (F y') hy'.2 hy'c
  have hz : ∀ᶠ z in 𝓝 ((fun y' j => r (q j) y') y), eval z (map (Int.castRingHom ℂ) f) = 0 := by
    rw [← hmap]
    exact Filter.eventually_map.mpr hev'
  have h0 := pointFormRank_holds.eq_zero_of_eventually_eval _ _ hz
  exact hf0 (MvPolynomial.map_injective _ (Int.castRingHom ℂ).injective_int (h0.trans (map_zero _).symm))

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section LinSubst

variable {Φ : Type} [Field Φ] {σ : Type} [Fintype σ] {n : ℕ}

def linSubst (ℓ : σ → Fin n → Φ) : MvPolynomial σ Φ →ₐ[Φ] MvPolynomial (Fin n) Φ :=
  aeval fun q => ∑ a, C (ℓ q a) * X a

def linKerForms (ℓ : σ → Fin n → Φ) : Set (MvPolynomial σ Φ) :=
  {f | ∃ μ : σ → Φ, (∀ b, ∑ q, μ q * ℓ q b = 0) ∧ f = ∑ q, C (μ q) * X q}

theorem sum_C_mul_linForm {τ ρ : Type} [Fintype τ] [Fintype ρ] (c : ρ → Φ) (ν : ρ → τ → Φ) :
    ∑ a, C (c a) * ∑ q, C (ν a q) * (X q : MvPolynomial τ Φ) = ∑ q, C (∑ a, c a * ν a q) * X q := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_

  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, mul_assoc]

theorem linSubst_linForm (ℓ : σ → Fin n → Φ) (μ : σ → Φ) :
    linSubst ℓ (∑ q, C (μ q) * X q) = ∑ b, C (∑ q, μ q * ℓ q b) * X b := by
  rw [← sum_C_mul_linForm μ ℓ]

  simp only [linSubst, map_sum, map_mul, aeval_C, aeval_X, MvPolynomial.algebraMap_eq]

theorem ker_linSubst (ℓ : σ → Fin n → Φ) (ν : Fin n → σ → Φ)
    (hν : ∀ a b, ∑ q, ν a q * ℓ q b = if a = b then 1 else 0) :
    RingHom.ker (linSubst ℓ) = Ideal.span (linKerForms ℓ) := by
  classical
  refine le_antisymm (fun f hf => ?_) ?_
  · set I := Ideal.span (linKerForms ℓ)
    let ρ : MvPolynomial (Fin n) Φ →ₐ[Φ] MvPolynomial σ Φ ⧸ I :=
      aeval fun a => Ideal.Quotient.mk I (∑ q, C (ν a q) * X q)
    have hρ : ρ.comp (linSubst ℓ) = Ideal.Quotient.mkₐ Φ I := by
      refine MvPolynomial.algHom_ext fun q => ?_
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
      have h1 : ρ (linSubst ℓ (X q)) =
          Ideal.Quotient.mk I (∑ q', C (∑ a, ℓ q a * ν a q') * X q') := by
        rw [← sum_C_mul_linForm]

        simp only [ρ, linSubst, aeval_X, map_sum, map_mul, aeval_C]
        rfl
      rw [h1, Ideal.Quotient.eq]
      refine Ideal.subset_span ⟨fun q' => ∑ a, ℓ q a * ν a q' - if q' = q then 1 else 0, fun b => ?_, ?_⟩
      · simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]
        rw [Finset.sum_comm]
        simp only [← Finset.mul_sum, hν, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        simp
      · simp [sub_mul, Finset.sum_sub_distrib, apply_ite C, ite_mul]
    have h2 := congrArg (fun φ => φ f) hρ
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h2
    rw [RingHom.mem_ker] at hf
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← h2]
    erw [hf]
    exact map_zero ρ
  · rw [Ideal.span_le]
    rintro f ⟨μ, hμ, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    erw [linSubst_linForm]
    simp [hμ]

end LinSubst

section Main

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]




end Main

section Fibre

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]




end Fibre

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem multAt_pos_of_mem_divSupp {P : Ideal (MRing ι)} {s : MRing ι} {W : Ideal (MRing ι)}
    (hW : W ∈ divSupp P s) : 0 < multAt (P ⊔ Ideal.span {s}) W := by
  have hmin := hW.1
  have hWp : W.IsPrime := hmin.1.1
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime W) ∈
      ((P ⊔ Ideal.span {s}).map (algebraMap (MRing ι) (Localization.AtPrime W))).minimalPrimes := by
    rw [IsLocalization.minimalPrimes_map W.primeCompl (Localization.AtPrime W)]
    rw [Set.mem_preimage, Localization.AtPrime.under_maximalIdeal]
    exact hmin
  have hne := ReciprocityTheory.ChartRestriction.G.AI.I1.SwapLoc.length_quot_ne_top_of_mem_minimalPrimes _ hm
  have : Nontrivial (Localization.AtPrime W ⧸
      (P ⊔ Ideal.span {s}).map (algebraMap (MRing ι) (Localization.AtPrime W))) :=
    Ideal.Quotient.nontrivial_iff.mpr
      (ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hm.1.2)
  have hpos := Module.length_pos (R := Localization.AtPrime W)
    (M := Localization.AtPrime W ⧸
      (P ⊔ Ideal.span {s}).map (algebraMap (MRing ι) (Localization.AtPrime W)))
  rw [multAt, dite_eq_left hWp, ReciprocityTheory.ChartRestriction.G.AI.I1.inh_length_locQuot]
  exact ENat.toNat_pos hpos.ne' hne

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace ThmIMultilin

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem smooth_update {n : ℕ} {L : Fin n → HermLine ι} (hL : ∀ i, IsSmoothHerm (L i)) (j : Fin n)
    {X : HermLine ι} (hX : IsSmoothHerm X) : ∀ i, IsSmoothHerm (Function.update L j X i) := by
  intro i
  by_cases h : i = j
  · subst h
    simpa using hX
  · simpa [Function.update_of_ne h] using hL i


omit [∀ k, Fintype (ι k)] in
theorem update_comp_swap {m : ℕ} (L : Fin (m + 1) → HermLine ι) (j : Fin (m + 1)) (X : HermLine ι) :
    Function.update L j X ∘ Equiv.swap j (Fin.last m) =
      Fin.snoc (fun i : Fin m => L (Equiv.swap j (Fin.last m) i.castSucc)) X := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp
  · have hne : Equiv.swap j (Fin.last m) i.castSucc ≠ j := by
      intro h
      have h' : Equiv.swap j (Fin.last m) i.castSucc = Equiv.swap j (Fin.last m) (Fin.last m) := by
        rw [h, Equiv.swap_apply_right]
      exact Fin.castSucc_ne_last i ((Equiv.swap j (Fin.last m)).injective h')
    simp [Function.update_of_ne hne]

end ThmIMultilin

end GroundTheory.Heights₂.Heights.Inter
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def funField {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    Subring (FractionRing (MRing ι ⧸ P)) :=
  Subring.closure {x | ∃ (u v : MRing ι) (a : K → ℕ)
    (hv : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P)),
    IsMultiHomog u a ∧ IsMultiHomog v a ∧
      x = IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hv⟩}

theorem exists_funField_mul_eq {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} [P.IsPrime] {f g : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) (hgP : g ∉ P) :
    ∃ x : funField P, (x : FractionRing (MRing ι ⧸ P)) *
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P g) =
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P f) := by
  have hv : Ideal.Quotient.mk P g ∈ nonZeroDivisors (MRing ι ⧸ P) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  exact ⟨⟨IsLocalization.mk' _ (Ideal.Quotient.mk P f) ⟨_, hv⟩,
    Subring.subset_closure ⟨f, g, a, hv, hf, hg, rfl⟩⟩, IsLocalization.mk'_spec _ _ _⟩

def regularityEmbedding_holds.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (R : Finset ((Σ k, ι k) → ℂ)),
    IsArithVar P 1 → (∀ t ∈ R, t ∈ mcPts P) → (∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t) →
    ∃ e : R ≃ (funField P →+* ℂ), ∀ (t : R) (u v : MRing ι) (a : K → ℕ),
      IsMultiHomog u a → IsMultiHomog v a → v ∉ P → ∀ x : funField P,
      (x : FractionRing (MRing ι ⧸ P)) *
          algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) →
      e t x * eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) v) =
        eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) u)

end

end GroundTheory.Heights₂.Heights.Inter
end
