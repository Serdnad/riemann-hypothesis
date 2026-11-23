module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle004
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

theorem ChartFiniteIrrel.proof : ChartFiniteIrrel.Statement.{u, v, w} := by
  intro K _ ι _ F _ V f i hV hf hirr
  classical
  let _ := MvPolynomial.weightedGradedAlgebra F (mw (ι := ι))
  let M : Ideal (MRingOver F ι) :=
    Ideal.span (weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => 1) : Set (MRingOver F ι))
  have hMrad : M ≤ (V ⊔ Ideal.span {f}).radical := by
    rw [← Ideal.sInf_minimalPrimes]
    refine le_sInf fun W hW => Ideal.span_le.mpr fun x hx => ?_
    have h := hirr W hW
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant, not_forall, not_exists, not_not] at h
    obtain ⟨k, hk⟩ := h
    exact weighted_le_of_irrel (e := fun _ => 1) hk le_rfl hx
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hMrad (IsNoetherian.noetherian M)
  have hA : ∀ t, N ≤ t → weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => t) ≤
      (V ⊔ Ideal.span {f}).restrictScalars F := fun t ht _ hh =>
    hN (Ideal.pow_le_pow_right ht (ChartFiniteIrrel.weighted_le_pow t hh))
  have hVh : V.IsHomogeneous (weightedHomogeneousSubmodule F (mw (ι := ι))) := by
    obtain ⟨S₀, hS₀, rfl⟩ := hV
    exact Ideal.homogeneous_span _ S₀ fun x hx =>
      let ⟨a, ha⟩ := hS₀ x hx; ⟨a, mem_weighted_of_isMultiHomog ha⟩
  let π := (Ideal.Quotient.mkₐ F (_root_.ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i)).toLinearMap
  let B : ℕ → Submodule F (MRingOver F ι ⧸ _root_.ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i) := fun t =>
    (weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => t)).map π
  have hmono : ∀ t, B t ≤ B (t + 1) := by
    rintro t _ ⟨h, hh, rfl⟩
    refine ⟨h * ∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ (fun _ : K => 1) k,
      SetLike.mul_mem_graded hh (mem_weighted_of_isMultiHomog (isMultiHomog_coordProd i _)), ?_⟩
    simp [π, map_prod, mk_chartIdeal_X_self]
  have hstep : ∀ t, N ≤ t + 1 → B (t + 1) ≤ (B t).map (LinearMap.mulLeft F (π f)) := by
    rintro t ht _ ⟨h, hh, rfl⟩
    have h2 : h ∈ weightedHomogeneousSubmodule F (mw (ι := ι)) (fun _ => t + 1) ⊓
        (V ⊔ Ideal.span {f}).restrictScalars F := ⟨hh, hA _ ht hh⟩
    rw [sup_span_inf_eq' hVh (mem_weighted_of_isMultiHomog hf) (d := fun _ => t + 1) (fun _ => Nat.le_add_left 1 t),
      show ((fun _ : K => t + 1) - fun _ => 1) = fun _ => t from funext fun _ => by simp] at h2
    obtain ⟨v, ⟨-, hv⟩, _, ⟨g, hg, rfl⟩, rfl⟩ := Submodule.mem_sup.mp h2
    refine ⟨π g, ⟨g, hg, rfl⟩, ?_⟩
    have hv0 : Ideal.Quotient.mk (_root_.ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal V i) v = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left hv)
    simp [π, hv0]
  have heq : ∀ t, N ≤ t → B t = B (t + 1) := fun t ht =>
    Submodule.eq_of_le_of_finrank_le (hmono t)
      ((Submodule.finrank_mono (hstep t (by omega))).trans (Submodule.finrank_map_le _ _))
  have hconst : ∀ t, N ≤ t → B t = B N := fun t ht => by
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih => rw [← heq t ht, ih]
  have htop : B N = ⊤ := by
    refine eq_top_iff.mpr fun a _ => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨e₀, he₀⟩ := exists_homog_chart V i b
    obtain ⟨b', hb', hbb⟩ := he₀ (fun _ => N + ∑ k, e₀ k) fun k =>
      le_add_left (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k))
    rw [← hconst _ (Nat.le_add_right _ _)]
    exact ⟨b', hb', hbb⟩
  rw [Module.finite_def, ← htop]
  exact Module.Finite.iff_fg.mp inferInstance

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsMultiHomogIdeal ptsIntegral pot segre mcPts SameOrbit
  segre_smul mcPts_smul sameOrbit_of_segre)
open GroundTheory.Heights₂.Heights (varInt IsDegZeroSmooth segreChartSet segreChartComponents segreChartIdeal chartLift
  chartLift_segre_apply mem_segreChartComponents)

namespace SegreChartIntegralPoints

theorem aeval_eq_eval' {m : ℕ} (x : Fin m → ℂ) (p : MvPolynomial (Fin m) ℂ) : aeval x p = eval x p := rfl

theorem ker_eval_isMaximal {m : ℕ} (x : Fin m → ℂ) :
    (RingHom.ker (eval x : MvPolynomial (Fin m) ℂ →+* ℂ)).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, eval_C _⟩

theorem minimalPrimes_vanishingIdeal {m : ℕ} {S : Set (Fin m → ℂ)} (hS : S.Finite) :
    (vanishingIdeal ℂ S : Ideal (MvPolynomial (Fin m) ℂ)).minimalPrimes =
      (fun x => RingHom.ker (eval x)) '' S := by
  classical
  have hle : ∀ x ∈ S, (vanishingIdeal ℂ S : Ideal (MvPolynomial (Fin m) ℂ)) ≤ RingHom.ker (eval x) :=
    fun x hx p hp => by rw [RingHom.mem_ker, ← aeval_eq_eval']; exact hp x hx
  have hinf : hS.toFinset.inf (fun x => RingHom.ker (eval x : MvPolynomial (Fin m) ℂ →+* ℂ)) ≤
      (vanishingIdeal ℂ S : Ideal (MvPolynomial (Fin m) ℂ)) := by
    intro p hp
    rw [mem_vanishingIdeal_iff]
    intro x hx
    have := Finset.inf_le (f := fun x => RingHom.ker (eval x : MvPolynomial (Fin m) ℂ →+* ℂ))
      (hS.mem_toFinset.2 hx) hp
    rwa [RingHom.mem_ker, ← aeval_eq_eval'] at this

  have hcont : ∀ q : Ideal (MvPolynomial (Fin m) ℂ), q.IsPrime → vanishingIdeal ℂ S ≤ q →
      ∃ x ∈ S, RingHom.ker (eval x) ≤ q := fun q hq hIq => by
    obtain ⟨x, hx, hxq⟩ := (hq.inf_le' (s := hS.toFinset)).1 (hinf.trans hIq)
    exact ⟨x, hS.mem_toFinset.1 hx, hxq⟩
  ext q
  constructor
  · intro hq
    obtain ⟨x, hx, hxq⟩ := hcont q hq.1.1 hq.1.2
    exact ⟨x, hx, le_antisymm hxq (hq.2 ⟨RingHom.ker_isPrime _, hle x hx⟩ hxq)⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨RingHom.ker_isPrime _, hle x hx⟩, fun q hq hqx => ?_⟩
    obtain ⟨y, hy, hyq⟩ := hcont q hq.1 hq.2
    have hxy := (ker_eval_isMaximal y).eq_of_le (ker_eval_isMaximal x).ne_top (hyq.trans hqx)
    show RingHom.ker (eval x) ≤ q
    rw [← hxy]
    exact hyq

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem segre_ne_zero {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ j, z ⟨k, j⟩ ≠ 0) : segre z ≠ 0 := by
  choose j hj using hz
  intro h
  have h0 : segre z j = 0 := by rw [h]; rfl
  exact Finset.prod_ne_zero_iff.2 (fun k _ => hj k) h0

theorem exists_normalised {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) (k₀ : K) (i : (k : K) → ι k)
    {t : (Σ k, ι k) → ℂ} (ht : t ∈ mcPts P) (hi : segre t i ≠ 0) :
    ∃ t', t' ∈ mcPts P ∧ SameOrbit t' t ∧ segre t' = (segre t i)⁻¹ • segre t := by
  classical
  let c : K → ℂ := fun k => if k = k₀ then (segre t i)⁻¹ else 1
  have hc : ∀ k, c k ≠ 0 := fun k => by by_cases h : k = k₀ <;> simp [c, h, hi]
  have hprod : ∏ k, c k = (segre t i)⁻¹ := by
    rw [Finset.prod_eq_single k₀ (fun k _ hk => by simp [c, hk]) (by simp)]
    simp [c]
  exact ⟨_, mcPts_smul hP c hc ht, ⟨c, hc, rfl⟩, by rw [segre_smul, hprod]⟩

theorem proof : SegreChartIntegralPoints.Statement := by
  classical
  intro K _ _ ι _ P m σ i L g δ G Φ hP hg hδ hvan hG
  obtain ⟨k₀⟩ := hP.1
  obtain ⟨R, hRm, hRu, hRint⟩ := Inter.regularityPointsSum_holds.proof K ι P hP
  have horb : ∀ z z', SameOrbit z z' → g z = g z' := by
    rintro z z' ⟨c, hc, rfl⟩
    exact hg.2 c z' hc
  have hL : pot L = (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) := Subsingleton.elim _ _
  rw [hL, hRint g fun z z' _ h => horb z z' h]
  set S := R.filter (fun t => segre t i ≠ 0) with hS
  let ν : ((Σ k, ι k) → ℂ) → Fin m → ℂ := fun t a => (segre t i)⁻¹ * segre t (σ a)

  have hν : ∀ t ∈ S, ∃ t', t' ∈ mcPts P ∧ SameOrbit t' t ∧ segre t' i = 1 ∧
      ν t = fun a => segre t' (σ a) := by
    intro t ht
    obtain ⟨htR, hti⟩ := Finset.mem_filter.1 ht
    obtain ⟨t', ht'm, ht'o, ht's⟩ := exists_normalised hP.2.1.2.1 k₀ i (hRm t htR) hti
    refine ⟨t', ht'm, ht'o, ?_, funext fun a => ?_⟩
    · rw [ht's, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hti]
    · rw [ht's, Pi.smul_apply, smul_eq_mul]
  have hchart : segreChartSet P σ i = ν '' S := by
    ext x
    constructor
    · rintro ⟨z, hz, hzi, rfl⟩
      obtain ⟨t, ⟨htR, c, hc, rfl⟩, -⟩ := hRu z hz
      have hzs : segre (fun p => c p.1 * t p) = (∏ k, c k) • segre t := segre_smul c t
      have h1 : (∏ k, c k) * segre t i = 1 := by
        rw [← hzi, hzs, Pi.smul_apply, smul_eq_mul]
      have hti : segre t i ≠ 0 := right_ne_zero_of_mul_eq_one h1
      refine ⟨t, Finset.mem_filter.2 ⟨htR, hti⟩, funext fun a => ?_⟩
      rw [hzs, Pi.smul_apply, smul_eq_mul, eq_inv_of_mul_eq_one_left h1]
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨t', ht'm, -, ht'i, hνt⟩ := hν t ht
      exact ⟨t', ht'm, ht'i, hνt⟩
  have hinj : Set.InjOn ν S := by
    intro t₁ ht₁ t₂ ht₂ h
    obtain ⟨ht₁R, ht₁i⟩ := Finset.mem_filter.1 ht₁
    obtain ⟨ht₂R, ht₂i⟩ := Finset.mem_filter.1 ht₂
    have hseg : segre t₁ = (segre t₁ i * (segre t₂ i)⁻¹) • segre t₂ := by
      funext j
      have hj := congrFun h (σ.symm j)
      simp only [ν, Equiv.apply_symm_apply] at hj
      rw [Pi.smul_apply, smul_eq_mul, mul_assoc, ← hj, ← mul_assoc, mul_inv_cancel₀ ht₁i, one_mul]
    have h12 := sameOrbit_of_segre (hRm t₂ ht₂R).1 _ (mul_ne_zero ht₁i (inv_ne_zero ht₂i)) hseg
    exact (hRu t₁ (hRm t₁ ht₁R)).unique ⟨ht₁R, fun _ => 1, fun _ => one_ne_zero, by simp⟩ ⟨ht₂R, h12⟩
  have hfin : (segreChartSet P σ i).Finite := hchart ▸ S.finite_toSet.image ν
  have hfs : hfin.toFinset = S.image ν := Finset.coe_injective (by simp [hchart])
  have hcomp : segreChartComponents P σ i = hfin.toFinset.image (fun x => RingHom.ker (eval x)) := by
    ext J
    rw [mem_segreChartComponents, segreChartIdeal, minimalPrimes_vanishingIdeal hfin]
    simp
  have hkinj : ∀ x y : Fin m → ℂ, RingHom.ker (eval x : MvPolynomial (Fin m) ℂ →+* ℂ) = RingHom.ker (eval y) →
      x = y := fun x y h => by
    have := PointIntegral.zeroSet_ker_eval x
    rw [h, PointIntegral.zeroSet_ker_eval] at this
    exact (Set.singleton_eq_singleton_iff.1 this).symm
  rw [hcomp, Finset.sum_image fun x _ y _ h => hkinj x y h]
  rw [Finset.sum_congr rfl fun x _ => PointIntegral.proof m x G Φ]
  rw [hfs, Finset.sum_image hinj]

  rw [← Finset.sum_filter_of_ne (p := fun t => segre t i ≠ 0) fun t ht hgt hti => hgt (hvan t (by
    rw [hti, norm_zero]
    exact mul_pos hδ (norm_pos_iff.2 (segre_ne_zero (hRm t ht).1))))]
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨t', ht'm, ht'o, ht'i, hνt⟩ := hν t ht
  have hx : ν t ∈ segreChartSet P σ i := hchart ▸ Set.mem_image_of_mem ν ht
  rw [(hG _ hx).eq_of_nhds, Function.comp_apply, ← horb t' t ht'o, hνt]
  have hne : ∀ k, t' ⟨k, i k⟩ ≠ 0 := fun k h0 => by
    have h1 : segre t' i = 0 := Finset.prod_eq_zero (f := fun k => t' ⟨k, i k⟩) (Finset.mem_univ k) h0
    rw [ht'i] at h1
    exact one_ne_zero h1
  have hlift : chartLift σ i (fun a => segre t' (σ a)) = fun p => (t' ⟨p.1, i p.1⟩)⁻¹ * t' p := by
    funext ⟨k, j⟩
    rw [chartLift_segre_apply σ i t' ht'i k j, mul_comm]
  rw [hlift]
  exact (hg.2 (fun k => (t' ⟨k, i k⟩)⁻¹) t' fun k => inv_ne_zero (hne k)).symm

end SegreChartIntegralPoints

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem CoordFibreDeg.proof (hM : FibreMultiHomog.Statement) (hD : GenFibreChartDeg.Statement)
    (hR : CoordRatioDeg.Statement) : CoordFibreDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v Ω _ _ y d G i hb hZ' hZ hi
  have : CharZero G.Φ' := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hmem : (C (n : ℤ) : MRing ι') ∈ mCoordIdeal y := by
      rw [← G.genericFibre_ker_target, RingHom.mem_ker]
      simpa using hn
    simp only [mCoordIdeal, RingHom.mem_ker, mConeMap] at hmem
    simpa using hmem
  have hMH : IsMultiHomogIdeal (mCoordIdeal y) := hZ'.2.1.2.1
  choose c hc using hZ.2.1.2.2
  have hx : ∀ k, G.x ⟨k, c k⟩ ≠ 0 := fun k h => hc k (by
    rw [← G.ker_x, RingHom.mem_ker, aeval_X]
    exact h)
  have hi' : ∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0 := fun k h => hi k (by
    rw [_root_.ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact h)
  have h1 := Inter.ChartRankAdjoin.proof (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ'
    (fun q : Σ k : FibreBlock κ, fibreIdx ι' κ k => G.x' ⟨q.1.1, q.2⟩) i hi'
    (hM K ι K' ι' κ v (mCoordIdeal y) G hb hMH)
  exact h1.trans ((hD K ι K' ι' κ v (mCoordIdeal y) G c i hb hMH hx hi').trans
    (hR K ι K' ι' κ v Ω y G.Φ' G.x' hb G.genericFibre_ker_target))

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre PBlk)
open ComplexSets

section Chart

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def projChartSet (P : Ideal (MRing ι)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set (Fin m → ℂ) :=
  {x | ∃ z ∈ mcPts P, Ψ (segre z) 0 = 1 ∧ x = fun a => segre z (σ a)}

def projChartIdeal (P : Ideal (MRing ι)) {m e : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Ideal (MvPolynomial (Fin m) ℂ) :=
  MvPolynomial.vanishingIdeal ℂ (projChartSet P σ Ψ)

end Chart

def GoodChartModel.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ →
      zeroSet (projChartIdeal P σ Ψ) = projChartSet P σ Ψ ∧
      ∀ J ∈ (projChartIdeal P σ Ψ).minimalPrimes,
        ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = (e : ℕ) ∧ IsFiniteProjection J (chartProjMatrix σ Ψ)

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj PBlk)
open ComplexSets

def SegreChartProjFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e m : ℕ) (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ w, Ψ w 0 = w i) →
      ∀ J ∈ segreChartComponents P σ i, IsFiniteProjection J (chartProjMatrix σ Ψ)

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsSectionOn divSupp IsHorizontal multAt mcPts)
open GroundTheory.Heights₂.Heights (segreChartSet segreChartIdeal segreChartComponents localMult mem_segreChartComponents)

variable {K : Type*} [Fintype K] {ι : K → Type*}

theorem segreChartIdeal_isRadical (P : Ideal (MRing ι)) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    (segreChartIdeal P σ i).IsRadical := by
  rintro f ⟨e, he⟩
  rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff] at he ⊢
  intro x hx
  have h := he x hx
  rw [map_pow] at h
  exact eq_zero_of_pow_eq_zero h

theorem segreChartIdeal_mono {P W : Ideal (MRing ι)} (h : P ≤ W) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k))
    (i : (k : K) → ι k) : segreChartIdeal P σ i ≤ segreChartIdeal W σ i := by
  apply MvPolynomial.vanishingIdeal_anti_mono
  rintro x ⟨z, ⟨hz0, hz⟩, hzi, rfl⟩
  exact ⟨z, ⟨hz0, fun f hf => hz f (h hf)⟩, hzi, rfl⟩

theorem ChartDivisorLength.proof (hNotMem : ChartSectionNotMem.Statement) (hComp : ChartDivisorComponents.Statement)
    (hLen : ChartSectionLength.Statement) : ChartDivisorLength.Statement := by
  intro K _ _ ι _ P n m σ i A s hP hs W hW hWh W' hW'
  have hcomp := (hComp K ι P n m σ i A s hP hs).1
  have hnot := hNotMem K ι P (n + 1) m σ i A s hP hs
  have hW'min : W' ∈ (segreChartIdeal W σ i).minimalPrimes := mem_segreChartComponents.1 hW'
  have hW'p : W'.IsPrime := hW'min.1.1
  have hIW' : segreChartIdeal P σ i ≤ W' :=
    (segreChartIdeal_mono (le_sup_left.trans hW.1.1.2) σ i).trans hW'min.1.2
  have hJW : ∀ J ∈ (segreChartIdeal P σ i).minimalPrimes, J ≤ W' →
      W' ∈ (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes := fun J hJ hJW' =>
    (hcomp J (mem_segreChartComponents.2 hJ) W').2 ⟨hJW', W, ⟨hW, hWh⟩, hW'⟩
  have hmin : W' ∈ (segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s}).minimalPrimes := by
    refine ⟨⟨hW'p, sup_le hIW' ?_⟩, fun Q hQ hQW' => ?_⟩
    · obtain ⟨J, hJ, hJW'⟩ := Ideal.exists_minimalPrimes_le hIW'
      exact le_sup_right.trans (hJW J hJ hJW').1.2
    · have := hQ.1
      obtain ⟨J, hJ, hJQ⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hQ.2)
      exact (hJW J hJ (hJQ.trans hQW')).2 ⟨hQ.1, sup_le hJQ (le_sup_right.trans hQ.2)⟩ hQW'
  have key := GroundTheory.Heights₂.Heights.SectionLengthSum.proof
    (GroundTheory.Heights₂.Heights.LocalSectionLengthSum.proof GroundTheory.Heights₂.Heights.PiQuotCokerFiniteLength.proof)
    (MvPolynomial (Fin m) ℂ) (segreChartIdeal P σ i) W' (chartSection σ i s) (segreChartIdeal_isRadical P σ i)
    (fun J hJ => hnot J (mem_segreChartComponents.2 hJ)) hmin hJW
  rw [← hLen K ι P n m σ i A s hP hs W hW hWh W' hW', key]
  rfl

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsArithVar IsSectionOn divSupp IsHorizontal PBlk fsLine Xc)
open GroundTheory.Heights₂.Heights (segreChartIdeal segreChartComponents localMult)

def ChartConeLength.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n m : ℕ)
    (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) (A : HermLine ι) (s : MRing ι),
    IsArithVar P (n + 2) → IsSectionOn P A s →
      ∀ W, W ∈ divSupp P s → IsHorizontal W → ∀ W' ∈ segreChartComponents W σ i,
        ∀ W'' ∈ (W.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes,
          W''.map (chartSubst σ i : MvPolynomial (Σ k, ι k) ℂ →+* MvPolynomial (Fin m) ℂ) ≤ W' →
            localMult (segreChartIdeal P σ i ⊔ Ideal.span {chartSection σ i s}) W' =
              localMult ((P ⊔ Ideal.span {s}).map (MvPolynomial.map (Int.castRingHom ℂ))) W''

end GroundTheory.Heights₂.Heights.Targets
end
end
