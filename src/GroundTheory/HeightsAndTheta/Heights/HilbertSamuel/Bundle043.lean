module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
public import Mathlib.RingTheory.Nullstellensatz
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle003

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

theorem exists_natMul_mem_of_map_rat_mem {σ : Type} (I : Ideal (MvPolynomial σ ℤ)) (f : MvPolynomial σ ℤ)
    (hf : map (Int.castRingHom ℚ) f ∈ Ideal.map (map (Int.castRingHom ℚ)) I) :
    ∃ M : ℕ, M ≠ 0 ∧ (M : MvPolynomial σ ℤ) * f ∈ I := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := σ) (R := ℤ) (S := ℚ)
  have hA : (map (Int.castRingHom ℚ) : MvPolynomial σ ℤ →+* MvPolynomial σ ℚ) =
      algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ) := by
    rw [algebraMap_def, algebraMap_int_eq]
  rw [hA, IsLocalization.mem_map_algebraMap_iff ((nonZeroDivisors ℤ).map (C (σ := σ)))] at hf
  obtain ⟨⟨⟨g, hg⟩, ⟨_, m, hm, rfl⟩⟩, h⟩ := hf
  have hinj : Function.Injective (algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ)) := by
    rw [← hA]; exact map_injective _ Int.cast_injective
  have h' : C m * f = g := by rw [mul_comm]; exact hinj (by simpa using h)
  obtain ⟨t, ht⟩ : m ∣ (m.natAbs : ℤ) := Int.dvd_natAbs.mpr dvd_rfl
  refine ⟨m.natAbs, Int.natAbs_ne_zero.mpr (nonZeroDivisors.ne_zero hm), ?_⟩
  have : (m.natAbs : MvPolynomial σ ℤ) = C (m.natAbs : ℤ) := (map_natCast C _).symm
  rw [this, ht, C_mul, mul_comm (C m), mul_assoc, h']
  exact I.mul_mem_left _ hg

theorem PullConeNullModP.proof : PullConeNullModP.Statement := by
  classical
  intro K _ ι _ Ω _ y D L hL p hp hbad
  have : Fact p.Prime := ⟨hp⟩
  have hQ : coneNullIdeal y L = (coneNullIdealZ y L).map (map (Int.castRingHom ℚ)) := by
    rw [coneNullIdeal, coneNullIdealZ, Ideal.map_span, Set.image_union, ← Set.range_comp]; rfl
  set I := coneNullIdealZ y L
  let π := Ideal.Quotient.mk I
  obtain ⟨N₁, hN₁⟩ := PullConeNull.proof K ι Ω y D L hL

  have key : ∀ c : ∀ k, ι k, ∃ N M : ℕ, ¬ p ∣ M ∧
      (M : MRing ι ⧸ I) * π (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N = 0 := by
    intro c
    set u := π (∏ k, (X ⟨k, c k⟩ : MRing ι))

    obtain ⟨M₁, hM₁, h₁⟩ := exists_natMul_mem_of_map_rat_mem I ((∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N₁)
      (by rw [← hQ]; simpa [map_prod] using hN₁ c)
    have e₁ : (M₁ : MRing ι ⧸ I) * u ^ N₁ = 0 := by
      rw [← map_natCast π, ← map_pow, ← map_mul]; exact Ideal.Quotient.eq_zero_iff_mem.mpr h₁

    obtain ⟨N₂, h, e₂⟩ : ∃ N₂ h, u ^ N₂ = (p : MRing ι ⧸ I) * h := by
      let φ : MRing ι →+* MvPolynomial (Σ k, ι k) (ZMod p) := map (Int.castRingHom (ZMod p))
      have hrad : φ (∏ k, (X ⟨k, c k⟩ : MRing ι)) ∈ (I.map φ).radical := by
        rw [← IsJacobsonRing.out inferInstance (Ideal.radical_isRadical (I.map φ)), Ideal.jacobson, Submodule.mem_sInf]
        rintro m ⟨hJm, hm⟩
        letI := Ideal.Quotient.field m
        have := finite_of_finite_type_of_isJacobsonRing (ZMod p) (MvPolynomial (Σ k, ι k) (ZMod p) ⧸ m)
        let ψ := IsAlgClosed.lift (R := ZMod p) (M := AlgebraicClosure (ZMod p))
          (S := MvPolynomial (Σ k, ι k) (ZMod p) ⧸ m)
        let z : (Σ k, ι k) → AlgebraicClosure (ZMod p) := fun q => ψ (Ideal.Quotient.mk m (X q))
        have hev : ∀ f : MRing ι, eval z (map (Int.castRingHom (AlgebraicClosure (ZMod p))) f) =
            ψ (Ideal.Quotient.mk m (φ f)) := by
          intro f
          have e : (eval z).comp (map (Int.castRingHom (AlgebraicClosure (ZMod p)))) =
              ((ψ : _ →+* AlgebraicClosure (ZMod p)).comp (Ideal.Quotient.mk m)).comp φ := by
            refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
            · exact RingHom.congr_fun (RingHom.ext_int
                (((eval z).comp (map (Int.castRingHom (AlgebraicClosure (ZMod p))))).comp C)
                ((((ψ : _ →+* AlgebraicClosure (ZMod p)).comp (Ideal.Quotient.mk m)).comp φ).comp C)) r
            · simp [z, φ]
          exact RingHom.congr_fun e f
        have hker : ∀ f : MRing ι, f ∈ I → ψ (Ideal.Quotient.mk m (φ f)) = 0 := fun f hf => by
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hJm (Ideal.le_radical (Ideal.mem_map_of_mem φ hf))), map_zero]
        by_contra hc
        refine hbad ⟨z, fun k => ⟨c k, fun h0 => hc ?_⟩, fun f hf => ?_, fun j => ?_⟩
        · rw [map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
          refine Ideal.mul_mem_right _ m (Ideal.Quotient.eq_zero_iff_mem.mp (ψ.injective ?_))
          simpa [z, φ] using h0
        · rw [hev]; exact hker f (Ideal.subset_span (Or.inl hf))
        · rw [hev]; exact hker _ (Ideal.subset_span (Or.inr ⟨j, rfl⟩))
      obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
      rw [← map_pow, ← Ideal.mem_comap,
        Ideal.comap_map_of_surjective φ (map_surjective _ ZMod.intCast_surjective)] at hn
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hn
      have hb' : b ∈ RingHom.ker φ := by simpa [RingHom.mem_ker] using hb
      rw [ker_map, ZMod.ker_intCastRingHom, Ideal.map_span, Set.image_singleton,
        Ideal.mem_span_singleton'] at hb'
      obtain ⟨h, rfl⟩ := hb'
      refine ⟨n, π h, ?_⟩
      rw [← map_pow, ← hab, map_add (f := _), Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add, map_mul, map_natCast C p,
        map_natCast, mul_comm]

    obtain ⟨a, M₀, hM₀, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM₁ p hp.ne_one
    refine ⟨a * N₂ + N₁, M₀, hM₀, ?_⟩
    rw [pow_add, pow_mul', e₂, mul_pow]
    push_cast at e₁
    linear_combination h ^ a * e₁
  choose Nc Mc hMc hc using key
  refine ⟨Finset.univ.sup Nc, ∏ c, Mc c, ?_, fun c => ?_⟩
  · exact fun hdvd => (Prime.dvd_finsetProd_iff hp.prime _).mp hdvd |>.elim fun c ⟨_, h⟩ => hMc c h
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow, map_natCast,
      ← Finset.mul_prod_erase _ _ (Finset.mem_univ c),
      ← Nat.add_sub_cancel' (Finset.le_sup (f := Nc) (Finset.mem_univ c)), pow_add]
    push_cast
    linear_combination ((∏ c' ∈ Finset.univ.erase c, (Mc c' : MRing ι ⧸ I)) *
      π (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ (Finset.univ.sup Nc - Nc c)) * hc c

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem resLift_continuousOn (d : HSMDatum D Ω κ) (x : d.R.X) (p : Ix κ) :
    ContinuousOn (fun z => d.R.lift x z p) (d.R.U x) := by
  intro z hz
  obtain ⟨j, hj⟩ := d.R.A.cover z
  have hzt : d.R.A.chart j z ∈ (d.R.A.chart j).target := (d.R.A.chart j).map_source hj
  have hc : ContinuousAt ((fun z => d.R.lift x z p) ∘ (d.R.A.chart j).symm) (d.R.A.chart j z) :=
    (d.R.holo x p j _ ⟨hzt, by rwa [Set.mem_preimage, (d.R.A.chart j).left_inv hj]⟩).continuousAt
  have h := ((d.R.A.chart j).symm.continuousAt_iff_continuousAt_comp_right
    (f := fun z => d.R.lift x z p) (x := z) (by simpa using hj)).mpr (by simpa using hc)
  exact h.continuousWithinAt

theorem resLift_contDiffOn (d : HSMDatum D Ω κ) (x : d.R.X) (j : Fin d.R.A.n) :
    ContDiffOn ℝ ∞ (fun y => d.R.lift x ((d.R.A.chart j).symm y))
      ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x) :=
  contDiffOn_pi.mpr fun p => ((d.R.holo x p j).contDiffOn_of_completeSpace).restrict_scalars ℝ

theorem resPot_smoothOn (d : HSMDatum D Ω κ) {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m)
    (x : d.R.X) : d.R.A.SmoothOn ((resPot d m).U x) ((resPot d m).φ x) := fun j => by
  have hne : ∀ y ∈ (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x,
      d.R.lift x ((d.R.A.chart j).symm y) ∈ {z : Ix κ → ℂ | z ≠ 0} :=
    fun y hy => gaamix_ne_zero_of_mcPts (d.R.mem x _ hy.2)
  exact (hm.comp (resLift_contDiffOn d x j) hne).log fun y hy => (m.pos _ (hne y hy)).ne'

theorem isPotential_resPot (d : HSMDatum D Ω κ) {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) :
    IsPotential d.R.A (resPot d m) := by
  refine ⟨resPot_smoothOn d hm, fun x x' y hy => ?_⟩
  have hy' : y ∈ d.R.U x ∩ d.R.U x' := hy
  obtain ⟨p, hp⟩ := (d.R.mem x' y hy'.2).1 ()
  obtain ⟨c, hc, hcy⟩ := d.R.compat x x' y hy'
  have hnum : d.R.lift x y ⟨(), p⟩ ≠ 0 := by
    rw [hcy]
    exact mul_ne_zero (hc ()) hp
  set r : ℂ := d.R.lift x y ⟨(), p⟩ / d.R.lift x' y ⟨(), p⟩ with hr_def
  have hr : r ≠ 0 := div_ne_zero hnum hp
  have hO : IsOpen (d.R.U x ∩ d.R.U x') := (d.R.isOpen_U x).inter (d.R.isOpen_U x')
  let q : d.R.X → ℂ := fun z => d.R.lift x z ⟨(), p⟩ / d.R.lift x' z ⟨(), p⟩ / r
  let W : Set d.R.X :=
    {z | z ∈ d.R.U x ∩ d.R.U x' ∧ d.R.lift x' z ⟨(), p⟩ ≠ 0 ∧ q z ∈ Complex.slitPlane}
  have hW : IsOpen W := by
    refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    have hn : ContinuousAt (fun z => d.R.lift x z ⟨(), p⟩) z :=
      ((resLift_continuousOn d x _).mono Set.inter_subset_left).continuousAt (hO.mem_nhds hz.1)
    have hd : ContinuousAt (fun z => d.R.lift x' z ⟨(), p⟩) z :=
      ((resLift_continuousOn d x' _).mono Set.inter_subset_right).continuousAt (hO.mem_nhds hz.1)
    filter_upwards [hO.mem_nhds hz.1, hd.eventually_ne hz.2.1,
      ((hn.div hd hz.2.1).div_const r).eventually_mem (Complex.isOpen_slitPlane.mem_nhds hz.2.2)]
      with w h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have hyW : y ∈ W := by
    refine ⟨hy', hp, ?_⟩
    have h1 : q y = 1 := div_self hr
    rw [h1]
    exact Complex.mem_slitPlane_iff.mpr (Or.inl (by simp))
  let G : d.R.X → ℂ := fun z => Complex.log (q z) + ((Real.log ‖r‖ : ℝ) : ℂ)
  refine ⟨W, hW, hyW, G, fun j y' hy'' => ?_, fun z hz => ?_⟩
  · have hz : (d.R.A.chart j).symm y' ∈ W := hy''.2
    have hn : AnalyticAt ℂ (fun y'' => d.R.lift x ((d.R.A.chart j).symm y'') ⟨(), p⟩) y' :=
      d.R.holo x _ j y' ⟨hy''.1, hz.1.1⟩
    have hd : AnalyticAt ℂ (fun y'' => d.R.lift x' ((d.R.A.chart j).symm y'') ⟨(), p⟩) y' :=
      d.R.holo x' _ j y' ⟨hy''.1, hz.1.2⟩
    have hq : AnalyticAt ℂ (fun y'' => q ((d.R.A.chart j).symm y'')) y' :=
      (hn.div hd hz.2.1).div analyticAt_const hr
    have hl : AnalyticAt ℂ (Complex.log ∘ fun y'' => q ((d.R.A.chart j).symm y'')) y' :=
      AnalyticAt.comp (f := fun y'' => q ((d.R.A.chart j).symm y'')) (analyticAt_clog hz.2.2) hq
    exact hl.add analyticAt_const
  · have hzW : z ∈ W := hz.1.1
    obtain ⟨c', hc', hcz⟩ := d.R.compat x x' z hzW.1
    have hpos : 0 < m.ρ (d.R.lift x' z) := m.pos _ (gaamix_ne_zero_of_mcPts (d.R.mem x' z hzW.1.2))
    have hsm : d.R.lift x z = c' () • d.R.lift x' z := by
      rw [hcz]
      funext w
      rfl
    have hqz : q z = c' () / r := by
      show d.R.lift x z ⟨(), p⟩ / d.R.lift x' z ⟨(), p⟩ / r = _
      rw [hsm, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hzW.2.1, mul_one]
    show Real.log (m.ρ (d.R.lift x z)) - Real.log (m.ρ (d.R.lift x' z)) = (G z).re
    rw [hsm, m.smul, Real.log_mul (norm_ne_zero_iff.mpr (hc' ())) hpos.ne', add_sub_cancel_right]
    show Real.log ‖c' ()‖ = (Complex.log (q z) + ((Real.log ‖r‖ : ℝ) : ℂ)).re
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, hqz, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr (hc' ())) (norm_ne_zero_iff.mpr hr)]
    ring

theorem continuous_logRatio_resPt (d : HSMDatum D Ω κ) {m₀ m₁ : ConeMetric ℂ (Ix κ)}
    (h₀ : IsSmoothMetric m₀) (h₁ : IsSmoothMetric m₁) :
    Continuous fun y => logRatio m₀ m₁ (resPt d y) := by
  refine continuous_iff_continuousAt.2 fun y0 => ?_
  have hU : d.R.U y0 ∈ 𝓝 y0 := (d.R.isOpen_U y0).mem_nhds (d.R.mem_U y0)
  have hL : ContinuousOn (d.R.lift y0) (d.R.U y0) :=
    continuousOn_pi.2 fun p => resLift_continuousOn d y0 p
  have hlog : ContinuousOn (fun y => logRatio m₀ m₁ (d.R.lift y0 y)) (d.R.U y0) :=
    (gbamix_smooth_logRatio h₀ h₁).continuousOn.comp hL
      fun y hy => gaamix_ne_zero_of_mcPts (d.R.mem y0 y hy)
  have heq : (fun y => logRatio m₀ m₁ (d.R.lift y0 y)) =ᶠ[𝓝 y0]
      fun y => logRatio m₀ m₁ (resPt d y) := by
    filter_upwards [hU] with y hy
    obtain ⟨c, hc, hcy⟩ := d.R.compat y y0 y ⟨d.R.mem_U y, hy⟩
    show _ = logRatio m₀ m₁ (d.R.lift y y)
    rw [hcy, gbamix_logRatio_deg c _ hc]
  exact (hlog.continuousAt hU).congr heq

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

def ResolutionMetricPair.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)) (P0₁ : Ideal (MRing (GlobalTheory κ))), IsSmoothMetric m₁ →
    P0₁ ≤ coordIdeal ℤ d.x → IsSemipositiveRel P0₁ (coordIdeal ℤ d.x) (HermLine.ofCone m₁) →
    ∃ (A : FinHolAtlas D d.R.X) (L : HolLineBundle A) (W₀ W₁ : Weight L) (dV : SmoothVolume A)
      (σ : ℕ → MvPolynomial (Ix κ) ℚ → Fin A.n → d.R.X → ℂ),
      A.Compatible d.R.A ∧ W₀.IsSemipositive ∧ W₁.IsSemipositive ∧ dV.μ = d.dV ∧
      (∀ (n : ℕ) (b : MvPolynomial (Ix κ) ℚ), b.IsHomogeneous n → σ n b ∈ L.sections n) ∧
      (∀ y : d.R.X, ∃ c : ℂ, c ≠ 0 ∧
        (∀ (n : ℕ) (b : MvPolynomial (Ix κ) ℚ), b.IsHomogeneous n →
          σ n b (chartIdx A y) y = eval (c • resPt d y) (map (algebraMap ℚ ℂ) b)) ∧
        W₀.φ (chartIdx A y) y = 2 * Real.log (d.m.ρ (c • resPt d y)) ∧
        W₁.φ (chartIdx A y) y = 2 * Real.log (m₁.ρ (c • resPt d y))) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ g : d.R.X → ℝ, Continuous g →
        ∫ y, g y * bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ =
          mInt d.R.A (fun _ => resPot d (interp d.m m₁ t)) g / (D.factorial : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory

noncomputable section

theorem ResolutionFormsIndependent.proof (hND : NonvanishingDense.Statement) :
    ResolutionFormsIndependent.Statement := by
  intro D Ω _ _ κ _ d n r b hb a ha
  obtain ⟨g, hgJ, hgP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set F : (Ix κ → ℂ) → ℂ := fun z => ∑ k, a k * secFun (b k) z with hF
  have hFc : Continuous F :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (continuous_secFun _)

  have hoff : ∀ z, z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) →
      eval z (map (Int.castRingHom ℂ) g) ≠ 0 → F z = 0 := by
    intro z hz hgz
    obtain ⟨y, c, hc, hyz⟩ := d.R.surj z hz (fun hJ => hgz (hJ.2 g hgJ))
    have h1 : resPt d y = c () • z := by
      funext p
      simp [resPt, hyz]
    have h2 : F (resPt d y) = 0 := ha y
    rw [h1, hF] at h2
    simp only at h2
    rw [sum_secFun_smul hb.1] at h2
    exact (mul_eq_zero.1 h2).resolve_left (pow_ne_zero _ (hc ()))

  have hpts : ∀ z ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x), F z = 0 := by
    intro z hz
    have hcl := hND Unit (GlobalTheory κ) (coordIdeal ℤ d.x) (D + 1) g d.arith hgP hz
    have hsub : {z' | z' ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) ∧
        eval z' (map (Int.castRingHom ℂ) g) ≠ 0} ⊆ {z' | F z' = 0} := by
      intro z' hz'
      exact hoff z' hz'.1 hz'.2
    exact closure_minimal hsub (isClosed_eq hFc continuous_const) hcl

  have : IsProbabilityMeasure d.dV := d.vol.1
  obtain ⟨y₀⟩ : Nonempty d.R.X := by
    by_contra h
    rw [not_nonempty_iff] at h
    have h1 := measure_univ (μ := d.dV)
    rw [Set.univ_eq_empty_iff.2 h, measure_empty] at h1
    exact zero_ne_one h1
  have hz₀ : resPt d y₀ ∈ mcPts (ι := GlobalTheory κ) (coordIdeal ℤ d.x) := d.R.mem y₀ y₀ (d.R.mem_U y₀)
  refine coeff_eq_zero_of_vanish (linIndep_rat_of_isSecBasis hb) fun z hz => ?_
  by_cases h0 : z = 0
  · have h1 := hpts _ hz₀
    rw [hF] at h1
    simp only at h1
    rw [h0, ← zero_smul ℂ (resPt d y₀), sum_secFun_smul hb.1, h1, mul_zero]
  · refine hpts z ⟨fun k => ?_, hz⟩
    by_contra hk
    push Not at hk
    exact h0 (funext fun p => by obtain ⟨⟨⟩, i⟩ := p; exact hk i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def ComplexGramMetricChange.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)) (P0₁ : Ideal (MRing (GlobalTheory κ))) (hs : IsSmoothMetric m₁)
    (hc : IsConjInvariant m₁) (hle : P0₁ ≤ coordIdeal ℤ d.x)
    (hp : IsSemipositiveRel P0₁ (coordIdeal ℤ d.x) (HermLine.ofCone m₁)) (e : Fin (D + 1) → Ix κ),
    IsProjFrame d.x e →
    (fun n => resCChi (d.withMetric m₁ P0₁ hs hc hle hp) n - resCChi d n -
        (n : ℝ) ^ (D + 1) / (D.factorial : ℝ) * resMetricInt d m₁) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem MetricToFS.proof (hE : PullFSExtension.Statement) (hC : DefectMetricChange.Statement) :
    MetricToFS.Statement := by
  intro D Ω _ _ κ _ I d e hI hF
  obtain ⟨m₀, hs, hc, hp, hpull⟩ := hE D Ω κ d.x e hF
  exact ⟨d.withMetric m₀ ⊥ hs hc bot_le hp, rfl, hpull,
    hC D Ω κ I d m₀ ⊥ hs hc bot_le hp e hI hF⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry KoszulCech

noncomputable section

def KoszulCechExact.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (α : K → ℤ) (R : ℕ)
    (z : Fin R → KH.CechC S ι (MRingOver S ι ⧸ V) 0),
    (∀ I : KH.Cell K ι 0, ∃ u : Fin R → LocalizedModule (KH.cellMon S I.1) (MRingOver S ι ⧸ V),
      (∀ j, u j ∈ KH.locPart ι (KH.quotPart S V) (KH.cellMon S I.1) (-α)) ∧ ∑ j, u j * z j I = 1) →
    ∀ (c : K → ℤ) (n : ℕ),
      (∀ φ ∈ kosPart S ι V R α c 0 n, ∃ ψ ∈ kosPart S ι V R α c 1 n, kosD z 0 n ψ = φ) ∧
      (∀ p : ℕ, ∀ φ ∈ kosPart S ι V R α c (p + 1) n, kosD z p n φ = 0 →
        ∃ ψ ∈ kosPart S ι V R α c (p + 2) n, kosD z (p + 1) n ψ = φ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def ChartDimLt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ)
    (p : (k : K) → ι k),
    IsMultiHomogIdeal J →
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) < ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
      ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ ReciprocityTheory.AnForm.R.chartIdeal J p) < (e : WithBot ℕ∞)

def ChartRatioImageNull.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Ideal (MvPolynomial (Σ k, ι k) ℂ)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)),
    ringKrullDim (MvPolynomial (Σ k, ι k) ℂ ⧸ J) < (e : WithBot ℕ∞) →
      volume {y : Fin e → ℂ | ∃ z ∈ zeroLocus ℂ J, Ψ (segre z) 0 ≠ 0 ∧
        (Fin.cons 1 y : Fin (e + 1) → ℂ) = (Ψ (segre z) 0)⁻¹ • Ψ (segre z)} = 0

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
