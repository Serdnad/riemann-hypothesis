module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartProjFinite
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle041
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveAlgebraic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open scoped ComplexOrder
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj pot sheetDensity fibre mcPts segre
  maDensity cxHessian IsSheet)

namespace PtsSemiPosMassFinite

theorem finsum_le_finsum_abs {α : Type*} (G : α → ℝ) : ∑ᶠ x, G x ≤ ∑ᶠ x, |G x| := by
  have hs : (Function.support fun x => |G x|) = Function.support G := by
    ext x
    simp
  by_cases h : (Function.support G).Finite
  · rw [finsum_eq_sum_of_support_subset G (s := h.toFinset) (by simp),
      finsum_eq_sum_of_support_subset (fun x => |G x|) (s := h.toFinset) (by simp [hs])]
    exact Finset.sum_le_sum fun x _ => le_abs_self _
  · rw [finsum_of_infinite_support h, finsum_of_infinite_support (by rwa [hs])]

theorem chartDens_le_chartAbsDens {n d : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    chartDens J A f φ y ≤ chartAbsDens J A f φ y := by
  classical
  unfold chartDens chartAbsDens sheetSum
  refine (finsum_le_finsum_abs _).trans (le_of_eq (finsum_congr fun x => ?_))
  rw [finsum_eq_if, finsum_eq_if]
  split_ifs <;> simp

theorem sheetDensity_nonneg {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P : Ideal (MRing ι)}
    {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {N : Fin e → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hNs : ∀ j, IsSmoothHerm (N j)) (hNp : ∀ j, Inter.IsSemiPosHerm (N j)) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : 0 ≤ sheetDensity P Ψ (pot N) (fun _ => 1) y w := by
  unfold sheetDensity
  split_ifs with hγ
  · rw [one_mul]
    have hpsd : ∀ j, (cxHessian (fun y' => pot N j (hγ.choose y')) y).PosSemidef := fun j =>
      Inter.SheetHessPSD.proof K ι P e Ψ (N j) y w _ (hNs j) (hNp j) hγ.choose_spec
    unfold maDensity
    exact mul_nonneg (by positivity) (ReciprocityTheory.AnForm.A.mdisc_nonneg_of_posSemidef _ hpsd).2
  · exact le_rfl

end PtsSemiPosMassFinite

theorem PtsSemiPosMassFinite.proof (hI : PtsPosPartProjIndep.Statement) (hF : PtsSegreChartFibreSum.Statement)
    (hA : SegreChartAbsIntegrable.Statement) : PtsSemiPosMassFinite.Statement := by
  intro K _ ι _ P e Ψ N hP hΨ hNs hNp
  classical
  by_cases hZ : (mcPts P).Nonempty
  · obtain ⟨z0, hz0⟩ := hZ
    choose i hi using hz0.1
    have hsi : segre z0 i ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hi k
    obtain ⟨Ψ', hΨ', hΨ'0⟩ := SegreCoordGoodProj.proof K ι P e i hP ⟨z0, hz0, hsi⟩
    rw [hI K ι P e Ψ Ψ' N (fun _ => 1) hP hΨ hΨ' hNs measurable_const (fun _ _ _ => rfl)]
    set σ : Fin (Fintype.card ((k : K) → ι k)) ≃ ((k : K) → ι k) := (Fintype.equivFin _).symm
    have hfs := hF K ι P e _ σ i N (fun _ => 1) Ψ' hP hNs (isDegZeroSmooth_const 1) hΨ' hΨ'0
    have hint : Integrable (fun y => ∑ J ∈ segreChartComponents P σ i,
        chartAbsDens J (chartProjMatrix σ Ψ') (chartWeight σ i (fun _ => 1)) (chartPot σ i N) y) :=
      integrable_finsetSum _ fun J hJ =>
        hA K ι P e _ σ i N (fun _ => 1) hP hNs (isDegZeroSmooth_const 1) J hJ _
          (SegreChartProjFinite.proof K ι P e _ σ i Ψ' hP hΨ' hΨ'0 J hJ)
    refine lt_of_le_of_lt (lintegral_mono_ae ?_) hint.lintegral_lt_top
    filter_upwards [hfs] with y hy
    refine ENNReal.ofReal_le_ofReal ?_
    have hpos : ptsPosDens P Ψ' (pot N) (fun _ => 1) y =
        ∑ᶠ w ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ' y, sheetDensity P Ψ' (pot N) (fun _ => 1) y w := by
      unfold ptsPosDens
      exact finsum_congr fun w => finsum_congr fun _ =>
        max_eq_left (PtsSemiPosMassFinite.sheetDensity_nonneg hNs hNp y w)
    rw [hpos, hy]
    exact Finset.sum_le_sum fun J _ => PtsSemiPosMassFinite.chartDens_le_chartAbsDens _ _ _ _ _
  · have h0 : ∀ y, ptsPosDens P Ψ (pot N) (fun _ => 1) y = 0 := by
      intro y
      have hf : _root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y = ∅ := by
        ext w
        simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨z, hz, -⟩
        exact hZ ⟨z, hz⟩
      simp [ptsPosDens, hf]
    simp [h0]

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace SegreChart

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def segre (y : (Σ k, ι k) → Ω) : (Σ _ : Unit, ∀ k, ι k) → Ω :=
  fun q ↦ ∏ k, y ⟨k, q.2 k⟩

omit [∀ k, Fintype (ι k)] in
theorem segre_ne_zero_iff (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k) :
    segre y ⟨(), f⟩ ≠ 0 ↔ ∀ k, y ⟨k, f k⟩ ≠ 0 := by
  simp [segre, Finset.prod_ne_zero_iff]


omit [∀ k, Fintype (ι k)] in
theorem segre_ratio (y : (Σ k, ι k) → Ω) (f g : ∀ k, ι k) :
    segre y ⟨(), g⟩ / segre y ⟨(), f⟩ = ∏ k, y ⟨k, g k⟩ / y ⟨k, f k⟩ := by
  simp [segre, Finset.prod_div_distrib]


omit [∀ k, Fintype (ι k)] in
theorem prod_ratio_update [DecidableEq K] (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0)
    (p : Σ k, ι k) :
    ∏ k, y ⟨k, Function.update f p.1 p.2 k⟩ / y ⟨k, f k⟩ = y p / y ⟨p.1, f p.1⟩ := by
  rw [Finset.prod_eq_single p.1]
  · simp
  · intro k _ hk
    rw [Function.update_of_ne hk, div_self (hf k)]
  · simp


omit [∀ k, Fintype (ι k)] in
theorem chartRingZ_segre (y : (Σ k, ι k) → Ω) (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) :
    chartRingZ (segre y) (fun _ ↦ f) = chartRingZ y f := by
  classical
  apply le_antisymm
  · rw [chartRingZ, Algebra.adjoin_le_iff]
    rintro _ ⟨⟨⟨⟩, g⟩, rfl⟩
    change segre y ⟨(), g⟩ / segre y ⟨(), f⟩ ∈ chartRingZ y f
    rw [segre_ratio]
    exact prod_mem fun k _ ↦ Algebra.subset_adjoin ⟨⟨k, g k⟩, rfl⟩
  · rw [chartRingZ, Algebra.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    change y p / y ⟨p.1, f p.1⟩ ∈ chartRingZ (segre y) (fun _ ↦ f)
    rw [← prod_ratio_update y f hf p, ← segre_ratio]
    exact Algebra.subset_adjoin ⟨⟨(), Function.update f p.1 p.2⟩, rfl⟩

theorem charZero_of_isArithVar {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) : CharZero Ω := by
  refine charZero_of_inj_zero fun n hn ↦ ?_
  have hmem : ((n : ℤ) : ℤ) ∈ (mCoordIdeal y).comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_C]
    rw [eq_intCast, Int.cast_natCast, ← map_natCast (C : Ω →+* MvPolynomial K Ω), hn, map_zero]
  rw [show (mCoordIdeal y).comap (C : ℤ →+* MRing ι) = ⊥ from hP.2.2.1, Ideal.mem_bot] at hmem
  exact_mod_cast hmem

theorem exists_chart {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) :
    ∃ f : ∀ k, ι k, ∀ k, y ⟨k, f k⟩ ≠ 0 := by
  have h : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k ↦ by
    obtain ⟨i, hi⟩ := hP.2.1.2.2 k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]
  choose f hf using h
  exact ⟨f, hf⟩

theorem isAlgebraic_segre_ratio [CharZero Ω] {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1)
    (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) (g : ∀ k, ι k) :
    IsAlgebraic ℚ (segre y ⟨(), g⟩ / segre y ⟨(), f⟩) := by
  rw [segre_ratio]
  refine (IsIntegral.prod _ fun k _ ↦ ?_).isAlgebraic
  exact (IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.isAlgebraic_ratio hP f hf ⟨k, g k⟩).isIntegral

theorem isArithVar_segre [DecidableEq K] [CharZero Ω] {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1)
    (f : ∀ k, ι k) (hf : ∀ k, y ⟨k, f k⟩ ≠ 0) : IsArithVar (mCoordIdeal (segre y)) 1 := by
  refine CoordConeArithVar.full Unit (fun _ ↦ ∀ k, ι k) Ω (segre y) (fun _ ↦ f) 0 Fin.elim0 ⟨()⟩
    (fun _ ↦ (segre_ne_zero_iff y f).mpr hf) algebraicIndependent_empty_type (fun i ↦ i.elim0) ?_
  rintro _ ⟨⟨⟨⟩, g⟩, rfl⟩
  exact IsAlgebraic.extendScalars (RingHom.injective _) (isAlgebraic_segre_ratio hP f hf g)

end SegreChart

end

end GroundTheory.Heights₂.Heights.Targets
end
