module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgePot
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeAnalytic
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle057
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle068
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle067
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle016
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveAlgebraic
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveDegree
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.EqSumMultihomogeneousComponents

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

section Res

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

theorem psi0_null (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 = 0}) = 0 :=
  volume_projection_zeroSet_null R Ψ hP hΨ j

theorem ram_null (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0}) = 0 :=
  ram_null' R Ψ hP hΨ j

theorem brBad_null (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' brBad R Ψ) = 0 := by
  have h3 : brBad R Ψ ⊆ {x | R.lift x x ∈ mcPts J} ∪ {x | Ψ (segre (R.lift x x)) 0 = 0} ∪
      {x | Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0} := by
    rintro x ((h | h) | ⟨k, hk, hn⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · by_cases h0 : Ψ (segre (R.lift x x)) 0 = 0
      · exact Or.inl (Or.inr h0)
      · refine Or.inr ⟨h0, k, hk, ?_⟩
        by_contra hd
        exact hn ⟨analyticAt_brQ R Ψ x k hk h0, hd⟩
  refine measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono h3)) ?_
  simp only [Set.preimage_union, Set.inter_union_distrib_left]
  exact measure_union_null (measure_union_null (R.null j) (psi0_null R Ψ hP hΨ j))
    (ram_null R Ψ hP hΨ j)

theorem potOf_isPotential (R : AnRes P J e) (L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (hL : IsSmoothHerm L) :
    IsPotential R.A (potOf R L) :=
  isPotential_potOf R hL

theorem brIntegrable (R : AnRes P J e) (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hs : IsSectionOn P A s) :
    MIntegrable R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) :=
  brIntegrable_of logAbsLocInt R L A s hL hA hs

theorem brQ_image_null (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) :
    volume (brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 :=
  brQ_image_null_of R Ψ (brBad_null R Ψ hP hΨ)

theorem brFibreSum_ae (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j))
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    ∀ᵐ y, ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y, sheetDensity P Ψ (pot L) (logNorm A s) y w =
      ∑ᶠ x ∈ brQ R Ψ ⁻¹' {y} \ brBad R Ψ,
        logNorm A s (R.lift x x) * pushDens R.A (fun j => potOf R (L j)) (brQ R Ψ) x := by
  have hN : volume ({y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} ∪
      brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) = 0 :=
    measure_union_null (projB_null Ψ hP hΨ R.homog R.nondeg) (brQ_image_null R Ψ hP hΨ)
  have hNae : ∀ᵐ y, y ∉ ({y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} ∪
      brQ R Ψ '' (brBad R Ψ ∩ {x | Ψ (segre (R.lift x x)) 0 ≠ 0})) :=
    ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using hN)
  filter_upwards [hNae, sheetIndep K ι P e Ψ L A s hP hΨ hL hA hs] with y hyN hind
  have hy1 : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y := fun h => hyN (Or.inl h)
  have hfib : ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y = brW R Ψ '' (brQ R Ψ ⁻¹' {y} \ brBad R Ψ) := by
    ext w
    constructor
    · intro hw
      obtain ⟨x, -, hx0, hxq, rfl⟩ := exists_of_mem_fibre R Ψ hw hy1
      exact ⟨x, ⟨hxq, fun hbad => hyN (Or.inr ⟨x, ⟨hbad, hx0⟩, hxq⟩)⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have := brW_mem_fibre R Ψ hP.1 hP.2.1.2.1 (projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2)
      rwa [show brQ R Ψ x = y from hx.1] at this
  rw [hfib, finsum_mem_image ((brW_injOn R Ψ).mono (by exact fun x hx => show _ ∧ _ from
    ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩))]
  refine finsum_mem_congr rfl fun x hx => ?_
  obtain ⟨γ, hγ, hval⟩ := exists_sheet_brW R Ψ L A s hP hL hs x hx.2
  rw [show brQ R Ψ x = y from hx.1] at hγ hval
  unfold sheetDensity
  rw [dite_eq_left ⟨γ, hγ⟩]
  exact (hind _ _ _ (Exists.choose_spec (⟨γ, hγ⟩ : ∃ γ, IsSheet P Ψ y (brW R Ψ x) γ)) hγ).trans hval

end Res

theorem bridge {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {e : ℕ}
    (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι)
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hs : IsSectionOn P A s) :
    ptsIntegralAt P Ψ (pot L) (logNorm A s) =
      mInt R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) := by
  rw [pushForward_null R.A (fun j => potOf R (L j)) (fun j => potOf_isPotential R (L j) (hL j))
    (brQ R Ψ) (brBad R Ψ) (brBad_null R Ψ hP hΨ) (brGood R Ψ) (brFib_finite R Ψ hP hΨ) _
    (brIntegrable R L A s hP hL hA hs)]
  exact integral_congr_ae (brFibreSum_ae R Ψ L A s hP hΨ hL hA hs)

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

set_option linter.unusedSectionVars false

namespace SmallSectionPointHeight

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_eq_eval_mConeMap (y : (Σ k, ι k) → Ω) (f : MRing ι) :
    aeval y f = eval (fun _ ↦ (1 : Ω)) (mConeMap y f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [mConeMap]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p n hp =>
    rw [map_mul, map_mul, map_mul, hp]
    simp [mConeMap]

theorem notMem_mCoordIdeal {y : (Σ k, ι k) → Ω} {f : MRing ι} (hf : aeval y f ≠ 0) :
    f ∉ mCoordIdeal y := by
  intro h
  rw [mCoordIdeal, RingHom.mem_ker] at h
  exact hf (by rw [aeval_eq_eval_mConeMap, h, map_zero])

theorem coord_ne_zero {y : (Σ k, ι k) → Ω} {p : Σ k, ι k} (hp : (X p : MRing ι) ∉ mCoordIdeal y) :
    y p ≠ 0 := by
  intro h0
  apply hp
  rw [mCoordIdeal, RingHom.mem_ker]
  simp [mConeMap, h0]

theorem powLine_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m : ℕ) (z : (Σ k, ι k) → ℂ) :
    (IndefiniteRowSideFullHecke.HeightsSet.powLine A m).h z = A.h z ^ m := by
  induction m with
  | zero => simp [IndefiniteRowSideFullHecke.HeightsSet.powLine, IndefiniteRowSideFullHecke.HeightsSet.constLine]
  | succ m ih => simp [IndefiniteRowSideFullHecke.HeightsSet.powLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ih, pow_succ]

theorem aeval_chartMon (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (e : K → ℕ) :
    aeval y (IndefiniteRowSideFullHecke.HeightsSet.chartMon c e) = ∏ k, y ⟨k, c k⟩ ^ e k := by
  simp [IndefiniteRowSideFullHecke.HeightsSet.chartMon, map_prod, map_pow]

theorem vertR_le {W : Ideal (MRing ι)} {G H : MRing ι}
    (h : ∀ V ∈ divSupp W H, V ∈ divSupp W G ∧
      multAt (W ⊔ Ideal.span {H}) V ≤ multAt (W ⊔ Ideal.span {G}) V) :
    vertR W (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) H ≤ vertR W (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) G := by
  classical
  unfold vertR
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite W H),
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite W G)]
  have hsub : (divSupp_finite W H).toFinset ⊆ (divSupp_finite W G).toFinset := fun V hV ↦ by
    rw [Set.Finite.mem_toFinset] at hV ⊢
    exact (h V hV).1
  have hc : ∀ V : Ideal (MRing ι), 0 ≤ (if IsHorizontal V then (0 : ℝ) else
      (geoNum 0 V (fun j ↦ ((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j).a) : ℝ) * Real.log (charOf V)) := by
    intro V
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (by exact_mod_cast IndefiniteRowSideFullHecke.HeightsSet.geoNum_zero_nonneg V _)
        (Real.log_natCast_nonneg _)
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun V _ _ ↦
    mul_nonneg (Nat.cast_nonneg _) (hc V))
  refine Finset.sum_le_sum fun V hV ↦ ?_
  rw [Set.Finite.mem_toFinset] at hV
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (h V hV).2) (hc V)

end SmallSectionPointHeight


open SmallSectionPointHeight in
theorem SmallSectionPointHeight.proof (hOrd : SectionOrderAtPoint.Statement) :
    SmallSectionPointHeight.Statement := by
  intro K _ ι _ Ω _ y D A τ s II hII hP hbir hA hτ hs hs0 hsmall
  classical

  choose c hc using hP.2.1.2.2
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k ↦ coord_ne_zero (hc k)

  set ap : K → ℕ := fun k ↦ ((τ : ℤ) * A.a k).toNat with hap
  set an : K → ℕ := fun k ↦ (-((τ : ℤ) * A.a k)).toNat with han
  have hpn : ∀ k, (ap k : ℤ) = an k + τ * A.a k := fun k ↦ by
    have := Int.toNat_sub_toNat_neg ((τ : ℤ) * A.a k)
    simp only [hap, han]
    linarith
  obtain ⟨d, g0, h0, hg0, hh0, hh0y, hgh0⟩ := hbir (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * A.a k)))
  set G := g0 * IndefiniteRowSideFullHecke.HeightsSet.chartMon c ap with hGdef
  set H := h0 * IndefiniteRowSideFullHecke.HeightsSet.chartMon c an with hHdef
  have hG : IsMultiHomog G (d + ap) :=
    IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_mul hg0 (IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_chartMon c ap)
  have hH : IsMultiHomog H (d + an) :=
    IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_mul hh0 (IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_chartMon c an)
  have hdeg : ∀ k, ((d + ap) k : ℤ) = (d + an) k + τ * A.a k := fun k ↦ by
    simp only [Pi.add_apply, Nat.cast_add, hpn k]
    ring
  have hGH : aeval y G = s * aeval y H := by
    have hprod : ∀ k, y ⟨k, c k⟩ ^ ap k = y ⟨k, c k⟩ ^ ((τ : ℤ) * A.a k) * y ⟨k, c k⟩ ^ an k := fun k ↦ by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), hpn k, add_comm]
    have h1 : (∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * A.a k))) * ∏ k, y ⟨k, c k⟩ ^ ((τ : ℤ) * A.a k) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun k _ ↦ by rw [← zpow_add₀ (hyc k), neg_add_cancel, zpow_zero]
    rw [hGdef, hHdef, map_mul, map_mul, aeval_chartMon, aeval_chartMon, hgh0,
      Finset.prod_congr rfl fun k _ ↦ hprod k, Finset.prod_mul_distrib]
    linear_combination (s * aeval y h0 * ∏ k, y ⟨k, c k⟩ ^ an k) * h1
  have hHy : aeval y H ≠ 0 := by
    rw [hHdef, map_mul, aeval_chartMon]
    exact mul_ne_zero hh0y (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hyc k))
  have hGy : aeval y G ≠ 0 := by
    rw [hGH]
    exact mul_ne_zero hs0 hHy
  refine ⟨G * H, ⟨_, IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_mul hG hH⟩,
    notMem_mCoordIdeal (by rw [map_mul]; exact mul_ne_zero hGy hHy), ?_⟩
  intro W hW hPW hfW
  have hGW : G ∉ W := fun h ↦ hfW (W.mul_mem_right H h)
  have hHW : H ∉ W := fun h ↦ hfW (W.mul_mem_left G h)

  have hI : IsIntersectionFamily (II K ι) := hII K ι
  set E := IndefiniteRowSideFullHecke.HeightsSet.powLine A τ with hEdef
  have hE : IsSmoothHerm E := IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_powLine hA τ
  set B := HermLine.sqMetric (ι := ι) (d + an) with hBdef
  have hB : IsSmoothHerm B := isSmoothHerm_sqMetric _
  have hEB : IsSmoothHerm (E.tensor B) := IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_tensor hE hB
  have hEBa : ∀ k, (E.tensor B).a k = ((d + ap) k : ℕ) := fun k ↦ by
    show E.a k + B.a k = _
    rw [hEdef, IndefiniteRowSideFullHecke.HeightsSet.powLine_a, hdeg k]
    show _ + ((d + an) k : ℤ) = _
    ring
  have hsecG : IsSectionOn W (E.tensor B) G := ⟨_, hEBa, hG, hGW⟩
  have hsecH : IsSectionOn W B H := ⟨_, fun k ↦ rfl, hH, hHW⟩
  have hRG := IndefiniteRowSideFullHecke.HeightsSet.inter_eq_recR (II K ι) hI hW hEB hEBa hG hGW
  have hRH := IndefiniteRowSideFullHecke.HeightsSet.inter_eq_recR (II K ι) hI hW hB (fun k ↦ rfl) hH hHW
  have hadd := IndefiniteRowSideFullHecke.HeightsSet.inter_tensor (II K ι) hI hW hE hB
  have hpow := IndefiniteRowSideFullHecke.HeightsSet.inter_powLine (II K ι) hI hW hA τ
  rw [recR_eq, Inter.cycR_eq_vertR_of_dimOne Inter.arithVarZero _ hW hsecG] at hRG
  rw [recR_eq, Inter.cycR_eq_vertR_of_dimOne Inter.arithVarZero _ hW hsecH] at hRH

  have hvert := vertR_le (hOrd K ι Ω y A.a τ s W G H (d + ap) (d + an) hW hPW hs hG hH hdeg hGH hGW hHW)

  have harch : arInt W G (E.tensor B) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) ≤
      arInt W H B (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) := by
    unfold arInt
    rw [Inter.ptsIntegral_add_of_dimOne fibreFinite hW _ (g₁ := logNorm B H)
      (g₂ := fun z ↦ logNorm (E.tensor B) G z - logNorm B H z) fun z _ ↦ by ring]
    refine add_le_of_nonpos_right (IndefiniteRowSideFullHecke.HeightsSet.ptsIntegral_nonpos W _ fun z hz ↦ ?_)
    show logNorm (E.tensor B) G z - logNorm B H z ≤ 0
    have hGz := norm_pos_iff.mpr (Inter.eval_ne_zero_of_dimOne Inter.arithVarZero hW hsecG hz)
    have hHz := norm_pos_iff.mpr (Inter.eval_ne_zero_of_dimOne Inter.arithVarZero hW hsecH hz)
    have hAz := A.pos z hz.1
    have hBz := B.pos z hz.1
    have hEz : E.h z = A.h z ^ τ := powLine_h A τ z
    have hEz0 : 0 < E.h z := hEz ▸ pow_pos hAz τ
    have hzP : z ∈ mcPts (mCoordIdeal y) := ⟨hz.1, fun f hf ↦ hz.2 f (hPW hf)⟩
    have hsm := hsmall (d + ap) (d + an) G H z hG hH hdeg hGH hzP
    rw [← hEz] at hsm
    refine sub_nonpos.mpr (Real.log_le_log (div_pos hGz (mul_pos hEz0 hBz)) ?_)
    show _ / (E.h z * B.h z) ≤ _ / B.h z
    rw [div_le_div_iff₀ (mul_pos hEz0 hBz) hBz]
    nlinarith [mul_le_mul_of_nonneg_right hsm hBz.le]

  have hτI : 0 ≤ (τ : ℝ) * II K ι W 1 ![A] := by
    rw [← hpow]
    linarith
  have hτ0 : (0 : ℝ) < τ := by exact_mod_cast hτ
  exact le_of_mul_le_mul_left (by rw [mul_zero]; exact hτI) hτ0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace CurvePointsFinite

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_eq_eval₂ {F : Type*} [CommRing F] {inst : Algebra ℤ F} (y : (Σ k, ι k) → F) (f : MRing ι) :
    @aeval ℤ F _ _ _ inst y f = eval₂ (Int.castRingHom F) y f := by
  rw [aeval_def]
  congr 1
  exact RingHom.ext_int _ _

def genericPt (W : Ideal (MRing ι)) [W.IsPrime] : (Σ k, ι k) → FractionRing (MRing ι ⧸ W) :=
  fun p ↦ algebraMap (MRing ι ⧸ W) _ (Ideal.Quotient.mk W (X p))

theorem aeval_genericPt (W : Ideal (MRing ι)) [W.IsPrime] (f : MRing ι) :
    aeval (genericPt W) f = algebraMap (MRing ι ⧸ W) _ (Ideal.Quotient.mk W f) := by
  have h : (aeval (genericPt W) : MRing ι →ₐ[ℤ] _).toRingHom =
      (algebraMap (MRing ι ⧸ W) (FractionRing (MRing ι ⧸ W))).comp (Ideal.Quotient.mk W) :=
    ringHom_ext (fun n ↦ by simp) (fun p ↦ by simp [genericPt])
  exact RingHom.congr_fun h f

theorem aeval_genericPt_eq_zero_iff (W : Ideal (MRing ι)) [W.IsPrime] (f : MRing ι) :
    aeval (genericPt W) f = 0 ↔ f ∈ W := by
  rw [aeval_genericPt, ← Ideal.Quotient.eq_zero_iff_mem]
  exact (IsFractionRing.injective (MRing ι ⧸ W) (FractionRing (MRing ι ⧸ W))).eq_iff' (map_zero _)

theorem mCoordIdeal_genericPt (W : Ideal (MRing ι)) [W.IsPrime] (hW : IsMultiHomogIdeal W) :
    mCoordIdeal (genericPt W) = W := by
  apply le_antisymm
  · intro f hf
    rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.eq_sum_multihomogeneous_components f]
    refine Ideal.sum_mem _ fun b _ ↦ ?_
    have h1 := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.i2comp_mem (CoordinateConeArithVar.isMultiHomogIdeal _) b hf
    rw [mCoordIdeal, RingHom.mem_ker,
      ProjLine.mConeMap_eq_of_isMultiHomog _ (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_i2comp b f)] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · exact (aeval_genericPt_eq_zero_iff W _).1 (by
        have h' := MvPolynomial.C_eq_zero.1 h
        rw [aeval_eq_eval₂] at h' ⊢
        exact h')
    · exact absurd h (Finset.prod_ne_zero_iff.2 fun k _ ↦ pow_ne_zero _ (MvPolynomial.X_ne_zero k))
  · obtain ⟨S, hS, hWS⟩ := hW
    calc W = Ideal.span S := hWS
      _ ≤ mCoordIdeal (genericPt W) := Ideal.span_le.2 fun f hf ↦ by
        obtain ⟨a, ha⟩ := hS f hf
        have hfW : f ∈ W := hWS ▸ Ideal.subset_span hf
        show f ∈ RingHom.ker (mConeMap (genericPt W))
        have h0 := (aeval_genericPt_eq_zero_iff W f).2 hfW
        rw [RingHom.mem_ker, ProjLine.mConeMap_eq_of_isMultiHomog _ ha]
        exact mul_eq_zero_of_left (MvPolynomial.C_eq_zero.2 (by
          rw [aeval_eq_eval₂] at h0 ⊢
          exact h0)) _

theorem charZero_fractionRing (W : Ideal (MRing ι)) [W.IsPrime] (hH : IsHorizontal W) :
    CharZero (FractionRing (MRing ι ⧸ W)) := by
  have hinj : Function.Injective (algebraMap ℤ (FractionRing (MRing ι ⧸ W))) := by
    have e : algebraMap ℤ (FractionRing (MRing ι ⧸ W)) =
        (algebraMap (MRing ι ⧸ W) (FractionRing (MRing ι ⧸ W))).comp (algebraMap ℤ (MRing ι ⧸ W)) :=
      RingHom.ext_int _ _
    rw [e]
    exact (IsFractionRing.injective (MRing ι ⧸ W) (FractionRing (MRing ι ⧸ W))).comp (CoordinateConeArithVar.algebraMap_injective W hH)
  exact charZero_of_injective_algebraMap hinj

end CurvePointsFinite


open CurvePointsFinite in
theorem CurvePointsFinite.proof : CurvePointsFinite.Statement := by
  intro K _ ι _ W hW
  have : W.IsPrime := hW.2.1.1
  have := charZero_fractionRing W hW.2.2.1
  have hEq := mCoordIdeal_genericPt W hW.2.1.2.1
  have hP : IsArithVar (mCoordIdeal (genericPt W)) 1 := by rw [hEq]; exact hW
  have hdeg := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.degC_eq hP
  rw [hEq, GroundTheory.Heights₂.Heights.degC_eq_card_projPts] at hdeg
  have := IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree.isAlgebraic_blockFnField hP
  set L := ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField (genericPt W)
  set S : Set (FractionRing (MRing ι ⧸ W)) :=
    {t | ∃ p q : Σ k, ι k, p.1 = q.1 ∧ t = genericPt W p / genericPt W q}
  have hSfin : S.Finite := (Set.finite_range fun pq : (Σ k, ι k) × (Σ k, ι k) ↦
      genericPt W pq.1 / genericPt W pq.2).subset fun t ⟨p, q, _, ht⟩ ↦ ⟨(p, q), ht.symm⟩
  have : Finite S := hSfin.to_subtype
  have hint : ∀ t ∈ S, IsIntegral ℚ t := fun t ht ↦
    ((Algebra.IsAlgebraic.isAlgebraic (⟨t, IntermediateField.subset_adjoin ℚ S ht⟩ : L)).isIntegral).map
      L.val
  have : FiniteDimensional ℚ L := IntermediateField.finiteDimensional_adjoin hint
  have hpos : 0 < Nat.card (L →ₐ[ℚ] ℂ) := Nat.card_pos_iff.2 ⟨⟨IsAlgClosed.lift⟩, inferInstance⟩
  exact (Nat.card_pos_iff.1 (hdeg ▸ hpos)).2

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end
