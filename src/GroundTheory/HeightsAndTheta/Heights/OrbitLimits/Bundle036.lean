module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalAmple
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveOrbitEmbedding
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle035
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle034
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle002
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle003
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle007
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
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.HilbertSamuel.LiftBirationalAmple

noncomputable section

namespace CurveSectionQuotientLocal

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  (y : (Σ k, ι k) → Ω)

theorem chart_mem_curveSectionMod (c : ∀ k, ι k) (d : K → ℕ) :
    ∏ k, y ⟨k, c k⟩ ^ d k ∈ curveSectionMod y (fun k => (d k : ℤ)) := by
  classical
  show _ ∈ chartLat y _ 1
  have h := chartLat_prod (y := y) Finset.univ (fun k => y ⟨k, c k⟩ ^ d k)
    (fun k => d k • (Pi.single k 1 : K → ℤ))
    (fun k _ => chartLat_pow (chartLat_var (y := y) ⟨k, c k⟩) (d k))
  convert h using 2
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    simp [Ne.symm hk]
  · simp


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem exists_mul_mem_of_mem_chartRingZ (m : Ideal (curveRing y)) (hm : m.IsPrime) (c : ∀ k, ι k)
    (h : ∀ p : Σ k, ι k, ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * (y p / y ⟨p.1, c p.1⟩) = a)
    {z : Ω} (hz : z ∈ chartRingZ y c) :
    ∃ a b : curveRing y, b ∉ m ∧ (b : Ω) * z = a := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact h p
  | algebraMap r =>
    refine ⟨(r : curveRing y), 1, (Ideal.ne_top_iff_one m).mp hm.ne_top, ?_⟩
    simp
  | add x z _ _ hx hz =>
    obtain ⟨a₁, b₁, hb₁, e₁⟩ := hx
    obtain ⟨a₂, b₂, hb₂, e₂⟩ := hz
    refine ⟨b₂ * a₁ + b₁ * a₂, b₁ * b₂, fun hmem => (hm.mem_or_mem hmem).elim hb₁ hb₂, ?_⟩
    push_cast
    rw [← e₁, ← e₂]
    ring
  | mul x z _ _ hx hz =>
    obtain ⟨a₁, b₁, hb₁, e₁⟩ := hx
    obtain ⟨a₂, b₂, hb₂, e₂⟩ := hz
    refine ⟨a₁ * a₂, b₁ * b₂, fun hmem => (hm.mem_or_mem hmem).elim hb₁ hb₂, ?_⟩
    push_cast
    rw [← e₁, ← e₂]
    ring

end CurveSectionQuotientLocal


open CurveSectionQuotientLocal in
theorem CurveSectionQuotLocal.proof : CurveSectionQuotLocal.Statement := by
  intro K _ ι _ Ω _ y s d _hy _hs _hsP m c hm hc hrat a b hb hba
  set x := aeval y s with hx_def
  set e₀ : Ω := ∏ k, y ⟨k, c k⟩ ^ d k with he₀_def
  have he₀ : e₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)

  let e : curveSectionMod y (fun k => (d k : ℤ)) := ⟨e₀, chart_mem_curveSectionMod y c d⟩
  let φ : curveRing y →ₗ[curveRing y] curveSectionQuot y (fun k => (d k : ℤ)) x :=
    LinearMap.toSpanSingleton (curveRing y) _ (Submodule.Quotient.mk e)
  have hφ : ∀ β : curveRing y, φ β = Submodule.Quotient.mk (β • e) := fun β => by
    simp [φ, Submodule.Quotient.mk_smul]
  have hφ0 : ∀ β : curveRing y, φ β = 0 ↔ ∃ γ : curveRing y, (γ : Ω) * x = β * e₀ := by
    intro β
    rw [hφ, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_span_singleton]
    rfl
  have hle : Ideal.span {a} ≤ LinearMap.ker φ := by
    rw [Ideal.span_singleton_le_iff_mem, LinearMap.mem_ker, hφ0]
    exact ⟨b, hba⟩
  let ψ : (curveRing y ⧸ Ideal.span {a}) →ₗ[curveRing y] curveSectionQuot y (fun k => (d k : ℤ)) x :=
    (Ideal.span {a}).liftQ φ hle

  have hker : ∀ q, ψ q = 0 → b • q = 0 := by
    intro q hq
    obtain ⟨β, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨γ, hγ⟩ := (hφ0 β).mp hq
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
      Ideal.mem_span_singleton']
    refine ⟨γ, Subtype.ext ?_⟩
    push_cast
    apply mul_right_cancel₀ he₀
    rw [mul_assoc, ← hba, mul_assoc, ← hγ]
    ring

  have hsurj0 : ∀ n : curveSectionMod y (fun k => (d k : ℤ)),
      ∃ r : curveRing y, r ∉ m ∧ ∃ β : curveRing y, r • n = β • e := by
    intro n
    have hn : (n : Ω) ∈ chartLat y (fun k => (d k : ℤ)) 1 := n.2
    have hnc : (n : Ω) * e₀⁻¹ ∈ chartRingZ y c := by
      have h1 := (mem_chartLat_one y).mp hn c hc
      have h2 : ∏ k, y ⟨k, c k⟩ ^ (-((fun k => (d k : ℤ)) k)) = e₀⁻¹ := by
        rw [he₀_def, ← Finset.prod_inv_distrib]
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [zpow_neg, zpow_natCast]
      rwa [h2] at h1
    obtain ⟨β, r, hr, hβ⟩ := exists_mul_mem_of_mem_chartRingZ y m hm c hrat hnc
    refine ⟨r, hr, β, Subtype.ext ?_⟩
    show (r : Ω) * n = β * e₀
    rw [← hβ]
    field_simp

  let S := m.primeCompl
  let Φ := IsLocalizedModule.map S (LocalizedModule.mkLinearMap S (curveRing y ⧸ Ideal.span {a}))
    (LocalizedModule.mkLinearMap S (curveSectionQuot y (fun k => (d k : ℤ)) x)) ψ
  have hΦ : ∀ q (r : S), Φ (LocalizedModule.mk q r) = LocalizedModule.mk (ψ q) r :=
    fun q r => IsLocalizedModule.map_LocalizedModules S _ q r
  have hinj : Function.Injective Φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z
    refine LocalizedModule.induction_on (β := fun z => Φ z = 0 → z = 0) (fun q r hz => ?_) z
    rw [hΦ, ← LocalizedModule.zero_mk r, LocalizedModule.mk_eq] at hz
    obtain ⟨u, hu⟩ := hz
    simp only [smul_zero, Submonoid.smul_def] at hu
    rw [← map_smul, ← map_smul] at hu
    have hq := hker _ hu
    rw [← LocalizedModule.zero_mk r, LocalizedModule.mk_eq]
    refine ⟨⟨b * u, S.mul_mem hb u.2⟩, ?_⟩
    simp only [smul_zero, Submonoid.smul_def, mul_smul]
    exact hq
  have hsurj : Function.Surjective Φ := by
    intro z
    refine LocalizedModule.induction_on (β := fun z => ∃ w, Φ w = z) (fun n r => ?_) z
    obtain ⟨n', rfl⟩ := Submodule.Quotient.mk_surjective _ n
    obtain ⟨r', hr', β, hβ⟩ := hsurj0 n'
    refine ⟨LocalizedModule.mk (Submodule.Quotient.mk β) (⟨r', hr'⟩ * r), ?_⟩
    rw [hΦ]
    have hψ : ψ (Submodule.Quotient.mk β) = Submodule.Quotient.mk (β • e) := by
      rw [← hφ]
      rfl
    rw [hψ, ← hβ, Submodule.Quotient.mk_smul]
    exact LocalizedModule.mk_cancel_common_left ⟨r', hr'⟩ r _
  have := hm
  let E := (LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩).extendScalarsOfIsLocalization S
    (Localization.AtPrime m)
  unfold locLen
  rw [dite_eq_left hm, dite_eq_left hm, E.length_eq]

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

theorem CurveBoxSmall.zpow_mul_toNat_neg {F : Type} [Field F] {t : F} (ht : t ≠ 0) (n : ℤ) :
    t ^ n * t ^ (-n).toNat = t ^ n.toNat :=
  calc t ^ n * t ^ (-n).toNat = t ^ ((n.toNat : ℤ) - ((-n).toNat : ℤ)) * t ^ (-n).toNat := by
        rw [Int.toNat_sub_toNat_neg]
    _ = t ^ n.toNat := by
        rw [zpow_sub₀ ht, zpow_natCast, zpow_natCast, div_mul_cancel₀ _ (pow_ne_zero _ ht)]

theorem CurveBoxSmall.proof : CurveBoxSmall.Statement := by
  intro K _ ι _ Ω _ y A c hP hB hc τ s
  classical
  have hU : ∀ σ : Ω →+* ℂ, ‖σ (chartUnit y c A.a τ)‖ = (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ := fun σ => by
    rw [chartUnit, map_prod, norm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_zpow₀, norm_zpow, ← zpow_natCast (_ ^ A.a k), ← zpow_mul, mul_comm (A.a k)]
  have hQ : ∀ σ : Ω →+* ℂ, 0 < (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ := fun σ =>
    pow_pos (Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr ((map_ne_zero σ).mpr (hc k))) _) _
  constructor
  · intro hS σ
    obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hB (s / chartUnit y c A.a τ)
    let ap : K → ℕ := fun k => ((τ : ℤ) * A.a k).toNat
    let am : K → ℕ := fun k => (-((τ : ℤ) * A.a k)).toNat
    have hU0 : chartUnit y c A.a τ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
    have hu : chartUnit y c A.a τ * ∏ k, y ⟨k, c k⟩ ^ am k = ∏ k, y ⟨k, c k⟩ ^ ap k := by
      rw [chartUnit, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => CurveBoxSmall.zpow_mul_toNat_neg (hc k) _
    have hdeg : ∀ k, (((d + ap) k : ℕ) : ℤ) = ((d + am) k : ℕ) + τ * A.a k := fun k => by
      have := Int.toNat_sub_toNat_neg ((τ : ℤ) * A.a k)
      simp only [Pi.add_apply, Nat.cast_add, ap, am]
      omega
    have hval : aeval y (g * curveChartMono c ap) = s * aeval y (h * curveChartMono c am) := by
      simp only [map_mul, curveChartMono, map_prod, map_pow, aeval_X]
      rw [← hu, hgh]
      field_simp
    have hS' := hS _ _ _ _ _ (CurveOrbit.isMultiHomog_mul hg (isMultiHomog_curveChartMono c ap))
      (CurveOrbit.isMultiHomog_mul hh (isMultiHomog_curveChartMono c am)) hdeg hval (CurveOrbit.mem_mcPts σ y hc)
    rw [CurveOrbit.eval_comp, CurveOrbit.eval_comp] at hS'
    simp only [map_mul, curveChartMono, map_prod, map_pow, aeval_X, norm_mul, norm_prod, norm_pow] at hS'
    have hsu : s / chartUnit y c A.a τ = aeval y g / aeval y h := eq_div_of_mul_eq hh0 hgh.symm
    have hσh : 0 < ‖σ (aeval y h)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hh0)
    have ht : ∀ k, ‖σ (y ⟨k, c k⟩)‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr (hc k))
    have hR : (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ * ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k =
        ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ ap k := by
      rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast (_ ^ A.a k), ← zpow_mul, mul_comm (A.a k)]
      exact CurveBoxSmall.zpow_mul_toNat_neg (ht k) _
    have hRm : 0 < ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k :=
      Finset.prod_pos fun k _ => pow_pos (lt_of_le_of_ne (norm_nonneg _) (ht k).symm) _
    rw [hsu, map_div₀, norm_div, chartRadius, div_pow, div_le_div_iff₀ hσh (hQ σ)]
    refine le_of_mul_le_mul_right ?_ hRm
    calc ‖σ (aeval y g)‖ * (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ A.a k) ^ τ * ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k
        = ‖σ (aeval y g)‖ * ∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ ap k := by rw [mul_assoc, hR]
      _ ≤ ‖σ (aeval y h)‖ * (∏ k, ‖σ (y ⟨k, c k⟩)‖ ^ am k) * A.h (fun p => σ (y p)) ^ τ := hS'
      _ = _ := by ring
  · intro hbox dg dh g h z hg hh hdeg hgs hz
    obtain ⟨σ, l, hl, rfl⟩ := CurveOrbit.exists_sameOrbit hP hB hz
    beta_reduce
    have hb := hbox σ
    rw [map_div₀, norm_div, chartRadius, div_pow, hU σ, div_le_div_iff_of_pos_right (hQ σ)] at hb
    have hlam : ‖∏ k, l k ^ dg k‖ = ‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ := by
      rw [norm_prod, norm_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hlk : ‖l k‖ ≠ 0 := norm_ne_zero_iff.mpr (hl k)
      rw [norm_pow, norm_pow, ← zpow_natCast (‖l k‖) (dg k), hdeg k, zpow_add₀ hlk, zpow_natCast,
        ← zpow_natCast (_ ^ A.a k), ← zpow_mul, mul_comm (A.a k)]
    rw [CurveOrbit.eval_smul _ l hg, CurveOrbit.eval_smul _ l hh, A.smul l _ hl, CurveOrbit.eval_comp,
      CurveOrbit.eval_comp, hgs, map_mul, norm_mul, norm_mul, norm_mul, hlam, mul_pow]
    calc ‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ * (‖σ s‖ * ‖σ (aeval y h)‖)
        = (‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ * ‖σ (aeval y h)‖) * ‖σ s‖ := by ring
      _ ≤ (‖∏ k, l k ^ dh k‖ * (∏ k, ‖l k‖ ^ A.a k) ^ τ * ‖σ (aeval y h)‖) * A.h (fun p => σ (y p)) ^ τ :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel LiftBlockGraph

noncomputable section

theorem LiftBlockDatum.proof (hE : ResExistsStatement) (hVol : ResVolume.Statement)
    (hPts : LiftGraphPoints.Statement) (hMet : LiftGraphMetric.Statement) : LiftBlockDatum.Statement := by
  intro K _ _ ι _ Ω _ _ y D N P0 a ι' _ x' hD harith _ hP0 hsemi hconj _ hx' hgen hbir'
  have hv : ∀ j, liftCoords x' j ∈ chartLat y (a • N.a) 1 := fun j => hx' _
  have hgv := generatesOn_liftCoords y (a • N.a) x' hgen
  have harith' := isArithVar_addBlock y (a • N.a) (liftCoords x') harith hv hgv
  obtain ⟨A, hAdeg, hAconj, hAsemi, hrel⟩ :=
    hMet K ι Ω y N P0 a (Fintype.card ι') (liftCoords x') hP0 hsemi hconj hv hgv
  have hnot : ¬ (⊤ : Ideal (MRing (addIdx ι (Fintype.card ι')))) ≤ mCoordIdeal (addBlock y (liftCoords x')) :=
    fun h => harith'.2.1.1.ne_top (top_le_iff.mp h)
  obtain ⟨J, -, -, -, ⟨R⟩⟩ := hE (Option K) (addIdx ι (Fintype.card ι')) _ ⊤ D harith'
    isMultiHomogIdeal_top hnot
  let _ : MeasurableSpace R.toAnRes.X := borel _
  have : BorelSpace R.toAnRes.X := ⟨rfl⟩
  obtain ⟨dV, hdV⟩ := hVol (Option K) (addIdx ι (Fintype.card ι')) _ J D R.toAnRes harith'
  refine ⟨
    { y := addBlock y (liftCoords x'), k₀ := none, A := A, P0 := mCoordIdeal (addBlock y (liftCoords x')),
      J := J, R := R.toAnRes, meas := borel _, borel := ⟨rfl⟩, dV := dV, one_le := hD, arith := harith',
      birat := blockBirational_addBlock y x' hbir', deg := hAdeg, conjInv := hAconj, normalForm_baseLattice_le_dualSpan_sup_line := le_rfl,
      semipos := hAsemi, vol := hdV }, rfl, rfl, hrel, ?_⟩
  exact hPts K ι Ω y (a • N.a) (Fintype.card ι') (liftCoords x') hv hgv

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem ImageArith.of_found (hBT : BlockTrdeg.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.ImageArithStatement := by
  intro K _ ι _ K' _ ι' _ κ v P' d' hK hbm hP'
  classical
  obtain ⟨-, hMP', hHor', hdim'⟩ := hP'

  have hMP : IsMultiProjPrime (imageZ v P') := by
    rw [← Bridge.isMultiProjPrime_iff] at hMP' ⊢
    exact FieldNumbers.ContractRelevant.isMultiProjPrime_comap_rename (j := κ) (g := v) hbm.2.2.1 hbm.1 hbm.2.1
      (fun w hw ↦ hbm.2.2.2 w hw |>.imp fun _ h ↦ h) hMP'

  have hHor : IsHorizontal (imageZ v P') := by
    refine (Ideal.ext fun a ↦ ?_).trans hHor'
    simp only [imageZ, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_C]

  have : (P').IsPrime := hMP'.1
  set A' := MRing ι' ⧸ P'
  set L := FractionRing A'
  have hinj : Function.Injective (algebraMap ℤ A') := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at ha
    have h' : a ∈ (P').comap (C : ℤ →+* MRing ι') := ha
    rw [show (P').comap (C : ℤ →+* MRing ι') = ⊥ from hHor'] at h'
    exact (Submodule.mem_bot ℤ).mp h'
  have : CharZero A' := charZero_of_injective_algebraMap hinj
  have : CharZero L := charZero_of_injective_algebraMap (IsFractionRing.injective A' L)
  set φ' : MRing ι' →+* L := (algebraMap A' L).comp (Ideal.Quotient.mk P')
  have hker' : RingHom.ker φ' = P' := by
    rw [← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective A' L),
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  set φ : MRing ι →+* L := φ'.comp (rename v : MRing ι →ₐ[ℤ] MRing ι').toRingHom
  have hker : RingHom.ker φ = imageZ v P' := by
    rw [← RingHom.comap_ker, hker']
    rfl

  obtain ⟨s', hs', hd'⟩ := TrdegAdjoin.ringKrullDim_quotient_ker φ'
  obtain ⟨s, hs, hd⟩ := TrdegAdjoin.ringKrullDim_quotient_ker φ
  rw [hker'] at hd'
  rw [hker] at hd
  have hφX : (Set.range fun p : Σ k, ι k ↦ φ (X p)) = Set.range fun p ↦ φ' (X (v p)) := by
    simp [φ]
  rw [hφX] at hs

  have h1 := hBT K ι K' ι' κ v P' L φ' hbm hMP' hker'
  rw [hs, hs'] at h1
  have h2 := @hBT Empty _ (fun k ↦ k.elim) (fun k ↦ k.elim) K _ ι _ (fun k ↦ k.elim) (fun p ↦ p.1.elim)
    (imageZ v P') L _ _ φ
    ⟨fun a ↦ a.elim, fun p ↦ p.1.elim, fun p ↦ p.1.elim, fun q ⟨a, _⟩ ↦ a.elim⟩ hMP hker
  rw [hφX, hs] at h2
  simp only [Fintype.card_empty, Nat.sub_zero] at h2
  have h1' : s + (Fintype.card K' - Fintype.card K) ≤ s' := by exact_mod_cast h1
  have h2' : Fintype.card K ≤ s := by
    have := le_trans (self_le_add_left _ _) h2
    exact_mod_cast this
  have hKK : Fintype.card K ≤ Fintype.card K' := Fintype.card_le_of_injective κ hbm.1
  rw [hdim'] at hd'
  have h3 : d' + Fintype.card K' = s' + 1 := by exact_mod_cast hd'
  refine ⟨s + 1 - Fintype.card K, by omega, hK, hMP, hHor, ?_⟩
  rw [hd]
  have : s + 1 - Fintype.card K + Fintype.card K = s + 1 := by omega
  rw [this]
  push_cast
  rfl

end GroundTheory.Heights₂.Heights
end
end
