module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBirationalModelExists
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle034
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PSemiPosTwist
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PTorusInvLevi
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle006

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace RatioAlgebraicDependence

variable {K : Type} {ι : K → Type} {d : ℕ}

def homog (c : ∀ k, ι k) (p : Fin d → Σ k, ι k) (f : MvPolynomial (Fin d) ℤ) : MvPolynomial (Σ k, ι k) ℤ :=
  ∑ m ∈ f.support, C (AddMonoidAlgebra.coeff f m) *
    ∏ j, X (p j) ^ m j * X ⟨(p j).1, c (p j).1⟩ ^ (f.totalDegree - m j)

theorem aeval_homog {F : Type} [Field F] [Algebra ℤ F] (c : ∀ k, ι k) (p : Fin d → Σ k, ι k)
    (f : MvPolynomial (Fin d) ℤ) (w : (Σ k, ι k) → F) (hw : ∀ j, w ⟨(p j).1, c (p j).1⟩ ≠ 0) :
    aeval w (homog c p f) = (∏ j, w ⟨(p j).1, c (p j).1⟩) ^ f.totalDegree *
      aeval (fun j ↦ w (p j) / w ⟨(p j).1, c (p j).1⟩) f := by
  classical
  have hsum : aeval (fun j ↦ w (p j) / w ⟨(p j).1, c (p j).1⟩) f =
      ∑ m ∈ f.support, aeval (fun j ↦ w (p j) / w ⟨(p j).1, c (p j).1⟩) (monomial m (AddMonoidAlgebra.coeff f m)) := by
    conv_lhs => rw [f.as_sum]

    rw [map_sum]

  rw [hsum, Finset.mul_sum, homog, map_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hle : ∀ j, m j ≤ f.totalDegree := fun j ↦
    (monomial_le_degreeOf j hm).trans (degreeOf_le_totalDegree f j)
  rw [map_mul, aeval_C, map_prod, aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
    ← Finset.prod_pow, mul_left_comm, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  obtain ⟨e, he⟩ := Nat.exists_eq_add_of_le (hle j)
  rw [map_mul, map_pow, map_pow, aeval_X, aeval_X, div_pow, he, Nat.add_sub_cancel_left, pow_add]
  rw [mul_comm (w ⟨(p j).1, c (p j).1⟩ ^ m j), mul_assoc, mul_div_cancel₀ _ (pow_ne_zero _ (hw j)),
    mul_comm]

end RatioAlgebraicDependence


open RatioAlgebraicDependence in
theorem RatioAlgDep.proof : RatioAlgDep.Statement := by
  intro K _ ι _ Q d c p hQ
  classical
  by_cases hX : ∃ k, (X ⟨k, c k⟩ : MRing ι) ∈ Q
  · obtain ⟨k, hk⟩ := hX
    refine ⟨1, one_ne_zero, fun z hz hzc ↦ absurd ?_ (hzc k)⟩
    simpa using hz _ hk
  push Not at hX
  obtain ⟨Ω, _, y, hy, hbir⟩ := HilbertSamuel.BirationalModelExists.proof K ι Q d hQ
  have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 ↦ hX k (by
    rw [← hy, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul])
  obtain ⟨_, ⟨hprime, -, -⟩, hhor, hdim⟩ := hQ
  have htr := ConeTrdeg.proof K ι Ω y hbir (fun k ↦ ⟨c k, hc k⟩) (hy ▸ hhor)
  rw [hy] at htr
  have := hprime
  have hA := IntDomainDim.proof (MRing ι ⧸ Q) (CoordinateConeArithVar.algebraMap_injective Q hhor)
  rw [hdim, htr, map_add (f := _), map_natCast] at hA
  have hA' : ((d + Fintype.card K : ℕ) : ℕ∞) =
      Cardinal.toENat (Algebra.trdeg ℤ Ω) + Fintype.card K + 1 := by exact_mod_cast hA
  have hlt : Algebra.trdeg ℤ Ω < d := by
    rw [← Cardinal.toENat_lt_natCast]
    obtain ⟨n, hn⟩ : ∃ n : ℕ, Cardinal.toENat (Algebra.trdeg ℤ Ω) = n := by
      refine ENat.ne_top_iff_exists.mp (fun htop ↦ ?_) |>.imp fun _ h ↦ h.symm
      rw [htop] at hA'
      simp at hA'
    rw [hn] at hA' ⊢
    have : d + Fintype.card K = n + Fintype.card K + 1 := by exact_mod_cast hA'
    exact_mod_cast (by omega : n < d)
  have hdep : ¬ AlgebraicIndependent ℤ (fun j : Fin d ↦ y (p j) / y ⟨(p j).1, c (p j).1⟩) :=
    fun hind ↦ by
      have h := hind.cardinalMk_le_trdeg
      rw [Cardinal.mk_fin] at h
      exact absurd hlt (not_lt.2 h)
  rw [algebraicIndependent_iff] at hdep
  push Not at hdep
  obtain ⟨f, hf0, hfne⟩ := hdep

  have hH : homog c p f ∈ Q := by
    rw [← hy, mCoordIdeal, RingHom.mem_ker]
    set L := FractionRing (MvPolynomial K Ω)
    let φ : MvPolynomial K Ω →ₐ[ℤ] L :=
      { algebraMap (MvPolynomial K Ω) L with
        commutes' := fun n ↦ by simp }
    have hφ : Function.Injective φ := fun a b h ↦ IsFractionRing.injective (MvPolynomial K Ω) L h
    have hw : ∀ q : Σ k, ι k, y q ≠ 0 → φ (C (y q) * X q.1) ≠ 0 := fun q hq ↦ by
      rw [Ne, ← map_zero φ, hφ.eq_iff]
      exact mul_ne_zero (by rwa [Ne, C_eq_zero]) (X_ne_zero _)
    have hrat : ∀ j, φ (C (y (p j)) * X (p j).1) / φ (C (y ⟨(p j).1, c (p j).1⟩) * X (p j).1) =
        φ (C (y (p j) / y ⟨(p j).1, c (p j).1⟩)) := fun j ↦ by
      rw [div_eq_iff (hw _ (hc _)), ← map_mul, ← mul_assoc, ← C_mul, div_mul_cancel₀ _ (hc _)]
    refine hφ ?_
    rw [map_zero, mConeMap, comp_aeval_apply, aeval_homog c p f _ (fun j ↦ hw _ (hc _))]
    simp only [hrat]
    let ψ : Ω →ₐ[ℤ] L := φ.comp (IsScalarTower.toAlgHom ℤ Ω (MvPolynomial K Ω))
    have key : (aeval fun j ↦ φ (C (y (p j) / y ⟨(p j).1, c (p j).1⟩))) f =
        ψ (aeval (fun j ↦ y (p j) / y ⟨(p j).1, c (p j).1⟩) f) := by
      rw [comp_aeval_apply]
      rfl
    rw [key, hf0, map_zero, mul_zero]
  refine ⟨f, hfne, fun z hz hzc ↦ ?_⟩
  have h1 := hz _ hH
  rw [eval_map, ← algebraMap_int_eq, ← aeval_def, aeval_homog c p f z (fun j ↦ hzc _)] at h1
  rw [eval_map, ← algebraMap_int_eq, ← aeval_def]
  exact (mul_eq_zero.1 h1).resolve_left
    (pow_ne_zero _ (Finset.prod_ne_zero_iff.2 fun j _ ↦ hzc _))

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ComplexOrder

namespace PointsAbsIntegrable

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem cxHessian_tensor {D : ℕ} {X Y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hX : IsSmoothHerm X) (hY : IsSmoothHerm Y)
    {γ : (Fin D → ℂ) → (Σ k, ι k) → ℂ} {y : Fin D → ℂ}
    (hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0) :
    cxHessian (fun y' => Real.log ((X.tensor Y).h (γ y'))) y =
      cxHessian (fun y' => Real.log (X.h (γ y'))) y + cxHessian (fun y' => Real.log (Y.h (γ y'))) y := by
  have hev := hγ.eventually_nhds
  have ha : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (X.h (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_log_metric hX (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hc : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 (fun y'' => Real.log (Y.h (γ y''))) y' := by
    filter_upwards [hev] with y' hy'
    exact contDiffAt_log_metric hY (hy'.mono fun _ h => h.1) hy'.self_of_nhds.2
  have hψ : (fun y' => Real.log ((X.tensor Y).h (γ y'))) =ᶠ[𝓝 y]
      fun y' => 1 * Real.log (X.h (γ y')) + 1 * Real.log (Y.h (γ y')) := by
    filter_upwards [hγ] with y' hy'
    rw [one_mul, one_mul]
    exact Real.log_mul (X.pos _ hy'.2).ne' (Y.pos _ hy'.2).ne'
  have hH := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaamix_cxHessian_comb 1 1 ha hc hψ
  simpa only [Complex.ofReal_one, one_smul] using hH

theorem abs_maDensity_le {P : Ideal (MRing ι)} {e : ℕ} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    {L T : Fin e → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) (hT : ∀ j, IsSmoothHerm (T j))
    (hTp : ∀ j, IsSemiPosHerm (T j)) (hLTp : ∀ j, IsSemiPosHerm ((L j).tensor (T j)))
    {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    (hS : IsSheet P Ψ y w γ) :
    |maDensity (fun j y' => pot L j (γ y')) y| ≤
      3 ^ e * maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y := by
  have hγ : ∀ᶠ y' in 𝓝 y, DifferentiableAt ℂ γ y' ∧ ∀ k, ∃ i, γ y' ⟨k, i⟩ ≠ 0 := by
    filter_upwards [hS.2] with y' hy'
    exact ⟨hy'.1, hy'.2.1.1⟩
  have hLT : ∀ j, IsSmoothHerm ((L j).tensor (T j)) := fun j => isSmoothHerm_tensor (hL j) (hT j)
  set A : Fin e → Matrix (Fin e) (Fin e) ℂ := fun j => cxHessian (fun y' => pot L j (γ y')) y with hAdef
  set B : Fin e → Matrix (Fin e) (Fin e) ℂ :=
    fun j => cxHessian (fun y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y with hBdef
  have hHT : ∀ j, (cxHessian (fun y' => Real.log ((T j).h (γ y'))) y).PosSemidef := fun j =>
    SheetHessPSD.proof K ι P e Ψ (T j) y w γ (hT j) (hTp j) hS
  have hHLT : ∀ j, (cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y).PosSemidef := fun j =>
    SheetHessPSD.proof K ι P e Ψ _ y w γ (hLT j) (hLTp j) hS
  have hB : ∀ j, B j = cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y +
      cxHessian (fun y' => Real.log ((T j).h (γ y'))) y := fun j =>
    cxHessian_tensor (hLT j) (hT j) hγ
  have hA : ∀ j, cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y =
      A j + cxHessian (fun y' => Real.log ((T j).h (γ y'))) y := fun j =>
    cxHessian_tensor (hL j) (hT j) hγ
  have hle : ∀ j, (B j - A j).PosSemidef := fun j => by
    have e1 : B j - A j = cxHessian (fun y' => Real.log ((T j).h (γ y'))) y +
        cxHessian (fun y' => Real.log ((T j).h (γ y'))) y := by
      rw [hB j, hA j]; abel
    rw [e1]
    exact (hHT j).add (hHT j)
  have hge : ∀ j, (A j + B j).PosSemidef := fun j => by
    have e1 : A j + B j = cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y +
        cxHessian (fun y' => Real.log (((L j).tensor (T j)).h (γ y'))) y := by
      rw [hB j, hA j]; abel
    rw [e1]
    exact (hHLT j).add (hHLT j)
  have hn : ‖mixedDisc A‖ ≤ 3 ^ e * (mixedDisc B).re :=
    ReciprocityTheory.AnForm.A.norm_mdisc_le_of_abs_le A B hle hge
  have hc : 0 ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e := by positivity
  unfold maDensity
  rw [abs_mul, abs_of_nonneg hc]
  calc (e.factorial : ℝ) * (2 / Real.pi) ^ e * |(mixedDisc A).re|
      ≤ (e.factorial : ℝ) * (2 / Real.pi) ^ e * (3 ^ e * (mixedDisc B).re) :=
        mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hn) hc
    _ = 3 ^ e * ((e.factorial : ℝ) * (2 / Real.pi) ^ e * (mixedDisc B).re) := by ring

end PointsAbsIntegrable


open PointsAbsIntegrable in
theorem PtsAbsIntegrable.proof (hInt : PtsIntegrableStatement) (hMeas : PtsAbsMeasurable.Statement) :
    PtsAbsIntegrable.Statement := by
  intro K _ ι _ P e Ψ L A s hP hΨ hL hA hs
  classical
  have hTw := SemiPosTwist.proof TorusInvLevi.proof
  choose T hTs hTp hLTp using fun j => hTw K ι (L j) (hL j)
  have hN : ∀ j, IsSmoothHerm (((L j).tensor (T j)).tensor (T j)) := fun j =>
    isSmoothHerm_tensor (isSmoothHerm_tensor (hL j) (hTs j)) (hTs j)
  obtain ⟨a, ha, hsa, hsP⟩ := hs
  have hs : IsSectionOn P A s := ⟨a, ha, hsa, hsP⟩
  set D := regLine A s ⟨a, ha, hsa⟩ 1 with hDdef
  have hD : IsSmoothHerm D := isSmoothHerm_regLine hA one_pos
  have hD1 : IsSectionOn P D 1 := by
    refine ⟨0, fun k => by simp [hDdef, regLine_a], fun m hm k => ?_,
      fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)⟩
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have h1 := hInt K ι P e Ψ _ A s hP hΨ hN hA hs
  have h2 := hInt K ι P e Ψ _ D 1 hP hΨ hN hD hD1

  have key : ∀ y w, |sheetDensity P Ψ (pot L) (logNorm A s) y w| ≤
      3 ^ e * (-2 * sheetDensity P Ψ (pot fun j => ((L j).tensor (T j)).tensor (T j)) (logNorm D 1) y w -
        sheetDensity P Ψ (pot fun j => ((L j).tensor (T j)).tensor (T j)) (logNorm A s) y w) := by
    intro y w
    unfold sheetDensity
    by_cases hγ : ∃ γ, IsSheet P Ψ y w γ
    · simp only [dif_pos hγ]
      set γ := hγ.choose
      have hS : IsSheet P Ψ y w γ := hγ.choose_spec
      have hmem : γ y ∈ mcPts P := hS.2.self_of_nhds.2.1
      have hm := abs_maDensity_le hL hTs hTp hLTp hS
      set r := Real.log (D.h (γ y)) with hr
      have hr0 : 0 ≤ r := by
        rw [hr, hDdef, log_regLine_h]
        exact div_nonneg (Real.log_nonneg (by nlinarith [sq_nonneg (secNorm A s (γ y))])) (by norm_num)
      have hgr : logNorm A s (γ y) ≤ r := by
        by_cases h0 : eval (γ y) (map (Int.castRingHom ℂ) s) = 0
        · have : logNorm A s (γ y) = 0 := by simp [logNorm, h0]
          rw [this]
          exact hr0
        · exact logNorm_le_log_regLine_h zero_le_one hmem.1 h0
      have hD1r : logNorm D 1 (γ y) = -r := by
        simp [logNorm, hr, Real.log_inv]
      rw [hD1r]
      have hg : |logNorm A s (γ y)| ≤ 2 * r - logNorm A s (γ y) := by
        rw [abs_le]
        constructor <;> linarith
      rw [abs_mul]
      calc |logNorm A s (γ y)| * |maDensity (fun j y' => pot L j (γ y')) y|
          ≤ (2 * r - logNorm A s (γ y)) *
              (3 ^ e * maDensity (fun j y' => pot (fun j => ((L j).tensor (T j)).tensor (T j)) j (γ y')) y) :=
            mul_le_mul hg hm (abs_nonneg _) (by linarith [abs_nonneg (logNorm A s (γ y))])
        _ = _ := by ring
    · simp only [dif_neg hγ]
      simp
  refine Integrable.mono' (((h2.const_mul (-2)).sub h1).const_mul (3 ^ e))
    (hMeas K ι P e Ψ L A s hP hΨ hL hA hs) (Eventually.of_forall fun y => ?_)
  have hfin := fibreFinite K ι P e Ψ hP hΨ y
  simp only [Pi.sub_apply]
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Real.norm_eq_abs,
    abs_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _), Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun w _ => key y w

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem mixedDisc_eq_zero_of_mulVec {D : ℕ} {A : Fin D → Matrix (Fin D) (Fin D) ℂ} {u : Fin D → ℂ} (hu : u ≠ 0)
    (hA : ∀ k, A k *ᵥ u = 0) : mixedDisc A = 0 := by
  unfold mixedDisc
  rw [Finset.sum_eq_zero, mul_zero]
  intro S _
  have hS : (∑ k ∈ S, A k) *ᵥ u = 0 :=
    Finset.sum_induction _ (fun M => M *ᵥ u = 0) (fun M N hM hN => by rw [add_mulVec, hM, hN, add_zero])
      (zero_mulVec u) fun k _ => hA k
  rw [Matrix.exists_mulVec_eq_zero_iff.mp ⟨u, hu, hS⟩, mul_zero]

theorem pointForm_holds.maDensity_eq_zero (hR : pointFormRank_holds.Statement) (hE : pointFormEuler_holds.Statement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} {d n : ℕ}
    {L : Fin n → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {L' : Fin n → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'} (hv : IsBlockMap κ v)
    (hQ : IsArithVar (imageZ v P') d) (hdn : d < n + 1) (hL : ∀ j, IsSmoothHerm (L j))
    (hLL : ∀ j, IsPullHerm κ v (L j) (L' j))
    {Ψ : (((k : K') → ι' k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)} {y : Fin n → ℂ} {w : ((k : K') → ι' k) → ℂ}
    {γ : (Fin n → ℂ) → (Σ k', ι' k') → ℂ} (hγ : IsSheet P' Ψ y w γ) :
    maDensity (fun j y' => Real.log ((L' j).h (γ y'))) y = 0 := by
  set F : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun y' p => γ y' (v p) with hF
  have hγa : AnalyticAt ℂ γ y := sheet_analyticAt osgood hγ
  have hFa : AnalyticAt ℂ F y := analyticAt_pi_iff.mpr fun p => analyticAt_coord hγa (v p)
  have hFy : ∀ k, ∃ i, F y ⟨k, i⟩ ≠ 0 := blocks_ne_zero_restrict hv hγ.2.self_of_nhds.2.1.1
  have hFQ : ∀ᶠ y' in 𝓝 y, F y' ∈ mcPts (imageZ v P') := by
    filter_upwards [hγ.2] with y' h
    refine ⟨blocks_ne_zero_restrict hv h.2.1.1, fun f hf => ?_⟩
    have h0 := h.2.1.2 _ (Ideal.mem_comap.mp hf)
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_rename, eval_rename] at h0
    exact h0
  obtain ⟨x, hx, c, hxc⟩ := hR K ι (imageZ v P') d n F y hQ (by omega) hFa hFQ
  have hpot : ∀ j, (fun y' => Real.log ((L' j).h (γ y'))) = fun y' => Real.log ((L j).h (F y')) :=
    fun j => funext fun y' => by rw [(hLL j).2]
  simp only [maDensity, hpot]
  rw [mixedDisc_eq_zero_of_mulVec (u := star x) (star_ne_zero.mpr hx)
    fun j => hE K ι (L j) n F y x c (hL j) hFa hFy hxc]
  simp

theorem pointForm_holds.proof (hR : pointFormRank_holds.Statement) (hE : pointFormEuler_holds.Statement) : pointForm_holds.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d n L L' g hv _ hQ hdn hL hLL
  classical
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have h0 : ∀ y w, sheetDensity P' hΨ.choose (fun j z => Real.log ((L' j).h z)) g y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · exact mul_eq_zero_of_right _ (pointForm_holds.maDensity_eq_zero hR hE hv hQ hdn hL hLL hγ.choose_spec)
      · rfl
    simp [h0]
  · rfl

end GroundTheory.Heights₂.Heights.Inter
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

theorem VerticalEmbedding.proof (hD : regularityDehomogenization_holds.Statement) (hC : regularityLocalCardinality_holds.Statement) (hL : RegularityLocalProduct.Statement) :
    VerticalEmbedding.Statement := by
  classical
  intro K _ ι _ P f g a x hP hf hg hfP hgP hx
  have : P.IsPrime := hP.2.1.1

  let t : Ideal (MRing ι) → MRing ι := fun W =>
    if h : IsRelevant W then ∏ k, (X ⟨k, (h k).choose⟩ : MRing ι) ^ a k else 1
  have ht : ∀ W : Ideal (MRing ι), W.IsPrime → IsRelevant W → IsMultiHomog (t W) a ∧ t W ∉ W := by
    intro W hWp hW
    simp only [t, dif_pos hW]
    refine ⟨AvoidRing.isMultiHomog_coordProd _ _, fun hmem => ?_⟩
    obtain ⟨k, -, hk⟩ := hWp.prod_mem_iff.mp hmem
    exact (hW k).choose_spec (hWp.mem_of_pow_mem _ hk)
  have hne : ∀ W : Ideal (MRing ι), P ≤ W → t W ∉ W →
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) ≠ 0 := by
    intro W hPW htW h0
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h0
    exact htW (hPW h0)

  let y : MRing ι → Ideal (MRing ι) → FractionRing (MRing ι ⧸ P) := fun s W =>
    algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) /
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W))
  have hdata : ∀ (s : MRing ι), ∀ W ∈ divSupp P s, P ≤ W ∧ W.IsPrime ∧ IsMultiHomog (t W) a ∧ t W ∉ W ∧
      ∀ s' : MRing ι, y s' W * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s') := by
    intro s W hW
    have hPW : P ≤ W := le_trans le_sup_left hW.1.1.2
    obtain ⟨h1, h2⟩ := ht W hW.1.1.1 hW.2
    exact ⟨hPW, hW.1.1.1, h1, h2, fun s' => div_mul_cancel₀ _ (hne W hPW h2)⟩

  have term : ∀ s : MRing ι, IsMultiHomog s a → s ∉ P → ∀ W ∈ divSupp P s,
      (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
          (if IsHorizontal W then 0 else
            (geoNum 0 W (fun j => ((Fin.elim0 : Fin 0 → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j).a) : ℝ) * Real.log (charOf W)) =
        Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y s W))) := by
    intro s hs hsP W hW
    have hA : IsSectionOn P (_root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun k => (a k : ℤ))) s :=
      ⟨a, fun _ => rfl, hs, hsP⟩
    rw [if_neg (not_isHorizontal_of_dimOne arithVarZero hP hA hW)]
    obtain ⟨-, -, hta, htW, hy⟩ := hdata s W hW
    obtain ⟨hyW, hm⟩ := hD K ι P s (t W) a W (y s W) hP.2.1 hs hsP hW hta htW (hy s)
    have hy0 : y s W ≠ 0 := by
      intro h0
      have h1 := hy s
      rw [h0, zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h1
      exact hsP h1
    rw [hm]
    exact hC K ι P s a W _ (y s W) hP hs hsP hW hyW hy0
  have hvert : ∀ s : MRing ι, IsMultiHomog s a → s ∉ P →
      vertR P (Fin.elim0 : Fin 0 → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) s =
        ∑ᶠ W ∈ divSupp P s, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y s W))) := by
    intro s hs hsP
    unfold vertR
    exact finsum_mem_congr rfl fun W hW => term s hs hsP W hW
  rw [hvert f hf hfP, hvert g hg hgP]
  refine hL K ι P f g a x t (y f) (y g) hP hf hg hfP hgP hx fun W hW => ?_
  obtain ⟨-, -, hta, htW, hy⟩ : P ≤ W ∧ W.IsPrime ∧ IsMultiHomog (t W) a ∧ t W ∉ W ∧ _ := by
    rcases hW with hW | hW
    · exact hdata f W hW
    · exact hdata g W hW
  exact ⟨hta, htW, hy f, hy g⟩

end

end GroundTheory.Heights₂.Heights.Inter
end
