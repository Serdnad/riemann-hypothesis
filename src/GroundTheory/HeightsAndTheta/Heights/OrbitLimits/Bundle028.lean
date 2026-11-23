module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle030
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle007
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle005
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle025
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle089
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle077
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PtsPosDensMeasurable
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle023
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreSheetFormCompare
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
import Std.Tactic.BVDecide.Normalize.Prop
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing multAt divSuppArith)
open GroundTheory.Heights₂.Heights (localMult localMult_map_of_flat map_eq_maximalIdeal_of_isRadical)

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem localMult_map_intCast_complex {τ : Type} [Fintype τ] (J W : Ideal (MvPolynomial τ ℤ)) [W.IsPrime]
    (W'' : Ideal (MvPolynomial τ ℂ)) (hW'' : W'' ∈ (W.map (MvPolynomial.map (Int.castRingHom ℂ))).minimalPrimes) :
    localMult (J.map (MvPolynomial.map (Int.castRingHom ℂ))) W'' = localMult J W := by
  have := HilbertSamuel.mvPolynomial_int_complex_flat τ
  have hAlg := HilbertSamuel.algebraMap_mvPolynomial_int_complex τ
  have : W''.IsPrime := hW''.1.1
  have hc : W''.comap (MvPolynomial.map (Int.castRingHom ℂ)) = W :=
    HilbertSamuel.ComplexMinimalPrimesContract.proof τ W ‹_› W'' hW''
  have : W''.LiesOver W := ⟨by rw [Ideal.under, hAlg, hc]⟩
  have hrad := HilbertSamuel.PrimeComplexRadical.proof τ W ‹_›
  have key := localMult_map_of_flat J W W''
    (by rw [hAlg]; exact map_eq_maximalIdeal_of_isRadical hrad hW'')
  rwa [hAlg] at key

theorem multAt_eq_localMult {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (J W : Ideal (MRing ι))
    [W.IsPrime] : multAt J W = localMult J W := by
  unfold multAt localMult
  rw [dite_eq_left ‹_›, dite_eq_left ‹_›, ObjectsChow.VerticalPartMultiplicity.length_localizedModule_quotient]

theorem ChartSectionLength.proof (hComp : ChartConeComponent.Statement) (hLen : ChartConeLength.Statement) :
    ChartSectionLength.Statement := by
  intro K _ _ ι _ P n m σ i A s hP hs W hW hWh W' hW'
  have hWa := (divSuppArith K ι P (n + 1) A s W hP hs hW).1 hWh
  have : W.IsPrime := hW.1.1.1
  obtain ⟨W'', hW'', hle⟩ := hComp K ι W m σ i hWa.2.1 W' hW'
  rw [hLen K ι P n m σ i A s hP hs W hW hWh W' hW' W'' hW'' hle, multAt_eq_localMult,
    localMult_map_intCast_complex _ W W'' hW'']

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsSectionOn ptsIntegral pot segre divSupp IsHorizontal
  multAt divSupp_finite divSuppArith)
open GroundTheory.Heights₂.Heights (varInt localMult IsDegZeroSmooth segreChartSet segreChartComponents chartLift
  SegreChartIntegral.Statement)

theorem segreChartSet_mono {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)}
    (h : P ≤ W) {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k) :
    segreChartSet W σ i ⊆ segreChartSet P σ i := by
  rintro _ ⟨z, ⟨hz1, hz2⟩, hzi, rfl⟩
  exact ⟨z, ⟨hz1, fun f hf => hz2 f (h hf)⟩, hzi, rfl⟩

theorem ptsIntegral_eq_sum_chart (hInt : SegreChartIntegral.Statement) (hPts : SegreChartIntegralPoints.Statement)
    {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)} {n m : ℕ}
    {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k} {L : Fin n → _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {g : ((Σ k, ι k) → ℂ) → ℝ} {δ : ℝ}
    {G : (Fin m → ℂ) → ℝ} {Φ : Fin n → (Fin m → ℂ) → ℝ} (hW : IsArithVar W (n + 1)) (hPW : P ≤ W)
    (hL : ∀ j, IsSmoothHerm (L j)) (hg : IsDegZeroSmooth g) (hδ : 0 < δ)
    (hsupp : ∀ z, ‖segre z i‖ < δ * ‖segre z‖ → g z = 0)
    (hgerm : ∀ x ∈ segreChartSet P σ i,
      G =ᶠ[𝓝 x] g ∘ chartLift σ i ∧ ∀ j, Φ j =ᶠ[𝓝 x] pot L j ∘ chartLift σ i) :
    ptsIntegral W (pot L) g = ∑ W' ∈ segreChartComponents W σ i, varInt W' n G Φ := by
  have hsub := segreChartSet_mono hPW σ i
  cases n with
  | zero => exact hPts K ι W m σ i L g δ G Φ hW hg hδ hsupp fun x hx => (hgerm x (hsub hx)).1
  | succ e => exact hInt K ι W e m σ i L g δ G Φ hW hL hg hδ (Or.inl hsupp) fun x hx => hgerm x (hsub hx)

theorem ChartDivisorCompare.proof (hInt : SegreChartIntegral.Statement) (hPts : SegreChartIntegralPoints.Statement)
    (hComp : ChartDivisorComponents.Statement) (hLen : ChartDivisorLength.Statement) :
    ChartDivisorCompare.Statement := by
  classical
  intro K _ _ ι _ P n m σ i L A s g δ G Φ hP hL hs hg hδ hsupp hgerm
  obtain ⟨hmin, hdisj⟩ := hComp K ι P n m σ i A s hP hs
  have hfin : {W | W ∈ divSupp P s ∧ IsHorizontal W}.Finite := (divSupp_finite P s).subset fun _ h => h.1
  set S := hfin.toFinset with hS
  set T := S.biUnion fun W => segreChartComponents W σ i with hT
  have hA : ∀ J ∈ segreChartComponents P σ i,
      ∑ᶠ (W' : Ideal (MvPolynomial (Fin m) ℂ)) (_ : W' ∈ (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {chartSection σ i s}) W' : ℝ) * varInt W' n G Φ =
        ∑ W' ∈ T, if J ≤ W' then
          (localMult (J ⊔ Ideal.span {chartSection σ i s}) W' : ℝ) * varInt W' n G Φ else 0 := by
    intro J hJ
    have hset : (J ⊔ Ideal.span {chartSection σ i s}).minimalPrimes = ↑(T.filter fun W' => J ≤ W') := by
      ext W'
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, hmin J hJ W', hT, hS, Finset.mem_biUnion,
        Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      tauto
    rw [hset, finsum_mem_coe_finset, Finset.sum_filter]
  have hB : ∀ W ∈ S, ∀ W' ∈ segreChartComponents W σ i,
      ∑ J ∈ segreChartComponents P σ i, (if J ≤ W' then
          (localMult (J ⊔ Ideal.span {chartSection σ i s}) W' : ℝ) * varInt W' n G Φ else 0) =
        (multAt (P ⊔ Ideal.span {s}) W : ℝ) * varInt W' n G Φ := by
    intro W hW W' hW'
    rw [Set.Finite.mem_toFinset] at hW
    rw [← Finset.sum_filter, ← Finset.sum_mul, ← Nat.cast_sum, hLen K ι P n m σ i A s hP hs W hW.1 hW.2 W' hW']
  have hdisjT : (↑S : Set (Ideal (MRing ι))).PairwiseDisjoint fun W => segreChartComponents W σ i := by
    intro W₁ h₁ W₂ h₂ hne
    rw [Finset.mem_coe, Set.Finite.mem_toFinset] at h₁ h₂
    exact Finset.disjoint_left.2 fun W' hW₁ hW₂ => hne (hdisj W₁ W₂ h₁ h₂ W' hW₁ hW₂)
  rw [Finset.sum_congr rfl hA, Finset.sum_comm, Finset.sum_biUnion hdisjT,
    Finset.sum_congr rfl fun W hW => Finset.sum_congr rfl (hB W hW), eq_comm]
  refine (finsum_mem_eq_finite_toFinset_sum
    (fun W => (multAt (P ⊔ Ideal.span {s}) W : ℝ) * ptsIntegral W (pot L) g) hfin).trans ?_
  refine Finset.sum_congr rfl fun W hW => ?_
  rw [← Finset.mul_sum]
  rw [Set.Finite.mem_toFinset] at hW
  have hWv : IsArithVar W (n + 1) := (divSuppArith K ι P (n + 1) A s W hP hs hW.1).1 hW.2
  rw [ptsIntegral_eq_sum_chart hInt hPts hWv (le_sup_left.trans hW.1.1.1.2) hL hg hδ hsupp hgerm]

end GroundTheory.Heights₂.Heights.Targets
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj IsSheet ptsIntegralAt sheetDensity
  fibre pot mcPts fibreFinite isOpen_blockNonzero)

section

variable {K : Type*} [Fintype K] {ι : K → Type*} {e : ℕ} {P : Ideal (MRing ι)}
  {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ}

theorem sheetDensity_neg (g : ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ) (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ (fun z => -g z) y w = -sheetDensity P Ψ φ g y w := by
  unfold sheetDensity
  split_ifs <;> simp [neg_mul]

theorem sheetDensity_congr {g g' : ((Σ k, ι k) → ℂ) → ℝ} (h : ∀ z ∈ mcPts P, g z = g' z) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) : sheetDensity P Ψ φ g y w = sheetDensity P Ψ φ g' y w := by
  unfold sheetDensity
  split_ifs with hγ
  · have hs : IsSheet P Ψ y w hγ.choose := hγ.choose_spec
    rw [h _ hs.2.self_of_nhds.2.1]
  · rfl

end

theorem PtsIntegralProjIndep.proof (hInt : PtsPosDensIntegrable.Statement)
    (hPos : PtsPosPartProjIndep.Statement) : PtsIntegralProjIndep.Statement := by
  intro K _ ι _ P e Ψ Ψ' L g hP hΨ hΨ' hL hg
  classical
  set S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hSdef
  set g₀ : ((Σ k, ι k) → ℂ) → ℝ := S.piecewise g 0 with hg₀def
  have hg₀m : Measurable g₀ :=
    hg.1.continuousOn.measurable_piecewise continuousOn_const isOpen_blockNonzero.measurableSet
  have hg₀inv : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) →
      g₀ (fun p => c p.1 * z p) = g₀ z := by
    intro c z hc
    have hmem : (fun p : Σ k, ι k => c p.1 * z p) ∈ S ↔ z ∈ S := by
      simp only [hSdef, Set.mem_ofPred_eq, ne_eq, mul_eq_zero, hc, false_or]
    by_cases hz : z ∈ S
    · rw [hg₀def, Set.piecewise_eq_of_mem _ _ _ hz, Set.piecewise_eq_of_mem _ _ _ (hmem.2 hz), hg.2 c z hc]
    · rw [hg₀def, Set.piecewise_eq_of_notMem _ _ _ hz, Set.piecewise_eq_of_notMem _ _ _ (mt hmem.1 hz)]
      rfl
  have hag : ∀ z ∈ mcPts P, g z = g₀ z := fun z hz =>
    (Set.piecewise_eq_of_mem S _ _ (show z ∈ S from hz.1)).symm
  have hagn : ∀ z ∈ mcPts P, -g z = -g₀ z := fun z hz => by rw [hag z hz]
  have hneg : IsDegZeroSmooth (fun z => -g z) :=
    ⟨hg.1.neg, fun c z hc => by simp only [hg.2 c z hc]⟩
  have hnn : ∀ (Ψ₀ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (u : ((Σ k, ι k) → ℂ) → ℝ) y,
      0 ≤ ptsPosDens P Ψ₀ (pot L) u y := fun Ψ₀ u y =>
    finsum_nonneg fun w => finsum_nonneg fun _ => le_max_right _ _

  have key : ∀ Ψ₀ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ₀ →
      ptsIntegralAt P Ψ₀ (pot L) g =
        (∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ₀ (pot L) g₀ y)).toReal -
          (∫⁻ y, ENNReal.ofReal (ptsPosDens P Ψ₀ (pot L) (fun z => -g₀ z) y)).toReal := by
    intro Ψ₀ h₀
    have hp := hInt K ι P e Ψ₀ L g hP h₀ hL hg
    have hn := hInt K ι P e Ψ₀ L (fun z => -g z) hP h₀ hL hneg
    have e₁ : ptsPosDens P Ψ₀ (pot L) g₀ = ptsPosDens P Ψ₀ (pot L) g := by
      funext y
      simp only [ptsPosDens, sheetDensity_congr (Ψ := Ψ₀) (φ := pot L) hag]
    have e₂ : ptsPosDens P Ψ₀ (pot L) (fun z => -g₀ z) = ptsPosDens P Ψ₀ (pot L) (fun z => -g z) := by
      funext y
      simp only [ptsPosDens, sheetDensity_congr (Ψ := Ψ₀) (φ := pot L) hagn]
    have hsplit : ∀ y, (∑ᶠ w ∈ _root_.ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ₀ y, sheetDensity P Ψ₀ (pot L) g y w) =
        ptsPosDens P Ψ₀ (pot L) g y - ptsPosDens P Ψ₀ (pot L) (fun z => -g z) y := by
      intro y
      have hF := fibreFinite K ι P e Ψ₀ hP h₀ y
      simp only [ptsPosDens, finsum_mem_eq_finite_toFinset_sum _ hF, sheetDensity_neg,
        ← Finset.sum_sub_distrib, max_zero_sub_max_neg_zero_eq_self]
    unfold ptsIntegralAt
    simp only [hsplit]
    rw [integral_sub hp hn, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnn Ψ₀ g)) hp.1,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hnn Ψ₀ _)) hn.1, e₁, e₂]
  rw [key Ψ hΨ, key Ψ' hΨ', hPos K ι P e Ψ Ψ' L g₀ hP hΨ hΨ' hL hg₀m hg₀inv,
    hPos K ι P e Ψ Ψ' L (fun z => -g₀ z) hP hΨ hΨ' hL hg₀m.neg fun c z hc => by simp only [hg₀inv c z hc]]

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm)
open ComplexSets Matrix

theorem SegreChartAbsIntegrable.proof (h₁ : SliceMassFinite.Statement)
    (h₂ : SegreChartSheetCompare.Statement) : SegreChartAbsIntegrable.Statement := by
  intro K _ _ ι _ P e m σ i L g _ hL hg J hJ A hA
  obtain ⟨M, hM⟩ := PtsPosDens.exists_bound hg
  obtain ⟨C, hC⟩ := h₂ K ι P e m σ i L hL
  have hJmin := mem_segreChartComponents.1 hJ
  have hℓ : linForm (Pi.single (σ.symm i) (1 : ℂ)) - 1 ∈ J := by
    rw [linForm_single]
    refine hJmin.1.2 ?_
    rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, -, hzi, rfl⟩
    simp [hzi]
  have hInt := h₁ m e (HermNorm.std m) J (Pi.single (σ.symm i) 1) A hJmin.1.1 hℓ
    (VarIntAdd.ringKrullDim_of_isFiniteProjection hA) hA
  set c : ℝ := max M 0 * max C 0 with hc
  have hmeas : Measurable (chartAbsDens J A (chartWeight σ i g) (chartPot σ i L)) :=
    SheetSumMeasurable.measurable_sheetSum hA (fun a b => |a * b|)
      ((continuous_mul.comp continuous_id).abs.measurable) (measurable_chartWeight σ i hg) _
  refine (hInt.const_mul c).mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (chartAbsDens_nonneg _ _ _ _ _)]
  refine sheetSum_le_mul (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y) c _ _ fun x hx s hs => ?_
  obtain ⟨hxJ, rfl⟩ := hx
  have hx1 : x (σ.symm i) = 1 := chart_coord_eq_one hJ hxJ
  have hG : |chartWeight σ i g x| ≤ max M 0 := by
    rw [chartWeight_of_coord g hx1]
    exact (hM _ (chartLift_blockNonzero σ i hx1)).trans (le_max_left _ _)
  have hD := hC J hJ A x s hxJ hs
  rw [abs_mul, one_mul, hc, mul_assoc]
  exact mul_le_mul hG (hD.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)))
    (abs_nonneg _) (le_max_right _ _)

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace CurveVerticalPointLength

theorem maximal_and_mult_eq (hCh : CurveVertPointChart.Statement) (hMC : CurveVertPointMultChart.Statement)
    (hSQ : CurveSectionQuotLocal.Statement) {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {s : MRing ι} {d : K → ℕ}
    (hP : IsArithVar (mCoordIdeal y) 1) (hs : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s d) (hsP : s ∉ mCoordIdeal y)
    {W : Ideal (MRing ι)} (hW : W ∈ divSupp (mCoordIdeal y) s) :
    (curvePtIdeal y W).IsMaximal ∧
      multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
        locLen (curvePtIdeal y W) (curveSectionQuot y (fun k => (d k : ℤ)) (aeval y s)) := by
  choose c hc using hW.2
  obtain ⟨hmax, hrat, hmem⟩ := hCh K ι Ω y s d hP hs hsP W hW c hc
  have hPW : mCoordIdeal y ≤ W := le_trans le_sup_left hW.1.1.2
  have hsW : s ∈ W := hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => ne_zero_of_X_notMem fun h => hc k (hPW h)
  obtain ⟨a, b, -, hb, hab⟩ := (hmem d s hs).mp hsW
  refine ⟨hmax, ?_⟩
  rw [hMC K ι Ω y s d hP hs hsP W hW c hc a b hb hab,
    hSQ K ι Ω y s d hP hs hsP _ c hmax.isPrime hyc hrat a b hb hab]

end CurveVerticalPointLength

theorem CurveVertPointLength.proof (hCh : CurveVertPointChart.Statement) (hInj : CurveVertPointInj.Statement)
    (hSurj : CurveVertPointSurj.Statement) (hMC : CurveVertPointMultChart.Statement)
    (hSQ : CurveSectionQuotLocal.Statement) : CurveVertPointLength.Statement := by
  intro K _ ι _ Ω _ y s d hP hs hsP
  refine ⟨⟨fun W hW => ?_, hInj K ι Ω y s d hP hs hsP,
      fun m hm => hSurj K ι Ω y s d hP hs hsP m hm.1 hm.2⟩,
    fun W hW => (CurveVerticalPointLength.maximal_and_mult_eq hCh hMC hSQ hP hs hsP hW).2⟩
  obtain ⟨hmax, hmult⟩ := CurveVerticalPointLength.maximal_and_mult_eq hCh hMC hSQ hP hs hsP hW
  exact ⟨hmax, hmult ▸ (IndefiniteRowSideFullHecke.Inter.multAt_pos_of_mem_divSupp hW).ne'⟩

end

end GroundTheory.Heights₂.Heights.Targets
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm pot segre)
open ComplexSets Matrix Filter Topology

namespace SegreChartSheetComparison

theorem hessC_congr_germ {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : f =ᶠ[𝓝 y] g) :
    ReciprocityTheory.AnForm.hessC f y = ReciprocityTheory.AnForm.hessC g y := by
  unfold ReciprocityTheory.AnForm.hessC
  rw [(h.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem eq_segre_chartLift {P : Ideal (MRing ι)} {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {i : (k : K) → ι k} {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ segreChartComponents P σ i)
    {x : Fin m → ℂ} (hx : x ∈ zeroSet J) : x = fun a => segre (chartLift σ i x) (σ a) := by
  have hle : segreChartIdeal P σ i ≤ J := (mem_segreChartComponents.1 hJ).1.2
  funext a
  set q : MvPolynomial (Fin m) ℂ := MvPolynomial.X a -
    ∏ k, MvPolynomial.X (σ.symm (Function.update i k (σ a k))) with hq
  have heval : ∀ w : Fin m → ℂ, MvPolynomial.eval w q = w a - segre (chartLift σ i w) (σ a) := fun w => by
    simp [hq, segre, chartLift, map_prod]
  have hmem : q ∈ segreChartIdeal P σ i := by
    rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, -, hzi, rfl⟩
    show MvPolynomial.eval _ q = 0
    rw [heval, segre_chartLift σ i z hzi, sub_self]
  have h := hx q (hle hmem)
  rw [heval] at h
  exact sub_eq_zero.1 h

end SegreChartSheetComparison


open SegreChartSheetComparison in
theorem SegreChartSheetCompare.of_segreSheetFormCompare (hF : SegreSheetFormCompare.Statement) :
    SegreChartSheetCompare.Statement := by
  intro K _ _ ι _ P e m σ i L hL
  obtain ⟨C, hC⟩ := hF K ι e L hL
  refine ⟨|C|, fun J hJ A x s hx hs => ?_⟩
  obtain ⟨U, hU, hyU, hsd, hsx, hsU, -⟩ := hs
  set z : (Fin e → ℂ) → (Σ k, ι k) → ℂ := chartLift σ i ∘ s with hzdef
  have hz : DifferentiableOn ℂ z U :=
    differentiableOn_pi.2 fun p => (differentiableOn_pi.1 hsd) (σ.symm (Function.update i p.1 p.2))
  have hblk : ∀ k, ∃ j, z (A *ᵥ x) ⟨k, j⟩ ≠ 0 := by
    have h1 : s (A *ᵥ x) (σ.symm i) = 1 := by rw [hsx]; exact chart_coord_eq_one hJ hx
    exact chartLift_blockNonzero σ i h1
  have h1 := hC z U (A *ᵥ x) hU hyU hz hblk
  have hfs : (fun w => Real.log ((HermNorm.std m).dualNorm w)) ∘ s =ᶠ[𝓝 (A *ᵥ x)]
      (fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z := by
    filter_upwards [hU.mem_nhds hyU] with y' hy'
    have he := eq_segre_chartLift hJ (hsU y' hy').2
    simp only [Function.comp_apply, hzdef]
    congr 1
    have hd : (HermNorm.std m).dualNorm (s y') = √(∑ a, ‖s y' a‖ ^ 2) := by
      simp [HermNorm.dualNorm, HermNorm.std]
    rw [hd]
    congr 1
    conv_lhs => rw [he]
    exact Equiv.sum_comp σ (fun i' => ‖segre (chartLift σ i (s y')) i'‖ ^ 2)
  have hden : ReciprocityTheory.AnForm.maDens
      (fun _ => (fun w => Real.log ((HermNorm.std m).dualNorm w)) ∘ s) (A *ᵥ x) =
      ReciprocityTheory.AnForm.maDens (fun _ => (fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z)
        (A *ᵥ x) := by
    unfold ReciprocityTheory.AnForm.maDens
    dsimp only
    rw [hessC_congr_germ hfs]
  have hpot : (fun k => chartPot σ i L k ∘ s) = fun j => pot L j ∘ z := rfl
  rw [hpot, hden]
  calc _ ≤ _ := h1
    _ ≤ |C * ReciprocityTheory.AnForm.maDens
          (fun _ => (fun w => Real.log (Real.sqrt (∑ i', ‖segre w i'‖ ^ 2))) ∘ z) (A *ᵥ x)| := le_abs_self _
    _ = _ := abs_mul _ _

theorem SegreChartSheetCompare.proof : SegreChartSheetCompare.Statement :=
  SegreChartSheetCompare.of_segreSheetFormCompare SegreSheetFormCompare.proof

end GroundTheory.Heights₂.Heights
end
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.Inter

def CurveBoxSmall.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (c : ∀ k, ι k),
    IsArithVar (mCoordIdeal y) 1 → Birational y → (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∀ (τ : ℕ) (s : Ω), IsSmallH (mCoordIdeal y) y A τ s ↔
      ∀ σ : Ω →+* ℂ, ‖σ (s / chartUnit y c A.a τ)‖ ≤ chartRadius A c (fun p => σ (y p)) ^ τ

namespace CurveBoxSmall

end CurveBoxSmall

end GroundTheory.Heights₂.Heights.Targets
end
