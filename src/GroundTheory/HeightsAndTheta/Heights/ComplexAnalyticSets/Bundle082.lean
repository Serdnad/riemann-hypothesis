module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle062
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle051
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle050
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle065
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle063
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle061
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle071
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle064
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem CurveRegularOffCentre.proof (hG : CurveGermComponents.Statement) (hR : CurveRegularOffFinite.Statement)
    (hF : CurveProperClosedFinite.Statement) : CurveRegularOffCentre.Statement := by
  classical
  intro n I q hdim
  obtain ⟨N, hN, hcomp⟩ := hG n I q hdim
  have hZc : ∀ J : Ideal (MvPolynomial (Fin n) ℂ), IsClosed (zeroSet J) := fun J ↦ by
    have : zeroSet J = ⋂ p ∈ J, {x : Fin n → ℂ | eval x p = 0} := by ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun p _ ↦ isClosed_eq (MvPolynomial.continuous_eval p) continuous_const
  have hM : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing _ I
  set S := {W | W ∈ I.minimalPrimes ∧ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = 1}
  have hS : S.Finite := hM.subset fun W hW ↦ hW.1
  choose! F hFfin hFchart using fun W (hW : W ∈ S) ↦ hR n W hW.1.1.1 hW.2
  have hnle : ∀ W ∈ S, ∀ W' ∈ I.minimalPrimes \ {W}, ¬ W' ≤ W := fun W hW W' hW' hle ↦
    hW'.2 (le_antisymm hle (hW.1.2 hW'.1.1 hle))
  set Bad := (⋃ W ∈ S, F W) ∪ ⋃ W ∈ S, ⋃ W' ∈ I.minimalPrimes \ {W}, zeroSet W ∩ zeroSet W'
  have hBad : Bad.Finite := (hS.biUnion hFfin).union (hS.biUnion fun W hW ↦
    hM.sdiff.biUnion fun W' hW' ↦ hF n W W' hW.1.1.1 hW.2 (hnle W hW W' hW'))
  have hN'o : IsOpen (interior N \ (Bad \ {q})) := isOpen_interior.sdiff hBad.sdiff.isClosed
  refine ⟨_, hN'o.mem_nhds ⟨mem_interior_iff_mem_nhds.2 hN, fun h ↦ h.2 rfl⟩, ?_⟩
  rintro x ⟨hxI, hxN, hxB⟩ hxq
  have hxBad : x ∉ Bad := fun h ↦ hxB ⟨h, hxq⟩
  obtain ⟨W, hWm, hWd, -, hxW⟩ := hcomp x ⟨hxI, interior_subset hxN⟩
  have hWS : W ∈ S := ⟨hWm, hWd⟩
  obtain ⟨A, O, V, g, hO, hV, hxV, hg, hAg, hWV⟩ :=
    hFchart W hWS x hxW fun h ↦ hxBad (Or.inl (Set.mem_biUnion hWS h))
  set V' := V ∩ interior N ∩ ⋂ W' ∈ I.minimalPrimes \ {W}, (zeroSet W')ᶜ
  have hV' : IsOpen V' := (hV.inter isOpen_interior).inter
    (hM.sdiff.isOpen_biInter fun W' _ ↦ (hZc W').isOpen_compl)
  have hIV' : zeroSet I ∩ V' = zeroSet W ∩ V' := by
    ext z
    refine ⟨fun ⟨hzI, hzV⟩ ↦ ⟨?_, hzV⟩, fun ⟨hzW, hzV⟩ ↦ ⟨fun p hp ↦ hzW p (hWm.1.2 hp), hzV⟩⟩
    obtain ⟨W'', hW''m, -, -, hzW''⟩ := hcomp z ⟨hzI, interior_subset hzV.1.2⟩
    by_cases h : W'' = W
    · exact h ▸ hzW''
    · exact absurd hzW'' (Set.mem_iInter₂.1 hzV.2 W'' ⟨hW''m, h⟩)
  refine ⟨A, O ∩ g ⁻¹' V', V', g, hg.continuousOn.isOpen_inter_preimage hO hV', hV',
    ⟨⟨hxV, hxN⟩, Set.mem_iInter₂.2 fun W' hW' hxW' ↦ hxBad (Or.inr (Set.mem_biUnion hWS
      (Set.mem_biUnion hW' ⟨hxW, hxW'⟩)))⟩, hg.mono Set.inter_subset_left,
    fun y hy ↦ hAg y hy.1, ?_⟩
  rw [hIV', Set.image_inter_preimage, ← hWV]
  ext z
  exact ⟨fun ⟨hzW, hzV⟩ ↦ ⟨⟨hzW, hzV.1.1⟩, hzV⟩, fun ⟨⟨hzW, _⟩, hzV⟩ ↦ ⟨hzW, hzV⟩⟩

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem LelongLimitAtBranches.proof (hDec : BranchIntDecompose.Statement) (hSl : SliceBranchInt.Statement)
    (hLim : PolydiscLelongLimit.Statement) (hPr : IndefiniteRowSideFullHecke.ComplexSets.BranchProperAtPoint.Statement) :
    LelongLimitAtBranches.Statement := by
  intro n d J W u q m γ ord π φ hJ hdim hu hW hq hφ hzW hcov hsl hdisj hord _
  obtain ⟨NA, hNA, hA⟩ := hDec n d J u q m γ ord hJ hdim hu hcov hdisj hord
  obtain ⟨NB, hNB, hB⟩ := hSl n d J W u q m γ ord hJ hdim hu hW hq hzW hcov hsl hdisj hord
  have hpr : ∀ b, ∃ e > 0, ∀ τ ∈ Metric.ball 0 (γ b).radius, (γ b).toFun τ ∈ Metric.ball q e →
      τ ∈ Metric.ball 0 ((γ b).radius / 2) := fun b =>
    hPr n (d + 1) J u q q m γ hJ hdim hu hcov hdisj b 0 (Metric.mem_ball_self (γ b).radius_pos)
      (γ b).map_zero _ (Metric.ball_mem_nhds _ (half_pos (γ b).radius_pos))
  choose e he hpe using hpr
  refine ⟨NA ∩ NB ∩ ⋂ b, Metric.ball q (e b), inter_mem (inter_mem hNA hNB)
    (iInter_mem.2 fun b => Metric.ball_mem_nhds q (he b)), fun f hf hfc hfN => ?_⟩
  have hcons : ∀ (g : (Fin n → ℂ) → ℝ) (b : Fin m), (fun k => vecCons g φ k ∘ (γ b).toFun) =
      vecCons (g ∘ (γ b).toFun) fun k => φ k ∘ (γ b).toFun := fun g b => by
    funext k; refine Fin.cases ?_ (fun j => ?_) k <;> simp
  have hsum : (fun ε => ∑ b, ReciprocityTheory.AnForm.maInt
      (vecCons (fun τ => Real.log (‖linEval u ((γ b).toFun τ)‖ ^ 2 + ε) / 2) fun k => φ k ∘ (γ b).toFun)
      (f ∘ (γ b).toFun) (Metric.ball 0 (γ b).radius)) =ᶠ[𝓝[>] 0]
      fun ε => varInt J (d + 1) f (vecCons (logReg u ε) φ) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [hA f _ hf hfc (hfN.trans (Set.inter_subset_left.trans Set.inter_subset_left))
      (fun i => Fin.cases ⟨Set.univ, isOpen_univ, Set.subset_univ _, (contDiff_logReg u hε).contDiffOn⟩
        (fun j => hφ j) i)]
    exact Finset.sum_congr rfl fun b _ => by rw [hcons]; rfl
  refine Tendsto.congr' hsum ?_
  have hlim : ∀ b, Tendsto (fun ε => ReciprocityTheory.AnForm.maInt
      (vecCons (fun τ => Real.log (‖linEval u ((γ b).toFun τ)‖ ^ 2 + ε) / 2) fun k => φ k ∘ (γ b).toFun)
      (f ∘ (γ b).toFun) (Metric.ball 0 (γ b).radius)) (𝓝[>] 0) (𝓝 ((ord b : ℝ) * varInt W d f φ)) := by
    intro b
    have han : AnalyticOnNhd ℂ (γ b).toFun (Metric.ball 0 (γ b).radius) := fun w hw =>
      AnalyticAt.pi fun i => ReciprocityTheory.AnForm.Osgood.osgood (d + 1) _ (fun z => (γ b).toFun z i)
        Metric.isOpen_ball (differentiableOn_pi.1 (γ b).differentiableOn i) w hw
    have hγ : ContDiffOn ℝ ∞ (γ b).toFun (Metric.ball 0 (γ b).radius) :=
      (han.contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ
    rw [hB b f φ hf hfc (hfN.trans (Set.inter_subset_left.trans Set.inter_subset_right)) hφ]
    refine hLim d (ord b) (γ b).radius ((γ b).radius / 2) _ (f ∘ (γ b).toFun) _
      (half_lt_self (γ b).radius_pos) (hord b) (hf.comp_contDiffOn hγ) (fun τ hτ hne => hpe b τ hτ ?_)
      (fun k => ?_)
    · exact Set.mem_iInter.1 (Set.inter_subset_right (hfN (subset_tsupport f hne))) b
    · obtain ⟨U, hU, hsub, hφU⟩ := hφ k
      exact hφU.comp hγ fun τ hτ => hsub ((γ b).mapsTo hτ)
  have := tendsto_finsetSum Finset.univ fun b _ => hlim b
  convert this using 2
  push_cast
  rw [Finset.sum_mul]

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets Function
open scoped ContDiff

theorem varInt_eq_zero_of_vanish {n k : ℕ} (W : Ideal (MvPolynomial (Fin n) ℂ))
    (f : (Fin n → ℂ) → ℝ) (φ : Fin k → (Fin n → ℂ) → ℝ) (hf : ∀ x ∈ zeroSet W, f x = 0) :
    varInt W k f φ = 0 := by
  classical
  unfold varInt
  split_ifs with h
  · have h0 : chartDens W h.choose f φ = fun _ => 0 := by
      funext y
      unfold chartDens sheetSum
      refine finsum_eq_zero_of_forall_eq_zero fun x => ?_
      rw [finsum_eq_dif]
      by_cases hx : x ∈ fibre W h.choose y
      · rw [dite_eq_left hx]
        split_ifs
        · show f x * _ = 0
          rw [hf x hx.1, zero_mul]
        · rfl
      · rw [dite_eq_right hx]
    simp [chartInt, h0]
  · rfl

theorem LelongLimit.proof (hOff : LelongLimitOffZero.Statement) (hOn : LelongLimitOnZero.Statement)
    (hAdd : VarIntAdd.Statement) : LelongLimit.Statement := by
  classical
  intro n d J u f φ hJ hdim hu hf hfc hφ
  set S := (J ⊔ Ideal.span {linForm u}).minimalPrimes with hS
  have hW : ∀ W ∈ S, W.IsPrime ∧ zeroSet W ⊆ zeroSet J ∧ ∀ x ∈ zeroSet W, linEval u x = 0 := by
    intro W hWm
    have hle : J ⊔ Ideal.span {linForm u} ≤ W := hWm.1.2
    refine ⟨hWm.1.1,
      fun x hx q hq => hx q (hle (Ideal.mem_sup_left hq)), fun x hx => ?_⟩
    have := hx _ (hle (Ideal.mem_sup_right (Ideal.subset_span rfl)))
    simpa [linForm, linEval] using this
  have hφW : ∀ W ∈ S, ∀ i, SmoothNear (zeroSet W) (φ i) := fun W hWm i => by
    obtain ⟨U, hU, hSU, hC⟩ := hφ i
    exact ⟨U, hU, (hW W hWm).2.1.trans hSU, hC⟩
  have hclosed : IsClosed (zeroSet J ∩ {x | linEval u x = 0}) := by
    refine IsClosed.inter ?_ (isClosed_eq ?_ continuous_const)
    · have : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | MvPolynomial.eval x q = 0} := by
        ext x; simp [zeroSet]
      rw [this]
      exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
    · exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)
  refine tendsto_of_forall_local (fun ε g => varInt J (d + 1) g (vecCons (logReg u ε) φ))
    (fun g => ∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ S),
      (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ) ?_ ?_ ?_ f hf hfc
  · intro g₁ g₂ h1 h1c h2 h2c
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    refine hAdd n (d + 1) J g₁ g₂ _ hJ h1.continuous h1c h2.continuous h2c fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε)
    · simpa using hφ j
  · intro g₁ g₂ h1 h1c h2 h2c
    rw [← finsum_mem_add_distrib (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _)]
    refine finsum_mem_congr rfl fun W hWm => ?_
    rw [hAdd n d W g₁ g₂ φ (hW W hWm).1 h1.continuous h1c h2.continuous h2c (hφW W hWm), mul_add]
  · intro p
    by_cases hp : p ∈ zeroSet J ∩ {x | linEval u x = 0}
    · exact hOn n d J u φ p hJ hdim hu hφ hp.1 hp.2
    · refine ⟨_, hclosed.isOpen_compl.mem_nhds hp, fun g hg hgc hgN => ?_⟩
      have h0 : (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ S),
          (localMult (J ⊔ Ideal.span {linForm u}) W : ℝ) * varInt W d g φ) = 0 := by
        refine finsum_eq_zero_of_forall_eq_zero fun W => ?_
        rw [finsum_eq_dif]
        by_cases hWm : W ∈ S
        · rw [dite_eq_left hWm, varInt_eq_zero_of_vanish W g φ fun x hx =>
            image_eq_zero_of_notMem_tsupport fun hxs =>
              hgN hxs ⟨(hW W hWm).2.1 hx, (hW W hWm).2.2 x hx⟩, mul_zero]
        · rw [dite_eq_right hWm]
      simp only [h0]
      exact hOff n d J u g φ hJ hdim hu hg hgc hφ (Set.disjoint_left.2 fun x hx hx' => hgN hx hx')

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

variable {n : ℕ}

theorem comap_curveLocalRing_strictMono (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    StrictMono (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q))) := by
  refine Monotone.strictMono_of_injective (fun P Q h ↦ Ideal.comap_mono h) ?_
  intro P Q h
  apply PrimeSpectrum.comap_injective_of_surjective _ (Ideal.Quotient.mk_surjective (I := I.map
    (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))))
  apply PrimeSpectrum.localization_comap_injective _ (RingHom.ker (eval q)).primeCompl
  exact h

theorem le_comap_curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (P : PrimeSpectrum (curveLocalRing I q)) :
    I ≤ (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) P).asIdeal := by
  intro x hx
  have h0 : Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q)))))
      (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))) x) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hx)
  change algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) x ∈ P.asIdeal
  rw [show algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) x = 0 from h0]
  exact P.asIdeal.zero_mem

theorem comap_curveLocalRing_le (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (P : PrimeSpectrum (curveLocalRing I q)) :
    (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) P).asIdeal ≤
      RingHom.ker (eval q) := by
  intro x hx
  by_contra h
  exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
    (isUnit_algebraMap_curveLocalRing I q x fun h' ↦ h (RingHom.mem_ker.2 h')))

theorem LocalDimComponentBound.proof : LocalDimComponentBound.Statement := by
  intro n I q hq
  rcases subsingleton_or_nontrivial (curveLocalRing I q) with hO | hO
  · refine ⟨RingHom.ker (eval q), inferInstance, fun x hx ↦ RingHom.mem_ker.2 (hq x hx),
      fun x hx ↦ RingHom.mem_ker.1 hx, ?_⟩
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  have : IsLocalRing (curveLocalRing I q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  set f := algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)
  set p := LTSeries.longestOf (PrimeSpectrum (curveLocalRing I q))
  set W := (PrimeSpectrum.comap f p.head).asIdeal with hW
  have hWle : ∀ i, W ≤ (PrimeSpectrum.comap f (p i)).asIdeal := fun i ↦
    Ideal.comap_mono (p.monotone (Fin.zero_le i))
  let p' : LTSeries (PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) W) :=
    { length := p.length
      toFun := fun i ↦ ⟨PrimeSpectrum.comap f (p i), hWle i⟩
      step := fun i ↦ comap_curveLocalRing_strictMono I q (p.step i) }
  refine ⟨W, (PrimeSpectrum.comap f p.head).isPrime, le_comap_curveLocalRing I q _,
    fun x hx ↦ RingHom.mem_ker.1 (comap_curveLocalRing_le I q _ hx), ?_⟩
  rw [ringKrullDim, Order.krullDim_eq_length_of_finiteDimensionalOrder, ringKrullDim_quotient]
  exact Order.LTSeries.length_le_krullDim p'

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace RegBallMass

variable {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin (d + 1)) (Fin n) ℂ}

theorem chartDens_indicator_mono (hN : RegDensNonneg.Statement) (hA : IsFiniteProjection J A)
    (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {S S' : Set (Fin n → ℂ)} (hS : S ⊆ S') (y : Fin (d + 1) → ℂ) :
    0 ≤ chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y ∧
      chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y ≤
        chartDens J A (S'.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) y := by
  have hfin : (fibre J A y).Finite := FiniteProjectionCluster.fibre_finite J A hA y
  have key : ∀ x ∈ fibre J A y, ∀ h : ∃ s, IsSheetAt J A x s,
      0 ≤ ReciprocityTheory.AnForm.maDens (fun k => (vecCons (logReg u ε) fun _ => euclPot :
        Fin (d + 1) → (Fin n → ℂ) → ℝ) k ∘ h.choose) y := by
    intro x hx h
    have := hN n d J A u ε x h.choose hε h.choose_spec
    rwa [hx.2] at this
  unfold chartDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  constructor
  · refine Finset.sum_nonneg fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with h
    · exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _) (key x hx h)
    · exact le_rfl
  · refine Finset.sum_le_sum fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with h
    · exact mul_le_mul_of_nonneg_right
        (Set.indicator_le_indicator_of_subset hS (fun _ => zero_le_one) x) (key x hx h)
    · exact le_rfl

theorem measurable_chartDens_indicator (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ)) (hA : IsFiniteProjection J A)
    (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) {S : Set (Fin n → ℂ)} (hS : MeasurableSet S) :
    Measurable (chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot)) := by
  refine (SheetSumMeasurable.proof n (d + 1) J A _ _ hJ hdim hA (measurable_const.indicator hS)
    fun k => ?_).1
  refine Fin.cases ?_ (fun i => ?_) k
  · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε)
  · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_euclPot n)

end RegBallMass


open RegBallMass in
theorem RegBallMass.proof (hF : RegFixedBallMass.Statement) (hM : RegLelongMono.Statement)
    (hN : RegDensNonneg.Statement) : RegBallMass.Statement := by
  intro n d J A u K hJ hdim hA hu hK
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.exists_norm_le
  set c : ℝ := Real.sqrt (n + 1) with hc
  have hc0 : 0 < c := Real.sqrt_pos.2 (by positivity)
  have hc2 : c ^ 2 = n + 1 := Real.sq_sqrt (by positivity)
  obtain ⟨M, hMb⟩ := hF n d J A u (R₀ + c) hJ hdim hA hu
  refine ⟨max M 0, le_max_right _ _, fun ε hε x hx r hr => ?_⟩
  set F : Set (Fin n → ℂ) → (Fin (d + 1) → ℂ) → ℝ := fun S =>
    chartDens J A (S.indicator fun _ => 1) (vecCons (logReg u ε) fun _ => euclPot) with hFdef
  have h1 : Metric.ball x r ⊆ euclBall x (c * r) := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm, pi_norm_lt_iff hr.1] at hy
    show Real.sqrt (euclPot (y - x)) < c * r
    rw [Real.sqrt_lt' (mul_pos hc0 hr.1), mul_pow, hc2]
    calc euclPot (y - x) = ∑ j, ‖(y - x) j‖ ^ 2 := rfl
      _ ≤ ∑ _j : Fin n, r ^ 2 :=
        Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hy j).le 2
      _ = n * r ^ 2 := by simp
      _ < (n + 1) * r ^ 2 := by nlinarith [pow_pos hr.1 2]
  have h2 : euclBall x c ⊆ Metric.closedBall 0 (R₀ + c) := by
    intro y hy
    have hy' : euclPot (y - x) < c ^ 2 := (Real.sqrt_lt' hc0).1 hy
    rw [Metric.mem_closedBall, dist_zero_right]
    have hyx : ‖y - x‖ ≤ c := by
      refine (pi_norm_le_iff_of_nonneg hc0.le).2 fun j => ?_
      have hj : ‖(y - x) j‖ ^ 2 ≤ euclPot (y - x) :=
        Finset.single_le_sum (f := fun j => ‖(y - x) j‖ ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ j)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hc0.le two_ne_zero).1 (by linarith)
    calc ‖y‖ = ‖x + (y - x)‖ := by rw [add_sub_cancel]
      _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
      _ ≤ R₀ + c := add_le_add (hR₀ x hx) hyx
  have h3 : euclBall x (c * r) ⊆ euclBall x c := fun y hy =>
    show Real.sqrt (euclPot (y - x)) < c from
      lt_of_lt_of_le (show Real.sqrt (euclPot (y - x)) < c * r from hy)
        (mul_le_of_le_one_right hc0.le hr.2)
  have hpos : ∀ {S S' : Set (Fin n → ℂ)}, S ⊆ S' → ∀ y, 0 ≤ F S y ∧ F S y ≤ F S' y :=
    fun hS y => chartDens_indicator_mono hN hA u hε.1 hS y
  have hEm : ∀ ρ, MeasurableSet (euclBall x ρ) := fun ρ =>
    (isOpen_lt (((contDiff_euclPot n).continuous.comp
      (continuous_id.sub continuous_const)).sqrt) continuous_const).measurableSet
  obtain ⟨hIR, hIRle⟩ := hMb ε hε
  have hint : ∀ S, MeasurableSet S → S ⊆ Metric.closedBall 0 (R₀ + c) → Integrable (F S) :=
    fun S hS hSR => hIR.mono' (measurable_chartDens_indicator hJ hdim hA u hε.1 hS).aestronglyMeasurable
      (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hpos hSR y).1]; exact (hpos hSR y).2)
  have hBI := hint _ Metric.isOpen_ball.measurableSet (h1.trans (h3.trans h2))
  refine ⟨hBI, ?_⟩
  have hmono := hM n d J A u ε x (c * r) c hJ hdim hA hε.1 (mul_pos hc0 hr.1)
    (mul_le_of_le_one_right hc0.le hr.2)
  have hI1 : ∫ y, F (Metric.ball x r) y ≤ ∫ y, F (euclBall x (c * r)) y :=
    integral_mono hBI (hint _ (hEm _) (h3.trans h2)) fun y => (hpos h1 y).2
  have hI2 : ∫ y, F (euclBall x c) y ≤ ∫ y, F (Metric.closedBall 0 (R₀ + c)) y :=
    integral_mono (hint _ (hEm _) h2) hIR fun y => (hpos h2 y).2
  have hI3 : ∫ y, F (euclBall x (c * r)) y ≤ r ^ (2 * d) * ∫ y, F (euclBall x c) y := by
    have : c ^ (2 * d) * ∫ y, F (euclBall x (c * r)) y ≤
        c ^ (2 * d) * (r ^ (2 * d) * ∫ y, F (euclBall x c) y) := by
      rw [← mul_assoc, ← mul_pow]; exact hmono
    exact le_of_mul_le_mul_left this (pow_pos hc0 _)
  calc ∫ y, F (Metric.ball x r) y ≤ r ^ (2 * d) * ∫ y, F (euclBall x c) y := hI1.trans hI3
    _ ≤ r ^ (2 * d) * max M 0 :=
      mul_le_mul_of_nonneg_left (hI2.trans (hIRle.trans (le_max_left _ _))) (pow_nonneg hr.1.le _)
    _ = max M 0 * r ^ (2 * d) := mul_comm _ _

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalCurvePointDVR.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I →
      ∃ _ : IsDomain (pointLocalRing I w), IsDiscreteValuationRing (pointLocalRing I w)

end

end GroundTheory.Heights₂.Heights
end
