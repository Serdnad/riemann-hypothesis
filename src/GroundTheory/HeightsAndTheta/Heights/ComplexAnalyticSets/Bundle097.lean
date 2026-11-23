module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle064
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle065
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle083
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle089
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle029
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle069
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle056
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle058
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PGraphAreaHolomorphic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle020
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle073
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle070
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle036
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle088
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle002
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle001
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets IsLocalRing

theorem length_slice_of_isCohenMacaulay (hCM : CMLengthParameters.Statement.{0})
    (hLS : LocalizeQuotientStages.Statement.{0}) {R : Type} [CommRing R] (m W I : Ideal R) [m.IsPrime] [W.IsPrime]
    [IsCohenMacaulayLocalRing (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m)))]
    (hW : W ∈ I.minimalPrimes) (hWm : W ≤ m) (huniq : ∀ W' ∈ I.minimalPrimes, W' ≤ m → W' = W)
    (d : ℕ) (lin : Fin d → R) (hlin : ∀ i, lin i ∈ m)
    (hdim : ringKrullDim (Localization.AtPrime m ⧸ W.map (algebraMap R (Localization.AtPrime m))) = (d : ℕ))
    (hT : ∀ g ∈ m, ∃ s ∉ m, s * g ∈ W ⊔ Ideal.span (Set.range lin)) :
    Module.length (Localization.AtPrime W) (Localization.AtPrime W ⧸ I.map (algebraMap R (Localization.AtPrime W))) =
      Module.length (Localization.AtPrime m)
        (Localization.AtPrime m ⧸ (I ⊔ Ideal.span (Set.range lin)).map (algebraMap R (Localization.AtPrime m))) := by
  classical
  have hIW : I ≤ W := hW.1.2
  have hP := isPrime_map_quotient_localization m W I hWm hIW

  have hunit : ∀ s ∉ m, IsUnit (((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) s) := fun s hs =>
    ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime m) m s).2 hs).map
      (Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m))))

  have hall : ∀ Q : Ideal (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))), Q.IsPrime →
      W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) ≤ Q := by
    intro Q hQ
    have hIQ : I ≤ Q.comap ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) := fun f hf => by
      rw [Ideal.mem_comap, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hf)]
      exact Q.zero_mem
    have hQm : Q.comap ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) ≤ m := fun f hf => by
      by_contra h
      exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ hf (hunit f h))
    obtain ⟨W', hW', hW'Q⟩ := Ideal.exists_minimalPrimes_le hIQ
    have : W' = W := huniq W' hW' (hW'Q.trans hQm)
    subst this
    exact Ideal.map_le_iff_le_comap.2 hW'Q
  have hmin : minimalPrimes (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) =
      {W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m)))} := by
    ext Q
    rw [Set.mem_singleton_iff]
    constructor
    · intro hQ
      exact le_antisymm (hQ.2 ⟨hP, bot_le⟩ (hall Q hQ.1.1)) (hall Q hQ.1.1)
    · rintro rfl
      exact ⟨⟨hP, bot_le⟩, fun Q hQ _ => hall Q hQ.1⟩

  have hPdef : W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) =
      (W.map (algebraMap R (Localization.AtPrime m))).map (Ideal.Quotient.mk _) := by
    rw [Ideal.map_map]
  have hdimP : ringKrullDim ((Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) ⧸
      W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m)))) = (d : ℕ) := by
    rw [ringKrullDim_eq_of_ringEquiv ((Ideal.quotEquivOfEq hPdef).trans
      (DoubleQuot.quotQuotEquivQuotOfLE (Ideal.map_mono hIW)))]
    exact hdim

  have hmB : m.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) =
      maximalIdeal (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) := by
    rw [← Ideal.map_map, Localization.AtPrime.map_eq_maximalIdeal]
    exact map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  have hspan : Ideal.span (Set.range fun i => ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) (lin i)) =
      (Ideal.span (Set.range lin)).map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) := by
    rw [Ideal.map_span, ← Set.range_comp]; rfl
  have hmax : Ideal.span (Set.range fun i => ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
      (algebraMap R (Localization.AtPrime m))) (lin i)) ⊔
      W.map ((Ideal.Quotient.mk (I.map (algebraMap R (Localization.AtPrime m)))).comp
        (algebraMap R (Localization.AtPrime m))) =
      maximalIdeal (Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) := by
    rw [hspan, ← Ideal.map_sup, sup_comm, ← hmB]
    apply le_antisymm
    · refine Ideal.map_mono (sup_le hWm ?_)
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hlin i
    · rw [Ideal.map_le_iff_le_comap]
      intro g hg
      obtain ⟨s, hs, hsg⟩ := hT g hg
      rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ (hunit s hs), ← map_mul]
      exact Ideal.mem_map_of_mem _ hsg
  have key := hCM _ _ d _ hmin hdimP hmax
  rw [hLS R m W I hWm hIW _ rfl] at key
  rw [← key, ← Module.length_eq_of_surjective (S := Localization.AtPrime m)
    (R := Localization.AtPrime m ⧸ I.map (algebraMap R (Localization.AtPrime m))) Ideal.Quotient.mk_surjective,
    hspan, ← Ideal.map_map, Ideal.map_sup]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ (Localization.AtPrime m) _ _).toLinearEquiv.length_eq

theorem LengthTransverseSlice.proof (hCM : CMLengthParameters.Statement.{0})
    (hLS : LocalizeQuotientStages.Statement.{0}) : LengthTransverseSlice.Statement := by
  intro n d I W q L hW hdim hq huniq hCMq hT
  have hWp : W.IsPrime := hW.1.1
  have hWm : W ≤ RingHom.ker (eval q) := fun f hf => RingHom.mem_ker.2 (hq f hf)
  have : IsCohenMacaulayLocalRing (localRingAt I q) := hCMq
  have h := length_slice_of_isCohenMacaulay hCM hLS (RingHom.ker (eval q)) W I hW hWm
    (fun W' hW' hle => huniq W' hW' fun f hf => RingHom.mem_ker.1 (hle hf)) d
    (fun i => linPoly L i - C ((L *ᵥ q) i))
    (fun i => by rw [RingHom.mem_ker, map_sub, eval_linPoly, eval_C, sub_self])
    (LocalDimDomain.proof n d W hWp hdim q hq)
    (fun g hg => by
      obtain ⟨s, hs, hsg⟩ := hT g (RingHom.mem_ker.1 hg)
      exact ⟨s, fun h => hs (RingHom.mem_ker.1 h), hsg⟩)
  unfold localMult
  rw [dite_eq_left hWp, dite_eq_left (inferInstance : (RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)).IsPrime), h]
  rfl

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm
open scoped ContDiff

theorem hessC_half_log_normSq_add {D : ℕ} (h : (Fin D → ℂ) → ℂ) (y : Fin D → ℂ)
    (hh : AnalyticAt ℂ h y) (hy : h y ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    hessC (fun w => Real.log (‖h w‖ ^ 2 + ε) / 2) y =
      ((ε / (2 * (‖h y‖ ^ 2 + ε) ^ 2) : ℝ) : ℂ) • hessC (fun w => ‖h w‖ ^ 2) y := by
  set L : (Fin D → ℂ) → ℝ := fun w => Real.log ‖h w‖ with hLdef
  set F : ℝ → ℝ := fun t => Real.log (Real.exp (2 * t) + ε) / 2 with hFdef
  set G : ℝ → ℝ := fun t => Real.exp (2 * t) with hGdef
  have hhc : ContDiffAt ℝ 2 h y := (hh.contDiffAt (n := 2)).restrict_scalars ℝ
  have hLc : ContDiffAt ℝ 2 L y := (hhc.norm ℝ hy).log (norm_ne_zero_iff.2 hy)
  have hL0 : hessC L y = 0 := ReciprocityTheory.AnForm.A.hessC_log_norm h y hh hy
  have he : ∀ t, HasDerivAt (fun t : ℝ => Real.exp (2 * t)) (Real.exp (2 * t) * 2) t := fun t => by
    simpa using ((hasDerivAt_id t).const_mul 2).exp
  have hFc : ContDiff ℝ 2 F :=
    ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).add contDiff_const).log
      (fun t => by simp only [Function.comp_apply, id]; positivity) |>.div_const 2
  have hGc : ContDiff ℝ 2 G := Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hF := HessCCompPluri.proof D F L y hFc.contDiffAt hLc hL0
  have hG := HessCCompPluri.proof D G L y hGc.contDiffAt hLc hL0
  have hdF : deriv F = fun t => Real.exp (2 * t) / (Real.exp (2 * t) + ε) := by
    funext t
    have hp : Real.exp (2 * t) + ε ≠ 0 := by positivity
    refine (((he t).add_const ε).log hp |>.div_const 2).deriv.trans ?_
    field_simp
  have hddF : ∀ t, deriv (deriv F) t = 2 * ε * Real.exp (2 * t) / (Real.exp (2 * t) + ε) ^ 2 := by
    intro t
    have hp : Real.exp (2 * t) + ε ≠ 0 := by positivity
    rw [hdF]
    refine ((he t).div ((he t).add_const ε) hp).deriv.trans ?_
    field_simp
    ring
  have hdG : deriv G = fun t => Real.exp (2 * t) * 2 := funext fun t => (he t).deriv
  have hddG : ∀ t, deriv (deriv G) t = Real.exp (2 * t) * 2 * 2 := fun t => by
    rw [hdG]
    exact ((he t).mul_const 2).deriv
  have hexp : ∀ w, h w ≠ 0 → Real.exp (2 * L w) = ‖h w‖ ^ 2 := fun w hw => by
    rw [hLdef, show 2 * Real.log ‖h w‖ = Real.log (‖h w‖ ^ 2) by rw [Real.log_pow]; push_cast; ring,
      Real.exp_log (by positivity)]
  have hev : ∀ᶠ w in 𝓝 y, h w ≠ 0 := hh.continuousAt.eventually_ne hy
  have eF : hessC (fun w => Real.log (‖h w‖ ^ 2 + ε) / 2) y = hessC (fun w => F (L w)) y :=
    ReciprocityTheory.AnForm.A.hessC_congr' (hev.mono fun w hw => by simp only [hFdef, hexp w hw])
  have eG : hessC (fun w => ‖h w‖ ^ 2) y = hessC (fun w => G (L w)) y :=
    ReciprocityTheory.AnForm.A.hessC_congr' (hev.mono fun w hw => by simp only [hGdef, hexp w hw])
  rw [eF, eG, hF, hG, hddF, hddG, hexp y hy, smul_smul]
  congr 1
  have ha : 0 < ‖h y‖ ^ 2 := by positivity
  push_cast
  field_simp

theorem LelongLimitOffZero.proof (hM : ChartMassCompact.Statement) : LelongLimitOffZero.Statement := by
  classical
  intro n d J u f φ hJ hdim hu hf hfc hφ hdisj
  unfold varInt
  split_ifs with hA
  swap
  · exact tendsto_const_nhds
  set A := hA.choose with hAdef
  have hAf : IsFiniteProjection J A := hA.choose_spec
  have hZc : IsClosed (zeroSet J) := by
    have : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | MvPolynomial.eval x q = 0} := by
      ext x; simp [zeroSet]
    rw [this]
    exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const
  have hK : IsCompact (tsupport f ∩ zeroSet J) := hfc.isCompact.inter_right hZc
  have hu0 : ∀ x ∈ tsupport f ∩ zeroSet J, linEval u x ≠ 0 := fun x hx h0 =>
    Set.disjoint_left.1 hdisj hx.1 ⟨hx.2, h0⟩
  set q : (Fin n → ℂ) → ℝ := fun x => ‖linEval u x‖ ^ 2 with hq
  have hqc : ContDiff ℝ ∞ q := (contDiff_norm_sq ℝ).comp (contDiff_linEval u)
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ x ∈ tsupport f ∩ zeroSet J, m ≤ q x := by
    rcases (tsupport f ∩ zeroSet J).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne hqc.continuous.continuousOn
      exact ⟨q x₀, by have := hu0 x₀ hx₀; simp only [hq]; positivity, fun x hx => hmin hx⟩
  have hGi : Integrable (chartAbsDens J A f (vecCons q φ)) := by
    refine hM n (d + 1) J A f _ hJ hdim hAf hf.continuous.continuousOn (fun i => ?_) (Or.inl hfc)
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using smoothNear_of_contDiff (S := zeroSet J) hqc
    · simpa using hφ j
  have hb : ∀ ε : ℝ, 0 < ε → ∀ y, ‖chartDens J A f (vecCons (logReg u ε) φ) y‖ ≤
      ε / (2 * m ^ 2) * chartAbsDens J A f (vecCons q φ) y := by
    intro ε hε y
    rw [Real.norm_eq_abs]
    refine (abs_chartDens_le J A f _ y).trans ?_
    have hfin := (FibreBound.proof n (d + 1) J A hJ hdim hAf y).2.1
    unfold chartAbsDens
    refine sheetSum_le_mul hfin _ _ _ fun x hx s hs => ?_
    by_cases hfx : f x = 0
    · simp [hfx]
    have hxK : x ∈ tsupport f ∩ zeroSet J := ⟨subset_tsupport _ hfx, hx.1⟩
    obtain rfl : A *ᵥ x = y := hx.2
    obtain ⟨U, hU, hxU, hsd, hsx, -, -⟩ := hs
    have hsa : AnalyticAt ℂ s (A *ᵥ x) := analyticAt_pi_iff.2 fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood _ U (fun z => s z i) hU (differentiableOn_pi.1 hsd i) _ hxU
    have hha : AnalyticAt ℂ (fun w => linEval u (s w)) (A *ᵥ x) := by
      unfold linEval
      exact Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.mul ((analyticAt_pi_iff.1 hsa) j)
    have hne : linEval u (s (A *ᵥ x)) ≠ 0 := by rw [hsx]; exact hu0 x hxK
    have hH0 := hessC_half_log_normSq_add (fun w => linEval u (s w)) _ hha hne hε
    simp only [hsx] at hH0
    have hH : hessC (logReg u ε ∘ s) (A *ᵥ x) =
        ((ε / (2 * (q x + ε) ^ 2) : ℝ) : ℂ) • hessC (q ∘ s) (A *ᵥ x) := hH0
    rw [vecCons_comp, vecCons_comp, maDens_cons_of_hessC_eq_smul (logReg u ε ∘ s) (q ∘ s) _ _ _ hH]
    have ha : m ≤ q x := hm x hxK
    have hc0 : 0 ≤ ε / (2 * (q x + ε) ^ 2) := by positivity
    have hc : ε / (2 * (q x + ε) ^ 2) ≤ ε / (2 * m ^ 2) :=
      div_le_div_of_nonneg_left hε.le (by positivity) (by nlinarith)
    calc |f x * (ε / (2 * (q x + ε) ^ 2) * maDens (Fin.cons (q ∘ s) fun k => φ k ∘ s) (A *ᵥ x))|
        = ε / (2 * (q x + ε) ^ 2) * |f x * maDens (Fin.cons (q ∘ s) fun k => φ k ∘ s) (A *ᵥ x)| := by
          rw [mul_left_comm, abs_mul, abs_of_nonneg hc0]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (abs_nonneg _)
  have hlim : Tendsto (fun ε : ℝ => ε / (2 * m ^ 2) * ∫ y, chartAbsDens J A f (vecCons q φ) y)
      (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun ε : ℝ => ε / (2 * m ^ 2) * ∫ y, chartAbsDens J A f (vecCons q φ) y) := by
      fun_prop
    exact tendsto_nhdsWithin_of_tendsto_nhds (hc.tendsto' 0 0 (by simp))
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  unfold chartInt
  rw [← integral_const_mul]
  exact norm_integral_le_of_norm_le (hGi.const_mul _) (Eventually.of_forall (hb ε hε))

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Module Matrix

open scoped ENNReal

noncomputable section

theorem SheetImageAreaSet.proof : SheetImageAreaSet.Statement := by
  classical
  intro n d A U s hU hs hA B hB hBU
  rcases U.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
  · obtain rfl : B = ∅ := Set.eq_empty_of_forall_notMem fun y hy => hBU y hy
    simp
  let Ue : Set (EuclideanSpace ℂ (Fin d)) := WithLp.ofLp ⁻¹' U
  have hUe : IsOpen Ue := hU.preimage (PiLp.continuous_ofLp 2 _)
  let T : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin n) := fun y => WithLp.toLp 2 (s (WithLp.ofLp y))
  let P : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin d) :=
    (WithLp.linearEquiv 2 ℂ (Fin d → ℂ)).symm.toLinearMap ∘ₗ Matrix.mulVecLin A ∘ₗ
      (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).toLinearMap
  have hPT : ∀ y ∈ Ue, P (T y) = y := fun y hy => by
    simp [P, T, hA _ hy]
  have hPs : Function.Surjective P := by
    have hle : Ue ⊆ (LinearMap.range P : Set _) := fun y hy => ⟨T y, hPT y hy⟩
    refine LinearMap.range_eq_top.1 (Submodule.eq_top_of_nonempty_interior' _
      ⟨WithLp.toLp 2 y₀, interior_mono hle ?_⟩)
    rw [hUe.interior_eq]
    exact hy₀
  obtain ⟨m, e, Q, L, π, hQn, hQ⟩ := SheetImageAreaSet.exists_adapted_frame P hPs
  let F : EuclideanSpace ℂ (Fin d) → EuclideanSpace ℂ (Fin m) := fun x => π (T (L.symm x))
  let Ω : Set (EuclideanSpace ℂ (Fin d)) := L.symm ⁻¹' Ue
  have hLc : Continuous L.symm := LinearMap.continuous_of_finiteDimensional _
  have hΩ : IsOpen Ω := hUe.preimage hLc
  have hQT : ∀ y ∈ Ue, Q (T y) = graphPt e F (L y) := by
    intro y hy
    rw [hQ, hPT y hy]
    simp [graphPt, F]
  have hsd : ∀ y ∈ Ue, DifferentiableAt ℂ s (WithLp.ofLp y) := fun y hy =>
    hs.differentiableAt (hU.mem_nhds hy)
  have hTd : ∀ y ∈ Ue, DifferentiableAt ℂ T y := fun y hy =>
    (PiLp.hasFDerivAt_toLp (𝕜 := ℂ) 2 _).differentiableAt.comp y
      ((hsd y hy).comp y (PiLp.hasFDerivAt_ofLp (𝕜 := ℂ) 2 y).differentiableAt)
  have hLd : ∀ x, DifferentiableAt ℂ (fun x => L.symm x) x := fun x => by
    simpa using (LinearMap.toContinuousLinearMap L.symm.toLinearMap).differentiableAt (x := x)
  have hπd : ∀ z, DifferentiableAt ℂ (fun z => π z) z := fun z => by
    simpa using (LinearMap.toContinuousLinearMap π).differentiableAt (x := z)
  have hFd : DifferentiableOn ℂ F Ω := fun x hx =>
    ((hπd _).comp x ((hTd _ hx).comp x (hLd x))).differentiableWithinAt
  have hBΩ : L '' B ⊆ Ω := by
    rintro _ ⟨y, hy, rfl⟩
    show L.symm (L y) ∈ Ue
    rw [L.symm_apply_apply]
    exact hBU y hy
  have hLB : MeasurableSet (L '' B) := by
    rw [L.image_eq_preimage_symm]
    exact hLc.measurable hB
  have hQi : Isometry Q := AddMonoidHomClass.isometry_of_norm Q hQn
  have himg : Q '' (T '' B) = graphPt e F '' (L '' B) := by
    rw [Set.image_image, Set.image_image]
    exact Set.image_congr fun y hy => hQT y (hBU y hy)
  have hGA := GraphAreaHolomorphic.proof (AreaGraph.proof
    (AreaGraphBound.proof AreaGraphPiece.proof AreaGraphPartition.proof GraphJacContinuous.proof))
  have hfin : finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  have : (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).IsAddHaarMeasure := by
    have := isAddHaarMeasure_hausdorffMeasure (E := EuclideanSpace ℂ (Fin d))
    rwa [hfin] at this
  let Lr : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin d) :=
    LinearMap.toContinuousLinearMap ((L : _ →ₗ[ℂ] _).restrictScalars ℝ)
  let Qr : EuclideanSpace ℂ (Fin n) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    LinearMap.toContinuousLinearMap (Q.restrictScalars ℝ)
  have hCV := lintegral_image_eq_lintegral_abs_det_fderiv_mul (μH[((2 * d : ℕ) : ℝ)]) hB
    (f := fun y => L y) (f' := fun _ => Lr) (fun y _ => Lr.hasFDerivAt.hasFDerivWithinAt) L.injective.injOn
    (fun x => ENNReal.ofReal (areaJacobian (fderiv ℝ (graphPt e F) x :
      EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))))
  rw [← hQi.hausdorffMeasure_image (Or.inl (Nat.cast_nonneg _)), himg,
    hGA d m n e Ω F hΩ hFd (L '' B) hBΩ hLB, hCV]
  refine setLIntegral_congr_fun hB fun y hy => ?_
  have hy' : y ∈ Ue := hBU y hy
  let Mt : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap.comp
      ((fderiv ℝ s (WithLp.ofLp y)).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℂ)).toContinuousLinearMap)
  have hT : HasFDerivAt T Mt y :=
    (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp y
      (((hsd y hy').restrictScalars ℝ).hasFDerivAt.comp y (PiLp.hasFDerivAt_ofLp (𝕜 := ℝ) 2 y))
  have hx : L y ∈ Ω := hBΩ ⟨y, hy, rfl⟩
  have hFR : DifferentiableAt ℝ F (L y) := ((hFd.differentiableAt (hΩ.mem_nhds hx)).restrictScalars ℝ)
  have hG : HasFDerivAt (graphPt e F) (fderiv ℝ (graphPt e F) (L y)) (L y) :=
    (GraphAreaHolomorphic.differentiableAt_graphPt_real e hFR).hasFDerivAt
  have h1 : HasFDerivAt (fun z => Q (T z)) (Qr.comp Mt) y := Qr.hasFDerivAt.comp y hT
  have h2 : HasFDerivAt (fun z => graphPt e F (L z)) ((fderiv ℝ (graphPt e F) (L y)).comp Lr) y :=
    hG.comp y Lr.hasFDerivAt
  have hM : Qr.comp Mt = (fderiv ℝ (graphPt e F) (L y)).comp Lr :=
    h1.unique (h2.congr_of_eventuallyEq (Filter.eventually_of_mem (hUe.mem_nhds hy') fun z hz => hQT z hz))
  have hJ : sheetJac s (WithLp.ofLp y) =
      areaJacobian (Mt : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) :=
    congrArg areaJacobian (LinearMap.ext fun v => rfl)
  have hJ2 : areaJacobian (Mt : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) =
      areaJacobian (fderiv ℝ (graphPt e F) (L y) : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) *
        |LinearMap.det (Lr : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin d))| := by
    have hQr : ∀ v, ‖(Qr : EuclideanSpace ℂ (Fin n) →ₗ[ℝ] EuclideanSpace ℂ (Fin n)) v‖ = ‖v‖ := fun v => by
      simp only [Qr, ContinuousLinearMap.coe_coe, LinearMap.coe_toContinuousLinearMap',
        LinearMap.coe_restrictScalars]
      exact hQn v
    rw [← SheetImageAreaSet.areaJacobian_comp_of_norm _ hQr,
      ← SheetImageAreaSet.areaJacobian_comp_endo]
    rw [← ContinuousLinearMap.toLinearMap_comp, ← ContinuousLinearMap.toLinearMap_comp, hM]
  rw [hJ, hJ2, mul_comm (areaJacobian _), ENNReal.ofReal_mul (abs_nonneg _)]

end

end GroundTheory.Heights₂.Heights
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Matrix ComplexSets

noncomputable section

theorem TubeCollarMass.proof (hC : TubeCollarCompare.Statement) (hM : ChartMassCompare.Statement)
    (hF : MassFinite.Statement) : TubeCollarMass.Statement := by
  intro n d J A P R hJ hdim hA hP
  obtain ⟨C, hCle⟩ := hC n d J A P R hJ hdim hA hP
  have hψ : ∀ k : Fin (d + 1), SmoothNear (zeroSet J) ((fun _ => euclPot) k) :=
    fun _ => smoothNear_of_contDiff (contDiff_euclPot n)

  have hI : Integrable (chartAbsDens J A ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ))
      (fun _ : Fin (d + 1) => euclPot)) := by
    obtain ⟨K, hK, hle⟩ := hM n (d + 1) J A (fun _ => euclPot) R hJ hdim hA hψ
    have hmeas := (SheetSumMeasurable.proof n (d + 1) J A
      ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ)) (fun _ => euclPot) hJ hdim hA
      (measurable_const.indicator Metric.isClosed_closedBall.measurableSet) hψ).2
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    have hbd : Bornology.IsBounded
        (WithLp.ofLp ⁻¹' Metric.closedBall (0 : Fin n → ℂ) R : Set (EuclideanSpace ℂ (Fin n))) :=
      (PiLp.antilipschitzWith_ofLp 2 fun _ : Fin n => ℂ).isBounded_preimage Metric.isBounded_closedBall
    obtain ⟨R', hR'⟩ := (Metric.isBounded_iff_subset_ball 0).1 hbd
    have h1 := hle (fun _ => 1) measurable_const
    simp only [enorm_one, setLIntegral_one] at h1
    refine h1.trans_lt (ENNReal.mul_lt_top hK ?_)
    exact (measure_mono (Set.inter_subset_inter_right _ hR')).trans_lt (hF n (d + 1) J hJ hdim R')

  have hl : Measurable (logAbsSq P) :=
    Real.measurable_log.comp ((MvPolynomial.continuous_eval P).norm.pow 2).measurable
  refine (hI.const_mul C).mono'
    (((measurable_tubeDens hA P R _).indicator (measurableSet_le measurable_const hl)).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun y _ => tubeDens_nonneg J A P R _ y) y)]
  exact hCle y

end

end GroundTheory.Heights₂.Heights
end
