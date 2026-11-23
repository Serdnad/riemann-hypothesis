module

public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle003
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle238
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.PowerBoundFastDecay
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.Bundle005
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.LogAbsEqLogIdeleNorm
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiClosT
import GroundTheory.AutomorphicForms.QuotientMeasure
public import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.SplitCentreMulTor
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Filter Set
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal

namespace DiscreteGroups.T1.G

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem continuous_aS : Continuous (aS E n) :=
  GlobalTheory.OneRep.SplitTwist.continuous_splitCentre.prodMk continuous_const

theorem lg_one_eq_zero : lg (1 : GA E n) = 0 := by
  have h := lg_mul (1 : GA E n) 1
  rw [mul_one] at h
  linarith

theorem lg_splitCentre (s : ℝ) : lg (splitCentre E n s) = s * lg (splitCentre E n 1) := by
  let f : ℝ →+ ℝ :=
    { toFun := fun s => lg (splitCentre E n s)
      map_zero' := by simp only [splitCentre_zero, lg_one_eq_zero]
      map_add' := fun s t => by simp only [splitCentre_add, lg_mul] }
  have hf : Continuous f := by
    show Continuous fun s => logAbs (splitCentre E n s).val.det
    exact continuous_logAbs_det.comp GlobalTheory.OneRep.SplitTwist.continuous_splitCentre
  have h := map_real_smul f hf s 1
  simpa [f, smul_eq_mul] using h

theorem ldet_mul_aS (x : H E n 0) (s : ℝ) : ldet (x * aS E n s) = ldet x + s * ldet (aS E n 1) := by
  show lg (x.1 * splitCentre E n s) = lg x.1 + s * lg (splitCentre E n 1)
  rw [lg_mul, lg_splitCentre]

theorem ldet_rat (γ : ratH E n 0) (y : H E n 0) : ldet ((γ : H E n 0) * y) = ldet y :=
  lg_rat_mul _ (eR γ).2 y.1

theorem sigmaFinite_nu (hn : 1 ≤ n) (D : Dom E n 0) : SigmaFinite D.ν :=
  ⟨⟨{ set := fun k : ℕ => {x : H E n 0 | |ldet x| ≤ k}
      set_mem := fun _ => Set.mem_univ _
      finite := fun k => CP.cp_vol hn D k
      spanning := Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨⌈|ldet x|⌉₊, show |ldet x| ≤ (⌈|ldet x|⌉₊ : ℝ) from Nat.le_ceil _⟩ }⟩⟩

theorem integral_shift {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] (D : Dom E n 0) (g : H E n 0 → F')
    (hg : ∀ (γ : ratH E n 0) x, g ((γ : H E n 0) * x) = g x) (a : H E n 0) :
    ∫ x, g (x * a) ∂D.ν = ∫ x, g x ∂D.ν := by
  haveI := borelSpace_H (E := E) (n := n)
  haveI := D.haar.2.1
  haveI : SMulInvariantMeasure (ratH E n 0) (H E n 0) D.μ :=
    ⟨fun γ s _ => by haveI := D.haar.1; exact measure_preimage_mul D.μ (γ : H E n 0) s⟩
  haveI : Countable (ratH E n 0) := (eR_bijective (E := E) (n := n)).1.countable
  have hmp : MeasurePreserving (fun x : H E n 0 => x * a) D.μ D.μ := measurePreserving_mul_right D.μ a
  have hemb : MeasurableEmbedding (fun x : H E n 0 => x * a) :=
    (Homeomorph.mulRight a).toMeasurableEquiv.measurableEmbedding
  have hfd : IsFundamentalDomain (ratH E n 0) ((fun x : H E n 0 => x * a) ⁻¹' D.F) D.μ :=
    D.fd.preimage_of_equiv hmp.quasiMeasurePreserving Function.bijective_id fun γ x => by
      simp only [Subgroup.smul_def, smul_eq_mul, id, mul_assoc]
  rw [Dom.ν, D.fd.setIntegral_eq hfd (f := fun x => g (x * a)) fun γ x => by
      simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc, hg]]
  exact hmp.setIntegral_preimage_emb hemb g D.F

theorem lintegral_shift (D : Dom E n 0) (g : H E n 0 → ℝ≥0∞)
    (hg : ∀ (γ : ratH E n 0) x, g ((γ : H E n 0) * x) = g x) (a : H E n 0) :
    ∫⁻ x, g (x * a) ∂D.ν = ∫⁻ x, g x ∂D.ν := by
  haveI := borelSpace_H (E := E) (n := n)
  haveI := D.haar.2.1
  haveI : SMulInvariantMeasure (ratH E n 0) (H E n 0) D.μ :=
    ⟨fun γ s _ => by haveI := D.haar.1; exact measure_preimage_mul D.μ (γ : H E n 0) s⟩
  haveI : Countable (ratH E n 0) := (eR_bijective (E := E) (n := n)).1.countable
  have hmp : MeasurePreserving (fun x : H E n 0 => x * a) D.μ D.μ := measurePreserving_mul_right D.μ a
  have hemb : MeasurableEmbedding (fun x : H E n 0 => x * a) :=
    (Homeomorph.mulRight a).toMeasurableEquiv.measurableEmbedding
  have hfd : IsFundamentalDomain (ratH E n 0) ((fun x : H E n 0 => x * a) ⁻¹' D.F) D.μ :=
    D.fd.preimage_of_equiv hmp.quasiMeasurePreserving Function.bijective_id fun γ x => by
      simp only [Subgroup.smul_def, smul_eq_mul, id, mul_assoc]
  rw [Dom.ν, D.fd.setLIntegral_eq hfd (f := fun x => g (x * a)) fun γ x => by
      simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc, hg]]
  exact hmp.setLIntegral_comp_preimage_emb hemb g D.F

theorem integrable_shift (D : Dom E n 0) (g : H E n 0 → ℂ) (hg : ∀ (γ : ratH E n 0) x, g ((γ : H E n 0) * x) = g x)
    (a : H E n 0) (hgi : Integrable g D.ν) (hm : AEStronglyMeasurable (fun x => g (x * a)) D.ν) :
    Integrable (fun x => g (x * a)) D.ν :=
  ⟨hm, (lintegral_shift D (fun x => ‖g x‖ₑ) (fun γ x => by simp only [hg]) a).trans_lt hgi.2⟩

theorem integral_affine {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] (v : ℝ → F') (r c : ℝ) (hc : 0 < c) :
    ∫ s : ℝ, v (r - s * c) = c⁻¹ • ∫ u : ℝ, v u := by
  have h1 : (fun s : ℝ => v (r - s * c)) = fun s => (fun u => v (r - u)) (c * s) := by
    funext s
    show v (r - s * c) = v (r - c * s)
    rw [mul_comm]
  rw [h1, Measure.integral_comp_mul_left (fun u => v (r - u)) c, integral_sub_left_eq_self (fun u => v u) volume r,
    abs_of_pos (inv_pos.2 hc)]

theorem avgInt_holds : AvgInt := by
  intro E _ _ _ n hn D L hL hLc hLi w hwc hws hw1
  haveI := borelSpace_H (E := E) (n := n)
  haveI := sigmaFinite_nu hn D
  obtain ⟨c, hc_eq⟩ : ∃ c, c = ldet (aS E n 1) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hc_eq]; exact lg_e_pos hn
  have hwi : Integrable w := hwc.integrable_of_hasCompactSupport hws
  have hldc : Continuous (ldet : H E n 0 → ℝ) := continuous_ldet
  have cF3 : Continuous fun p : H E n 0 × ℝ => w (ldet p.1 - p.2 * c) * L p.1 :=
    (hwc.comp ((hldc.comp continuous_fst).sub (continuous_snd.mul continuous_const))).mul (hLc.comp continuous_fst)
  have cF2 : Continuous fun p : H E n 0 × ℝ => w (ldet p.1) * L (p.1 * aS E n p.2) :=
    (hwc.comp (hldc.comp continuous_fst)).mul (hLc.comp (continuous_fst.mul (continuous_aS.comp continuous_snd)))
  have hF3 : Integrable (fun p : H E n 0 × ℝ => w (ldet p.1 - p.2 * c) * L p.1) (D.ν.prod volume) := by
    rw [integrable_prod_iff cF3.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
    · exact ((hwi.comp_sub_left (ldet x)).comp_mul_right' hc.ne').mul_const (L x)
    · have e : (fun x => ∫ s : ℝ, ‖w (ldet x - s * c) * L x‖) = fun x => (c⁻¹ * ∫ u : ℝ, ‖w u‖) * ‖L x‖ := by
        funext x
        simp_rw [norm_mul]
        rw [integral_mul_const, integral_affine (fun u => ‖w u‖) (ldet x) c hc, smul_eq_mul]
      refine (hLi.norm.const_mul (c⁻¹ * ∫ u : ℝ, ‖w u‖)).congr (Eventually.of_forall fun x => ?_)
      exact (congrFun e x).symm
  have e3x : ∀ x, ∫ s : ℝ, w (ldet x - s * c) * L x = (c : ℂ)⁻¹ * L x := fun x => by
    rw [integral_mul_const, integral_affine w (ldet x) c hc, hw1, Complex.real_smul, mul_one, Complex.ofReal_inv]
  have I3 : ∫ x, ∫ s : ℝ, w (ldet x - s * c) * L x ∂volume ∂D.ν = (c : ℂ)⁻¹ * ∫ x, L x ∂D.ν := by
    simp_rw [e3x]
    exact integral_const_mul _ _
  have swap3 : ∫ x, ∫ s : ℝ, w (ldet x - s * c) * L x ∂volume ∂D.ν =
      ∫ s : ℝ, ∫ x, w (ldet x - s * c) * L x ∂D.ν ∂volume := integral_integral_swap hF3
  have hinv : ∀ s : ℝ, ∀ (γ : ratH E n 0) y, w (ldet ((γ : H E n 0) * y) - s * c) * L ((γ : H E n 0) * y) =
      w (ldet y - s * c) * L y := fun s γ y => by rw [ldet_rat, hL]
  have shift32 : ∀ s : ℝ, ∫ x, w (ldet x - s * c) * L x ∂D.ν = ∫ x, w (ldet x) * L (x * aS E n s) ∂D.ν := by
    intro s
    rw [← integral_shift D (fun y => w (ldet y - s * c) * L y) (hinv s) (aS E n s)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ldet_mul_aS, ← hc_eq, add_sub_cancel_right]
  have hF2 : Integrable (fun p : H E n 0 × ℝ => w (ldet p.1) * L (p.1 * aS E n p.2)) (D.ν.prod volume) := by
    rw [integrable_prod_iff' cF2.aestronglyMeasurable]
    obtain ⟨h1, h2⟩ := (integrable_prod_iff' cF3.aestronglyMeasurable).1 hF3
    refine ⟨h1.mono fun s hs => ?_, ?_⟩
    · have hm : AEStronglyMeasurable (fun x => (fun y => w (ldet y - s * c) * L y) (x * aS E n s)) D.ν :=
        (((hwc.comp (hldc.sub continuous_const)).mul hLc).comp (continuous_mul_const (aS E n s))).aestronglyMeasurable
      refine (integrable_shift D (fun y => w (ldet y - s * c) * L y) (hinv s) (aS E n s) hs hm).congr
        (Eventually.of_forall fun x => ?_)
      simp only [ldet_mul_aS, ← hc_eq, add_sub_cancel_right]
    · refine h2.congr (Eventually.of_forall fun s => ?_)
      show ∫ x, ‖w (ldet x - s * c) * L x‖ ∂D.ν = ∫ x, ‖w (ldet x) * L (x * aS E n s)‖ ∂D.ν
      rw [← integral_shift D (fun y => ‖w (ldet y - s * c) * L y‖) (fun γ y => by rw [hinv s γ y]) (aS E n s)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [ldet_mul_aS, ← hc_eq, add_sub_cancel_right]
  have swap2 : ∫ x, ∫ s : ℝ, w (ldet x) * L (x * aS E n s) ∂volume ∂D.ν =
      ∫ s : ℝ, ∫ x, w (ldet x) * L (x * aS E n s) ∂D.ν ∂volume := integral_integral_swap hF2
  have ex : ∀ x, w (ldet x) * (∫ s : ℝ, L (x * aS E n s)) = ∫ s : ℝ, w (ldet x) * L (x * aS E n s) :=
    fun x => (integral_const_mul _ _).symm
  have key : ∫ x, w (ldet x) * (∫ s : ℝ, L (x * aS E n s)) ∂D.ν = (c : ℂ)⁻¹ * ∫ x, L x ∂D.ν := by
    simp_rw [ex]
    rw [swap2]
    simp_rw [← shift32]
    rw [← swap3, I3]
  refine ⟨?_, ?_⟩
  · refine hF2.integral_prod_left.congr (Eventually.of_forall fun x => ?_)
    exact integral_const_mul (w (ldet x)) (fun s => L (x * aS E n s))
  · rw [key, ← hc_eq, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hc.ne'), one_mul]

end DiscreteGroups.T1.G

end
end

section

set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Filter Set
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal

namespace DiscreteGroups.T1.G.Dcy

attribute [local instance] borelH

theorem piVecEx_holds : PiVecEx := by
  intro E _ _ _ n hn D π hθ ψ hψ u hu hus
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  have hψc : IsCuspForm ψ := π.cusp ψ hψ
  have hA : ∀ t g, ψ.1 (splitCentre E n t * g) = ψ.1 g := hθ.1 ψ hψ
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ s, u s ≠ 0 → |s| ≤ R := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).1 hus.isCompact.isBounded
    exact ⟨R, fun s hs => by
      have := hR (subset_tsupport u hs)
      rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this⟩
  obtain ⟨U, hU⟩ := hu.bounded_above_of_compact_support hus
  have hU0 : 0 ≤ U := (norm_nonneg _).trans (hU 0)
  set S : Set (H E n 0) := {x | |ldet x| ≤ R} with hSdef
  have hSm : MeasurableSet S :=
    (isClosed_le (continuous_abs.comp (continuous_ldet (E := E) (n := n))) continuous_const).measurableSet
  have hS : D.ν S < ⊤ := CP.cp_vol hn D R
  set f : H E n 0 → ℂ := fun x => ψ.1 x.1 * u (ldet x) with hf
  have hfS : ∀ x, x ∉ S → f x = 0 := fun x hx => by
    simp only [hf]
    by_contra h
    exact hx (hR _ (right_ne_zero_of_mul h))
  have hfind : S.indicator f = f := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, hfS x hx]
  have hfc : Continuous f :=
    ((continuous_of_mem π hψ).comp continuous_fst).mul (hu.comp (continuous_ldet (E := E) (n := n)))
  have hwt : ∀ x : H E n 0, 0 ≤ wt x := fun x => by
    have h1 := redSize_nonneg x.1
    have h2 := redSize_nonneg x.2
    simp only [wt]; linarith
  refine ⟨?_, fun M => ?_⟩
  · obtain ⟨C, hC⟩ := cp_decay_wt ψ hψc hA R 0
    haveI : IsFiniteMeasure (D.ν.restrict S) := isFiniteMeasure_restrict.2 hS.ne
    rw [← hfind, memLp_indicator_iff_restrict hSm.nullMeasurableSet]
    refine MemLp.of_bound hfc.aestronglyMeasurable (C * U) ((ae_restrict_iff' hSm).2 (Eventually.of_forall fun x hx => ?_))
    have h1 := hC x hx
    rw [pow_zero, mul_one] at h1
    simp only [hf, norm_mul]
    exact mul_le_mul h1 (hU _) (norm_nonneg _) ((norm_nonneg _).trans h1)
  · obtain ⟨C, hC⟩ := cp_decay_wt ψ hψc hA R M
    have hC0 : ∀ x ∈ S, 0 ≤ C := fun x hx => (mul_nonneg (norm_nonneg _) (pow_nonneg (hwt x) _)).trans (hC x hx)
    set K : ℝ≥0∞ := ENNReal.ofReal ((C * U) ^ 2) with hK
    have hpt : ∀ x, ENNReal.ofReal (wt x ^ (2 * M)) * ‖f x‖ₑ ^ 2 ≤ S.indicator (fun _ => K) x := by
      intro x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
          ← ENNReal.ofReal_mul (pow_nonneg (hwt x) _)]
        refine ENNReal.ofReal_le_ofReal ?_
        have e : wt x ^ (2 * M) * ‖f x‖ ^ 2 = (‖ψ.1 x.1‖ * wt x ^ M * ‖u (ldet x)‖) ^ 2 := by
          simp only [hf, norm_mul]; rw [pow_mul]; ring
        rw [e]
        refine pow_le_pow_left₀ (mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (hwt x) _)) (norm_nonneg _)) ?_ 2
        exact mul_le_mul (hC x hx) (hU _) (norm_nonneg _) (hC0 x hx)
      · rw [Set.indicator_of_notMem hx, hfS x hx]
        simp
    calc ∫⁻ x, ENNReal.ofReal (wt x ^ (2 * M)) * ‖ψ.1 x.1 * u (ldet x)‖ₑ ^ 2 ∂D.ν
        ≤ ∫⁻ x, S.indicator (fun _ => K) x ∂D.ν := lintegral_mono hpt
      _ = K * D.ν S := lintegral_indicator_const hSm K
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hS

end DiscreteGroups.T1.G.Dcy

end
end

section

set_option linter.all false

noncomputable section

open NumberField Matrix MeasureTheory Filter Set
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc
open scoped ENNReal

namespace DiscreteGroups.T1.G.Dcy

attribute [local instance] borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def chi (N : ℕ) (s : ℝ) : ℝ := max 0 (min 1 ((N : ℝ) + 1 - |s|))

theorem continuous_chi (N : ℕ) : Continuous (chi N) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs))

theorem chi_nonneg (N : ℕ) (s : ℝ) : 0 ≤ chi N s := le_max_left _ _

theorem chi_eq_zero {N : ℕ} {s : ℝ} (h : (N : ℝ) + 1 ≤ |s|) : chi N s = 0 :=
  max_eq_left (min_le_of_right_le (by linarith))

theorem chi_eq_one {N : ℕ} {s : ℝ} (h : |s| ≤ N) : chi N s = 1 := by
  unfold chi
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem hasCompactSupport_chi_pow (N k : ℕ) : HasCompactSupport fun s : ℝ => chi N s * s ^ k :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) ((N : ℝ) + 1)) fun s hs => by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, not_le] at hs
    rw [chi_eq_zero hs.le, zero_mul]

theorem countable_GL' (m : ℕ) : Countable (GL (Fin m) E) := by
  have : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have : Countable (Matrix (Fin m) (Fin m) E) := inferInstanceAs (Countable (Fin m → Fin m → E))
  exact Function.Injective.countable (f := (Units.val : GL (Fin m) E → Matrix (Fin m) (Fin m) E)) fun a b hab => Units.ext hab

theorem countable_ratH' : Countable (ratH E n 0) := by
  have := countable_GL' (E := E) n
  have := countable_GL' (E := E) 0
  show Countable ((ratGL E n).prodMap (ratGL E 0)).range
  exact (MonoidHom.rangeRestrict_surjective ((ratGL E n).prodMap (ratGL E 0))).countable

theorem bdd_of_mem {π : CuspSub E n} (hθ : ThetaFix π) {ψ : Sm E n} (hψ : ψ ∈ π.V) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : H E n 0, |ldet x| ≤ R → ‖ψ.1 x.1‖ ≤ C := by
  obtain ⟨C, hC⟩ := cp_decay_wt ψ (π.cusp ψ hψ) (hθ.1 ψ hψ) R 0
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have := hC x hx
  rw [pow_zero, mul_one] at this
  exact this.trans (le_max_left _ _)

theorem integrable_of_ldet (hn : 1 ≤ n) (D : Dom E n 0) (F : H E n 0 → ℂ) (hF : Continuous F) (R K : ℝ)
    (h0 : ∀ x, R < |ldet x| → F x = 0) (hK : ∀ x, |ldet x| ≤ R → ‖F x‖ ≤ K) : Integrable F D.ν := by
  haveI : BorelSpace (H E n 0) := ⟨rfl⟩
  set S : Set (H E n 0) := {x | |ldet x| ≤ R} with hSdef
  have hSm : MeasurableSet S :=
    (isClosed_le (continuous_abs.comp (continuous_ldet (E := E) (n := n))) continuous_const).measurableSet
  have hS : D.ν S < ⊤ := CP.cp_vol hn D R
  have hind : S.indicator F = F := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, h0 x (lt_of_not_ge hx)]
  rw [← hind, integrable_indicator_iff hSm]
  exact Measure.integrableOn_of_bounded (M := K) hS.ne hF.aestronglyMeasurable
    ((ae_restrict_iff' hSm).2 (Eventually.of_forall fun x hx => hK x hx))

theorem integrable_pair (hn : 1 ≤ n) (D : Dom E n 0) {π : CuspSub E n} (hθ : ThetaFix π) {ψ φ : Sm E n}
    (hψ : ψ ∈ π.V) (hφ : φ ∈ π.V) (U V : ℝ → ℂ) (hU : Continuous U) (hV : Continuous V) (R : ℝ)
    (hUs : ∀ s, R < |s| → U s = 0) :
    Integrable (fun x : H E n 0 => starRingEnd ℂ (ψ.1 x.1 * U (ldet x)) * (φ.1 x.1 * V (ldet x))) D.ν := by
  obtain ⟨Cψ, hCψ0, hCψ⟩ := bdd_of_mem hθ hψ R
  obtain ⟨Cφ, hCφ0, hCφ⟩ := bdd_of_mem hθ hφ R
  obtain ⟨KU, hKU⟩ := (isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn hU.continuousOn
  obtain ⟨KV, hKV⟩ := (isCompact_Icc : IsCompact (Icc (-R) R)).exists_bound_of_continuousOn hV.continuousOn
  have hc : Continuous fun x : H E n 0 => starRingEnd ℂ (ψ.1 x.1 * U (ldet x)) * (φ.1 x.1 * V (ldet x)) := by
    have h1 := (continuous_of_mem π hψ).comp (continuous_fst (X := GA E n) (Y := GA E 0))
    have h2 := (continuous_of_mem π hφ).comp (continuous_fst (X := GA E n) (Y := GA E 0))
    have hl := continuous_ldet (E := E) (n := n)
    exact (continuous_star.comp (h1.mul (hU.comp hl))).mul (h2.mul (hV.comp hl))
  refine integrable_of_ldet hn D _ hc R (Cψ * KU * (Cφ * KV)) (fun x hx => by simp [hUs _ hx]) fun x hx => ?_
  have hI : ldet x ∈ Icc (-R) R := abs_le.1 hx
  have hKU0 : 0 ≤ KU := (norm_nonneg _).trans (hKU _ hI)
  rw [norm_mul, RCLike.norm_conj, norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul (hCψ x hx) (hKU _ hI) (norm_nonneg _) hCψ0)
    (mul_le_mul (hCφ x hx) (hKV _ hI) (norm_nonneg _) hCφ0) (by positivity) (by positivity)

end DiscreteGroups.T1.G.Dcy

end
end
