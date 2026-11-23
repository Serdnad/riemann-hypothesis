module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import GroundTheory.AutomorphicForms.ReductionMahler
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle217
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Aesop.Main
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle396
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle234
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle391
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Finset
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle001

@[expose] public section

section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC

noncomputable section

namespace GlobalTheory.CompanionTheory.SplitHomeo

open GroundTheory.Automorphic GroundTheory.Global

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_splitCentre : Continuous (splitCentre E a) := by
  have e : splitCentre E a = fun t : ℝ =>
      Matrix.GeneralLinearGroup.scalar (Fin a) (infId E (expU fun _ : InfinitePlace E => (t : ℂ))) :=
    funext splitCentre_eq_scalar
  rw [e]
  refine Continuous.units_map _ ?_ |>.comp ((continuous_infId E).comp
    (continuous_expU.comp (continuous_pi fun _ => Complex.continuous_ofReal)))
  change Continuous fun x : Ad E => Matrix.diagonal fun _ : Fin a => x
  exact (continuous_pi fun _ => continuous_id).matrix_diagonal


variable (E) in
def expIdele (t : ℝ) : IdeleGroup E := infId E (expU fun _ : InfinitePlace E => (t : ℂ))

theorem pInf_expIdele (t : ℝ) (w : InfinitePlace E) :
    pInf E (expIdele E t : Ad E) w = Complex.exp t := by
  have h : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
  change pInf E (1 - sInf E 1 + sInf E _) w = _
  simp only [map_add (f := _), map_sub, map_one, h, sub_self, zero_add]
  rfl

theorem pFin_expIdele (t : ℝ) : pFin E (expIdele E t : Ad E) = 1 := by
  change (1 : Af E) - 0 + 0 = 1
  simp

theorem ideleModule_expIdele (t : ℝ) :
    (IdeleGroup.ideleModule E (expIdele E t) : ℝ) = Real.exp (Module.finrank ℚ E * t) := by
  have h1 : ∀ v : InfinitePlace E, ‖(expIdele E t : Ad E).1 v‖ = Real.exp t := fun v => by
    have := pInf_expIdele (E := E) t v
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _)]
    refine (congrArg norm this).trans ?_
    rw [Complex.norm_exp, Complex.ofReal_re]
  have h2 : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖(expIdele E t : Ad E).2 v‖ = 1 := fun v => by
    change ‖pFin E (expIdele E t : Ad E) v‖ = 1
    rw [pFin_expIdele]
    exact norm_one
  rw [IdeleGroup.ideleModule_eq]
  change (∏ v : InfinitePlace E, ‖(expIdele E t : Ad E).1 v‖ ^ v.mult) *
    ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), ‖(expIdele E t : Ad E).2 v‖ = _
  simp only [h1, h2, finprod_one, mul_one]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, ← Real.exp_nat_mul]

theorem det_splitCentre (t : ℝ) : AdelicGLn.det E a (splitCentre E a t) = expIdele E t ^ a := by
  rw [splitCentre_eq_scalar]
  refine Units.ext ?_
  change (Matrix.scalar (Fin a) (expIdele E t : Ad E)).det = _
  simp

theorem ideleModule_det_splitCentre (t : ℝ) :
    (IdeleGroup.ideleModule E (AdelicGLn.det E a (splitCentre E a t)) : ℝ) =
      Real.exp ((a * Module.finrank ℚ E : ℝ) * t) := by
  rw [det_splitCentre, map_pow, Positive.val_pow, ideleModule_expIdele, ← Real.exp_nat_mul]
  congr 1
  ring

def splitDeg (E : Type) [Field E] [NumberField E] (a : ℕ) (g : GA E a) : ℝ :=
  Real.log (IdeleGroup.ideleModule E (AdelicGLn.det E a g)) / (a * Module.finrank ℚ E : ℝ)

theorem continuous_splitDeg : Continuous (splitDeg E a) := by
  refine Continuous.div_const (Continuous.log ?_ fun g => ?_) _
  · exact continuous_subtype_val.comp
      (IdeleGroup.continuous_ideleModule.comp (AdelicGLn.continuous_det E a))
  · exact (IdeleGroup.ideleModule E (AdelicGLn.det E a g)).2.ne'

theorem coeff_ne_zero (ha : 0 < a) : (a * Module.finrank ℚ E : ℝ) ≠ 0 :=
  mul_ne_zero (Nat.cast_ne_zero.2 ha.ne') (Nat.cast_ne_zero.2 Module.finrank_pos.ne')

theorem splitCentre_neg_mul_mem (ha : 0 < a) (g : GA E a) :
    splitCentre E a (-splitDeg E a g) * g ∈ Reduction.normOneGL (K := E) (n := a) := by
  have hc := coeff_ne_zero (E := E) ha
  have hpos := (IdeleGroup.ideleModule E (AdelicGLn.det E a g)).2
  rw [Reduction.mem_normOneGL, map_mul, map_mul, Positive.val_mul, ideleModule_det_splitCentre,
    mul_neg, splitDeg, mul_div_cancel₀ _ hc, Real.exp_neg, Real.exp_log hpos, inv_mul_cancel₀ hpos.ne']

theorem splitDeg_splitCentre_mul (ha : 0 < a) (x : Reduction.normOneGL (K := E) (n := a)) (t : ℝ) :
    splitDeg E a (splitCentre E a t * (x : GA E a)) = t := by
  have hc := coeff_ne_zero (E := E) ha
  have hx : (IdeleGroup.ideleModule E (AdelicGLn.det E a (x : GA E a)) : ℝ) = 1 :=
    Reduction.mem_normOneGL.1 x.2
  rw [splitDeg, map_mul, map_mul, Positive.val_mul, ideleModule_det_splitCentre, hx, mul_one,
    Real.log_exp, mul_div_cancel_left₀ _ hc]

theorem splitCentre_neg_mul_self (t : ℝ) (g : GA E a) :
    splitCentre E a (-t) * (splitCentre E a t * g) = g := by
  rw [← mul_assoc, ← splitCentre_add, neg_add_cancel, splitCentre_zero, one_mul]

theorem exists_homeomorph (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (ha : 0 < a) :
    ∃ e : Reduction.normOneGL (K := E) (n := a) × ℝ ≃ₜ GA E a, ∀ x t, e (x, t) = splitCentre E a t * (x : GA E a) := by
  refine ⟨{
    toFun := fun p => splitCentre E a p.2 * (p.1 : GA E a)
    invFun := fun g => (⟨splitCentre E a (-splitDeg E a g) * g, splitCentre_neg_mul_mem ha g⟩, splitDeg E a g)
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }, fun _ _ => rfl⟩
  · rintro ⟨x, t⟩
    refine Prod.ext (Subtype.ext ?_) (splitDeg_splitCentre_mul ha x t)
    change splitCentre E a (-splitDeg E a (splitCentre E a t * (x : GA E a))) * _ = _
    rw [splitDeg_splitCentre_mul ha x t, splitCentre_neg_mul_self]
  · intro g
    change splitCentre E a (splitDeg E a g) * (splitCentre E a (-splitDeg E a g) * g) = g
    simpa using splitCentre_neg_mul_self (-splitDeg E a g) g
  · exact (continuous_splitCentre.comp continuous_snd).mul
      (continuous_subtype_val.comp continuous_fst)
  · refine Continuous.prodMk (Continuous.subtype_mk ?_ _) continuous_splitDeg
    exact (continuous_splitCentre.comp continuous_splitDeg.neg).mul continuous_id

end GlobalTheory.CompanionTheory.SplitHomeo
end
end

section

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.RCalc.ByParts

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem integral_deriv_eq_zero {Γ V : Type*} [TopologicalSpace Γ] [SecondCountableTopology Γ] [T2Space Γ]
    [MeasurableSpace Γ] [BorelSpace Γ] {μ : Measure Γ} [IsFiniteMeasureOnCompacts μ]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {F F' : ℝ → Γ → V} {K : Set Γ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) (C : ℝ)
    (hc : ∀ t ∈ Metric.ball (0 : ℝ) ε, Continuous (F t)) (hc' : Continuous (F' 0))
    (hd : ∀ y, ∀ t ∈ Metric.ball (0 : ℝ) ε, HasDerivAt (fun s => F s y) (F' t y) t)
    (hz : ∀ y, y ∉ K → F 0 y = 0)
    (hz' : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∀ y, y ∉ K → F' t y = 0)
    (hb : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∀ y ∈ K, ‖F' t y‖ ≤ C)
    (hconst : ∀ t ∈ Metric.ball (0 : ℝ) ε, ∫ y, F t y ∂μ = ∫ y, F 0 y ∂μ) :
    ∫ y, F' 0 y ∂μ = 0 := by
  have hs : Metric.ball (0 : ℝ) ε ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ hε
  have hm : ∀ᶠ t in 𝓝 (0 : ℝ), AEStronglyMeasurable (F t) μ :=
    eventually_of_mem hs fun t ht => (hc t ht).aestronglyMeasurable
  have hint : Integrable (F 0) μ :=
    (hc 0 (Metric.mem_ball_self hε)).integrable_of_hasCompactSupport (HasCompactSupport.intro hK hz)
  have hbi : Integrable (K.indicator fun _ => C) μ :=
    (integrable_indicator_iff hK.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne)
  have hbound : ∀ᵐ y ∂μ, ∀ t ∈ Metric.ball (0 : ℝ) ε, ‖F' t y‖ ≤ K.indicator (fun _ => C) y :=
    ae_of_all _ fun y t ht => by
      by_cases hy : y ∈ K
      · simpa [hy] using hb t ht y hy
      · simp [hy, hz' t ht y hy]
  have h1 := (hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hm hint hc'.aestronglyMeasurable hbound hbi
    (ae_of_all _ hd)).2
  have h2 : HasDerivAt (fun t => ∫ y, F t y ∂μ) 0 0 := by
    refine (hasDerivAt_const (0 : ℝ) (∫ y, F 0 y ∂μ)).congr_of_eventuallyEq ?_
    exact eventually_of_mem hs hconst
  exact h1.unique h2

theorem continuousOn_fderiv_apply {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [TopologicalSpace P] {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U)
    {S : Set P} {A B : P → E} (hA : ContinuousOn A S) (hB : ContinuousOn B S) (hm : MapsTo A S U) :
    ContinuousOn (fun p => fderiv ℝ f (A p) (B p)) S := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact (h1.continuousOn.comp hA hm).clm_apply hB

theorem hasDerivAt_line {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (g v : E) (t : ℝ) (hf : DifferentiableAt ℝ f (g + t • v)) :
    HasDerivAt (fun s : ℝ => f (g + s • v)) (fderiv ℝ f (g + t • v) v) t := by
  have h2 : HasDerivAt (fun s : ℝ => g + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add g
  exact hf.hasFDerivAt.comp_hasDerivAt t h2

variable {n : ℕ}

def c (X : Mat n) (t : ℝ) : Mat n := 1 + t • X

theorem continuous_c (X : Mat n) : Continuous (c X) :=
  continuous_const.add (continuous_id.smul continuous_const)

theorem c_zero (X : Mat n) : c X 0 = 1 := by simp [c]

theorem mul_c (y X : Mat n) (t : ℝ) : y * c X t = y + t • (y * X) := by
  simp [c, mul_add]

theorem exists_eps (X : Mat n) : ∃ ε > 0, ∀ t ∈ Metric.closedBall (0 : ℝ) ε, c X t ∈ GLs n := by
  have h : IsOpen (c X ⁻¹' GLs n) := isOpen_GLs.preimage (continuous_c X)
  have h0 : (0 : ℝ) ∈ c X ⁻¹' GLs n := by simp [c_zero, GLs]
  obtain ⟨ε, hε, h'⟩ := Metric.nhds_basis_closedBall.mem_iff.1 (h.mem_nhds h0)
  exact ⟨ε, hε, h'⟩

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem mul_mem_GLs' {x y : Mat n} (hx : x ∈ GLs n) (hy : y ∈ GLs n) : x * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hy

theorem inv_mem_GLs {x : Mat n} (hx : x ∈ GLs n) : x⁻¹ ∈ GLs n := by
  have h : x.det ≠ 0 := hx
  simp [GLs, Matrix.det_nonsing_inv, h]

def toG {x : Mat n} (hx : x ∈ GLs n) : G n := Matrix.GeneralLinearGroup.mkOfDetNeZero x hx

theorem secondCountable_G : SecondCountableTopology (G n) := by
  haveI : SecondCountableTopology (Mat n) := inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Mat n)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem lg_le_lg_mul (hL : LgFacts) (y : G n) {x : Mat n} (hx : x ∈ GLs n) : lg y.val ≤ lg (y.val * x) + lg x := by
  obtain ⟨hsub, hinv, -⟩ := hL n
  have hdet : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  have e : y.val = (y.val * x) * x⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
  calc lg y.val = lg ((y.val * x) * x⁻¹) := by rw [← e]
    _ ≤ lg (y.val * x) + lg x⁻¹ := hsub _ (mul_mem_GLs' (val_mem_GLs y) hx) _ (inv_mem_GLs hx)
    _ = lg (y.val * x) + lg x := by rw [hinv x hx]

theorem fderiv_eq_zero_far (hL : LgFacts) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V} {R : ℝ}
    (hR : ∀ y ∈ GLs n, R < lg y → f y = 0) {x : Mat n} (hx : x ∈ GLs n) (hlg : R < lg x) : fderiv ℝ f x = 0 := by
  obtain ⟨-, -, -, hsm, -⟩ := hL n
  have ho : IsOpen (GLs n ∩ lg ⁻¹' Ioi R) := hsm.continuousOn.isOpen_inter_preimage isOpen_GLs isOpen_Ioi
  have he : f =ᶠ[𝓝 x] fun _ => (0 : V) :=
    eventually_of_mem (ho.mem_nhds ⟨hx, hlg⟩) fun y hy => hR y hy.1 hy.2
  rw [he.fderiv_eq]
  simp

theorem ibp_of (hL : LgFacts) (hU : Unimod) : IBP := by
  intro n _ _ μ _ V _ _ _ f hf hC X
  obtain ⟨R, hR⟩ := hC
  obtain ⟨-, -, -, hsm, hcpt, -⟩ := hL n
  haveI := (hU n μ).1
  haveI : SecondCountableTopology (G n) := secondCountable_G
  obtain ⟨ε, hε, hcε⟩ := exists_eps X
  have hball : ∀ t ∈ Metric.ball (0 : ℝ) ε, c X t ∈ GLs n := fun t ht => hcε t (Metric.ball_subset_closedBall ht)
  have hmem : ∀ (y : G n), ∀ t ∈ Metric.closedBall (0 : ℝ) ε, y.val * c X t ∈ GLs n :=
    fun y t ht => mul_mem_GLs' (val_mem_GLs y) (hcε t ht)
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, ∀ t ∈ Metric.closedBall (0 : ℝ) ε, lg (c X t) ≤ C₀ := by
    have hcont : ContinuousOn (fun t => lg (c X t)) (Metric.closedBall (0 : ℝ) ε) :=
      hsm.continuousOn.comp (continuous_c X).continuousOn hcε
    obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : ℝ) ε).bddAbove_image hcont
    exact ⟨C₀, fun t ht => hC₀ (mem_image_of_mem _ ht)⟩
  set K : Set (G n) := {y : G n | lg y.val ≤ R + C₀} with hKdef
  have hK : IsCompact K := hcpt (R + C₀)
  have hfar : ∀ (y : G n), y ∉ K → ∀ t ∈ Metric.closedBall (0 : ℝ) ε, R < lg (y.val * c X t) := by
    intro y hy t ht
    have h1 : R + C₀ < lg y.val := not_le.1 hy
    have h2 := lg_le_lg_mul hL y (hcε t ht)
    have h3 := hC₀ t ht
    linarith
  have hvalc : Continuous fun y : G n => y.val := Units.continuous_val
  obtain ⟨C, hCb⟩ : ∃ C, ∀ p ∈ K ×ˢ Metric.closedBall (0 : ℝ) ε,
      ‖fderiv ℝ f (p.1.val * c X p.2) (p.1.val * X)‖ ≤ C := by
    have hcont : ContinuousOn (fun p : G n × ℝ => fderiv ℝ f (p.1.val * c X p.2) (p.1.val * X))
        (K ×ˢ Metric.closedBall (0 : ℝ) ε) := by
      refine continuousOn_fderiv_apply isOpen_GLs hf ?_ ?_ ?_
      · exact ((hvalc.comp continuous_fst).mul ((continuous_c X).comp continuous_snd)).continuousOn
      · exact ((hvalc.comp continuous_fst).mul continuous_const).continuousOn
      · exact fun p hp => hmem p.1 p.2 hp.2
    exact (hK.prod (isCompact_closedBall (0 : ℝ) ε)).exists_bound_of_continuousOn hcont
  have key := integral_deriv_eq_zero (μ := μ) (F := fun t (y : G n) => f (y.val * c X t))
    (F' := fun t (y : G n) => fderiv ℝ f (y.val * c X t) (y.val * X)) hK hε C ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simpa [c_zero, Rd] using key
  · intro t ht
    exact hf.continuousOn.comp_continuous (hvalc.mul continuous_const)
      fun y => hmem y t (Metric.ball_subset_closedBall ht)
  · refine continuousOn_univ.1 (continuousOn_fderiv_apply isOpen_GLs hf ?_ ?_ ?_)
    · exact (hvalc.mul continuous_const).continuousOn
    · exact (hvalc.mul continuous_const).continuousOn
    · exact fun y _ => hmem y 0 (Metric.mem_closedBall_self hε.le)
  · intro y t ht
    have hd : DifferentiableAt ℝ f (y.val + t • (y.val * X)) := by
      rw [← mul_c]
      exact differentiableAt_of_smooth hf (hmem y t (Metric.ball_subset_closedBall ht))
    have := hasDerivAt_line (y.val) (y.val * X) t hd
    have e1 : (fun s : ℝ => f (y.val * c X s)) = fun s : ℝ => f (y.val + s • (y.val * X)) := by
      funext s; rw [mul_c]
    show HasDerivAt (fun s : ℝ => f (y.val * c X s)) (fderiv ℝ f (y.val * c X t) (y.val * X)) t
    rw [e1, mul_c]
    exact this
  · intro y hy
    exact hR _ (hmem y 0 (Metric.mem_closedBall_self hε.le)) (hfar y hy 0 (Metric.mem_closedBall_self hε.le))
  · intro t ht y hy
    have ht' := Metric.ball_subset_closedBall ht
    simp only [fderiv_eq_zero_far hL hR (hmem y t ht') (hfar y hy t ht'), ContinuousLinearMap.zero_apply]
  · intro t ht y hy
    exact hCb (y, t) ⟨hy, Metric.ball_subset_closedBall ht⟩
  · intro t ht
    have h0 := integral_mul_right_eq_self (μ := μ) (fun y : G n => f y.val) (toG (hball t ht))
    simpa [toG, Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.GeneralLinearGroup.mk', Matrix.unitOfDetInvertible, c_zero] using h0

end GlobalTheory.CompanionTheory.RCalc.ByParts

theorem GlobalTheory.CompanionTheory.RCalc.ibp : GlobalTheory.CompanionTheory.RCalc.IBP :=
  GlobalTheory.CompanionTheory.RCalc.ByParts.ibp_of GlobalTheory.T.length_function_facts_hold GlobalTheory.T.general_linear_group_unimodular
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

theorem det_mul_eq_sum_mnr {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (M : Matrix ι (Fin n) R) (L : Matrix (Fin n) ι R) :
    (L * M).det = ∑ g : Fin n → ι, (∏ i, L i (g i)) * mnr M g := by
  have h1 : (L * M).det =
      (Matrix.detRowAlternating (R := R) (n := Fin n)).toMultilinearMap
        (fun i => ∑ j, L i j • M j) := by
    have : (L * M) = Matrix.of (fun i => ∑ j, L i j • M j) := by
      ext i k
      simp [Matrix.mul_apply, Finset.sum_apply]
    rw [this]
    rfl

  rw [h1, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [MultilinearMap.map_smul_univ]
  rfl

theorem exists_mnr_ne_zero_of_left_inverse :
    ∀ (R : Type) [CommRing R] [Nontrivial R] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ)
      (M : Matrix ι (Fin n) R) (L : Matrix (Fin n) ι R),
      L * M = 1 → ∃ f, mnr M f ≠ 0 := by
  intro R _ _ ι _ _ n M L h
  by_contra hc
  push_neg at hc
  have key := det_mul_eq_sum_mnr M L
  rw [h, Matrix.det_one] at key
  simp [hc] at key

end GlobalTheory.CompanionTheory.GodementH
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH

theorem absEv_mul_locFin_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Type) [Fintype J] (v : Pl (F := F)) (u : J → E) (δ : (Fv F v ⊗[F] E)ˣ) (z : J → Fv F v ⊗[F] E) (c : ℝ≥0),
    (∀ f, z f = ((1 : Fv F v) ⊗ₜ[F] u f) * δ.1) → (∀ f, absFin F v (z f) ≤ c) →
    GlobalTheory.Doubling.absEv F E v δ * locFin σ v u ≤ c ^ 2 := by
  intro F E _ _ _ _ _ σ hσ J _ v u δ z c hz hc
  have e2 : ∀ (τ : E →ₐ[F] FvBar F v) (w : Fv F v ⊗[F] E),
      finEmb F v τ (sigR (Fv F v) σ w) = finEmb F v (τ.comp σ) w := by
    intro τ w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [sigR]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  have hN := congrArg (fun y => absBar F v (finEmb F v (embBar F E v) y))
    (GlobalTheory.Doubling.algebraMap_norm_eq hσ (R := Fv F v) δ.1)
  simp only [map_mul, absBar_mul, e2, AlgHom.commutes, absBar_algebraMap] at hN
  have key : ∀ τ : E →ₐ[F] FvBar F v, absBar F v (finEmb F v τ δ.1) * supBar v τ u ≤ c := by
    intro τ
    unfold supBar
    rw [NNReal.mul_finset_sup]
    refine Finset.sup_le fun f _ => ?_
    refine le_trans (le_of_eq ?_) ((le_absFin F v τ (z f)).trans (hc f))
    rw [hz f, map_mul, absBar_mul, finEmb_tmul, map_one, one_mul, mul_comm]
  rw [GlobalTheory.Doubling.absEv_apply, hN]
  unfold locFin
  calc _ = (absBar F v (finEmb F v (embBar F E v) δ.1) * supBar v (embBar F E v) u) *
        (absBar F v (finEmb F v ((embBar F E v).comp σ) δ.1) * supBar v ((embBar F E v).comp σ) u) := by ring
    _ ≤ c * c := mul_le_mul' (key _) (key _)
    _ = c ^ 2 := (sq c).symm

end GlobalTheory.CompanionTheory.GodementH

end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH

theorem absEw_mul_locInf_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (J : Type) [Fintype J] (w : InfinitePlace F) (e : EmbOver E w)
    (u : J → E) (δ : (w.Completion ⊗[F] E)ˣ) (z : J → w.Completion ⊗[F] E) (c : ℝ≥0)
    (hz : ∀ f, z f = ((1 : w.Completion) ⊗ₜ[F] u f) * δ.1) (hc : ∀ f, ‖infEmb e (z f)‖₊ ≤ c) :
    GlobalTheory.Doubling.absEw F E w δ * locInf w u ≤ c ^ 2 := by
  classical
  have hnorm : ∀ (τ : EmbOver E w) (y : w.Completion ⊗[F] E), ‖infEmb τ y‖₊ = ‖infEmb e y‖₊ := by
    intro τ y
    rcases infEmb_eq_or_conj hσ e τ with h | h
    · rw [h]
    · rw [h, RingHom.comp_apply, RCLike.nnnorm_conj]
  have hterm : ∀ p : EmbOver E w × J, ‖infEmb e δ.1‖₊ * ‖p.1.1 (u p.2)‖₊ ≤ c := by
    rintro ⟨τ, f⟩
    have h1 : infEmb τ (z f) = τ.1 (u f) * infEmb τ δ.1 := by
      rw [hz f, map_mul, infEmb_tmul, map_one, one_mul]
    calc ‖infEmb e δ.1‖₊ * ‖τ.1 (u f)‖₊ = ‖infEmb τ δ.1‖₊ * ‖τ.1 (u f)‖₊ := by rw [hnorm τ]
      _ = ‖infEmb τ (z f)‖₊ := by rw [h1, nnnorm_mul, mul_comm]
      _ = ‖infEmb e (z f)‖₊ := hnorm τ _
      _ ≤ c := hc f
  have hsup : ‖infEmb e δ.1‖₊ * (Finset.univ.sup fun p : EmbOver E w × J => ‖p.1.1 (u p.2)‖₊) ≤ c := by
    rw [Finset.mul_sup₀]
    exact Finset.sup_le fun p _ => hterm p
  unfold locInf
  rw [GlobalTheory.Doubling.absEw_eq_sq hσ e, ← mul_pow]
  convert pow_le_pow_left' hsup 2
end GlobalTheory.CompanionTheory.GodementH

end
end
