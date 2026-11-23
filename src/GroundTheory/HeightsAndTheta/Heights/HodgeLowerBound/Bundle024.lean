module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle019
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle011
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle006
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle021
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle012
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle018
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle027
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle091
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB

@[expose] public section

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas)

namespace CuspWeightIntegrable

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem isOpen_blocks : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

def logRatio (A A' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (z : (Σ k, ι k) → ℂ) : ℝ := Real.log (A.h z) - Real.log (A'.h z)

theorem continuousAt_logRatio {A A' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A')
    {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContinuousAt (logRatio A A') z := by
  have hn := isOpen_blocks.mem_nhds hz
  exact ((hA.continuousOn.continuousAt hn).log (A.pos z hz).ne').sub
    ((hA'.continuousOn.continuousAt hn).log (A'.pos z hz).ne')


omit [∀ k, Fintype (ι k)] in
theorem logRatio_torusSmul {A A' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (ha : A.a = A'.a) (c : K → ℂ) (hc : ∀ k, c k ≠ 0)
    {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    logRatio A A' (torusSmul c z) = logRatio A A' z := by
  have hpos : 0 < ∏ k, ‖c k‖ ^ A.a k := Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.2 (hc k)) _
  have e : torusSmul c z = fun x => c x.1 * z x := rfl
  have h1 := A.smul c z hc
  have h2 := A'.smul c z hc
  rw [← ha] at h2
  unfold logRatio
  rw [e, h1, h2, Real.log_mul hpos.ne' (A.pos z hz).ne', Real.log_mul hpos.ne' (A'.pos z hz).ne']
  ring

variable {P : Ideal (MRing ι)} {d : ℕ}

def descend (M : CxModel P d) (v : ((Σ k, ι k) → ℂ) → ℝ) (x : M.Xc) : ℝ := v (M.surj x).choose


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem descend_proj (M : CxModel P d) {v : ((Σ k, ι k) → ℂ) → ℝ}
    (hv : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ z ∈ mcPts P, v (torusSmul c z) = v z)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : descend M v (M.proj z) = v z := by
  obtain ⟨hz', hpz⟩ := (M.surj (M.proj z)).choose_spec
  obtain ⟨c, hc, hzc⟩ := (M.fibre _ hz' z hz).1 hpz
  have h := hv c hc _ hz'
  rw [← hzc] at h
  exact h.symm

theorem continuousAt_of_holoOn {X : Type} [TopologicalSpace X] {A : FinHolAtlas d X} {U : Set X}
    {f : X → ℂ} (hf : A.HoloOn U f) {x : X} (hx : x ∈ U) : ContinuousAt f x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
    (hf j _ ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩).continuousAt
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x := h1.comp ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem continuous_descend (M : CxModel P d) {A A' : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A)
    (hA' : IsSmoothHerm A') (ha : A.a = A'.a) : Continuous (descend M (logRatio A A')) := by
  have hv : ∀ c : K → ℂ, (∀ k, c k ≠ 0) → ∀ z ∈ mcPts P,
      logRatio A A' (torusSmul c z) = logRatio A A' z := fun c hc z hz => logRatio_torusSmul ha c hc hz.1
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨U, hU, hxU, s, hs, hholo⟩ := M.sections x
  have hsc : ContinuousAt s x := continuousAt_pi.2 fun p => continuousAt_of_holoOn (hholo p) hxU
  have h : ContinuousAt (logRatio A A' ∘ s) x := (continuousAt_logRatio hA hA' (hs x hxU).1.1).comp hsc
  refine h.congr ?_
  filter_upwards [hU.mem_nhds hxU] with y hy
  have h' := descend_proj M hv (hs y hy).1
  rw [(hs y hy).2] at h'
  exact h'.symm

theorem upperSemicontinuous_ph {X : Type} [TopologicalSpace X] {A : FinHolAtlas d X}
    (B : GroundTheory.Heights₂.Heights.Regular.BoundedPshData A) : UpperSemicontinuous B.ph := by
  intro x
  obtain ⟨j, hj⟩ := B.cover x
  have hxs : x ∈ (B.chart j).source := B.mid_subset_source j (B.inner_subset_mid j hj)
  have hy : B.chart j x ∈ (B.chart j).target := (B.chart j).map_source hxs
  have hn := (B.chart j).open_target.mem_nhds hy
  have h1 : UpperSemicontinuousAt (fun y => B.q j y + B.ph ((B.chart j).symm y)) (B.chart j x) :=
    fun c hc => by
      have h := ((B.u_psh j).1 _ hy) c hc
      rwa [nhdsWithin_eq_nhds.2 hn] at h
  have h2 : UpperSemicontinuousAt (fun y => -B.q j y) (B.chart j x) :=
    ((B.q_smooth j).continuousOn.continuousAt hn).neg.upperSemicontinuousAt
  have h3 : UpperSemicontinuousAt (fun y => B.ph ((B.chart j).symm y)) (B.chart j x) := by
    have h := h1.add h2
    have e : (fun y => B.q j y + B.ph ((B.chart j).symm y) + -B.q j y) =
        fun y => B.ph ((B.chart j).symm y) := by
      funext y
      ring
    rwa [e] at h
  intro c hc
  have hc' : B.ph ((B.chart j).symm (B.chart j x)) < c := by rwa [(B.chart j).left_inv hxs]
  filter_upwards [((B.chart j).continuousAt hxs).eventually (h3 c hc'),
    (B.chart j).open_source.mem_nhds hxs] with y hy hys
  rwa [(B.chart j).left_inv hys] at hy

theorem continuousOn_ph {X : Type} [TopologicalSpace X] {A : FinHolAtlas d X}
    (R : GroundTheory.Heights₂.Heights.Regular.RegChartData A) : ContinuousOn R.ph R.Yo := by
  intro x hx
  obtain ⟨j, hj⟩ := R.cover x
  have hxs : x ∈ (R.chart j).source := R.mid_subset_source j (R.inner_subset_mid j hj)
  have h1 := (GroundTheory.Heights₂.Heights.Regular.contDiffAt_comp_symm_of_smoothOn (R.compat j) R.isOpen_Yo
    R.ph_smooth hx hxs).continuousAt
  have h2 : ContinuousAt ((R.ph ∘ (R.chart j).symm) ∘ R.chart j) x := h1.comp ((R.chart j).continuousAt hxs)
  refine (h2.congr ?_).continuousWithinAt
  filter_upwards [(R.chart j).open_source.mem_nhds hxs] with y hy
  simp [(R.chart j).left_inv hy]

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]


open Classical in
def uFn (X : ComponentSetting D O Lt) (x : X.M.Xc) : ℝ :=
  X.S'.B.ph x + descend X.M (logRatio X.S'.ref X.S.ref) x - X.S.R.Yo.piecewise X.S.R.ph (fun _ => 0) x

theorem ref_deg_eq (X : ComponentSetting D O Lt) : X.S'.ref.a = X.S.ref.a :=
  X.S'.ref_deg.trans X.S.ref_deg.symm


open Classical in
theorem measurable_uFn (X : ComponentSetting D O Lt) : @Measurable X.M.Xc ℝ (borel X.M.Xc) _ (uFn X) := by
  let _ : MeasurableSpace X.M.Xc := borel X.M.Xc
  have _ : BorelSpace X.M.Xc := ⟨rfl⟩
  refine ((upperSemicontinuous_ph X.S'.B).measurable.add
    (continuous_descend X.M X.S'.ref_smooth X.S.ref_smooth (ref_deg_eq X)).measurable).sub ?_
  exact ContinuousOn.measurable_piecewise (continuousOn_ph X.S.R) continuousOn_const
    X.S.R.isOpen_Yo.measurableSet


open Classical in
theorem uFn_bound (X : ComponentSetting D O Lt) :
    ∃ C C' : ℝ, ∀ x ∈ X.S.R.Yo, |uFn X x| ≤ C + C' * Real.log (X.S.R.r x) := by
  obtain ⟨CB, hCB⟩ := X.S'.B.bdd
  obtain ⟨CV, hCV⟩ := isCompact_univ.exists_bound_of_continuousOn
    (continuous_descend X.M X.S'.ref_smooth X.S.ref_smooth (ref_deg_eq X)).continuousOn
  refine ⟨CB + CV + |X.S.R.Cph|, |X.S.R.Clog|, fun x hx => ?_⟩
  have h1 := hCB x
  have h2 : |descend X.M (logRatio X.S'.ref X.S.ref) x| ≤ CV := by
    simpa [Real.norm_eq_abs] using hCV x (Set.mem_univ x)
  have hr : 0 ≤ Real.log (X.S.R.r x) := Real.log_nonneg (X.S.R.one_le_r x hx)
  have h3 := X.S.R.ph_le x hx
  have h4 : -(X.S.R.Clog * Real.log (X.S.R.r x)) ≤ X.S.R.ph x := by
    rw [← neg_mul]
    exact X.S.R.ph_ge x hx
  have h5 : X.S.R.Clog * Real.log (X.S.R.r x) ≤ |X.S.R.Clog| * Real.log (X.S.R.r x) :=
    mul_le_mul_of_nonneg_right (le_abs_self _) hr
  have h6 : 0 ≤ |X.S.R.Clog| * Real.log (X.S.R.r x) := mul_nonneg (abs_nonneg _) hr
  have h7 := le_abs_self X.S.R.Cph
  have h8 := abs_nonneg X.S.R.Cph
  have hu : uFn X x = X.S'.B.ph x + descend X.M (logRatio X.S'.ref X.S.ref) x - X.S.R.ph x := by
    simp [uFn, Set.piecewise_eq_of_mem _ _ _ hx]
  rw [hu]
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]


open Classical in
theorem cuspWeight_eq (X : ComponentSetting D O Lt) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y))
    (hzb : z ∉ D.Bd) (hY : X.M.proj z ∈ X.S.R.Yo) : X.Cd.cuspWeight z / 2 = uFn X (X.M.proj z) := by
  have hXo : z ∈ D.Xo ∩ mcPts (mCoordIdeal D.y) := ⟨⟨hz, hzb⟩, hz⟩
  have h1 := X.S'.ph_eq z hXo
  have h2 := X.S.ph_eq z hXo hY
  have h3 := descend_proj X.M (fun c hc z hz => logRatio_torusSmul (ref_deg_eq X) c hc hz.1) hz
  have hu : uFn X (X.M.proj z) = X.S'.B.ph (X.M.proj z) +
      descend X.M (logRatio X.S'.ref X.S.ref) (X.M.proj z) - X.S.R.ph (X.M.proj z) := by
    simp [uFn, Set.piecewise_eq_of_mem _ _ _ hY]
  rw [hu, h1, h2, h3]
  simp only [cuspCorr, logRatio, phMu]
  ring

end CuspWeightIntegrable

theorem TpCuspIntegrable.proof (hM : ModelLogIntegrable.Statement) (hBd : BoundaryNull.Statement) :
    TpCuspIntegrable.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q t hsm
  obtain ⟨C, C', hb⟩ := CuspWeightIntegrable.uFn_bound X
  have hω : X.omN B p q t = fun _ z => (q : ℝ)⁻¹ * Real.log ((X.NbarQ B p q t).h z) := by
    funext _ z
    simp [ComponentSetting.omN, div_eq_inv_mul]
  rw [hω]
  exact hM K ι (mCoordIdeal D.y) D.n X.M X.S.R (X.NbarQ B p q t) (q : ℝ)⁻¹ D.Bd (CuspWeightIntegrable.uFn X) C C'
    _ D.arith hsm (hBd II Ψ K ι Ω E D) (CuspWeightIntegrable.measurable_uFn X) hb
    (fun z hz hzb hY => CuspWeightIntegrable.cuspWeight_eq X hz hzb hY)

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace TopNPoly

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem orbitRep_orbitRep (z : (Σ k, ι k) → ℂ) : orbitRep (orbitRep z) = orbitRep z := by
  simp only [orbitRep, Quotient.out_eq]

theorem orbitRep_blocks {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, orbitRep z ⟨k, i⟩ ≠ 0 := by
  obtain ⟨c, -, hzc⟩ := exists_eq_smul_orbitRep z
  intro k
  obtain ⟨i, hi⟩ := hz k
  refine ⟨i, fun h => hi ?_⟩
  rw [hzc]
  simp [torusSmul, h]

theorem hermOfFun_h_orbitRep {a : K → ℤ} {F : ((Σ k, ι k) → ℂ) → ℝ} {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (hF : 0 < F (orbitRep z)) :
    (hermOfFun ι a F).h (orbitRep z) = F (orbitRep z) := by
  have hR := refNorm_pos a (orbitRep_blocks hz)
  simp only [hermOfFun]
  rw [orbitRep_orbitRep, Real.exp_log (div_pos hF hR), mul_div_cancel₀ _ hR.ne']

theorem hermOfFun_h_smul {a : K → ℤ} {F : ((Σ k, ι k) → ℂ) → ℝ} {z : (Σ k, ι k) → ℂ} {c : K → ℂ}
    (hc : ∀ k, c k ≠ 0) (hzc : z = torusSmul c (orbitRep z)) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (hF : 0 < F (orbitRep z)) :
    (hermOfFun ι a F).h z = (∏ k, ‖c k‖ ^ a k) * F (orbitRep z) := by
  have h1 := hermOfFun_h_orbitRep (a := a) hz hF
  conv_lhs => rw [hzc]
  exact ((hermOfFun ι a F).smul c (orbitRep z) hc).trans (by rw [h1]; rfl)

theorem prod_norm_zpow_add {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (a b : K → ℤ) (q : ℕ) :
    (∏ k, ‖c k‖ ^ ((q : ℤ) • a + ((1 : ℕ) : ℤ) • b) k) = (∏ k, ‖c k‖ ^ a k) ^ q * ∏ k, ‖c k‖ ^ b k := by
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  have h0 : ‖c k‖ ≠ 0 := norm_ne_zero_iff.mpr (hc k)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Nat.cast_one, one_mul]
  rw [zpow_add₀ h0, show (q : ℤ) * a k = a k * q by ring, zpow_mul, zpow_natCast]

theorem smoothRep_smooth_of {P : Ideal (MRing ι)} {A Z : _root_.ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (ha : Z.a = A.a) (hZ : IsSmoothHerm Z)
    (hh : ∀ z ∈ mcPts P, Z.h z = A.h z) : IsSmoothHerm (smoothRep P A) := by
  classical
  unfold smoothRep
  split_ifs with h
  · exact h.choose_spec.2.1
  · exact absurd ⟨Z, ha, hZ, hh⟩ h

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E} {O Lt : Type} [CommRing O] [AddCommGroup Lt] [Module O Lt]


omit [DecidableEq Ψ] in
theorem NbarQ_h_eq (hV : VertFactorPos.Statement) (X : ComponentSetting D O Lt) (B q : ℕ) (t : ℝ)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    (X.NbarQ B 1 q t).h z = (muReg X.H X.S B t).h z ^ q * D.A'.h z := by
  obtain ⟨c, hc, hzc⟩ := exists_eq_smul_orbitRep z
  have hz0 := hz.1
  have hw0 := orbitRep_blocks hz0
  have hwP : orbitRep z ∈ mcPts (mCoordIdeal D.y) := by
    have h := mcPts_smul D.arith.2.1.2.1 (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k)) hz
    convert h using 1
    funext p
    have hp : z p = c p.1 * orbitRep z p := congrFun hzc p
    rw [hp, ← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]
  have hvf : 0 < ∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z) :=
    Finset.prod_pos fun p' hp' => hV II Ψ K ι Ω E D p' (Finset.mem_filter.1 hp').1 _ hwP
  have hG0 : 0 < X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    mul_pos (X.S.ref.pos _ hw0) (Real.exp_pos _)
  have hreg : (X.S.regLine t).h (orbitRep z) =
      X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z))) :=
    hermOfFun_h_orbitRep hz0 hG0
  have hM : (muReg X.H X.S B t).h z = (∏ k, ‖c k‖ ^ muTwDeg X.H B k) *
      ((X.S.regLine t).h (orbitRep z) * ∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z)) := by
    unfold muReg
    rw [smoothRep_h _ hz]
    exact hermOfFun_h_smul hc hzc hz0 (by rw [hreg]; exact mul_pos hG0 hvf)
  have hN : (X.NbarQ B 1 q t).h z = (∏ k, ‖c k‖ ^ ((q : ℤ) • muTwDeg X.H B + ((1 : ℕ) : ℤ) • D.a') k) *
      ((X.S.ref.h (orbitRep z) * Real.exp (X.S.regWeight t (X.M.proj (orbitRep z)))) ^ q *
        (∏ p' ∈ D.SB B, D.vertFactor p' (orbitRep z)) ^ q * D.A'.h (orbitRep z) ^ 1) := by
    unfold ComponentSetting.NbarQ
    rw [smoothRep_h _ hz]
    exact hermOfFun_h_smul hc hzc hz0
      (mul_pos (mul_pos (pow_pos hG0 _) (pow_pos hvf _)) (pow_pos (D.A'.pos _ hw0) _))
  have hA : D.A'.h z = (∏ k, ‖c k‖ ^ D.a' k) * D.A'.h (orbitRep z) := by
    conv_lhs => rw [hzc]
    exact (D.A'.smul c (orbitRep z) hc).trans (by rw [D.A'_deg])
  rw [hN, hM, hA, hreg, prod_norm_zpow_add hc]
  ring

end TopNPoly


open TopNPoly in
theorem TopNPoly.proof (hIso : HilbertSamuel.IsomInvariance.Statement) (hV : VertFactorPos.Statement)
    (hS : MuRegSmooth.Statement) : TopNPoly.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B hII _
  have hP : IsArithVar (mCoordIdeal D.y) (D.n + 1) := D.arith
  have hA : IsSmoothHerm D.A' := D.A'_pos.1
  refine ⟨fun i t => if i = 0 then arLimFun X.H X.S B t else ((D.n + 1).choose i : ℝ) *
      II K ι (mCoordIdeal D.y) (D.n + 1)
        (fun j : Fin (D.n + 1) => if (j : ℕ) < D.n + 1 - i then muReg X.H X.S B t else D.A'),
    by funext t; simp, fun q hq => ?_⟩
  filter_upwards [hS II Ψ K ι Ω E D O Lt X B] with t ht
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set Z := HilbertSamuel.HermLine.zcomb (muReg X.H X.S B t) D.A' (q : ℤ) ((1 : ℕ) : ℤ) with hZdef
  have hZ : IsSmoothHerm Z := HilbertSamuel.ZCombLimit.isSmoothHerm_zcomb_int ht hA _ _
  have hagree : ∀ z ∈ mcPts (mCoordIdeal D.y), Z.h z = (X.NbarQ B 1 q t).h z := by
    intro z hz
    rw [NbarQ_h_eq hV X B q t hz]
    show (muReg X.H X.S B t).h z ^ (q : ℤ) * D.A'.h z ^ ((1 : ℕ) : ℤ) = _
    simp
  have hdeg : Z.a = (X.NbarQ B 1 q t).a := by
    unfold ComponentSetting.NbarQ
    rw [smoothRep_a]
    show (q : ℤ) • (muReg X.H X.S B t).a + ((1 : ℕ) : ℤ) • D.A'.a = _
    rw [muReg, smoothRep_a, D.A'_deg]
    rfl
  have hN : IsSmoothHerm (X.NbarQ B 1 q t) := by
    unfold ComponentSetting.NbarQ
    refine smoothRep_smooth_of (Z := Z) ?_ hZ fun z hz => ?_
    · rw [hdeg]; unfold ComponentSetting.NbarQ; rw [smoothRep_a]
    · rw [hagree z hz]; unfold ComponentSetting.NbarQ; rw [smoothRep_h _ hz]
  have hne : (1 : MRing ι) ∉ mCoordIdeal D.y := fun h =>
    hP.2.1.1.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hiso : ∀ j : Fin (D.n + 1), HilbertSamuel.IsIsometricOn (mCoordIdeal D.y)
      ((fun _ => X.NbarQ B 1 q t) j) ((fun _ => Z) j) := fun _ =>
    ⟨1, 1, 0, 0, by simpa using isMultiHomog_C_zero (ι := ι) 1, by simpa using isMultiHomog_C_zero (ι := ι) 1,
      hne, hne, fun k => by simp [hdeg], rfl, fun z hz => by simp [hagree z hz]⟩
  have hI := hIso K ι (II K ι) (hII K ι) (mCoordIdeal D.y) (D.n + 1) (fun _ => X.NbarQ B 1 q t) (fun _ => Z) hP
    (fun _ => hN) (fun _ => hZ) hiso
  have hE := (HilbertSamuel.ZCombExpand.proof K ι (II K ι) (hII K ι) (mCoordIdeal D.y) (D.n + 1)
    (muReg X.H X.S B t) D.A' q 1 hP ht hA).1
  show II K ι (mCoordIdeal D.y) (D.n + 1) (fun _ => X.NbarQ B 1 q t) / (q : ℝ) ^ (D.n + 1) = _
  rw [hI, hE, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ D.n + 1 := by simp at hi; omega
  have hpow : (q : ℝ) ^ (D.n + 1) = (q : ℝ) ^ (D.n + 1 - i) * (q : ℝ) ^ i := by
    rw [← pow_add, Nat.sub_add_cancel hi']
  split_ifs with h0
  · subst h0
    have hall : (fun j : Fin (D.n + 1) => if (j : ℕ) < D.n + 1 - 0 then muReg X.H X.S B t else D.A') =
        fun _ => muReg X.H X.S B t := by
      funext j; simp [j.isLt]
    rw [hall]
    simp only [arLimFun, Nat.choose_zero_right, Nat.cast_one, mul_one, one_mul, Nat.sub_zero, pow_zero]
    field_simp
  · rw [hpow, Nat.cast_one, one_pow, mul_one, one_div, inv_pow]
    field_simp

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end
