module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle089
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle080
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle082
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle013
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle086
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PHFlProdLinear
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle010
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle090
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle047
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle061
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Weights
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle087
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle013
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle006

@[expose] public section

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize

theorem continuousAt_of_chart {X E F : Type*} [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace F]
    (c : OpenPartialHomeomorph X E) {f : X → F} {x : X} (hx : x ∈ c.source)
    (h : ContinuousAt (f ∘ c.symm) (c x)) : ContinuousAt f x := by
  have h1 : ContinuousAt ((f ∘ c.symm) ∘ c) x := ContinuousAt.comp h (c.continuousAt hx)
  refine h1.congr ?_
  filter_upwards [c.open_source.mem_nhds hx] with z hz
  simp [c.left_inv hz]

theorem holoOn_continuousAt {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X) {W : Set X}
    {g : X → ℂ} (h : A.HoloOn W g) {x : X} (hx : x ∈ W) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  refine continuousAt_of_chart (A.chart j) hj ?_
  have hm : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  exact (h j _ hm).continuousAt

theorem smoothOn_continuousAt {e : ℕ} {X : Type*} [TopologicalSpace X] (A : FinHolAtlas e X) {W : Set X}
    (hW : IsOpen W) {g : X → ℝ} (h : A.SmoothOn W g) {x : X} (hx : x ∈ W) : ContinuousAt g x := by
  obtain ⟨j, hj⟩ := A.cover x
  refine continuousAt_of_chart (A.chart j) hj ?_
  have hm : (A.chart j) x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' W :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  have ho : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) :=
    (A.chart j).isOpen_inter_preimage_symm hW
  exact ((h j).continuousOn).continuousAt (ho.mem_nhds hm)

variable {N : ℕ}

theorem gram_cmp {k : ℕ} (hk : k ≤ N) {G : Matrix (Fin N) (Fin N) ℂ} (V : Matrix (Fin N) (Fin k) ℂ) {m : ℝ}
    (hm : 1 ≤ m) (hG : G.PosDef) (h1 : ((m : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef)
    (h2 : ((m : ℂ) • G - 1).PosSemidef) (hV : LinearIndependent ℂ Vᵀ) :
    |Real.log (Vᴴ * G * V).det.re - Real.log (Vᴴ * (1 : Matrix (Fin N) (Fin N) ℂ) * V).det.re| ≤ N * Real.log m := by
  refine (GlobalTheory.T.log_det_comparable_gram_bound N k G 1 V m hm Matrix.PosDef.one hG h1 h2 hV).trans ?_
  have : (k : ℝ) ≤ N := by exact_mod_cast hk
  exact mul_le_mul_of_nonneg_right this (Real.log_nonneg hm)

theorem card_le (S : Finset (Fin N)) : S.card ≤ N := by
  simpa using S.card_le_univ

theorem blockPot_sub_le (j : ℕ) (i : Fin N) {G h : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) (hd : h.det ≠ 0)
    {m : ℝ} (hm : 1 ≤ m) (h1 : ((m : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef)
    (h2 : ((m : ℂ) • G - 1).PosSemidef) :
    |blockPot j i G h - blockPot j i 1 h| ≤ (3 / 2) * N * Real.log m := by
  obtain ⟨hS, hHS, hP⟩ := GramPot.blockPot_eq_gram N j i G h
  obtain ⟨-, -, hP1⟩ := GramPot.blockPot_eq_gram N j i 1 h
  have e1 := hP hG
  have e2 := hP1 Matrix.PosDef.one
  have tW := abs_le.1 (gram_cmp (card_le (wIdx N j)) (selM (wIdx N j)) hm hG h1 h2 (hS _))
  have tO := abs_le.1 (gram_cmp (card_le (omIdx N j)) (selM (omIdx N j)) hm hG h1 h2 (hS _))
  have tH := abs_le.1 (gram_cmp (card_le (stepCols N j i)) (h * selM (stepCols N j i)) hm hG h1 h2 (hHS hd _))
  have hl : 0 ≤ (N : ℝ) * Real.log m := mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hm)
  rw [e1, e2, abs_le]
  split_ifs <;> constructor <;> linarith [tW.1, tW.2, tO.1, tO.2, tH.1, tH.2]

theorem size_abs {G : Matrix (Fin N) (Fin N) ℂ} {r c : ℝ} (hr : 1 ≤ r) (hG : G.PosDef)
    (h : (((r ^ c : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef ∧
      (((r ^ c : ℝ) : ℂ) • G - 1).PosSemidef) :
    (((r ^ |c| : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - G).PosSemidef ∧
      (((r ^ |c| : ℝ) : ℂ) • G - 1).PosSemidef := by
  have hd : (0 : ℝ) ≤ r ^ |c| - r ^ c := sub_nonneg.2 (Real.rpow_le_rpow_of_exponent_le hr (le_abs_self c))
  have hd' : (0 : ℂ) ≤ ((r ^ |c| - r ^ c : ℝ) : ℂ) := by exact_mod_cast hd
  constructor
  · have := h.1.add (Matrix.PosSemidef.one.smul hd')
    convert this using 1
    push_cast
    module
  · have := h.2.add (hG.posSemidef.smul hd')
    convert this using 1
    push_cast
    module

theorem gram_one_pos {h : Matrix (Fin N) (Fin N) ℂ} (hd : h.det ≠ 0) (S : Finset (Fin N)) :
    0 < (minorIJ (hᴴ * 1 * h) S S).re := by
  have hu : IsUnit h := (Matrix.isUnit_iff_isUnit_det h).2 hd.isUnit
  have hp : (hᴴ * 1 * h).PosDef :=
    Matrix.PosDef.one.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
  exact (Complex.lt_def.1 (GramPot.minor_pos hp S)).1

theorem continuous_gram (S : Finset (Fin N)) :
    Continuous fun h : Matrix (Fin N) (Fin N) ℂ => (minorIJ (hᴴ * 1 * h) S S).re := by
  simp only [minorIJ, dif_pos]
  refine Complex.continuous_re.comp (Continuous.matrix_det ?_)
  refine Continuous.matrix_submatrix ?_ _ _
  fun_prop

theorem continuousAt_blockPot_one {X : Type*} [TopologicalSpace X] (j : ℕ) (i : Fin N)
    {H : X → Matrix (Fin N) (Fin N) ℂ} {x : X} (hH : ∀ a b, ContinuousAt (fun y => H y a b) x)
    (hd : (H x).det ≠ 0) : ContinuousAt (fun y => blockPot j i 1 (H y)) x := by
  have hc : ContinuousAt H x :=
    continuousAt_pi.2 fun a => continuousAt_pi.2 fun b => hH a b
  unfold blockPot
  refine continuousAt_const.add ?_
  split_ifs
  · refine continuousAt_const.mul (ContinuousAt.log ((continuous_gram _).continuousAt.comp hc) ?_)
    exact (gram_one_pos hd _).ne'
  · exact continuousAt_const

theorem stepPh_le_log : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (Kk : Type) [Fintype Kk] (ιk : Kk → Type) [∀ k, Fintype (ιk k)] (κ : Kk → K) (v : (Σ k, ιk k) → (Σ k, ι k)) (e : ℕ) (R : AnLogRes (mCoordIdeal (y ∘ v)) ⊤ e) (pr : R.X → BM.Rb.X) (hp : HoloMap R.A BM.Rb.A pr), HasStepCharts M BM p κ v R pr → IsPotential R.A (potOf R (fsHerm ιk fun k => M.dy p (κ k))) → ∃ C₁ : ℝ, ∀ x ∉ bdry (fun x y => BM.s (pr x) (pr y)), |stepPh M BM p v R pr x| ≤ C₁ * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p Kk _ ιk _ κ v e R pr hp hch hpot
  have hr : ∀ x, Real.exp 1 ≤ rW BM.L BM.s x := fun x => by
    have := BM.norm_le x
    simp only [rW]
    linarith
  have hrpos : ∀ x, 0 < rW BM.L BM.s x := fun x => (Real.exp_pos 1).trans_le (hr x)
  have hr1 : ∀ x, 1 ≤ rW BM.L BM.s x := fun x =>
    (by linarith [Real.add_one_le_exp (1 : ℝ)] : (1 : ℝ) ≤ Real.exp 1).trans (hr x)
  have hlog : ∀ x, 1 ≤ Real.log (rW BM.L BM.s x) := fun x =>
    (Real.le_log_iff_exp_le (hrpos x)).2 (hr x)
  have key : ∀ y₀ : R.X, ∃ t ∈ 𝓝 y₀, ∃ C : ℝ, ∀ x ∈ t, x ∉ bdry (fun x y => BM.s (pr x) (pr y)) →
      |stepPh M BM p v R pr x| ≤ C * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := by
    intro y₀
    obtain ⟨W, l, H, D, hW, hy₀, -, hO, hH, hHd, hD, hDne, heq⟩ := hch y₀ y₀ (R.mem_U y₀)
    let u : R.X → ℝ := fun y' => blockPot j p.2 1 (H y') + Real.log ‖D y'‖ -
      Real.log ((fsHerm ιk fun k => M.dy p (κ k)).h (R.lift y₀ y'))
    have hu : ContinuousAt u y₀ := by
      refine ((continuousAt_blockPot_one j p.2 (fun a b => holoOn_continuousAt R.A (hH a b) hy₀)
        (hHd y₀ hy₀).2).add ?_).sub ?_
      · exact ContinuousAt.log (holoOn_continuousAt R.A hD hy₀).norm (norm_ne_zero_iff.2 (hDne y₀ hy₀))
      · exact smoothOn_continuousAt R.A (R.isOpen_U y₀) (hpot.1 y₀) (R.mem_U y₀)
    refine ⟨W ∩ {y' | |u y'| < |u y₀| + 1}, inter_mem (hW.mem_nhds hy₀)
      (hu.abs.eventually_lt continuousAt_const (lt_add_one _)), (3 / 2) * N * |BM.Cst| + (|u y₀| + 1), ?_⟩
    rintro y' ⟨hy'W, hy'u⟩ hb
    have hb' : pr y' ∉ bdry BM.s := hb
    have hmem : pr y' ∈ BM.O l \ bdry BM.s := ⟨hO y' hy'W, hb'⟩
    obtain ⟨-, hpd⟩ := BM.G_pos l p.1 _ hmem
    have hs := size_abs (hr1 (pr y')) hpd (BM.size l p.1 _ hmem)
    have hm1 : 1 ≤ rW BM.L BM.s (pr y') ^ |BM.Cst| := Real.one_le_rpow (hr1 _) (abs_nonneg _)
    have hdiff := blockPot_sub_le j p.2 hpd (hHd y' hy'W).2 hm1 hs.1 hs.2
    rw [Real.log_rpow (hrpos _)] at hdiff
    have e' := heq y' hy'W hb'
    have hL := hlog (pr y')
    have hsum : stepPh M BM p v R pr y' = (blockPot j p.2 (BM.G l p.1 (pr y')) (H y') - blockPot j p.2 1 (H y')) + u y' := by
      simp only [u]
      linarith
    change |stepPh M BM p v R pr y'| ≤ _ * Real.log (rW BM.L BM.s (pr y'))
    rw [hsum]
    have hu' : |u y'| < |u y₀| + 1 := hy'u
    have hc : |u y₀| + 1 ≤ (|u y₀| + 1) * Real.log (rW BM.L BM.s (pr y')) :=
      le_mul_of_one_le_right (by positivity) hL
    calc _ ≤ |blockPot j p.2 (BM.G l p.1 (pr y')) (H y') - blockPot j p.2 1 (H y')| + |u y'| := abs_add_le _ _
      _ ≤ (3 / 2) * N * (|BM.Cst| * Real.log (rW BM.L BM.s (pr y'))) + (|u y₀| + 1) * Real.log (rW BM.L BM.s (pr y')) := by
        linarith
      _ = _ := by ring
  have hlogr : ∀ x, 0 ≤ Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x) := fun x =>
    zero_le_one.trans (hlog (pr x))
  obtain ⟨C, hC⟩ := (isCompact_univ (X := R.X)).induction_on
    (p := fun S => ∃ C : ℝ, ∀ x ∈ S, x ∉ bdry (fun x y => BM.s (pr x) (pr y)) →
      |stepPh M BM p v R pr x| ≤ C * Real.log (rW (BM.L.pullback pr hp.1) (fun x y => BM.s (pr x) (pr y)) x))
    ⟨0, fun x hx => absurd hx (Set.notMem_empty x)⟩
    (fun s t hst ⟨C, hC⟩ => ⟨C, fun x hx => hC x (hst hx)⟩)
    (fun s t ⟨C, hC⟩ ⟨C', hC'⟩ => ⟨max C C', fun x hx hb => hx.elim
      (fun h => (hC x h hb).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlogr x)))
      (fun h => (hC' x h hb).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (hlogr x)))⟩)
    (fun y₀ _ => by
      obtain ⟨t, ht, C, hC⟩ := key y₀
      exact ⟨t, mem_nhdsWithin_of_mem_nhds ht, C, hC⟩)
  exact ⟨C, fun x hb => hC x (Set.mem_univ x) hb⟩

end GlobalTheory.CompanionTheory.Ar.PB.StepW.WeightSize
end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def coneOver {A : Type} [CommRing A] (Y : (Σ k, ι k) → A) : MRing ι →ₐ[ℤ] MvPolynomial K A :=
  aeval fun p => C (Y p) * X p.1

def scaleBy {F : Type} [Field F] (c : K → F) : MvPolynomial K F →ₐ[F] MvPolynomial K F :=
  aeval fun k => C (c k) * X k

omit [Fintype K] in
theorem scaleBy_injective {F : Type} [Field F] (c : K → F) (hc : ∀ k, c k ≠ 0) :
    Function.Injective (scaleBy c) := by
  have h : (scaleBy fun k => (c k)⁻¹).comp (scaleBy c) = AlgHom.id F _ := by
    apply MvPolynomial.algHom_ext
    intro k
    simp only [scaleBy, AlgHom.comp_apply, aeval_X, map_mul, algHom_C, AlgHom.id_apply]
    rw [← mul_assoc, algebraMap_eq, ← C_mul, mul_inv_cancel₀ (hc k), C_1, one_mul]
  exact Function.LeftInverse.injective (g := scaleBy fun k => (c k)⁻¹) fun f => DFunLike.congr_fun h f

theorem mConeMap_eq {A F : Type} [CommRing A] [Field F] (f : A →+* F) (Y : (Σ k, ι k) → A) (z : (Σ k, ι k) → F)
    (c : K → F) (hz : ∀ q, z q = c q.1 * f (Y q)) (p : MRing ι) :
    mConeMap z p = scaleBy c (MvPolynomial.map f (coneOver Y p)) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [mConeMap, coneOver]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p q hp =>
    rw [map_mul, map_mul, map_mul, map_mul, hp]
    congr 1
    simp only [mConeMap, coneOver, aeval_X, scaleBy, map_mul, map_C, map_X, algHom_C, algebraMap_eq, hz q]
    ring

theorem mCoordIdeal_eq {A F : Type} [CommRing A] [Field F] (f : A →+* F) (hf : Function.Injective f)
    (Y : (Σ k, ι k) → A) (z : (Σ k, ι k) → F) (c : K → F) (hc : ∀ k, c k ≠ 0)
    (hz : ∀ q, z q = c q.1 * f (Y q)) : mCoordIdeal z = RingHom.ker (coneOver Y) := by
  ext p
  rw [mCoordIdeal, RingHom.mem_ker, RingHom.mem_ker, mConeMap_eq f Y z c hz]
  constructor
  · intro h
    have h1 : MvPolynomial.map f (coneOver Y p) = 0 := scaleBy_injective c hc (by rw [h, map_zero])
    exact MvPolynomial.map_injective f hf (by rw [h1, map_zero])
  · intro h
    rw [h, map_zero, map_zero]

theorem map_minorIJ {R S : Type} [CommRing R] [CommRing S] {N : ℕ} (f : R →+* S) (h : Matrix (Fin N) (Fin N) R)
    (I J : Finset (Fin N)) : f (minorIJ h I J) = minorIJ (h.map f) I J := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]
    rfl
  · exact map_zero f

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} {N j : ℕ}

def polyPt (M : FlagModel y Ψ N j) : (Σ k, ι k) → MvPolynomial (LowIdx Ψ N j) M.Ω := fun q =>
  if h : ∀ p, M.blk p ≠ some q.1 then C (M.x ⟨⟨q.1, h⟩, q.2⟩)
  else ∑ I, C (M.coef q I) * minorIJ (genLow M.Ω N j (stepOf M q.1 h).1) I (stepCols N j (stepOf M q.1 h).2)

theorem exists_scale (M : FlagModel y Ψ N j) {F : Type} [Field F] (f : MvPolynomial (LowIdx Ψ N j) M.Ω →+* F)
    (ψ : M.Ω →+* F) (hfC : ∀ a, f (C a) = ψ a) (G B : Ψ → Matrix (Fin N) (Fin N) F)
    (hG : ∀ τ, IsBlockDiag j (G τ))
    (hB : ∀ τ, IsBlockDiag j (B τ) ∧ (B τ).BlockTriangular id ∧ IsLowerUni (G τ * B τ))
    (hf : ∀ q : LowIdx Ψ N j, f (X q) = (G q.1.1 * B q.1.1) q.1.2.1 q.1.2.2)
    (z : (Σ k, ι k) → F)
    (hbase : ∀ q : Σ k, baseIdx ι M.blk k, z ⟨q.1.1, q.2⟩ = ψ (M.x q))
    (hstep : ∀ p k, M.blk p = some k → ∀ m : ι k,
      z ⟨k, m⟩ = ∑ I, ψ (M.coef ⟨k, m⟩ I) * minorIJ (G p.1) I (stepCols N j p.2)) :
    ∃ c : K → F, (∀ k, c k ≠ 0) ∧ ∀ q, z q = c q.1 * f (polyPt M q) := by
  have hmap : ∀ τ, (genLow M.Ω N j τ).map f = G τ * B τ :=
    genLow_map f (H := fun τ => G τ * B τ) (fun τ => ⟨(hG τ).mul (hB τ).1, (hB τ).2.2⟩) hf
  have hdiag : ∀ τ c, B τ c c ≠ 0 := fun τ c h0 => by
    have h1 : (G τ).det * (B τ).det = 1 := by rw [← det_mul, (hB τ).2.2.det]
    have h2 : ∏ i, B τ i i = 0 := Finset.prod_eq_zero (Finset.mem_univ c) h0
    rw [det_of_upperTriangular (hB τ).2.1, h2, mul_zero] at h1
    exact zero_ne_one h1
  let s : Ψ × Fin N → F := fun p => ∏ c ∈ stepCols N j p.2, B p.1 c c
  have hs : ∀ p, s p ≠ 0 := fun p => Finset.prod_ne_zero_iff.2 fun c _ => hdiag p.1 c
  have gen : ∀ a b t : F, t ≠ 0 → a * b = t⁻¹ * (a * (b * t)) := fun a b t ht => by field_simp
  refine ⟨fun k => if h : ∀ p, M.blk p ≠ some k then 1 else (s (stepOf M k h))⁻¹, fun k => ?_, ?_⟩
  · dsimp only
    split_ifs with h
    · exact one_ne_zero
    · exact inv_ne_zero (hs _)
  · rintro ⟨k, m⟩
    by_cases h : ∀ p, M.blk p ≠ some k
    · have e := hbase ⟨⟨k, h⟩, m⟩
      simp only [polyPt, dif_pos h, one_mul, hfC]
      exact e
    · set_option synthInstance.maxHeartbeats 100000 in
        simp only [polyPt, dif_neg h, map_sum, map_mul, hfC, map_minorIJ, hmap]
      rw [hstep _ k (blk_stepOf M k h) m, Finset.mul_sum]
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [(GlobalTheory.T.block_diagonal_minor_vanishing F N j (stepOf M k h).2 M.j_le).2.2.1 _ _ I (hB _).1 (hB _).2.1]
      exact gen _ _ _ (hs _)

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.GenIdeal

end
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FA GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

namespace GlobalTheory.CompanionTheory.Ar.PB.FA.StepLine

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)

theorem pullDeg_zero {K K' : Type} (κ : K → K') : pullDeg κ (0 : K → ℤ) = 0 := by
  funext k
  by_cases h : ∃ a, κ a = k
  · simp [pullDeg, Function.extend_def, h]
  · simp [pullDeg, Function.extend_def, h]

theorem isSmoothHerm_pullHerm {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}
    [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : IsBlockMap κ v) {B : HermLine ι} (hB : IsSmoothHerm B) : IsSmoothHerm (pullHerm hv B) := by
  have hlin : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k', ι' k') → ℂ => fun q => z (v q)) :=
    contDiff_pi.2 fun q => contDiff_apply ℝ (fun _ => ℂ) (v q)
  show ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (B.h ∘ fun z : (Σ k', ι' k') → ℂ => fun q => z (v q))
    {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}
  refine ContDiffOn.comp hB hlin.contDiffOn ?_
  intro z hz k
  obtain ⟨i', hi'⟩ := hz (κ k)
  obtain ⟨q, hq⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
  have h2 : q.1 = k := hv.1 (by rw [← hv.2.2.1 q, hq])
  obtain ⟨k₀, m⟩ := q
  simp only at h2
  subst h2
  exact ⟨m, by simpa [hq] using hi'⟩

theorem exists_stepLine : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ]
    (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (p : Ψ × Fin N)
    (B : HermLine (stepIdx M p)), B.a = 0 → ∃ A : HermLine ι, A.a = M.dy p ∧ M.OnStep p A ∧
      (IsSmoothHerm B → IsSmoothHerm A) ∧ ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
        Real.log (A.h z) = Real.log ((fsHerm ι (M.dy p)).h z) + Real.log (B.h (z ∘ stepV M p)) := by
  intro K _ ι _ Φ _ y Ψ N j M p B hB
  have hdy : ∀ k, M.dy p k ≠ 0 → k ∈ Set.range (Subtype.val : PartialFlagBlocks M p → K) := by
    intro k hk
    by_cases h : ∀ p', M.blk p' ≠ some k
    · exact ⟨⟨k, Or.inl h⟩, rfl⟩
    · by_cases h' : M.blk p = some k
      · exact ⟨⟨k, Or.inr h'⟩, rfl⟩
      · exact absurd (show M.dy p k = 0 by unfold FlagModel.dy; rw [dite_eq_right h, if_neg h']) hk
  refine ⟨(fsHerm ι (M.dy p)).tensor (pullHerm (isBlockMap_stepV M p) B), ?_, ?_, ?_, ?_⟩
  · show M.dy p + pullDeg _ B.a = M.dy p
    rw [hB, pullDeg_zero, add_zero]
  · intro z z' hb hs
    have hc : z ∘ stepV M p = z' ∘ stepV M p := by
      funext ⟨⟨k, hk⟩, m⟩
      rcases hk with h | h
      · exact congrFun hb ⟨⟨k, h⟩, m⟩
      · exact hs k h m
    show (fsHerm ι (M.dy p)).h z * B.h (z ∘ stepV M p) = (fsHerm ι (M.dy p)).h z' * B.h (z' ∘ stepV M p)
    rw [StepW.fsHerm_h_blockMap K ι (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) (M.dy p) z
        (isBlockMap_stepV M p) hdy,
      StepW.fsHerm_h_blockMap K ι (PartialFlagBlocks M p) (stepIdx M p) Subtype.val (stepV M p) (M.dy p) z'
        (isBlockMap_stepV M p) hdy, hc]
  · intro hS
    exact isSmoothHerm_tensor (FlagHeightMultilinear.isSmoothHerm_fsHerm _)
      (isSmoothHerm_pullHerm (isBlockMap_stepV M p) hS)
  · intro z hz
    have h1 := (fsHerm ι (M.dy p)).pos z hz
    have h2 := (pullHerm (isBlockMap_stepV M p) B).pos z hz
    exact Real.log_mul h1.ne' h2.ne'

end GlobalTheory.CompanionTheory.Ar.PB.FA.StepLine
end

section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

def xiDeg (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) : K → ℤ := fun k => ∑ p, xiCoef τ a p * M.dy p k

def aDeg (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) : Option K → ℤ := fun o =>
  match o with
  | none => 1
  | some k => if k = k₀ then 1 else -xiDeg M τ a k

def potA (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) : HermLine fun o : Option K => ι (o.getD k₀) :=
  fsHerm (fun o : Option K => ι (o.getD k₀)) (aDeg M τ a k₀)

def IsPtData (M : FlagModel y Ψ N j) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) {e : ℕ}
    (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ)
    (F : FrameData ι Ψ N M.Ω M.blk) (h : Matrix (Fin N) (Fin N) ℂ) (t : ℂ) : Prop :=
  M.IsFrame F ∧ M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) ∧ SameOrbit z₀ (fstPt k₀ (RW.lift x x)) ∧
    SameOrbit z₁ (sndPt k₀ (RW.lift x x)) ∧ IsBlockDiag j h ∧ h.det ≠ 0 ∧ t ≠ 0 ∧
    (∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₀ h) ∧ ∀ i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ, i) z₁ (h * (1 + Matrix.single cb ca t))

def IsLocSec (M : FlagModel y Ψ N j) {n e : ℕ} (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K)
    (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (x : RW.X)
    (ψ : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : Fin Rb.A.n) (σ : Fin n ↪ Fin e) (i₀ : Fin e) (V : Set RW.X)
    (u : RW.X → ℂ) : Prop :=
  (∃ F H, IsWChart M Rb τ a k₀ ca cb RW pr ψ kb σ i₀ F H) ∧ IsOpen V ∧ x ∈ V ∧ V ⊆ ψ.source ∧ V ⊆ RW.U x ∧
    RW.A.HoloOn V u ∧ (∀ y' ∈ V, u y' ≠ 0) ∧
    (∀ y' ∈ V, ψ y' i₀ = 0 ↔ SameOrbit (fstPt k₀ (RW.lift y' y')) (sndPt k₀ (RW.lift y' y'))) ∧
    ∀ y' ∈ V, ψ y' i₀ ≠ 0 → ∀ z₀ z₁ F h t, IsPtData M τ a k₀ ca cb RW y' z₀ z₁ F h t →
      Real.log ‖u y' * ψ y' i₀‖ - Real.log ((potA M τ a k₀).h (RW.lift x y')) = normRhs M τ a F z₀ z₁ h t

def diagSet (k₀ : K) {P J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing (fun o : Option K => ι (o.getD k₀)))} {e : ℕ} (R : AnLogRes P J e) : Set R.X :=
  {x | SameOrbit (fstPt k₀ (R.lift x x)) (sndPt k₀ (R.lift x x))}

def diagSec {e : ℕ} {X : Type} [TopologicalSpace X] (ψ : X → OpenPartialHomeomorph X (Fin e → ℂ)) (i₀ : X → Fin e)
    (u : X → X → ℂ) : X → X → ℂ := fun x y' => u x y' * ψ x y' (i₀ x)

def secPot {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)] {P J : Ideal (MRing ρ)} {e : ℕ}
    (R : AnLogRes P J e) (A : HermLine ρ) (V : R.X → Set R.X) (hV : ∀ x, IsOpen (V x)) (hm : ∀ x, x ∈ V x) (c : ℝ) :
    LocPot R.X where
  U := V
  isOpen_U := hV
  mem_U := hm
  φ x y' := Real.log (A.h (R.lift x y')) + c

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

section

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem genDegGeomDeg_of_system :
    ReciprocityTheory.ChartRestriction.G.Geo.ArithIntersectionSystemStatement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement →
      GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.Statement :=
  fun hI _ => GroundTheory.Heights₂.Heights.HilbertSamuel.GenDegGeomDeg.proof
    (degreeGeneric_of_degree (degree_of_system hI))

end GlobalTheory.CompanionTheory.Ar.Giv
end

section

open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

theorem _root_.GlobalTheory.T.smooth_local_potential_lift : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (n : ℕ) (M : CxModel P n) (Y : Set M.Xc) (c : Fin n → ℝ) (B : Fin n → HermLine ι) (Φ : Fin n → LocPot M.Xc) (j : Fin M.atlas.n), IsOpen Y → (∀ i x, M.atlas.SmoothOn ((Φ i).U x ∩ Y) ((Φ i).φ x)) → (∀ i, ∀ x, ∀ y₀ ∈ (Φ i).U x ∩ Y, ∃ U : Set M.Xc, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ (Φ i).U x ∩ Y ∧ ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts (P) ∧ M.proj (s y') = y') ∧ (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧ ∀ y' ∈ U, (Φ i).φ x y' - (fun z => c i * Real.log ((B i).h z)) (s y') = (G y').re) → ContinuousOn (locDens M.atlas Φ j) ((M.atlas.chart j).target ∩ (M.atlas.chart j).symm ⁻¹' Y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.Push.DCont.locDens_continuousOn_of_sections | exact GlobalTheory.CompanionTheory.Ar.Giv.Push.DCont.locDens_continuousOn_of_sections | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.Push.DCont.locDens_continuousOn_of_sections <;> assumption)
end
