module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle203
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle204
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle202
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentLocalizationUniversal
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.ObFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
import Development.AbelianVarietyTheory.Definitions.Divisors.OneFormMapEqKaehlerDifferentialMap
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CoeEqAlgebraMapZeroEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.FormCos
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HodgeC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.XSmulSucc

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.WaveSpd

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace SmCalc

section Generic

variable {E W : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] {u : ℝ → E → W} {O : Set E}

theorem hasFDerivAt_unc (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) {y : E} (hy : y ∈ O) :
    HasFDerivAt (Function.uncurry u) (fderiv ℝ (Function.uncurry u) (s, y)) (s, y) :=
  ((hu.contDiffAt ((isOpen_univ.prod hO).mem_nhds ⟨Set.mem_univ _, hy⟩)).differentiableAt
    (by simp)).hasFDerivAt

theorem hasDerivAt_line (s : ℝ) (y : E) :
    HasDerivAt (fun r : ℝ => (r, y)) ((1 : ℝ), (0 : E)) s :=
  (hasDerivAt_id s).prodMk (hasDerivAt_const s y)

theorem deriv_eq (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) {y : E} (hy : y ∈ O) :
    deriv (fun r => u r y) s = fderiv ℝ (Function.uncurry u) (s, y) ((1 : ℝ), (0 : E)) := by
  have h2 := HasFDerivAt.comp_hasDerivAt (f := fun r : ℝ => (r, y)) s
    (hasFDerivAt_unc hO hu s hy) (hasDerivAt_line s y)
  exact h2.deriv

theorem fderiv_slice_eq (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) {y : E} (hy : y ∈ O)
    (v : E) : fderiv ℝ (u s) y v = fderiv ℝ (Function.uncurry u) (s, y) ((0 : ℝ), v) := by
  have h1 : HasFDerivAt (fun z : E => (s, z)) (ContinuousLinearMap.inr ℝ ℝ E) y :=
    hasFDerivAt_prodMk_right s y
  have h2 := HasFDerivAt.comp (g := Function.uncurry u) (f := fun z : E => (s, z)) y
    (hasFDerivAt_unc hO hu s hy) h1
  have h3 : HasFDerivAt (u s) ((fderiv ℝ (Function.uncurry u) (s, y)).comp
      (ContinuousLinearMap.inr ℝ ℝ E)) y := h2
  simp [h3.fderiv]

theorem fd_smooth (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) :
    ContDiffOn ℝ ∞ (fderiv ℝ (Function.uncurry u)) (Set.univ ×ˢ O) :=
  hu.fderiv_of_isOpen (isOpen_univ.prod hO) (by simp)

theorem smooth_deriv (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) :
    ContDiffOn ℝ ∞ (Function.uncurry fun s y => deriv (fun r => u r y) s) (Set.univ ×ˢ O) := by
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      fderiv ℝ (Function.uncurry u) p ((1 : ℝ), (0 : E))) (Set.univ ×ˢ O) :=
    (fd_smooth hO hu).clm_apply contDiffOn_const
  refine ContDiffOn.congr h ?_
  rintro ⟨s, y⟩ ⟨-, hy⟩
  exact deriv_eq hO hu s hy

theorem smooth_field (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O))
    {V : E → E} (hV : ContDiff ℝ ∞ V) :
    ContDiffOn ℝ ∞ (Function.uncurry fun s y => fderiv ℝ (u s) y (V y)) (Set.univ ×ˢ O) := by
  have h0 : ContDiff ℝ ∞ (fun p : ℝ × E => ((0 : ℝ), V p.2)) :=
    contDiff_const.prodMk (hV.comp contDiff_snd)
  have h : ContDiffOn ℝ ∞ (fun p : ℝ × E =>
      fderiv ℝ (Function.uncurry u) p ((0 : ℝ), V p.2)) (Set.univ ×ˢ O) :=
    (fd_smooth hO hu).clm_apply h0.contDiffOn
  refine ContDiffOn.congr h ?_
  rintro ⟨s, y⟩ ⟨-, hy⟩
  exact fderiv_slice_eq hO hu s hy _

theorem smooth_slice (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (s : ℝ) :
    ContDiffOn ℝ ∞ (u s) O := by
  have h1 : ContDiff ℝ ∞ (fun z : E => (s, z)) := contDiff_const.prodMk contDiff_id
  exact ContDiffOn.comp (g := Function.uncurry u) (f := fun z : E => (s, z)) hu
    h1.contDiffOn (fun z hz => ⟨Set.mem_univ _, hz⟩)

theorem smooth_line (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O))
    {y : E} (hy : y ∈ O) : ContDiff ℝ ∞ fun s => u s y := by
  have h1 : ContDiff ℝ ∞ (fun r : ℝ => (r, y)) := contDiff_id.prodMk contDiff_const
  have h2 := ContDiffOn.comp (s := Set.univ) (g := Function.uncurry u)
    (f := fun r : ℝ => (r, y)) hu h1.contDiffOn (fun _ _ => ⟨Set.mem_univ _, hy⟩)
  exact contDiffOn_univ.1 h2

theorem deriv_fderiv_comm (hO : IsOpen O)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Set.univ ×ˢ O)) (v : E) (s : ℝ) {y : E}
    (hy : y ∈ O) :
    deriv (fun r => fderiv ℝ (u r) y v) s =
      fderiv ℝ (fun z => deriv (fun r => u r z) s) y v := by
  have hm : (s, y) ∈ (Set.univ : Set ℝ) ×ˢ O := ⟨Set.mem_univ _, hy⟩
  have hn := (isOpen_univ.prod hO).mem_nhds hm
  have hF : ContDiffAt ℝ ∞ (Function.uncurry u) (s, y) := hu.contDiffAt hn
  have hG : HasFDerivAt (fderiv ℝ (Function.uncurry u))
      (fderiv ℝ (fderiv ℝ (Function.uncurry u)) (s, y)) (s, y) :=
    (((fd_smooth hO hu).contDiffAt hn).differentiableAt (by simp)).hasFDerivAt
  have hsym : IsSymmSndFDerivAt ℝ (Function.uncurry u) (s, y) :=
    hF.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hL : HasDerivAt (fun r => fderiv ℝ (u r) y v)
      (fderiv ℝ (fderiv ℝ (Function.uncurry u)) (s, y) ((1 : ℝ), (0 : E)) ((0 : ℝ), v)) s := by
    have h2 := HasFDerivAt.comp_hasDerivAt (f := fun r : ℝ => (r, y)) s hG (hasDerivAt_line s y)
    have h3 := ((ContinuousLinearMap.apply ℝ W ((0 : ℝ), v)).hasFDerivAt).comp_hasDerivAt s h2
    have he : (fun r => fderiv ℝ (u r) y v) = (⇑(ContinuousLinearMap.apply ℝ W ((0 : ℝ), v)) ∘
        (fderiv ℝ (Function.uncurry u)) ∘ fun r : ℝ => (r, y)) := by
      funext r
      simpa using fderiv_slice_eq hO hu r hy v
    rw [he]
    simpa using h3
  have hR : HasFDerivAt (fun z => deriv (fun r => u r z) s)
      ((ContinuousLinearMap.apply ℝ W ((1 : ℝ), (0 : E))).comp
        ((fderiv ℝ (fderiv ℝ (Function.uncurry u)) (s, y)).comp
          (ContinuousLinearMap.inr ℝ ℝ E))) y := by
    have h1 : HasFDerivAt (fun z : E => (s, z)) (ContinuousLinearMap.inr ℝ ℝ E) y :=
      hasFDerivAt_prodMk_right s y
    have h2 := HasFDerivAt.comp (f := fun z : E => (s, z)) y hG h1
    have h3 := ((ContinuousLinearMap.apply ℝ W ((1 : ℝ), (0 : E))).hasFDerivAt).comp y h2
    refine h3.congr_of_eventuallyEq ?_
    filter_upwards [hO.mem_nhds hy] with z hz
    simpa using deriv_eq hO hu s hz
  rw [hL.deriv, hR.fderiv]
  simpa using hsym.eq ((1 : ℝ), (0 : E)) ((0 : ℝ), v)

end Generic

theorem contDiff_mulRight {n : ℕ} (X : Mat n) : ContDiff ℝ ∞ (fun y : Mat n => y * X) :=
  (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)).contDiff

end SmCalc

theorem sm_calculus : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (u : ℝ → Mat n → W), Sm u → Sm (dt u) ∧ (∀ X : Mat n, Sm (Rt X u)) ∧
      (∀ s, ContDiffOn ℝ ∞ (u s) (GLs n)) ∧ (∀ y ∈ GLs n, ContDiff ℝ ∞ fun s => u s y) ∧
      ∀ (X : Mat n) (s : ℝ), ∀ y ∈ GLs n, dt (Rt X u) s y = Rr X (dt u s) y :=
  fun _ hu => ⟨SmCalc.smooth_deriv isOpen_GLs hu,
    fun X => SmCalc.smooth_field isOpen_GLs hu (SmCalc.contDiff_mulRight X),
    SmCalc.smooth_slice hu, fun _ hy => SmCalc.smooth_line hu hy,
    fun _ s _ hy => SmCalc.deriv_fderiv_comm isOpen_GLs hu _ s hy⟩

end GlobalTheory.CompanionTheory.WaveSpd
end
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.GlTranspose

variable {n : ℕ} {A : Type} [Ring A]

theorem epw_zero (e : Fin n → Fin n → A) (a b : Fin n) :
    Epw e 0 a b = if a = b then 1 else 0 := by
  rw [Epw]

theorem epw_succ (e : Fin n → Fin n → A) (m : ℕ) (a b : Fin n) :
    Epw e (m + 1) a b = ∑ c, e a c * Epw e m c b := by
  rw [Epw]

theorem epw_succ_right (e : Fin n → Fin n → A) (m : ℕ) (a b : Fin n) :
    Epw e (m + 1) a b = ∑ c, Epw e m a c * e c b := by
  induction m generalizing a b with
  | zero =>
    simp [epw_succ, epw_zero]
  | succ m ih =>
    calc Epw e (m + 1 + 1) a b = ∑ c, e a c * ∑ d, Epw e m c d * e d b := by
          rw [epw_succ]
          exact sum_congr rfl fun c _ => by rw [ih]
      _ = ∑ d, (∑ c, e a c * Epw e m c d) * e d b := by
          simp only [mul_sum, sum_mul, mul_assoc]
          exact Finset.sum_comm
      _ = ∑ c, Epw e (m + 1) a c * e c b := sum_congr rfl fun d _ => by rw [epw_succ]

theorem bco_zero_zero (N : A) (τ : ℕ → A) : bco N τ 0 0 = 1 := by rw [bco]

theorem bco_zero_succ (N : A) (τ : ℕ → A) (j : ℕ) : bco N τ 0 (j + 1) = 0 := by rw [bco]

theorem bco_succ_zero (N : A) (τ : ℕ → A) (m : ℕ) :
    bco N τ (m + 1) 0 = N * bco N τ m 0 - τ m := by rw [bco]

theorem bco_succ_succ (N : A) (τ : ℕ → A) (m j : ℕ) :
    bco N τ (m + 1) (j + 1) = bco N τ m j + N * bco N τ m (j + 1) := by rw [bco]

theorem bco_eq_zero (N : A) (τ : ℕ → A) (m j : ℕ) (h : m < j) : bco N τ m j = 0 := by
  induction m generalizing j with
  | zero =>
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact bco_zero_succ N τ j
  | succ m ih =>
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [bco_succ_succ, ih j (by omega), ih (j + 1) (by omega)]
    simp

theorem bco_self (N : A) (τ : ℕ → A) (m : ℕ) : bco N τ m m = 1 := by
  induction m with
  | zero => exact bco_zero_zero N τ
  | succ m ih =>
    rw [bco_succ_succ, ih, bco_eq_zero N τ m (m + 1) (by omega)]
    simp

theorem phiSeq_eq (N : A) (τ : ℕ → A) (m : ℕ) :
    phiSeq N τ m = τ m - ∑ j ∈ range m, bco N τ m j * phiSeq N τ j := by
  rw [phiSeq, Fin.sum_univ_eq_sum_range (fun j => bco N τ m j * phiSeq N τ j) m]

section Gl

variable (e : Fin n → Fin n → A)
  (he : ∀ a b c d, e a b * e c d - e c d * e a b =
    (if b = c then e a d else 0) - (if a = d then e c b else 0))
include he

theorem comm_epw (m : ℕ) (a b c d : Fin n) :
    e a b * Epw e m c d - Epw e m c d * e a b =
      (if b = c then Epw e m a d else 0) - (if a = d then Epw e m c b else 0) := by
  induction m generalizing c d with
  | zero =>
    simp only [epw_zero]
    by_cases h1 : c = d
    · subst h1
      by_cases h2 : b = c
      · subst h2; simp
      · have h3 : ¬ c = b := fun h => h2 h.symm
        simp [h2, h3]
    · by_cases h2 : b = c
      · subst h2
        by_cases h3 : a = d
        · subst h3; simp [h1]
        · simp [h1, h3]
      · have h3 : ¬ c = b := fun h => h2 h.symm
        simp [h1, h2, h3]
  | succ m ih =>
    have step : ∀ f, e a b * (e c f * Epw e m f d) - (e c f * Epw e m f d) * e a b =
        ((if b = c then e a f else 0) - (if a = f then e c b else 0)) * Epw e m f d +
          e c f * ((if b = f then Epw e m a d else 0) - (if a = d then Epw e m f b else 0)) := by
      intro f
      rw [← he a b c f, ← ih f d]
      noncomm_ring
    rw [epw_succ e m c d, mul_sum, sum_mul, ← sum_sub_distrib, sum_congr rfl (fun f _ => step f)]
    simp only [sub_mul, mul_sub, sum_add_distrib, sum_sub_distrib, ite_mul, mul_ite, zero_mul,
      mul_zero, sum_ite_eq, sum_ite_eq', mem_univ, if_true]
    by_cases h1 : b = c <;> by_cases h2 : a = d <;>
      simp only [h1, h2, if_true, if_false, ← epw_succ, sum_const_zero] <;> abel

theorem transpose_step (m : ℕ) (a b : Fin n) :
    Epw e (m + 1) b a =
      ∑ c, Epw e m c a * e b c + (n : A) * Epw e m b a - (if a = b then trE e m else 0) := by
  have h : Epw e (m + 1) b a - ∑ c, Epw e m c a * e b c =
      (n : A) * Epw e m b a - (if a = b then trE e m else 0) := by
    rw [epw_succ, ← sum_sub_distrib,
      sum_congr rfl (fun c _ => comm_epw e he m b c c a), sum_sub_distrib]
    by_cases h1 : a = b
    · subst h1; simp [trE]
    · have h2 : ¬ b = a := fun h => h1 h.symm
      simp [h1, h2]
  rw [add_sub_assoc, ← h]
  abel

theorem transpose_poly (m : ℕ) (a b : Fin n) :
    Epw e m b a =
      ∑ j ∈ range (m + 1), bco (n : A) (trE e) m j * Epw (fun a b => e b a) j a b := by
  induction m generalizing a b with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, bco_zero_zero, one_mul, epw_zero]
    simp only [eq_comm]
  | succ m ih =>
    set f : Fin n → Fin n → A := fun a b => e b a with hf
    set N : A := (n : A) with hN
    set τ : ℕ → A := trE e with hτ
    have key : ∑ c, Epw e m c a * e b c =
        ∑ j ∈ range (m + 1), bco N τ m j * Epw f (j + 1) a b := by
      simp only [epw_succ_right f, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun c _ => ?_
      rw [ih a c, sum_mul]
      refine sum_congr rfl fun j _ => ?_
      rw [mul_assoc]
    have hn : N * Epw e m b a =
        ∑ j ∈ range (m + 1), N * bco N τ m (j + 1) * Epw f (j + 1) a b +
          N * bco N τ m 0 * Epw f 0 a b := by
      rw [← sum_range_succ' (fun j => N * bco N τ m j * Epw f j a b) (m + 1),
        sum_range_succ _ (m + 1), bco_eq_zero N τ m (m + 1) (by omega), ih a b, mul_sum]
      simp [mul_assoc]
    rw [transpose_step e he, key, hn, sum_range_succ' _ (m + 1), bco_succ_zero]
    simp only [bco_succ_succ, add_mul, sum_add_distrib, sub_mul, epw_zero f]
    by_cases h1 : a = b
    · simp [h1]
      try abel
    · simp [h1]
      try abel

theorem trE_eq_sum (m : ℕ) :
    trE e m = ∑ j ∈ range (m + 1), bco (n : A) (trE e) m j * trE (fun a b => e b a) j := by
  have h : trE e m = ∑ a, Epw e m a a := rfl
  rw [h, sum_congr rfl (fun a _ => transpose_poly e he m a a), sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [trE, mul_sum]

end Gl

theorem trE_transpose_eq_phiSeq (n : ℕ) {A : Type} [Ring A] [Algebra ℂ A]
    (e : Fin n → Fin n → A)
    (he : ∀ a b c d, e a b * e c d - e c d * e a b =
      (if b = c then e a d else 0) - (if a = d then e c b else 0)) (m : ℕ) :
    trE (fun a b => e b a) m = phiSeq (n : A) (trE e) m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have h := trE_eq_sum e he m
    rw [sum_range_succ, bco_self, one_mul] at h
    have hs : ∑ j ∈ range m, bco (n : A) (trE e) m j * phiSeq (n : A) (trE e) j =
        ∑ j ∈ range m, bco (n : A) (trE e) m j * trE (fun a b => e b a) j :=
      sum_congr rfl fun j hj => by rw [ih j (mem_range.mp hj)]
    rw [phiSeq_eq, hs, h, add_sub_cancel_left]

end GlobalTheory.CompanionTheory.WaveMult.GlTranspose
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

theorem _root_.GlobalTheory.T.double_complex_degenerate_column_iso : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a : ℕ), (∀ p q, q ≠ a → Subsingleton ((K.col p).H q)) →
    ∀ j, ∃ e : K.tot.H (a + j) ≃ₗ[R] (colH K a).H j, ∀ z : Zf K (a + j) j, e (clsZ K (a + j) j z) = leadE K j a z := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.row_iso_of_columns | exact GlobalTheory.CompanionTheory.CechSerre.row_iso_of_columns | (intros; apply GlobalTheory.CompanionTheory.CechSerre.row_iso_of_columns <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.sharp_surjective_ker_span : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), Function.Surjective A.aToU1 ∧ RingHom.ker A.aToU1 = Ideal.span {A.pi} := by
  first | exact @GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker | exact GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker | (intros; apply GlobalTheory.CompanionTheory.Untilt.sharp_map_surjective_ker <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.crystalline_filtration_multiplicative : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.Fil0 0 = ⊤ ∧ (∀ i j, A.dxi0 i * A.dxi0 j = ((i + j).choose i : A.Acr0) * A.dxi0 (i + j)) ∧ (∀ k, (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k) ∧ (∀ r s, A.Fil0 r * A.Fil0 s ≤ A.Fil0 (r + s)) ∧ (∀ n r, A.Fil n r = (A.Fil0 r).map (A.mkAcr n)) ∧ (∀ n, A.PFil n = A.PFil0.map (A.mkAcr n)) ∧ (∀ n, A.Fil n 0 = ⊤) ∧ ∀ n r s, A.Fil n r * A.Fil n s ≤ A.Fil n (r + s) := by
  first | exact @GlobalTheory.CompanionTheory.FilMul.main | exact GlobalTheory.CompanionTheory.FilMul.main | (intros; apply GlobalTheory.CompanionTheory.FilMul.main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.functoriality_of_period_ring_maps : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (B : PAlg l) (f : A ⟶ B), (∀ a, mapAcr f 1 (A.aTo1 a) = B.aTo1 (Hom.f f a)) ∧ (∀ c : ℕ →₀ A.A, mapAcr f 1 (A.expand c) = B.expand (c.mapRange (Hom.f f) (map_zero _))) ∧ (∀ a, mapU f (A.sharp a) = B.sharp (Hom.f f a)) ∧ (∀ a, mapUn f 1 (A.aToU1 a) = B.aToU1 (Hom.f f a)) ∧ (∀ n x, Ideal.Quotient.mk (B.Fil n 1) (mapAcr f n (A.toAcr n x)) = B.uToQ n (mapU f (A.th x))) ∧ ∀ x : Ainf l, algebraMap (Ainf l) (A.Acr 1) x = A.aTo1 (A.s (x.coeff 0)) := by
  first | exact @GlobalTheory.CompanionTheory.PAlgNat.expand_nat | exact GlobalTheory.CompanionTheory.PAlgNat.expand_nat | (intros; apply GlobalTheory.CompanionTheory.PAlgNat.expand_nat <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.continuous_functions_perfect_adic_ring : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (Γ : Type) [TopologicalSpace Γ], PerfectRing (A.contR Γ) l ∧ IsAdicComplete (Ideal.span {A.contC Γ A.pi}) (A.contR Γ) ∧ A.contC Γ A.pi ∈ nonZeroDivisors (A.contR Γ) ∧ ∀ (k : ℕ) (f : A.contR Γ), f ∈ Ideal.span {A.contC Γ A.pi ^ k} ↔ ∀ γ, f.1 γ ∈ Ideal.span {A.pi ^ k} := by
  first | exact @GlobalTheory.CompanionTheory.ContFn.main | exact GlobalTheory.CompanionTheory.ContFn.main | (intros; apply GlobalTheory.CompanionTheory.ContFn.main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.twist_frobenius_filtration_compat : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)), (∀ x ∈ (tw σ A).Fil0 1, (pdOk_twId σ A).acr0 x ∈ A.Fil0 1) ∧ (∀ x ∈ A.PFil0, A.pdOk_frob.acr0 x ∈ Ideal.span {(l : A.Acr0)}) ∧ (∀ n r, ∀ x ∈ (tw σ A).Fil n r, twAcr σ A n x ∈ A.Fil n r) ∧ (∀ n, Function.Bijective (twAcr σ A n)) ∧ ∀ n x, twAcr σ A n ((tw σ A).phi n x) = A.phi n (twAcr σ A n x) := by
  first | exact @GlobalTheory.CompanionTheory.TwFil.tw_fil | exact GlobalTheory.CompanionTheory.TwFil.tw_fil | (intros; apply GlobalTheory.CompanionTheory.TwFil.tw_fil <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.Untilt

theorem isUnit_of_isUnit_sharp {l : ℕ} [Fact l.Prime] (A : PAlg l) (a : A.A)
    (h : IsUnit (A.sharp a)) : IsUnit a := by
  have hu : IsUnit (A.aToU1 a) := by
    rw [CrystallineSemistableComparison.PAlg.sharpMap_eq]
    exact h.map _
  obtain ⟨hsurj, hker⟩ := sharp_map_surjective_ker A
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨b, rfl⟩ := hsurj v
  have hmem : a * b - 1 ∈ Ideal.span {A.pi} := by
    rw [← hker, RingHom.mem_ker, map_sub, map_mul, hv, map_one, sub_self]
  have hjac : Ideal.span {A.pi} ≤ (⊥ : Ideal A.A).jacobson := by
    haveI : IsAdicComplete (Ideal.span {A.pi}) A.A := A.compl
    exact IsAdicComplete.le_jacobson_bot _
  have hunit := Ideal.mem_jacobson_bot.mp (hjac hmem) 1
  rw [mul_one, sub_add_cancel] at hunit
  exact isUnit_of_mul_isUnit_left hunit

end GlobalTheory.CompanionTheory.Untilt
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

theorem _root_.GlobalTheory.T.idempotent_localization_universal : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (e : A.A), IsIdempotentElem e → ∃ (A' : PAlg l) (lam : A ⟶ A'), (A.IsTest → A'.IsTest) ∧ PAlg.Hom.f lam e = 1 ∧ (∀ (B : PAlg l) (ψ : A ⟶ B), PAlg.Hom.f ψ e = 1 → ∃! χ : A' ⟶ B, lam ≫ χ = ψ) ∧ ∀ n, Function.Surjective (mapAcr lam n) ∧ ∀ x, mapAcr lam n x = 0 → A.toAcr n (WittVector.teichmuller l e) * x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.IdemObj.directFactor | exact GlobalTheory.CompanionTheory.IdemObj.directFactor | (intros; apply GlobalTheory.CompanionTheory.IdemObj.directFactor <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.acris_level_sequence_facts : ∀ (l : ℕ) [Fact l.Prime], CrystallineSemistableComparison.D.RAcrSeq l := by
  first | exact @GlobalTheory.CompanionTheory.LSeq.racrSeq | exact GlobalTheory.CompanionTheory.LSeq.racrSeq | (intros; apply GlobalTheory.CompanionTheory.LSeq.racrSeq <;> assumption)
end
