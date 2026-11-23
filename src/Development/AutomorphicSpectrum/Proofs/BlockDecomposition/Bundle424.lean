module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle403
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle406
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle239
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle241
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMemGLs
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.OnlyIsotropic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightIndicator
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightSupportBound
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobData
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle414
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub

@[expose] public section

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.SmoothRep

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

def hsq (x : Lie E a) : ℝ :=
  ∑ i, ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2

theorem hsq_nonneg (x : Lie E a) : 0 ≤ hsq x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem sq_le_hsq (x : Lie E a) (i j : Fin a) (w : InfinitePlace E) :
    ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤ hsq x := by
  have h1 : ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤
      ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 :=
    Finset.single_le_sum (f := fun w => ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ w)
  have h2 : ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤
      ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)
  have h3 : ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2 ≤ hsq x :=
    Finset.single_le_sum (f := fun i => ∑ j, ∑ w, ‖(Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)
  exact h1.trans (h2.trans h3)

theorem hsq_oneL : hsq (oneL E a) = 0 := by
  simp [hsq, oneL, toL]

theorem dist_oneL_lt {x : Lie E a} {δ : ℝ} (hδ : 0 < δ) (h : hsq x < δ ^ 2) : dist x (oneL E a) < δ := by
  refine (dist_pi_lt_iff hδ).2 fun i => (dist_pi_lt_iff hδ).2 fun j => (dist_pi_lt_iff hδ).2 fun w => ?_
  have h1 := (sq_le_hsq x i j w).trans_lt h
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hδ.le h1

theorem contDiff_hsq : ContDiff ℝ ∞ (hsq : Lie E a → ℝ) := by
  unfold hsq
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ContDiff.sum fun w _ => ContDiff.norm_sq ℝ ?_
  change ContDiff ℝ ∞ fun x : Lie E a => x i j w - (1 : Matrix (Fin a) (Fin a) (Cinf E)) i j w
  fun_prop

theorem ofReal_hsq (x : Lie E a) :
    (hsq x : ℂ) = ∑ w, Matrix.trace ((Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E)) *
      star (Matrix.of x - 1 : Matrix (Fin a) (Fin a) (Cinf E))) w := by
  simp only [hsq, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply, Finset.sum_apply, Pi.mul_apply,
    Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow, Complex.star_def, Complex.mul_conj']
  refine Eq.trans ?_ Finset.sum_comm
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Eq.trans ?_ Finset.sum_comm
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => rfl

theorem hsq_conj (k : Kinf E a) (x : Lie E a) : hsq (toL (k.1 * Matrix.of x * star k.1)) = hsq x := by
  apply Complex.ofReal_injective
  rw [ofReal_hsq, ofReal_hsq]
  have hk : k.1 * star k.1 = 1 := Matrix.mem_unitaryGroup_iff.1 k.2
  have hk' : star k.1 * k.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 k.2
  set Y : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of x - 1 with hY
  have e1 : (Matrix.of (toL (k.1 * Matrix.of x * star k.1)) - 1 : Matrix (Fin a) (Fin a) (Cinf E)) = k.1 * Y * star k.1 := by
    rw [hY, mul_sub, sub_mul, mul_one, hk]
    rfl
  have e2 : Matrix.trace ((k.1 * Y * star k.1) * star (k.1 * Y * star k.1)) = Matrix.trace (Y * star Y) := by
    have : (k.1 * Y * star k.1) * star (k.1 * Y * star k.1) = k.1 * ((Y * star Y) * star k.1) := by
      simp only [star_mul, star_star]
      calc k.1 * Y * star k.1 * (k.1 * (star Y * star k.1))
          = k.1 * Y * (star k.1 * k.1) * (star Y * star k.1) := by simp only [mul_assoc]
        _ = k.1 * ((Y * star Y) * star k.1) := by rw [hk']; simp only [mul_one, mul_assoc]
    rw [this, Matrix.trace_mul_comm, mul_assoc, hk', mul_one]
  rw [e1, e2]

end GlobalTheory.CompanionTheory.SmoothRep

namespace GlobalTheory.CompanionTheory.SmoothRep


attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem val_image_mem_nhds_one {E : Type} [Field E] [NumberField E] {a : ℕ} {N : Set (GL (Fin a) (Cinf E))} (hN : N ∈ 𝓝 1) :
    (Units.val '' N) ∈ 𝓝 (1 : Matrix (Fin a) (Fin a) (Cinf E)) := by
  letI : NormedAddCommGroup (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (Fin a) (Fin a) (Cinf E)) := Matrix.linftyOpNormedRing
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  exact (Units.isOpenEmbedding_val (R := Matrix (Fin a) (Fin a) (Cinf E))).isOpenMap.image_mem_nhds hN

theorem exists_bump_conjInv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (N : Set (GL (Fin a) (Cinf E))), N ∈ 𝓝 1 → ∃ β₀ : Lie E a → ℝ, 0 ≤ β₀ ∧ 0 < β₀ (oneL E a) ∧
      IsTest (fun x => (β₀ x : ℂ)) ∧ ConjInv (fun x => (β₀ x : ℂ)) ∧ ∀ x, β₀ x ≠ 0 → ∃ y ∈ N, toL y.val = x := by
  intro E _ _ _ a N hN
  have h := val_image_mem_nhds_one hN
  have e : (toL '' (Units.val '' N) : Set (Lie E a)) = Units.val '' N := Set.image_id _
  have hV : (toL '' (Units.val '' N) : Set (Lie E a)) ∈ 𝓝 (oneL E a) := by
    rw [e]; exact h
  obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.1 hV
  have hδ2 : 0 < δ ^ 2 := by positivity
  let f : ContDiffBump (0 : ℝ) := ⟨δ ^ 2 / 4, δ ^ 2 / 2, by positivity, by linarith⟩
  have hsupp : ∀ x : Lie E a, f (hsq x) ≠ 0 → hsq x < δ ^ 2 / 2 := fun x hx => by
    have : hsq x ∈ Function.support f := hx
    rw [f.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg (hsq_nonneg x)] at this
    exact this
  have hmem : ∀ x : Lie E a, hsq x ≤ δ ^ 2 / 2 → ∃ y ∈ N, toL y.val = x := fun x hx => by
    have : x ∈ Metric.ball (oneL E a) δ := dist_oneL_lt hδ (by linarith)
    obtain ⟨_, ⟨y, hy, rfl⟩, rfl⟩ := hb this
    exact ⟨y, hy, rfl⟩
  have hKc : IsClosed {x : Lie E a | hsq x ≤ δ ^ 2 / 2} :=
    isClosed_le contDiff_hsq.continuous continuous_const
  have hts : tsupport (fun x => (f (hsq x) : ℂ)) ⊆ {x : Lie E a | hsq x ≤ δ ^ 2 / 2} :=
    closure_minimal (fun x hx => (hsupp x (fun h0 => hx (by simp [h0]))).le) hKc
  have hKb : {x : Lie E a | hsq x ≤ δ ^ 2 / 2} ⊆ Metric.closedBall (oneL E a) δ := fun x hx =>
    (dist_oneL_lt hδ (by simp only [Set.mem_setOf_eq] at hx; linarith)).le
  refine ⟨fun x => f (hsq x), fun x => f.nonneg, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · show 0 < f (hsq (oneL E a))
    rw [hsq_oneL]
    exact f.pos_of_mem_ball (Metric.mem_ball_self f.rOut_pos)
  · exact Complex.ofRealCLM.contDiff.comp (f.contDiff.comp contDiff_hsq)
  · exact (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hts.trans hKb)
  · intro x hx
    obtain ⟨y, _, rfl⟩ := hmem x (hts hx)
    exact y.isUnit
  · intro k x
    show (f (hsq (toL (k.1 * Matrix.of x * star k.1))) : ℂ) = f (hsq x)
    rw [hsq_conj]
  · exact fun x hx => hmem x (hsupp x hx).le

end GlobalTheory.CompanionTheory.SmoothRep
end
end

section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SmoothRep

theorem contDiff_mulRight {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Lie E a) :
    ContDiff ℝ ∞ (fun w : Lie E a => toL (Matrix.of w * Matrix.of X)) := by
  let L : Lie E a →ₗ[ℝ] Lie E a :=
    { toFun := fun w => toL (Matrix.of w * Matrix.of X)
      map_add' := fun w v => by
        simp only [toL]
        exact congrArg Matrix.of.symm (Matrix.add_mul (Matrix.of w) (Matrix.of v) (Matrix.of X))
      map_smul' := fun c w => by
        simp only [toL, RingHom.id_apply]
        exact congrArg Matrix.of.symm (Matrix.smul_mul c (Matrix.of w) (Matrix.of X)) }
  exact (LinearMap.toContinuousLinearMap L).contDiff

theorem tsupport_dTest_subset {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Lie E a) (β : Lie E a → ℂ) :
    tsupport (dTest X β) ⊆ tsupport β := by
  refine (closure_mono fun w hw => ?_).trans (tsupport_fderiv_subset ℝ (f := β))
  rw [Function.mem_support] at hw ⊢
  intro h
  apply hw
  simp [dTest, h]

theorem isTest_dTest (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (β : Lie E a → ℂ)
    (hβ : IsTest β) (X : Lie E a) : IsTest (dTest X β) := by
  have hfd := (contDiff_infty_iff_fderiv.mp hβ.contDiff).2
  refine IsTest.mk ?_ ?_ ?_
  · exact hfd.clm_apply (contDiff_mulRight X)
  · exact hβ.compact.mono' ((subset_tsupport _).trans (tsupport_dTest_subset X β))
  · exact (tsupport_dTest_subset X β).trans hβ.support

end GlobalTheory.CompanionTheory.SmoothRep
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobOpsPf

open GlobalTheory.CompanionTheory.RCalc (Rd_congr Rd_add Rd_smul Rd_contDiffOn differentiableAt_of_smooth gel_contDiffOn Rd_gel gel_right
  gel_post fderiv_comp_clm fderiv_post mulR mapsTo_mulR)
open GlobalTheory.CompanionTheory.SobSecK (Rw_congr Rw_smooth Rw_append Rd_sum_cf)

variable {n : ℕ}

section Words

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rw_add (w : List (Bool × Fin n × Fin n)) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) : Set.EqOn (Rw w (f + f')) (Rw w f + Rw w f') (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_add (bs p) (Rw_smooth w hf) (Rw_smooth w hf') hx)

theorem Rw_smul (w : List (Bool × Fin n × Fin n)) (c : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Rw w (c • f)) (c • Rw w f) (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_smul c (bs p) (Rw_smooth w hf) hx)

theorem Om_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) : ContDiffOn ℝ ∞ (Om f) (GLs n) :=
  ((gel_contDiffOn true 2 hf).add (gel_contDiffOn false 2 hf)).const_smul (2 : ℂ)

theorem Rd_Om (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (Om f) g = Om (Rd X f) g := by
  have h1 := gel_contDiffOn true 2 hf
  have h2 := gel_contDiffOn false 2 hf
  have h3 : ContDiffOn ℝ ∞ (gel true 2 f + gel false 2 f) (GLs n) := h1.add h2
  have e1 := Rd_smul (2 : ℂ) X h3 hg
  have e2 := Rd_add X h1 h2 hg
  simp only [Pi.smul_apply, Pi.add_apply] at e1 e2
  simp only [Om, Pi.smul_apply, Pi.add_apply]
  rw [e1, e2, Rd_gel X true 2 hf hg, Rd_gel X false 2 hf hg]

theorem Rw_Om (w : List (Bool × Fin n × Fin n)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Rw w (Om f)) (Om (Rw w f)) (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_Om (bs p) (Rw_smooth w hf) hx)

theorem Rd_translate (X : Mat n) {x : Mat n} (hx : x ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (fun y => f (y * x)) g = Rd (x⁻¹ * X * x) f (g * x) := by
  have hu : IsUnit x.det := isUnit_iff_ne_zero.mpr hx
  have hd := differentiableAt_of_smooth hf (mapsTo_mulR hx hg)
  have e : g * x * (x⁻¹ * X * x) = g * X * x := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  have := fderiv_comp_clm (mulR x) hd (g * X)
  simp only [Rd, e]
  exact this

theorem Rd_post (X : Mat n) (A : V →L[ℂ] V) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Rd X (fun y => A (f y)) g = A (Rd X f g) :=
  fderiv_post A (differentiableAt_of_smooth hf hg) _

theorem post_smooth (A : V →L[ℂ] V) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (fun y => A (f y)) (GLs n) :=
  (A.restrictScalars ℝ).contDiff.comp_contDiffOn hf

theorem Rw_post (w : List (Bool × Fin n × Fin n)) (A : V →L[ℂ] V) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) : Set.EqOn (Rw w (fun y => A (f y))) (fun y => A (Rw w f y)) (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_post (bs p) A (Rw_smooth w hf) hx)

theorem Om_post (A : V →L[ℂ] V) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Om (fun y => A (f y)) g = A (Om f g) := by
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_post A _ _ hf hg, map_smul, map_add (f := _)]

theorem Om_translate {x : Mat n} (hx : x ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Om (fun y => f (y * x)) g = Om f (g * x) := by
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_right _ _ hx hf hg]

theorem translate_smooth {x : Mat n} (hx : x ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (fun y => f (y * x)) (GLs n) :=
  hf.comp (mulR x).contDiff.contDiffOn (mapsTo_mulR hx)

end Words

section Sob

variable [MeasurableSpace (G n)] {μ : Measure (G n)} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem val_mem (y : G n) : y.val ∈ GLs n := GlobalTheory.CompanionTheory.RCalc.ByParts.val_mem_GLs y

theorem sob_congr {f h : Mat n → V} (hf : Sob μ f) (e : Set.EqOn f h (GLs n)) : Sob μ h :=
  ⟨hf.1.congr fun _ hx => (e hx).symm, fun w =>
    MemLp.ae_eq (ae_of_all _ fun y => Rw_congr w e (val_mem y)) (hf.2 w)⟩

theorem sob_add {f h : Mat n → V} (hf : Sob μ f) (hh : Sob μ h) : Sob μ (f + h) :=
  ⟨hf.1.add hh.1, fun w => MemLp.ae_eq (ae_of_all _ fun y => (Rw_add w hf.1 hh.1 (val_mem y)).symm)
    ((hf.2 w).add (hh.2 w))⟩

theorem sob_smul (c : ℂ) {f : Mat n → V} (hf : Sob μ f) : Sob μ (c • f) :=
  ⟨hf.1.const_smul c, fun w => MemLp.ae_eq (ae_of_all _ fun y => (Rw_smul w c hf.1 (val_mem y)).symm)
    ((hf.2 w).const_smul c)⟩

theorem sob_zero {f : Mat n → V} (hf : Sob μ f) : Sob μ (0 : Mat n → V) := by
  simpa using sob_smul (0 : ℂ) hf

theorem sob_sum {ι : Type} (s : Finset ι) {f₀ : Mat n → V} (h₀ : Sob μ f₀) {F : ι → Mat n → V}
    (hF : ∀ i, Sob μ (F i)) : Sob μ (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sob_zero h₀
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact sob_add (hF a) ih

theorem sob_Rw (w : List (Bool × Fin n × Fin n)) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Rw w f) :=
  ⟨Rw_smooth w hf.1, fun w' => by rw [Rw_append]; exact hf.2 _⟩

theorem sob_bs (p : Bool × Fin n × Fin n) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Rd (bs p) f) :=
  sob_Rw [p] hf

theorem sob_Rd (X : Mat n) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Rd X f) := by
  refine sob_congr (f := ∑ p : Bool × Fin n × Fin n, ((GlobalTheory.CompanionTheory.SobSecK.cf X p : ℝ) : ℂ) • Rd (bs p) f)
    (sob_sum _ hf fun p => sob_smul _ (sob_bs p hf)) fun g _ => ?_
  rw [Rd_sum_cf X f g]
  simp only [Finset.sum_apply, Pi.smul_apply]

theorem sob_Eu (s : Bool) (a b : Fin n) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Eu s a b f) :=
  sob_smul _ (sob_add (sob_Rd _ hf) (sob_smul _ (sob_Rd _ hf)))

theorem sob_Epow (s : Bool) (m : ℕ) {f : Mat n → V} (hf : Sob μ f) : ∀ a b, Sob μ (Epow s m a b f) := by
  induction m with
  | zero =>
    intro a b
    by_cases hab : a = b
    · simpa [Epow, hab] using hf
    · simpa [Epow, hab] using sob_zero hf
  | succ m ih =>
    intro a b
    exact sob_sum _ hf fun c => sob_Eu s a c (ih c b)

theorem sob_gel (s : Bool) (m : ℕ) {f : Mat n → V} (hf : Sob μ f) : Sob μ (gel s m f) :=
  sob_sum _ hf fun a => sob_Epow s m hf a a

theorem sob_Om {f : Mat n → V} (hf : Sob μ f) : Sob μ (Om f) :=
  sob_smul _ (sob_add (sob_gel _ _ hf) (sob_gel _ _ hf))

theorem sob_post (A : V →L[ℂ] V) {f : Mat n → V} (hf : Sob μ f) : Sob μ (fun y => A (f y)) :=
  ⟨post_smooth A hf.1, fun w => MemLp.ae_eq (ae_of_all _ fun y => (Rw_post w A hf.1 (val_mem y)).symm)
    (A.comp_memLp' (hf.2 w))⟩

variable [BorelSpace (G n)] [μ.IsHaarMeasure]

theorem memLp_translate (hU : Unimod) (h : G n) {F : Mat n → V} (hF : MemLp (fun y : G n => F y.val) 2 μ) :
    MemLp (fun y : G n => F (y.val * h.val)) 2 μ := by
  haveI := (hU n μ).1
  exact hF.comp_measurePreserving (measurePreserving_mul_right μ h)

theorem translate_memLp (hU : Unimod) (h : G n) (w : List (Bool × Fin n × Fin n)) :
    ∀ F : Mat n → V, Sob μ F → MemLp (fun y : G n => Rw w (fun z => F (z * h.val)) y.val) 2 μ := by
  induction w using List.reverseRecOn with
  | nil => exact fun F hF => memLp_translate hU h (hF.2 [])
  | append_singleton w p ih =>
    intro F hF
    rw [← Rw_append [p] w]
    have e : Set.EqOn (Rw [p] fun z => F (z * h.val)) (fun z => Rd (h.val⁻¹ * bs p * h.val) F (z * h.val)) (GLs n) :=
      fun g hg => Rd_translate (bs p) (val_mem h) hF.1 hg
    exact MemLp.ae_eq (ae_of_all _ fun y => (Rw_congr w e (val_mem y)).symm) (ih _ (sob_Rd _ hF))

theorem sob_translate (hU : Unimod) (h : G n) {F : Mat n → V} (hF : Sob μ F) : Sob μ (fun y => F (y * h.val)) :=
  ⟨translate_smooth (val_mem h) hF.1, fun w => translate_memLp hU h w F hF⟩

end Sob

theorem sobOps : SobOps := by
  intro n _ _ μ _ V _ _ _ hU _ f hf
  refine ⟨sob_Om hf, fun w => sob_Rw w hf, fun w g hg => Rw_Om w hf.1 hg, fun a f' hf' => ⟨sob_add (sob_smul a hf) hf', ?_⟩,
    fun h A => ⟨sob_post A (sob_translate hU h hf), fun g hg => ?_⟩⟩
  · intro g hg
    have hs : ContDiffOn ℝ ∞ (a • f) (GLs n) := hf.1.const_smul a
    have e1 := GlobalTheory.CompanionTheory.WaveK.Lin.Om_add hs hf'.1 hg
    have e2 := GlobalTheory.CompanionTheory.WaveK.Lin.Om_smul a hf.1 hg
    simp only [Pi.add_apply, Pi.smul_apply] at e1 e2
    rw [e1, e2]
  · rw [Om_post A (translate_smooth (val_mem h) hf.1) hg, Om_translate (val_mem h) hf.1 hg]

end GlobalTheory.CompanionTheory.SobOpsPf
end
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.Dblock.SzFinProof

theorem finite_one_lt_norm_cW {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : Ad E) :
    {w : HeightOneSpectrum (𝓞 E) | 1 < ‖cW w a‖}.Finite := by
  delta PositivityTheory.Rg.BcB.cW GlobalTheory.CuspRep.pLoc GlobalTheory.CuspRep.pFin
  have h := RestrictedProduct.eventually _ _ (RingHom.snd (InfiniteAdeleRing E) (Af E) a)
  refine (Filter.eventually_cofinite.mp h).subset ?_
  intro w hw
  simp only [Set.mem_ofPred_eq, RingHom.comp_apply, RestrictedProduct.evalRingHom_apply] at hw ⊢
  intro hmem
  exact absurd hw (not_lt.mpr (Valued.toNormedField.norm_le_one_iff.mpr
    ((IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp hmem)))

theorem szFin : SzFin := by
  intro E _ _ _ ι κ _ _ A
  refine (Set.Finite.biUnion (s := (Set.univ : Set (ι × κ))) Set.finite_univ
    fun p _ => finite_one_lt_norm_cW (A p.1 p.2)).subset ?_
  intro w hw
  change 1 < ⨆ p : ι × κ, ‖(A.map (PositivityTheory.Rg.BcB.cW w)) p.1 p.2‖ at hw
  rcases isEmpty_or_nonempty (ι × κ) with hι | hι
  · rw [Real.iSup_of_isEmpty] at hw
    exact absurd hw (by norm_num)
  · obtain ⟨p, hp⟩ := exists_lt_of_lt_ciSup hw
    exact Set.mem_biUnion (Set.mem_univ p) hp

end GlobalTheory.CompanionTheory.Dblock.SzFinProof
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.sign_cone_weight_indicator : ∀ m : ℕ, ∀ (y : (Fin m → SignType) → ℝ) a, PosFam y → gam y a = Set.indicator {a | ∀ e, sdot e a ≤ y e} 1 a := by
  first | exact @GlobalTheory.CompanionTheory.ChainInd.gam_eq_indicator | exact GlobalTheory.CompanionTheory.ChainInd.gam_eq_indicator | (intros; apply GlobalTheory.CompanionTheory.ChainInd.gam_eq_indicator <;> assumption)
end

section

open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

theorem _root_.GlobalTheory.T.sign_cone_weight_support_bound : ∀ m : ℕ, ∀ (y : (Fin m → SignType) → ℝ) (M : ℝ) a, (∀ e, |y e| ≤ M) → gam y a ≠ 0 → ∀ i, |a i| ≤ 2 * M := by
  first | exact @GlobalTheory.CompanionTheory.SignChain.gam_support | exact GlobalTheory.CompanionTheory.SignChain.gam_support | (intros; apply GlobalTheory.CompanionTheory.SignChain.gam_support <;> assumption)
end

section


theorem _root_.GlobalTheory.T.iteratedDeriv_gaussian_exponential_at_zero : ∀ (m n : ℕ) (X : Fin n → ℝ) (v : Fin m → Fin n → ℂ), Differentiable ℂ (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) ∧ ∀ r : ℕ, iteratedDeriv r (fun z : ℂ => (Complex.exp ((m : ℂ) * z * ∑ j, (X j : ℂ)) * Complex.exp (-(2 * Real.pi : ℂ) * ∑ a, ∑ j, Complex.exp (2 * z * X j) * ((‖v a j‖ ^ 2 : ℝ) : ℂ)))) 0 = PositivityTheory.Rg.Sw.evX ((PositivityTheory.Rg.Sw.dil (m := m) (2 * Real.pi) X ^ r) 1) v * PositivityTheory.Rg.Sw.gs (2 * Real.pi) v := by
  first | exact @GlobalTheory.CompanionTheory.DilFam.main | exact GlobalTheory.CompanionTheory.DilFam.main | (intros; apply GlobalTheory.CompanionTheory.DilFam.main <;> assumption)
end
