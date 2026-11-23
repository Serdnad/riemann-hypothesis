module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle181
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaOperatorEqCasimirSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle205
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle213
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle210
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle211
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle206
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle217
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle214
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris
public import GroundTheory.PAdicHodge.Bundle011
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle212
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

set_option maxSynthPendingDepth 1
open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing


theorem _root_.GlobalTheory.T.omega_operator_eq_casimir_sum : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a d : ℕ)
    (b : Module.Basis (Fin d) ℝ (AutomorphicForm.isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ),
    (∀ i, ε i = 1 ∨ ε i = -1) →
    (∀ i j, AutomorphicForm.archTraceForm E a (b i) (b j) = if i = j then ε i else 0) →
    GlobalTheory.CompanionTheory.HCRep.omegaOp (⇑b) ε = (2 : ℂ) • ∑ w : InfinitePlace E,
      (Formalism.REAL.Cas (Eop (a := a) w.embedding) +
        Formalism.REAL.Cas (Eop (a := a) (ComplexEmbedding.conjugate w.embedding))) := by
  first | exact @GlobalTheory.CompanionTheory.HCRep.TraceCas.omegaOp_eq_two_cas | exact GlobalTheory.CompanionTheory.HCRep.TraceCas.omegaOp_eq_two_cas | (intros; apply GlobalTheory.CompanionTheory.HCRep.TraceCas.omegaOp_eq_two_cas <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.smooth_time_right_derivatives_commute : ∀ {n : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (u : ℝ → Mat n → W), Sm u → Sm (dt u) ∧ (∀ X : Mat n, Sm (Rt X u)) ∧ (∀ s, ContDiffOn ℝ ∞ (u s) (GLs n)) ∧ (∀ y ∈ GLs n, ContDiff ℝ ∞ fun s => u s y) ∧ ∀ (X : Mat n) (s : ℝ), ∀ y ∈ GLs n, dt (Rt X u) s y = Rr X (dt u s) y := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.sm_calculus | exact GlobalTheory.CompanionTheory.WaveSpd.sm_calculus | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.sm_calculus <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.WaveSpd.OmDec

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem fderiv_sub_apply' {f h : E → F} {g : E} (hf : DifferentiableAt ℝ f g)
    (hh : DifferentiableAt ℝ h g) (v : E) :
    fderiv ℝ (f - h) g v = fderiv ℝ f g v - fderiv ℝ h g v := by
  rw [fderiv_sub hf hh]; rfl

theorem fderiv_zero_apply' (g v : E) : fderiv ℝ (0 : E → F) g v = 0 := by
  have h : fderiv ℝ (0 : E → F) g = 0 := by
    simpa using (fderiv_const_apply (𝕜 := ℝ) (x := g) (0 : F))
  rw [h]; rfl

end General

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_sub_left (A B : Mat n) (h : Mat n → V) : Rd (A - B) h = Rd A h - Rd B h := by
  funext g; simp [Rd, mul_sub]

theorem Rd_zero (X : Mat n) : Rd X (0 : Mat n → V) = 0 := by
  funext g
  exact fderiv_zero_apply' _ _

theorem Rd_add_right (X : Mat n) {a b : Mat n → V} (ha : ContDiffOn ℝ ∞ a (GLs n))
    (hb : ContDiffOn ℝ ∞ b (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (a + b) g = Rd X a g + Rd X b g :=
  RCalc.fderiv_add_apply' (RCalc.differentiableAt_of_smooth ha hg)
    (RCalc.differentiableAt_of_smooth hb hg) _

theorem Rd_sub_right (X : Mat n) {a b : Mat n → V} (ha : ContDiffOn ℝ ∞ a (GLs n))
    (hb : ContDiffOn ℝ ∞ b (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (a - b) g = Rd X a g - Rd X b g :=
  fderiv_sub_apply' (RCalc.differentiableAt_of_smooth ha hg)
    (RCalc.differentiableAt_of_smooth hb hg) _

theorem Rd_smul_right (c : ℂ) (X : Mat n) {a : Mat n → V} (ha : ContDiffOn ℝ ∞ a (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (c • a) g = c • Rd X a g :=
  RCalc.fderiv_csmul_apply (RCalc.differentiableAt_of_smooth ha hg) c _

theorem Eu_zero (s : Bool) (a b : Fin n) : Eu s a b (0 : Mat n → V) = 0 := by
  simp [Eu, Rd_zero]

theorem Epow_one (s : Bool) (c a : Fin n) (f : Mat n → V) : Epow s 1 c a f = Eu s c a f := by
  show ∑ d, Eu s c d (Epow s 0 d a f) = _
  rw [Finset.sum_eq_single a]
  · simp [Epow]
  · intro d _ hd
    simp [Epow, hd, Eu_zero]
  · simp

theorem gel_two (s : Bool) (f : Mat n → V) :
    gel s 2 f = ∑ a, ∑ c, Eu s a c (Eu s c a f) := by
  refine Finset.sum_congr rfl fun a _ => ?_
  show ∑ c, Eu s a c (Epow s 1 c a f) = _
  simp only [Epow_one]

theorem Eu_Eu_apply (s : Bool) (a b c d : Fin n) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) (ε : ℂ)
    (hε : ε = if s then -Complex.I else Complex.I) :
    Eu s a b (Eu s c d f) g = (1 / 4 : ℂ) •
      (Rd (Matrix.single a b 1) (Rd (Matrix.single c d 1) f) g
        + ε • Rd (Matrix.single a b 1) (Rd (Matrix.single c d Complex.I) f) g
        + ε • Rd (Matrix.single a b Complex.I) (Rd (Matrix.single c d 1) f) g
        + (ε * ε) • Rd (Matrix.single a b Complex.I) (Rd (Matrix.single c d Complex.I) f) g) := by
  have hX := RCalc.Rd_contDiffOn (Matrix.single c d (1 : ℂ)) hf
  have hY := RCalc.Rd_contDiffOn (Matrix.single c d Complex.I) hf
  have hS : ContDiffOn ℝ ∞ (ε • Rd (Matrix.single c d Complex.I) f) (GLs n) := hY.const_smul ε
  have key : ∀ Z : Mat n, Rd Z (Eu s c d f) g =
      (1 / 2 : ℂ) • (Rd Z (Rd (Matrix.single c d 1) f) g
        + ε • Rd Z (Rd (Matrix.single c d Complex.I) f) g) := by
    intro Z
    have e : Eu s c d f = (1 / 2 : ℂ) • (Rd (Matrix.single c d 1) f
        + ε • Rd (Matrix.single c d Complex.I) f) := by
      rw [hε]; rfl
    have hA : ContDiffOn ℝ ∞ (Rd (Matrix.single c d 1) f + ε • Rd (Matrix.single c d Complex.I) f)
        (GLs n) := hX.add hS
    rw [e, Rd_smul_right _ _ hA hg, Rd_add_right _ hX hS hg, Rd_smul_right _ _ hY hg]
  have e2 : Eu s a b (Eu s c d f) g = (1 / 2 : ℂ) • (Rd (Matrix.single a b 1) (Eu s c d f) g
      + ε • Rd (Matrix.single a b Complex.I) (Eu s c d f) g) := by
    rw [hε]; rfl
  rw [e2, key, key]
  module

theorem Eu_pair_apply (a b c d : Fin n) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Eu true a b (Eu true c d f) g + Eu false a b (Eu false c d f) g = (1 / 2 : ℂ) •
      (Rd (Matrix.single a b 1) (Rd (Matrix.single c d 1) f) g
        - Rd (Matrix.single a b Complex.I) (Rd (Matrix.single c d Complex.I) f) g) := by
  rw [Eu_Eu_apply true a b c d hf hg (-Complex.I) (by simp),
    Eu_Eu_apply false a b c d hf hg Complex.I (by simp)]
  have h1 : (-Complex.I) * (-Complex.I) = -1 := by simp
  have h2 : Complex.I * Complex.I = -1 := by simp
  rw [h1, h2]
  module

theorem Om_apply {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Om f g = ∑ a, ∑ b, (Rd (Matrix.single a b 1) (Rd (Matrix.single b a 1) f) g
        - Rd (Matrix.single a b Complex.I) (Rd (Matrix.single b a Complex.I) f) g) := by
  have h : Om f g = (2 : ℂ) • ∑ a, ∑ b,
      (Eu true a b (Eu true b a f) g + Eu false a b (Eu false b a f) g) := by
    simp only [Om, gel_two, Pi.smul_apply, Pi.add_apply, Finset.sum_apply, Finset.sum_add_distrib]
  rw [h]
  simp only [Eu_pair_apply _ _ _ _ hf hg, Finset.smul_sum, smul_smul]
  norm_num

theorem Rd_sq_add (A B : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Rd (A + B) (Rd (A + B) f) g =
      Rd A (Rd A f) g + Rd A (Rd B f) g + Rd B (Rd A f) g + Rd B (Rd B f) g := by
  have dA := RCalc.Rd_contDiffOn A hf
  have dB := RCalc.Rd_contDiffOn B hf
  rw [RCalc.Rd_add_left A B f, RCalc.Rd_add_left A B (Rd A f + Rd B f)]
  simp only [Pi.add_apply]
  rw [Rd_add_right _ dA dB hg, Rd_add_right _ dA dB hg]
  abel

theorem Rd_sq_sub (A B : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Rd (A - B) (Rd (A - B) f) g =
      Rd A (Rd A f) g - Rd A (Rd B f) g - Rd B (Rd A f) g + Rd B (Rd B f) g := by
  have dA := RCalc.Rd_contDiffOn A hf
  have dB := RCalc.Rd_contDiffOn B hf
  rw [Rd_sub_left A B f, Rd_sub_left A B (Rd A f - Rd B f)]
  simp only [Pi.sub_apply]
  rw [Rd_sub_right _ dA dB hg, Rd_sub_right _ dA dB hg]
  abel

theorem sum_Ix (F : Ix n → V) :
    ∑ p, F p = ∑ a, ∑ b, (F (true, a, b) + F (false, a, b)) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fintype.sum_prod_type, Finset.sum_add_distrib]

theorem sum_reindex (x y : Fin n → Fin n → V) :
    ∑ a, ∑ b, (x a b - y a b) = (1 / 4 : ℂ) • ∑ a, ∑ b,
      ((2 : ℂ) • (x a b + x b a) - (2 : ℂ) • (y a b + y b a)) := by
  have hx : ∑ a, ∑ b, x b a = ∑ a, ∑ b, x a b := Finset.sum_comm
  have hy : ∑ a, ∑ b, y b a = ∑ a, ∑ b, y a b := Finset.sum_comm
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.smul_sum]
  rw [hx, hy]
  module

theorem Om_eq_squares {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (f : Mat n → V) :
    ContDiffOn ℝ ∞ f (GLs n) → ∀ g ∈ GLs n,
      Om f g = (1 / 4 : ℂ) • ∑ p : Ix n, Rd (hm p) (Rd (hm p) f) g
        - (1 / 4 : ℂ) • ∑ p : Ix n, Rd (sk p) (Rd (sk p) f) g := by
  intro hf g hg
  rw [Om_apply hf hg, sum_reindex, sum_Ix, sum_Ix, ← smul_sub]
  congr 1
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  have e1 : hm (n := n) (true, a, b) = Matrix.single a b 1 + Matrix.single b a 1 := by simp [hm]
  have e2 : hm (n := n) (false, a, b) =
      Matrix.single a b Complex.I - Matrix.single b a Complex.I := by simp [hm]
  have e3 : sk (n := n) (true, a, b) = Matrix.single a b 1 - Matrix.single b a 1 := by simp [sk]
  have e4 : sk (n := n) (false, a, b) =
      Matrix.single a b Complex.I + Matrix.single b a Complex.I := by simp [sk]
  rw [e1, e2, e3, e4, Rd_sq_add _ _ hf hg, Rd_sq_sub _ _ hf hg, Rd_sq_add _ _ hf hg,
    Rd_sq_sub _ _ hf hg]
  module

end GlobalTheory.CompanionTheory.WaveSpd.OmDec
end
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.integral_right_derivative_zero_alt : RCalc → ∀ {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (Ψ : Mat n → ℝ), ContDiffOn ℝ ∞ Ψ (GLs n) → (∃ R : ℝ, ∀ y ∈ GLs n, R < lg y → Ψ y = 0) → ∀ X : Mat n, ∫ y : G n, Rr X Ψ y.val ∂μ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.integral_Rr_eq_zero | exact GlobalTheory.CompanionTheory.WaveSpd.integral_Rr_eq_zero | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.integral_Rr_eq_zero <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveSpd
open PositivityTheory.RgTw (Mat G)
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.translated_length_bounded_derivative : LgFacts → ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ GLs n, ContDiffOn ℝ ∞ (fun y : Mat n => lg (x⁻¹ * y)) (GLs n) ∧ (∀ R : ℝ, IsCompact {y : G n | lg (x⁻¹ * y.val) ≤ R}) ∧ ∀ y ∈ GLs n, ∀ p : Ix n, |fderiv ℝ (fun y : Mat n => lg (x⁻¹ * y)) y (y * hm p)| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.lg_left_facts | exact GlobalTheory.CompanionTheory.WaveSpd.lg_left_facts | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.lg_left_facts <;> assumption)
end

section

noncomputable section

open Matrix
open scoped ContDiff
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveK.Uniq

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Eu_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a b : Fin n) :
    ContDiffOn ℝ ∞ (Eu s a b f) (GLs n) := by
  have h := fun X : Mat n => GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf
  unfold Eu
  exact ((h _).add (contDiffOn_const.smul (h _))).const_smul _

theorem Epow_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, ContDiffOn ℝ ∞ (Epow s m a b f) (GLs n) := by
  induction m with
  | zero =>
    intro a b
    by_cases hab : a = b
    · simpa [Epow, hab] using hf
    · simp only [Epow, if_neg hab]
      exact contDiffOn_const (c := (0 : V))
  | succ m ih =>
    intro a b
    have e : Epow s (m + 1) a b f = fun x => ∑ c, Eu s a c (Epow s m c b f) x := by
      ext x
      simp only [Epow, Finset.sum_apply]
    rw [e]
    exact ContDiffOn.sum fun c _ => Eu_smooth (ih c b) s a c

theorem Epow_sub {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s m a b (f - f')) (Epow s m a b f - Epow s m a b f') (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.sub_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.CompanionTheory.WaveAll.Eu_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs (ih c b) s a c hx]
    exact GlobalTheory.CompanionTheory.WaveAll.Eu_sub (Epow_smooth hf s m c b) (Epow_smooth hf' s m c b) s a c hx

theorem gel_sub {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) : Set.EqOn (gel s m (f - f')) (gel s m f - gel s m f') (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.sub_apply, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => Epow_sub hf hf' s m a a hx

theorem Om_sub {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) :
    Set.EqOn (Om (f - f')) (Om f - Om f') (GLs n) := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, gel_sub hf hf' _ _ hx, smul_sub, smul_add]
  abel

theorem wave_sub {E : KMod n} {u v : ℝ → Mat n → E.V} (hu : IsWave E u) (hv : IsWave E v) :
    IsWave E (u - v) := by
  refine ⟨?_, fun t => ⟨?_, ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · exact hu.1.sub hv.1
  · exact (hu.2.1 t).1.sub (hv.2.1 t).1
  · intro g hg k
    simp only [Pi.sub_apply, (hu.2.1 t).2 g hg k, (hv.2.1 t).2 g hg k, map_sub]
  · have h1 := (GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg).contDiffAt (x := t)
    have h2 := (GlobalTheory.CompanionTheory.WaveAll.wave_line hv hg).contDiffAt (x := t)
    have e : (fun s => (u - v) s g) = (fun s => u s g) - fun s => v s g := rfl
    rw [e, iteratedDeriv_sub (h1.of_le (WithTop.coe_le_coe.2 le_top)) (h2.of_le (WithTop.coe_le_coe.2 le_top)),
      hu.2.2.1 t g hg, hv.2.2.1 t g hg]
    exact (Om_sub (hu.2.1 t).1 (hv.2.1 t).1 hg).symm
  · have h1 : DifferentiableAt ℝ (fun s => u s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg).differentiable (by simp)).differentiableAt
    have h2 : DifferentiableAt ℝ (fun s => v s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hv hg).differentiable (by simp)).differentiableAt
    have e : (fun s => (u - v) s g) = (fun s => u s g) - fun s => v s g := rfl
    rw [e, deriv_sub h1 h2, hu.2.2.2 g hg, hv.2.2.2 g hg, sub_zero]

theorem waveUniq_of_waveSpeed : WaveSpeed → WaveUniq := by
  intro hS n E u v hu hv h0 t x hx
  obtain ⟨c, hc⟩ := hS n
  have hw := wave_sub hu hv
  have h := hc E (u - v) hw t x hx fun y hy _ => by
    simp only [Pi.sub_apply]
    exact sub_eq_zero.2 (h0 _ (GlobalTheory.CompanionTheory.WaveAll.mul_mem_GLs hx hy))
  exact sub_eq_zero.1 h

end GlobalTheory.CompanionTheory.WaveK.Uniq
end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.CompanionTheory.LTPer

section Abs

variable {B : Type} [CommRing B]

def ltIter (ϖ : B) (q n : ℕ) : B → B := (fun x => ϖ * x + x ^ q)^[n]

def Near (S : Subring B) (ϖ : B) (J : Ideal B) (m : ℕ) (x : B) : Prop :=
  ∃ s ∈ S, x - ϖ ^ m * s ∈ J

structure PerEnv (S : Subring B) (F : ℕ → Ideal B) (ϖ : B) : Prop where
  top : F 0 = ⊤
  anti : ∀ k, F (k + 1) ≤ F k
  mul_le : ∀ a b, F a * F b ≤ F (a + b)
  sep : ∀ x, (∀ k, x ∈ F k) → x = 0
  complete : ∀ x : ℕ → B, (∀ k, x (k + 1) - x k ∈ F k) → ∃ t, ∀ k, t - x k ∈ F k
  unit : IsUnit ϖ
  mem : ϖ ∈ S
  sumS : ∀ s : ℕ → B, (∀ n, s n ∈ S) → ∃ r ∈ S, ∀ N, ∃ a ∈ S,
    r - ∑ n ∈ Finset.range N, ϖ ^ n * s n = ϖ ^ N * a
  closed : ∀ k, ∀ x ∈ S, (∀ m, Near S ϖ (F k) m x) → x ∈ F k

def Tends (S : Subring B) (F : ℕ → Ideal B) (ϖ : B) (x : ℕ → B) (t : B) : Prop :=
  ∀ k, ∃ c : ℕ, ∀ m, ∃ N, ∀ n ≥ N, Near S ϖ (F k) m (ϖ ^ c * (x n - t))

def EvalMod {R : Type} [CommRing R] (S : Subring B) (F : ℕ → Ideal B) (ϖ : B) (h : R →+* B)
    (φ : PowerSeries R) (y r : B) (m : ℕ) : Prop :=
  ∀ k, ∃ D, ∀ D' ≥ D, Near S ϖ (F k) m
    ((∑ i ∈ Finset.range D', h (PowerSeries.coeff i φ) * y ^ i) - r)

end Abs

section Conc

variable (l : ℕ) [Fact l.Prime]

open scoped Formalism.Per6

abbrev Tl : Type := PreTilt ↥(GroundTheory.PAdicHodge.normInteger ℂ_[l]) l

abbrev Wl : Type := WittVector l (Tl l)

def wB : Wl l →+* Formalism.Per6.BdRp l :=
  GroundTheory.PAdicHodge.wittToBDeRhamPlus ↥(GroundTheory.PAdicHodge.normInteger ℂ_[l]) l

def tch (x : Tl l) : Formalism.Per6.BdRp l := wB l (WittVector.teichmuller l x)

def rB : Om l →+* Formalism.Per6.BdRp l := (GroundTheory.PAdicHodge.algClToBdR l).toRingHom

def thB : Formalism.Per6.BdRp l →+* ℂ_[l] := (GroundTheory.PAdicHodge.thetaAlgHom l).toRingHom

def FB (k : ℕ) : Ideal (Formalism.Per6.BdRp l) := RingHom.ker (thB l) ^ k

variable {l}

def actB (g : GQ l) : Formalism.Per6.BdRp l →+* Formalism.Per6.BdRp l := MulSemiringAction.toRingHom _ _ (Formalism.Per6.toBot g)

def actT (g : GQ l) : Tl l →+* Tl l :=
  GroundTheory.PAdicHodge.preTiltMap l (GroundTheory.PAdicHodge.galCp (Formalism.Per6.toBot g) : ℂ_[l] →+* ℂ_[l])
    (GroundTheory.PAdicHodge.AInf.norm_galCp_toRingHom (Formalism.Per6.toBot g))

abbrev qOf {K : FinExt l} (π : ↥(OL K)) : ℕ := Nat.card (↥(OL K) ⧸ Ideal.span {π})

def oB (K : FinExt l) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) : ↥(OL K) →+* Formalism.Per6.BdRp l :=
  (rB l).comp ((μ : ↥K.1 →+* Om l).comp (algebraMap ↥(OL K) ↥K.1))

def LTData (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l) : Prop :=
  Irreducible π ∧ z 0 = 0 ∧ z 1 ≠ 0 ∧
    (∀ n, z (n + 1) ^ Nat.card (↥(OL K) ⧸ Ideal.span {π}) +
      (((π : ↥K.1) : Om l)) * z (n + 1) = z n) ∧
    ∀ (g : ↥(GK K)) (φ : PowerSeries ↥(OL K)), PowerSeries.constantCoeff φ = 0 →
      ((PowerSeries.coeff 1 φ : ↥(OL K)) : ↥K.1) = ((χ g : (↥K.1)ˣ) : ↥K.1) →
      PowerSeries.subst φ (GlobalTheory.CompanionTheory.LTHodge.ltSeries π) = PowerSeries.subst (GlobalTheory.CompanionTheory.LTHodge.ltSeries π) φ →
      ∀ n, HasSum (fun k : ℕ => (((PowerSeries.coeff k φ : ↥(OL K)) : ↥K.1) : Om l) * z n ^ k)
        ((g : GQ l) (z n))

def PrePer (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (t : Formalism.Per6.BdRp l) : Prop :=
  t ≠ 0 ∧ (∀ (g : GQ l) (hg : g ∈ GK K), (∀ x : ↥K.1, g (μ x) = μ x) →
      actB g t = rB l (μ ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1)) * t) ∧
    (μ = K.1.val → thB l t = 0)

end Conc

end GlobalTheory.CompanionTheory.LTPer
end
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.bump_convolution_support : ∀ (g g' : ℝ → ℝ) (T T' : ℝ), IsBump g T → IsBump g' T' → IsBump (gconv g g') (T + T') := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.isBump_gconv | exact GlobalTheory.CompanionTheory.WaveMult.isBump_gconv | (intros; apply GlobalTheory.CompanionTheory.WaveMult.isBump_gconv <;> assumption)
end
