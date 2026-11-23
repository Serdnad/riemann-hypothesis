module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.IntSmooth
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.SymZeroCommFrame
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle045
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle218
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence
public import GroundTheory.AutomorphicForms.InductionParabolic
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle053
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle219
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
public import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle216
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle038

@[expose] public section

section

noncomputable section

open Matrix Finset

namespace GlobalTheory.CompanionTheory.LgBound

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lgCpt : PositivityTheory.RgBcC.VC.LgCpt := by
  intro n R
  haveI : ProperSpace (Mat n) := FiniteDimensional.proper ℂ _
  let f : G n → ℝ := fun y => 1 + ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2)
  have hinv : ∀ y : G n, (y.val)⁻¹ = (y⁻¹).val := fun y => (Matrix.coe_units_inv y).symm
  have hc1 : Continuous fun y : G n => y.val := Units.continuous_val
  have hc2 : Continuous fun y : G n => (y⁻¹).val := Units.continuous_val.comp continuous_inv
  have hfc : Continuous f := by
    refine continuous_const.add (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_)
    exact ((hc1.matrix_elem a b).norm.pow 2).add ((hc2.matrix_elem a b).norm.pow 2)
  have hsum : ∀ y : G n, 0 ≤ ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) := fun y =>
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by positivity
  have hfpos : ∀ y, 0 < f y := fun y => by
    have := hsum y
    show 0 < 1 + _
    linarith
  have hS : {y : G n | lg y.val ≤ R} = f ⁻¹' Set.Iic (Real.exp R) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Iic, lg, hinv]
    exact Real.log_le_iff_le_exp (hfpos y)
  rw [hS]
  have hclosed : IsClosed (f ⁻¹' Set.Iic (Real.exp R)) := isClosed_Iic.preimage hfc

  set r : ℝ := Real.exp R with hr
  have hr0 : 0 ≤ r + 1 := by positivity
  have hterm : ∀ y : G n, f y ≤ r → ∀ a b, ‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2 ≤ r := by
    intro y hy a b
    have h1 : ‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2 ≤ ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) :=
      Finset.single_le_sum (f := fun b => ‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2)
        (fun b _ => by positivity) (Finset.mem_univ b)
    have h2 : ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) ≤ ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) :=
      Finset.single_le_sum (f := fun a => ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2))
        (fun a _ => Finset.sum_nonneg fun b _ => by positivity) (Finset.mem_univ a)
    have h3 : 1 + ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y⁻¹).val a b‖ ^ 2) ≤ r := hy
    linarith
  have hle : ∀ t : ℝ, 0 ≤ t → t ^ 2 ≤ r → t ≤ r + 1 := by
    intro t ht h
    nlinarith [sq_nonneg (t - 1)]
  have hb1 : ∀ y : G n, f y ≤ r → ‖y.val‖ ≤ r + 1 := by
    intro y hy
    refine (Matrix.norm_le_iff hr0).2 fun a b => hle _ (norm_nonneg _) ?_
    have := hterm y hy a b
    have h2 : 0 ≤ ‖(y⁻¹).val a b‖ ^ 2 := by positivity
    linarith
  have hb2 : ∀ y : G n, f y ≤ r → ‖(y⁻¹).val‖ ≤ r + 1 := by
    intro y hy
    refine (Matrix.norm_le_iff hr0).2 fun a b => hle _ (norm_nonneg _) ?_
    have := hterm y hy a b
    have h2 : 0 ≤ ‖y.val a b‖ ^ 2 := by positivity
    linarith
  have hball : IsCompact (Metric.closedBall (0 : Mat n) (r + 1)) := isCompact_closedBall _ _
  have hK : IsCompact ((fun p : Mat n × Mat n => (p.1, MulOpposite.op p.2)) ''
      (Metric.closedBall (0 : Mat n) (r + 1) ×ˢ Metric.closedBall (0 : Mat n) (r + 1))) :=
    (hball.prod hball).image (continuous_fst.prodMk (MulOpposite.continuous_op.comp continuous_snd))
  have hpre := (Units.isClosedEmbedding_embedProduct (α := Mat n)).isCompact_preimage hK
  refine hpre.of_isClosed_subset hclosed ?_
  intro y hy
  refine ⟨(y.val, (y⁻¹).val), ⟨?_, ?_⟩, rfl⟩
  · simpa using hb1 y hy
  · simpa using hb2 y hy

end GlobalTheory.CompanionTheory.LgBound
end
end

section

noncomputable section

open Matrix
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.WaveInv

open PositivityTheory.RgBcC PositivityTheory.RgBcC.VC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem gls_mul {h x : Mat n} (hh : h ∈ GLs n) (hx : x ∈ GLs n) : h * x ∈ GLs n := by
  simp only [GLs, Set.mem_ofPred_eq, Matrix.det_mul] at *
  exact mul_ne_zero hh hx

theorem gls_val (v : G n) : v.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).mp v.isUnit).ne_zero

theorem contDiff_mulLeft (h : Mat n) : ContDiff ℝ ∞ (fun x : Mat n => h * x) :=
  (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ h)).contDiff

theorem contDiffOn_translate {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) {h : Mat n} (hh : h ∈ GLs n) :
    ContDiffOn ℝ ∞ (fun y => f (h * y)) (GLs n) :=
  hf.comp (contDiff_mulLeft h).contDiffOn fun _ hy => gls_mul hh hy

theorem gel_sub (hG : GelComm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (s : Bool) (m : ℕ)
    {f₁ f₂ : Mat n → V} (h₁ : ContDiffOn ℝ ∞ f₁ (GLs n)) (h₂ : ContDiffOn ℝ ∞ f₂ (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) :
    gel s m (fun y => f₁ y - f₂ y) g = gel s m f₁ g - gel s m f₂ g := by
  have hP : ContDiffOn ℝ ∞ (fun y => (f₁ y, f₂ y)) (GLs n) := h₁.prodMk h₂
  have c := ((hG n (V × V) V s m (fun y => (f₁ y, f₂ y)) hP).2 g hg).2.2
  have a : gel s m f₁ g = _ := c (ContinuousLinearMap.fst ℂ V V)
  have b : gel s m f₂ g = _ := c (ContinuousLinearMap.snd ℂ V V)
  have d : gel s m (fun y => f₁ y - f₂ y) g = _ :=
    c (ContinuousLinearMap.fst ℂ V V - ContinuousLinearMap.snd ℂ V V)
  rw [d, a, b]
  rfl

theorem Om_sub (hG : GelComm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f₁ f₂ : Mat n → V} (h₁ : ContDiffOn ℝ ∞ f₁ (GLs n)) (h₂ : ContDiffOn ℝ ∞ f₂ (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) :
    Om (fun y => f₁ y - f₂ y) g = Om f₁ g - Om f₂ g := by
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_sub hG _ _ h₁ h₂ hg]
  module

theorem Om_translate (hG : GelComm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {h g : Mat n} (hh : h ∈ GLs n) (hg : g ∈ GLs n) :
    Om (fun y => f (h * y)) g = Om f (h * g) := by
  have c := fun s m => (((hG n V V s m f hf).2 g hg).2.1 h hh).1
  simp only [Om, Pi.smul_apply, Pi.add_apply, c]

theorem contDiff_line {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u) {y : Mat n} (hy : y ∈ GLs n) :
    ContDiff ℝ ∞ (fun s => u s y) := by
  have hl : ContDiff ℝ ∞ (fun s : ℝ => (s, y)) := contDiff_id.prodMk contDiff_const
  have := hu.1.comp hl.contDiffOn (s := Set.univ) fun s _ => ⟨Set.mem_univ _, hy⟩
  exact contDiffOn_univ.mp this

theorem isWave_translate_sub (hG : GelComm) {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u)
    {h : Mat n} (hh : h ∈ GLs n) : IsWave E (fun t x => u t (h * x) - u t x) := by
  have hs : ∀ t, ContDiffOn ℝ ∞ (u t) (GLs n) := fun t => (hu.2.1 t).1
  refine ⟨?_, fun t => ⟨(contDiffOn_translate (hs t) hh).sub (hs t), fun g hg k => ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · have hmap : ContDiff ℝ ∞ (fun p : ℝ × Mat n => (p.1, h * p.2)) :=
      contDiff_fst.prodMk ((contDiff_mulLeft h).comp contDiff_snd)
    have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => Function.uncurry u (p.1, h * p.2)) (Set.univ ×ˢ GLs n) :=
      hu.1.comp hmap.contDiffOn fun p hp => ⟨Set.mem_univ _, gls_mul hh hp.2⟩
    exact h1.sub hu.1
  · have e₁ := (hu.2.1 t).2 (h * g) (gls_mul hh hg) k
    have e₂ := (hu.2.1 t).2 g hg k
    simp only [← mul_assoc, e₁, e₂, map_sub]
  · have hc₁ : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun s => u s (h * g)) t :=
      (contDiff_infty.mp (contDiff_line hu (gls_mul hh hg)) 2).contDiffAt
    have hc₂ : ContDiffAt ℝ ((2 : ℕ) : WithTop ℕ∞) (fun s => u s g) t :=
      (contDiff_infty.mp (contDiff_line hu hg) 2).contDiffAt
    rw [iteratedDeriv_fun_sub hc₁ hc₂, hu.2.2.1 t _ (gls_mul hh hg), hu.2.2.1 t _ hg,
      Om_sub hG (contDiffOn_translate (hs t) hh) (hs t) hg, Om_translate hG (hs t) hh hg]
  · have d₁ : DifferentiableAt ℝ (fun s => u s (h * g)) 0 :=
      ((contDiff_line hu (gls_mul hh hg)).differentiable (by simp)).differentiableAt
    have d₂ : DifferentiableAt ℝ (fun s => u s g) 0 :=
      ((contDiff_line hu hg).differentiable (by simp)).differentiableAt
    rw [deriv_fun_sub d₁ d₂, hu.2.2.2 _ (gls_mul hh hg), hu.2.2.2 _ hg, sub_zero]

theorem waveN : PositivityTheory.RgBcC.VC.WaveN := by
  intro hEx hSp hG n E W₁ W₂ f hf hN
  obtain ⟨u, hu, h0⟩ := hEx n E f hf
  refine ⟨u, hu, h0, fun t v hv x hx => ?_⟩
  obtain ⟨c, hc⟩ := hSp n
  have hvG := gls_val v
  have hz := hc E _ (isWave_translate_sub hG hu hvG) t x hx fun y hy _ => by
    have hxy := gls_mul hx hy
    rw [h0 _ (gls_mul hvG hxy), h0 _ hxy, hN v hv _ hxy, sub_self]
  exact sub_eq_zero.mp hz

end GlobalTheory.CompanionTheory.WaveInv
end
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.WaveField

open PositivityTheory.RgBcC PositivityTheory.RgBcC.VC
open PositivityTheory.RgTw (Mat G th tw hb)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contDiffOn_clm_apply {M V : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M]
    [NormedAddCommGroup V] [NormedSpace ℂ V] {s : Set M} {B : M → (V →L[ℂ] V)} {f : M → V}
    (hB : ContDiffOn ℝ ∞ B s) (hf : ContDiffOn ℝ ∞ f s) :
    ContDiffOn ℝ ∞ (fun x => B x (f x)) s := by
  have hL : ContDiffOn ℝ ∞ (fun x => (B x).restrictScalars ℝ) s :=
    (ContinuousLinearMap.restrictScalarsL ℂ V V ℝ ℝ).contDiff.comp_contDiffOn hB
  exact hL.clm_apply hf

theorem deriv_clm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (B : V →L[ℂ] V) {h : ℝ → V} (hh : Differentiable ℝ h) (s : ℝ) :
    deriv (fun r => B (h r)) s = B (deriv h s) :=
  ((B.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hh s).hasDerivAt).deriv

theorem iteratedDeriv_two_clm {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (B : V →L[ℂ] V) {f : ℝ → V} (hf : ContDiff ℝ ∞ f) (t : ℝ) :
    iteratedDeriv 2 (fun s => B (f s)) t = B (iteratedDeriv 2 f t) := by
  have h1 : Differentiable ℝ f := hf.differentiable (by simp)
  have h2 : Differentiable ℝ (deriv f) :=
    (contDiff_infty_iff_deriv.1 hf).2.differentiable (by simp)
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have : deriv (fun s => B (f s)) = fun s => B (deriv f s) := funext (deriv_clm B h1)
  rw [this, deriv_clm B h2, iteratedDeriv_succ, iteratedDeriv_one]

theorem waveA : WaveA := by
  intro hGF n E W₁ W₂ hW A u hA hQ hu hN
  obtain ⟨hs, hce, heq, hd0⟩ := hu
  have hline : ∀ g ∈ GLs n, ContDiff ℝ ∞ (fun s => u s g) := by
    intro g hg
    have hc : ContDiff ℝ ∞ (fun s : ℝ => (s, g)) := contDiff_id.prodMk contDiff_const
    exact contDiffOn_univ.1 (hs.comp hc.contDiffOn fun s _ => ⟨trivial, hg⟩)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => A p.2) (Set.univ ×ˢ GLs n) :=
      hA.1.comp contDiff_snd.contDiffOn fun p hp => hp.2
    exact contDiffOn_clm_apply h1 hs
  · intro t
    refine ⟨contDiffOn_clm_apply hA.1 (hce t).1, fun g hg k => ?_⟩
    show A (g * k.1) (u t (g * k.1)) = E.ρ k⁻¹ (A g (u t g))
    rw [(hce t).2 g hg k, hA.2 g hg k]
    simp only [ContinuousLinearMap.mul_apply]
    have : E.ρ k (E.ρ k⁻¹ (u t g)) = u t g := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul]; simp
    rw [this]
  · intro t g hg
    rw [iteratedDeriv_two_clm (A g) (hline g hg), heq t g hg]
    have hG := fun s => hGF n E.V W₁ W₂ hW A (u t) hA.1 (hce t).1 hQ (hN t) s 2 g hg
    simp only [Om, Pi.smul_apply, Pi.add_apply, hG, map_smul, map_add (f := _)]
  · intro g hg
    rw [deriv_clm (A g) ((hline g hg).differentiable (by simp)), hd0 g hg, map_zero]

end GlobalTheory.CompanionTheory.WaveField
end
end

section

noncomputable section

open MeasureTheory Matrix Topology Filter
open scoped ContDiff ENNReal ComplexOrder Pointwise Kronecker

namespace GlobalTheory.CompanionTheory.ConeLin

open PositivityTheory.RgTw (Mat G hb)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.ConeHaar

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem hOf_add (v w : Fin n × Fin n → ℝ) : hOf (v + w) = hOf v + hOf w := by
  simp only [hOf, Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]

theorem hOf_smul (c : ℝ) (v : Fin n × Fin n → ℝ) : hOf (c • v) = (c : ℂ) • hOf v := by
  simp only [hOf, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.smul_sum, smul_smul]

theorem hOf_single (q : Fin n × Fin n) : hOf (Pi.single q (1 : ℝ)) = hb q := by
  classical
  simp [hOf, Pi.single_apply, ite_smul]

theorem hOf_herm (v : Fin n × Fin n → ℝ) : (hOf v)ᴴ = hOf v := by
  simp [hOf, conjTranspose_sum, conjTranspose_smul, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose]

theorem re_trace (P : Mat n) (hP : Pᴴ = P) (p : Fin n × Fin n) :
    (((P * hb p).trace).re : ℂ) = (P * hb p).trace := by
  apply Complex.conj_eq_iff_re.1
  have h1 : star (P * hb p).trace = (P * hb p).trace := by
    rw [← Matrix.trace_conjTranspose, conjTranspose_mul, hP, GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose,
      Matrix.trace_mul_comm]
  exact h1

theorem hOf_re (P : Mat n) (hP : Pᴴ = P) : hOf (fun p => ((P * hb p).trace).re) = P := by
  have h := (GlobalTheory.CompanionTheory.TopClass.hbB n).sum_repr P
  simp only [GlobalTheory.CompanionTheory.TopClass.hbB_repr, GlobalTheory.CompanionTheory.TopClass.hbB_apply] at h
  conv_rhs => rw [← h]
  simp only [hOf, re_trace P hP]

theorem conj_herm (g P : Mat n) (hP : Pᴴ = P) : (g * P * gᴴ)ᴴ = g * P * gᴴ := by
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hP, Matrix.mul_assoc]

def realMap (g : Mat n) : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ) where
  toFun v p := ((g * hOf v * gᴴ * hb p).trace).re
  map_add' v w := by
    funext p
    simp [hOf_add, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
  map_smul' c v := by
    funext p
    simp [hOf_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul]

def cplxMap (g : Mat n) : Mat n →ₗ[ℂ] Mat n where
  toFun X := g * X * gᴴ
  map_add' X Y := by simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by simp [Matrix.mul_smul, Matrix.smul_mul]

theorem cplxMap_apply (g X : Mat n) : cplxMap g X = g * X * gᴴ := rfl

theorem hOf_realMap (g : Mat n) (v : Fin n × Fin n → ℝ) : hOf (realMap g v) = g * hOf v * gᴴ :=
  hOf_re _ (conj_herm g _ (hOf_herm v))

theorem det_realMap (g : Mat n) : ((LinearMap.det (realMap g) : ℝ) : ℂ) = LinearMap.det (cplxMap g) := by
  rw [← LinearMap.det_toMatrix' (realMap g), ← GlobalTheory.CompanionTheory.TopClass.det_of_trace (cplxMap g),
    ← Matrix.det_transpose (Matrix.of _)]
  have h : ((LinearMap.toMatrix' (realMap g)).det : ℂ) =
      Complex.ofRealHom (LinearMap.toMatrix' (realMap g)).det := rfl
  rw [h, RingHom.map_det]
  congr 1
  ext p q
  have hh : (g * hb q * gᴴ)ᴴ = g * hb q * gᴴ := conj_herm g _ (GlobalTheory.CompanionTheory.TwistHomotopy.hb_conjTranspose q)
  have := re_trace _ hh p
  simpa [LinearMap.toMatrix'_apply, realMap, hOf_single, cplxMap_apply, Pi.single_apply] using this

theorem det_cplxMap (g : Mat n) : LinearMap.det (cplxMap g) = (g.det * star g.det) ^ n := by
  have h : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin n) (Fin n)) (Matrix.stdBasis ℂ (Fin n) (Fin n)) (cplxMap g) =
      g ⊗ₖ g.map star := by
    ext ⟨i, j⟩ ⟨k, l⟩
    have hr : ∀ X : Mat n, (Matrix.stdBasis ℂ (Fin n) (Fin n)).repr X (i, j) = X i j := by
      intro X
      simp [Matrix.stdBasis]
    rw [LinearMap.toMatrix_apply, hr]
    simp [cplxMap_apply, Matrix.stdBasis_eq_single, Matrix.mul_apply, Matrix.single_apply, ite_and]
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis ℂ (Fin n) (Fin n)), h, Matrix.det_kronecker]
  have h2 : (g.map star).det = star g.det := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose]
    rfl
  rw [h2, Fintype.card_fin, mul_pow]

theorem cone_lin (n : ℕ) (g : Mat n) (_hg : g.det ≠ 0) :
    ∃ T : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ),
      (∀ v, hOf (T v) = g * hOf v * gᴴ) ∧ LinearMap.det T = ‖g.det‖ ^ (2 * n) := by
  refine ⟨realMap g, hOf_realMap g, ?_⟩
  apply Complex.ofReal_injective
  rw [det_realMap, det_cplxMap]
  have : g.det * star g.det = ((‖g.det‖ ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.mul_conj' g.det
  rw [this, pow_mul]
  simp

end GlobalTheory.CompanionTheory.ConeLin
end
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.kernel_action_equivariant : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (κ : Mat n → (E.V →L[ℂ] E.V)) (f : Mat n → E.V), KReg κ → ContinuousOn f (GLs n) → (∀ y ∈ GLs n, ∀ k₁ : Matrix.unitaryGroup (Fin n) ℂ, κ (k₁.1 * y) = E.ρ k₁ * κ y) → ContinuousOn (act μ E κ f) (GLs n) ∧ ∀ x ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, act μ E κ f (x * k₂.1) = E.ρ k₂⁻¹ (act μ E κ f x) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.act_kReg_section | exact GlobalTheory.CompanionTheory.WaveMult.act_kReg_section | (intros; apply GlobalTheory.CompanionTheory.WaveMult.act_kReg_section <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.kernel_adjoint_regular : LgFacts → ∀ (n : ℕ) (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)), KReg k → (∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, k (k₁.1 * y * k₂.1) = E.ρ k₁ * k y * E.ρ k₂) → (haveI := FiniteDimensional.complete ℂ E.V; KReg (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) ∧ ∀ y ∈ GLs n, ∀ k₁ k₂ : Matrix.unitaryGroup (Fin n) ℂ, ContinuousLinearMap.adjoint (k (k₁.1 * y * k₂.1)⁻¹) = E.ρ k₁ * ContinuousLinearMap.adjoint (k y⁻¹) * E.ρ k₂) := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.adjoint_kernel_reg | exact GlobalTheory.CompanionTheory.WaveMult.adjoint_kernel_reg | (intros; apply GlobalTheory.CompanionTheory.WaveMult.adjoint_kernel_reg <;> assumption)
end

section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem _root_.GlobalTheory.T.kernel_multiplier_linear : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) {ι ι' : Type} [Fintype ι] [Fintype ι'] (c : ι → ℂ) (c' : ι' → ℂ) (ks : ι → Mat n → (E.V →L[ℂ] E.V)) (ks' : ι' → Mat n → (E.V →L[ℂ] E.V)) (k k' : Mat n → (E.V →L[ℂ] E.V)), (∀ i, KReg (ks i)) → (∀ j, KReg (ks' j)) → (∀ y ∈ GLs n, k y = ∑ i, c i • ks i y) → (∀ y ∈ GLs n, k' y = ∑ j, c' j • ks' j y) → ∀ x ∈ GLs n, conv μ E k k' x = ∑ i, ∑ j, (c i * c' j) • conv μ E (ks i) (ks' j) x := by
  first | exact @GlobalTheory.CompanionTheory.WaveMult.conv_eq_sum_of_kernels | exact GlobalTheory.CompanionTheory.WaveMult.conv_eq_sum_of_kernels | (intros; apply GlobalTheory.CompanionTheory.WaveMult.conv_eq_sum_of_kernels <;> assumption)
end

section


theorem _root_.GlobalTheory.T.length_function_facts_hold : PositivityTheory.RgBcC.LgFacts := by
  first | exact @GlobalTheory.CompanionTheory.LengthGL.lgFacts | exact GlobalTheory.CompanionTheory.LengthGL.lgFacts | (intros; apply GlobalTheory.CompanionTheory.LengthGL.lgFacts <;> assumption)
end

section


theorem _root_.GlobalTheory.T.wave_solution_existence : PositivityTheory.RgBcC.AsmEx := by
  first | exact @GlobalTheory.CompanionTheory.WaveAll.asmEx | exact GlobalTheory.CompanionTheory.WaveAll.asmEx | (intros; apply GlobalTheory.CompanionTheory.WaveAll.asmEx <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open GlobalTheory.SmGL
open GroundTheory.Automorphic.Parabolic (levi parabolicInd jacquetRep JacquetModule sqrtModular leviIncl cellLeviSub normInducing unipotentRadical)
open GroundTheory.Automorphic.Iwasawa (blockUpper)
open GroundTheory.Automorphic (permGL indRep)
open DoubleCoset (doubleCoset)

theorem _root_.GlobalTheory.T.jacquet_module_equiv : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ) (γ : Fin n → ℕ) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (π : Representation ℂ (GL (Fin n) F) V) (π' : Representation ℂ (GL (Fin n) F) V'), π.Equiv π' → Nonempty ((jacquetRep F n γ π).Equiv (jacquetRep F n γ π')) := by
  first | exact @GlobalTheory.CompanionTheory.JacquetEquiv.nonempty_jacquetRep_equiv | exact GlobalTheory.CompanionTheory.JacquetEquiv.nonempty_jacquetRep_equiv | (intros; apply GlobalTheory.CompanionTheory.JacquetEquiv.nonempty_jacquetRep_equiv <;> assumption)
end

section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

theorem _root_.GlobalTheory.T.chart_lattice_span_twist_shift : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ), IsArithVar (mCoordIdeal y) (D + 1) → Birational y → ∃ (e : K → ℕ) (c : Ω), c ≠ 0 ∧ ∀ (a : K → ℤ) (τ : ℕ), ∀ s ∈ Submodule.span ℚ (chartLatNm y a τ : Set Ω), c * s ∈ chartLatQ y ((τ : ℤ) • a + fun k => (e k : ℤ)) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Conductor.exists_conductor_section | exact GlobalTheory.CompanionTheory.Conductor.exists_conductor_section | (intros; apply GlobalTheory.CompanionTheory.Conductor.exists_conductor_section <;> assumption)
end
