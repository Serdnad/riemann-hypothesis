module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle232
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GLMatrixDerivatives.Bundle003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle249
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle250
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle212
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterOperatorCommutesIntegral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CenterOperatorPreservesWave
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle215
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveTimeAverageIsWave
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle236
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle251
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle252
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle253
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

noncomputable section

open MeasureTheory Matrix Finset Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.SecBd

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem val_mem (y : G n) : y.val ∈ GLs n := (Matrix.isUnits_det_units y).ne_zero

theorem basis_true_eq_single (a c : Fin n) : bs (true, a, c) = Matrix.single a c (1 : ℂ) := by simp [bs]

theorem bs_f (a c : Fin n) : bs (false, a, c) = Matrix.single a c Complex.I := by simp [bs]

theorem Rw_append {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (w : List (Bool × Fin n × Fin n))
    (p : Bool × Fin n × Fin n) (f : Mat n → V) : Rw (w ++ [p]) f = Rw w (Rd (bs p) f) := by
  induction w with
  | nil => rfl
  | cons q w ih =>
    show Rd (bs q) (Rw (w ++ [p]) f) = Rd (bs q) (Rw w (Rd (bs p) f))
    rw [ih]

theorem Rd_sub {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (X X' : Mat n) (f : Mat n → V) (g : Mat n) :
    Rd (X - X') f g = Rd X f g - Rd X' f g := by
  simp [Rd, mul_sub]

theorem Rd_add {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (X X' : Mat n) (f : Mat n → V) (g : Mat n) :
    Rd (X + X') f g = Rd X f g + Rd X' f g := by
  simp [Rd, mul_add]

theorem single_conj (a b : Fin n) (c : ℂ) : (Matrix.single a b c)ᴴ = Matrix.single b a (star c) := by
  ext x y
  simp only [Matrix.conjTranspose_apply, Matrix.single_apply]
  by_cases h1 : a = y <;> by_cases h2 : b = x <;> simp [h1, h2]

theorem skewY (a c : Fin n) :
    (Matrix.single a c (1 : ℂ) - Matrix.single c a (1 : ℂ) : Mat n)ᴴ = -(Matrix.single a c (1 : ℂ) - Matrix.single c a 1) := by
  simp [Matrix.conjTranspose_sub, single_conj]

theorem skewZ (a c : Fin n) :
    (Matrix.single a c Complex.I + Matrix.single c a Complex.I : Mat n)ᴴ =
      -(Matrix.single a c Complex.I + Matrix.single c a Complex.I) := by
  simp [Matrix.conjTranspose_add, single_conj, Matrix.single_neg, add_comm]

section L2

variable [MeasurableSpace (G n)] (μ : Measure (G n)) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem cls_eq {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) : cls μ f = h.toLp _ := dif_pos h

theorem cls_ae {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) : cls μ f =ᵐ[μ] fun y => f y.val := by
  rw [cls_eq μ h]
  exact h.coeFn_toLp

theorem cls_congr {f f' : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) (e : ∀ g ∈ GLs n, f g = f' g) :
    cls μ f = cls μ f' := by
  have e' : (fun y : G n => f y.val) = fun y => f' y.val := funext fun y => e _ (val_mem y)
  have h' : MemLp (fun y : G n => f' y.val) 2 μ := e' ▸ h
  rw [cls_eq μ h, cls_eq μ h']
  exact MemLp.toLp_congr h h' (by rw [e'])

theorem cls_sub {f f' : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) (h' : MemLp (fun y : G n => f' y.val) 2 μ) :
    cls μ (fun g => f g - f' g) = cls μ f - cls μ f' := by
  rw [cls_eq μ h, cls_eq μ h', cls_eq μ (h.sub h')]
  exact MemLp.toLp_sub h h'

theorem cls_sum {ι : Type} (s : Finset ι) (F : ι → Mat n → V)
    (h : ∀ i ∈ s, MemLp (fun y : G n => F i y.val) 2 μ) :
    MemLp (fun y : G n => ∑ i ∈ s, F i y.val) 2 μ ∧ cls μ (fun g => ∑ i ∈ s, F i g) = ∑ i ∈ s, cls μ (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : MemLp (fun _ : G n => (0 : V)) 2 μ := MemLp.zero
    refine ⟨by simpa using h0, ?_⟩
    simp only [Finset.sum_empty]
    rw [cls_eq μ h0]
    exact MemLp.toLp_zero h0
  | insert i s hi ih =>
    obtain ⟨m, e⟩ := ih fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hi' := h i (Finset.mem_insert_self i s)
    simp only [Finset.sum_insert hi]
    refine ⟨hi'.add m, ?_⟩
    rw [← e, cls_eq μ hi', cls_eq μ (f := fun g => ∑ i ∈ s, F i g) m,
      cls_eq μ (f := fun g => F i g + ∑ i ∈ s, F i g) (hi'.add m)]
    exact MemLp.toLp_add hi' m

theorem norm_le_of_ae {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) (x : Lp V 2 μ) (C : V →L[ℂ] V)
    (e : ∀ᵐ y ∂μ, x y = C (f (y : G n).val)) : ‖x‖ ≤ ‖C‖ * ‖cls μ f‖ := by
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [e, cls_ae μ h] with y h1 h2
  rw [h1, h2]
  exact C.le_opNorm _

end L2

theorem pol_sub {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (u v : H) :
    -(⟪v, u⟫_ℂ).re ≤ ‖u - v‖ ^ 2 / 4 := by
  have h1 := @norm_add_sq ℂ _ _ _ _ u v
  have h2 := @norm_sub_sq ℂ _ _ _ _ u v
  have h3 := @inner_re_symm ℂ _ _ _ _ u v
  simp only [RCLike.re_eq_complex_re] at h1 h2 h3
  nlinarith [sq_nonneg ‖u + v‖]

theorem pol_add {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (u v : H) :
    (⟪v, u⟫_ℂ).re ≤ ‖u + v‖ ^ 2 / 4 := by
  have h1 := @norm_add_sq ℂ _ _ _ _ u v
  have h2 := @norm_sub_sq ℂ _ _ _ _ u v
  have h3 := @inner_re_symm ℂ _ _ _ _ u v
  simp only [RCLike.re_eq_complex_re] at h1 h2 h3
  nlinarith [sq_nonneg ‖u - v‖]

section Main

variable [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem sob_Rd (hR : RCalc) {f : Mat n → V} (hS : Sob μ f) (p : Bool × Fin n × Fin n) : Sob μ (Rd (bs p) f) :=
  ⟨((hR n).1 V f hS.1).1 _, fun w => by
    have := hS.2 (w ++ [p])
    rwa [Rw_append] at this⟩

theorem mem1 {f : Mat n → V} (hS : Sob μ f) (p : Bool × Fin n × Fin n) :
    MemLp (fun y : G n => Rd (bs p) f y.val) 2 μ := hS.2 [p]

theorem mem0 {f : Mat n → V} (hS : Sob μ f) : MemLp (fun y : G n => f y.val) 2 μ := hS.2 []

end Main

theorem secBound (hI : IbpSob) : SecBound := by
  intro n _ _ μ _ E hL hU hR
  choose BY hBY using fun a c : Fin n => GlobalTheory.CompanionTheory.WaveSpd.rd_skew_eq_const E _ (skewY a c)
  choose BZ hBZ using fun a c : Fin n => GlobalTheory.CompanionTheory.WaveSpd.rd_skew_eq_const E _ (skewZ a c)
  refine ⟨∑ a, ∑ c, (‖BY a c‖ ^ 2 + ‖BZ a c‖ ^ 2) / 4, fun f hS hsec => ?_⟩
  have hCE : f ∈ CE E := ⟨hS.1, hsec⟩
  set x := cls μ f with hx
  have hf0 := mem0 μ hS

  have hd : ∀ p q : Bool × Fin n × Fin n, MemLp (fun y : G n => Rd (bs p) (Rd (bs q) f) y.val) 2 μ := fun p q =>
    mem1 μ (sob_Rd μ hR hS q) p
  have hip : ∀ p q : Bool × Fin n × Fin n, ⟪cls μ (Rd (bs p) (Rd (bs q) f)), x⟫_ℂ =
      -⟪cls μ (Rd (bs q) f), cls μ (Rd (bs p) f)⟫_ℂ := fun p q =>
    hI n μ E.V hL hU hR _ _ (sob_Rd μ hR hS q) hS (bs p)

  let T : Fin n → Fin n → Mat n → E.V := fun a c g =>
    Rd (bs (true, a, c)) (Rd (bs (true, c, a)) f) g - Rd (bs (false, a, c)) (Rd (bs (false, c, a)) f) g
  have hT : ∀ a c, MemLp (fun y : G n => T a c y.val) 2 μ := fun a c => (hd _ _).sub (hd _ _)
  have hOm : ∀ g ∈ GLs n, Om f g = ∑ a, ∑ c, T a c g := by
    intro g hg
    rw [GlobalTheory.CompanionTheory.Casimir.omFormula n E.V f hS.1 g hg]
    simp only [T, basis_true_eq_single, bs_f]
  have hsumc : ∀ a, MemLp (fun y : G n => ∑ c, T a c y.val) 2 μ ∧
      cls μ (fun g => ∑ c, T a c g) = ∑ c, cls μ (T a c) := fun a =>
    cls_sum μ _ (T a) fun c _ => hT a c
  have hsum := cls_sum μ Finset.univ (fun a g => ∑ c, T a c g) fun a _ => (hsumc a).1
  have hcls : cls μ (Om f) = ∑ a, ∑ c, cls μ (T a c) := by
    have h1 : cls μ (fun g => ∑ a, ∑ c, T a c g) = cls μ (Om f) :=
      cls_congr μ hsum.1 fun g hg => (hOm g hg).symm
    rw [← h1, hsum.2]
    exact Finset.sum_congr rfl fun a _ => (hsumc a).2

  have hterm : ∀ a c, (⟪cls μ (T a c), x⟫_ℂ).re ≤ (‖BY a c‖ ^ 2 + ‖BZ a c‖ ^ 2) / 4 * ‖x‖ ^ 2 := by
    intro a c
    set u := cls μ (Rd (bs (true, a, c)) f) with hu
    set u' := cls μ (Rd (bs (true, c, a)) f) with hu'
    set v := cls μ (Rd (bs (false, a, c)) f) with hv
    set v' := cls μ (Rd (bs (false, c, a)) f) with hv'
    have e1 : (⟪cls μ (T a c), x⟫_ℂ).re = -(⟪u', u⟫_ℂ).re + (⟪v', v⟫_ℂ).re := by
      have : cls μ (T a c) = _ := cls_sub μ (hd (true, a, c) (true, c, a)) (hd (false, a, c) (false, c, a))
      rw [this, inner_sub_left, hip, hip]
      simp [hu, hu', hv, hv']
    have b1 : ‖u - u'‖ ≤ ‖BY a c‖ * ‖x‖ := by
      refine norm_le_of_ae μ hf0 _ _ ?_
      filter_upwards [Lp.coeFn_sub u u', cls_ae μ (mem1 μ hS (true, a, c)), cls_ae μ (mem1 μ hS (true, c, a))] with y h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3, ← hBY a c f hCE _ (val_mem y), Rd_sub, basis_true_eq_single, basis_true_eq_single]
    have b2 : ‖v + v'‖ ≤ ‖BZ a c‖ * ‖x‖ := by
      refine norm_le_of_ae μ hf0 _ _ ?_
      filter_upwards [Lp.coeFn_add v v', cls_ae μ (mem1 μ hS (false, a, c)), cls_ae μ (mem1 μ hS (false, c, a))] with y h1 h2 h3
      rw [h1, Pi.add_apply, h2, h3, ← hBZ a c f hCE _ (val_mem y), Rd_add, bs_f, bs_f]
    have p1 := pol_sub u u'
    have p2 := pol_add v v'
    have s1 : ‖u - u'‖ ^ 2 ≤ (‖BY a c‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) b1 2
    have s2 : ‖v + v'‖ ^ 2 ≤ (‖BZ a c‖ * ‖x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) b2 2
    rw [e1]
    nlinarith
  rw [hcls, sum_inner, Complex.re_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [sum_inner, Complex.re_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun c _ => hterm a c

theorem secBound_main : SecBound := secBound GlobalTheory.T.sobolev_integration_by_parts

end GlobalTheory.CompanionTheory.SecBd
end
end

section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

theorem l2_limit_eq_pointwise_limit : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (a : ℕ → Mat n → V) (b : Mat n → V) (x : Lp V 2 μ), (∀ k, MemLp (fun y : G n => a k y.val) 2 μ) → Tendsto (fun k => cls μ (a k)) atTop (𝓝 x) → (∀ z ∈ GLs n, Tendsto (fun k => a k z) atTop (𝓝 (b z))) → MemLp (fun y : G n => b y.val) 2 μ ∧ cls μ b = x := by
  intro n _ _ μ _ V _ _ _ a b x hm hc hp
  have hin : TendstoInMeasure μ (fun k => (cls μ (a k) : G n → V)) atTop (x : G n → V) :=
    tendstoInMeasure_of_tendsto_Lp hc
  obtain ⟨ns, hns, hae⟩ := hin.exists_seq_tendsto_ae
  have hall : ∀ᵐ y ∂μ, ∀ k, (cls μ (a k) : G n → V) y = a k y.val :=
    ae_all_iff.2 fun k => coe_cls μ (hm k)
  have hbx : (fun y : G n => b y.val) =ᵐ[μ] x := by
    filter_upwards [hae, hall] with y h1 h2
    have hy : y.val ∈ GLs n := by
      have hu : IsUnit y.val.det := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
      exact hu.ne_zero
    have h3 : Tendsto (fun k => a (ns k) y.val) atTop (𝓝 (b y.val)) :=
      (hp y.val hy).comp hns.tendsto_atTop
    have h4 : Tendsto (fun k => a (ns k) y.val) atTop (𝓝 (x y)) := by
      simpa only [h2] using h1
    exact tendsto_nhds_unique h3 h4
  exact cls_of_ae μ hbx

end GlobalTheory.CompanionTheory.PresSobA
end
end

section


theorem _root_.GlobalTheory.T.height_bound_facts : PositivityTheory.RgBcC.LfSt.HbFacts := by
  first | exact @GlobalTheory.CompanionTheory.HbBasis.hbFacts | exact GlobalTheory.CompanionTheory.HbBasis.hbFacts | (intros; apply GlobalTheory.CompanionTheory.HbBasis.hbFacts <;> assumption)
end

section

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult

theorem integral_smul_integral_shift {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V] {g g' : ℝ → ℝ} {T T' : ℝ} (hg : IsBump g T) (hg' : IsBump g' T')
    {φ : ℝ → V} (hφ : Continuous φ) :
    ∫ t, (g t : ℂ) • ∫ s, (g' s : ℂ) • φ (t + s) = ∫ r, (gconv g g' r : ℂ) • φ r := by
  have cg : Continuous g := hg.1.continuous
  have cg' : Continuous g' := hg'.1.continuous
  let F : ℝ → ℝ → V := fun t r => ((g t * g' (r - t) : ℝ) : ℂ) • φ r
  have hFc : Continuous (Function.uncurry F) := by
    have : Function.uncurry F = fun p : ℝ × ℝ => ((g p.1 * g' (p.2 - p.1) : ℝ) : ℂ) • φ p.2 := rfl
    rw [this]
    fun_prop
  have hFs : HasCompactSupport (Function.uncurry F) := by
    refine HasCompactSupport.intro
      (K := Set.Icc (-|T|) |T| ×ˢ Set.Icc (-(|T| + |T'|)) (|T| + |T'|))
      (isCompact_Icc.prod isCompact_Icc) ?_
    rintro ⟨t, r⟩ h
    by_cases ht : T < |t|
    · simp [Function.uncurry, F, hg.2.2 t ht]
    · by_cases hr : T' < |r - t|
      · simp [Function.uncurry, F, hg'.2.2 _ hr]
      · exfalso
        apply h
        have h1 : |t| ≤ |T| := (not_lt.mp ht).trans (le_abs_self T)
        have h2 : |r - t| ≤ |T'| := (not_lt.mp hr).trans (le_abs_self T')
        have h3 : |r| ≤ |t| + |r - t| := by simpa using abs_add_le t (r - t)
        exact ⟨abs_le.mp h1, abs_le.mp (by linarith)⟩
  have hFi : Integrable (Function.uncurry F) (volume.prod volume) :=
    hFc.integrable_of_hasCompactSupport hFs
  have hL : ∀ t, (g t : ℂ) • ∫ s, (g' s : ℂ) • φ (t + s) = ∫ r, F t r := by
    intro t
    rw [← integral_add_left_eq_self (fun r => F t r) t, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [F, add_sub_cancel_left, Complex.ofReal_mul, mul_smul]
  have hR : ∀ r, (gconv g g' r : ℂ) • φ r = ∫ t, F t r := by
    intro r
    simp only [F, gconv]
    rw [integral_smul_const, integral_complex_ofReal]
  simp only [hL, hR]
  exact integral_integral_swap hFi

theorem wave_compose : RCalc → WaveSpeed → ∀ (n : ℕ) (E : KMod n) (u : ℝ → Mat n → E.V)
    (w w' : List (Bool × ℕ)) (g g' : ℝ → ℝ) (T T' : ℝ), IsWave E u → IsBump g T → IsBump g' T' →
    ∃ v : ℝ → Mat n → E.V, IsWave E v ∧
      (∀ x ∈ GLs n, v 0 x = zOp w' (fun x' => ∫ t, (g' t : ℂ) • u t x') x) ∧
      ∀ x ∈ GLs n, zOp w (fun x' => ∫ t, (g t : ℂ) • v t x') x =
        zOp (w ++ w') (fun x' => ∫ t, (gconv g g' t : ℂ) • u t x') x := by
  intro hR hS n E u w w' g g' T T' hu hg hg'
  have : CompleteSpace E.V := FiniteDimensional.complete ℂ E.V
  have hu' : IsWave E (fun t => zOp w' (u t)) := WaveZ.isWave_zOp hR n E u w' hu
  have hv := WaveAvg.isWave_avg hS n E (fun t => zOp w' (u t)) g' T' hu' hg'
  refine ⟨_, hv, ?_, ?_⟩
  · intro x hx
    have h := ZOpAvg.zOp_avg n u g' T' w' hu.1 hg' x hx
    simp only [zero_add]
    exact h.symm
  · intro x hx
    have hb := isBump_gconv g g' T T' hg hg'
    have hφ : ∀ x' ∈ GLs n, Continuous fun r => zOp w' (u r) x' := fun x' hx' =>
      hu'.1.continuousOn.comp_continuous (f := fun r : ℝ => (r, x')) (by fun_prop)
        (fun r => ⟨trivial, hx'⟩)
    have h1 : ∀ x' ∈ GLs n, (∫ t, (g t : ℂ) • ∫ s, (g' s : ℂ) • zOp w' (u (t + s)) x') =
        ∫ r, (gconv g g' r : ℂ) • zOp w' (u r) x' := fun x' hx' =>
      integral_smul_integral_shift hg hg' (hφ x' hx')
    rw [zOp_agree_GLs n w _ _ h1 x hx,
      ZOpAvg.zOp_avg n (fun t => zOp w' (u t)) (gconv g g') (T + T') w hu'.1 hb x hx,
      ZOpAvg.zOp_avg n u (gconv g g') (T + T') (w ++ w') hu.1 hb x hx]
    simp only [Swap.zOp_append]

end GlobalTheory.CompanionTheory.WaveMult
end
end

section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG

theorem _root_.GlobalTheory.T.average_membership : AvgMem := by
  first | exact @GlobalTheory.CompanionTheory.EisMirGen.avgMem | exact GlobalTheory.CompanionTheory.EisMirGen.avgMem | (intros; apply GlobalTheory.CompanionTheory.EisMirGen.avgMem <;> assumption)
end

section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG

theorem _root_.GlobalTheory.T.height_term_good : HGood := by
  first | exact @GlobalTheory.CompanionTheory.RgEisHGood.hGood | exact GlobalTheory.CompanionTheory.RgEisHGood.hGood | (intros; apply GlobalTheory.CompanionTheory.RgEisHGood.hGood <;> assumption)
end

section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG

theorem _root_.GlobalTheory.T.test_function_spherical_K : StdGood → BdetLaw → TestFun → TestK := by
  first | exact @GlobalTheory.CompanionTheory.EisTestK.testK | exact GlobalTheory.CompanionTheory.EisTestK.testK | (intros; apply GlobalTheory.CompanionTheory.EisTestK.testK <;> assumption)
end

section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG

theorem _root_.GlobalTheory.T.zeta_value_at_one : EpMain → ZetaOne := by
  first | exact @GlobalTheory.CompanionTheory.EisMG.zetaOne_of_epMain | exact GlobalTheory.CompanionTheory.EisMG.zetaOne_of_epMain | (intros; apply GlobalTheory.CompanionTheory.EisMG.zetaOne_of_epMain <;> assumption)
end

section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG

theorem _root_.GlobalTheory.T.diagonal_term_good : DGood := by
  first | exact @GlobalTheory.CompanionTheory.RgEisDGood.dGood | exact GlobalTheory.CompanionTheory.RgEisDGood.dGood | (intros; apply GlobalTheory.CompanionTheory.RgEisDGood.dGood <;> assumption)
end

section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG

theorem _root_.GlobalTheory.T.side_term_convergence : EpConv → TestSph → Lines → Term → SideConv := by
  first | exact @GlobalTheory.CompanionTheory.RgEisSide.sideConv | exact GlobalTheory.CompanionTheory.RgEisSide.sideConv | (intros; apply GlobalTheory.CompanionTheory.RgEisSide.sideConv <;> assumption)
end

section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG

theorem _root_.GlobalTheory.T.unfolding_of_average : SecLaw → AvgMem → Unfold := by
  first | exact @GlobalTheory.CompanionTheory.RgEisUnfold.unfold | exact GlobalTheory.CompanionTheory.RgEisUnfold.unfold | (intros; apply GlobalTheory.CompanionTheory.RgEisUnfold.unfold <;> assumption)
end

section

open PositivityTheory.RgEis PositivityTheory.RgEis.MG

theorem _root_.GlobalTheory.T.mirabolic_generation : SecLaw → TestSph → AvgMem → AvgInv → SideOf → TestK → Core → MirGen := by
  first | exact @GlobalTheory.CompanionTheory.EisMir.mirGen_of_core | exact GlobalTheory.CompanionTheory.EisMir.mirGen_of_core | (intros; apply GlobalTheory.CompanionTheory.EisMir.mirGen_of_core <;> assumption)
end
