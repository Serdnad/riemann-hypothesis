module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.DiscreteSeriesTopClasses.IsInvOne
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Topology.Instances.Matrix
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaAbsoluteValues.KSumApply
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.LinearAlgebra.BilinearMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Normed
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Normed.Group.InfiniteSum

@[expose] public section

section

noncomputable section

open MeasureTheory PositivityTheory.Rg.BcB.E1
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.KerAdj

theorem pairing_swap {α : Type*} [MeasurableSpace α] {ν : Measure α} [SFinite ν]
    (k : α → α → ℂ) (g f : α → ℂ)
    (h : Integrable (fun p : α × α => conj (g p.1) * k p.1 p.2 * f p.2) (ν.prod ν)) :
    Integrable (fun x => conj (∫ y, conj (k y x) * g y ∂ν) * f x) ν ∧
    Integrable (fun y => conj (g y) * ∫ x, k y x * f x ∂ν) ν ∧
    ∫ x, conj (∫ y, conj (k y x) * g y ∂ν) * f x ∂ν
      = ∫ y, conj (g y) * ∫ x, k y x * f x ∂ν ∂ν := by
  have hL : ∀ x, conj (∫ y, conj (k y x) * g y ∂ν) * f x
      = ∫ y, conj (g y) * k y x * f x ∂ν := by
    intro x
    rw [← integral_conj, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [map_mul, Complex.conj_conj]
    ring
  have hR : ∀ y, conj (g y) * ∫ x, k y x * f x ∂ν
      = ∫ x, conj (g y) * k y x * f x ∂ν := by
    intro y
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [mul_assoc]
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [hL]
    exact h.swap.integral_prod_left
  · simp_rw [hR]
    exact h.integral_prod_left
  · simp_rw [hL, hR]
    exact (integral_integral_swap (f := fun y x => conj (g y) * k y x * f x) h).symm

theorem inner_eq_integral_conj_mul {α : Type*} [MeasurableSpace α] {ν : Measure α} (u v : Lp ℂ 2 ν) :
    inner ℂ u v = ∫ x, conj ((u : α → ℂ) x) * (v : α → ℂ) x ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [mul_comm]

theorem entry_pairing (hK : KerBasic) (hR : RowInt) (hS : SchurInt) (X : Ctx) (φ : X.G → ℂ)
    (hφ : Tst φ) (g f : Lp ℂ 2 X.ν) :
    Integrable (fun x => conj (∫ y, ker X.Γ (adj φ) x y * (g : X.G → ℂ) y ∂X.ν) * (f : X.G → ℂ) x) X.ν ∧
    Integrable (fun y => conj ((g : X.G → ℂ) y) * ∫ x, ker X.Γ φ y x * (f : X.G → ℂ) x ∂X.ν) X.ν ∧
    ∫ x, conj (∫ y, ker X.Γ (adj φ) x y * (g : X.G → ℂ) y ∂X.ν) * (f : X.G → ℂ) x ∂X.ν
      = ∫ y, conj ((g : X.G → ℂ) y) * ∫ x, ker X.Γ φ y x * (f : X.G → ℂ) x ∂X.ν ∂X.ν := by
  haveI : SFinite X.ν := by unfold Ctx.ν; infer_instance
  obtain ⟨-, hc, -, -, hadj, -⟩ := hK X φ hφ
  obtain ⟨A, hA, h1, h2⟩ := hR X φ hφ
  have hg : MemLp (fun y => conj ((g : X.G → ℂ) y)) 2 X.ν := (Lp.memLp g).star
  have hI := hS X.G X.ν (ker X.Γ φ) A hc.measurable hA h1 h2 _ _ hg (Lp.memLp f)
  have := pairing_swap (ν := X.ν) (ker X.Γ φ) (g : X.G → ℂ) (f : X.G → ℂ) hI
  simpa only [hadj] using this

theorem opAdj_of : KerBasic → RowInt → SchurInt → OpExA → OpAdj := by
  intro hK hR hS hE X ι _ Φ T hΦ hT
  have hadj : ∀ i j, Tst (adj (Φ j i)) := fun i j => (hK X _ (hΦ j i)).2.2.2.1
  obtain ⟨T', hT', -⟩ := hE X ι (fun i j => adj (Φ j i)) hadj
  have hEq : T' = ContinuousLinearMap.adjoint T := by
    rw [ContinuousLinearMap.eq_adjoint_iff]
    intro g f
    have key := fun i j => entry_pairing hK hR hS X (Φ j i) (hΦ j i) (g j) (f i)
    have hl : ∀ i, inner ℂ (T' g i) (f i)
        = ∑ j, ∫ x, conj (∫ y, ker X.Γ (adj (Φ j i)) x y * (g j : X.G → ℂ) y ∂X.ν)
            * (f i : X.G → ℂ) x ∂X.ν := by
      intro i
      rw [inner_eq_integral_conj_mul, ← MeasureTheory.integral_finsetSum _ fun j _ => (key i j).1]
      refine integral_congr_ae ?_
      filter_upwards [hT' g i] with x hx

      rw [hx, map_sum, Finset.sum_mul]
    have hr : ∀ j, inner ℂ (g j) (T f j)
        = ∑ i, ∫ y, conj ((g j : X.G → ℂ) y)
            * ∫ x, ker X.Γ (Φ j i) y x * (f i : X.G → ℂ) x ∂X.ν ∂X.ν := by
      intro j
      rw [inner_eq_integral_conj_mul, ← MeasureTheory.integral_finsetSum _ fun i _ => (key i j).2.1]
      refine integral_congr_ae ?_
      filter_upwards [hT f j] with y hy
      rw [hy, Finset.mul_sum]
    rw [PiLp.inner_apply, PiLp.inner_apply]
    simp_rw [hl, hr]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => (key i j).2.2
  rw [← hEq]
  exact hT'

end GlobalTheory.CompanionTheory.KerAdj

end
end

section

noncomputable section

open PositivityTheory.RgTw (Mat)

namespace GlobalTheory.CompanionTheory.GelfAct

variable {n : ℕ}

open scoped Matrix.Norms.Operator in
theorem hasDerivAt_exp_entry (X : Mat n) (a b : Fin n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) a b) (X a b) 0 := by
  have hsmul (t : ℝ) : (t : ℂ) • X = t • X := by ext; simp
  simp only [hsmul]
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let entry : Mat n →L[ℝ] ℂ := (Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap
  exact entry.hasFDerivAt.comp_hasDerivAt 0 h

end GlobalTheory.CompanionTheory.GelfAct

end
end

section

open PositivityTheory.Rg.Cz Fin Function

namespace GlobalTheory.CompanionTheory.KAdjoint

variable {P : Type} [AddCommGroup P] [Module ℝ P] {M : Type} [AddCommGroup M] [Module ℂ M]
  [Module ℝ M] [IsScalarTower ℝ ℂ M] {β : Type} [Fintype β]

theorem comp_insertNth_eq {m : ℕ} (b : β → P) (s : Fin (m + 1)) (i : β) (J : Fin m → β) :
    b ∘ (s.insertNth i J : Fin (m + 1) → β) = s.insertNth (b i) (b ∘ J) := by
  funext j
  refine Fin.succAboveCases s ?_ (fun k => ?_) j
  · simp
  · simp

theorem position_sum (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (b : β → P) (T T' : P →ₗ[ℝ] Module.End ℂ M)
    (h : ∀ X x y, B (T X x) y = B x (T' X y)) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M)
    (θ : P [⋀^Fin (m + 1)]→ₗ[ℝ] M) (s : Fin (m + 1)) :
    ∑ I : Fin (m + 1) → β,
        B ((-1 : ℤ) ^ (s : ℕ) • T (b (I s)) (η (s.removeNth (b ∘ I)))) (θ (b ∘ I))
      = kIp B b η (kDel T' b θ) := by
  rw [← (Fin.insertNthEquiv (fun _ => β) s).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]

  simp only [kIp, kDel_apply, map_sum]
  refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.insertNthEquiv, Equiv.coe_fn_mk, comp_insertNth_eq, Fin.insertNth_apply_same,
    Fin.removeNth_insertNth]
  rw [← h, θ.map_insertNth]
  simp only [map_zsmul, LinearMap.smul_apply, smul_smul, ← pow_add, Even.neg_one_pow ⟨_, rfl⟩, one_smul]

theorem kIp_kD (B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ) (b : β → P) (T T' : P →ₗ[ℝ] Module.End ℂ M)
    (h : ∀ X x y, B (T X x) y = B x (T' X y)) {m : ℕ} (η : P [⋀^Fin m]→ₗ[ℝ] M)
    (θ : P [⋀^Fin (m + 1)]→ₗ[ℝ] M) :
    kIp B b (kD T η) θ = ((m : ℂ) + 1) * kIp B b η (kDel T' b θ) := by
  have hs : ∀ s : Fin (m + 1), ∑ I : Fin (m + 1) → β,
      B ((-1 : ℤ) ^ (s : ℕ) • T (b (I s)) (η (s.removeNth (b ∘ I)))) (θ (b ∘ I))
        = kIp B b η (kDel T' b θ) := fun s => position_sum B b T T' h η θ s

  simp only [kIp, kD_apply, Function.comp_apply, map_sum, LinearMap.sum_apply]
  rw [Finset.sum_comm]
  simp only [kIp] at hs
  rw [Finset.sum_congr rfl fun s _ => hs s]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.CompanionTheory.KAdjoint
end

section

open Filter Topology

namespace GlobalTheory.CompanionTheory.EisCross

open PositivityTheory.RgEis

theorem pos_nonneg' {G : Type} [Group G] (Δ P : Subgroup G) (l : G → ℝ) (g : G) : 0 ≤ pos Δ P l g := by
  unfold pos
  exact tsum_nonneg fun _ => (Real.exp_pos _).le

theorem pos_mul_le {G : Type} [Group G] (Δ P : Subgroup G) (l : G → ℝ) (C : Set G) (A : ℝ)
    (hA : ∀ g, ∀ u ∈ C, |l (g * u) - l g| ≤ A) (hc : Conv Δ P l) (y v : G) (hv : v ∈ C) :
    pos Δ P l (y * v) ≤ Real.exp A * pos Δ P l y := by
  unfold pos
  have hle : ∀ q : Cos P Δ, Real.exp (l (rep q * (y * v))) ≤ Real.exp A * Real.exp (l (rep q * y)) := by
    intro q
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := hA (rep q * y) v hv
    rw [mul_assoc] at h
    have h' := (abs_le.mp h).2
    linarith
  have hs : Summable fun q : Cos P Δ => Real.exp A * Real.exp (l (rep q * y)) := (hc y).mul_left _
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) hle hs) hs

theorem exp_between (e₁ e₂ t s : ℝ) (h₁ : e₁ ≤ t) (h₂ : t ≤ e₂) :
    Real.exp (t * s) ≤ Real.exp (e₁ * s) + Real.exp (e₂ * s) := by
  rcases le_total 0 s with hs | hs
  · have h3 : t * s ≤ e₂ * s := mul_le_mul_of_nonneg_right h₂ hs
    have h4 := Real.exp_le_exp.mpr h3
    have h5 := Real.exp_pos (e₁ * s)
    linarith
  · have h3 : t * s ≤ e₁ * s := mul_le_mul_of_nonpos_right h₁ hs
    have h4 := Real.exp_le_exp.mpr h3
    have h5 := Real.exp_pos (e₂ * s)
    linarith

theorem exp_shift (e a b A : ℝ) (h : |a - b| ≤ A) :
    Real.exp (e * a) ≤ Real.exp (|e| * A) * Real.exp (e * b) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h1 : e * (a - b) ≤ |e| * |a - b| := by
    rw [← abs_mul]
    exact le_abs_self _
  have h2 : |e| * |a - b| ≤ |e| * A := mul_le_mul_of_nonneg_left h (abs_nonneg e)
  have h3 : e * (a - b) = e * a - e * b := by ring
  linarith

theorem dom : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] (Γ Δ P P' : Subgroup G) (ξ l₁ l₂ : G → ℝ) (H : ℂ → G → X)
    (a b e₁ e₂ M : ℝ),
    (∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |ξ (g * u) - ξ g| ≤ A) →
    (∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |l₁ (g * u) - l₁ g| ≤ A) →
    (∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |l₂ (g * u) - l₂ g| ≤ A) →
    PositivityTheory.RgEis.Conv Δ P l₁ → PositivityTheory.RgEis.Conv Δ P' l₂ →
    (∀ z : ℂ, b ≤ z.re → z.re ≤ a → ∀ g, ‖H z g‖ ≤ M * (PositivityTheory.RgEis.pos Δ P l₁ g + PositivityTheory.RgEis.pos Δ P' l₂ g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₁ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P l₁ (PositivityTheory.RgEis.rep r * g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₂ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P l₁ (PositivityTheory.RgEis.rep r * g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₁ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P' l₂ (PositivityTheory.RgEis.rep r * g)) →
    (∀ g, Summable fun r : PositivityTheory.RgEis.Cos Δ Γ => Real.exp (e₂ * ξ (PositivityTheory.RgEis.rep r * g)) *
      PositivityTheory.RgEis.pos Δ P' l₂ (PositivityTheory.RgEis.rep r * g)) →
    ∀ g : G, ∃ U ∈ 𝓝 g, ∃ u : PositivityTheory.RgEis.Cos Δ Γ → ℝ, Summable u ∧
      ∀ l : ℂ × ℂ, b ≤ l.1.re → l.1.re ≤ a → e₁ ≤ l.2.re → l.2.re ≤ e₂ → ∀ g' ∈ U, ∀ r,
        ‖Complex.exp (l.2 * ξ (PositivityTheory.RgEis.rep r * g')) • H l.1 (PositivityTheory.RgEis.rep r * g')‖ ≤ u r := by
  intro G _ _ _ _ X _ _ Γ Δ P P' ξ l₁ l₂ H a b e₁ e₂ M hξ hl₁ hl₂ hc₁ hc₂ hH s11 s21 s12 s22 g
  obtain ⟨C, hC1, -, hCc⟩ := local_compact_nhds (x := (1 : G)) Filter.univ_mem
  obtain ⟨Aξ, hAξ⟩ := hξ C hCc
  obtain ⟨A₁, hA₁⟩ := hl₁ C hCc
  obtain ⟨A₂, hA₂⟩ := hl₂ C hCc
  have hU : (fun g' => g⁻¹ * g') ⁻¹' C ∈ 𝓝 g := by
    apply (continuous_const_mul g⁻¹).continuousAt.preimage_mem_nhds
    simpa using hC1
  refine ⟨(fun g' => g⁻¹ * g') ⁻¹' C, hU, fun r => |M| *
      (Real.exp (|e₁| * Aξ) * Real.exp A₁ * (Real.exp (e₁ * ξ (rep r * g)) * pos Δ P l₁ (rep r * g)) +
        Real.exp (|e₂| * Aξ) * Real.exp A₁ * (Real.exp (e₂ * ξ (rep r * g)) * pos Δ P l₁ (rep r * g)) +
        Real.exp (|e₁| * Aξ) * Real.exp A₂ * (Real.exp (e₁ * ξ (rep r * g)) * pos Δ P' l₂ (rep r * g)) +
        Real.exp (|e₂| * Aξ) * Real.exp A₂ * (Real.exp (e₂ * ξ (rep r * g)) * pos Δ P' l₂ (rep r * g))), ?_, ?_⟩
  · exact Summable.mul_left |M|
      ((((s11 g).mul_left (Real.exp (|e₁| * Aξ) * Real.exp A₁)).add
        ((s21 g).mul_left (Real.exp (|e₂| * Aξ) * Real.exp A₁))).add
        ((s12 g).mul_left (Real.exp (|e₁| * Aξ) * Real.exp A₂)) |>.add
        ((s22 g).mul_left (Real.exp (|e₂| * Aξ) * Real.exp A₂)))
  · intro l hb ha he₁ he₂ g' hg' r
    have hw : g⁻¹ * g' ∈ C := hg'
    have hy : rep r * g' = rep r * g * (g⁻¹ * g') := by
      rw [mul_assoc, mul_inv_cancel_left]
    have hnorm : ‖Complex.exp (l.2 * ξ (rep r * g')) • H l.1 (rep r * g')‖ =
        Real.exp (l.2.re * ξ (rep r * g')) * ‖H l.1 (rep r * g')‖ := by
      rw [norm_smul, Complex.norm_exp]
      simp [Complex.mul_re]
    have hξw := hAξ (rep r * g) (g⁻¹ * g') hw
    rw [← hy] at hξw
    have hexp : Real.exp (l.2.re * ξ (rep r * g')) ≤
        Real.exp (|e₁| * Aξ) * Real.exp (e₁ * ξ (rep r * g)) +
          Real.exp (|e₂| * Aξ) * Real.exp (e₂ * ξ (rep r * g)) := by
      have h0 := exp_between e₁ e₂ l.2.re (ξ (rep r * g')) he₁ he₂
      have h1 := exp_shift e₁ (ξ (rep r * g')) (ξ (rep r * g)) Aξ hξw
      have h2 := exp_shift e₂ (ξ (rep r * g')) (ξ (rep r * g)) Aξ hξw
      linarith
    have hp1 : pos Δ P l₁ (rep r * g') ≤ Real.exp A₁ * pos Δ P l₁ (rep r * g) := by
      rw [hy]
      exact pos_mul_le Δ P l₁ C A₁ hA₁ hc₁ (rep r * g) (g⁻¹ * g') hw
    have hp2 : pos Δ P' l₂ (rep r * g') ≤ Real.exp A₂ * pos Δ P' l₂ (rep r * g) := by
      rw [hy]
      exact pos_mul_le Δ P' l₂ C A₂ hA₂ hc₂ (rep r * g) (g⁻¹ * g') hw
    have hH1 := hH l.1 hb ha (rep r * g')
    have hs0 : 0 ≤ pos Δ P l₁ (rep r * g') + pos Δ P' l₂ (rep r * g') :=
      add_nonneg (pos_nonneg' _ _ _ _) (pos_nonneg' _ _ _ _)
    have hH2 : ‖H l.1 (rep r * g')‖ ≤ |M| * (pos Δ P l₁ (rep r * g') + pos Δ P' l₂ (rep r * g')) :=
      hH1.trans (mul_le_mul_of_nonneg_right (le_abs_self M) hs0)
    have hE0 : 0 ≤ Real.exp (|e₁| * Aξ) * Real.exp (e₁ * ξ (rep r * g)) +
        Real.exp (|e₂| * Aξ) * Real.exp (e₂ * ξ (rep r * g)) := by positivity
    rw [hnorm]
    calc Real.exp (l.2.re * ξ (rep r * g')) * ‖H l.1 (rep r * g')‖
        ≤ Real.exp (l.2.re * ξ (rep r * g')) *
            (|M| * (pos Δ P l₁ (rep r * g') + pos Δ P' l₂ (rep r * g'))) :=
          mul_le_mul_of_nonneg_left hH2 (Real.exp_pos _).le
      _ ≤ (Real.exp (|e₁| * Aξ) * Real.exp (e₁ * ξ (rep r * g)) +
            Real.exp (|e₂| * Aξ) * Real.exp (e₂ * ξ (rep r * g))) *
            (|M| * (pos Δ P l₁ (rep r * g') + pos Δ P' l₂ (rep r * g'))) :=
          mul_le_mul_of_nonneg_right hexp (mul_nonneg (abs_nonneg M) hs0)
      _ ≤ (Real.exp (|e₁| * Aξ) * Real.exp (e₁ * ξ (rep r * g)) +
            Real.exp (|e₂| * Aξ) * Real.exp (e₂ * ξ (rep r * g))) *
            (|M| * (Real.exp A₁ * pos Δ P l₁ (rep r * g) + Real.exp A₂ * pos Δ P' l₂ (rep r * g))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add hp1 hp2) (abs_nonneg M)) hE0
      _ = _ := by ring

end GlobalTheory.CompanionTheory.EisCross
end

section

namespace GlobalTheory.CompanionTheory.RgEis

open PositivityTheory.RgEis

variable {G : Type} [Group G] {P Δ Γ : Subgroup G}

def cls (y : Γ) : Cos P Γ := Quotient.mk _ y

theorem cls_eq {a b : Γ} : (cls a : Cos P Γ) = cls b ↔ (b : G) * (a : G)⁻¹ ∈ P := by
  unfold cls
  rw [Quotient.eq]
  show QuotientGroup.rightRel _ a b ↔ _
  rw [QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
  simp

theorem rep_mem (q : Cos P Γ) : rep q ∈ Γ := (Quotient.out q).2

theorem cls_rep (q : Cos P Γ) : cls ⟨rep q, rep_mem q⟩ = q := Quotient.out_eq q

theorem rep_cls (y : Γ) : ∃ p ∈ P, p ∈ Γ ∧ rep (cls y : Cos P Γ) = p * y := by
  have h : (cls y : Cos P Γ) = cls ⟨rep (cls y : Cos P Γ), rep_mem _⟩ := (cls_rep _).symm
  refine ⟨rep (cls y : Cos P Γ) * (y : G)⁻¹, cls_eq.1 h, Γ.mul_mem (rep_mem _) (Γ.inv_mem y.2), by group⟩

noncomputable def glue (hΔ : Δ ≤ Γ) (s : (_ : Cos Δ Γ) × Cos P Δ) : Cos P Γ :=
  cls ⟨rep s.2 * rep s.1, Γ.mul_mem (hΔ (rep_mem _)) (rep_mem _)⟩

theorem glue_injective (hΔ : Δ ≤ Γ) (hP : ∀ γ ∈ Γ, γ ∈ P → γ ∈ Δ) :
    Function.Injective (glue (P := P) hΔ) := by
  rintro ⟨r, q⟩ ⟨r', q'⟩ h
  have h1 : rep q' * rep r' * (rep q * rep r)⁻¹ ∈ P := cls_eq.1 h
  have hΓ : rep q' * rep r' * (rep q * rep r)⁻¹ ∈ Γ :=
    Γ.mul_mem (Γ.mul_mem (hΔ (rep_mem _)) (rep_mem _))
      (Γ.inv_mem (Γ.mul_mem (hΔ (rep_mem _)) (rep_mem _)))
  have h2 := hP _ hΓ h1
  have h3 : rep r' * (rep r)⁻¹ ∈ Δ := by
    have : rep r' * (rep r)⁻¹ = (rep q')⁻¹ * (rep q' * rep r' * (rep q * rep r)⁻¹) * rep q := by
      group
    rw [this]
    exact Δ.mul_mem (Δ.mul_mem (Δ.inv_mem (rep_mem _)) h2) (rep_mem _)
  have hr : r = r' := by
    rw [← cls_rep r, ← cls_rep r']
    exact cls_eq.2 h3
  subst hr
  have h4 : rep q' * (rep q)⁻¹ ∈ P := by
    have : rep q' * (rep q)⁻¹ = rep q' * rep r * (rep q * rep r)⁻¹ := by group
    rw [this]
    exact h1
  have hq : q = q' := by
    rw [← cls_rep q, ← cls_rep q']
    exact cls_eq.2 h4
  subst hq
  rfl

theorem glue_surjective (hΔ : Δ ≤ Γ) (hP : ∀ γ ∈ Γ, γ ∈ P → γ ∈ Δ) :
    Function.Surjective (glue (P := P) hΔ) := by
  intro t
  obtain ⟨y, rfl⟩ : ∃ y : Γ, cls y = t := ⟨_, cls_rep t⟩
  obtain ⟨d, hdΔ, -, hd⟩ := rep_cls (P := Δ) y
  obtain ⟨p, hpP, hpΔ, hp⟩ := rep_cls (P := P) (⟨d⁻¹, Δ.inv_mem hdΔ⟩ : Δ)
  refine ⟨⟨cls y, cls ⟨d⁻¹, Δ.inv_mem hdΔ⟩⟩, ?_⟩
  apply cls_eq.2
  show (y : G) * (rep (cls ⟨d⁻¹, Δ.inv_mem hdΔ⟩ : Cos P Δ) * rep (cls y : Cos Δ Γ))⁻¹ ∈ P
  rw [hp, hd]
  have : (y : G) * (p * d⁻¹ * (d * y))⁻¹ = p⁻¹ := by group
  rw [this]
  exact P.inv_mem hpP

theorem f_rep {X : Type} {f : G → X} (hf : ∀ γ ∈ Γ, γ ∈ P → ∀ x, f (γ * x) = f x) (y : Γ) (g : G) :
    f (rep (cls y : Cos P Γ) * g) = f (y * g) := by
  obtain ⟨p, hpP, hpΓ, hp⟩ := rep_cls (P := P) y
  rw [hp, mul_assoc, hf p hpΓ hpP]

theorem stage : PiLocalization₂ := by
  intro G _ X _ _ P Δ Γ f hΔ hP hf g hs
  have hmem : ∀ (q : Cos P Δ) (x : G), x ∈ Γ → rep q * x ∈ Γ := fun q x hx =>
    Γ.mul_mem (hΔ (rep_mem q)) hx

  have h1 : ∀ x ∈ Γ, Summable fun q : Cos P Δ => ‖f (rep q * (x * g))‖ := by
    intro x hx
    have hinj : Function.Injective fun q : Cos P Δ => (cls ⟨rep q * x, hmem q x hx⟩ : Cos P Γ) := by
      intro q q' h
      have h1 : rep q' * x * (rep q * x)⁻¹ ∈ P := cls_eq.1 h
      have h2 : rep q' * (rep q)⁻¹ ∈ P := by
        have : rep q' * (rep q)⁻¹ = rep q' * x * (rep q * x)⁻¹ := by group
        rw [this]
        exact h1
      rw [← cls_rep q, ← cls_rep q']
      exact cls_eq.2 h2
    refine (hs.comp_injective hinj).congr fun q => ?_
    simp only [Function.comp_apply]
    rw [f_rep hf, mul_assoc]

  let e : ((_ : Cos Δ Γ) × Cos P Δ) ≃ Cos P Γ :=
    Equiv.ofBijective (glue hΔ) ⟨glue_injective hΔ hP, glue_surjective hΔ hP⟩
  let φ : ((_ : Cos Δ Γ) × Cos P Δ) → X := fun s => f (rep s.2 * (rep s.1 * g))
  have hφ : ∀ s, f (rep (e s) * g) = φ s := by
    intro s
    show f (rep (glue hΔ s) * g) = _
    unfold glue
    rw [f_rep hf, mul_assoc]
  have hn : Summable fun s => ‖φ s‖ := by
    refine ((e.summable_iff (f := fun q : Cos P Γ => ‖f (rep q * g)‖)).2 hs).congr fun s => ?_
    simp only [Function.comp_apply]
    rw [hφ]
  have hsig := (summable_sigma_of_nonneg (fun s => norm_nonneg (φ s))).1 hn
  have hφs : Summable φ := hn.of_norm
  refine ⟨h1, hsig.2, ?_⟩
  have hfib : ∀ r, Summable fun q : Cos P Δ => φ ⟨r, q⟩ := fun r => (hsig.1 r).of_norm
  calc ∑' q : Cos P Γ, f (rep q * g) = ∑' s, f (rep (e s) * g) := (e.tsum_eq _).symm
    _ = ∑' s, φ s := tsum_congr hφ
    _ = ∑' r : Cos Δ Γ, ∑' q : Cos P Δ, φ ⟨r, q⟩ := hφs.tsum_sigma' hfib

end GlobalTheory.CompanionTheory.RgEis
end

section


theorem _root_.GlobalTheory.T.double_annihilator_eq_self : ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y] (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n), Function.Injective B → Function.Injective B.flip → ∀ U : Submodule (ZMod n) X, (⨅ y ∈ (⨅ x ∈ U, LinearMap.ker (B.flip x)), LinearMap.ker (B y)) = U := by
  first | exact @GlobalTheory.CompanionTheory.FiniteDuality.double_annihilator | exact GlobalTheory.CompanionTheory.FiniteDuality.double_annihilator | (intros; apply GlobalTheory.CompanionTheory.FiniteDuality.double_annihilator <;> assumption)
end
