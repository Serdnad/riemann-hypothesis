module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private noncomputable def kA (δ : F) : Fin 4 → A F := ![1, 1, 2, -2 * rt δ]

private noncomputable def qG (δ : F) (v : V4 F) : A F := v 0 ^ 2 + v 1 ^ 2 + 2 * (v 2 ^ 2 - rt δ * v 3 ^ 2)

private theorem kap_eq (δ : F) (w : InfinitePlace F) (i : Fin 4) :
    kap δ w i = ((TR.pInf F (kA δ i) w : ℝ) : ℂ) := by
  have h2 : TR.pInf F (2 : A F) w = 2 := by
    rw [map_ofNat]
    rfl
  fin_cases i <;> simp [kap, kA, cw, h2]

private theorem form_step (δ : F) (v : V4 F) (i : Fin 4) (s : A F) :
    qG δ (v + Pi.single i s) = qG δ v + kA δ i * (2 * v i * s + s * s) := by
  fin_cases i <;> simp [qG, kA, Pi.single_apply] <;> ring

private theorem sum_step (w : InfinitePlace F) (K b : InfinitePlace F → ℝ) (t : ℝ) :
    ∑ w', (K * (2 * b * Pi.single w t + Pi.single w t * Pi.single w t) : InfinitePlace F → ℝ) w' =
      K w * (2 * b w * t + t * t) := by
  rw [Finset.sum_eq_single w]
  · simp
  · intro b' _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ w) h

private theorem gauss_step (δ : F) (v : V4 F) (i : Fin 4) (w : InfinitePlace F) (t : ℝ) :
    gauss δ (v + Pi.single i (at1 w t)) =
      gauss δ v * Complex.exp (-((Real.pi : ℂ) * kap δ w i * (2 * cw w (v i) * t + t * t))) := by
  have hp : TR.pInf F (at1 w t) = Pi.single w t := (atLaws F w).2.2.1 t
  have hs : (∑ w', TR.pInf F (qG δ (v + Pi.single i (at1 w t))) w' : ℝ) =
      (∑ w', TR.pInf F (qG δ v) w') +
        TR.pInf F (kA δ i) w * (2 * TR.pInf F (v i) w * t + t * t) := by
    rw [form_step, ← sum_step w (TR.pInf F (kA δ i)) (TR.pInf F (v i)) t,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w' _ => ?_
    have h2 : TR.pInf F (2 : A F) = 2 := by rw [map_ofNat]
    simp only [map_add (f := _), map_mul, hp, h2, Pi.add_apply]
  have hg : ∀ u : V4 F, gauss δ u =
      Complex.exp (-(Real.pi : ℂ) * ((∑ w', TR.pInf F (qG δ u) w' : ℝ) : ℂ)) := by
    intro u
    unfold gauss qG
    rfl
  rw [hg, hg, hs, ← Complex.exp_add, kap_eq]
  congr 1
  simp only [cw]
  push_cast
  ring

private theorem cw_step (v : V4 F) (i : Fin 4) (w : InfinitePlace F) (t : ℝ) :
    cw w ((v + Pi.single i (at1 w t) : V4 F) i) = cw w (v i) + t := by
  have hp : TR.pInf F (at1 w t) = Pi.single w t := (atLaws F w).2.2.1 t
  simp [cw, hp]

private theorem line_step (δ : F) (O : Ops F) (φ : S4 F)
    (h : ∀ w i, O.d w i φ = (-2 * Real.pi * kap δ w i) • O.x w i φ)
    (v : V4 F) (i : Fin 4) (w : InfinitePlace F) (t : ℝ) :
    φ.1 (v + Pi.single i (at1 w t)) * gauss δ v = φ.1 v * gauss δ (v + Pi.single i (at1 w t)) := by
  set a : ℂ := cw w (v i) with ha
  set κ : ℂ := kap δ w i with hκ
  let f : ℝ → ℂ := fun t => φ.1 (v + Pi.single i (at1 w t))
  let X : ℝ → ℂ := fun t => (Real.pi : ℂ) * κ * (2 * a * t + t * t)
  have hf : ∀ t, HasDerivAt f (-2 * Real.pi * κ * (a + t) * f t) t := by
    intro t
    have h0 := O.d_spec w i φ (v + Pi.single i (at1 w t))
    have e : (fun s : ℝ => φ.1 (v + Pi.single i (at1 w t) + Pi.single i (at1 w s))) = fun s => f (t + s) := by
      funext s
      simp only [f]
      rw [(atLaws F w).2.2.2.1 t s, Pi.single_add, add_assoc]
    rw [e] at h0
    have h1 : HasDerivAt (fun s => f (t + s)) ((O.d w i φ).1 (v + Pi.single i (at1 w t))) (t - t) := by
      simpa using h0
    have h2 := h1.comp_sub_const t t
    have e2 : (fun x => f (t + (x - t))) = f := by
      funext x
      simp
    rw [e2] at h2
    have key : (O.d w i φ).1 (v + Pi.single i (at1 w t)) = -2 * Real.pi * κ * (a + t) * f t := by
      rw [h w i]
      change (-2 * Real.pi * kap δ w i) * (O.x w i φ).1 (v + Pi.single i (at1 w t)) = _
      rw [O.x_apply, cw_step]
      simp only [f]
      ring
    rw [key] at h2
    exact h2
  have hX : ∀ t : ℝ, HasDerivAt X ((Real.pi : ℂ) * κ * (2 * a + 2 * t)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := (hasDerivAt_id t).ofReal_comp
    have h2 := ((h1.const_mul (2 * a)).add (h1.mul h1)).const_mul ((Real.pi : ℂ) * κ)
    exact h2.congr_deriv (by ring)
  have hE : ∀ t : ℝ, HasDerivAt (fun t => f t * Complex.exp (X t)) 0 t := by
    intro t
    have h2 := (hf t).mul (hX t).cexp
    exact h2.congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun t => (hE t).differentiableAt) (fun t => (hE t).deriv) t 0
  have h0 : f 0 = φ.1 v := by
    simp only [f]
    rw [(atLaws F w).2.2.2.2.1]
    simp
  have hX0 : X 0 = 0 := by simp [X]
  simp only [hX0, Complex.exp_zero, mul_one, h0] at hc
  rw [gauss_step, ← hc]
  have : Complex.exp (X t) * Complex.exp (-X t) = 1 := by
    rw [← Complex.exp_add]
    simp
  change f t * gauss δ v = f t * Complex.exp (X t) * (gauss δ v * Complex.exp (-X t))
  linear_combination (-(f t * gauss δ v)) * this

private theorem chain_step (δ : F) (O : Ops F) (φ : S4 F)
    (h : ∀ w i, O.d w i φ = (-2 * Real.pi * kap δ w i) • O.x w i φ)
    (v : V4 F) (c : Fin 4 × InfinitePlace F → ℝ) (s : Finset (Fin 4 × InfinitePlace F)) :
    φ.1 (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p))) * gauss δ v =
      φ.1 v * gauss δ (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p))) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    rw [Finset.sum_insert hp, add_comm (Pi.single p.1 _), ← add_assoc]
    have hs := line_step δ O φ h (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p))) p.1 p.2 (c p)
    have hg : gauss δ (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p))) ≠ 0 := Complex.exp_ne_zero _
    refine mul_right_cancel₀ hg ?_
    linear_combination (gauss δ v) * hs +
      (gauss δ (v + ∑ p ∈ s, Pi.single p.1 (at1 p.2 (c p)) + Pi.single p.1 (at1 p.2 (c p)))) * ih

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Fo.annVac :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F) (φ : S4 F), (∀ w i, O.d w i φ = (-2 * Real.pi * kap δ w i) • O.x w i φ) → φ ∈ Vac δ := by
  intro F _ _ _ δ O φ h v v' e
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  let c : Fin 4 × InfinitePlace F → ℝ := fun p => TR.pInf F (v' p.1 - v p.1) p.2
  have hv : v' = v + ∑ p, Pi.single p.1 (at1 p.2 (c p)) := by
    funext j
    have h0 : (v' j - v j).2 = 0 := by
      have := congrFun e j
      change (v j).2 = (v' j).2 at this
      change (v' j).2 - (v j).2 = 0
      rw [this, sub_self]
    have h1 := (atLaws F w₀).2.2.2.2.2.2.1 (v' j - v j) h0
    have h2 : (∑ p : Fin 4 × InfinitePlace F, (Pi.single p.1 (at1 p.2 (c p)) : V4 F)) j = v' j - v j := by
      rw [h1, Fintype.sum_prod_type, Finset.sum_apply, Finset.sum_eq_single j]
      · rw [Finset.sum_apply]
        refine Finset.sum_congr rfl fun w _ => ?_
        simp [c, ← h1]
      · intro b _ hb
        rw [Finset.sum_apply]
        exact Finset.sum_eq_zero fun w _ => Pi.single_eq_of_ne hb.symm _
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    rw [Pi.add_apply, h2]
    abel
  have := chain_step δ O φ h v c Finset.univ
  rw [← hv] at this
  exact this.symm ▸ (by ring)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem quadraticForm_add_expand (δ : F) (v : V4 F) (i : Fin 4) (a : A F) :
    q4 δ (v + Pi.single i a) = q4 δ v + a * (B4 δ v (Pi.single i 1) + a * q4 δ (Pi.single i 1)) := by
  fin_cases i <;> simp [q4, B4, Pi.single_apply] <;> ring

private theorem psi_add (x y : A F) : ψ (x + y) = ψ x * ψ y := by
  simp [ψ, (adelicChar F).map_add_eq_mul]

private theorem cw_mul (w : InfinitePlace F) (a b : A F) : cw w (a * b) = cw w a * cw w b := by
  simp [cw, map_mul]

private theorem psi_curve (w : InfinitePlace F) (b : A F) (δ : F) (i : Fin 4) (v : V4 F) :
    ∃ g : ℝ → ℂ, (∀ t, ψ (b * q4 δ (v + Pi.single i (at1 w t))) = ψ (b * q4 δ v) * g t) ∧ g 0 = 1 ∧
      HasDerivAt g (cc * (cw w b * cw w (B4 δ v (Pi.single i 1)))) 0 := by
  obtain ⟨hψ, -, hp, -, -, hm, -, -⟩ := atLaws F w
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = TR.pInf F b w * TR.pInf F (B4 δ v (Pi.single i 1)) w := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = TR.pInf F b w * TR.pInf F (q4 δ (Pi.single i 1)) w := ⟨_, rfl⟩
  refine ⟨fun t => Complex.exp (cc * ((t * (β + t * κ) : ℝ) : ℂ)), ?_, by simp, ?_⟩
  · intro t
    have h0 : at1 w t * (b * (B4 δ v (Pi.single i 1) + at1 w t * q4 δ (Pi.single i 1))) =
        at1 w (t * (β + t * κ)) := by
      rw [hm]
      congr 2
      have : TR.pInf F (at1 w t) w = t := by rw [hp]; simp
      simp only [map_mul, map_add (f := _), Pi.mul_apply, Pi.add_apply, this, hβ, hκ]
      ring
    have h1 : b * q4 δ (v + Pi.single i (at1 w t)) = b * q4 δ v + at1 w (t * (β + t * κ)) := by
      rw [quadraticForm_add_expand, ← h0]
      ring
    rw [h1, psi_add, hψ]
  · have hu : HasDerivAt (fun t : ℝ => t * (β + t * κ)) β 0 := by
      have := (hasDerivAt_id' (0 : ℝ)).fun_mul (((hasDerivAt_id' (0 : ℝ)).mul_const κ).const_add β)
      simpa using this
    have h2 := (hu.ofReal_comp.const_mul cc).cexp
    convert h2 using 1
    simp [hβ, cw]

private theorem p_apply (O : Ops F) (δ : F) (w : InfinitePlace F) (i : Fin 4) (φ : S4 F) (v : V4 F) :
    (O.p δ w i φ).1 v = cc * cw w (B4 δ v (Pi.single i 1)) * φ.1 v := by
  have hs : ∀ (c : ℂ) (T : Module.End ℂ (S4 F)), ((c • T) φ).1 v = c * (T φ).1 v := fun _ _ => rfl
  have hn : ∀ a : A F, cw w (-a) = -cw w a := fun a => by simp [cw]
  have h2 : cw w (2 : A F) = 2 := by
    have : TR.pInf F (2 : A F) = 2 := map_ofNat _ 2
    simp [cw, this]
  fin_cases i
  · have : B4 δ v (Pi.single 0 1) = -v 1 := by simp [B4, Pi.single_apply]
    simp only [Fin.zero_eta, this, hn, Ops.p]
    simp [hs, O.x_apply]
    ring
  · have : B4 δ v (Pi.single 1 1) = -v 0 := by simp [B4, Pi.single_apply]
    simp only [Fin.mk_one, this, hn, Ops.p]
    simp [hs, O.x_apply]
    ring
  · have : B4 δ v (Pi.single 2 1) = 2 * v 2 := by simp [B4, Pi.single_apply]
    simp only [Fin.reduceFinMk, this, cw_mul, h2, Ops.p]
    simp [hs, O.x_apply]
    ring
  · have : B4 δ v (Pi.single 3 1) = (-2 * rt δ) * v 3 := by simp [B4, Pi.single_apply]; ring
    simp only [Fin.reduceFinMk, this, cw_mul, hn, h2, Ops.p]
    simp [hs, O.x_apply]
    ring

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Fo.dN :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) w i b, O.d w i * W.Om (nU b) = W.Om (nU b) * (O.d w i + cw w b • O.p D.δ w i) ∧
    O.x w i * W.Om (nU b) = W.Om (nU b) * O.x w i := by
  intro F E _ _ _ _ _ _ _ D W O w i b
  refine ⟨?_, ?_⟩
  · refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
    obtain ⟨g, hg, hg0, hgd⟩ := psi_curve w b D.δ i v
    have hφ := O.d_spec w i φ v
    have h1 := O.d_spec w i (W.Om (nU b) φ) v
    have hz : v + Pi.single i (at1 w 0) = v := by
      rw [(atLaws F w).2.2.2.2.1]; simp
    have hfun : (fun t : ℝ => (W.Om (nU b) φ).1 (v + Pi.single i (at1 w t))) =
        fun t => (ψ (b * q4 D.δ v) * g t) * φ.1 (v + Pi.single i (at1 w t)) := by
      funext t
      rw [W.Om_n, hg]
    rw [hfun] at h1
    have h2 := (hgd.const_mul (ψ (b * q4 D.δ v))).mul hφ
    have h3 := h1.unique h2
    change (O.d w i (W.Om (nU b) φ)).1 v = (W.Om (nU b) ((O.d w i + cw w b • O.p D.δ w i) φ)).1 v
    rw [h3, W.Om_n]
    change _ = _ * ((O.d w i φ).1 v + cw w b * (O.p D.δ w i φ).1 v)
    rw [p_apply, hg0, hz]
    ring
  · refine LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_)
    change (O.x w i (W.Om (nU b) φ)).1 v = (W.Om (nU b) (O.x w i φ)).1 v
    rw [O.x_apply, W.Om_n, W.Om_n, O.x_apply]
    ring
end
