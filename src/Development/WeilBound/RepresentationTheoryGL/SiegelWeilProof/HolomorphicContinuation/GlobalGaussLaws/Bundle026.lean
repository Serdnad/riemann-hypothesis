module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle019
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle024
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle022
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle012
import Std.Tactic.BVDecide.Normalize.Bool

@[expose] public section

section

noncomputable section

open MeasureTheory Filter Topology

namespace PositivityTheory.Rg.Sw.Glob

open DCalcBH DCalcCH in
theorem dCalc : DCalc := by
  intro m n ε t c e X hc _
  have hfun : ∀ u : Fin m → Fin n → ℂ, (fun s' : ℝ => famC ε t c e 1 X (↑s') u) = fF c X 1 u :=
    fun u => funext fun s => famC_one ε t c e X u s
  refine ⟨fun s r u => ?_, fun r s => ?_⟩
  · rw [hfun, fF_iter]
    rfl
  · simp only [hfun, fF_iter]
    rw [pow_succ']
    exact DCalc2H.l2conv c hc X ((dil c X ^ r) 1) s

end PositivityTheory.Rg.Sw.Glob
end
end

section

noncomputable section

open scoped Matrix ComplexOrder
open Matrix

namespace PositivityTheory.Rg.Sw.Glob.GaussH

variable {m n : ℕ}

theorem evX_Qb (ε : Fin m → Bool) (b : Bool) (i j : Fin n) (u : Fin m → Fin n → ℂ) :
    evX (Qb ε b i j) u = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a i) * u a j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [evX, Qb, map_sum]

theorem gramB_apply (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) (i j : Fin n) :
    gramB ε b u i j = ∑ a ∈ Finset.univ.filter (fun a => ε a = b), star (u a i) * u a j := evX_Qb ε b i j u

theorem gramB_not (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    gramB (fun a => !ε a) b u = gramB ε (!b) u := by
  ext i j
  simp only [gramB_apply]
  refine Finset.sum_congr (Finset.filter_congr fun a _ => ?_) fun _ _ => rfl
  cases ε a <;> cases b <;> simp

theorem gramX_eq (ε : Fin m → Bool) (u : Fin m → Fin n → ℂ) :
    gramX ε u = gramB ε true u - gramB ε false u := by
  ext i j
  simp [gramX, gramB, Qp, evX, map_sub]

private theorem gramB_eq_conjTranspose_diagonal_mul (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    gramB ε b u = (Matrix.of u)ᴴ * diagonal (fun a => if ε a = b then (1 : ℂ) else 0) * Matrix.of u := by
  ext i j
  simp [gramB_apply, Matrix.mul_apply, diagonal_apply, Finset.sum_filter, conjTranspose_apply]

theorem gramB_mul (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) (a : Matrix (Fin n) (Fin n) ℂ) :
    gramB ε b (Matrix.of u * a) = aᴴ * gramB ε b u * a := by
  rw [gramB_eq_conjTranspose_diagonal_mul ε b u]
  refine (gramB_eq_conjTranspose_diagonal_mul ε b (Matrix.of u * a)).trans ?_
  change (Matrix.of u * a)ᴴ * _ * (Matrix.of u * a) = _
  rw [conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem epsT_pos {t : ℝ} (ht : 0 < t) (ε : Fin m → Bool) : epsT t ε = ε := by
  funext a; simp [epsT, ht]

theorem epsT_nonpos {t : ℝ} (ht : ¬ 0 < t) (ε : Fin m → Bool) : epsT t ε = fun a => !ε a := by
  funext a; simp [epsT, ht]

theorem cnt_add (ε : Fin m → Bool) : cnt ε true + cnt ε false = m := by
  simp only [cnt]
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (p := fun a => ε a = true)
  simpa using this

theorem chN_mul_gZf (ε : Fin m → Bool) {t c : ℝ} (htc : |t| = c) (b Z : Matrix (Fin n) (Fin n) ℂ) (hb : bᴴ = b)
    (u : Fin m → Fin n → ℂ) : chN ε t b u * gZf ε t c Z u = gZf ε t c (Z + b) u := by
  unfold chN gZf
  rw [← Complex.exp_add]
  congr 1
  rw [gramX_eq, conjTranspose_add, hb]
  by_cases ht : 0 < t
  · rw [epsT_pos ht]
    have htc' : t = c := by rw [← htc, abs_of_pos ht]
    subst htc'
    simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]
    ring
  · rw [epsT_nonpos ht, gramB_not, gramB_not]
    have htc' : t = -c := by rw [← htc, abs_of_nonpos (not_lt.mp ht), neg_neg]
    subst htc'
    simp only [Bool.not_true, Bool.not_false, Matrix.add_mul, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub,
      Complex.ofReal_neg]
    ring

theorem trace_cyc (Z a G : Matrix (Fin n) (Fin n) ℂ) : (Z * (aᴴ * G * a)).trace = (a * Z * aᴴ * G).trace := by
  rw [show Z * (aᴴ * G * a) = (Z * aᴴ * G) * a by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem gZf_mul (ε : Fin m → Bool) (t c : ℝ) (Z a : Matrix (Fin n) (Fin n) ℂ) (u : Fin m → Fin n → ℂ) :
    gZf ε t c Z (Matrix.of u * a) = gZf ε t c (a * Z * aᴴ) u := by
  unfold gZf
  rw [gramB_mul, gramB_mul, trace_cyc, trace_cyc, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

end PositivityTheory.Rg.Sw.Glob.GaussH
end
end

section

noncomputable section

open MeasureTheory FourierTransform

namespace PositivityTheory.Rg.Sw.Glob.PlanchH

open PositivityTheory.Rg.Sw.Glob.FTD

variable {m n : ℕ}

theorem haar_linR (A : (Fin m → Fin n → ℂ) ≃L[ℝ] V m n) : ∃ c : ℝ, 0 < c ∧ ∀ F : V m n → ℝ, Continuous F →
    ∫ y : Fin m → Fin n → ℂ, F (A y) = c * ∫ w, F w := by
  have : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  set μ' : Measure (V m n) := (volume : Measure (Fin m → Fin n → ℂ)).map A with hμ'
  have : μ'.IsAddHaarMeasure := A.isAddHaarMeasure_map volume
  have h := Measure.isAddLeftInvariant_eq_smul μ' volume
  refine ⟨Measure.addHaarScalarFactor μ' volume, by
    exact_mod_cast Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure μ' volume, fun F hF => ?_⟩
  have h' : ∫ y, F y ∂μ' = ∫ y, F y ∂(Measure.addHaarScalarFactor μ' volume • volume) :=
    congrArg (fun ν => ∫ y, F y ∂ν) h
  rw [← integral_map A.continuous.aemeasurable hF.aestronglyMeasurable, ← hμ', h', integral_smul_nnreal_measure]
  simp [NNReal.smul_def]

end PositivityTheory.Rg.Sw.Glob.PlanchH

namespace PositivityTheory.Rg.Sw.Glob

open PositivityTheory.Rg.Sw.Glob.FTD PositivityTheory.Rg.Sw.Glob.PlanchH

theorem planchLoc : PlanchLoc := by
  intro m n ε t ht
  obtain ⟨c1, hc1, hft⟩ := ftLoc_eq (m := m) (n := n) ε t ht
  obtain ⟨kM, hkM, hM⟩ := haar_linR (Mt (m := m) (n := n) ε t ht)
  obtain ⟨kL, hkL, hL⟩ := haar_linR (Lc (m := m) (n := n))
  refine ⟨c1 ^ 2 * kM / kL, by positivity, fun f hf => ?_⟩
  obtain ⟨S, rfl⟩ := hf
  set g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Lc (m := m) (n := n)).symm S with hg
  have e1 : ∀ u, ‖ftLoc ε t (⇑S) u‖ ^ 2 = c1 ^ 2 * ‖(𝓕 g) (Mt ε t ht u)‖ ^ 2 := by
    intro u
    rw [hft S u, norm_mul, mul_pow, Complex.norm_real, Real.norm_of_nonneg hc1.le]
  have e2 : ∀ u, ‖S u‖ ^ 2 = ‖g (Lc u)‖ ^ 2 := by
    intro u
    simp [hg]
  simp_rw [e1, e2]
  have h1 := hM (fun w => ‖(𝓕 g) w‖ ^ 2) ((SchwartzMap.continuous _).norm.pow 2)
  have h2 := hL (fun w => ‖g w‖ ^ 2) ((SchwartzMap.continuous _).norm.pow 2)
  rw [integral_const_mul, h1, h2, SchwartzMap.integral_norm_sq_fourier g]
  field_simp

end PositivityTheory.Rg.Sw.Glob
end
end
