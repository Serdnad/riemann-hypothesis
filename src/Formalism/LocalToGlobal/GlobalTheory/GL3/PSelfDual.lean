module

import Formalism.LocalToGlobal.KernelLattices.ColumnData.SelfDual
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PIopNorm
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CanonicalTranslateJets
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfTrace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Polynomial.SpecificDegree
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SD

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits

variable (D : D7)

theorem mm_unimod (x : D.host.E) :
    x ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ↔
      ∀ y ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
        Algebra.trace D.host.K D.host.E (x * D.host.conj y) ∈
          (algebraMap (𝓞 D.host.K) D.host.K).range :=
  D.host.der.unimodular D.host.𝔟 D.host.𝔟_spec.1 x

theorem bb_ne_zero :
    (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
  rw [FractionalIdeal.coeIdeal_ne_zero]
  intro h
  have := D.host.𝔟_spec.2
  rw [h] at this
  simp at this

theorem ideal_mul_inverse_integral {b a : D.host.E}
    (hb : b ∈ (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))
    (ha : a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) :
    b * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  have h := FractionalIdeal.mul_mem_mul hb ha
  rw [Host.AA0] at h
  rw [mul_inv_cancel₀ (bb_ne_zero D), FractionalIdeal.mem_one_iff] at h
  obtain ⟨r, hr⟩ := h
  exact ⟨r, hr⟩

theorem one_mem_ideal_mul_inverse :
    (1 : D.host.E) ∈ (D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
      D.host.AA0 := by
  rw [Host.AA0, mul_inv_cancel₀ (bb_ne_zero D)]
  exact FractionalIdeal.one_mem_one _

variable {D}

theorem stdH_eq {N : ℕ} (x y : Fin N → D.host.E) :
    (letI := D.host.cmStar; stdH D.host.E N x y) = ∑ i, D.host.conj (x i) * y i := by
  unfold stdH
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [CU.star_conj]

theorem hom_step {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL' : letI := D.host.cmStar; IsSDLat D.host.E N' L')
    (Z : Matrix (Fin N') (Fin N) D.host.E)
    (hZ : ∀ x ∈ L, ∀ y ∈ L', (∑ i, D.host.conj (y i) * Z.mulVec x i) ∈
      (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) :
    Z ∈ YYl D L L' := by
  exact _root_.Formalism.L2.Ker.Cd.IntegralLatticeDensity.SD.hom_step (D := (_root_.Formalism.L2.Ker.Car.ofRec D)) L L' hL' Z hZ

theorem rank_one_mem_hom_lattice {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hL : letI := D.host.cmStar; IsSDLat D.host.E N L)
    {x : Fin N → D.host.E} (hx : x ∈ L) {y : Fin N' → D.host.E} (hy : y ∈ L') :
    (Matrix.of fun i j => y i * D.host.conj (x j)) ∈ homL D L L' := by
  refine Submodule.subset_span ?_
  intro v hv
  obtain ⟨r, hr⟩ := (hL.2.2 v).mp hv x hx
  have e : (Matrix.of fun i j => y i * D.host.conj (x j)).mulVec v = r • y := by
    funext i
    rw [Pi.smul_apply, Algebra.smul_def, hr, stdH_eq]
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e]
  exact L'.smul_mem r hy

theorem hYY_rank1 {N N' : ℕ} (X : Matrix (Fin N') (Fin N) D.host.E) (a : D.host.E)
    (x : Fin N → D.host.E) (y : Fin N' → D.host.E) :
    hYY D X (a • Matrix.of fun i j => y i * D.host.conj (x j)) =
      Algebra.trace D.host.K D.host.E
        ((∑ i, D.host.conj (y i) * X.mulVec x i) * D.host.conj a) := by
  unfold hYY
  congr 1
  simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, map_mul, CU.conj_conj,
    Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem alg_step (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (hA : admitted D N N' L L')
    (X : Matrix (Fin N') (Fin N) D.host.E)
    (hX : ∀ Y ∈ YYl D L L', ∃ c ∈ cc, hYY D X Y = ((c : 𝓞 D.host.K) : D.host.K)) :
    X ∈ AddSubgroup.closure {B | ∃ c ∈ cc, ∃ Z ∈ YYl D L L',
      B = (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) • Z} := by
  obtain ⟨c0, hc0, hc0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcc
  have hdvd : cc ∣ Ideal.span {c0} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hc0)
  obtain ⟨cc', hcc'⟩ := hdvd
  have hc0K : ((c0 : D.host.K)) ≠ 0 := by
    intro h; apply hc0ne; exact RingOfIntegers.ext h
  have hc0E : (((c0 : D.host.K) : D.host.E)) ≠ 0 := by
    intro h; apply hc0K; exact Subtype.ext h
  have key : ∀ e ∈ cc', ((((e : D.host.K) / (c0 : D.host.K) : D.host.K) : D.host.E)) • X ∈
      YYl D L L' := by
    intro e he
    apply hom_step L L' hA.2.2.2
    intro x hx y hy
    rw [mm_unimod]
    intro a ha
    obtain ⟨c', hc', hh⟩ := hX _
      (Submodule.subset_span ⟨a, ha, _, rank_one_mem_hom_lattice L L' hA.2.2.1 hx hy, rfl⟩)
    rw [hYY_rank1] at hh
    have hmem : c' * e ∈ Ideal.span {c0} := by rw [hcc']; exact Ideal.mul_mem_mul hc' he
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
    refine ⟨r, ?_⟩
    set k : D.host.K := (e : D.host.K) / (c0 : D.host.K)
    have e1 : (∑ i, D.host.conj (y i) * ((k : D.host.E) • X).mulVec x i) * D.host.conj a =
        k • ((∑ i, D.host.conj (y i) * X.mulVec x i) * D.host.conj a) := by
      rw [Algebra.smul_def, Matrix.smul_mulVec]
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [IntermediateField.algebraMap_apply]
      ring
    rw [e1, LinearMap.map_smul_of_tower, hh, smul_eq_mul]
    have hr' : ((r : D.host.K)) * (c0 : D.host.K) = (c' : D.host.K) * (e : D.host.K) := by
      have := congrArg (fun t : 𝓞 D.host.K => (t : D.host.K)) hr
      simpa using this
    show (r : D.host.K) = k * (c' : D.host.K)
    simp only [k]
    field_simp
    linear_combination hr'
  have main : ∀ z ∈ cc * cc', ((((z : D.host.K) / (c0 : D.host.K) : D.host.K) : D.host.E)) • X ∈
      AddSubgroup.closure {B | ∃ c ∈ cc, ∃ Z ∈ YYl D L L',
        B = (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) • Z} := by
    intro z hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro c hc e he
      refine AddSubgroup.subset_closure ⟨c, hc, _, key e he, ?_⟩
      rw [smul_smul]
      congr 1
      push_cast
      ring
    · intro u w hu hw
      have : ((((u + w : 𝓞 D.host.K) : D.host.K) / (c0 : D.host.K) : D.host.K) : D.host.E) • X =
          ((((u : D.host.K) / (c0 : D.host.K) : D.host.K) : D.host.E)) • X +
          ((((w : D.host.K) / (c0 : D.host.K) : D.host.K) : D.host.E)) • X := by
        rw [← add_smul]; congr 1; push_cast; ring
      rw [this]
      exact AddSubgroup.add_mem _ hu hw
  have h1 := main c0 (by rw [← hcc']; exact Ideal.mem_span_singleton_self c0)
  rwa [div_self hc0K, IntermediateField.coe_one, one_smul] at h1


variable (D) in
theorem coord (δ : ℂ) (hδ : δ ≠ 0) (u : D.what₂.Tau → ℂ)
    (hu : ∀ y : D.host.E, ∃ k : D.host.K,
      ∑ τ, u τ * embT D τ y = δ * D.host.φ₀ (k : D.host.E)) :
    ∃ x : D.host.E, ∀ τ, u τ = δ * embT D τ x := by
  exact _root_.Formalism.L2.Ker.Cd.IntegralLatticeDensity.SD.coord (_root_.Formalism.L2.Ker.Car.ofRec D) δ hδ u hu

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SD

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits

def CurveSelfDualRec : Prop :=
  ∀ D : D7, ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, δ ≠ 0 →
    ∀ x : ℂ, (∀ w ∈ lamOf D cc δ, ∃ b : ℤ,
      (x * starRingEnd ℂ w / (area (lamOf D cc δ) : ℂ)).im = b) → x ∈ lamOf D cc δ

namespace SD

variable {D : D7}

theorem mem_La_of {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {X : Matrix (Fin N') (Fin N) D.host.E}
    (hX : X ∈ AddSubgroup.closure {B | ∃ c ∈ cc, ∃ Z ∈ YYl D L L',
      B = (((c : 𝓞 D.host.K) : D.host.K) : D.host.E) • Z}) :
    (fun τ i j => δ * embT D τ (X i j) : VC D N N') ∈ La D (tor0 D cc δ) L L' := by
  induction hX using AddSubgroup.closure_induction with
  | mem B hB =>
    obtain ⟨c, hc, Z, hZ, rfl⟩ := hB
    refine AddSubgroup.subset_closure ⟨δ * D.host.φ₀ (((c : D.host.K) : D.host.E)),
      AddSubgroup.subset_closure ⟨c, hc, rfl⟩, Z, hZ, ?_⟩
    funext τ i j
    simp only [Matrix.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply, embV, tor0]
    rw [FL.embT_K D τ _ (c : D.host.K).2]
    ring
  | zero =>
    have : (fun τ i j => δ * embT D τ ((0 : Matrix (Fin N') (Fin N) D.host.E) i j) : VC D N N') = 0 := by
      funext τ i j; simp
    rw [this]; exact AddSubgroup.zero_mem _
  | add A B _ _ h1 h2 =>
    have : (fun τ i j => δ * embT D τ ((A + B) i j) : VC D N N') =
        (fun τ i j => δ * embT D τ (A i j)) + (fun τ i j => δ * embT D τ (B i j)) := by
      funext τ i j; simp [mul_add]
    rw [this]; exact AddSubgroup.add_mem _ h1 h2
  | neg A _ h1 =>
    have : (fun τ i j => δ * embT D τ ((-A) i j) : VC D N N') =
        -(fun τ i j => δ * embT D τ (A i j)) := by
      funext τ i j; simp
    rw [this]; exact AddSubgroup.neg_mem _ h1

end SD

theorem SelfDualRec_of_curve (hC : CurveSelfDualRec) : SelfDualRec := by
  intro D
  exact _root_.Formalism.L2.Ker.Cd.IntegralLatticeDensity.self_dual_lattice (_root_.Formalism.L2.Ker.Car.ofRec D)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CS

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits Polynomial

theorem im_comb (w1 w2 : ℂ) (m1 n1 m2 n2 : ℤ) :
    (starRingEnd ℂ ((m1 : ℂ) * w1 + (n1 : ℂ) * w2) * ((m2 : ℂ) * w1 + (n2 : ℂ) * w2)).im =
      ((m1 * n2 - n1 * m2 : ℤ) : ℝ) * (starRingEnd ℂ w1 * w2).im := by
  simp only [map_add (f := _), map_mul, map_intCast, Complex.mul_im, Complex.mul_re,
    Complex.add_im, Complex.add_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]
  push_cast
  ring

theorem area_of_basis (Λ : AddSubgroup ℂ) {w1 w2 : ℂ} (h1 : w1 ∈ Λ) (h2 : w2 ∈ Λ)
    (hb : ∀ w ∈ Λ, ∃ m n : ℤ, w = (m : ℂ) * w1 + (n : ℂ) * w2)
    (hD : (starRingEnd ℂ w1 * w2).im ≠ 0) :
    area Λ = |(starRingEnd ℂ w1 * w2).im| := by
  unfold area
  apply IsLeast.csInf_eq
  refine ⟨⟨abs_pos.mpr hD, w1, h1, w2, h2, rfl⟩, ?_⟩
  rintro a ⟨ha, u, hu, v, hv, rfl⟩
  obtain ⟨m1, n1, rfl⟩ := hb u hu
  obtain ⟨m2, n2, rfl⟩ := hb v hv
  rw [im_comb, abs_mul] at ha ⊢
  have hk : (m1 * n2 - n1 * m2 : ℤ) ≠ 0 := by
    intro h; rw [h] at ha; simp at ha
  have : (1 : ℝ) ≤ |((m1 * n2 - n1 * m2 : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk
  nlinarith [abs_nonneg (starRingEnd ℂ w1 * w2).im]

theorem cramer (x w1 w2 : ℂ) :
    x * ((starRingEnd ℂ w1 * w2).im : ℂ) =
      ((x * starRingEnd ℂ w1).im : ℂ) * w2 - ((x * starRingEnd ℂ w2).im : ℂ) * w1 := by
  apply Complex.ext <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im] <;> ring

theorem dual_of_basis (Λ : AddSubgroup ℂ) {w1 w2 : ℂ} (h1 : w1 ∈ Λ) (h2 : w2 ∈ Λ)
    (hD : (starRingEnd ℂ w1 * w2).im ≠ 0) (harea : area Λ = |(starRingEnd ℂ w1 * w2).im|)
    (x : ℂ) (hx : ∀ w ∈ Λ, ∃ b : ℤ, (x * starRingEnd ℂ w / (area Λ : ℂ)).im = b) : x ∈ Λ := by
  obtain ⟨b1, hb1⟩ := hx w1 h1
  obtain ⟨b2, hb2⟩ := hx w2 h2
  rw [Complex.div_ofReal_im, harea] at hb1 hb2
  set D := (starRingEnd ℂ w1 * w2).im with hDdef
  have hA : |D| ≠ 0 := abs_ne_zero.mpr hD
  have e1 : (x * starRingEnd ℂ w1).im = b1 * |D| := (div_eq_iff hA).mp hb1
  have e2 : (x * starRingEnd ℂ w2).im = b2 * |D| := (div_eq_iff hA).mp hb2
  have hc := cramer x w1 w2
  rw [← hDdef, e1, e2] at hc
  have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD
  have m1 : (b1 : ℂ) * w2 ∈ Λ := by rw [← zsmul_eq_mul]; exact Λ.zsmul_mem h2 b1
  have m2 : (b2 : ℂ) * w1 ∈ Λ := by rw [← zsmul_eq_mul]; exact Λ.zsmul_mem h1 b2
  rcases abs_cases D with ⟨hDa, -⟩ | ⟨hDa, -⟩
  · have : x = (b1 : ℂ) * w2 - (b2 : ℂ) * w1 := by
      apply mul_right_cancel₀ hD'
      rw [hc, hDa]; push_cast; ring
    rw [this]; exact Λ.sub_mem m1 m2
  · have : x = -((b1 : ℂ) * w2 - (b2 : ℂ) * w1) := by
      apply mul_right_cancel₀ hD'
      rw [hc, hDa]; push_cast; ring
    rw [this]; exact Λ.neg_mem (Λ.sub_mem m1 m2)

variable (D : D7)

theorem s_sq : (D.host.sqd) ^ 2 = -(D.host.d : D.host.E) :=
  D.host.sqd_sq

theorem d_pos : (0 : ℚ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos

alias K_repr := _root_.UpperTheory.Reformulated.B.CanonicalTranslateJets.K_repr

theorem embedding_sqrt_neg_d : D.host.φ₀ (D.host.sqd) = Complex.I * (Real.sqrt D.host.d : ℂ) :=
  D.host.φ₀_mem

theorem finrank_K : Module.finrank ℚ D.host.K = 2 := by
  apply Formalism.L2.Pj.LPb.finrank_K

theorem cc_basis (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) :
    ∃ c1 ∈ cc, ∃ c2 ∈ cc, (∀ c ∈ cc, ∃ m n : ℤ, c = (m : 𝓞 D.host.K) * c1 + (n : 𝓞 D.host.K) * c2) ∧
      ∀ p q : ℚ, (p : D.host.E) * ((c1 : D.host.K) : D.host.E) +
        (q : D.host.E) * ((c2 : D.host.K) : D.host.E) = 0 → p = 0 ∧ q = 0 := by
  exact _root_.Formalism.L2.Ker.Cd.IntegralLatticeDensity.CS.cc_basis (_root_.Formalism.L2.Ker.Car.ofRec D) cc hcc

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CS

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits

theorem CS.coe_intO (D : D7) (n : ℤ) :
    ((((n : 𝓞 D.host.K) : D.host.K)) : D.host.E) = (n : D.host.E) := by
  have h1 : ((n : 𝓞 D.host.K) : D.host.K) = (n : D.host.K) :=
    map_intCast (algebraMap (𝓞 D.host.K) D.host.K) n
  rw [h1]; exact map_intCast D.host.K.val n

theorem CS.im_conj_mul (δ a b : ℂ) :
    (starRingEnd ℂ (δ * a) * (δ * b)).im = Complex.normSq δ * (starRingEnd ℂ a * b).im := by
  have : starRingEnd ℂ (δ * a) * (δ * b) = (starRingEnd ℂ δ * δ) * (starRingEnd ℂ a * b) := by
    rw [map_mul]; ring
  rw [this, ← Complex.normSq_eq_conj_mul_self, Complex.im_ofReal_mul]

theorem curve_lattice_self_dual : CurveSelfDualRec := by
  intro D cc hcc δ hδ x hx
  obtain ⟨c1, hc1, c2, hc2, hspan, hind⟩ := CS.cc_basis D cc hcc.1
  set w1 := δ * D.host.φ₀ (((c1 : D.host.K) : D.host.E)) with hw1
  set w2 := δ * D.host.φ₀ (((c2 : D.host.K) : D.host.E)) with hw2
  have h1 : w1 ∈ lamOf D cc δ := AddSubgroup.subset_closure ⟨c1, hc1, rfl⟩
  have h2 : w2 ∈ lamOf D cc δ := AddSubgroup.subset_closure ⟨c2, hc2, rfl⟩
  have hb : ∀ w ∈ lamOf D cc δ, ∃ m n : ℤ, w = (m : ℂ) * w1 + (n : ℂ) * w2 := by
    intro w hw
    obtain ⟨c, hc, rfl⟩ := FL.lam_mem D cc δ w hw
    obtain ⟨m, n, rfl⟩ := hspan c hc
    refine ⟨m, n, ?_⟩
    have e : ((((m : 𝓞 D.host.K) * c1 + (n : 𝓞 D.host.K) * c2 : 𝓞 D.host.K) : D.host.K) : D.host.E) =
        (m : D.host.E) * ((c1 : D.host.K) : D.host.E) + (n : D.host.E) * ((c2 : D.host.K) : D.host.E) := by
      rw [← CS.coe_intO D m, ← CS.coe_intO D n]
      rfl
    rw [e, hw1, hw2, map_add (f := _), map_mul, map_mul, map_intCast, map_intCast]
    ring
  have hD : (starRingEnd ℂ w1 * w2).im ≠ 0 := by
    obtain ⟨p1, q1, e1⟩ := CS.K_repr D _ (c1 : D.host.K).2
    obtain ⟨p2, q2, e2⟩ := CS.K_repr D _ (c2 : D.host.K).2
    have hφ1 : D.host.φ₀ ((c1 : D.host.K) : D.host.E) =
        (p1 : ℂ) + (q1 : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℂ)) := by
      rw [e1, map_add (f := _), map_mul, map_ratCast, map_ratCast, CS.embedding_sqrt_neg_d]
    have hφ2 : D.host.φ₀ ((c2 : D.host.K) : D.host.E) =
        (p2 : ℂ) + (q2 : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℂ)) := by
      rw [e2, map_add (f := _), map_mul, map_ratCast, map_ratCast, CS.embedding_sqrt_neg_d]
    have him : (starRingEnd ℂ w1 * w2).im =
        Complex.normSq δ * (((p1 * q2 - q1 * p2 : ℚ) : ℝ) * Real.sqrt D.host.d) := by
      rw [hw1, hw2, CS.im_conj_mul, hφ1, hφ2]
      congr 1
      simp only [map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.mul_im,
        Complex.mul_re, Complex.add_im, Complex.add_re, Complex.ratCast_re, Complex.ratCast_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re,
        Complex.neg_im, map_ratCast]
      push_cast
      ring
    rw [him]
    have hsd : 0 < Real.sqrt D.host.d := IO.sqrt_d_pos D
    have hnδ : 0 < Complex.normSq δ := Complex.normSq_pos.mpr hδ
    intro h0
    have hpqR : ((p1 * q2 - q1 * p2 : ℚ) : ℝ) = 0 := by
      rcases mul_eq_zero.mp h0 with h | h
      · exact absurd h hnδ.ne'
      · rcases mul_eq_zero.mp h with h' | h'
        · exact h'
        · exact absurd h' hsd.ne'
    have hpq : p1 * q2 - q1 * p2 = 0 := by exact_mod_cast hpqR
    have hpqE : (p1 : D.host.E) * q2 - q1 * p2 = 0 := by
      have := congrArg (fun t : ℚ => (t : D.host.E)) hpq
      push_cast at this
      exact this
    by_cases hq : q1 = 0 ∧ q2 = 0
    · have r := hind p2 (-p1) (by rw [e1, e2, hq.1, hq.2]; push_cast; ring)
      have hp1 : p1 = 0 := by linarith [r.2]
      have r2 := hind 1 0 (by rw [e1, hp1, hq.1]; push_cast; ring)
      exact one_ne_zero r2.1
    · have r := hind q2 (-q1) (by rw [e1, e2]; push_cast; linear_combination hpqE)
      exact hq ⟨by linarith [r.2], r.1⟩
  exact CS.dual_of_basis _ h1 h2 hD (CS.area_of_basis _ h1 h2 hb hD) x hx

theorem self_dual_lattice : SelfDualRec := SelfDualRec_of_curve curve_lattice_self_dual

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity
