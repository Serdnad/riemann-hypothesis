module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle179
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle141
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle142
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairIdealKillsDiscriminantModules
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormTerminalDeterminant
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle181
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeAnalytic
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle182
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle183
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle180
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Real.Pi.Bounds
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle011
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle163
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle165
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle167
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121

@[expose] public section

section

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal Pointwise

noncomputable section

namespace GlobalTheory.AmpMoments

theorem lenA_mul {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (t x : MatKR k r) (s : Fin (r + 1) → ℂ)
    (hs : ∀ a, s a ≠ 0) (ht : ∀ a, t⁻¹ *ᵥ fvec k r z a = s a • fvec k r z a) (a : Fin (r + 1)) :
    lenA k r z (t * x) a = ‖s a‖ * lenA k r z x a := by
  have e : ∀ b, (WithLp.toLp 2 ((t * x)⁻¹ *ᵥ fvec k r z b) : EuclideanSpace ℂ (Fin (2 * r + k + 1))) =
      s b • WithLp.toLp 2 (x⁻¹ *ᵥ fvec k r z b) := fun b => by
    rw [Matrix.mul_inv_rev, ← Matrix.mulVec_mulVec, ht, Matrix.mulVec_smul, WithLp.toLp_smul]
  unfold lenA
  simp only [e]
  set v : Fin (r + 1) → EuclideanSpace ℂ (Fin (2 * r + k + 1)) := fun b => WithLp.toLp 2 (x⁻¹ *ᵥ fvec k r z b)
  have hsp : Submodule.span ℂ ((fun b => s b • v b) '' {b | b < a}) = Submodule.span ℂ (v '' {b | b < a}) := by
    apply le_antisymm <;> refine Submodule.span_le.2 ?_ <;> rintro _ ⟨b, hb, rfl⟩
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
    · have := Submodule.smul_mem (Submodule.span ℂ ((fun b => s b • v b) '' {b | b < a})) (s b)⁻¹
        (Submodule.subset_span ⟨b, hb, rfl⟩)
      simp only [smul_smul, inv_mul_cancel₀ (hs b), one_smul] at this
      exact this
  rw [hsp, ← infDist_smul₀ (s a)]
  congr 1
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (hs a)]
  exact ((Submodule.smul_mem_iff _ (inv_ne_zero (hs a)))).symm

theorem lintegral_translate {k r : ℕ} (ν : Measure (Mt k r)) (t : MatKR k r) (ht : IsUnit t.det)
    (F : Mt k r → ℝ≥0∞) :
    ∫⁻ y, F y ∂ν = ∫⁻ x, F (fun i j => (t * Matrix.of x) i j) ∂(ν.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) := by
  have hc : ∀ g : MatKR k r, Continuous fun x : Mt k r => (fun i j => (g * Matrix.of x) i j : Mt k r) := fun g =>
    (continuous_const.matrix_mul continuous_id : Continuous fun x : MatKR k r => g * x)
  let e : Mt k r ≃ₜ Mt k r :=
    { toFun := fun x => fun i j => (t⁻¹ * Matrix.of x) i j
      invFun := fun x => fun i j => (t * Matrix.of x) i j
      left_inv := fun x => (Matrix.mul_nonsing_inv_cancel_left t (Matrix.of x) ht :)
      right_inv := fun x => (Matrix.nonsing_inv_mul_cancel_left t (Matrix.of x) ht :)
      continuous_toFun := hc _
      continuous_invFun := hc _ }
  have := lintegral_map_equiv (μ := ν) (fun x => F (e.symm x)) e.toMeasurableEquiv
  refine Eq.trans ?_ this.symm
  exact lintegral_congr fun y => congrArg F (e.symm_apply_apply y).symm

theorem sq_nnnorm {V : Type} [NormedAddCommGroup V] (v : V) : (‖v‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal]; rfl

theorem haar_of_conj {k r : ℕ} {μ : Measure (Mt k r)} {t : MatKR k r} (ht : IsUnit t.det)
    (hN : ∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r)
    (h : PI.BesselPeriodGGP.IsHaarOn (Nset k r) (μ.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j)) :
    PI.BesselPeriodGGP.IsHaarOn (Nset k r) μ := by
  have hc : ∀ g g' : MatKR k r, Continuous fun x : Mt k r => (fun i j => (g * Matrix.of x * g') i j : Mt k r) :=
    fun g g' => ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const :
      Continuous fun x : MatKR k r => g * x * g')
  have hl : ∀ g : MatKR k r, Measurable (lmulM g : Mt k r → Mt k r) := fun g =>
    (show Continuous (lmulM g : Mt k r → Mt k r) from
      (continuous_const.matrix_mul continuous_id : Continuous fun x : MatKR k r => g * x)).measurable
  have i1 : ∀ x : MatKR k r, t * (t⁻¹ * x * t) * t⁻¹ = x := fun x => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left t x ht, Matrix.mul_nonsing_inv_cancel_right t x ht]
  have i2 : ∀ x : MatKR k r, t⁻¹ * (t * x * t⁻¹) * t = x := fun x => by
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left t x ht, Matrix.nonsing_inv_mul_cancel_right t x ht]
  let e0 : Mt k r ≃ₜ Mt k r :=
    { toFun := fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j
      invFun := fun x => fun i j => (t * Matrix.of x * t⁻¹) i j
      left_inv := fun x => (i1 (Matrix.of x) :)
      right_inv := fun x => (i2 (Matrix.of x) :)
      continuous_toFun := hc _ _
      continuous_invFun := hc _ _ }
  let e := e0.toMeasurableEquiv
  obtain ⟨h1, h2, h3, h4⟩ : PI.BesselPeriodGGP.IsHaarOn (Nset k r) (μ.map e) := h
  refine ⟨?_, fun h0 => h2 (by rw [h0, Measure.map_zero]), ?_, fun s hs => ?_⟩
  · rw [← e.map_symm_map (μ := μ)]
    exact e.symm.sigmaFinite_map
  · rw [e.map_apply] at h3
    rw [← h3]
    congr 1
    ext x
    have := hN (t⁻¹ * Matrix.of x * t)
    rw [i1] at this
    exact not_congr this.symm
  · have hs' : t⁻¹ * s * t ∈ Nset k r := (hN _).2 (by rwa [i1])
    apply e.map_measurableEquiv_injective
    show (μ.map (lmulM s)).map e = μ.map e
    rw [← h4 _ hs', Measure.map_map e.measurable (hl _), Measure.map_map (hl _) e.measurable]
    congr 1
    funext x
    show t⁻¹ * (s * Matrix.of x) * t = t⁻¹ * s * t * (t⁻¹ * Matrix.of x * t)
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left t _ ht]

theorem size_bound {b v g T x Cg Cu CT : ℝ} {r q : ℕ} (hb : Real.exp 1 < b) (hv : 1 ≤ v) (hvb : 2 * v ≤ b)
    (hg : 1 ≤ g) (hgb : g ≤ b ^ (2 * Cg)) (hCg : 8 ≤ Cg) (hT : T ≤ b ^ (CT * (2 * r + 2 : ℝ))) (hx0 : 0 ≤ x)
    (hx : x ≤ max (Real.pi / v / g) (Real.pi / v / g)⁻¹ ^ r) :
    x ^ (2 * q) * Hsq r T (b ^ max 2 Cu) ^ q ≤
      b ^ (2 * (2 * Cg + 2 + |CT| + 10 * max 2 Cu) * (2 * r + 2 : ℝ) * q) := by
  have hb2 : 2 < b := lt_trans (by have := Real.exp_one_gt_d9; linarith) hb
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hB : (2 : ℝ) ≤ max 2 Cu := le_max_left _ _
  have hp := Real.pi_gt_three
  have hg2 : 1 ≤ b ^ (2 * Cg) := hg.trans hgb
  have hM : max (Real.pi / v / g) (Real.pi / v / g)⁻¹ ≤ b ^ (2 * Cg + 2) := by
    rw [Real.rpow_add hb0, Real.rpow_two]
    refine max_le ?_ ?_
    · have : Real.pi / v / g ≤ Real.pi :=
        (div_le_self (by positivity) hg).trans (div_le_self (by positivity) hv)
      have := Real.pi_le_four
      nlinarith
    · rw [div_div, inv_div, div_le_iff₀ (by positivity)]
      have h1 : v * g ≤ b ^ 2 * b ^ (2 * Cg) := mul_le_mul (by nlinarith) hgb (by linarith) (by positivity)
      have : 0 ≤ b ^ (2 * Cg) * b ^ 2 := by positivity
      nlinarith
  have h1 : x ≤ b ^ ((2 * Cg + 2) * r) := by
    rw [Real.rpow_mul_natCast hb0.le]
    exact hx.trans (pow_le_pow_left₀ (le_max_of_le_left (by positivity)) hM r)
  have h2 : max 1 T ≤ b ^ (|CT| * (2 * r + 2 : ℝ)) :=
    max_le (Real.one_le_rpow hb1 (by positivity))
      (hT.trans (Real.rpow_le_rpow_of_exponent_le hb1 (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))))
  have h3 : x ^ 2 * Hsq r T (b ^ max 2 Cu) ≤
      b ^ (2 * (2 * Cg + 2 + |CT| + 10 * max 2 Cu) * (2 * r + 2 : ℝ)) := by
    unfold Hsq
    calc x ^ 2 * (max 1 T * (b ^ max 2 Cu) ^ (20 * (r + 1)))
        ≤ (b ^ ((2 * Cg + 2) * r)) ^ 2 * (b ^ (|CT| * (2 * r + 2 : ℝ)) * (b ^ max 2 Cu) ^ (20 * (r + 1))) := by
          gcongr
      _ = b ^ ((2 * Cg + 2) * r * (2 : ℕ) + (|CT| * (2 * r + 2 : ℝ) + max 2 Cu * (20 * (r + 1) : ℕ))) := by
          rw [Real.rpow_add hb0, Real.rpow_add hb0, Real.rpow_mul_natCast hb0.le _ 2,
            Real.rpow_mul_natCast hb0.le (max 2 Cu)]
      _ ≤ _ := by
          refine Real.rpow_le_rpow_of_exponent_le hb1 ?_
          push_cast
          have := abs_nonneg CT
          nlinarith [mul_nonneg this hr, mul_nonneg (by linarith : 0 ≤ Cg) hr, mul_nonneg (by linarith : 0 ≤ max 2 Cu) hr]
  rw [pow_mul, ← mul_pow, Real.rpow_mul_natCast hb0.le]
  exact pow_le_pow_left₀ (by unfold Hsq; positivity) h3 q

theorem radius_bound {k r m N q : ℕ} {Cn Cq : ℝ} (hm : m = 2 * r + 2) (hk : m ^ 4 ≤ k) (hC : |Cn| + |Cq| ≤ m)
    (hN : (N : ℝ) ≤ Cn * k * (m : ℝ) ^ 3) (hq : (q : ℝ) ≤ Cq * (r : ℝ) ^ 3) :
    N + (r + 1) * q ≤ k * m ^ 5 ∧ (r + 1) * q ≤ 2 * (2 * r + k + 1) ^ 2 := by
  have a1 := abs_nonneg Cn
  have a2 := abs_nonneg Cq
  have hN' : N ≤ m * k * m ^ 3 := by
    have : (N : ℝ) ≤ m * k * (m : ℝ) ^ 3 := hN.trans (by gcongr; linarith [le_abs_self Cn])
    exact_mod_cast this
  have hq' : q ≤ m * r ^ 3 := by
    have : (q : ℝ) ≤ m * (r : ℝ) ^ 3 := hq.trans (by gcongr; linarith [le_abs_self Cq])
    exact_mod_cast this
  have h1 : (r + 1) * q ≤ m * k :=
    calc (r + 1) * q ≤ m * (m * m ^ 3) :=
          Nat.mul_le_mul (by omega) (hq'.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)))
      _ = m * m ^ 4 := by ring
      _ ≤ m * k := Nat.mul_le_mul_left _ hk
  have h2 : m ≤ m ^ 4 := Nat.le_self_pow (by norm_num) m
  constructor
  · calc N + (r + 1) * q ≤ m * k * m ^ 3 + m ^ 4 * k := Nat.add_le_add hN' (h1.trans (Nat.mul_le_mul_right _ h2))
      _ = k * m ^ 4 * 2 := by ring
      _ ≤ k * m ^ 4 * m := Nat.mul_le_mul_left _ (by omega)
      _ = k * m ^ 5 := by ring
  · have : m * k ≤ k * k := Nat.mul_le_mul_right _ (h2.trans hk)
    nlinarith

theorem isBesselMapSm_of {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {ψ : MatKR k r → ℂ}
    {σ : MatKR k r → (H →L[ℂ] H)} {π : MatKR k r → (Wp →L[ℂ] Wp)} {B : H → Wp}
    (h : IsBesselMapSm (k := k) (r := r) z ψ σ π B) : PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z ψ σ π B := by
  have e : ∀ (w : List (MatKR k r)) (v : H), PI.UpqRep.dsigW (k := k) (r := r) σ w v = dsigW (k := k) (r := r) σ w v := by
    intro w v
    induction w with
    | nil => rfl
    | cons X w ih =>
      show PI.UpqRep.dsig σ X (PI.UpqRep.dsigW σ w v) = dsig σ X (dsigW σ w v)
      rw [ih]; rfl
  obtain ⟨h1, h2, h3, C, Ws, h4, h5⟩ := h
  exact ⟨h1, h2, h3, C, Ws, h4, fun v hv => by simp only [e]; exact h5 v hv⟩

end GlobalTheory.AmpMoments
end
end

section

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.MirSum

variable {g : ℕ} [Fact g.Prime]

theorem inMir_toG {m : ℕ} {M : Mt g m} (h : InMir M) : InMir ((toG M : Gn g m) : Mt g m) := by
  unfold toG
  split_ifs with hu
  · rw [hu.unit_spec]
    exact h
  · exact inMir_one m

theorem indV_sum (ψ : AddChar (ZMod g) ℂ) (m : ℕ) (f : Gn g m → ℂ) (s : Finset ℕ) (fs : ℕ → Gn g m → ℂ)
    (h : ∀ p : Gn g m, InMir (p : Mt g m) → f p = ∑ i ∈ s, fs i p) (x : Gn g (m + 1)) :
    indV ψ m f x = ∑ i ∈ s, indV ψ m (fs i) x := by
  simp only [indV]
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  split_ifs with hc
  · rw [h _ (inMir_toG hc.2.2), Finset.sum_mul]
  · simp

theorem inMir_one_iff (p : Gn g 1) : InMir (p : Mt g 1) ↔ p = 1 := by
  constructor
  · intro h
    ext i j
    fin_cases i
    fin_cases j
    simpa using h 0 0 rfl
  · rintro rfl i j _
    rfl

theorem isUniUp_one_iff (p : Gn g 1) : IsUniUp (p : Mt g 1) ↔ p = 1 := by
  constructor
  · intro h
    ext i j
    fin_cases i
    fin_cases j
    simpa using (h 0 0).2 rfl
  · rintro rfl a b
    fin_cases a
    fin_cases b
    simp

theorem br_one (M : Mt g 1) : br 0 1 M = M := by
  ext i j
  obtain rfl := Subsingleton.elim i 0
  obtain rfl := Subsingleton.elim j 0
  simp [br, entN]

theorem inPar_zero {n : ℕ} (M : Mt g n) : InPar 0 M := by
  intro i j hj _
  exact absurd hj (Nat.not_lt_zero _)

theorem inR_one_iff (p : Gn g 1) : InR 0 (p : Mt g 1) ↔ p = 1 := by
  show InPar 0 (p : Mt g 1) ∧ IsUniUp (br 0 1 (p : Mt g 1)) ↔ p = 1
  rw [br_one, isUniUp_one_iff]
  exact ⟨fun h => h.2, fun h => ⟨inPar_zero _, h⟩⟩

theorem res_one (F : Gn g 1 → ℂ) (h : Gn g 0) (u : Gn g 1) : res 0 1 F h u = F u := by
  have key : ∀ x : Gn g 1, (InPar 0 (x : Mt g 1) ∧ tl 0 (x : Mt g 1) = (h : Mt g 0) ∧
      br 0 1 (x : Mt g 1) = (u : Mt g 1)) ↔ x = u := by
    intro x
    rw [br_one]
    exact ⟨fun hx => Units.ext hx.2.2, fun hx => ⟨inPar_zero _, by ext i j; exact i.elim0, by rw [hx]⟩⟩
  unfold res
  simp only [key, Finset.sum_ite_eq', Finset.mem_univ, if_true, zero_mul, pow_zero, inv_one, one_mul]

theorem eU_one (ψ : AddChar (ZMod g) ℂ) : eU g 1 ψ = MonoidAlgebra.single 1 1 := by
  have hf : (Finset.univ.filter fun u : Gn g 1 => IsUniUp (u : Mt g 1)) = {1} := by
    ext u
    simp [isUniUp_one_iff]
  simp only [eU, eDat, hf]
  simp

theorem der_one (ψ : AddChar (ZMod g) ℂ) (F : Gn g 1 → ℂ) (h : Gn g 0) : der ψ 0 F h = F 1 := by
  show wh ψ (res 0 1 F h) = F 1
  unfold wh tr
  rw [eU_one, Finset.sum_eq_single (1 : Gn g 1)]
  · rw [MonoidAlgebra.coeff_single, Finsupp.single_eq_same, one_mul, res_one]
  · intro b _ hb
    simp [MonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hb]
  · intro h1
    exact absurd (Finset.mem_univ _) h1

theorem base (ψ : AddChar (ZMod g) ℂ) (F : Gn g 1 → ℂ) : F 1 = indR ψ 0 1 (der ψ 0 F) 1 := by
  have hc : (Finset.univ.filter fun p : Gn g 1 => InR 0 (p : Mt g 1)) = {1} := by
    ext p
    simp [inR_one_iff]
  have hs : ∀ y : Gn g 1, (InMir (y : Mt g 1) ∧ InR 0 ((y⁻¹ * 1 * y : Gn g 1) : Mt g 1)) ↔ y = 1 := by
    intro y
    rw [inMir_one_iff, inR_one_iff]
    simp
  unfold indR
  simp only [hc, hs, Finset.card_singleton, Nat.cast_one, inv_one, one_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, der_one, supFrom]
  simp

theorem eq_sum_indR_der : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (n : ℕ) (F : Gn g n → ℂ), 1 ≤ n → IsMirClass F → ∀ p : Gn g n, InMir (p : Mt g n) → F p = ∑ i ∈ Finset.range n, indR ψ i n (der ψ i F) p := by
  intro g _ ψ hψ n
  induction n with
  | zero =>
    intro F h
    omega
  | succ m ih =>
    intro F _ hF p hp
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · have hp1 := (inMir_one_iff p).mp hp
      subst hp1
      show F 1 = ∑ i ∈ Finset.range 1, indR ψ i 1 (der ψ i F) 1
      rw [Finset.sum_range_one]
      exact base ψ F
    · have hT := GlobalTheory.T.isMirabolicConjInvariant_twistedTailMeanFun g ψ m (m + 1) F hm (Nat.le_succ m) hF
      rw [GlobalTheory.T.mirabolic_function_eq_induced_derivative_add_tail g ψ hψ m F hm hF p hp, Finset.sum_range_succ,
        add_comm (indR ψ m (m + 1) (der ψ m F) p)]
      congr 1
      refine (indV_sum ψ m (tail ψ m F) (Finset.range m)
        (fun i => indR ψ i m (der ψ i (tail ψ m F))) (fun q hq => ih (tail ψ m F) hm hT q hq) p).trans ?_
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_range] at hi
      show indV ψ m (indR ψ i m (der ψ i (tail ψ m F))) p = _
      rw [GlobalTheory.T.mirabolicInductionPhiPlus_inductionFromBlockUni g ψ i m _ hi p hp, GlobalTheory.T.der_tail_of_lt_of_le g ψ i m (m + 1) F hi (Nat.le_succ m)]

end GlobalTheory.GLm.MirSum
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermFramePair_ideal_kills_discriminantModules : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → 𝔠 ^ 3 • dual H (latTh N.F N.F' Λ) ≤ latTh N.F N.F' Λ ∧ 𝔠 • dual H N.P0 ≤ N.P0 ∧ 𝔠 • N.P0 ≤ dual H N.P0 := by
  first | exact @GlobalTheory.DegCnt.Kill.main | exact GlobalTheory.DegCnt.Kill.main | (intros; apply GlobalTheory.DegCnt.Kill.main <;> assumption)
end

section

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.normal_form_terminal_determinant : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → N.bI Λ ≠ 0 ∧ bOne N.F' N.F Λ N.j = N.bI Λ ∧ delBar N.F N.F' Λ * (N.bI Λ : ℝ) ^ 2 = N.Del ∧ 1 ≤ delBar N.F N.F' Λ := by
  first | exact @GlobalTheory.DegCnt.SplitIdx.main | exact GlobalTheory.DegCnt.SplitIdx.main | (intros; apply GlobalTheory.DegCnt.SplitIdx.main <;> assumption)
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

theorem _root_.GlobalTheory.T.highest_weight_derivative_sum_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (u : V), IsHCParam lam → IsDS ε lam σ → IsDer ε σ V E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → ∀ G ∈ Vminus ε E (LamOf ε lam) u, ∑ a, ∑ b, E a b (at1 G a b) = 0 := by
  first | exact @GlobalTheory.Jet.Schmid.mul_vminus_eq_zero | exact GlobalTheory.Jet.Schmid.mul_vminus_eq_zero | (intros; apply GlobalTheory.Jet.Schmid.mul_vminus_eq_zero <;> assumption)
end

section

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder

theorem _root_.GlobalTheory.T.lowest_K_type_analytic : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ), IsURepOn (UJset ε) σ → IsDer ε σ V E → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → lowKSub ε lam σ ≤ V → ∀ x ∈ lowKSub ε lam σ, ∀ X : Matrix (Fin n) (Fin n) ℂ, inG ε X → AnalyticOnNhd ℝ (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) x) Set.univ := by
  first | exact @GlobalTheory.Jet.Anal.lowK_analytic | exact GlobalTheory.Jet.Anal.lowK_analytic | (intros; apply GlobalTheory.Jet.Anal.lowK_analytic <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

theorem _root_.GlobalTheory.T.map_infiniteGLHaarMeasure_mul_left : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (γ : MatInf E j), 0 < detNorm E j γ → (haarGL E j).map (fun g => γ * g) = haarGL E j := by
  first | exact @GlobalTheory.OrbitTerm.map_haarGL_mul_left_eq | exact GlobalTheory.OrbitTerm.map_haarGL_mul_left_eq | (intros; apply GlobalTheory.OrbitTerm.map_haarGL_mul_left_eq <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

theorem _root_.GlobalTheory.T.measure_inter_translate_eq_zero_of_covolume : ∀ (X : Type) [Mul X] [MeasurableSpace X] [MeasurableSpace.CountablySeparated X] (S : Set X) (μ : Measure X) [SigmaFinite μ] (U D : Set X), S.Countable → (∀ γ ∈ S, Measurable fun x => γ * x) → (∀ γ ∈ S, μ.map (fun x => γ * x) = μ) → (∀ γ ∈ S, ∀ δ ∈ S, ∃ ε ∈ S, ∀ x, ε * x = γ * (δ * x)) → (∀ γ ∈ S, ∃ δ ∈ S, (∀ x, δ * (γ * x) = x) ∧ ∀ x, γ * (δ * x) = x) → MeasurableSet U → (∀ γ ∈ S, ∀ x ∈ U, γ * x ∈ U) → MeasurableSet D → D ⊆ U → (∀ A, MeasurableSet A → A ⊆ U → (∀ γ ∈ S, ∀ x ∈ A, γ * x ∈ A) → covol S μ A = μ (A ∩ D)) → ∀ γ ∈ S, (∀ x ∈ U, γ * x ≠ x) → μ {x | x ∈ D ∧ γ * x ∈ D} = 0 := by
  first | exact @GlobalTheory.StrictDomain.measure_inter_translate_eq_zero | exact GlobalTheory.StrictDomain.measure_inter_translate_eq_zero | (intros; apply GlobalTheory.StrictDomain.measure_inter_translate_eq_zero <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm

theorem _root_.GlobalTheory.T.mem_latticeAut_split_iff_firstCol_single : ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), (∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ') → ∀ x : MatInf E (k + 1), (∀ w a, x w a 0 = if a = 0 then 1 else 0) → (x ∈ autGL E (k + 1) Λ ↔ (fun w a b => x w a.succ b.succ) ∈ autGL E k Λ' ∧ ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ ∀ w b, x w 0 b.succ = w.embedding (τ b)) := by
  first | exact @GlobalTheory.OrbitTerm.mem_autGL_split_iff | exact GlobalTheory.OrbitTerm.mem_autGL_split_iff | (intros; apply GlobalTheory.OrbitTerm.mem_autGL_split_iff <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

theorem _root_.GlobalTheory.T.isotropicFlagUnipotentDim_eq_sum_pairs : ∀ (n a : ℕ) (j : Fin a → ℕ) (r : ℕ → ℕ), (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) → r a = n - 2 * ∑ i, j i → (∀ b, 2 * a + 1 ≤ b → r b = 0) → dimN n j = ∑ c ∈ Finset.range (2 * a + 1), ∑ b ∈ Finset.range (2 * a + 1), r b * r (b + c + 1) := by
  first | exact @GlobalTheory.RadicalDimSum.dimN_eq_sum_pairs | exact GlobalTheory.RadicalDimSum.dimN_eq_sum_pairs | (intros; apply GlobalTheory.RadicalDimSum.dimN_eq_sum_pairs <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct

theorem _root_.GlobalTheory.T.lintegral_tsum_cosets_fundamentalDomain_eq_covol : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ S : Subgroup G) (μ : Measure G) (fund : Set G) (Φ : G → ENNReal) (ι : Type) [Countable ι] (r : ι → G), (Γ : Set G).Countable → S ≤ Γ → (∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) → MeasurableSet fund → (∀ y, ∃ γ ∈ Γ, γ * y ∈ fund) → (∀ γ ∈ Γ, γ ≠ 1 → μ ((fun y => γ * y) '' fund ∩ fund) = 0) → Measurable Φ → (∀ γ ∈ S, ∀ g, Φ (γ * g) = Φ g) → (∀ i, r i ∈ Γ) → (∀ γ ∈ Γ, ∃! i, γ * (r i)⁻¹ ∈ S) → ∫⁻ g in fund, ∑' i, Φ (r i * g) ∂μ = covol (S : Set G) (μ.withDensity Φ) Set.univ := by
  first | exact @GlobalTheory.StabUnfold.lintegral_tsum_cosets_eq_covol | exact GlobalTheory.StabUnfold.lintegral_tsum_cosets_eq_covol | (intros; apply GlobalTheory.StabUnfold.lintegral_tsum_cosets_eq_covol <;> assumption)
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

theorem _root_.GlobalTheory.T.sizeQ_saturatedIsotropicFlag_pos : ∀ (I : AutInst) (x : I.GA) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I x) j S → ∀ i : Fin a, 0 < Formalism.HN.sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc) := by
  first | exact @GlobalTheory.LeviIso.sizeQ_flag_pos | exact GlobalTheory.LeviIso.sizeQ_flag_pos | (intros; apply GlobalTheory.LeviIso.sizeQ_flag_pos <;> assumption)
end
