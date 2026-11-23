module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle190
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAlgebraIsotropicFlagSelfAdjointLevi
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle169
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle223
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle178
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle131
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle173
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle247
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle170
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle239
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle209
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle171
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle157
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle156
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle271
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle042
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle253
public import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle254
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFdegFdegOfOfIsDS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SettingBlocks
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MultiplicityGExists
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle024
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle022
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle255
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle256
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericLocalTermsSelfDualLattices
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle021
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001

@[expose] public section

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

noncomputable section

namespace GlobalTheory.LeviIso.Chart

def twist {j : ℕ} (p : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ →+* ℂ) (x : Fin j → Fin j → ℂ) : Fin j → Fin j → ℂ :=
  fun r s => (p * (Matrix.of x).map τ * p⁻¹) r s

theorem of_twist {j : ℕ} (p : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ →+* ℂ) (x : Fin j → Fin j → ℂ) :
    Matrix.of (twist p τ x) = p * (Matrix.of x).map τ * p⁻¹ := rfl

variable {j : ℕ} {p : Matrix (Fin j) (Fin j) ℂ} {τ : ℂ →+* ℂ}

theorem norm_tau (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) (z : ℂ) : ‖τ z‖ = ‖z‖ := by
  rcases hτ with rfl | rfl <;> simp

theorem tau_tau (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) (z : ℂ) : τ (τ z) = z := by
  rcases hτ with rfl | rfl <;> simp

theorem det_map_tau (x : Matrix (Fin j) (Fin j) ℂ) : (x.map τ).det = τ x.det := by
  rw [RingHom.map_det]; rfl

theorem det_twist (hp : p.det ≠ 0) (x : Fin j → Fin j → ℂ) :
    (Matrix.of (twist p τ x)).det = τ (Matrix.of x).det := by
  rw [of_twist, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul,
    Matrix.mul_nonsing_inv _ (Ne.isUnit hp), Matrix.det_one, one_mul, det_map_tau]

theorem det_twist_ne (hp : p.det ≠ 0) {x : Fin j → Fin j → ℂ} (hx : (Matrix.of x).det ≠ 0) :
    (Matrix.of (twist p τ x)).det ≠ 0 := by
  rw [det_twist hp]
  exact (map_ne_zero τ).2 hx

theorem twist_mul (hp : p.det ≠ 0) (x y : Fin j → Fin j → ℂ) :
    Matrix.of (twist p τ fun r s => (Matrix.of x * Matrix.of y) r s) =
      Matrix.of (twist p τ x) * Matrix.of (twist p τ y) := by
  have e : (Matrix.of fun r s => (Matrix.of x * Matrix.of y) r s) = Matrix.of x * Matrix.of y := rfl
  rw [of_twist, of_twist, of_twist, e, Matrix.map_mul]
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul_cancel_left _ _ (Ne.isUnit hp)]

theorem twist_inj (hp : p.det ≠ 0) {x y : Fin j → Fin j → ℂ}
    (h : Matrix.of (twist p τ x) = Matrix.of (twist p τ y)) : x = y := by
  have h2 := congrArg (fun M => p⁻¹ * (M * p)) h
  simp only [of_twist, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (Ne.isUnit hp), Matrix.mul_one,
    Matrix.nonsing_inv_mul_cancel_left _ _ (Ne.isUnit hp)] at h2
  funext r s
  exact τ.injective (congrFun (congrFun h2 r) s)

theorem twist_surj (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) (hp : p.det ≠ 0) (y : Matrix (Fin j) (Fin j) ℂ) :
    ∃ x, Matrix.of (twist p τ x) = y := by
  refine ⟨fun r s => τ ((p⁻¹ * y * p) r s), ?_⟩
  have e : (Matrix.of fun r s => τ ((p⁻¹ * y * p) r s)).map τ = p⁻¹ * y * p := by
    ext r s
    simp only [Matrix.map_apply, Matrix.of_apply, tau_tau hτ]
  rw [of_twist, e]
  simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit hp), Matrix.mul_one,
    Matrix.mul_nonsing_inv_cancel_left _ _ (Ne.isUnit hp)]

theorem measurePreserving_twist (hτ : τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) (hp : p.det ≠ 0) :
    MeasurePreserving (twist p τ) (haarLoc j) (haarLoc j) := by
  have hq : p⁻¹.det ≠ 0 := (Matrix.isUnit_nonsing_inv_det p (Ne.isUnit hp)).ne_zero
  have h1 := GlobalTheory.HaarMul.measurePreserving_mul_mul j p p⁻¹ hp hq
  rcases hτ with rfl | rfl
  · exact h1
  · exact h1.comp (haarLoc_conj_and_null j).1

theorem uMat_injective {n : ℕ} {ε : Fin n → Bool} {g h : Formalism.REAL.UJ ε} (e : uMat g = uMat h) : g = h :=
  Subtype.ext (Units.ext e)

theorem exists_leviChart : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (C : ∀ i, Matrix (Fin (j i)) (Fin n) ℂ) (A₀ : Matrix (Fin n) (Fin n₀) ℂ) (τ τ₀ : ℂ →+* ℂ), (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) → (τ₀ = RingHom.id ℂ ∨ τ₀ = starRingEnd ℂ) → n = n₀ + 2 * ∑ i, j i → (∀ i, C i * A i = 1) → (∀ i k, i ≠ k → C i * A k = 0) → (∀ i k, (A i)ᴴ * Formalism.REAL.Jm ε * A k = 0) → (∀ i, (A i)ᴴ * Formalism.REAL.Jm ε * A₀ = 0) → A₀ᴴ * Formalism.REAL.Jm ε * A₀ = Formalism.REAL.Jm ε₀ → SpansFlag A W → IsIsoFlag ε j W → ∃ θ, IsLeviChart ε ε₀ W A A₀ τ τ₀ θ := by
  intro n n₀ a j ε ε₀ W A C A₀ τ τ₀ hτ hτ₀ hn hC1 hC0 hAA hA0 h00 hsp hiso
  obtain ⟨B, p, q, hB1, hB0, htri, hAB, hBA, hpq⟩ := BlockGS.block_gramSchmidt n a j A C hC1 hC0
  have hspB : SpansFlag B W := GlobalTheory.T.columnBlocksSpanFlag_of_block_triangular n a j A B p q W htri hAB hBA hsp
  have hBJA : ∀ (m : ℕ) (X : Matrix (Fin n) (Fin m) ℂ), (∀ i, (A i)ᴴ * Formalism.REAL.Jm ε * X = 0) →
      ∀ i, (B i)ᴴ * Formalism.REAL.Jm ε * X = 0 := by
    intro m X hX i
    rw [hBA i, Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.sum_mul]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc (q k i)ᴴ, Matrix.mul_assoc (q k i)ᴴ, hX, Matrix.mul_zero]
  have hBJB : ∀ i k, (B i)ᴴ * Formalism.REAL.Jm ε * B k = 0 := by
    intro i k
    refine hBJA _ _ (fun l => ?_) i
    rw [hBA k, Matrix.mul_sum]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [← Matrix.mul_assoc, hAA, Matrix.zero_mul]
  obtain ⟨B₀, s, d, hF, hA₀⟩ := GlobalTheory.T.exists_orthonormalFrame_of_isotropicBlocks n n₀ a j ε ε₀ B A₀ hn hB1 hB0 hBJB (hBJA _ _ hA0) h00
  obtain ⟨θ₀, hθm, hθ⟩ := GlobalTheory.T.exists_measurable_unitaryLeviBlockMap n n₀ a j ε ε₀ B B₀ hF
  obtain ⟨C₀, hC₀, hC₀m⟩ := exists_conj_gauge_invariant n₀ ε₀ τ₀ hτ₀
  have hp : ∀ i, (p i i).det ≠ 0 := fun i => (Matrix.isUnit_det_of_right_inverse (hpq i)).ne_zero
  let R : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ :=
    Prod.map (fun x i => twist (p i i) τ (x i)) (fun g => s * C₀ g * s⁻¹)
  have hcont : Continuous fun g : Formalism.REAL.UJ ε₀ => s * C₀ g * s⁻¹ :=
    (continuous_const.mul C₀.continuous_toFun).mul continuous_const
  have hR1 : Measurable fun (x : ∀ i, Fin (j i) → Fin (j i) → ℂ) i => twist (p i i) τ (x i) :=
    Measurable.of_eval fun i =>
      (measurePreserving_twist hτ (hp i)).measurable.comp (measurable_pi_apply i)
  have hRm : Measurable R := hR1.prodMap hcont.measurable
  have hθR : ∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ₀ (R z)) =
      lev ε B B₀ (fun i => Matrix.of (twist (p i i) τ (z.1 i))) (uMat (s * C₀ z.2 * s⁻¹)) :=
    fun z hz => hθ (R z) fun i => det_twist_ne (hp i) (hz i)
  refine ⟨θ₀ ∘ R, hθm.comp hRm, fun m => ?_, fun z z' hz hz' => ⟨?_, fun e => ?_⟩,
    fun z hz => ⟨fun i => ?_, fun g hg hg0 => ?_⟩, fun μ c hμ hc => ?_⟩
  · rw [GlobalTheory.T.mem_isotropicFlagSelfAdjointLevi_iff_block n n₀ a j ε ε₀ B B₀ hF W hspB m]
    constructor
    · rintro ⟨x, g, hx, hm⟩
      choose y hy using fun i => twist_surj hτ (hp i) (x i)
      have hy0 : ∀ i, (Matrix.of (y i)).det ≠ 0 := by
        intro i h0
        apply hx i
        rw [← hy i, det_twist (hp i), h0, map_zero]
      refine ⟨(y, C₀.symm (s⁻¹ * g * s)), hy0, uMat_injective ?_⟩
      have e : s * C₀ (C₀.symm (s⁻¹ * g * s)) * s⁻¹ = g := by
        rw [ContinuousMulEquiv.apply_symm_apply]; group
      rw [Function.comp_apply, hθR _ hy0, hm]
      simp only [hy, e]
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, _, fun i => det_twist_ne (hp i) (hz i), hθR z hz⟩
  · apply uMat_injective
    have hzz : ∀ i, (Matrix.of fun r s => (Matrix.of (z.1 i) * Matrix.of (z'.1 i)) r s).det ≠ 0 := by
      intro i
      change (Matrix.of (z.1 i) * Matrix.of (z'.1 i)).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero (hz i) (hz' i)
    have e : uMat (s * C₀ (z.2 * z'.2) * s⁻¹) = uMat (s * C₀ z.2 * s⁻¹) * uMat (s * C₀ z'.2 * s⁻¹) := by
      change _ = uMat ((s * C₀ z.2 * s⁻¹) * (s * C₀ z'.2 * s⁻¹))
      congr 1
      rw [map_mul]; group
    change uMat (θ₀ (R z)) * uMat (θ₀ (R z')) = uMat (θ₀ (R _))
    rw [hθR z hz, hθR z' hz', hθR _ hzz, ← hF.lev_mul]
    simp only [twist_mul (hp _), e]
  · have e2 : uMat (θ₀ (R z)) = uMat (θ₀ (R z')) := congrArg uMat e
    rw [hθR z hz, hθR z' hz'] at e2
    obtain ⟨e3, e4⟩ := hF.lev_inj _ _ _ _ e2
    refine Prod.ext (funext fun i => twist_inj (τ := τ) (hp i) (congrFun e3 i)) ?_
    have e5 := uMat_injective e4
    exact C₀.injective (mul_left_cancel (mul_right_cancel e5))
  · rw [Function.comp_apply, Size.locSize_blocks n a j B W hB1 hB0 hspB _
      (fun i => Matrix.of (twist (p i i) τ (z.1 i))) (fun i => det_twist_ne (hp i) (hz i))
      (fun i => by rw [hθR z hz, hF.lev_mul_B]) i, det_twist (hp i), norm_tau hτ]
  · refine GlobalTheory.T.flagStabilizer_mul_inv_leviComponent_mem_unipotent n n₀ a j ε ε₀ B B₀ hF W A A₀ p d s (C₀ z.2) (fun i => (Matrix.of (z.1 i)).map τ) g _
      hsp hspB (fun k i h => (htri k i h).1) hp hAB hA₀ (fun i => ?_) hg (by rw [hC₀]; exact hg0) (hθR z hz)
    rw [det_map_tau]
    exact (map_ne_zero τ).2 (hz i)
  · have hR : MeasurePreserving R
        ((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod
          (ENNReal.ofReal c • Formalism.REAL.muG ε₀))
        ((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod
          (ENNReal.ofReal c • Formalism.REAL.muG ε₀)) := by
      refine MeasurePreserving.prod ?_ ⟨hcont.measurable, hC₀m s c hc⟩
      exact measurePreserving_pi _ _ fun i => (measurePreserving_twist hτ (hp i)).smul_measure _
    rw [← Measure.map_map hθm hRm, hR.map_eq]
    obtain ⟨g1, g2⟩ := GlobalTheory.T.levi_chart_map_haar_carried_invariant n n₀ a j ε ε₀ B B₀ hF W hspB θ₀ hθm hθ c
    have g3 := GlobalTheory.T.isRadial_map_unitaryLeviBlockProduct n n₀ a j ε ε₀ B B₀ hF θ₀ hθm hθ c hc
    have hν : IsGaugeSub (flagM ε W) (n₀ ^ 2 + 2 * ∑ i, j i ^ 2) _ := ⟨g1, g2, g3⟩
    have hd : n - 2 * ∑ i, j i = n₀ := by omega
    have halg := GlobalTheory.LeviAlgebra.exists_levi_algebra n ε a j W hiso
    rw [hd] at halg
    obtain ⟨𝒜, E, a1, a2, a3, a4⟩ := halg
    rw [a4] at hμ hν
    exact (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε 𝒜 _ E a1 a2 a3 _ hν).2.2.1 μ hμ

end GlobalTheory.LeviIso.Chart
end
end

section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas Formalism.REAL

noncomputable section

namespace GlobalTheory.NilCov

variable {n : ℕ} {ε : Fin n → Bool} {d : ℕ}

theorem continuous_uMat_sub_one : Continuous fun g : UJ ε => uMat g - 1 :=
  (Units.continuous_val.comp continuous_subtype_val).sub continuous_const

theorem continuous_coord (E : Fin d → Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun (g : UJ ε) (i : Fin d) => ipL (E i) (uMat g - 1) :=
  continuous_pi fun i => (ipL (E i)).continuous_of_finiteDimensional.comp continuous_uMat_sub_one

theorem continuous_hs_sub_one : Continuous fun g : UJ ε => hs (uMat g - 1) := by
  unfold hs
  fun_prop

theorem mul_sub_one (g h : UJ ε) :
    uMat (g * h) - 1 = (uMat g - 1) + (uMat h - 1) + (uMat g - 1) * (uMat h - 1) := by
  have : uMat (g * h) = uMat g * uMat h := rfl
  rw [this]; noncomm_ring

theorem measurePreserving_coord {m : ℕ} {A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)}
    {E : Fin d → Matrix (Fin n) (Fin n) ℂ} {deg : Fin d → ℕ}
    (hle : ∀ c, A (c + 1) ≤ A c) (hm : A m = ⊥)
    (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hinv : ∀ c, ∀ X ∈ A c, Jm ε * Xᴴ * Jm ε ∈ A c)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hsp : ∀ c X, (X ∈ A c ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (E '' {i | c ≤ deg i}))
    {ν : Measure (UJ ε)} (hν : IsGaugeSub {g | uMat g - 1 ∈ A 0} d ν) :
    MeasurePreserving (fun (g : UJ ε) (i : Fin d) => ipL (E i) (uMat g - 1)) ν volume := by
  have hE0 : ∀ i, E i ∈ A 0 ∧ inG ε (E i) := fun i =>
    (hsp 0 (E i)).2 (Submodule.subset_span ⟨i, Nat.zero_le _, rfl⟩)
  have hsp0 : ∀ X, (X ∈ A 0 ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (Set.range E) := fun X => by
    simpa using hsp 0 X
  have hmul0 : ∀ X ∈ A 0, ∀ Y ∈ A 0, X * Y ∈ A 0 := fun X hX Y hY => hle 0 (hmul 0 X hX Y hY).1
  obtain ⟨σ, hσc, hσ⟩ := GlobalTheory.T.exists_orthonormal_lie_coordinates n d m ε A E hm hmul hle hinv hE hE0
  have hσ2 : ∀ x i, ipL (E i) (uMat (σ x) - 1) = x i := fun x => (hσ x).2
  have hinj : ∀ g h : UJ ε, uMat g - 1 ∈ A 0 → uMat h - 1 ∈ A 0 →
      (∀ i, ipL (E i) (uMat g - 1) = ipL (E i) (uMat h - 1)) → g = h := by
    intro g h hg hh hc
    have := sub_mem_of_coord_eq hmul hinv hE hsp hg hh m fun i _ => hc i
    rw [hm, Submodule.mem_bot, sub_eq_zero] at this
    exact Subtype.ext (Units.ext this)
  have hS : MeasurableSet {g : UJ ε | uMat g - 1 ∈ A 0} :=
    ((A 0).closed_of_finiteDimensional.preimage continuous_uMat_sub_one).measurableSet
  have hμ : IsGaugeSub {g | uMat g - 1 ∈ A 0} d ((volume : Measure (Fin d → ℝ)).map σ) := by
    refine ⟨?_, fun s hs => ?_, ?_⟩
    · rw [Measure.map_apply hσc.measurable hS.compl]
      convert measure_empty (μ := (volume : Measure (Fin d → ℝ)))
      ext x
      simpa using (hσ x).1
    · have hs' : uMat s - 1 ∈ A 0 := hs
      have hT := GlobalTheory.T.measurePreserving_add_of_triangular d deg (fun x i => ipL (E i) (uMat (s * σ x) - 1) - x i)
        (((continuous_coord E).comp (continuous_const.mul hσc)).sub continuous_id).measurable (by
          intro x y i hxy
          have h1 := sub_mem_of_coord_eq hmul hinv hE hsp (hσ x).1 (hσ y).1 (deg i) fun k hk => by
            rw [hσ2, hσ2, hxy k hk]
          have h2 := ipL_eq_zero_of_mem hE (fun i => (hE0 i).2) (hinv (deg i + 1))
            (fun X => (hsp (deg i + 1) X).1) (i := i) (by simp) (hmul _ _ h1 _ hs').2
          have h3 : (uMat s - 1) * (uMat (σ x) - uMat (σ y)) =
              (uMat s - 1) * (uMat (σ x) - 1) - (uMat s - 1) * (uMat (σ y) - 1) := by noncomm_ring
          rw [h3, map_sub] at h2
          simp only [mul_sub_one, map_add (f := _), hσ2]
          linarith)
      have he : (fun g => s * g) ∘ σ =
          σ ∘ fun x => x + fun i => ipL (E i) (uMat (s * σ x) - 1) - x i := by
        funext x
        refine hinj _ _ ?_ (hσ _).1 fun i => ?_
        · simp only [Function.comp, mul_sub_one]
          exact (A 0).add_mem ((A 0).add_mem hs' (hσ x).1) (hmul0 _ hs' _ (hσ x).1)
        · simp only [Function.comp, hσ2, Pi.add_apply]
          ring
      rw [Measure.map_map (measurable_const_mul s) hσc.measurable, he,
        ← Measure.map_map hσc.measurable hT.measurable, hT.map_eq]
    · have hest := fun x => GlobalTheory.T.traceCoord_sq_sum_le_hilbertSchmidt_unitaryGroup n d ε E hE (fun i => (hE0 i).2) (σ x)
        ((hsp0 _).1 ⟨(A 0).sub_mem (hσ x).1 (hinv 0 _ (hσ x).1), inG_sub_inv _⟩)
      simp only [(hσ _).2] at hest
      have h0 : σ 0 = 1 := hinj _ _ (hσ 0).1 (by simp [uMat]) fun i => by
        rw [hσ2]; simp [uMat]
      have := GlobalTheory.T.tendsto_volume_sqrt_sublevel_div_pow_eq_volume_ball d (fun x => hs (uMat (σ x) - 1))
        (continuous_hs_sub_one.comp hσc).continuousAt (by simp [h0, uMat, hs])
        (fun x => (hest x).1) (fun x => (hest x).2)
      refine this.congr fun r => ?_
      rw [Measure.map_apply hσc.measurable
        (isClosed_le continuous_hs_sub_one.sqrt continuous_const).measurableSet]
      rfl
  have heq := (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε (A 0) d E hmul0 hE hsp0 ν hν).2.2.1 _ hμ
  refine ⟨(continuous_coord E).measurable, ?_⟩
  rw [← heq, Measure.map_map (continuous_coord E).measurable hσc.measurable]
  have : (fun (g : UJ ε) (i : Fin d) => ipL (E i) (uMat g - 1)) ∘ σ = id := by
    funext x i
    exact hσ2 x i
  rw [this, Measure.map_id]

theorem covol_le_prod_layers : ∀ (ι : Type) [Fintype ι] (n d m : ℕ) (ε : ι → Fin n → Bool) (A : ι → ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)) (E : ι → Fin d → Matrix (Fin n) (Fin n) ℂ) (deg : Fin d → ℕ), (∀ v c, A v (c + 1) ≤ A v c) → (∀ v, A v m = ⊥) → (∀ v c, ∀ X ∈ A v c, ∀ Y ∈ A v 0, X * Y ∈ A v (c + 1) ∧ Y * X ∈ A v (c + 1)) → (∀ v c, ∀ X ∈ A v c, Formalism.REAL.Jm (ε v) * Xᴴ * Formalism.REAL.Jm (ε v) ∈ A v c) → (∀ v i k, ((E v i * (E v k)ᴴ).trace).re = if i = k then 1 else 0) → (∀ v c X, (X ∈ A v c ∧ Formalism.REAL.inG (ε v) X) ↔ X ∈ Submodule.span ℝ (E v '' {i | c ≤ deg i})) → ∀ (ν : ∀ v, Measure (Formalism.REAL.UJ (ε v))) [∀ v, SigmaFinite (ν v)], (∀ v, IsGaugeSub {g | uMat g - 1 ∈ A v 0} d (ν v)) → ∀ (Γ : Subgroup (∀ v, Formalism.REAL.UJ (ε v))) (D : ∀ c : ℕ, Set (ι → {i : Fin d // deg i = c} → ℝ)), (∀ γ ∈ Γ, ∀ v, uMat (γ v) - 1 ∈ A v 0) → (∀ c, MeasurableSet (D c)) → (∀ (c : ℕ) (x : ι → {i : Fin d // deg i = c} → ℝ), ∃ γ ∈ Γ, (∀ v, uMat (γ v) - 1 ∈ A v c) ∧ (fun v (i : {i : Fin d // deg i = c}) => (((uMat (γ v) - 1) * (E v i.1)ᴴ).trace).re + x v i) ∈ D c) → covol (Γ : Set (∀ v, Formalism.REAL.UJ (ε v))) (Measure.pi ν) {g | ∀ v, uMat (g v) - 1 ∈ A v 0} ≤ ∏ c ∈ Finset.range m, volume (D c) := by
  intro ι _ n d m ε A E deg hle hm hmul hinv hE hsp ν _ hν Γ D hΓ hD hcov
  have hE0 : ∀ v i, E v i ∈ A v 0 ∧ inG (ε v) (E v i) := fun v i =>
    (hsp v 0 (E v i)).2 (Submodule.subset_span ⟨i, Nat.zero_le _, rfl⟩)
  have hanti : ∀ v, Antitone (A v) := fun v => antitone_nat_of_succ_le (hle v)
  have horth : ∀ v c i, deg i < c → ∀ X ∈ A v c, ipL (E v i) X = 0 := fun v c i hi X hX =>
    ipL_eq_zero_of_mem (hE v) (fun i => (hE0 v i).2) (hinv v c) (fun X => (hsp v c X).1)
      (by simpa using hi) hX
  have hdeg : ι → ∀ i, deg i < m := by
    intro v i
    by_contra hi
    have h1 := ((hsp v m (E v i)).2 (Submodule.subset_span ⟨i, not_lt.1 hi, rfl⟩)).1
    rw [hm, Submodule.mem_bot] at h1
    have := hE v i i
    simp [h1] at this
  have hmp := measurePreserving_pi ν (fun _ => (volume : Measure (Fin d → ℝ))) fun v =>
    measurePreserving_coord (hle v) (hm v) (hmul v) (hinv v) (hE v) (hsp v) (hν v)
  have hB : MeasurableSet {x : ι → Fin d → ℝ |
      ∀ c < m, (fun v (i : {i : Fin d // deg i = c}) => x v i.1) ∈ D c} := by
    simp only [Set.setOf_forall]
    refine MeasurableSet.iInter fun c => MeasurableSet.iInter fun _ => ?_
    exact (show Measurable fun (x : ι → Fin d → ℝ) v (i : {i : Fin d // deg i = c}) => x v i.1 by
      fun_prop) (hD c)
  rw [← GlobalTheory.T.volume_product_over_grading_layers ι d m deg D hdeg hD]
  refine le_trans ?_ (hmp.measure_preimage hB.nullMeasurableSet).le
  refine iInf_le_of_le _ (iInf_le_of_le (hmp.measurable hB) (iInf_le_of_le ?_ le_rfl))
  intro x hx
  have key : ∀ k : ℕ, ∃ γ ∈ Γ, (∀ v, uMat ((γ * x) v) - 1 ∈ A v 0) ∧ ∀ c < k,
      (fun v (i : {i : Fin d // deg i = c}) => ipL (E v i.1) (uMat ((γ * x) v) - 1)) ∈ D c := by
    intro k
    induction k with
    | zero => exact ⟨1, Γ.one_mem, by simpa using hx, fun c hc => absurd hc (Nat.not_lt_zero c)⟩
    | succ k ih =>
      obtain ⟨γ, hγ, h0, hc⟩ := ih
      obtain ⟨δ, hδ, hδk, hδD⟩ := hcov k fun v i => ipL (E v i.1) (uMat ((γ * x) v) - 1)
      have hexp : ∀ v, uMat ((δ * γ * x) v) - 1 = (uMat (δ v) - 1) + (uMat ((γ * x) v) - 1) +
          (uMat (δ v) - 1) * (uMat ((γ * x) v) - 1) := fun v => by
        rw [mul_assoc, Pi.mul_apply, mul_sub_one]
      have hprod : ∀ v, (uMat (δ v) - 1) * (uMat ((γ * x) v) - 1) ∈ A v (k + 1) := fun v =>
        (hmul v k _ (hδk v) _ (h0 v)).1
      refine ⟨δ * γ, Γ.mul_mem hδ hγ, fun v => ?_, fun c hck => ?_⟩
      · rw [hexp]
        exact (A v 0).add_mem ((A v 0).add_mem (hΓ δ hδ v) (h0 v)) (hanti v (Nat.zero_le _) (hprod v))
      · rcases (Nat.lt_succ_iff.1 hck).lt_or_eq with h | rfl
        · convert hc c h using 1
          funext v i
          rw [hexp, map_add (f := _), map_add (f := _), horth v k i.1 (by rw [i.2]; exact h) _ (hδk v),
            horth v (k + 1) i.1 (by rw [i.2]; exact hck) _ (hprod v), zero_add, add_zero]
        · convert hδD using 1
          funext v i
          rw [hexp, map_add (f := _), map_add (f := _), horth v (c + 1) i.1 (by rw [i.2]; exact hck) _ (hprod v), add_zero]
          rfl
  obtain ⟨γ, hγ, -, hc⟩ := key m
  exact ⟨γ, hγ, hc⟩

end GlobalTheory.NilCov
end
end

section

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.riemannianHaarGauge_transport_block_model : ∀ (n : ℕ) (ε : Fin n → Bool) (c : ℝ) (P Q : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin n) (hf : Sorts ε f), GlobalTheory.Count.IsGauge ε c → 0 < c ∧ HasEuclDensity ((ENNReal.ofReal c • Formalism.REAL.muG ε).map hf.equiv.symm) := by
  first | exact @GlobalTheory.GaugeQuot.gauge_transport | exact GlobalTheory.GaugeQuot.gauge_transport | (intros; apply GlobalTheory.GaugeQuot.gauge_transport <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

theorem _root_.GlobalTheory.T.normalizedFockForm_pureTensor_properties : ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n), (∀ f g : ι → MvPolynomial (Fin n × Fin n) ℂ, nfAll lam (ten f) (ten g) = ∏ τ, normFock (lam τ) (f τ) (g τ)) ∧ (∀ p : MvPolynomial (ι × Fin n × Fin n) ℂ, nfAll lam p p = 0 → p = 0) ∧ ∀ (G M : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) (y : Frames G), fnOf G s M (ten f) y = ∏ τ, ((M τ * y.1 τ).det ^ s τ * MvPolynomial.eval (fun v : Fin n × Fin n => (M τ * y.1 τ) v.1 v.2) (f τ)) := by
  first | exact @GlobalTheory.FockTen.nfAll_ten | exact GlobalTheory.FockTen.nfAll_ten | (intros; apply GlobalTheory.FockTen.nfAll_ten <;> assumption)
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace GlobalTheory.LowestVectorDegree

theorem isFdeg_fdegOf_lowest : ∀ (D : D7) (X : HidaSetting D) (v : InfinitePlace X.B.I.F),
    IsFdeg (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v)
      (fdegOf (Formalism.REAL.muG (X.B.I.ε v)) (X.B.σ v) (X.B.w v)) :=
  fun _ X v => isFdeg_fdegOf_of_isDS (X.ds v) (X.low v).1

end GlobalTheory.LowestVectorDegree
end

section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace GlobalTheory.St

theorem mExists_holds : ∀ D : D7, MExists D :=
  fun D => Formalism.L2.SG.Pf.mExists_of_cuts D weil_measure_compat infinite_measure_transfer

end GlobalTheory.St
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.hermitianTerm_stabilizer_commensurable : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (d : LocNG.Datum P) (τ : Term V M r), LocNG.IsTermOver P d τ → P.UW0 ⊓ LocNG.Aut τ.abelian₂ ≤ LocNG.Datum.Stab d ∧ (P.UW0 ⊓ LocNG.Aut τ.abelian₂).relIndex (LocNG.Datum.Stab d) ≠ 0 ∧ ∀ (d' : LocNG.Datum P) (τ' : Term V M r), LocNG.IsTermOver P d' τ' → (LocNG.Datum.Stab d).relIndex (LocNG.Datum.Stab d') ≠ 0 := by
  first | exact @GlobalTheory.HL.LocComm.stab_commensurable | exact GlobalTheory.HL.LocComm.stab_commensurable | (intros; apply GlobalTheory.HL.LocComm.stab_commensurable <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical

theorem _root_.GlobalTheory.T.selfDual_lattice_frame_eq_standard_translate : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∃ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L ∧ (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f ∧ ∃ n ∈ Fr.N, (∀ b, n (Fr.f b) = Fr.f b) ∧ Λ = img n (Fr.LamStd L) := by
  first | exact @GlobalTheory.StdLat.eq_img_lamStd | exact GlobalTheory.StdLat.eq_img_lamStd | (intros; apply GlobalTheory.StdLat.eq_img_lamStd <;> assumption)
end

section

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

theorem _root_.GlobalTheory.T.generic_local_terms_selfDual_lattices : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (f f' : Fin (r + 1) → V), (∃ n ∈ P.A.N, f = fun b => n (P.A.f b)) → (∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b)) → ∀ Λ : Submodule M.L.O V, ((H.IsSelfDual Λ ∧ Λ.FG ∧ (∀ i, H.MMfam (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) i ∈ Λ) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) ↔ ∃ d : LocNG.Datum P, LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)) ∧ ∀ d d' : LocNG.Datum P, LocNG.IsTermOver P d (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) → LocNG.IsTermOver P d' (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) → d = d' := by
  first | exact @GlobalTheory.HL.GenericTerm.generic_terms | exact GlobalTheory.HL.GenericTerm.generic_terms | (intros; apply GlobalTheory.HL.GenericTerm.generic_terms <;> assumption)
end
