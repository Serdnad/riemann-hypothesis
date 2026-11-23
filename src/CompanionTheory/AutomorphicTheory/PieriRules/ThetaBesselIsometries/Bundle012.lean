module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RightTypeAction
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle001
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DiscreteSeriesUnitarySmoothBasic
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle010
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.DerivedActionDiscreteSeriesProperties
public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.Bundle007
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle063
import Formalism.FormalDegreeBessel.FinalG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle035
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Function.L2Space
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem eLpNorm_two_of_lintegral_sq {α E : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    (f : α → E) (c : ℝ) (hf : AEStronglyMeasurable f μ) (hc : 0 ≤ c) (h : ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ 2 ∂μ = ENNReal.ofReal (c ^ 2)) :
    eLpNorm f 2 μ = ENNReal.ofReal c := by
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hf]
  have h2 : ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ = ENNReal.ofReal c ^ (2 : ℝ) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hc (by norm_num), Real.rpow_two, ← h]
    refine lintegral_congr fun x => ?_
    simp [enorm_eq_nnnorm]
  rw [h2, ← ENNReal.rpow_mul]
  norm_num

theorem integral_inner_of_isometric {α E F : Type*} [MeasurableSpace α] {μ : Measure α} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F] (S : Submodule ℂ E) (Φ : E → α → F)
    (hm : ∀ w ∈ S, MemLp (Φ w) 2 μ) (hn : ∀ w ∈ S, eLpNorm (Φ w) 2 μ = ENNReal.ofReal ‖w‖)
    (hadd : ∀ v ∈ S, ∀ w ∈ S, Φ (v + w) =ᵐ[μ] Φ v + Φ w)
    (hsmul : ∀ (c : ℂ), ∀ v ∈ S, Φ (c • v) =ᵐ[μ] c • Φ v) :
    ∀ w ∈ S, ∀ w' ∈ S, ∫ x, ⟪Φ w' x, Φ w x⟫_ℂ ∂μ = ⟪w', w⟫_ℂ := by
  let L : S →ₗᵢ[ℂ] Lp F 2 μ :=
    { toFun := fun v => (hm v v.2).toLp (Φ v)
      map_add' := fun v w => by
        rw [← MemLp.toLp_add]
        exact MemLp.toLp_congr _ _ (hadd v v.2 w w.2)
      map_smul' := fun c v => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        exact MemLp.toLp_congr _ _ (hsmul c v v.2)
      norm_map' := fun v => by
        change ‖(hm v v.2).toLp (Φ v)‖ = _
        rw [Lp.norm_toLp, hn v v.2, ENNReal.toReal_ofReal (norm_nonneg _)]
        rfl }
  intro w hw w' hw'
  have h := L.inner_map_map ⟨w', hw'⟩ ⟨w, hw⟩
  rw [L2.inner_def] at h
  refine Eq.trans ?_ h
  refine integral_congr_ae ?_
  filter_upwards [(hm w hw).coeFn_toLp, (hm w' hw').coeFn_toLp] with x h1 h2
  change _ = ⟪((hm w' hw').toLp (Φ w')) x, ((hm w hw).toLp (Φ w)) x⟫_ℂ
  rw [h1, h2]

theorem isoBessel_polarised : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (Bm : R.H → Wp), R.IsDG ε mu → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → (∀ w ∈ R.sm, MemLp (fun x : Formalism.QuantumDeterminants.Mt k r => Bm (R.σ (Matrix.of x) w)) 2 νq) ∧ ∀ w ∈ R.sm, ∀ w' ∈ R.sm, ∫ x, ⟪Bm (R.σ (Matrix.of x) w'), Bm (R.σ (Matrix.of x) w)⟫_ℂ ∂νq = ⟪w', w⟫_ℂ := by
  intro hK k r ε mu R Wp _ _ _ _ z π u μW μN μG νq Bm hDS hS hB
  obtain ⟨hae, -, -, hmeas⟩ := GlobalTheory.T.quotientMeasure_ae_mem_and_measurable_besselModel hK k r ε mu R Wp z π u μW μN μG νq hDS hS
  obtain ⟨-, -, -, hsm, -⟩ := GlobalTheory.rep_basic_of_isDS hK k r ε mu R hDS
  have hn : ∀ w ∈ R.sm, eLpNorm (fun x : Formalism.QuantumDeterminants.Mt k r => Bm (R.σ (Matrix.of x) w)) 2 νq =
      ENNReal.ofReal ‖w‖ := fun w hw =>
    eLpNorm_two_of_lintegral_sq _ _ (hmeas Bm hB.1 w hw) (norm_nonneg _) (hB.2 w hw)
  have hm : ∀ w ∈ R.sm, MemLp (fun x : Formalism.QuantumDeterminants.Mt k r => Bm (R.σ (Matrix.of x) w)) 2 νq := fun w hw =>
    by rw [memLp_iff, hn w hw]; exact ENNReal.ofReal_lt_top
  refine ⟨hm, ?_⟩
  refine integral_inner_of_isometric R.smSub
    (fun w (x : Formalism.QuantumDeterminants.Mt k r) => Bm (R.σ (Matrix.of x) w)) hm hn ?_ ?_
  · intro v hv w hw
    filter_upwards [hae] with x hx
    simp only [Pi.add_apply, map_add (f := _)]
    exact hB.1.1 _ (hsm _ hx v hv) _ (hsm _ hx w hw)
  · intro c v hv
    filter_upwards [hae] with x hx
    simp only [Pi.smul_apply, map_smul]
    exact hB.1.2.1 c _ (hsm _ hx v hv)

end GlobalTheory
end Gp91
end

section

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselIntertwine

theorem bessel_dsig (hK : PI.KFinSmooth) {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ}
    {R : Rep k r} (hR : R.IsDG ε mu) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {l : R.H → Wp} (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hl : IsBes R z π l) {X : Mx k r} (hX : Formalism.FourierDecayAlt.P.QrD.InLieW k r z X) (hX' : PI.UpqRep.InLieHpk k r X)
    {v : R.H} (hv : v ∈ R.sm) :
    l (PI.UpqRep.dsig (k := k) (r := r) R.σ X v) = Formalism.FourierDecayAlt.Q.dRep π X (l v) := by
  have hd := (GlobalTheory.T.frechetContinuous_continuousOn_orbit_hasDerivAt hK k r ε mu R hR Wp l hl.1 hl.2.1 hl.2.2.2 v hv).2 X hX'
  have h1 : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.Nset k r := by
    refine ⟨?_, ?_, ?_⟩
    · simp [Formalism.QuantumDeterminants.UH]
    · intro a i _
      simp [Matrix.one_apply]
    · intro i j _ _ _
      simp [Matrix.one_apply]
  have he : (fun t : ℝ => l (R.σ (NormedSpace.exp ((t : ℂ) • X)) v)) =
      fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) (l v) := by
    funext t
    have := hl.2.2.1 _ (Formalism.FourierDecayAlt.P.QrD.exp_uw hX t) 1 h1 v hv
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.Qx8.psi_one hz, one_smul] at this
    exact this
  rw [he] at hd
  exact hd.deriv.symm

theorem bessel_intertwines_glW : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp) (g : Mx k r), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.UpqRep.IsFrameW k r z g → IsBes R z π l → ∀ i j : Fin k, ∀ v ∈ R.sm, l (R.dC (g * Matrix.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) 1 * g⁻¹) v) = Formalism.FourierDecayAlt.Q.EcRep (Formalism.QuantumDeterminants.Hpk k r) π (g * Matrix.single ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) i) ((fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) j) 1 * g⁻¹) (l v) := by
  intro hK k r ε mu R hR Wp _ _ _ _ z π l g hz hT hg hl i j v hv
  obtain ⟨hF, hU⟩ := (GlobalTheory.T.frameW_conj_matrix_units k r z g hz hT hg).2.2.1
  rw [← hU i j]
  obtain ⟨h1, h2⟩ := Formalism.FourierDecayAlt.P.QrD.frame_lie hF i j
  set Y := Formalism.FourierDecayAlt.Q.unitB (Formalism.QuantumDeterminants.Hpk k r) _ i j with hY
  have hinv : (Formalism.QuantumDeterminants.Hpk k r)⁻¹ = Formalism.QuantumDeterminants.Hpk k r :=
    Matrix.inv_eq_left_inv (Formalism.QuantumDeterminants.hpkFacts k r).2.1
  have e1 : (1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)) =
      Formalism.QuantumDeterminants.hpart1 (Formalism.QuantumDeterminants.Hpk k r) Y := by
    rw [Formalism.QuantumDeterminants.hpart1, hinv, sub_eq_add_neg]
  have e2 : (1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r)) =
      Formalism.QuantumDeterminants.hpart2 (Formalism.QuantumDeterminants.Hpk k r) Y := by
    rw [Formalism.QuantumDeterminants.hpart2, hinv, sub_neg_eq_add]
  have l1 : PI.UpqRep.InLieHpk k r (Formalism.QuantumDeterminants.hpart1 (Formalism.QuantumDeterminants.Hpk k r) Y) := h1.1.1
  have l2 : PI.UpqRep.InLieHpk k r (Formalism.QuantumDeterminants.hpart2 (Formalism.QuantumDeterminants.Hpk k r) Y) := h2.1.1
  have s1 := ((GlobalTheory.DerivedAction.derived_action hK k r ε mu R hR _ l1).1 v hv).1
  have s2 := ((GlobalTheory.DerivedAction.derived_action hK k r ε mu R hR _ l2).1 v hv).1
  rw [Rep.dC, e1, e2, hl.1 _ s1 _ (Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul _ s2), hl.2.1 _ _ s2,
    bessel_dsig hK hR hz hl h1 l1 hv, bessel_dsig hK hR hz hl h2 l2 hv]
  rfl

end GlobalTheory.BesselIntertwine
end Gp91
end
