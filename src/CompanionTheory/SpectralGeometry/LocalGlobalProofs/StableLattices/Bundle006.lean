module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle002
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle025
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem isOpen_congK : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r ≤ 1), 0 < r →
    IsOpen (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) := by
  intro L _ _ n r h0 h1 hr
  have hball : IsOpen (Metric.closedBall (0 : L) r) :=
    IsUltrametricDist.isOpen_closedBall _ hr.ne'
  have hval : Continuous fun k : GL (Fin n) L => (k : Matrix (Fin n) (Fin n) L) :=
    Units.continuous_val
  have hinv : Continuous fun k : GL (Fin n) L => ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) :=
    Units.continuous_val.comp continuous_inv
  have hset : (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) =
      ⋂ i : Fin n, ⋂ j : Fin n,
        ((fun k : GL (Fin n) L => ((k : Matrix (Fin n) (Fin n) L) - 1) i j) ⁻¹'
            Metric.closedBall (0 : L) r ∩
          (fun k : GL (Fin n) L =>
            (((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) - 1) i j) ⁻¹'
            Metric.closedBall (0 : L) r) := by
    ext k
    simp only [SetLike.mem_coe, mem_congK, Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage,
      mem_closedBall_zero_iff]
  rw [hset]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
  · refine hball.preimage ?_
    exact (continuous_apply_apply i j).comp (hval.sub continuous_const)
  · refine hball.preimage ?_
    exact (continuous_apply_apply i j).comp (hinv.sub continuous_const)

end GlobalTheory.CompanionTheory.CartGL
end

section

open Matrix Topology

namespace GlobalTheory.CompanionTheory.CartGL

theorem exists_pi_entry_box {L : Type} [NontriviallyNormedField L] {n : ℕ}
    {A : Set (Fin n → Fin n → L)} {x : Fin n → Fin n → L} (hA : A ∈ 𝓝 x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : Fin n → Fin n → L, (∀ i j, ‖y i j - x i j‖ ≤ ε) → y ∈ A := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hA
  refine ⟨ε / 2, half_pos hε, fun y hy => hball ?_⟩
  have hd : dist y x ≤ ε / 2 := by
    rw [dist_pi_le_iff (half_pos hε).le]
    intro i
    rw [dist_pi_le_iff (half_pos hε).le]
    intro j
    rw [dist_eq_norm]
    exact hy i j
  rw [Metric.mem_ball]
  linarith

theorem exists_entry_box {L : Type} [NontriviallyNormedField L] {n : ℕ}
    {A : Set (Matrix (Fin n) (Fin n) L)} (hA : A ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) L)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ M : Matrix (Fin n) (Fin n) L,
      (∀ i j, ‖(M - 1) i j‖ ≤ ε) → M ∈ A := by
  obtain ⟨ε, hε, h⟩ := exists_pi_entry_box (x := (1 : Matrix (Fin n) (Fin n) L)) hA
  refine ⟨ε, hε, fun M hM => h M fun i j => ?_⟩
  have := hM i j
  rwa [Matrix.sub_apply] at this

theorem congK_cofinal (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ)
    (U : Set (GL (Fin n) L)) (hU : IsOpen U) (h1U : (1 : GL (Fin n) L) ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1), r ≤ ε →
      (GlobalTheory.CompanionTheory.CartGL.congK L n r h0 h1 : Set (GL (Fin n) L)) ⊆ U := by
  have hU1 : U ∈ 𝓝 (1 : GL (Fin n) L) := hU.mem_nhds h1U
  rw [Units.isEmbedding_embedProduct.nhds_eq_comap, Filter.mem_comap, map_one] at hU1
  obtain ⟨V, hV, hVU⟩ := hU1
  obtain ⟨A, hA, B, hB, hAB⟩ :=
    (mem_nhds_prod_iff (x := (1 : Matrix (Fin n) (Fin n) L)) (y := MulOpposite.op 1)).1 hV
  have hB' : MulOpposite.op ⁻¹' B ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) L) :=
    MulOpposite.continuous_op.continuousAt.preimage_mem_nhds hB
  obtain ⟨ε₁, hε₁, h₁⟩ := exists_entry_box hA
  obtain ⟨ε₂, hε₂, h₂⟩ := exists_entry_box hB'
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun r h0 h1 hr k hk => hVU (hAB ⟨?_, ?_⟩)⟩
  · exact h₁ _ fun i j => ((hk i j).1.trans hr).trans (min_le_left _ _)
  · exact h₂ _ fun i j => ((hk i j).2.trans hr).trans (min_le_right _ _)

end GlobalTheory.CompanionTheory.CartGL
end

section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL

theorem exists_isUnif : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L],
    ∃ p : Lˣ, GlobalTheory.CompanionTheory.CartGL.IsUnif p := by
  intro L _ _ _
  obtain ⟨x₀, h0, h1⟩ := NormedField.exists_norm_lt_one L
  have hc : IsCompact (Metric.ball (0 : L) 1) :=
    Metric.isCompact_of_isClosed_isBounded (IsUltrametricDist.isClosed_ball 0 1) Metric.isBounded_ball
  have hx : x₀ ∈ Metric.ball (0 : L) 1 := by simpa using h1
  obtain ⟨p, hp, hmax⟩ := hc.exists_isMaxOn ⟨x₀, hx⟩ continuous_norm.continuousOn
  have hmax' : ∀ w : L, ‖w‖ < 1 → ‖w‖ ≤ ‖p‖ := fun w hw =>
    isMaxOn_iff.mp hmax w (by simpa using hw)
  have hp1 : ‖p‖ < 1 := by simpa using hp
  have hp0 : 0 < ‖p‖ := h0.trans_le (hmax' x₀ h1)
  have hpne : p ≠ 0 := norm_pos_iff.mp hp0
  refine ⟨Units.mk0 p hpne, hp1, fun x hx0 => ?_⟩
  rw [Units.val_mk0]
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hy : 1 < ‖p‖⁻¹ := (one_lt_inv₀ hp0).mpr hp1
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ico_zpow hxpos hy
  set w : L := p ^ (-n) * x⁻¹ with hw
  have hwn : ‖w‖ = ‖p‖⁻¹ ^ n / ‖x‖ := by
    rw [hw, norm_mul, norm_inv, norm_zpow, _root_.inv_zpow', div_eq_mul_inv]
  have hle : ‖w‖ ≤ 1 := by
    rw [hwn]; exact (div_le_one hxpos).mpr hn1
  have hgt : ‖p‖ < ‖w‖ := by
    rw [hwn, lt_div_iff₀ hxpos]
    have : ‖x‖ < ‖p‖⁻¹ ^ n * ‖p‖⁻¹ := by rwa [zpow_add_one₀ (inv_pos.mpr hp0).ne'] at hn2
    calc ‖p‖ * ‖x‖ < ‖p‖ * (‖p‖⁻¹ ^ n * ‖p‖⁻¹) := mul_lt_mul_of_pos_left this hp0
      _ = ‖p‖⁻¹ ^ n := by field_simp
  have heq : ‖w‖ = 1 := by
    by_contra hne
    exact absurd (hmax' w (lt_of_le_of_ne hle hne)) (not_le.mpr hgt)
  refine ⟨-n, ?_⟩
  rw [hwn, div_eq_one_iff_eq hxpos.ne'] at heq
  rw [← heq, _root_.inv_zpow']

end GlobalTheory.CompanionTheory.CartGL
end

section

noncomputable section

open Matrix

namespace GlobalTheory.CompanionTheory.CartGL.IwahoriLU

variable {L : Type} [NontriviallyNormedField L] [IsUltrametricDist L] {n : ℕ}





theorem factor (n : ℕ) (r : ℝ) (h0 : 0 ≤ r) (h1 : r < 1) :
    ∀ A : Matrix (Fin n) (Fin n) L, (∀ i j, ‖(A - 1) i j‖ ≤ r) →
      ∃ U W : Matrix (Fin n) (Fin n) L, (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → W i j = 0) ∧
        (∀ i j, ‖(U - 1) i j‖ ≤ r) ∧ (∀ i j, ‖(W - 1) i j‖ ≤ r) ∧ A = U * W :=
  _root_.UpperTheory.Reformulated.B.TriangularFactorizationNearIdentity.factor n r h0 h1

theorem iwahori_factorisation (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] (n : ℕ) (r : ℝ)
    (h0 : 0 ≤ r) (h1 : r < 1) (A : Matrix (Fin n) (Fin n) L) (hA : ∀ i j, ‖(A - 1) i j‖ ≤ r) :
    ∃ U W : Matrix (Fin n) (Fin n) L, (∀ i j, j < i → U i j = 0) ∧ (∀ i j, i < j → W i j = 0) ∧
      (∀ i j, ‖(U - 1) i j‖ ≤ r) ∧ (∀ i j, ‖(W - 1) i j‖ ≤ r) ∧ A = U * W :=
  factor n r h0 h1 A hA

end GlobalTheory.CompanionTheory.CartGL.IwahoriLU
end
end
