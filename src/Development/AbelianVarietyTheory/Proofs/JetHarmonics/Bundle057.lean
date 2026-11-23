module

import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CharEqOfThetaCharEqMul
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.AffineMonoid.Basic
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle001
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle050
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle051
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CloudNodeProjectionNormLowLevel
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPrAlt
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle052
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.NumberTheory.NumberField.Norm

@[expose] public section

section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointStepCompare

open NumberField Matrix
open scoped MatrixOrder

section Evaluations

variable {Y : Type} [AddCommGroup Y] {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ Y)

def evalOn (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) : (ι × ι → ℤ) →ₗ[ℤ] ℝ where
  toFun n := ∑ p, (n p : ℝ) * B (b p.1) (b p.2)
  map_add' n n' := by simp [add_mul, Finset.sum_add_distrib]
  map_smul' k n := by simp [Finset.mul_sum, mul_assoc]

def tensorCoord : Y →ₗ[ℤ] Y →ₗ[ℤ] (ι × ι → ℤ) :=
  LinearMap.mk₂ ℤ (fun x y p => b.repr x p.1 * b.repr y p.2)
    (fun _ _ _ => by funext p; simp [add_mul]) (fun _ _ _ => by funext p; simp [mul_assoc])
    (fun _ _ _ => by funext p; simp [mul_add]) (fun _ _ _ => by funext p; simp [mul_left_comm])

theorem evalOn_tensorCoord (B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (x y : Y) :
    evalOn b B (tensorCoord b x y) = B x y := by
  conv_rhs => rw [← b.sum_repr x, ← b.sum_repr y]
  change ∑ p : ι × ι, ((b.repr x p.1 * b.repr y p.2 : ℤ) : ℝ) * B (b p.1) (b p.2) = _

  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
  Fintype.sum_prod_type, Int.cast_mul, zsmul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Evaluations

theorem posSemidef_of_int {ι : Type} [Fintype ι] {N : Matrix ι ι ℝ} (hH : N.IsHermitian)
    (hp : ∀ x : ι → ℤ, 0 ≤ (fun i => (x i : ℝ)) ⬝ᵥ N *ᵥ (fun i => (x i : ℝ))) : N.PosSemidef := by
  apply GlobalTheory.ThetaCompare.posSemidef_of_int_nonneg <;> assumption

theorem posDef_of_int {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) (hs : ∀ i j, M i j = M j i)
    (hp : ∀ x : ι → ℤ, x ≠ 0 → 0 < x ⬝ᵥ M *ᵥ x) :
    M.det ≠ 0 ∧ (M.map (Int.cast : ℤ → ℝ)).PosDef := by
  have hd : M.det ≠ 0 := fun h => by
    obtain ⟨v, hv, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    simpa [h0] using hp v hv
  have h1 : (M.map (Int.cast : ℤ → ℝ)).PosSemidef := by
    refine posSemidef_of_int (by ext i j; simp [hs i j]) fun x => ?_
    have : (fun i => (x i : ℝ)) ⬝ᵥ M.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => (x i : ℝ)) =
        ((x ⬝ᵥ M *ᵥ x : ℤ) : ℝ) := by simp [dotProduct, mulVec]
    rw [this]
    by_cases hx : x = 0
    · simp [hx]
    · exact_mod_cast (hp x hx).le
  refine ⟨hd, h1.posDef_iff_det_ne_zero.2 ?_⟩
  rw [← Int.cast_det]
  exact_mod_cast hd

theorem sum_pos_of_tensor_pos : ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (ι : Type) [Fintype ι] (a c : ι → Y), (∀ f g : Y →ₗ[ℤ] ℤ, ∑ i, f (a i) * g (c i) = ∑ i, g (a i) * f (c i)) → (∀ f : Y →ₗ[ℤ] ℤ, f ≠ 0 → 0 < ∑ i, f (a i) * f (c i)) → ∀ γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ, (∀ x y, γ x y = γ y x) → (∀ x, 0 ≤ γ x x) → γ ≠ 0 → 0 < ∑ i, γ (a i) (c i) := by
  intro Y _ _ _ ι _ a c hs hp γ hγ h0 hne
  classical
  let b := Module.finBasis ℤ Y
  let M : Matrix _ _ ℤ := Matrix.of fun p q => ∑ i, b.coord p (a i) * b.coord q (c i)
  have hM := (posDef_of_int M (fun p q => hs _ _) fun x hx => by
    have := hp (∑ p, x p • b.coord p) fun h => hx (funext fun q => by
      simpa [Finsupp.single_apply] using LinearMap.congr_fun h (b q))
    convert this using 1
    simp only [dotProduct, mulVec, M, Matrix.of_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset ι))]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm (s := (Finset.univ : Finset ι))]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
    ring).2
  let G : Matrix _ _ ℝ := Matrix.of fun p q => γ (b p) (b q)
  have hG : G.PosSemidef := posSemidef_of_int (by ext p q; simp [G, hγ (b p) (b q)]) fun x => by
    convert h0 (∑ p, x p • b p) using 1

    simp only [dotProduct, mulVec, G, Matrix.of_apply, map_sum, map_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hγ (b p) (b q)]; ring
  have htr : ∑ i, γ (a i) (c i) = (M.map (Int.cast : ℤ → ℝ) * G).trace := by
    simp only [← evalOn_tensorCoord b γ]
    change ∑ i, ∑ p : _ × _, ((b.repr (a i) p.1 * b.repr (c i) p.2 : ℤ) : ℝ) * γ (b p.1) (b p.2) = _
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, M, G, Matrix.of_apply,
      Int.cast_sum, Finset.sum_mul, Module.Basis.coord_apply]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [hγ (b p) (b q)]
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.posSemidef.nonneg
  have hCd : IsUnit C.det := by
    refine Ne.isUnit fun h => hM.det_pos.ne' ?_
    rw [hC, det_mul, h, mul_zero]
  have h1 := hG.mul_mul_conjTranspose_same C
  have h2 : (C * G * Cᴴ).trace = ∑ i, γ (a i) (c i) := by
    rw [htr, hC, trace_mul_cycle, star_eq_conjTranspose]
  rw [← h2]
  refine lt_of_le_of_ne h1.trace_nonneg fun h => hne ?_
  have h3 := h1.trace_eq_zero_iff.1 h.symm
  have hu : IsUnit C := (Matrix.isUnit_iff_isUnit_det C).2 hCd
  have h4 : G = 0 := by
    rwa [← star_eq_conjTranspose, hu.star.mul_left_eq_zero, hu.mul_right_eq_zero] at h3
  exact b.ext fun p => b.ext fun q => congrFun (congrFun h4 p) q

theorem eq_zero_of_trace_mul (E : Type) [Field E] [NumberField E] {u : 𝓞 E}
    (h : ∀ α : 𝓞 E, Algebra.trace ℤ (𝓞 E) (α * u) = 0) : u = 0 := by
  by_contra hu
  obtain ⟨r, hr, α, hα⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) u).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hu)
  have h1 := h α
  rw [mul_comm, ← hα, Algebra.trace_algebraMap, nsmul_eq_mul] at h1
  have hd : 0 < Module.finrank ℤ (𝓞 E) := Module.finrank_pos
  exact mul_ne_zero (by exact_mod_cast hd.ne') hr h1

theorem exists_traceDual : ∀ (E : Type) [Field E] [NumberField E], ∃ (N : ℕ) (ι : Type) (_ : Fintype ι) (ω θ : ι → 𝓞 E), 0 < N ∧ ∑ s, θ s * ω s = (N : 𝓞 E) ∧ ∀ g : 𝓞 E →ₗ[ℤ] ℤ, ∀ α : 𝓞 E, Algebra.trace ℤ (𝓞 E) (α * ∑ s, g (ω s) • θ s) = N * g α := by
  intro E _ _
  classical
  let ω := RingOfIntegers.basis E
  let d := (integralBasis E).traceDual
  have : Algebra.IsAlgebraic ℤ E := (IsFractionRing.comap_isAlgebraic_iff (K := ℚ)).2 inferInstance
  obtain ⟨k, hk, hint⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image d)
  let θ : _ → 𝓞 E := fun s => k • (⟨k • d s, hint _ (by simp)⟩ : 𝓞 E)
  have hN : (((k * k).toNat : ℕ) : ℤ) = k * k := Int.toNat_of_nonneg (mul_self_nonneg k)
  have hθ : ∀ s t, Algebra.trace ℤ (𝓞 E) (ω t * θ s) = if t = s then k * k else 0 := by
    intro s t
    apply Int.cast_injective (α := ℚ)
    rw [Algebra.coe_trace_int]
    have : ((ω t * θ s : 𝓞 E) : E) = k • k • (d s * integralBasis E t) := by
      change (ω t : E) * (k • k • d s) = _
      rw [integralBasis_apply, zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul, zsmul_eq_mul]
      ring
    rw [this, map_zsmul, map_zsmul, Module.Basis.trace_traceDual_mul]
    split_ifs <;> simp
  have h3 : ∀ (g : 𝓞 E →ₗ[ℤ] ℤ) (α : 𝓞 E),
      Algebra.trace ℤ (𝓞 E) (α * ∑ s, g (ω s) • θ s) = k * k * g α := by
    intro g α
    have : (Algebra.trace ℤ (𝓞 E)) ∘ₗ LinearMap.mulRight ℤ (∑ s, g (ω s) • θ s) = (k * k) • g :=
      ω.ext fun t => by

        simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, Finset.mul_sum, mul_smul_comm,
        map_sum, map_smul, hθ, LinearMap.smul_apply, smul_eq_mul]
        simp [mul_comm]
    exact LinearMap.congr_fun this α
  refine ⟨(k * k).toNat, _, inferInstance, ω, θ, ?_, ?_, fun g α => by rw [hN, h3]⟩
  · have := mul_self_pos.2 hk
    omega
  · rw [← sub_eq_zero]
    refine eq_zero_of_trace_mul E fun α => ?_
    have h4 : ∀ s, Algebra.trace ℤ (𝓞 E) (α * (θ s * ω s)) = k * k * ω.repr (α * ω s) s := by
      intro s
      have := h3 (ω.coord s) (α * ω s)
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, ite_smul,
        one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
      rw [← this, mul_comm (θ s), mul_assoc]

    rw [mul_sub, map_sub, Finset.mul_sum, map_sum, mul_comm α (_ : 𝓞 E), ← nsmul_eq_mul, map_nsmul,
    nsmul_eq_mul, hN, Algebra.trace_eq_matrix_trace ω α]
    simp only [h4, Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, Finset.mul_sum, sub_self]

end GlobalTheory.PointStepCompare
end
end

section

open GlobalTheory.ConvSer

theorem _root_.GlobalTheory.T.exists_formalGroup_heightOne_torsion_tower : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] [CharZero K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ‖PowerSeries.coeff p (nMul F p)‖ = 1 → (∀ k < p, ‖PowerSeries.coeff k (nMul F p)‖ < 1) → ∃ t : ℕ → K, (∀ n, ‖t n‖ < 1) ∧ t 0 = 0 ∧ t 1 ≠ 0 ∧ ∀ n, ev1 (nMul F p) (t (n + 1)) = t n := by
  first | exact @GlobalTheory.ConvSer.exists_torsion_tower | exact GlobalTheory.ConvSer.exists_torsion_tower | (intros; apply GlobalTheory.ConvSer.exists_torsion_tower <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_cmType_embeddings_into_valuation_ring : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (p : ℕ) [Fact p.Prime] (X : ValExt T p), ∃ (τT : (E →+* ℂ) → (𝓞 E →+* T.V)), (∀ τ a, algebraMap T.V T.Fr (τT τ a) = io (embK c τ a)) ∧ IsTypes X io (fun τ => X.ι.comp (τT τ)) ∧ Function.Injective (fun τ => X.ι.comp (τT τ)) ∧ (∀ τ τ', τ (H.rt : E) = τ' (H.rt : E) ↔ X.ι (τT τ H.rt) = X.ι (τT τ' H.rt)) ∧ ∀ τ a, τT (ComplexEmbedding.conjugate τ) a = τT τ (H.bar a) := by
  first | exact @GlobalTheory.CharDepth.exists_types_valuationRing | exact GlobalTheory.CharDepth.exists_types_valuationRing | (intros; apply GlobalTheory.CharDepth.exists_types_valuationRing <;> assumption)
end

section

open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.cloudNode_projection_norm_lowLevel : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (N : Fin n → Type) [∀ s, NormedAddCommGroup (N s)] [∀ s, InnerProductSpace ℂ (N s)] (F : ∀ s, Fin n → Fin n → Module.End ℂ (N s)) (io : ∀ s, N s →ₗ[ℂ] (Fin n → M)) (pr : ∀ s, (Fin n → M) →ₗ[ℂ] N s) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (w : M), IsMod ε E μ → (∀ s, IsMod ε (F s) (μ - Pi.single s 1)) → AlgTens ε E N F io pr → Shape ε kk μ bv → j ≤ 4 * n ^ 2 → Lev ε E μ j w → ∀ c, ∑ d, ‖(∑ s ∈ univ.filter (fun a : Fin n => a.val + 1 < kk), io s (pr s (Pi.single c w))) d‖ ^ 2 ≤ (18 / 13) ^ 2 * ‖w‖ ^ 2 ∧ ∀ s : Fin n, kk ≤ s.val + 1 → ∑ d, ‖io s (pr s (Pi.single c w)) d‖ ^ 2 ≤ (3 * (6 * bv) ^ (n - kk)) ^ 2 * ‖w‖ ^ 2 := by
  first | exact @GlobalTheory.cloud_node_projection_norm | exact GlobalTheory.cloud_node_projection_norm | (intros; apply GlobalTheory.cloud_node_projection_norm <;> assumption)
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

namespace DualFRep

theorem gram_transpose (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r)ᵀ = Formalism.QuantumDeterminants.Hpk k r := by
  have h := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).1
  ext i j
  have h1 := congrFun (congrFun h i) j
  rw [conjTranspose_apply] at h1
  rw [transpose_apply, ← h1]
  simp only [Formalism.QuantumDeterminants.Hpk]
  split_ifs <;> simp

variable {n : ℕ}

theorem left_inv {H g : Matrix (Fin n) (Fin n) ℂ} (h2 : H * H = 1) (hg : gᴴ * H * g = H) :
    H * gᴴ * H * g = 1 := by
  calc H * gᴴ * H * g = H * (gᴴ * H * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg, h2]

theorem inv_eq {H g : Matrix (Fin n) (Fin n) ℂ} (h2 : H * H = 1) (hg : gᴴ * H * g = H) :
    g⁻¹ = H * gᴴ * H :=
  Matrix.inv_eq_left_inv (left_inv h2 hg)

theorem entry_le {k r : ℕ} (g : Mx k r) (a b : Fin (2 * r + k + 1)) : ‖g a b‖ ≤ B.gN g := by
  unfold B.gN
  apply Real.le_sqrt_of_sq_le
  rw [← Complex.normSq_eq_norm_sq]
  calc Complex.normSq (g a b) ≤ ∑ j, Complex.normSq (g a j) :=
        Finset.single_le_sum (f := fun j => Complex.normSq (g a j))
          (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ b)
    _ ≤ ∑ i, ∑ j, Complex.normSq (g i j) :=
        Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (g i j))
          (fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ a)

end DualFRep


open DualFRep in
theorem isFRep_dualM (k r : ℕ) : IsFRep (k := k) (r := r) dualM (Formalism.QuantumDeterminants.Hpk k r) 1 := by
  have h1 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).1
  have h2 := (Formalism.QuantumDeterminants.hermitian_pos_facts_hold k r).2.1
  have h3 := gram_transpose k r
  have hmem : ∀ g ∈ GG k r, gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := fun g hg => hg
  generalize Formalism.QuantumDeterminants.Hpk k r = H at h1 h2 h3 hmem ⊢
  refine ⟨h1, h2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [dualM]
  · intro g hg h hh
    simp only [dualM]
    rw [Matrix.mul_inv_rev, Matrix.transpose_mul]
  · intro g hg
    have key : g⁻¹ * H * (g⁻¹)ᴴ = H := by
      rw [inv_eq h2 (hmem g hg)]
      simp only [conjTranspose_mul, conjTranspose_conjTranspose, h1]
      calc H * gᴴ * H * H * (H * (g * H)) = H * (gᴴ * (H * H) * H * g) * H := by
            simp only [Matrix.mul_assoc]
        _ = H := by rw [h2, Matrix.mul_one, hmem g hg, h2, Matrix.one_mul]
    have e : ((g⁻¹)ᵀ)ᴴ = ((g⁻¹)ᴴ)ᵀ := rfl
    have := congrArg Matrix.transpose key
    rw [transpose_mul, transpose_mul, h3] at this
    simp only [dualM]
    rw [e, Matrix.mul_assoc, this]
  · intro i j
    have hc : Continuous (fun g : Mx k r => (H * gᴴ * H) j i) := by
      have : Continuous (fun g : Mx k r => H * gᴴ * H) :=
        (continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const
      exact this.matrix_elem j i
    refine hc.continuousOn.congr ?_
    intro g hg
    simp only [dualM, transpose_apply]
    rw [inv_eq h2 (hmem g hg)]
  · refine ⟨∑ p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1), ∑ b, ∑ a, ‖H p.2 a‖ * ‖H b p.1‖, ?_⟩
    intro g hg i j
    simp only [dualM, transpose_apply, pow_one]
    rw [inv_eq h2 (hmem g hg)]
    have hN : 0 ≤ B.gN g := Real.sqrt_nonneg _
    calc ‖(H * gᴴ * H) j i‖ = ‖∑ b, ∑ a, H j a * star (g b a) * H b i‖ := by
          simp only [Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul]
      _ ≤ ∑ b, ∑ a, ‖H j a * star (g b a) * H b i‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => norm_sum_le _ _)
      _ ≤ ∑ b, ∑ a, ‖H j a‖ * ‖H b i‖ * B.gN g := by
          refine Finset.sum_le_sum fun b _ => Finset.sum_le_sum fun a _ => ?_
          rw [norm_mul, norm_mul, norm_star, mul_right_comm]
          exact mul_le_mul_of_nonneg_left (entry_le g b a) (by positivity)
      _ = (∑ b, ∑ a, ‖H j a‖ * ‖H b i‖) * B.gN g := by simp only [Finset.sum_mul]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hN
          exact Finset.single_le_sum
            (f := fun p : Fin (2 * r + k + 1) × Fin (2 * r + k + 1) => ∑ b, ∑ a, ‖H p.2 a‖ * ‖H b p.1‖)
            (fun p _ => by positivity) (Finset.mem_univ (i, j))
  · intro g hg hu
    have hl : star g * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hu
    have hinv : g⁻¹ = star g := Matrix.inv_eq_left_inv hl
    rw [Matrix.mem_unitaryGroup_iff]
    simp only [dualM]
    rw [hinv]
    have e : star ((star g)ᵀ) = gᵀ := by
      ext a b
      simp [Matrix.star_apply]
    rw [e, ← transpose_mul, (Matrix.mem_unitaryGroup_iff).1 hu, transpose_one]

end GlobalTheory
end

section

open Matrix Finset PI.UpqRep
open scoped InnerProductSpace ContDiff

noncomputable section

namespace GlobalTheory.TensCompare

open GlobalTheory.IndefiniteRowSideFullHecke.SmoothDecompositionForms (HRep IsSmoothMap IsSmoothMapInto IsSmoothMapFrom IsSmoothDecomp IsSignedDecomp IsFormRep
  tensSmooth tensAct tensForm pureT contr LieWord Mx Ix)

variable {k r : ℕ}

theorem isURepOn_of_isDS {R : BranchingSupport.Rep k r} {ε : Ix k r → Bool} {μ : Ix k r → ℝ} (h : R.IsDS ε μ) :
    IsURepOn (BranchingSupport.GG k r) R.σ := by
  obtain ⟨-, P, hP, -, -, ⟨⟨h1, hm⟩, hn, hc⟩, -⟩ := h
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hPP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hdet
  have hmaps := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.cayley_maps hP
  have e : ∀ g : Mx k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPP, Matrix.one_mul, Matrix.mul_assoc, hPP, Matrix.mul_one]
  refine ⟨⟨by simpa [hPP] using h1, fun a ha b hb => ?_⟩, fun g hg v => ?_, fun v => ?_⟩
  · have := hm _ (hmaps ha) _ (hmaps hb)
    have e2 : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc P⁻¹ P, hPP, Matrix.one_mul]
    simpa only [e2, e] using this
  · simpa only [e] using hn _ (hmaps hg) v
  · have h3 : Continuous fun g : Mx k r => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := (hc v).comp h3.continuousOn hmaps
    simpa only [Function.comp_def, e] using this

section Smooth

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

end Smooth

section Tensor

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable {ρ : Mx k r → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ} {R : HRep k r} {Rs : κ → HRep k r}
  {io : ∀ I, (Rs I).H → ι → R.H} {pr : ∀ I, ι → R.H → (Rs I).H} {p : ∀ I, (ι → R.H) → (Rs I).H} {ep : κ → ℝ}


end Tensor

end GlobalTheory.TensCompare

end
end

section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TopMinorWedge

theorem det_mul_sub {n l : ℕ} (A : Matrix (Fin l) (Fin n) ℂ) (B : Matrix (Fin n) (Fin l) ℂ) :
    (A * B).det = ∑ I : BranchingSupport.Sub n l, (A.submatrix id (I.1.orderEmbOfFin I.2)).det *
      (B.submatrix (I.1.orderEmbOfFin I.2) id).det := by
  rw [GlobalTheory.det_mul_eq_sum_minors]
  exact Fintype.sum_equiv
    (⟨fun S => ⟨S.1, S.2⟩, fun S => ⟨S.1, S.2⟩, fun _ => rfl, fun _ => rfl⟩ :
      Set.powersetCard (Fin n) l ≃ BranchingSupport.Sub n l) _ _ (fun _ => rfl)

theorem cmp_mulVec_wedge {n l : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin l → Fin n → ℂ) :
    BranchingSupport.cmp l g *ᵥ BranchingSupport.wedge f = BranchingSupport.wedge (fun b => g *ᵥ f b) := by
  funext I
  have h := det_mul_sub (g.submatrix (I.1.orderEmbOfFin I.2) id) (Matrix.of fun c b => f b c)
  have h2 : BranchingSupport.wedge (fun b => g *ᵥ f b) I =
      (g.submatrix (I.1.orderEmbOfFin I.2) id * (Matrix.of fun c b => f b c)).det := rfl
  rw [h2, h]
  rfl

theorem star_wedge_dot {n l : ℕ} (f f' : Fin l → Fin n → ℂ) :
    star (BranchingSupport.wedge f) ⬝ᵥ BranchingSupport.wedge f' = (Matrix.of fun a b => star (f a) ⬝ᵥ f' b).det := by
  have h := det_mul_sub (Matrix.of fun a c => star (f a c)) (Matrix.of fun c b => f' b c)
  have h2 : (Matrix.of fun a b => star (f a) ⬝ᵥ f' b) =
      (Matrix.of fun a c => star (f a c)) * (Matrix.of fun c b => f' b c) := rfl
  rw [h2, h]
  refine Finset.sum_congr rfl fun I _ => ?_
  congr 1
  rw [Pi.star_apply, BranchingSupport.wedge, ← Matrix.det_conjTranspose]
  rfl

theorem herm_cmp_wedge_eq_det : ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r),
    Formalism.QuantumDeterminants.herm (cmp (r + 1) (Formalism.QuantumDeterminants.Hpk k r)) (cmp (r + 1) g *ᵥ wedge (Formalism.QuantumDeterminants.fvec k r z'))
      (wedge (Formalism.QuantumDeterminants.fvec k r z)) = (Formalism.QuantumDeterminants.Zhat k r z z' g).det := by
  intro k r z z' g
  rw [Formalism.QuantumDeterminants.herm, cmp_mulVec_wedge, cmp_mulVec_wedge, star_wedge_dot]
  rfl

end GlobalTheory.TopMinorWedge
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.FieldBaseChange (constVal isoVal)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.fn_eigen_equation_of_forall_geometric_point_alt : ∀ (V O F : Type) [CommRing V] [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F], Function.Injective (algebraMap O F) → ∀ (β : V →+* O) (G : Over (Spec (CommRingCat.of V))) [GrpObj G], Flat G.hom → ∀ (Z : Over (Spec (CommRingCat.of O))), IsFinite Z.hom → Flat Z.hom → IsReduced (Pdiv.specO O F ⊗ Z).left → ∀ (jZ : Z.left ⟶ G.left), jZ ≫ G.hom = Z.hom ≫ Spec.map (CommRingCat.ofHom β) → ∀ (U : G.left.Opens) (l : ℕ) (c : Fin l → O) (s : Fin l → Γ(G.left, U)) (k : Γ(Z.left, ⊤)), (∀ (T : Over (Spec (CommRingCat.of V))) (e : T.left ⟶ Spec (CommRingCat.of F)) (c₀ : Pdiv.specO O F ⟶ Z) (r g : T ⟶ G), g.left = (e ≫ c₀.left) ≫ jZ → ∀ z : T.left, r.left z ∈ U → (r * g).left z ∈ U → ∑ i, constVal e z (algebraMap O F (c i)) * gs (r * g).left z U (s i) = gs (e ≫ c₀.left) z ⊤ k * ∑ i, constVal e z (algebraMap O F (c i)) * gs r.left z U (s i)) → ∀ (T : Over (Spec (CommRingCat.of V))) (q : T.left ⟶ Z.left) (r g : T ⟶ G), g.left = q ≫ jZ → ∀ z : T.left, r.left z ∈ U → (r * g).left z ∈ U → ∑ i, constVal (q ≫ Z.hom) z (c i) * gs (r * g).left z U (s i) = gs q z ⊤ k * ∑ i, constVal (q ≫ Z.hom) z (c i) * gs r.left z U (s i) := by
  first | exact @GlobalTheory.fn_eigen_equation_of_forall_geometric_point | exact GlobalTheory.fn_eigen_equation_of_forall_geometric_point | (intros; apply GlobalTheory.fn_eigen_equation_of_forall_geometric_point <;> assumption)
end
