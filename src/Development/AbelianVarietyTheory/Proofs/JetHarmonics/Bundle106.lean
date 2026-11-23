module

public import Formalism.HermitianCurvature.FrameExists2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
public import Formalism.HermitianCurvature.StatementB
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle024
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle002
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
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
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed

@[expose] public section

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)

open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

namespace GlobalTheory.TensorStd

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable def coefL {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun g => herm H (g *ᵥ v) w
      map_add' := fun g h => by simp [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
      map_smul' := fun c g => by simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul] }

theorem coefL_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (v w : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    coefL H v w g = herm H (g *ᵥ v) w := rfl

theorem coef_hasDerivAt {k r : ℕ} (X : Mx k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    HasDerivAt (fun t : ℝ => herm (Hpk k r) (NormedSpace.exp ((t : ℂ) • X) *ᵥ v) w)
      (herm (Hpk k r) (X *ᵥ v) w) 0 := by
  have h1 := B5.curve_hasDerivAt (1 : Mx k r) X 0
  simp only [Matrix.one_mul, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero] at h1
  exact ((coefL (Hpk k r) v w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1

theorem hpart_sum {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) :
    hpart1 H Z + Complex.I • hpart2 H Z = Z := by
  unfold hpart1 hpart2
  rw [smul_smul]
  have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  rw [this, ← smul_add]
  have : Z - H⁻¹ * Zᴴ * H + (Z + H⁻¹ * Zᴴ * H) = (2 : ℂ) • Z := by rw [two_smul]; abel
  rw [this, smul_smul]; norm_num

theorem dOp_tensor {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (V →L[ℂ] V)} {B : Fin k → (Fin (2 * r + k + 1) → ℂ)}
    {πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V)))}
    (hπ : IsRepW k r z π) (hπt : IsRepW k r z πt) (hB : IsFrameOf k r [z] B)
    (hf : ∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (y d))
    {X : Mx k r} (hX : InLieW k r z X) (y : PiLp 2 (fun _ : Fin k => V)) (c : Fin k) :
    dOp πt X y c = dOp π X (y c) + ∑ d, herm (Hpk k r) (X *ᵥ B d) (B c) • y d := by
  have h1 := dOp_hasDeriv hπt.1 hπt.2 hX
  have h2 := dOp_hasDeriv hπ.1 hπ.2 hX
  have h3 : HasDerivAt (fun t : ℝ => πt (NormedSpace.exp ((t : ℂ) • X)) y c) (dOp πt X y c) 0 :=
    (((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin k => V) c).comp
      (ContinuousLinearMap.apply ℂ _ y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  have h4 : ∀ d, HasDerivAt (fun t : ℝ => π (NormedSpace.exp ((t : ℂ) • X)) (y d)) (dOp π X (y d)) 0 := fun d =>
    ((ContinuousLinearMap.apply ℂ V (y d)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h5 := HasDerivAt.fun_sum (u := Finset.univ) fun d _ => (coef_hasDerivAt X (B d) (B c)).fun_smul (h4 d)
  have h6 : (fun t : ℝ => πt (NormedSpace.exp ((t : ℂ) • X)) y c) = fun t : ℝ => ∑ d,
      herm (Hpk k r) (NormedSpace.exp ((t : ℂ) • X) *ᵥ B d) (B c) • π (NormedSpace.exp ((t : ℂ) • X)) (y d) :=
    funext fun t => hf _ (exp_uw hX t) y c
  rw [h6] at h3
  rw [h3.unique h5]
  simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec, hπ.1.1, hB.2.1,
    Finset.sum_add_distrib, one_apply_eq_self]
  simp

theorem EB_tensor_std : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mx k r → (V →L[ℂ] V)) (B : Fin k → (Fin (2 * r + k + 1) → ℂ)) (πt : Mx k r → ((PiLp 2 (fun _ : Fin k => V)) →L[ℂ] (PiLp 2 (fun _ : Fin k => V)))), inWb k r z → 0 < Tz k r z → IsRepW k r z π → IsRepW k r z πt → IsFrameOf k r [z] B → (∀ h ∈ UWset k r z, ∀ y c, πt h y c = ∑ d, herm (Hpk k r) (h *ᵥ B d) (B c) • π h (y d)) → ∀ a b y c, EB πt B a b y c = EB π B a b (y c) + if c = a then y b else 0 := by
  intro V _ _ _ k r z π B πt _ _ hπ hπt hB hf a b y c
  obtain ⟨l1, l2⟩ := frame_lie hB a b
  have e1 := dOp_tensor hπ hπt hB hf l1 y c
  have e2 := dOp_tensor hπ hπt hB hf l2 y c
  have e3 : ∀ d, herm (Hpk k r) (hpart1 (Hpk k r) (unitB (Hpk k r) B a b) *ᵥ B d) (B c) +
      Complex.I * herm (Hpk k r) (hpart2 (Hpk k r) (unitB (Hpk k r) B a b) *ᵥ B d) (B c) =
      if d = b then (if c = a then 1 else 0) else 0 := by
    intro d
    rw [← coefL_apply, ← coefL_apply, ← smul_eq_mul Complex.I, ← map_smul, ← map_add (f := _), hpart_sum, coefL_apply,
      Qx8.unitB_mulVec, hB.2.1]
    have := hB.2.1 a c
    by_cases hd : d = b
    · subst hd
      have e : herm (Hpk k r) ((1 : ℂ) • B a) (B c) = herm (Hpk k r) (B a) (B c) := by rw [one_smul]
      rw [if_pos rfl, if_pos rfl, e, this]
      simp only [eq_comm]
    · simp [hd, herm]
  show dOp πt _ y c + Complex.I • dOp πt _ y c = (dOp π _ (y c) + Complex.I • dOp π _ (y c)) + _
  rw [e1, e2, smul_add, Finset.smul_sum, add_add_add_comm, ← Finset.sum_add_distrib]
  congr 1
  simp only [smul_smul, ← add_smul, e3]
  by_cases hc : c = a <;> simp [hc]

end GlobalTheory.TensorStd
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
open Formalism.REAL (qdet GlRel IsHW)
open Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.QrD

namespace GlobalTheory

theorem intertwiner_dOp_of_stabiliser {V₁ : Type} [NormedAddCommGroup V₁] [NormedSpace ℂ V₁]
    [FiniteDimensional ℂ V₁] {V₂ : Type} [NormedAddCommGroup V₂] [NormedSpace ℂ V₂]
    [FiniteDimensional ℂ V₂] {k r : ℕ} {z e : Fin (2 * r + k + 1) → ℂ}
    {π₁ : Mx k r → (V₁ →L[ℂ] V₁)} {π₂ : Mx k r → (V₂ →L[ℂ] V₂)} (T : V₁ →L[ℂ] V₂)
    (h₁ : IsRepW k r z π₁) (h₂ : IsRepW k r z π₂)
    (hT : ∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v, T (π₁ h v) = π₂ h (T v))
    {X : Mx k r} (hX : InLieW k r z X) (he : X *ᵥ e = 0) (v : V₁) :
    T (dOp π₁ X v) = dOp π₂ X (T v) := by
  have d₁ := dOp_hasDeriv h₁.1 h₁.2 hX
  have d₂ := dOp_hasDeriv h₂.1 h₂.2 hX
  have e₁ := ((T.comp (ContinuousLinearMap.apply ℂ V₁ v)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) d₁
  have e₂ := ((ContinuousLinearMap.apply ℂ V₂ (T v)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (0 : ℝ) d₂
  have hf : (((T.comp (ContinuousLinearMap.apply ℂ V₁ v)).restrictScalars ℝ) ∘
      fun t : ℝ => π₁ (NormedSpace.exp ((t : ℂ) • X))) =
      (((ContinuousLinearMap.apply ℂ V₂ (T v)).restrictScalars ℝ) ∘
      fun t : ℝ => π₂ (NormedSpace.exp ((t : ℂ) • X))) := by
    funext t
    exact hT _ (exp_uw hX t) (Qx8.exp_fix he t) v
  rw [hf] at e₁
  exact e₁.unique e₂

theorem intertwiner_EB_of_stabiliser : ∀ (V₁ : Type) [NormedAddCommGroup V₁] [NormedSpace ℂ V₁] [FiniteDimensional ℂ V₁] (V₂ : Type) [NormedAddCommGroup V₂] [NormedSpace ℂ V₂] [FiniteDimensional ℂ V₂] (k r m : ℕ) (z e : (Fin (2 * r + k + 1) → ℂ)) (π₁ : Mx k r → (V₁ →L[ℂ] V₁)) (π₂ : Mx k r → (V₂ →L[ℂ] V₂)) (T : V₁ →L[ℂ] V₂) (B : Fin m → (Fin (2 * r + k + 1) → ℂ)), IsRepW k r z π₁ → IsRepW k r z π₂ → IsFrameOf k r [z, e] B → (∀ h ∈ UWset k r z, h *ᵥ e = e → ∀ v, T (π₁ h v) = π₂ h (T v)) → ∀ a b v, T (EB π₁ B a b v) = EB π₂ B a b (T v) := by
  intro V₁ _ _ _ V₂ _ _ _ k r m z e π₁ π₂ T B h₁ h₂ hB hT a b v
  have hz : IsFrameOf k r [z] B := ⟨hB.1, hB.2.1, fun c y hy => hB.2.2 c y (by simp at hy; simp [hy])⟩
  have he : IsFrameOf k r [e] B := ⟨hB.1, hB.2.1, fun c y hy => hB.2.2 c y (by simp at hy; simp [hy])⟩
  have lz := frame_lie hz a b
  have le := frame_lie he a b
  have p1 := intertwiner_dOp_of_stabiliser T h₁ h₂ hT lz.1 le.1.2 v
  have p2 := intertwiner_dOp_of_stabiliser T h₁ h₂ hT lz.2 le.2.2 v
  show T (ecOp π₁ (unitB (Hpk k r) B a b) v) = ecOp π₂ (unitB (Hpk k r) B a b) (T v)
  unfold ecOp
  simp only [_root_.add_apply, _root_.smul_apply, map_add (f := _), map_smul, p1, p2]

end GlobalTheory
end

section

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh.OmgNorm

open Formalism.FourierDecayAlt.P.Dx2.DF

section form

variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

theorem form_add_left (u v w : Fin m → ℂ) : herm H (u + v) w = herm H u w + herm H v w := by
  simp only [herm, mulVec_add, dotProduct_add]

theorem form_add_right (u v w : Fin m → ℂ) : herm H w (u + v) = herm H w u + herm H w v := by
  simp only [herm, star_add, add_dotProduct]

theorem form_sub_left (u v w : Fin m → ℂ) : herm H (u - v) w = herm H u w - herm H v w := by
  simp only [herm, mulVec_sub, dotProduct_sub]

theorem form_sub_right (u v w : Fin m → ℂ) : herm H w (u - v) = herm H w u - herm H w v := by
  simp only [herm, star_sub, sub_dotProduct]

theorem form_smul_left (c : ℂ) (u w : Fin m → ℂ) : herm H (c • u) w = c * herm H u w := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem form_smul_right (c : ℂ) (u w : Fin m → ℂ) : herm H w (c • u) = star c * herm H w u := by
  simp only [herm, star_smul, smul_dotProduct, smul_eq_mul]

end form

variable {k r : ℕ}

theorem inWb_Wb (v : Fin (2 * r + k + 1) → ℂ) : inWb k r (Wb v) := by
  intro i hi
  show (if r ≤ i.val ∧ i.val ≤ r + k then v i else 0) = 0
  rw [if_neg (by omega)]

theorem split_of_free {v : Fin (2 * r + k + 1) → ℂ} (hv : ∀ a : Fin r, v (esI k r a) = 0) :
    v = (∑ a : Fin r, v (eI k r a) • ee k r a) + Wb v := by
  funext i
  have hval : ∀ a : Fin r, (eI k r a).val = a.val := fun a => rfl
  have hsum : (∑ a : Fin r, v (eI k r a) • ee k r a) i = if i.val < r then v i else 0 := by
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, ee, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    split_ifs with h
    · have hi : i = eI k r ⟨i.val, h⟩ := Fin.ext (hval ⟨i.val, h⟩).symm
      rw [Finset.sum_eq_single ⟨i.val, h⟩]
      · rw [if_pos hi, ← hi]
      · intro b _ hb
        rw [if_neg]
        intro hib
        apply hb
        apply Fin.ext
        show b.val = i.val
        rw [hib, hval]
      · intro h'
        exact absurd (Finset.mem_univ _) h'
    · apply Finset.sum_eq_zero
      intro b _
      rw [if_neg]
      intro hib
      apply h
      rw [hib, hval]
      exact b.isLt
  rw [Pi.add_apply, hsum]
  show v i = (if i.val < r then v i else 0) + (if r ≤ i.val ∧ i.val ≤ r + k then v i else 0)
  have hlt := i.isLt
  by_cases h1 : i.val < r
  · rw [if_pos h1, if_neg (by omega), add_zero]
  · rw [if_neg h1, zero_add]
    by_cases h2 : i.val ≤ r + k
    · rw [if_pos ⟨by omega, h2⟩]
    · rw [if_neg (by omega)]
      have hi : i = esI k r ⟨2 * r + k - i.val, by omega⟩ :=
        Fin.ext (by show i.val = 2 * r + k - (2 * r + k - i.val); omega)
      rw [hi]
      exact hv _

theorem form_Wb_right {v w : Fin (2 * r + k + 1) → ℂ} (hv : ∀ a : Fin r, v (esI k r a) = 0) (hw : inWb k r w) :
    herm (Hpk k r) (Wb v) w = herm (Hpk k r) v w := by
  conv_rhs => rw [split_of_free hv]
  rw [form_add_left, herm_sum_left]
  simp only [form_smul_left, h_ee_w hw, mul_zero, Finset.sum_const_zero, zero_add]

theorem form_Wb_self {v : Fin (2 * r + k + 1) → ℂ} (hv : ∀ a : Fin r, v (esI k r a) = 0) :
    herm (Hpk k r) (Wb v) (Wb v) = herm (Hpk k r) v v := by
  rw [form_Wb_right hv (inWb_Wb v)]
  have hs := split_of_free hv
  calc herm (Hpk k r) v (Wb v)
      = herm (Hpk k r) v ((∑ a : Fin r, v (eI k r a) • ee k r a) + Wb v) := by
        rw [form_add_right, herm_sum_right]
        simp [form_smul_right, herm_ee, hv]
    _ = herm (Hpk k r) v v := by rw [← hs]

theorem mul_adj {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g * (Hpk k r * gᴴ * Hpk k r) = 1 := by
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg
  have hl : (Hpk k r * gᴴ * Hpk k r) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, Formalism.QuantumDeterminants.GBasic.Hpk_sq]
  exact mul_eq_one_comm.mp hl

theorem adj_last (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) :
    (Zhat k r z z' g).adjugate (Fin.last r) (Fin.last r) = Dmin k r z z' g ⟨r, by omega⟩ := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  have hs : ((-1 : ℂ)) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]
    simp
  rw [hs, one_mul]
  rfl

theorem det_last (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) :
    (Zhat k r z z' g).det = Dmin k r z z' g (Fin.last (r + 1)) := by
  show _ = Matrix.det ((Zhat k r z z' g).submatrix (Fin.castLE le_rfl) (Fin.castLE le_rfl))
  rw [Fin.castLE_rfl, Matrix.submatrix_id_id]

private theorem herm_adjoint_mulVec_eq (g : Mx k r) (x y : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) ((Hpk k r * gᴴ * Hpk k r) *ᵥ x) y = herm (Hpk k r) x (g *ᵥ y) := by
  unfold herm
  rw [mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.one_mul,
    star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

theorem omg_norm : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g : Mx k r), inWb k r z → 0 < Tz k r z →
    inWb k r z' → 0 < Tz k r z' → g ∈ UH (Hpk k r) →
    inWb k r (GlobalTheory.WigSh.omg k r z z' g) ∧ herm (Hpk k r) (GlobalTheory.WigSh.omg k r z z' g) z' = 0 ∧
      (herm (Hpk k r) (GlobalTheory.WigSh.omg k r z z' g) (GlobalTheory.WigSh.omg k r z z' g)).re = Gf k r z z' g / Tz k r z' := by
  intro k r z z' g hz _ hz' hT' hg
  have hTne : (Tz k r z' : ℂ) ≠ 0 := by exact_mod_cast hT'.ne'
  have hss : herm (Hpk k r) z' z' = -((Tz k r z' : ℝ) : ℂ) := herm_self_alt
  have hsz : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := herm_self_alt
  have hs0 : herm (Hpk k r) z' z' ≠ 0 := by rw [hss]; exact neg_ne_zero.mpr hTne
  obtain ⟨u, hu⟩ : ∃ u : Fin (2 * r + k + 1) → ℂ,
      u = ∑ a, star ((Zhat k r z z' g).adjugate (Fin.last r) a) • fvec k r z a := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : Fin (2 * r + k + 1) → ℂ, v = (Hpk k r * gᴴ * Hpk k r) *ᵥ u := ⟨_, rfl⟩
  have homg : GlobalTheory.WigSh.omg k r z z' g = Formalism.FourierDecayAlt.D.prW k r z' v := by
    rw [hv, hu]; rfl
  have hkey : ∀ b : Fin (r + 1), herm (Hpk k r) v (fvec k r z' b) =
      star ((Zhat k r z z' g).det * (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (Fin.last r) b) := by
    intro b
    have hsym : ∀ a, herm (Hpk k r) (fvec k r z a) (g *ᵥ fvec k r z' b) = star (Zhat k r z z' g a b) := by
      intro a
      rw [herm_symm']
      rfl
    rw [hv, herm_adjoint_mulVec_eq, hu, herm_sum_left]
    simp only [form_smul_left, hsym, ← star_mul', ← star_sum]
    rw [← Matrix.mul_apply, Matrix.adjugate_mul, Matrix.smul_apply, smul_eq_mul]
  have hfree : ∀ a : Fin r, v (esI k r a) = 0 := by
    intro a
    rw [← herm_ee v a, ← fvec_cs z' a, hkey, Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne', mul_zero,
      star_zero]
  have hlast : ∀ w : Fin (2 * r + k + 1) → ℂ, fvec k r w (Fin.last r) = w := by
    intro w
    simp [fvec]
  have hvz' : herm (Hpk k r) v z' = star (Zhat k r z z' g).det := by
    have h := hkey (Fin.last r)
    rw [hlast, Matrix.one_apply_eq, mul_one] at h
    exact h
  have hWv : herm (Hpk k r) (Wb v) z' = star (Zhat k r z z' g).det := by
    rw [form_Wb_right hfree hz', hvz']
  have hWW : herm (Hpk k r) (Wb v) (Wb v) =
      star ((Zhat k r z z' g).adjugate (Fin.last r) (Fin.last r)) *
        ((Zhat k r z z' g).adjugate (Fin.last r) (Fin.last r)) * herm (Hpk k r) z z := by
    rw [form_Wb_self hfree, hv, herm_adjoint_mulVec_eq, mulVec_mulVec, mul_adj hg, one_mulVec, hu,
      Fin.sum_univ_castSucc]
    simp only [fvec_cs, hlast]
    simp [herm_sum_left, herm_sum_right, form_add_left, form_add_right, form_smul_left, form_smul_right,
      h_ee_w hz, h_w_ee hz]
    ring
  rw [homg, prW_eq]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    simp only [Pi.sub_apply, Pi.smul_apply, inWb_Wb v i hi, hz' i hi, smul_zero, sub_zero]
  · rw [form_sub_left, form_smul_left, div_mul_cancel₀ _ hs0, sub_self]
  · rw [form_sub_left, form_sub_right, form_sub_right, form_smul_left, form_smul_left, form_smul_right,
      form_smul_right, herm_symm' (Wb v) z', hWv, hWW, hss, hsz]
    unfold Gf
    rw [← det_last, ← adj_last]
    set d := (Zhat k r z z' g).det
    set A := (Zhat k r z z' g).adjugate (Fin.last r) (Fin.last r)
    have hT'0 : Tz k r z' ≠ 0 := hT'.ne'
    rw [Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.star_def, map_div₀, map_neg, Complex.conj_ofReal, Complex.conj_conj]
    simp only [Complex.sub_re, Complex.mul_re, Complex.div_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.conj_re, Complex.conj_im, Complex.mul_im, Complex.div_im, Complex.neg_im,
      Complex.normSq_neg, Complex.normSq_ofReal]
    field_simp
    ring

end GlobalTheory.WigSh.OmgNorm
end
end

section

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory


set_option synthInstance.maxSize 2000 in
theorem besselJ_family_aestronglyMeasurable : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (α : Type) [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [SecondCountableTopology α] (μ : Measure α) [SFinite μ] (U : Set α) (γ : α → B.Mat k r) (V : Set (B.Mat k r)) (H : B.Mat k r → (Wq →L[ℂ] Wp)), IsOpen U → ContinuousOn γ U → (∀ x ∈ U, ∀ q, Bs.inSS q → B.sgs q (γ x) ∈ V) → ContinuousOn H V → AEStronglyMeasurable (fun x => B.JF Bs H (γ x)) (μ.restrict U) := by
  intro k r Wp Wq _ _ _ _ _ _ Bs α _ _ _ _ μ _ U γ V H hU hγ hV hH
  set S : Set (B.SS k r) := {p | Bs.inSS p} with hS
  have hWc := (P.weyl_subgroup_closed k r Bs.z).closed
  have hWc' := (P.weyl_subgroup_closed k r Bs.z').closed
  have hNc := (P.unipotent_radical_closed k r).closed
  have hSc : IsClosed S := by
    have e : S = (fun p : B.SS k r => (p.1.1 : B.Mat k r)) ⁻¹' (UWset k r Bs.z) ∩
        ((fun p : B.SS k r => (p.1.2 : B.Mat k r)) ⁻¹' (Nset k r) ∩
          ((fun p : B.SS k r => (p.2.1 : B.Mat k r)) ⁻¹' (UWset k r Bs.z') ∩
            (fun p : B.SS k r => (p.2.2 : B.Mat k r)) ⁻¹' (Nset k r))) := by
      ext p; rfl
    rw [e]
    exact (hWc.preimage continuous_fst.fst).inter ((hNc.preimage continuous_fst.snd).inter
      ((hWc'.preimage continuous_snd.fst).inter (hNc.preimage continuous_snd.snd)))
  have hxi : Continuous fun p : B.SS k r => B.xiTau Bs (1, 1) p :=
    (P.B7.continuous_xi Bs).comp (by fun_prop : Continuous fun p : B.SS k r => (((1 : ℝ), (1 : ℝ)), p))
  have hπ : ContinuousOn (fun p : B.SS k r => Bs.π (Matrix.of p.1.1)) S :=
    Bs.π_cont.comp (continuous_fst.fst).continuousOn (fun p hp => hp.1)
  have hinv1 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.1.1 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_fst.fst).continuousOn (fun p hp => hp.1.1)
  have hinv2 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.1.2 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_fst.snd).continuousOn (fun p hp => hp.2.1.1)
  have hinv3 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)⁻¹) S :=
    (P.B6.inv_continuousOn k r).comp (continuous_snd.fst).continuousOn (fun p hp => hp.2.2.1.1)
  have hπ' : ContinuousOn (fun p : B.SS k r => Bs.π' (Matrix.of p.2.1 : B.Mat k r)⁻¹) S :=
    Bs.π'_cont.comp hinv3 (fun p hp => Formalism.QuantumDeterminants.WeylGroupFacts.uw_inv hp.2.2.1)
  have hc4 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.2 : B.Mat k r)) S :=
    (continuous_snd.snd).continuousOn
  have hc5 : ContinuousOn (fun p : B.SS k r => (Matrix.of p.2.1 : B.Mat k r)) S :=
    (continuous_snd.fst).continuousOn
  have up : ∀ {β : Type} [TopologicalSpace β] {f : B.SS k r → β}, ContinuousOn f S →
      ContinuousOn (fun y : α × B.SS k r => f y.2) (U ×ˢ S) :=
    fun hf => hf.comp continuous_snd.continuousOn (fun y hy => hy.2)
  have hγ' : ContinuousOn (fun y : α × B.SS k r => γ y.1) (U ×ˢ S) :=
    hγ.comp continuous_fst.continuousOn (fun y hy => hy.1)
  have hsgs : ContinuousOn (fun y : α × B.SS k r => B.sgs y.2 (γ y.1)) (U ×ˢ S) :=
    (((((up hinv1).mul (up hinv2)).mul hγ').mul (up hc4)).mul (up hc5))
  have hFs : ContinuousOn (fun y : α × B.SS k r => H (B.sgs y.2 (γ y.1))) (U ×ˢ S) :=
    hH.comp hsgs (fun y hy => hV y.1 hy.1 y.2 hy.2)
  have hcont : ContinuousOn (fun y : α × B.SS k r => D.orbIntegrand Bs (γ y.1) H y.2) (U ×ˢ S) := by
    unfold D.orbIntegrand B.rho
    exact (up hxi.continuousOn).smul ((up hπ).clm_comp (hFs.clm_comp (up hπ')))
  have hW : SigmaFinite Bs.μW := P.Dx2.MN.sigma_of_haar Bs.haarW
  have hW' : SigmaFinite Bs.μW' := P.Dx2.MN.sigma_of_haar Bs.haarW'
  have hN : SigmaFinite Bs.μN := P.Dx2.MN.sigma_of_haar Bs.haarN
  have hsf : SFinite Bs.μSS := by unfold B.RealPlaceData.μSS; infer_instance
  have h1 := hcont.aestronglyMeasurable (μ := μ.prod Bs.μSS) (hU.measurableSet.prod hSc.measurableSet)
  have hae : ∀ᵐ p ∂Bs.μSS, p ∈ S := P.Dx2.OrbJ.ae_inSS Bs
  rw [← Measure.prod_restrict, Measure.restrict_eq_self_of_ae_mem hae] at h1
  have h2 := h1.integral_prod_right'
  have e : (fun x => B.JF Bs H (γ x)) = fun x => ∫ p, D.orbIntegrand Bs (γ x) H p ∂Bs.μSS := by
    funext x
    rw [← P.bessel_function_trivial_index k r Wp Wq Bs H (γ x)]
    rfl
  rw [e]
  exact h2

end GlobalTheory
end
