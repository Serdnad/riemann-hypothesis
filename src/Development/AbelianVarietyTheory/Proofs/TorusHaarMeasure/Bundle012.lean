module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle010
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.IsStrictDom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle002

@[expose] public section

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.UnitaryLift

open GlobalTheory.UnitaryFrames

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma conj_unitary {r : ℕ} (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0)
    (c : X.Ψ → GL (Fin r) ℂ)
    (hc : ∀ τ, (c τ : Matrix (Fin r) (Fin r) ℂ)ᵀ *
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) *
      (c τ : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1)) :
    X.IsUnitaryC fun τ =>
      ((toGL X hx0 * c * (toGL X hx0)⁻¹) τ : Matrix (Fin r) (Fin r) ℂ) := by
  have hJ : (Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) := by
    congr 1
    funext k
    unfold sgn
    split_ifs <;> simp
  have hy : IsOrth X
      (fun τ => (mat x0 τ * (c τ : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)) := by
    intro τ
    have h0 := hx0 τ
    rw [gram_eq_mul, hJ] at h0
    change gram τ.1 X.Gm (mat x0 τ * (c τ : Matrix (Fin r) (Fin r) ℂ)) = _
    rw [gram_eq_mul, hJ, Matrix.transpose_mul, Matrix.map_mul]
    calc _ = (c τ : Matrix (Fin r) (Fin r) ℂ)ᵀ *
          ((mat x0 τ)ᵀ * (X.Gm.map τ.1 * (mat x0 τ).map (starRingEnd ℂ))) *
          (c τ : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h0, hc τ]
  have he : toGL X hy = toGL X hx0 * c := by
    funext τ
    exact Units.ext rfl
  rw [← he]
  exact quotient_unitary X hy hx0

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
lemma _root_.GlobalTheory.UnitaryLift.det_ne_zero_of_diag {r p : ℕ} {a : Matrix (Fin r) (Fin r) ℂ}
    (ha : aᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) *
      a.map (starRingEnd ℂ) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1)) : a.det ≠ 0 := by
  have hD : (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1).det ≠ 0 := by
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro k _
    split_ifs <;> norm_num
  intro h0
  have h := congrArg Matrix.det ha
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul] at h
  exact hD h.symm

open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
private lemma conj_mul_inv_preserves_gram {r : ℕ} (G D M b : Matrix (Fin r) (Fin r) ℂ)
    (hM : IsUnit M.det) (hG : Mᵀ * (G * M.map (starRingEnd ℂ)) = D)
    (hb : bᵀ * D * b.map (starRingEnd ℂ) = D) :
    (M * b * M⁻¹)ᵀ * (G * (M * b * M⁻¹).map (starRingEnd ℂ)) = G := by
  obtain ⟨P, hP⟩ : ∃ P, P = M * b * M⁻¹ := ⟨_, rfl⟩
  rw [← hP]
  have hPM : P * M = M * b := by
    rw [hP, mul_assoc, mul_assoc, Matrix.nonsing_inv_mul _ hM, mul_one]
  have hT : IsUnit (Mᵀ).det := by rwa [Matrix.det_transpose]
  have hC : IsUnit (M.map (starRingEnd ℂ)).det := by
    have := (RingHom.map_det (starRingEnd ℂ) M).symm
    rw [show (starRingEnd ℂ).mapMatrix M = M.map (starRingEnd ℂ) from rfl] at this
    rw [this]
    exact hM.map _
  have key : Mᵀ * (Pᵀ * (G * P.map (starRingEnd ℂ))) * M.map (starRingEnd ℂ) =
      Mᵀ * G * M.map (starRingEnd ℂ) := by
    have e1 : Mᵀ * (Pᵀ * (G * P.map (starRingEnd ℂ))) * M.map (starRingEnd ℂ) =
        (P * M)ᵀ * G * (P * M).map (starRingEnd ℂ) := by
      simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    rw [e1, hPM, Matrix.transpose_mul, Matrix.map_mul]
    calc bᵀ * Mᵀ * G * (M.map (starRingEnd ℂ) * b.map (starRingEnd ℂ))
        = bᵀ * (Mᵀ * (G * M.map (starRingEnd ℂ))) * b.map (starRingEnd ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = Mᵀ * G * M.map (starRingEnd ℂ) := by
          rw [hG, hb, ← hG, Matrix.mul_assoc]
  calc Pᵀ * (G * P.map (starRingEnd ℂ))
      = (Mᵀ)⁻¹ * (Mᵀ * (Pᵀ * (G * P.map (starRingEnd ℂ))) * M.map (starRingEnd ℂ)) *
          (M.map (starRingEnd ℂ))⁻¹ := by
        rw [← Matrix.mul_assoc (Mᵀ)⁻¹, Matrix.mul_nonsing_inv_cancel_right _ _ hC, Matrix.nonsing_inv_mul_cancel_left _ _ hT]
    _ = (Mᵀ)⁻¹ * (Mᵀ * G * M.map (starRingEnd ℂ)) * (M.map (starRingEnd ℂ))⁻¹ := by rw [key]
    _ = G := by
        rw [← Matrix.mul_assoc (Mᵀ)⁻¹, Matrix.mul_nonsing_inv_cancel_right _ _ hC, Matrix.nonsing_inv_mul_cancel_left _ _ hT]


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.UnitaryLift.step_of_right_mul :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (H : Subgroup (X.Ψ → GL (Fin r) ℂ)), (∀ g, g ∈ H ↔ X.IsUnitaryC fun τ => (g τ : Matrix (Fin r) (Fin r) ℂ)) → ∀ x0, _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x0 → ∀ (τ0 : X.Ψ) (a s : Matrix (Fin r) (Fin r) ℂ), (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) → (s)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) * (s).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) → s * a = a⁻¹ * s → ∃ h k : H, k * h = h⁻¹ * k ∧ ∀ g : H, (X.lmulC (fun τ => (((g * h : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) = (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) τ0 (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat (X.lmulC (fun τ => (((g : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ)) x0) τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ))) := by
  classical
  intro r X H hH x0 hx0 τ0 a s ha hs hsa
  have hM : IsUnit (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0).det :=
    isUnit_iff_ne_zero.mpr (_root_.GlobalTheory.UnitaryFrames.det_ne_zero_of_isOrth X hx0 τ0)
  have ha' : IsUnit a.det := isUnit_iff_ne_zero.mpr (_root_.GlobalTheory.UnitaryLift.det_ne_zero_of_diag ha)
  have hs' : IsUnit s.det := isUnit_iff_ne_zero.mpr (_root_.GlobalTheory.UnitaryLift.det_ne_zero_of_diag hs)
  have horth : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0)ᵀ * (X.Gm.map (τ0 : E →+* ℂ) * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0).map (starRingEnd ℂ)) =
      Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1 := by
    have h := hx0
    unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at h
    have h := h τ0
    rw [_root_.GlobalTheory.UnitaryFrames.gram_eq_mul] at h
    rw [h]
    congr 1
    funext k
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> simp
  let ν : GL (Fin r) ℂ := Matrix.nonsingInvUnit _ hM
  have hmem : ∀ b : GL (Fin r) ℂ, (b : Matrix (Fin r) (Fin r) ℂ)ᵀ *
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) *
      (b : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) =
      (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) →
      (Pi.mulSingle τ0 (ν * b * ν⁻¹) : X.Ψ → GL (Fin r) ℂ) ∈ H := by
    intro b hb
    rw [hH]
    intro τ u w
    by_cases hτ : τ = τ0
    · beta_reduce
      rw [hτ, Pi.mulSingle_eq_same]
      have hcoe : ((ν * b * ν⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) =
          _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0 * b * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0)⁻¹ := rfl
      rw [hcoe, _root_.GlobalTheory.UnitaryFrames.hermC_mulVec, _root_.GlobalTheory.UnitaryFrames.gram_eq_mul,
        conj_mul_inv_preserves_gram _ _ _ _ hM horth hb, _root_.GlobalTheory.UnitaryFrames.hermC_eq_dot]
    · beta_reduce
      rw [Pi.mulSingle_eq_of_ne hτ, Units.val_one, Matrix.one_mulVec, Matrix.one_mulVec]
  let αa : GL (Fin r) ℂ := Matrix.nonsingInvUnit a ha'
  let σ : GL (Fin r) ℂ := Matrix.nonsingInvUnit s hs'
  have hσ : σ * αa = αa⁻¹ * σ := Units.ext hsa
  have hσ' : σ * αa⁻¹ = αa * σ := by
    calc σ * αa⁻¹ = αa * (αa⁻¹ * σ) * αa⁻¹ := by group
      _ = αa * (σ * αa) * αa⁻¹ := by rw [hσ]
      _ = αa * σ := by group
  let hh : H := (⟨_, hmem αa ha⟩ : H)⁻¹
  have hh0 : ((hh : X.Ψ → GL (Fin r) ℂ) τ0 : Matrix (Fin r) (Fin r) ℂ) =
      _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0 * a⁻¹ * (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0)⁻¹ := by
    simp only [hh, Subgroup.coe_inv, Pi.inv_apply, Pi.mulSingle_eq_same]
    rw [show (ν * αa * ν⁻¹)⁻¹ = ν * αa⁻¹ * ν⁻¹ by group]
    rfl
  have hhne : ∀ τ, τ ≠ τ0 → ((hh : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) = 1 := by
    intro τ hτ
    simp only [hh, Subgroup.coe_inv, Pi.inv_apply, Pi.mulSingle_eq_of_ne hτ, inv_one, Units.val_one]
  refine ⟨hh, ⟨_, hmem σ hs⟩, ?_, ?_⟩
  · apply Subtype.ext
    simp only [hh, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    rw [← Pi.mulSingle_inv, ← Pi.mulSingle_mul, ← Pi.mulSingle_mul]
    congr 1
    calc ν * σ * ν⁻¹ * (ν * αa * ν⁻¹)⁻¹ = ν * (σ * αa⁻¹) * ν⁻¹ := by group
      _ = ν * (αa * σ) * ν⁻¹ := by rw [hσ']
      _ = ν * αa * ν⁻¹ * (ν * σ * ν⁻¹) := by group
  · intro g
    refine funext fun τ => ?_
    by_cases hτ : τ = τ0
    · rw [hτ]
      refine Eq.trans ?_ (@Function.update_self _ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) τ0 _ _).symm
      change (((g * hh : H) : X.Ψ → GL (Fin r) ℂ) τ0 : Matrix (Fin r) (Fin r) ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0 =
        ((g : X.Ψ → GL (Fin r) ℂ) τ0 : Matrix (Fin r) (Fin r) ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ0 * a⁻¹
      rw [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, hh0, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul_cancel_right _ _ hM, Matrix.mul_assoc]
    · refine Eq.trans ?_ (@Function.update_of_ne _ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) _ _ hτ _ _).symm
      change (((g * hh : H) : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ =
        ((g : X.Ψ → GL (Fin r) ℂ) τ : Matrix (Fin r) (Fin r) ℂ) * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x0 τ
      rw [Subgroup.coe_mul, Pi.mul_apply, Units.val_mul, hhne τ hτ, Matrix.mul_one]

end GlobalTheory.UnitaryLift
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

open scoped Matrix in
private theorem gram_mul_eq_transpose_mul_gram_mul_conj {F : Type} [Field F] {r : ℕ} (τ : F →+* ℂ)
    (G : Matrix (Fin r) (Fin r) F) (A g : Matrix (Fin r) (Fin r) ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G (A * g) = gᵀ * _root_.ReciprocityTheory.ChartRestriction.G.FD.gram τ G A * g.map (starRingEnd ℂ) := by
  simp only [_root_.GlobalTheory.UnitaryFrames.gram_eq_mul, Matrix.transpose_mul, Matrix.map_mul,
    Matrix.mul_assoc]

open scoped Matrix in
private theorem transpose_mul_diagonal_mul_conj_of_offDiag_eq_zero {r : ℕ}
    {B : Matrix (Fin r) (Fin r) ℂ} (d : Fin r → ℂ) (hdiag : ∀ a c, c ≠ a → B a c = 0) :
    Bᵀ * Matrix.diagonal d * B.map (starRingEnd ℂ) =
      Matrix.diagonal fun a => ((Complex.normSq (B a a) : ℝ) : ℂ) * d a := by
  have hBd : B = Matrix.diagonal fun a => B a a := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [Matrix.diagonal_apply_ne _ hij, hdiag i j (Ne.symm hij)]
  rw [hBd]
  simp only [Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq]
  congr 1
  funext a
  rw [← Complex.mul_conj]
  ring

open scoped Matrix in
private theorem transpose_mul_diagonal_mul_conj_eq_diagonal_iff {r : ℕ} {B : Matrix (Fin r) (Fin r) ℂ}
    {d : Fin r → ℂ} (hd : ∀ a, d a ≠ 0) (hdet : B.det ≠ 0) (hup : ∀ a c, c < a → B a c = 0) :
    Bᵀ * Matrix.diagonal d * B.map (starRingEnd ℂ) = Matrix.diagonal d ↔
      ∀ a, ‖B a a‖ = 1 ∧ ∀ c, c ≠ a → B a c = 0 := by
  constructor
  · intro h
    have hunit : IsUnit B.det := isUnit_iff_ne_zero.2 hdet
    have htri : B.BlockTriangular id := fun i j hij => hup i j hij
    letI := B.invertibleOfIsUnitDet hunit
    have hinv : B⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular htri
    have h2 : Matrix.diagonal d * B.map (starRingEnd ℂ) = (B⁻¹)ᵀ * Matrix.diagonal d := by
      have h3 : (B⁻¹)ᵀ * (Bᵀ * Matrix.diagonal d * B.map (starRingEnd ℂ)) =
          (B⁻¹)ᵀ * Matrix.diagonal d := by rw [h]
      rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
        Matrix.mul_nonsing_inv _ hunit, Matrix.transpose_one, Matrix.one_mul] at h3
    have hoff : ∀ a c, a < c → B a c = 0 := by
      intro a c hac
      have h4 := congrFun (congrFun h2 a) c
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply, hinv hac, zero_mul,
        Matrix.map_apply] at h4
      have h5 := (mul_eq_zero.1 h4).resolve_left (hd a)
      simpa using h5
    have hdiag : ∀ a c, c ≠ a → B a c = 0 := by
      intro a c hca
      rcases lt_or_gt_of_ne hca with hlt | hlt
      · exact hup a c hlt
      · exact hoff a c hlt
    rw [transpose_mul_diagonal_mul_conj_of_offDiag_eq_zero d hdiag] at h
    intro a
    refine ⟨?_, hdiag a⟩
    have h6 := congrFun (congrFun h a) a
    simp only [Matrix.diagonal_apply_eq] at h6
    have h7 : ((Complex.normSq (B a a) : ℝ) : ℂ) = 1 :=
      mul_right_cancel₀ (hd a) (h6.trans (one_mul _).symm)
    have h8 : ‖B a a‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      exact_mod_cast h7
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h8
  · intro h
    rw [transpose_mul_diagonal_mul_conj_of_offDiag_eq_zero d fun a c hca => (h a).2 c hca]
    congr 1
    funext a
    rw [Complex.normSq_eq_norm_sq, (h a).1]
    simp


open NumberField MeasureTheory Topology in
open scoped ContDiff ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.isOrth_rmul_iff_unitary_diagonal :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x b : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x → b ∈ _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor X.Ψ r →
      (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) ↔ ∀ τ a, ‖b τ a a‖ = 1 ∧ ∀ c, c ≠ a → b τ a c = 0)) := by
  intro r X x b hx hb
  unfold _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth at hx ⊢
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Bor at hb
  simp only [Set.mem_setOf_eq] at hb
  have hd : ∀ a : Fin r, ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 (a : ℕ) : ℝ) : ℂ) ≠ 0 := by
    intro a
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn
    split_ifs <;> norm_num
  have hprod : ∀ τ : X.Ψ, _root_.ReciprocityTheory.ChartRestriction.G.FD.mat (_root_.ReciprocityTheory.ChartRestriction.G.FD.rmul x b) τ = _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ * _root_.ReciprocityTheory.ChartRestriction.G.FD.mat b τ := fun τ => rfl
  constructor
  · intro h τ
    have key := h τ
    rw [hprod, gram_mul_eq_transpose_mul_gram_mul_conj, hx τ] at key
    exact (transpose_mul_diagonal_mul_conj_eq_diagonal_iff hd (hb τ).1 (hb τ).2).1 key
  · intro h τ
    rw [hprod, gram_mul_eq_transpose_mul_gram_mul_conj, hx τ]
    exact (transpose_mul_diagonal_mul_conj_eq_diagonal_iff hd (hb τ).1 (hb τ).2).2 (h τ)

end GlobalTheory
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.MajorantOrthFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open NumberField MeasureTheory Topology in
open scoped ComplexOrder ENNReal Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.MajorantOrthFrame.maj_eq_sum_norm_sq_of_isOrth :
    (∀ (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x →
      (∀ τ : X.Ψ, (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0) ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ),
        X.maj x τ v = ∑ a, ‖((_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ)⁻¹.mulVec v) a‖ ^ 2) := by
  intro r X x hx
  refine ⟨_root_.GlobalTheory.UnitaryFrames.det_ne_zero_of_isOrth X hx, fun τ v => ?_⟩
  have hdet : (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ).det ≠ 0 := _root_.GlobalTheory.UnitaryFrames.det_ne_zero_of_isOrth X hx τ
  have hG : _root_.ReciprocityTheory.ChartRestriction.G.FD.gram (↑τ) X.Gm (_root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ) =
      Matrix.diagonal fun a : Fin r ↦ ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑a : ℝ) : ℂ) := hx τ
  set P := _root_.ReciprocityTheory.ChartRestriction.G.FD.mat x τ with hP
  set c := P⁻¹ *ᵥ v with hc
  have hv : v = P *ᵥ c := by
    rw [hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have hcol : ∀ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (↑τ) X.Gm v (_root_.ReciprocityTheory.ChartRestriction.G.FD.col P a) = c a * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑a : ℝ) : ℂ) := by
    intro a
    have hcolumn : _root_.ReciprocityTheory.ChartRestriction.G.FD.col P a = P *ᵥ Pi.single a 1 := by
      ext i
      simp [_root_.ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.mulVec_single_one]
    rw [hcolumn, hv, _root_.GlobalTheory.UnitaryFrames.hermC_mulVec, hG]
    simp [dotProduct, Matrix.mulVec_diagonal, Pi.single_apply]
  have hvv : _root_.ReciprocityTheory.ChartRestriction.G.FD.hermC (↑τ) X.Gm v v = ∑ a, c a * ((_root_.ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 ↑a : ℝ) : ℂ) * star (c a) := by
    conv_lhs => rw [hv]
    rw [_root_.GlobalTheory.UnitaryFrames.hermC_mulVec, hG]
    simp [dotProduct, Matrix.mulVec_diagonal, mul_assoc]
  have hgp : X.gramPos x τ = 1 := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.gramPos
    rw [← hP, hG]
    ext a b
    simp [Matrix.one_apply, Matrix.diagonal_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn]
  have hp : X.p0 ≤ r := X.p0_le
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.maj _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.posPart
  rw [hgp, hvv]
  simp only [← hP, inv_one, Matrix.one_apply, hcol]
  simp [Finset.sum_ite_eq, _root_.ReciprocityTheory.ChartRestriction.G.FD.sgn]
  have key : ∀ f : Fin r → ℝ,
      ∑ b : Fin X.p0, f (Fin.castLE hp b) = ∑ a : Fin r, if (a : ℕ) < X.p0 then f a else 0 := by
    intro f
    have hmap := Finset.sum_map Finset.univ (Fin.castLEEmb hp) f
    simp only [Fin.castLEEmb_apply] at hmap
    rw [← Finset.sum_filter, ← hmap]
    congr 1
    ext a
    simp only [Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_filter, Fin.castLEEmb_apply]
    constructor
    · rintro ⟨b, rfl⟩
      exact b.isLt
    · intro h
      exact ⟨⟨a, h⟩, rfl⟩
  rw [key fun a => (c a).re * (c a).re + (c a).im * (c a).im, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  split_ifs <;> ring

end GlobalTheory.MajorantOrthFrame
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix

namespace GlobalTheory.FiniteCovolume

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma inv_keeps_gram {r : ℕ} {J a : Matrix (Fin r) (Fin r) ℂ} (hJ : J.det ≠ 0)
    (ha : aᵀ * J * a.map (starRingEnd ℂ) = J) :
    (a⁻¹)ᵀ * J * (a⁻¹).map (starRingEnd ℂ) = J := by
  have hdet : IsUnit a.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => hJ ?_
    rw [← ha, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul]
  have h1 : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a hdet
  have h2 : (a⁻¹)ᵀ * aᵀ = 1 := by rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
  have h3 : a.map (starRingEnd ℂ) * (a⁻¹).map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  calc (a⁻¹)ᵀ * J * (a⁻¹).map (starRingEnd ℂ)
      = (a⁻¹)ᵀ * (aᵀ * J * a.map (starRingEnd ℂ)) * (a⁻¹).map (starRingEnd ℂ) := by rw [ha]
    _ = ((a⁻¹)ᵀ * aᵀ) * J * (a.map (starRingEnd ℂ) * (a⁻¹).map (starRingEnd ℂ)) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [h2, h3, Matrix.one_mul, Matrix.mul_one]

theorem isOrth_update_mul_inv :
    (∀ (r : ℕ) (X : Data E r) (τ0 : X.Ψ) (x : Frame X.Ψ r) (a : Matrix (Fin r) (Fin r) ℂ), IsOrth X x → (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1) → IsOrth X (@Function.update X.Ψ (fun _ => Fin r → Fin r → ℂ) (Classical.decEq _) x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ))) := by
  intro r X τ0 x a hx ha τ
  letI : DecidableEq X.Ψ := Classical.decEq _
  by_cases hτ : τ = τ0
  · subst hτ
    have hm : mat (Function.update x τ (mat x τ * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) τ
        = mat x τ * a⁻¹ := by
      unfold mat
      exact Function.update_self _ _ _
    have hJ : (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1)
        = gram τ.1 X.Gm (mat x τ) := by
      rw [hx τ]
      congr 1
      funext k
      unfold sgn
      split_ifs <;> simp
    have hdet : (Matrix.diagonal fun k : Fin r => if (k : ℕ) < X.p0 then (1 : ℂ) else -1).det
        ≠ 0 := by
      rw [Matrix.det_diagonal]
      refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
      split_ifs <;> simp
    have h := inv_keeps_gram hdet ha
    rw [hJ] at h
    rw [hm, ← hx τ, ← h, GlobalTheory.UnitaryFrames.gram_eq_mul, GlobalTheory.UnitaryFrames.gram_eq_mul,
      Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  · have hm : mat (Function.update x τ0 (mat x τ0 * a⁻¹ : Matrix (Fin r) (Fin r) ℂ)) τ
        = mat x τ := by
      unfold mat
      exact Function.update_of_ne hτ _ _
    rw [hm]
    exact hx τ

end GlobalTheory.FiniteCovolume
end

section

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
theorem _root_.GlobalTheory.T.relIndex_integralSpan_supermultiplicative : (∀ (r : ℕ) (X : Data E r) (α β γ : Type) [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (w : α ⊕ β ⊕ γ → Fin r → E), LinearIndependent E w → (∀ a, w a ∈ X.Λ) → ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.map id Sum.inl : α ⊕ β → α ⊕ β ⊕ γ)))).toAddSubgroup)) * ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.map id Sum.inr : α ⊕ γ → α ⊕ β ⊕ γ)))).toAddSubgroup)) ≤ ((Submodule.span (𝓞 E) (Set.range (w ∘ (Sum.inl : α → α ⊕ β ⊕ γ)))).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range (w ∘ (Sum.inl : α → α ⊕ β ⊕ γ)))).toAddSubgroup)) * ((Submodule.span (𝓞 E) (Set.range w)).toAddSubgroup.relIndex (X.Λ.toAddSubgroup ⊓ (Submodule.span E (Set.range w)).toAddSubgroup))) := by
  first | exact @GlobalTheory.SpanIndex.relIndex_span_mul_le | exact GlobalTheory.SpanIndex.relIndex_span_mul_le | (intros; apply GlobalTheory.SpanIndex.relIndex_span_mul_le <;> assumption)
end
