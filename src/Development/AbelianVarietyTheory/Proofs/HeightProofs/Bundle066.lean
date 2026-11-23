module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle049
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle062
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle063
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle064
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle052
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle057
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle005
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

@[expose] public section

section

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.TypeSum GlobalTheory.TypeSum.CasBasis GlobalTheory.LowTypeDetermined
open scoped InnerProductSpace

namespace GlobalTheory.TypeSum.CasEquiv

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

abbrev trF (U V : Mx n) : ℝ := (trace (U * V)).re

theorem trF_sum_left {ι : Type} (s : Finset ι) (r : ι → ℝ) (Z : ι → Mx n) (V : Mx n) :
    trF (∑ c ∈ s, r c • Z c) V = ∑ c ∈ s, r c * trF (Z c) V := by
  simp [trF, Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]

theorem trF_comm (U V : Mx n) : trF U V = trF V U := by
  simp only [trF, Matrix.trace_mul_comm U V]

theorem dRep_finsum (hσ : IsURepOn (UJset ε) σ) {Z : Mx n} (hZ : Z ∈ lieSet ε) {ι : Type} (s : Finset ι)
    (w : ι → H) (hw : ∀ i, Sm ε σ (w i)) : dRep σ Z (∑ i ∈ s, w i) = ∑ i ∈ s, dRep σ Z (w i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := Dw_smul hσ (l := [Z]) (by simp [hZ]) (0 : ℂ) (x := 0) ((smooth (Jm ε) σ).zero_mem)
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact Dw_add hσ (l := [Z]) (by simp [hZ]) (hw _) ((smooth (Jm ε) σ).sum_mem fun i _ => hw i)

variable [CompleteSpace H]

theorem dRep_sum_fin (h : Std ε σ) {ι : Type} [Fintype ι] {Z : ι → Mx n} (hZ : ∀ c, Z c ∈ lieSet ε) {w : H}
    (hw : Sm ε σ w) (a : ι → ℝ) : dRep σ (∑ c, a c • Z c) w = ∑ c, (a c : ℂ) • dRep σ (Z c) w := by
  let e := Fintype.equivFin ι
  have := h.dRep_sum (B := Z ∘ e.symm) (fun i => hZ _) hw (a ∘ e.symm)
  simpa only [Function.comp_apply, e.symm.sum_comp (fun c => a c • Z c),
    e.symm.sum_comp (fun c => (a c : ℂ) • dRep σ (Z c) w)] using this

theorem dRep_dRep_sum (h : Std ε σ) {ι : Type} [Fintype ι] {Z : ι → Mx n} (hZ : ∀ c, Z c ∈ lieSet ε) {v : H}
    (hv : Sm ε σ v) (a b : ι → ℝ) :
    dRep σ (∑ c, a c • Z c) (dRep σ (∑ d, b d • Z d) v) =
      ∑ c, ∑ d, ((a c * b d : ℝ) : ℂ) • dRep σ (Z c) (dRep σ (Z d) v) := by
  have hs : ∀ d, Sm ε σ (dRep σ (Z d) v) := fun d => dRep_mem (isUnit_Jm ε) h.1 hv (hZ d)
  have hw : Sm ε σ (∑ d, (b d : ℂ) • dRep σ (Z d) v) :=
    (smooth (Jm ε) σ).sum_mem fun d _ => (smooth (Jm ε) σ).smul_mem _ (hs d)
  rw [dRep_sum_fin h hZ hv b, dRep_sum_fin h hZ hw a]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [dRep_finsum h.1 (hZ c) _ _ fun d => (smooth (Jm ε) σ).smul_mem _ (hs d), Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  have := Dw_smul h.1 (l := [Z c]) (by simp [hZ c]) (b d : ℂ) (hs d)
  rw [show dRep σ (Z c) ((b d : ℂ) • dRep σ (Z d) v) = (b d : ℂ) • dRep σ (Z c) (dRep σ (Z d) v) from this,
    smul_smul]
  push_cast; ring_nf

theorem trF_conj {g : Mx n} (hg : g ∈ UJset ε) (U V : Mx n) : trF (g⁻¹ * U * g) V = trF U (g * V * g⁻¹) := by
  unfold trF
  congr 1
  rw [show g⁻¹ * U * g * V = g⁻¹ * (U * g * V) by simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem trF_conj_conj {g : Mx n} (hg : g ∈ UJset ε) (U V : Mx n) :
    trF (g * U * g⁻¹) (g * V * g⁻¹) = trF U V := by
  unfold trF
  congr 1
  have e : g * U * g⁻¹ * (g * V * g⁻¹) = g * (U * V * g⁻¹) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc g⁻¹ g, inv_mul_UJ hg, Matrix.one_mul]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, inv_mul_UJ hg, Matrix.mul_one]

theorem conj_mem' {g : Mx n} (hg : g ∈ UJset ε) {X : Mx n} (hX : X ∈ lieSet ε) : g * X * g⁻¹ ∈ lieSet ε := by
  have := conj_mem_lie (isUnit_Jm ε) (inv_mem_UJ hg) hX
  rwa [Matrix.nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 (isUnit_of_UJ hg))] at this

theorem coef_orth {ι : Type} [Fintype ι] [DecidableEq ι] {Z : ι → Mx n} {s : ι → ℝ} (hs : ∀ c, s c * s c = 1)
    (hO : ∀ c d, trF (Z c) (Z d) = if c = d then s c else 0)
    (hE : ∀ U ∈ lieSet ε, U = ∑ c, (s c * trF U (Z c)) • Z c) (hZ : ∀ c, Z c ∈ lieSet ε) {g : Mx n}
    (hg : g ∈ UJset ε) (d e : ι) :
    ∑ c, s c * (s d * trF (g⁻¹ * Z c * g) (Z d)) * (s e * trF (g⁻¹ * Z c * g) (Z e)) =
      if d = e then s d else 0 := by
  have h3 : ∑ c, s c * trF (Z c) (g * Z d * g⁻¹) * trF (Z c) (g * Z e * g⁻¹) =
      trF (g * Z d * g⁻¹) (g * Z e * g⁻¹) := by
    conv_rhs => rw [hE _ (conj_mem' hg (hZ d)), trF_sum_left]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [trF_comm (g * Z d * g⁻¹) (Z c)]
  rw [trF_conj_conj hg, hO] at h3
  simp only [trF_conj hg]
  calc _ = s d * s e * ∑ c, s c * trF (Z c) (g * Z d * g⁻¹) * trF (Z c) (g * Z e * g⁻¹) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun c _ => ?_; ring
    _ = _ := by
        rw [h3]; split_ifs with hde
        · subst hde; rw [mul_assoc, hs, mul_one]
        · simp

theorem sum_sq_conj (h : Std ε σ) {ι : Type} [Fintype ι] [DecidableEq ι] {Z : ι → Mx n} {s : ι → ℝ}
    (hs : ∀ c, s c * s c = 1) (hO : ∀ c d, trF (Z c) (Z d) = if c = d then s c else 0)
    (hE : ∀ U ∈ lieSet ε, U = ∑ c, (s c * trF U (Z c)) • Z c) (hZ : ∀ c, Z c ∈ lieSet ε) {g : Mx n}
    (hg : g ∈ UJset ε) {v : H} (hv : Sm ε σ v) :
    ∑ c, (s c : ℂ) • dRep σ (g⁻¹ * Z c * g) (dRep σ (g⁻¹ * Z c * g) v) =
      ∑ c, (s c : ℂ) • dRep σ (Z c) (dRep σ (Z c) v) := by
  set a : ι → ι → ℝ := fun c d => s d * trF (g⁻¹ * Z c * g) (Z d) with ha
  have hW : ∀ c, g⁻¹ * Z c * g = ∑ d, a c d • Z d := fun c =>
    hE _ (conj_mem_lie (isUnit_Jm ε) hg (hZ c))
  have key := coef_orth hs hO hE hZ hg
  calc _ = ∑ c, (s c : ℂ) • ∑ d, ∑ e, ((a c d * a c e : ℝ) : ℂ) • dRep σ (Z d) (dRep σ (Z e) v) :=
        Finset.sum_congr rfl fun c _ => by rw [hW c, dRep_dRep_sum h hZ hv]
    _ = ∑ d, ∑ e, ((∑ c, s c * a c d * a c e : ℝ) : ℂ) • dRep σ (Z d) (dRep σ (Z e) v) := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Complex.ofReal_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl fun c _ => ?_
        congr 1; push_cast; ring
    _ = _ := by
        simp only [ha, key]
        refine Finset.sum_congr rfl fun d _ => ?_
        simp [apply_ite]

omit [CompleteSpace H] in
theorem casOp_translate (hσ : IsURepOn (UJset ε) σ) {d e : ℕ} {X : Fin d → Mx n} {Y : Fin e → Mx n}
    (hX : ∀ i, X i ∈ lieSet ε) (hY : ∀ b, Y b ∈ lieSet ε) {g : Mx n} (hg : g ∈ UJset ε) {v : H} (hv : Sm ε σ v) :
    casOp σ X Y (σ g v) = σ g (casOp σ (fun i => g⁻¹ * X i * g) (fun b => g⁻¹ * Y b * g) v) := by
  have h : ∀ Z ∈ lieSet ε, dRep σ Z (dRep σ Z (σ g v)) = σ g (dRep σ (g⁻¹ * Z * g) (dRep σ (g⁻¹ * Z * g) v)) :=
    fun Z hZ => Dw_translate hσ hg hv (l := [Z, Z]) (by simp [hZ])

  simp only [casOp, h _ (hX _), h _ (hY _), map_sub, map_sum]

theorem kk_orth (n : ℕ) (ε : Fin n → Bool) (i j : Fin (kList ε).length) :
    (trace (kB ε i * kB ε j)).re = if i = j then -1 else 0 := GlobalTheory.T.skewHermitianOrthonormalBasis_trace_orthonormal n ε i j
theorem pp_orth (n : ℕ) (ε : Fin n → Bool) (a b : Fin (pList ε).length) :
    (trace (pB ε a * pB ε b)).re = if a = b then 1 else 0 := GlobalTheory.T.re_trace_hermitianOrthonormalBasis_mul_eq_ite n ε a b
theorem kp_orth (n : ℕ) (ε : Fin n → Bool) (i : Fin (kList ε).length) (b : Fin (pList ε).length) :
    (trace (kB ε i * pB ε b)).re = 0 := GlobalTheory.T.re_trace_skewHermitian_mul_hermitianOrthonormalBasis n ε i b
theorem expand (n : ℕ) (ε : Fin n → Bool) : ∀ U ∈ lieSet ε,
    U = ∑ b, (trace (U * pB ε b)).re • pB ε b - ∑ i, (trace (U * kB ε i)).re • kB ε i := GlobalTheory.T.signature_lieSet_expand_orthonormal_bases n ε

theorem casOp_equivariant : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ g ∈ UJset ε, ∀ v, Sm ε σ v →
      casOp σ (kB ε) (pB ε) (σ g v) = σ g (casOp σ (kB ε) (pB ε) v) := by
  intro n ε H _ _ _ σ h g hg v hv
  obtain ⟨hk, hp⟩ := GlobalTheory.T.orthonormalBases_mem_unitaryLieAlgebra n ε
  let Z : Fin (kList ε).length ⊕ Fin (pList ε).length → Mx n := Sum.elim (kB ε) (pB ε)
  let s : Fin (kList ε).length ⊕ Fin (pList ε).length → ℝ := Sum.elim (fun _ => -1) (fun _ => 1)
  have hs : ∀ c, s c * s c = 1 := by rintro (c | c) <;> simp [s]
  have hZ : ∀ c, Z c ∈ lieSet ε := by rintro (c | c); exacts [hk c, hp c]
  have hO : ∀ c d, trF (Z c) (Z d) = if c = d then s c else 0 := by
    rintro (c | c) (d | d)
    · simpa [Z, s] using kk_orth n ε c d
    · simpa [Z, s] using kp_orth n ε c d
    · simpa [Z, s, trF_comm] using kp_orth n ε d c
    · simpa [Z, s] using pp_orth n ε c d
  have hE : ∀ U ∈ lieSet ε, U = ∑ c, (s c * trF U (Z c)) • Z c := by
    intro U hU
    simp only [Fintype.sum_sum_type, Z, s, Sum.elim_inl, Sum.elim_inr, neg_one_mul, one_mul, neg_smul,
      Finset.sum_neg_distrib]
    conv_lhs => rw [expand n ε U hU]
    abel
  have := sum_sq_conj h hs hO hE hZ hg hv
  simp only [Fintype.sum_sum_type, Z, s, Sum.elim_inl, Sum.elim_inr, Complex.ofReal_neg, Complex.ofReal_one, neg_smul,
    one_smul, Finset.sum_neg_distrib] at this
  rw [casOp_translate h.1 hk hp hg hv]
  congr 1
  simp only [casOp, sub_eq_neg_add]
  exact this

end GlobalTheory.TypeSum.CasEquiv

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

noncomputable section

namespace GlobalTheory.KFourier

theorem toMK_injective_of_gap {n : ℕ} (ε : Fin n → Bool) : Function.Injective (fun k : KG ε => toMK k) := by
  intro a b h
  exact Subtype.ext (Subtype.ext (Units.ext h))

theorem integrable_real_of_continuousK {n : ℕ} {ε : Fin n → Bool} {f : KG ε → ℝ} (hf : Continuous f) :
    Integrable f (muK ε) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem sq_dist_right_translate_le {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n) (hX : ∀ j, inK ε (X j))
    (C : ℝ) (hC : 0 ≤ C)
    (hcoef : ∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j ∧ ∑ j, c j ^ 2 ≤ C * Formalism.REAL.hs Y)
    {d : ℕ} {p : KG ε → ℂ} (hp : p ∈ polyV ε d) (k : KG ε) :
    ∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε) ≤
      3 * C * Formalism.REAL.hs (toMK k - 1) * ∑ j, ∫ x, ‖rder ε [X j] p x‖ ^ 2 ∂(muK ε) := by
  obtain ⟨Y, hY, hexp, hhs⟩ := compact_exponential_surjective n ε (toMK k) k.2
  have hk : expK ε Y 1 = k := by
    apply toMK_injective_of_gap ε
    show toMK (expK ε Y 1) = toMK k
    rw [toMK_expK hY, Complex.ofReal_one, one_smul, hexp]
  obtain ⟨c, rfl, hc⟩ := hcoef Y hY
  have h1 := GlobalTheory.T.poly_translation_l2_bound ε d p hp _ hY
  rw [hk, GlobalTheory.T.compactUnitaryRightDeriv_real_linear_direction ε d p hp X c hX] at h1
  have hcont : ∀ j, Continuous (rder ε [X j] p) := fun j =>
    continuous_of_mem (rder_mem_and_hasDerivAt ε d p hp (X j) (hX j)).1
  have hpt : ∀ x, ‖(∑ j, (c j : ℂ) • rder ε [X j] p) x‖ ^ 2 ≤
      (∑ j, c j ^ 2) * ∑ j, ‖rder ε [X j] p x‖ ^ 2 := by
    intro x
    rw [Finset.sum_apply]
    calc ‖∑ j, ((c j : ℂ) • rder ε [X j] p) x‖ ^ 2 ≤ (∑ j, |c j| * ‖rder ε [X j] p x‖) ^ 2 := by
          gcongr
          refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
          simp [Complex.norm_real]
      _ ≤ (∑ j, |c j| ^ 2) * ∑ j, ‖rder ε [X j] p x‖ ^ 2 := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ = (∑ j, c j ^ 2) * ∑ j, ‖rder ε [X j] p x‖ ^ 2 := by simp [sq_abs]
  have hint : ∀ j, Integrable (fun x => ‖rder ε [X j] p x‖ ^ 2) (muK ε) := fun j =>
    integrable_real_of_continuousK ((hcont j).norm.pow 2)
  have h2 : ∫ x, ‖(∑ j, (c j : ℂ) • rder ε [X j] p) x‖ ^ 2 ∂(muK ε) ≤
      (∑ j, c j ^ 2) * ∑ j, ∫ x, ‖rder ε [X j] p x‖ ^ 2 ∂(muK ε) := by
    rw [← integral_finsetSum _ fun j _ => hint j, ← integral_const_mul]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity)
      ((integrable_finsetSum _ fun j _ => hint j).const_mul _) (Filter.Eventually.of_forall hpt)
  have hE : 0 ≤ ∑ j, ∫ x, ‖rder ε [X j] p x‖ ^ 2 ∂(muK ε) :=
    Finset.sum_nonneg fun j _ => integral_nonneg fun x => by positivity
  calc _ ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ C * Formalism.REAL.hs (∑ j, (c j : ℂ) • X j) * ∑ j, ∫ x, ‖rder ε [X j] p x‖ ^ 2 ∂(muK ε) :=
        mul_le_mul_of_nonneg_right hc hE
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hhs hC
        nlinarith

theorem spectral_gap_rder : ∀ {n : ℕ} (ε : Fin n → Bool) {r : ℕ} (X : Fin r → Mx n), (∀ j, inK ε (X j)) →
    (∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j) → ∃ c α : ℝ, 0 < c ∧ 0 < α ∧
    ∀ i : ℕ, 1 ≤ i → ∀ p ∈ polyV ε i, (∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) →
    c * (i : ℝ) ^ α * ∫ k, ‖p k‖ ^ 2 ∂(muK ε) ≤ ∑ j, ∫ k, ‖rder ε [X j] p k‖ ^ 2 ∂(muK ε) := by
  intro n ε r X hX hspan
  obtain ⟨C3, hC3, hcoef⟩ := GlobalTheory.T.exists_spanning_lieAlgebra_coef_sq_bound ε X hspan
  obtain ⟨C4, hC4, hker⟩ := GlobalTheory.T.exists_compactUnitaryKernel_concentrated_near_one ε
  set A : ℝ := 3 * C3 * C4 ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨1 / (A + 1), 1 / 2, by positivity, by norm_num, ?_⟩
  intro i hi p hp horth
  set E := ∑ j, ∫ k, ‖rder ε [X j] p k‖ ^ 2 ∂(muK ε) with hEdef
  have hE : 0 ≤ E := Finset.sum_nonneg fun j _ => integral_nonneg fun x => by positivity
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  obtain ⟨κ, hκc, hκ0, hκ1, hκmem, hκb⟩ := hker m
  have hpc : Continuous p := continuous_of_mem hp
  have horth' := GlobalTheory.T.orthogonal_lowerDegree_kernel_translates ε (m + 1) p (fun k => (κ k : ℂ)) hκmem horth
  have h1 := GlobalTheory.T.sqrt_integral_norm_sq_le_integral_kernel_mul_translate ε p κ hpc hκc hκ0 hκ1 horth'
  set P := ∫ x, ‖p x‖ ^ 2 ∂(muK ε) with hPdef
  have hP : 0 ≤ P := integral_nonneg fun x => by positivity
  have hint : Integrable (fun k => κ k * Real.sqrt (3 * C3 * E) * Real.sqrt (Formalism.REAL.hs (toMK k - 1))) (muK ε) := by
    refine integrable_real_of_continuousK ?_
    refine (hκc.mul continuous_const).mul (Real.continuous_sqrt.comp ?_)
    unfold Formalism.REAL.hs
    fun_prop
  have h2 : ∫ k, κ k * Real.sqrt (∫ x, ‖p x - p (x * k)‖ ^ 2 ∂(muK ε)) ∂(muK ε) ≤
      ∫ k, κ k * Real.sqrt (3 * C3 * E) * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun k => mul_nonneg (hκ0 k) (Real.sqrt_nonneg _))
      hint (Filter.Eventually.of_forall fun k => ?_)
    dsimp only
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (hκ0 k)
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have := sq_dist_right_translate_le ε X hX C3 hC3 hcoef hp k
    nlinarith [show 0 ≤ Formalism.REAL.hs (toMK k - 1) from by unfold Formalism.REAL.hs; positivity]
  have h3 : ∫ k, κ k * Real.sqrt (3 * C3 * E) * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε) =
      Real.sqrt (3 * C3 * E) * ∫ k, κ k * Real.sqrt (Formalism.REAL.hs (toMK k - 1)) ∂(muK ε) := by
    rw [← integral_const_mul]; congr 1; funext k; ring
  have hmi : ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hmi] at hκb
  set I : ℝ := ((m + 1 : ℕ) : ℝ) with hIdef
  have hI : 1 ≤ I := by rw [hIdef]; exact_mod_cast Nat.succ_pos m
  have hsq : Real.sqrt P ≤ Real.sqrt (3 * C3 * E) * (C4 * I ^ (-(1 / 4 : ℝ))) := by
    calc Real.sqrt P ≤ _ := h1
      _ ≤ _ := h2
      _ = _ := h3
      _ ≤ _ := mul_le_mul_of_nonneg_left hκb (Real.sqrt_nonneg _)
  have hq : 0 ≤ I ^ (-(1 / 4 : ℝ)) := Real.rpow_nonneg (by linarith) _
  have hPle : P ≤ 3 * C3 * E * C4 ^ 2 * (I ^ (-(1 / 4 : ℝ))) ^ 2 := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg P) hsq 2
    rw [Real.sq_sqrt hP, mul_pow, Real.sq_sqrt (by positivity), mul_pow] at h
    linarith
  have hpow : (I ^ (-(1 / 4 : ℝ))) ^ 2 * I ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), ← Real.rpow_add (by linarith)]
    norm_num
  have hIp : 0 ≤ I ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have key : I ^ (1 / 2 : ℝ) * P ≤ A * E := by
    calc I ^ (1 / 2 : ℝ) * P ≤ I ^ (1 / 2 : ℝ) * (3 * C3 * E * C4 ^ 2 * (I ^ (-(1 / 4 : ℝ))) ^ 2) :=
          mul_le_mul_of_nonneg_left hPle hIp
      _ = A * E * ((I ^ (-(1 / 4 : ℝ))) ^ 2 * I ^ (1 / 2 : ℝ)) := by rw [hA]; ring
      _ = A * E := by rw [hpow, mul_one]
  have hA1 : 0 < A + 1 := by linarith
  rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, div_le_iff₀ hA1]
  nlinarith

end GlobalTheory.KFourier

end
end
