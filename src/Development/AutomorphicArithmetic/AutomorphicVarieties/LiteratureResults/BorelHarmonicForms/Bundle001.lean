module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem tform_star_mul_self_eq_sum_cmp {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ}
    (H : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (B : Matrix (Fin d) (Fin d) ℂ) (x : W ⊗[ℂ] (Fin d → ℂ)) :
    tform H (star B * B) x x = ∑ k, H (∑ i, B k i • Bor.cmp i x) (∑ j, B k j • Bor.cmp j x) := by
  rw [tform_apply]

  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
  Matrix.mul_apply, Matrix.star_apply, starRingEnd_apply, Finset.sum_mul, Finset.mul_sum,
  RingHom.id_apply]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
  ring

open scoped ComplexOrder MatrixOrder in
theorem UpperTheory.V.Lit.Bor.tformPos :
    UpperTheory.V.Lit.Bor.TformPos := by
  intro W _ _ d H N G hH hG
  classical
  have h0 : 0 ≤ G := Matrix.nonneg_iff_posSemidef.mpr hG.posSemidef
  obtain ⟨B, hBs, -, hBB⟩ := sub_zero G ▸
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts h0.isSelfAdjoint
      (QuasispectrumRestricts.nnreal_of_nonneg h0)
  have hB : G = star B * B := by rw [hBs.star_eq, hBB, sub_zero]
  have hself : ∀ y : W, H y y = ((H y y).re : ℂ) := by
    intro y
    have hc := hH.herm y y
    apply Complex.ext
    · simp
    · have := congrArg Complex.im hc
      simp at this
      simp
      linarith
  have hz : ∀ x ∈ tens d N, ∀ k : Fin d, (∑ i, B k i • Bor.cmp i x) ∈ N := by
    intro x hx k
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (mem_tens.mp hx i)
  refine ⟨?_, ?_, ?_⟩
  · intro x y

    rw [tform_apply, tform_apply, map_sum]

    simp only [map_sum, map_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hH.herm, ← hG.isHermitian.apply j i]
    simp [mul_comm]
  · intro x hx
    rw [hB, tform_star_mul_self_eq_sum_cmp, Complex.re_sum]
    exact Finset.sum_nonneg fun k _ => hH.nonneg _ (hz x hx k)
  · intro x hx h
    rw [hB, tform_star_mul_self_eq_sum_cmp] at h
    have hre : ∑ k, (H (∑ i, B k i • Bor.cmp i x) (∑ j, B k j • Bor.cmp j x)).re = 0 := by
      rw [← Complex.re_sum, h, Complex.zero_re]
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hH.nonneg _ (hz x hx k))] at hre
    have hzero : ∀ k, (∑ i, B k i • Bor.cmp i x) = 0 := by
      intro k
      apply hH.definite _ (hz x hx k)
      rw [hself, hre k (Finset.mem_univ _), Complex.ofReal_zero]
    have hdet : IsUnit B.det := by
      have := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
      rw [hB, Matrix.det_mul] at this
      exact isUnit_of_mul_isUnit_right this
    have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B hdet
    have hcomp : ∀ l, Bor.cmp l x = 0 := by
      intro l
      have e : Bor.cmp l x = ∑ k, B⁻¹ l k • ∑ i, B k i • Bor.cmp i x := by
        simp only [Finset.smul_sum, smul_smul]
        rw [Finset.sum_comm]
        simp only [← Finset.sum_smul]
        have : ∀ i, ∑ k, B⁻¹ l k * B k i = (1 : Matrix (Fin d) (Fin d) ℂ) l i := by
          intro i
          rw [← hinv, Matrix.mul_apply]
        simp only [this, Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
      rw [e]
      simp [hzero]
    rw [← sum_cmp x]
    simp [hcomp]
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem op_cont_inf (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

open scoped Matrix.Norms.Operator in
private theorem exists_one_parameter_exp {E : Type} [Field E] [NumberField E] {a : ℕ} (Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    ∃ c : ℝ → GL (Fin a) (Cinf E), c 0 = 1 ∧ (∀ s t, c (s + t) = c s * c t) ∧ Continuous c ∧
      HasDerivAt (fun t => toL (c t).val) (toL Y) 0 ∧ ∀ t : ℝ, (c t).val = NormedSpace.exp (t • Y) := by
  let c : ℝ → GL (Fin a) (Cinf E) := fun t => (Matrix.isUnit_exp (t • Y)).unit
  have hc : ∀ t, (c t).val = NormedSpace.exp (t • Y) := fun t => rfl
  have h0 : c 0 = 1 := Units.ext (by simp [c])
  have hadd : ∀ s t, c (s + t) = c s * c t := fun s t => Units.ext (by
    rw [Units.val_mul, hc, hc, hc, add_smul,
      Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left s).smul_right t)])
  have hv : Continuous fun t : ℝ => NormedSpace.exp (t • Y) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y t).continuousAt
  have hinv : ∀ t, (c t)⁻¹ = c (-t) := fun t =>
    inv_eq_of_mul_eq_one_right (by rw [← hadd, add_neg_cancel, h0])
  refine ⟨c, h0, hadd, Units.continuous_iff.2 ⟨hv, ?_⟩, ?_, hc⟩
  · simp only [hinv, hc]
    exact hv.comp continuous_neg
  · have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
    exact h

theorem UpperTheory.V.Lit.Bor.oneParam :
    UpperTheory.V.Lit.Bor.OneParam := by
  intro E _ _ _ a X
  obtain ⟨c, h0, hadd, hc, hd, he⟩ := exists_one_parameter_exp (E := E) (Matrix.of X)
  exact ⟨c, h0, hadd, (op_cont_inf E a).comp hc, hd, he⟩
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.inclFacts :
    UpperTheory.V.Lit.Bor.InclFacts := by
  intro E _ _ _ a π Ξ r
  have hA : ∀ X m, incl π Ξ (lieA π Ξ X m) = smA Ξ X (incl π Ξ m) := fun X m => by
    induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul φ v => rfl
  have hB : ∀ X m, incl π Ξ (lieB π Ξ X m) = smB Ξ X (incl π Ξ m) := fun X m => by
    rw [smB_apply]
    induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul φ v => rfl
  refine ⟨?_, fun i m => ?_, fun k m => ?_, fun X m => ?_, fun X m => ?_⟩
  · exact Module.Flat.rTensor_preserves_injective_linearMap _ π.V.injective_subtype
  · induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]; rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]; rfl
    | tmul φ v =>
      rw [cmp_tmul]
      exact cmp_tmul i φ.1 v
  · induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul φ v => rfl
  · induction m using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
    | tmul φ v => rfl
  · rw [piAdj, smAdj, adj_apply, adj_apply, map_sub, map_sub, hA, hB, LinearMap.map_smul_of_tower]
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem ell_toL {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    ell E a (toL X) = (∑ w : InfinitePlace E, (X.trace w).re) / ((a : ℝ) * Fintype.card (InfinitePlace E)) := by
  simp [ell, Matrix.trace, Finset.sum_apply]

private theorem ell_br {E : Type} [Field E] [NumberField E] {a : ℕ} (X Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    ell E a (toL (X * Y - Y * X)) = 0 := by
  rw [ell_toL, Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  simp

theorem UpperTheory.V.Lit.Bor.ellFacts :
    UpperTheory.V.Lit.Bor.EllFacts := by
  intro E _ _ _ a
  refine ⟨fun ha => ?_, ell_br, fun k X => ?_, fun A _ _ _ _ L r hL X Y => ?_⟩
  · have h1 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
    have h2 : (Fintype.card (InfinitePlace E) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    change ell E a (toL 1) = 1
    rw [ell_toL, div_eq_one_iff_eq (mul_ne_zero h1 h2)]
    simp [mul_comm]
  · rw [ell_toL, ell_toL, Matrix.trace_mul_cycle, k.2.1, one_mul]
  · have h := hL X Y
    simp only [shift_apply, ell_br, mul_zero, zero_smul, add_zero, ← h, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
      one_mul, mul_one, smul_add, smul_smul]
    rw [mul_comm (r * ell E a (toL Y))]
    abel
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem frame_abs {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hs : LinearMap.IsSymm B) (hp : ∀ x, x ≠ 0 → 0 < B x x) :
    ∃ (n : ℕ) (e : Fin n → V), ∀ x, x = ∑ j, B (e j) x • e j := by
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hs
  refine ⟨_, fun j => (Real.sqrt (B (v j) (v j)))⁻¹ • v j, fun x => ?_⟩
  conv_lhs => rw [← v.sum_repr x]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 : 0 < B (v j) (v j) := hp _ (v.ne_zero j)
  have h1 : B (v j) x = v.repr x j * B (v j) (v j) := by
    conv_lhs => rw [← v.sum_repr x]

    rw [map_sum, Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      have : B (v j) (v k) = 0 := hv (Ne.symm hk)
      simp [this]
    · simp
  have h2 : Real.sqrt (B (v j) (v j)) * Real.sqrt (B (v j) (v j)) = B (v j) (v j) := Real.mul_self_sqrt h0.le
  have h3 : Real.sqrt (B (v j) (v j)) ≠ 0 := (Real.sqrt_pos.2 h0).ne'
  rw [smul_smul, map_smul, LinearMap.smul_apply, h1, smul_eq_mul]
  congr 1
  generalize Real.sqrt (B (v j) (v j)) = s at h2 h3
  rw [← h2]
  field_simp

private noncomputable def trB (E : Type) [Field E] [NumberField E] (a : ℕ) : LinearMap.BilinForm ℝ (Herm E a) :=
  LinearMap.mk₂ ℝ (fun X Y => trF X.1 Y.1)
    (fun X Y Z => by simp [trF, add_mul, Finset.sum_add_distrib])
    (fun c X Y => by simp [trF, Finset.mul_sum])
    (fun X Y Z => by simp [trF, mul_add, Finset.sum_add_distrib])
    (fun c X Y => by simp [trF, Finset.mul_sum])

private theorem trF_self {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Herm E a) :
    trF X.1 X.1 = ∑ w : InfinitePlace E, ∑ i, ∑ j, Complex.normSq (X.1 i j w) := by
  have h : star X.1 = X.1 := X.2
  have h' : ∀ i j w, X.1 j i w = starRingEnd ℂ (X.1 i j w) := fun i j w => by
    conv_lhs => rw [← h]
    rfl
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h' i j w, Complex.mul_conj, Complex.ofReal_re]

theorem UpperTheory.V.Lit.Bor.frameEx :
    UpperTheory.V.Lit.Bor.FrameEx := by
  intro E _ _ _ a
  refine frame_abs (trB E a) ⟨fun X Y => ?_⟩ fun X hX => ?_
  · change trF X.1 Y.1 = trF Y.1 X.1
    simp only [trF, Matrix.trace_mul_comm X.1 Y.1]
  · change 0 < trF X.1 X.1
    rw [trF_self]
    have hn : ∀ w i j, 0 ≤ Complex.normSq (X.1 i j w) := fun _ _ _ => Complex.normSq_nonneg _
    refine lt_of_le_of_ne (Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hn w i j)
      fun h => hX ?_
    refine Subtype.ext (Matrix.ext fun i j => funext fun w => ?_)
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun w _ =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hn w i j).1 h.symm w (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => hn w i j).1 h1 i (Finset.mem_univ _)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hn w i j).1 h2 j (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 h3
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.frameAd :
    UpperTheory.V.Lit.Bor.FrameAd := by
  intro E _ _ _ a n e he N _ _ β k
  have hk1 : k.1 * star k.1 = 1 := k.2.2
  have hc : ∀ i j, trF (e i).1 (adHerm k (e j)).1 = trF (e j).1 (star k.1 * (e i).1 * k.1) := fun i j => by
    have h : ((e i).1 * (k.1 * (e j).1 * star k.1)).trace = ((e j).1 * (star k.1 * (e i).1 * k.1)).trace := by
      rw [show (e i).1 * (k.1 * (e j).1 * star k.1) = ((e i).1 * k.1) * ((e j).1 * star k.1) by simp only [mul_assoc],
        Matrix.trace_mul_comm]
      simp only [mul_assoc]
    simp only [trF, adHerm, h]
  have hs : ∀ i, ∑ j, trF (e i).1 (adHerm k (e j)).1 • adHerm k (e j) = e i := fun i => by
    have h := congrArg Subtype.val (he ⟨star k.1 * (e i).1 * k.1, IsSelfAdjoint.conjugate' (e i).2 k.1⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
    refine Subtype.ext ?_
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, hc]
    calc ∑ j, trF (e j).1 (star k.1 * (e i).1 * k.1) • (adHerm k (e j)).1
        = k.1 * (∑ j, trF (e j).1 (star k.1 * (e i).1 * k.1) • (e j).1) * star k.1 := by
          simp only [adHerm, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
      _ = k.1 * (star k.1 * (e i).1 * k.1) * star k.1 := by rw [← h]
      _ = (k.1 * star k.1) * (e i).1 * (k.1 * star k.1) := by simp only [mul_assoc]
      _ = (e i).1 := by rw [hk1, one_mul, mul_one]
  calc ∑ j, β (adHerm k (e j)) (adHerm k (e j))
      = ∑ j, β (∑ i, trF (e i).1 (adHerm k (e j)).1 • e i) (adHerm k (e j)) :=
        Finset.sum_congr rfl fun j _ => by rw [← he (adHerm k (e j))]
    _ = ∑ j, ∑ i, trF (e i).1 (adHerm k (e j)).1 • β (e i) (adHerm k (e j)) := by

        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = ∑ i, β (e i) (∑ j, trF (e i).1 (adHerm k (e j)).1 • adHerm k (e j)) := by
        rw [Finset.sum_comm]

        simp only [map_sum, map_smul]
    _ = ∑ j, β (e j) (e j) := by simp only [hs]
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open MeasureTheory
open scoped TensorProduct ComplexOrder

theorem UpperTheory.V.Lit.Bor.avgPos :
    UpperTheory.V.Lit.Bor.AvgPos := by
  intro K _ _ _ _ _ d ρ hρ
  classical
  letI : MeasurableSpace K := borel K
  haveI : BorelSpace K := ⟨rfl⟩
  let μ : Measure K := Measure.haar
  have hint : ∀ f : K → ℂ, Continuous f → Integrable f μ := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hc : ∀ i j, Continuous fun h : K => ρ h⁻¹ i j := fun i j => (hρ i j).comp continuous_inv
  let F : K → Matrix (Fin d) (Fin d) ℂ := fun h => (ρ h⁻¹)ᴴ * ρ h⁻¹
  have hFc : ∀ a b, Continuous fun h => F h a b := by
    intro a b
    simp only [F, Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact continuous_finsetSum _ fun l _ => (continuous_star.comp (hc l a)).mul (hc l b)
  have hlin : ∀ (A C : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d),
      (A * Matrix.of (fun a b => ∫ h, F h a b ∂μ) * C) i j = ∫ h, (A * F h * C) i j ∂μ := by
    intro A C i j
    simp only [Matrix.mul_apply, Matrix.of_apply]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_mul_const, integral_finsetSum]
      · congr 1
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_const_mul]
      · intro a _
        exact hint _ (continuous_const.mul (hFc a b))
    · intro b _
      exact hint _ ((continuous_finsetSum _ fun a _ => continuous_const.mul (hFc a b)).mul
        continuous_const)
  refine ⟨Matrix.of fun a b => ∫ h, F h a b ∂μ, ?_, ?_⟩
  · rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨?_, ?_⟩
    · refine Matrix.IsHermitian.ext fun i j => ?_
      simp only [Matrix.of_apply]
      rw [show star (∫ h, F h j i ∂μ) = ∫ h, star (F h j i) ∂μ from integral_conj.symm]
      congr 1
      funext h
      exact (Matrix.isHermitian_conjTranspose_mul_self (ρ h⁻¹)).apply i j
    · intro x hx
      have hq : ∀ h, star x ⬝ᵥ (F h *ᵥ x) = star (ρ h⁻¹ *ᵥ x) ⬝ᵥ (ρ h⁻¹ *ᵥ x) := by
        intro h
        rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
      have hdot : star x ⬝ᵥ (Matrix.of (fun a b => ∫ h, F h a b ∂μ) *ᵥ x) =
          ∫ h, star x ⬝ᵥ (F h *ᵥ x) ∂μ := by
        simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
        rw [integral_finsetSum]
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finsetSum]
          · refine Finset.sum_congr rfl fun j _ => ?_
            rw [integral_const_mul, integral_mul_const]
          · intro j _
            exact hint _ (continuous_const.mul ((hFc i j).mul continuous_const))
        · intro i _
          exact hint _ (continuous_finsetSum _ fun j _ =>
            continuous_const.mul ((hFc i j).mul continuous_const))
      have hre : ∀ h, star (ρ h⁻¹ *ᵥ x) ⬝ᵥ (ρ h⁻¹ *ᵥ x) =
          ((star (ρ h⁻¹ *ᵥ x) ⬝ᵥ (ρ h⁻¹ *ᵥ x)).re : ℂ) := by
        intro h
        have h0 := (Complex.le_def.mp (dotProduct_star_self_nonneg (ρ h⁻¹ *ᵥ x))).2
        rw [Complex.zero_im] at h0
        apply Complex.ext
        · rw [Complex.ofReal_re]
        · rw [Complex.ofReal_im]
          exact h0.symm
      have hyc : ∀ l, Continuous fun h => (ρ h⁻¹ *ᵥ x) l := by
        intro l
        simp only [Matrix.mulVec, dotProduct]
        exact continuous_finsetSum _ fun j _ => (hc l j).mul continuous_const
      have hdc : Continuous fun h => star (ρ h⁻¹ *ᵥ x) ⬝ᵥ (ρ h⁻¹ *ᵥ x) := by
        simp only [dotProduct, Pi.star_apply]
        exact continuous_finsetSum _ fun l _ => (continuous_star.comp (hyc l)).mul (hyc l)
      rw [hdot]
      simp only [hq]
      rw [congrArg (integral μ) (funext hre), integral_complex_ofReal, Complex.zero_lt_real]
      rw [integral_pos_iff_support_of_nonneg]
      · have hsupp : Function.support (fun h => (star (ρ h⁻¹ *ᵥ x) ⬝ᵥ (ρ h⁻¹ *ᵥ x)).re) =
            Set.univ := by
          ext h
          simp only [Function.mem_support, Set.mem_univ, iff_true]
          intro h0
          have hz : star (ρ h⁻¹ *ᵥ x) ⬝ᵥ (ρ h⁻¹ *ᵥ x) = 0 := by
            rw [hre h, h0, Complex.ofReal_zero]
          rw [dotProduct_star_self_eq_zero] at hz
          apply hx
          have e : ρ h *ᵥ (ρ h⁻¹ *ᵥ x) = x := by
            rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
          rw [← e, hz, Matrix.mulVec_zero]
        rw [hsupp]
        exact Measure.measure_univ_pos.mpr (NeZero.ne μ)
      · intro h
        have := (Complex.le_def.mp (dotProduct_star_self_nonneg (ρ h⁻¹ *ᵥ x))).1
        simpa using this
      · exact (Complex.continuous_re.comp hdc).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
  · intro k
    ext i j
    rw [hlin]
    have hF : ∀ h, (ρ k)ᴴ * F h * ρ k = F (k⁻¹ * h) := by
      intro h
      simp only [F, _root_.mul_inv_rev, inv_inv, map_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    simp only [hF]
    exact integral_mul_left_eq_self (fun h => F h i j) k⁻¹
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.holExt :
    UpperTheory.V.Lit.Bor.HolExt := by
  intro E _ _ _ a f hf
  induction hf using Algebra.adjoin_induction with
  | mem f hf =>
    rcases hf with ⟨τ, i, j, rfl⟩ | ⟨τ, rfl⟩
    · exact ⟨fun x => x i j τ, by fun_prop, fun _ => rfl⟩
    · refine ⟨fun x => ((Matrix.of x).det τ)⁻¹, DifferentiableOn.inv ?_ fun x hx => ?_, fun y => ?_⟩
      · simp only [Matrix.det_apply', Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Matrix.of_apply]
        exact Differentiable.differentiableOn (Differentiable.fun_sum fun σ _ =>
          (differentiable_const _).mul (by fun_prop))
      · exact (((Matrix.isUnit_iff_isUnit_det _).1 hx).map (Pi.evalRingHom (fun _ : E →+* ℂ => ℂ) τ)).ne_zero
      · exact congrArg (fun z : (E →+* ℂ) → ℂ => (z τ)⁻¹) ((emb E).map_det y.val).symm
  | algebraMap c => exact ⟨fun _ => c, differentiableOn_const c, fun _ => rfl⟩
  | add f g _ _ h1 h2 =>
    obtain ⟨Φ, hΦ, e1⟩ := h1
    obtain ⟨Ψ, hΨ, e2⟩ := h2
    exact ⟨Φ + Ψ, hΦ.add hΨ, fun y => by rw [Pi.add_apply, Pi.add_apply, e1, e2]⟩
  | mul f g _ _ h1 h2 =>
    obtain ⟨Φ, hΦ, e1⟩ := h1
    obtain ⟨Ψ, hΨ, e2⟩ := h2
    exact ⟨Φ * Ψ, hΦ.mul hΨ, fun y => by rw [Pi.mul_apply, Pi.mul_apply, e1, e2]⟩
end
