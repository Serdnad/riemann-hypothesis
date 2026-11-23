module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.schTensor :
    UpperTheory.V.Af.Smo.SchOfClosed → UpperTheory.V.Af.Smo.SchTensor := by
  intro hS V M _ _ _ _ _ _ h hh hhc α
  classical
  let S : Set (V × M → ℂ) := {F | ∃ (f : V → ℂ) (β : 𝓢(M, ℂ)), ContDiff ℝ ∞ f ∧
    HasCompactSupport f ∧ F = fun p => f p.1 * β p.2}
  let A : Set (V × M → ℂ) := (Submodule.span ℂ S : Set (V × M → ℂ))
  have hgen : ∀ F ∈ S, (∃ C, ∀ x, ‖F x‖ ≤ C) ∧ Differentiable ℝ F ∧
      (∀ v : V × M, (fun x => fderiv ℝ F x v) ∈ A) ∧
      ∀ l : V × M →L[ℝ] ℝ, (fun x => (l x : ℂ) * F x) ∈ A := by
    rintro F ⟨f, β, hf, hfc, rfl⟩
    have hfd : Differentiable ℝ f := hf.differentiable (by simp)
    refine ⟨?_, ?_, ?_, ?_⟩
    · obtain ⟨Cf, hCf⟩ := hfc.exists_bound_of_continuous hf.continuous
      obtain ⟨Cb, hCb⟩ : ∃ C, ∀ y, ‖β y‖ ≤ C :=
        ⟨‖β.toBoundedContinuousFunction‖, fun y => by
          simpa using β.toBoundedContinuousFunction.norm_coe_le_norm y⟩
      refine ⟨Cf * Cb, fun p => ?_⟩
      rw [norm_mul]
      exact mul_le_mul (hCf _) (hCb _) (norm_nonneg _) (le_trans (norm_nonneg _) (hCf p.1))
    · exact (hfd.comp differentiable_fst).mul (β.differentiable.comp differentiable_snd)
    · intro v
      have hder : ∀ p : V × M, fderiv ℝ (fun p : V × M => f p.1 * β p.2) p v =
          fderiv ℝ f p.1 v.1 * β p.2 + f p.1 * (LineDeriv.lineDerivOp v.2 β : 𝓢(M, ℂ)) p.2 := by
        intro p
        have h1 : HasFDerivAt (fun p : V × M => f p.1)
            ((fderiv ℝ f p.1).comp (ContinuousLinearMap.fst ℝ V M)) p :=
          (hfd p.1).hasFDerivAt.comp p hasFDerivAt_fst
        have h2 : HasFDerivAt (fun p : V × M => β p.2)
            ((fderiv ℝ β p.2).comp (ContinuousLinearMap.snd ℝ V M)) p :=
          (β.differentiableAt).hasFDerivAt.comp p hasFDerivAt_snd
        rw [show (fun p : V × M => f p.1 * β p.2) = (fun p => f p.1) * (fun p => β p.2) from rfl,
          (h1.mul h2).fderiv, SchwartzMap.lineDerivOp_apply_eq_fderiv]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
          smul_eq_mul]
        ring
      have hfe : (fun x => fderiv ℝ (fun p : V × M => f p.1 * β p.2) x v) =
          (fun p : V × M => (fun ξ => fderiv ℝ f ξ v.1) p.1 * β p.2) +
          (fun p : V × M => f p.1 * (LineDeriv.lineDerivOp v.2 β : 𝓢(M, ℂ)) p.2) := by
        ext p
        rw [hder]
        rfl
      rw [hfe]
      refine (Submodule.span ℂ S).add_mem
        (Submodule.subset_span ⟨fun ξ => fderiv ℝ f ξ v.1, β, ?_, ?_, rfl⟩)
        (Submodule.subset_span ⟨f, LineDeriv.lineDerivOp v.2 β, hf, hfc, rfl⟩)
      · exact ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const
      · exact (hfc.fderiv ℝ).comp_left (g := fun L : V →L[ℝ] ℂ => L v.1) (by simp)
    · intro l
      let l1 : V →L[ℝ] ℝ := l.comp (ContinuousLinearMap.inl ℝ V M)
      let l2 : M →L[ℝ] ℝ := l.comp (ContinuousLinearMap.inr ℝ V M)
      have hl : ∀ p : V × M, l p = l1 p.1 + l2 p.2 := by
        intro p
        simp only [l1, l2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply,
          ContinuousLinearMap.inr_apply]
        rw [← map_add (f := _)]
        congr 1
        ext <;> simp
      have htg : Function.HasTemperateGrowth (fun y : M => ((l2 y : ℝ) : ℂ)) := by
        fun_prop
      have hfe : (fun x : V × M => (l x : ℂ) * (f x.1 * β x.2)) =
          (fun p : V × M => (fun ξ => ((l1 ξ : ℝ) : ℂ) * f ξ) p.1 * β p.2) +
          (fun p : V × M => f p.1 *
            (SchwartzMap.smulLeftCLM ℂ (fun y : M => ((l2 y : ℝ) : ℂ)) β) p.2) := by
        ext p
        simp only [Pi.add_apply, SchwartzMap.smulLeftCLM_apply_apply htg, smul_eq_mul, hl p]
        push_cast
        ring
      rw [hfe]
      refine (Submodule.span ℂ S).add_mem
        (Submodule.subset_span ⟨fun ξ => ((l1 ξ : ℝ) : ℂ) * f ξ, β, ?_, ?_, rfl⟩)
        (Submodule.subset_span ⟨f, SchwartzMap.smulLeftCLM ℂ (fun y : M => ((l2 y : ℝ) : ℂ)) β,
          hf, hfc, rfl⟩)
      · exact (Complex.ofRealCLM.contDiff.comp l1.contDiff).mul hf
      · exact hfc.mul_left
  have hclosed : ∀ F ∈ A, (∃ C, ∀ x, ‖F x‖ ≤ C) ∧ Differentiable ℝ F ∧
      (∀ v : V × M, (fun x => fderiv ℝ F x v) ∈ A) ∧
      ∀ l : V × M →L[ℝ] ℝ, (fun x => (l x : ℂ) * F x) ∈ A := by
    intro F hF
    induction hF using Submodule.span_induction with
    | mem F hF => exact hgen F hF
    | zero =>
      refine ⟨⟨0, fun x => by simp⟩, differentiable_const 0, fun v => ?_, fun l => ?_⟩
      · have h0 : (fun x => fderiv ℝ (0 : V × M → ℂ) x v) = 0 := by
          ext x
          simp
        rw [h0]
        exact (Submodule.span ℂ S).zero_mem
      · have h0 : (fun x => (l x : ℂ) * (0 : V × M → ℂ) x) = 0 := by
          ext x
          simp
        rw [h0]
        exact (Submodule.span ℂ S).zero_mem
    | add F G _ _ hF hG =>
      obtain ⟨⟨C1, hC1⟩, hd1, hv1, hl1⟩ := hF
      obtain ⟨⟨C2, hC2⟩, hd2, hv2, hl2⟩ := hG
      refine ⟨⟨C1 + C2, fun x => (norm_add_le _ _).trans (add_le_add (hC1 x) (hC2 x))⟩,
        hd1.add hd2, fun v => ?_, fun l => ?_⟩
      · have he : (fun x => fderiv ℝ (F + G) x v) =
            (fun x => fderiv ℝ F x v) + (fun x => fderiv ℝ G x v) := by
          ext x
          rw [fderiv_add (hd1 x) (hd2 x)]
          rfl
        rw [he]
        exact (Submodule.span ℂ S).add_mem (hv1 v) (hv2 v)
      · have he : (fun x => (l x : ℂ) * (F + G) x) =
            (fun x => (l x : ℂ) * F x) + (fun x => (l x : ℂ) * G x) := by
          ext x
          simp [mul_add]
        rw [he]
        exact (Submodule.span ℂ S).add_mem (hl1 l) (hl2 l)
    | smul c F _ hF =>
      obtain ⟨⟨C1, hC1⟩, hd1, hv1, hl1⟩ := hF
      refine ⟨⟨‖c‖ * C1, fun x => ?_⟩, hd1.const_smul c, fun v => ?_, fun l => ?_⟩
      · rw [Pi.smul_apply, norm_smul]
        exact mul_le_mul_of_nonneg_left (hC1 x) (norm_nonneg _)
      · have he : (fun x => fderiv ℝ (c • F) x v) = c • (fun x => fderiv ℝ F x v) := by
          ext x
          rw [fderiv_const_smul (hd1 x) c]
          rfl
        rw [he]
        exact (Submodule.span ℂ S).smul_mem c (hv1 v)
      · have he : (fun x => (l x : ℂ) * (c • F) x) = c • (fun x => (l x : ℂ) * F x) := by
          ext x
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
        rw [he]
        exact (Submodule.span ℂ S).smul_mem c (hl1 l)
  obtain ⟨G, hG⟩ := hS (V × M) A hclosed _ (Submodule.subset_span ⟨h, α, hh, hhc, rfl⟩)
  exact ⟨G, fun ξ y => by rw [hG]⟩
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem inv_row {R : Type} [CommRing R] {n : ℕ} (m : ℕ) (k : Fin n) (hk : k.val = m + 1) (p : GL (Fin n) R)
    (hp : IsY (m + 1) p.val) : (∀ j, j < k → (p⁻¹).val k j = 0) ∧ (p⁻¹).val k k = 1 := by
  have h1 : ∀ j, j < k → (p⁻¹).val k j = 0 := by
    have hb : p.val.BlockTriangular (fun i : Fin n => if i.val ≤ m then 0 else i.val) := by
      intro i j hij
      dsimp only at hij
      have hi : m + 1 ≤ i.val := by split_ifs at hij <;> omega
      refine (hp i hi).2 j ?_
      rw [Fin.lt_def]
      split_ifs at hij <;> omega
    haveI : Invertible p.val := p.invertible
    have hq := Matrix.blockTriangular_inv_of_blockTriangular hb
    intro j hj
    rw [Matrix.coe_units_inv]
    refine hq ?_
    rw [Fin.lt_def] at hj
    dsimp only
    split_ifs <;> omega
  refine ⟨h1, ?_⟩
  have h2 : ((p⁻¹).val * p.val) k k = 1 := by rw [Units.inv_mul, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single k, (hp k hk.ge).1, mul_one] at h2
  · exact h2
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [h1 j h, zero_mul]
    · rw [(hp j (by rw [Fin.lt_def] at h; omega)).2 k h, mul_zero]
  · simp

theorem UpperTheory.V.Af.Smo.colConj :
    UpperTheory.V.Af.Smo.ColConj := by
  intro R _ n m hm p hp u
  set k : Fin n := ⟨m.val + 1, hm⟩ with hkdef
  have hk : k.val = m.val + 1 := rfl
  obtain ⟨hb0, hb1⟩ := inv_row m.val k hk p hp
  set c : Fin n → R := fun i => if i ≤ m then u i else 0 with hc
  set a : Fin n → R := p.val *ᵥ c with ha
  set b : Fin n → R := (p⁻¹).val k with hb
  have ha0 : ∀ i, m < i → a i = 0 := by
    intro i hi
    change ∑ j, p.val i j * c j = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j ≤ m
    · rw [(hp i hi).2 j (lt_of_le_of_lt hj hi), zero_mul]
    · simp [hc, hj]
  have hab : ∀ i j, j ≤ i → a i * b j = 0 := by
    intro i j hij
    by_cases hi : m < i
    · rw [ha0 i hi, zero_mul]
    · rw [hb0 j (by rw [Fin.lt_def] at hi ⊢; rw [Fin.le_def] at hij; omega), mul_zero]
  have hdot : b ⬝ᵥ a = 0 := Finset.sum_eq_zero fun i _ => by rw [mul_comm]; exact hab i i le_rfl
  have hsq : vecMulVec a b * vecMulVec a b = 0 := by
    rw [vecMulVec_mul_vecMulVec, hdot, zero_smul, vecMulVec_zero]
  refine ⟨⟨1 + vecMulVec a b, 1 - vecMulVec a b, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [add_mul, mul_sub, mul_sub, hsq]; simp
  · rw [sub_mul, mul_add, mul_add, hsq]; simp
  · intro i _
    refine ⟨?_, fun j hj => ?_⟩
    · simp [vecMulVec_apply, hab i i le_rfl]
    · simp [vecMulVec_apply, hab i j hj.le, Matrix.one_apply_ne hj.ne']
  · have : dotLe m (p.val m) u = a m := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [hc]
    rw [this]
    unfold supN
    rw [Finset.sum_eq_single m, Finset.sum_eq_single k]
    · have : m ≠ k := fun h => by have := congrArg Fin.val h; omega
      simp [hk, vecMulVec_apply, hb1, Matrix.one_apply_ne this]
    · intro j _ hj
      rw [if_neg fun h => hj (Fin.ext (by omega))]
    · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      split_ifs with h
      · have hne : i ≠ j := fun e => by have := congrArg Fin.val e; omega
        have : a i * b j = 0 := by
          rcases lt_or_gt_of_ne hi with h' | h'
          · rw [hb0 j (by rw [Fin.lt_def] at h' ⊢; omega), mul_zero]
          · rw [ha0 i h', zero_mul]
        simp [vecMulVec_apply, this, Matrix.one_apply_ne hne]
      · rfl
    · simp
  · have h1 : colM m u = 1 + vecMulVec c (Pi.single k 1) := by
      unfold colM
      congr 1
      ext i j
      by_cases hj : j = k
      · subst hj
        simp [vecMulVec_apply, hc, hk]
      · have : j.val ≠ m.val + 1 := fun h => hj (Fin.ext h)
        simp [vecMulVec_apply, hj, this]
    have h2 : b ᵥ* p.val = Pi.single k 1 := by
      ext j
      have : ((p⁻¹).val * p.val) k j = (1 : Matrix (Fin n) (Fin n) R) k j := by rw [Units.inv_mul]
      rw [Matrix.one_apply] at this
      rw [Pi.single_apply, ← if_congr eq_comm rfl rfl, ← this]
      rfl
    change p.val * colM m u = (1 + vecMulVec a b) * p.val
    rw [h1, mul_add, add_mul, mul_one, one_mul, mul_vecMulVec, vecMulVec_mul, h2]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology


open GroundTheory.Automorphic.FourierWhittaker in
private theorem isY_blockGL {K : Type} [Field K] {n k : ℕ} (hk : k < n) (γ : GL (Fin k) K) :
    IsY (n - 1) (blockGL hk.le γ : GL (Fin n) K).val := by
  intro i hi
  have hik : ¬ i.val < k := by omega
  refine ⟨?_, fun j hj => ?_⟩
  · rw [coe_blockGL, blockMat_apply, dite_eq_right hik, if_pos rfl]
  · rw [coe_blockGL, blockMat_apply, dite_eq_right hik, if_neg hj.ne']


open GroundTheory.Automorphic.FourierWhittaker in
open scoped NumberField.AdeleRing in
private theorem step {K : Type} [Field K] [NumberField K] {n : ℕ} {ϕ : AdelicGLn.AdelicGL K n → ℂ}
    (hc : Continuous ϕ) (hl : IsLeftInvariant ϕ) (hcusp : AutomorphicForm.IsCuspidal ϕ)
    {V : OpenSubgroup (AdelicGLn.FiniteAdelicGL K n)}
    (hV : ∀ g, ∀ v ∈ V, ϕ (g * finEmb K n v) = ϕ g) {k : ℕ} (hk0 : 0 < k) (hk : k < n)
    (g : AdelicGLn.AdelicGL K n)
    (h0 : ∀ γ : GL (Fin k) K, partialCoeff ϕ k (AdelicGLn.diagonal K n (blockGL hk.le γ) * g) = 0) :
    partialCoeff ϕ (k + 1) g = 0 := by
  classical
  obtain ⟨δ, hδ, hδV⟩ := exists_integer_colGL_mem (n := n) k V (AdelicGLn.prodEquiv K n g).2
  have hδK : (algebraMap (𝓞 K) K δ) ≠ 0 := by
    simpa using (RingOfIntegers.coe_ne_zero_iff).2 hδ
  set u : Kˣ := Units.mk0 _ hδK
  set D := AdelicGLn.diagonal K n (blockGL hk.le (scalarGL k u⁻¹)) with hD
  have hconj : ∀ w : Fin k → 𝔸[K], colGL k w * D =
      D * colGL k (fun i => algebraMap K 𝔸[K] u * w i) := by
    intro w
    simp only [D]
    rw [diagonal_blockGL, colGL_mul_blockGL hk, mulVec_map_inv, ← map_inv, inv_inv, coe_scalarGL,
      matVec_scalar]
  set F : (Fin k → 𝔸[K]) → ℂ := fun x => partialCoeff ϕ (k + 1) (colGL k x * (D * g))
  have hip : IsIntegralPeriodic F := by
    refine ⟨(continuous_partialCoeff hc _).comp ((continuous_colGL k).mul continuous_const),
      fun ξ hξ x => ?_, fun x z hz => ?_⟩
    · obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
      simp only [F]
      rw [colGL_add, mul_assoc, ← diagonal_colGL, partialCoeff_succ_diagonal_colGL hl hk]
    · have e1 : (fun i => algebraMap K 𝔸[K] (u : K) * GroundTheory.Global.finiteAdeleInr (z i)) =
          fun i => GroundTheory.Global.finiteAdeleInr (algebraMap K (FiniteAdeleRing (𝓞 K) K)
            (algebraMap (𝓞 K) K δ) * z i) := by
        funext i; rw [GroundTheory.Global.algebraMap_mul_finiteAdeleInr]; rfl
      change partialCoeff ϕ (k + 1)
          (colGL k (x + fun i => GroundTheory.Global.finiteAdeleInr (z i)) * (D * g)) =
        partialCoeff ϕ (k + 1) (colGL k x * (D * g))
      rw [colGL_add, mul_assoc (colGL k x),
        ← mul_assoc (colGL k fun i => GroundTheory.Global.finiteAdeleInr (z i)), hconj, e1,
        colGL_finiteAdeleInr, mul_assoc D, finEmb_mul_eq, ← mul_assoc,
        ← mul_assoc, partialCoeff_mul_finEmb hV _ _ (hδV z hz), mul_assoc]
  have hcoeff : vecCoeff F = 0 := by
    funext ξ
    by_cases hξ : ξ = 0
    · rw [hξ]
      exact vecCoeff_zero_of_isCuspidal hc hl hcusp hk0 hk (D * g)
    · have h1 := partialCoeff_diagonal_blockGL_eq_vecCoeff hl hk (rowCompletion ξ) (D * g)
      rw [vecMul_rowCompletion hξ] at h1
      refine h1.symm.trans ?_
      rw [hD, ← mul_assoc, ← map_mul, ← map_mul]
      exact h0 _
  have H := hip.hasSum_vecCoeff (hcoeff ▸ summable_zero) 0
  simp only [hcoeff, Pi.zero_apply, zero_mul] at H
  have hF0 : F 0 = 0 := (hasSum_zero.unique H).symm
  rw [← partialCoeff_succ_diagonal_blockGL hl hk (scalarGL k u⁻¹) g]
  change partialCoeff ϕ (k + 1) (D * g) = 0
  simpa [F, colGL_zero] using hF0

open GroundTheory.Automorphic.FourierWhittaker in
theorem UpperTheory.V.Af.Smo.injP :
    UpperTheory.V.Af.Smo.InjP := by
  intro E _ _ n hn f hf X hX hW
  obtain ⟨V, hV⟩ := hf.level
  rw [← Fb.finEmb_eq] at hV
  have key : ∀ k, k < n → ∀ g ∈ X, partialCoeff f (k + 1) g = 0 := by
    intro k
    induction k with
    | zero =>
      intro _ g hg
      exact (whittaker_eq_partialCoeff hf.cont hn g).symm.trans (hW g hg)
    | succ m ih =>
      intro hm g hg
      exact step hf.cont hf.left hf.cusp hV (Nat.succ_pos m) hm g fun γ =>
        ih (by omega) _ (hX _ (isY_blockGL hm γ) g hg)
  intro g hg
  have := key (n - 1) (by omega) g hg
  rwa [Nat.sub_add_cancel hn, partialCoeff_self] at this
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem mul_rowM_apply {R : Type} [CommRing R] {n : ℕ} (m : Fin n) (ξ : Fin n → R)
    (q : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (q * rowM m ξ) i j
      = (if j = m then 0 else q i j) + q i m * (if j ≤ m then ξ j else 0) := by
  rw [Matrix.mul_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ m)]
  have hs : ∑ k ∈ Finset.univ.erase m, q i k * rowM m ξ k j = if j = m then 0 else q i j := by
    have hk1 : ∀ k ∈ Finset.univ.erase m,
        q i k * rowM m ξ k j = q i k * (1 : Matrix (Fin n) (Fin n) R) k j := by
      intro k hk
      have hkm : k ≠ m := Finset.ne_of_mem_erase hk
      simp [rowM, hkm]
    rw [Finset.sum_congr rfl hk1]
    split_ifs with hjm
    · apply Finset.sum_eq_zero
      intro k hk
      rw [Matrix.one_apply_ne (by rw [hjm]; exact Finset.ne_of_mem_erase hk), mul_zero]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb
        rw [Matrix.one_apply_ne hb, mul_zero]
      · intro hj
        exact absurd (Finset.mem_erase.mpr ⟨hjm, Finset.mem_univ j⟩) hj
  rw [hs, add_comm]
  congr 1
  by_cases hjm : j ≤ m
  · simp [rowM, hjm]
  · have hmj : m ≠ j := fun h => hjm (le_of_eq h.symm)
    simp [rowM, hjm, Matrix.one_apply_ne hmj]

theorem UpperTheory.V.Af.Smo.rowStep :
    UpperTheory.V.Af.Smo.RowStep := by
  unfold UpperTheory.V.Af.Smo.RowStep IsY
  intro R _ n m p s hp hs
  have key : ∀ i j, (p : Matrix (Fin n) (Fin n) R) i j
      = (if j = m then 0 else ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j)
        + ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i m
          * (if j ≤ m then (p : Matrix (Fin n) (Fin n) R) m j else 0) := by
    intro i j
    have h := mul_rowM_apply m ((p : Matrix (Fin n) (Fin n) R) m)
      ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j
    rw [← hs, ← Units.val_mul, inv_mul_cancel_right] at h
    exact h
  have hu : ((s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) m m
      * (p : Matrix (Fin n) (Fin n) R) m m = 1 := by
    have h := mul_rowM_apply m ((p : Matrix (Fin n) (Fin n) R) m)
      ((s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) m m
    rw [← hs, ← Units.val_mul, inv_mul_cancel] at h
    simpa using h.symm
  generalize ((s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) m m = t at hu
  generalize ((p * s⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = Q at key ⊢
  generalize (p : Matrix (Fin n) (Fin n) R) = P at key hu hp
  intro i hi
  rcases eq_or_lt_of_le hi with h | h
  · have him : i = m := Fin.ext h.symm
    rw [him]
    have k := key m m
    rw [if_pos rfl, if_pos le_rfl, zero_add] at k
    have hQ : Q m m = 1 := by linear_combination (-t) * k + (1 - Q m m) * hu
    refine ⟨hQ, fun j hj => ?_⟩
    have k2 := key m j
    rw [if_neg (ne_of_lt hj), if_pos (le_of_lt hj), hQ, one_mul] at k2
    linear_combination -k2
  · have hi1 : (m : ℕ) + 1 ≤ (i : ℕ) := h
    obtain ⟨hpi, hpj⟩ := hp i hi1
    have hmi : m < i := h
    have k := key i m
    rw [if_pos rfl, if_pos le_rfl, zero_add, hpj m hmi] at k
    have hQm : Q i m = 0 := by linear_combination (-Q i m) * hu - t * k
    constructor
    · have k2 := key i i
      rw [if_neg (ne_of_gt hmi), if_neg (not_le.mpr hmi), mul_zero, add_zero, hpi] at k2
      exact k2.symm
    · intro j hj
      have k2 := key i j
      rw [hpj j hj] at k2
      by_cases hjm : j = m
      · rw [hjm]
        exact hQm
      · rw [if_neg hjm, hQm, zero_mul, add_zero] at k2
        exact k2.symm
end
