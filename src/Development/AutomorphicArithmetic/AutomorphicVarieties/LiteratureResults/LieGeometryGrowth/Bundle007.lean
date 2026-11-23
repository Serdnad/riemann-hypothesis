module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle005
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

section

open NumberField Matrix MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC
open UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Pf
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private noncomputable def ptForm (χ : HChar E) (g : GA E a) : Sm E a →ₗ⋆[ℂ] Sm E a →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun φ ψ => starRingEnd ℂ ((mulChi a χ φ).1 g) * (mulChi a χ ψ).1 g)
    (fun φ φ' ψ => by simp only [map_add (f := _), Submodule.coe_add, Pi.add_apply, add_mul])
    (fun c φ ψ => by simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc])
    (fun φ ψ ψ' => by simp only [map_add (f := _), Submodule.coe_add, Pi.add_apply, mul_add])
    (fun c φ ψ => by
      simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring)

private theorem ptForm_apply (χ : HChar E) (g : GA E a) (φ ψ : Sm E a) :
    ptForm χ g φ ψ = starRingEnd ℂ ((mulChi a χ φ).1 g) * (mulChi a χ ψ).1 g := rfl

private theorem pt_tform (χ : HChar E) {d : ℕ} (G : Matrix (Fin d) (Fin d) ℂ) (x y : Sm E a ⊗[ℂ] (Fin d → ℂ)) (g : GA E a) :
    pt χ G x y g = tform (ptForm χ g) G x y := by
  rw [(ptInv E a χ d G x y).1 g, tform_apply]
  rfl

private theorem cmp_rT {W : Type} [AddCommGroup W] [Module ℂ W] {d : ℕ} (S : Module.End ℂ W)
    (y : W ⊗[ℂ] (Fin d → ℂ)) (j : Fin d) :
    cmp j (S.rTensor (Fin d → ℂ) y) = S (cmp j y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul φ v => simp only [LinearMap.rTensor_tmul, cmp_tmul, map_smul]

private theorem sum_val {ι : Type} (s : Finset ι) (f : ι → Sm E a) (g : GA E a) :
    (∑ i ∈ s, f i).1 g = ∑ i ∈ s, (f i).1 g := by
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]

end SlopeTestRemainingChoices

theorem UpperTheory.V.Lit.Geo.Pf.ptDiv :
    UpperTheory.V.Lit.Geo.Pf.PtDiv := by
  intro E _ _ _ a Ξ r χ G hχ hG x y
  choose θ h0 h1 using fun i j => prodEx E a (mulChi a χ (cmp i x)) (mulChi a χ (cmp j y))
  refine ⟨∑ i, ∑ j, G i j • θ i j, fun g => ?_, fun X g => ?_⟩
  · rw [(ptInv E a χ _ G x y).1 g]
    simp only [sum_val, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, h0]
  · set c : ℂ := ((r * ell E a (toL X.1) : ℝ) : ℂ) with hc
    have hcc : starRingEnd ℂ c = c := Complex.conj_ofReal _
    have hX : star X.1 = X.1 := X.2
    have e1 := (UpperTheory.V.Lit.Bor.tformAdj (Sm E a) Ξ.d (ptForm χ g) ⊤ G (Ξ.dmat (toL X.1)) (Ξ.dmat (toL X.1)) 0 0).1
      (by have := hG.adj X.1; rwa [hX] at this) x y
    have e3 : smLie Ξ (toL X.1) y = smA Ξ (toL X.1) y + smB Ξ (toL X.1) y := by
      simp [smB]
    have e4 : smAdj Ξ r (toL X.1) x = smB Ξ (toL X.1) x - smA Ξ (toL X.1) x - (2 * c) • x := by
      rw [smAdj, adj_apply, ← algebraMap_smul ℂ (2 * r * ell E a (toL X.1)) x]
      congr 2
      rw [hc]
      simp [mul_assoc]
    have e5 : (lie E a (toL X.1) (∑ i, ∑ j, G i j • θ i j)).1 g =
        tform (ptForm χ g) G x (smA Ξ (toL X.1) y) + tform (ptForm χ g) G (smA Ξ (toL X.1) x) y +
          2 * c * tform (ptForm χ g) G x y := by

      simp only [map_sum, map_smul, sum_val, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, h1, tform_apply,
      smA_apply, cmp_rT, Finset.mul_sum, ← Finset.sum_add_distrib, ptForm_apply]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hχ.2, hχ.2, ← hc]
      simp only [map_add (f := _), map_smul, Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        map_mul, hcc]
      ring
    rw [e5, pt_tform, pt_tform, e3, e4, smB_apply]
    simp only [map_add (f := _), map_sub, LinearMap.map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, e1,
      map_mul, hcc, map_ofNat]
    ring
end

section

noncomputable section

open ContinuousAlternatingMap

namespace UpperTheory.V.Lit.Geo

private theorem line_der {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {q : ℕ} (p : V) (t : ℝ) (Ω : V × ℝ → (V × ℝ) [⋀^Fin q]→L[ℝ] F) (h : DifferentiableAt ℝ Ω (p, t)) :
    HasDerivAt (fun r => (Ω (p, r)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ))
      ((fderiv ℝ Ω (p, t) (0, 1)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ)) t := by
  have h1 : HasDerivAt (fun r : ℝ => (p, r)) ((0 : V), (1 : ℝ)) t := (hasDerivAt_const t p).prodMk (hasDerivAt_id t)
  have h2 : HasDerivAt (fun r : ℝ => Ω (p, r)) (fderiv ℝ Ω (p, t) (0, 1)) t :=
    HasFDerivAt.comp_hasDerivAt t (l := Ω) h.hasFDerivAt h1
  exact (compContinuousLinearMapCLM (ι := Fin q) (F := F) (ContinuousLinearMap.inl ℝ V ℝ)).hasFDerivAt.comp_hasDerivAt t h2

private theorem hasFDerivAt_slice_of_differentiableAt {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {m : ℕ} (p : V) (t : ℝ) (Ω : V × ℝ → (V × ℝ) [⋀^Fin m]→L[ℝ] F)
    (h : DifferentiableAt ℝ Ω (p, t)) :
    HasFDerivAt (fun x : V => Ω (x, t))
      ((fderiv ℝ Ω (p, t)).comp ((ContinuousLinearMap.id ℝ V).prod 0)) p := by
  have hs : HasFDerivAt (fun x : V => ((x, t) : V × ℝ)) ((ContinuousLinearMap.id ℝ V).prod 0) p :=
    (hasFDerivAt_id p).prodMk (hasFDerivAt_const t p)
  exact h.hasFDerivAt.comp p hs

private theorem fderiv_slice_apply_eq_fderiv_prod_inl {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {m : ℕ} (p : V) (t : ℝ) (Ω : V × ℝ → (V × ℝ) [⋀^Fin m]→L[ℝ] F)
    (h : DifferentiableAt ℝ Ω (p, t)) (c : Fin m → V × ℝ) (u : V) :
    fderiv ℝ (fun x : V => Ω (x, t) c) p u = fderiv ℝ Ω (p, t) (u, 0) c := by
  rw [((hasFDerivAt_slice_of_differentiableAt p t Ω h).continuousAlternatingMap_apply_const c).fderiv]
  simp

private theorem removeNth_succ_vecCons' {α : Type*} {n : ℕ} (a : α) (w : Fin (n + 1) → α) (i : Fin (n + 1)) :
    Fin.removeNth i.succ (Matrix.vecCons a w) = Matrix.vecCons a (Fin.removeNth i w) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp [Fin.removeNth, Fin.succ_succAbove_zero]
  · simp [Fin.removeNth, Fin.succ_succAbove_succ]

theorem prodDer : ProdDer := by
  intro V F _ _ _ _ p t
  refine ⟨fun Ω h => ?_, fun q Ω h => ?_⟩
  · convert line_der p t Ω h using 1
    ext v
    simp [curryLeft_apply_apply, extDeriv_apply h, fderiv_continuousAlternatingMap_apply_const h]
  · have hβ : DifferentiableAt ℝ
        (fun x => ((Ω (x, t)).curryLeft (0, 1)).compContinuousLinearMap (ContinuousLinearMap.inl ℝ V ℝ)) p := by
      have hs := (hasFDerivAt_slice_of_differentiableAt p t Ω h).differentiableAt
      exact ((compContinuousLinearMapCLM (ContinuousLinearMap.inl ℝ V ℝ)).differentiableAt).comp p
        ((((curryLeftLI (𝕜 := ℝ) (E := V × ℝ) (F := F) (n := q)).toContinuousLinearMap.differentiableAt).comp p
          hs).clm_apply (differentiableAt_const _))
    convert line_der p t Ω h using 1
    ext v
    rw [ContinuousAlternatingMap.add_apply, compContinuousLinearMap_apply, curryLeft_apply_apply,
      extDeriv_apply h, Fin.sum_univ_succ, extDeriv_apply hβ]
    have hc : ∀ i : Fin (q + 1), (⇑(ContinuousLinearMap.inl ℝ V ℝ) ∘ Fin.removeNth i v) =
        Fin.removeNth i (⇑(ContinuousLinearMap.inl ℝ V ℝ) ∘ v) := fun i => rfl
    simp only [compContinuousLinearMap_apply, curryLeft_apply_apply, fderiv_slice_apply_eq_fderiv_prod_inl p t Ω h,
      fderiv_continuousAlternatingMap_apply_const h, removeNth_succ_vecCons', hc,
      ContinuousLinearMap.flipAlternating_apply_apply, Matrix.cons_val_succ, Matrix.cons_val_zero,
      Fin.removeNth_zero, Matrix.tail_cons, Fin.tail_cons, Fin.val_succ, Fin.val_zero, pow_zero, one_smul,
      pow_succ, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib, Function.comp_apply,
      ContinuousLinearMap.inl_apply]
    abel

end UpperTheory.V.Lit.Geo
end
end

section

noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

namespace UpperTheory.V.Lit.Geo

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem lie_bound {φ : Sm E a} (h : BddDer φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (X : Lie E a) (g : GA E a), ‖(lie E a X φ).1 g‖ ≤ B * ‖X‖ := by
  let b := Module.finBasis ℝ (Lie E a)
  choose c hc using fun k => h (b k) []
  have hc' : ∀ k g, ‖(lie E a (b k) φ).1 g‖ ≤ c k := fun k g => by simpa using hc k g
  have h0 : ∀ k, 0 ≤ c k := fun k => (norm_nonneg _).trans (hc' k 1)
  refine ⟨∑ k, ‖LinearMap.toContinuousLinearMap (b.coord k)‖ * c k,
    Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (h0 k), fun X g => ?_⟩
  let L : Lie E a →ₗ[ℝ] ℂ :=
    { toFun := fun X => (lie E a X φ).1 g
      map_add' := fun X X' => by rw [map_add (f := _)]; rfl
      map_smul' := fun r X => by rw [map_smul]; rfl }
  have e : L X = ∑ k, b.repr X k • L (b k) := by
    conv_lhs => rw [← b.sum_repr X]

    simp only [map_sum, map_smul]
  change ‖L X‖ ≤ _
  rw [e, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_smul, mul_right_comm]
  exact mul_le_mul ((LinearMap.toContinuousLinearMap (b.coord k)).le_opNorm X) (hc' k g) (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

private theorem val_bound {U : Subgroup (GL (Fin a) (Af E))} {Y : GA E a → Herm E a} {C : ℝ} (h : IsFld U Y C)
    (g : GA E a) : ‖hv (Y g)‖ ≤ a * C ^ 2 + 1 := by
  obtain ⟨x, h1, h2, -⟩ := h.root g 1 (by simp)
  have hC : 0 ≤ C := (norm_nonneg _).trans h2
  have hp : (0 : ℝ) ≤ a * C ^ 2 + 1 := by positivity
  have e : (Y g).1 = x.val * star x.val - 1 := by rw [h1, one_smul, add_sub_cancel_left]
  have hx : ∀ i j, ‖x.val i j‖ ≤ C := fun i j =>
    ((norm_le_pi_norm (toL x.val i) j).trans (norm_le_pi_norm (toL x.val) i)).trans h2
  change ‖toL (Y g).1‖ ≤ _
  refine (pi_norm_le_iff_of_nonneg hp).2 fun i => (pi_norm_le_iff_of_nonneg hp).2 fun j => ?_
  change ‖(Y g).1 i j‖ ≤ _
  rw [e, Matrix.sub_apply, Matrix.mul_apply]
  refine (norm_sub_le _ _).trans (add_le_add ((norm_sum_le _ _).trans ?_) ?_)
  · calc ∑ k, ‖x.val i k * star x.val k j‖ ≤ ∑ _k : Fin a, C ^ 2 := Finset.sum_le_sum fun k _ => by
          refine (norm_mul_le _ _).trans ?_
          rw [Matrix.star_apply, norm_star, sq]
          exact mul_le_mul (hx i k) (hx j k) (norm_nonneg _) hC
      _ = a * C ^ 2 := by simp
  · refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun w => ?_
    rw [Matrix.one_apply]
    split_ifs <;> simp

theorem fieldDer : FieldDer := by
  intro E _ _ _ a U Y C h
  choose φ hφ hb using h.sm
  choose B hB0 hB using fun i j w => lie_bound (hb i j w)
  obtain ⟨P, hP⟩ := LinearMap.exists_leftInverse_of_injective (HV E a).subtype (Submodule.ker_subtype _)
  have hP' : ∀ v : HV E a, LinearMap.toContinuousLinearMap P v.1 = v := fun v => LinearMap.congr_fun hP v
  let B' : Lie E a := fun i j w => (B i j w : ℂ)
  have hle : ∀ i j w, B i j w ≤ ‖B'‖ := fun i j w =>
    calc B i j w ≤ ‖B' i j w‖ := by simpa [B'] using le_abs_self _
      _ ≤ ‖B'‖ := ((norm_le_pi_norm (B' i j) w).trans (norm_le_pi_norm (B' i) j)).trans (norm_le_pi_norm B' i)
  refine ⟨max (a * C ^ 2 + 1) (‖LinearMap.toContinuousLinearMap P‖ * ‖B'‖), le_max_of_le_left (by positivity),
    fun g => ⟨le_max_of_le_left (val_bound h g), fun c X h0 hX => ?_⟩⟩
  let D : Lie E a := fun i j w => (lie E a X (φ i j w)).1 g
  have hD : HasDerivAt (fun t => (hv (Y (g * infGL E a (c t)))).1) D 0 :=
    hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun w =>
      (hasDerivAt_curve (φ i j w) g c X h0 hX).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => (hφ i j w _).symm)
  have hn : ‖D‖ ≤ ‖B'‖ * ‖X‖ := by
    have hp : 0 ≤ ‖B'‖ * ‖X‖ := by positivity
    exact (pi_norm_le_iff_of_nonneg hp).2 fun i => (pi_norm_le_iff_of_nonneg hp).2 fun j =>
      (pi_norm_le_iff_of_nonneg hp).2 fun w =>
        (hB i j w X g).trans (mul_le_mul_of_nonneg_right (hle i j w) (norm_nonneg _))
  refine ⟨LinearMap.toContinuousLinearMap P D, ?_, ?_⟩
  · refine ((LinearMap.toContinuousLinearMap P).le_opNorm_of_le hn).trans ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · exact ((LinearMap.toContinuousLinearMap P).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hD).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => (hP' _).symm)

end UpperTheory.V.Lit.Geo
end
end

section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Geo
open scoped ContDiff Topology

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem cut_chart (Ψ : ℂ → ℂ) (φ : GA E a → ℂ) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (fun h => Ψ (φ h)) g x = Ψ (chart φ g x) := by
  obtain ⟨y, hy⟩ := hx
  obtain rfl : x = toL y.val := hy.symm
  rw [chart_val, chart_val]

private theorem cut_mem {Ψ : ℂ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) (φ : Sm E a) : (fun h => Ψ (φ.1 h)) ∈ Sm E a := fun g =>
  (hΨ.comp_contDiffOn (φ.2 g)).congr fun _ hx => cut_chart Ψ φ.1 g hx

private theorem cut_lie {Ψ : ℂ → ℂ} (hΨ : ContDiff ℝ ∞ Ψ) (φ : Sm E a) (X : Lie E a) (g : GA E a) :
    (lie E a X ⟨_, cut_mem hΨ φ⟩).1 g = fderiv ℝ Ψ (φ.1 g) ((lie E a X φ).1 g) := by
  have hv : chart φ.1 g (oneL E a) = φ.1 g := by simpa using chart_val φ.1 g 1
  rw [← hv]
  change fderiv ℝ (chart (fun h => Ψ (φ.1 h)) g) (oneL E a) X = fderiv ℝ Ψ _ (fderiv ℝ (chart φ.1 g) (oneL E a) X)
  have e : chart (fun h => Ψ (φ.1 h)) g =ᶠ[𝓝 (oneL E a)] Ψ ∘ chart φ.1 g := by
    filter_upwards [isOpen_invSet.mem_nhds (val_mem_invSet (1 : GL (Fin a) (Cinf E)))] with x hx
    exact cut_chart Ψ φ.1 g hx
  rw [e.fderiv_eq, fderiv_comp _ (hΨ.differentiable (by simp) _) (differentiableAt_chart φ.2 g)]
  rfl

private theorem cut_unif (φ : Sm E a) (h : BddDer φ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (X : Lie E a) g, ‖(lie E a X φ).1 g‖ ≤ K * ‖X‖ := by
  obtain ⟨K, hK⟩ := banach_steinhaus (g := fun g : GA E a => fderiv ℝ (chart φ.1 g) (oneL E a)) fun X => by
    obtain ⟨C, hC⟩ := h X []
    refine ⟨C, fun g => ?_⟩
    have := hC g
    rw [List.map_singleton, List.prod_singleton] at this
    exact this
  exact ⟨K, (norm_nonneg _).trans (hK 1), fun X g =>
    ((fderiv ℝ (chart φ.1 g) (oneL E a)).le_opNorm X).trans (mul_le_mul_of_nonneg_right (hK g) (norm_nonneg _))⟩

end SlopeTestRemainingChoices

private theorem cut_lip : ∃ M : NNReal, LipschitzWith M Real.smoothTransition := by
  have hs : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  have hc : HasCompactSupport (deriv Real.smoothTransition) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1)) fun x hx => ?_
    rcases not_and_or.1 hx with h | h
    · have e : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 0 :=
        (eventually_lt_nhds (not_le.1 h)).mono fun y hy => Real.smoothTransition.zero_of_nonpos hy.le
      rw [e.deriv_eq, deriv_const]
    · have e : Real.smoothTransition =ᶠ[𝓝 x] fun _ => 1 :=
        (eventually_gt_nhds (not_le.1 h)).mono fun y hy => Real.smoothTransition.one_of_one_le hy.le
      rw [e.deriv_eq, deriv_const]
  obtain ⟨C, hC⟩ := (hs.continuous_deriv le_rfl).bounded_above_of_compact_support hc
  exact ⟨C.toNNReal, lipschitzWith_of_nnnorm_deriv_le (hs.differentiable (by simp)) fun x => by
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hC x).trans (Real.le_coe_toNNReal C)⟩

private noncomputable def cutRe (R : ℝ) (z : ℂ) : ℝ := Real.smoothTransition (R + 1 - z.re)

private noncomputable def cutFn (R : ℝ) (z : ℂ) : ℂ := cutRe R z

private theorem cutRe_smooth (R : ℝ) : ContDiff ℝ ∞ (cutRe R) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub Complex.reCLM.contDiff)

private theorem cutFn_smooth (R : ℝ) : ContDiff ℝ ∞ (cutFn R) :=
  Complex.ofRealCLM.contDiff.comp (cutRe_smooth R)

private theorem cutFn_der : ∃ M : ℝ, 0 ≤ M ∧ ∀ (R : ℝ) z, ‖fderiv ℝ (cutFn R) z‖ ≤ M := by
  obtain ⟨M, hM⟩ := cut_lip
  refine ⟨M, M.2, fun R z => norm_fderiv_le_of_lip' ℝ M.2 (Filter.Eventually.of_forall fun w => ?_)⟩
  have h1 := hM.dist_le_mul (R + 1 - w.re) (R + 1 - z.re)
  rw [Real.dist_eq, Real.dist_eq] at h1
  have h2 : |R + 1 - w.re - (R + 1 - z.re)| ≤ ‖w - z‖ := by
    rw [show R + 1 - w.re - (R + 1 - z.re) = -(w - z).re by rw [Complex.sub_re]; ring, abs_neg]
    exact Complex.abs_re_le_norm _
  rw [cutFn, cutFn, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 M.2)

private theorem cutFn_flat (R : ℝ) (z : ℂ) (h : cutRe R z = 0 ∨ cutRe R z = 1) : fderiv ℝ (cutFn R) z = 0 := by
  have h0 : fderiv ℝ (cutRe R) z = 0 := by
    rcases h with h | h
    · exact IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun w => by
        rw [h]; exact Real.smoothTransition.nonneg _)
    · exact IsLocalMax.fderiv_eq_zero (Filter.Eventually.of_forall fun w => by
        rw [h]; exact Real.smoothTransition.le_one _)
  have h1 := (Complex.ofRealCLM.hasFDerivAt.comp z
    ((cutRe_smooth R).differentiable (by simp) z).hasFDerivAt).fderiv
  rw [h0, ContinuousLinearMap.comp_zero] at h1
  exact h1

theorem UpperTheory.V.Lit.Geo.stepCut :
    StepCut := by
  intro E _ _ _ a U f Y C c f₀ H
  obtain ⟨φ, hφ, hb⟩ := H.f_sm
  obtain ⟨K, hK0, hK⟩ := cut_unif φ hb
  obtain ⟨M, hM0, hM⟩ := cutFn_der
  have hc : ∀ t g, f (splitCentre E a t * g) = f g := fun t g => by
    have := H.f_left 1 t g
    rwa [map_one, one_mul] at this
  have hl : ∀ γ g, f (ratGL E a γ * g) = f g := fun γ g => by
    have h1 := H.f_left γ 0 ((splitCentre E a 0)⁻¹ * g)
    have h2 := hc 0 ((splitCentre E a 0)⁻¹ * g)
    rw [mul_assoc, mul_inv_cancel_left] at h1
    rw [mul_inv_cancel_left] at h2
    exact h1.trans h2.symm
  refine ⟨M * K, mul_nonneg hM0 hK0, fun R =>
    ⟨⟨_, cut_mem (cutFn_smooth R) φ⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, fun g => ⟨fun X => ?_, fun hg => ?_, fun hg => ?_⟩⟩⟩
  · intro γ g
    simp only [hφ, hl]
  · intro t g
    simp only [hφ, hc]
  · intro k
    refine Subtype.ext (funext fun g => ?_)
    change cutFn R (φ.1 (g * infGL E a (Unitary.toUnits k))) = cutFn R (φ.1 g)
    rw [hφ, hφ, H.f_cpt]
  · intro k hk
    refine Subtype.ext (funext fun g => ?_)
    change cutFn R (φ.1 (g * finGL E a k)) = cutFn R (φ.1 g)
    rw [hφ, hφ, H.f_lev k hk]
  · intro g
    exact ⟨_, Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _, rfl⟩
  · rw [cut_lie (cutFn_smooth R) φ X g, mul_assoc]
    exact ((fderiv ℝ (cutFn R) _).le_opNorm _).trans (mul_le_mul (hM R _) (hK X g) (norm_nonneg _) hM0)
  · have h1 : cutRe R (φ.1 g) = 1 := by
      rw [hφ, cutRe, Complex.ofReal_re, Real.smoothTransition.one_of_one_le (by linarith)]
    refine ⟨?_, fun X => ?_⟩
    · change cutFn R (φ.1 g) = 1
      rw [cutFn, h1, Complex.ofReal_one]
    · rw [cut_lie (cutFn_smooth R) φ X g, cutFn_flat R _ (Or.inr h1)]
      rfl
  · have h1 : cutRe R (φ.1 g) = 0 := by
      rw [hφ, cutRe, Complex.ofReal_re, Real.smoothTransition.zero_of_nonpos (by linarith)]
    refine ⟨?_, fun X => ?_⟩
    · change cutFn R (φ.1 g) = 0
      rw [cutFn, h1, Complex.ofReal_zero]
    · rw [cut_lie (cutFn_smooth R) φ X g, cutFn_flat R _ (Or.inl h1)]
      rfl
end

section

open UpperTheory.V.Lit.Geo

private theorem UpperTheory.V.Lit.Geo.euler_flow {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {W : V → V} {p : V}
    (hd : DifferentiableAt ℝ W p) (hh : ∀ t : ℝ, 0 < t → W (t • p) = t • W p) (t : ℝ) :
    fderiv ℝ (flow W t) p p = flow W t p := by
  have hp1 : HasFDerivAt W (fderiv ℝ W p) ((1 : ℝ) • p) := by
    rw [one_smul]
    exact hd.hasFDerivAt
  have hr : HasDerivAt (fun s : ℝ => s • p) ((1 : ℝ) • p) 1 := (hasDerivAt_id (1 : ℝ)).smul_const p
  have h1 : HasDerivAt (fun s : ℝ => W (s • p)) (fderiv ℝ W p ((1 : ℝ) • p)) 1 :=
    hp1.comp_hasDerivAt (1 : ℝ) hr
  have h2 : HasDerivAt (fun s : ℝ => W (s • p)) (W p) 1 := by
    have hl : HasDerivAt (fun s : ℝ => s • W p) ((1 : ℝ) • W p) 1 := (hasDerivAt_id (1 : ℝ)).smul_const (W p)
    rw [one_smul] at hl
    refine hl.congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (zero_lt_one' ℝ)] with s hs
    exact hh s hs
  have heul : fderiv ℝ W p p = W p := by
    have := h1.unique h2
    rwa [one_smul] at this
  have hf : HasFDerivAt (flow W t) (ContinuousLinearMap.id ℝ V + t • fderiv ℝ W p) p :=
    (hasFDerivAt_id p).add (hd.hasFDerivAt.const_smul t)
  rw [hf.fderiv]
  simp [flow, heul]

theorem UpperTheory.V.Lit.Geo.pbBasic :
    PbBasic := by
  intro V F _ _ _ _ _ _ Y hY W hW hh q
  have hdiff : ∀ p ∈ Y, DifferentiableAt ℝ W p := fun p hp =>
    (hW.1.contDiffAt (hY.mem_nhds hp)).differentiableAt (by simp)
  have he : ∀ p ∈ Y, ∀ t : ℝ, fderiv ℝ (flow W t) p p = flow W t p := fun p hp t =>
    euler_flow (hdiff p hp) (fun s hs => hh s hs p hp) t
  refine ⟨fun w hw => ?_, fun w _ hw => ?_⟩
  · intro p hp v i hi
    rw [pb_apply]
    apply hw (flow W 1 p) (hW.2 p hp 1 ⟨zero_le_one, le_rfl⟩) _ i
    simp [hi, he p hp]
  · intro p hp v i hi
    have hz : ∀ t ∈ Set.Icc (0 : ℝ) 1, hk W t w p v = 0 := by
      intro t ht
      rw [hk_apply]
      apply hw (flow W t p) (hW.2 p hp t ht) _ i.succ
      simp [hi, he p hp]
    show (∫ t in (0 : ℝ)..1, hk W t w p) v = 0
    by_cases hint : IntervalIntegrable (fun t => hk W t w p) MeasureTheory.volume 0 1
    · have hc := (ContinuousAlternatingMap.apply ℝ V F v).intervalIntegral_comp_comm hint
      simp only [ContinuousAlternatingMap.apply_apply] at hc
      rw [← hc, intervalIntegral.integral_congr (g := fun _ => (0 : F))]
      · simp
      · intro t ht
        rw [Set.uIcc_of_le zero_le_one] at ht
        exact hz t ht
    · rw [intervalIntegral.integral_undef hint]
      rfl
end
