module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GammaConjAt
public import GroundTheory.AutomorphicForms.MacdonaldFormula
public import GroundTheory.AutomorphicForms.Satake
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Henselian
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
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
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen

private noncomputable def refl {n : ℕ} (z : Fin n → ℂˣ) : Fin n → ℂˣ :=
  fun i => (Units.map (starRingEnd ℂ).toMonoidHom (z i))⁻¹

private noncomputable def star' {n : ℕ} (p : LaurentRing n) : LaurentRing n :=
  p.coeff.sum fun l c => AddMonoidAlgebra.single (-l) ((starRingEnd ℂ) c)

private theorem refl_val {n : ℕ} (z : Fin n → ℂˣ) (i : Fin n) :
    ((refl z i : ℂˣ) : ℂ) = ((starRingEnd ℂ) (z i : ℂ))⁻¹ := by
  simp [refl]

private theorem evalAt_star' {n : ℕ} (p : LaurentRing n) (z : Fin n → ℂˣ) :
    evalAt z (star' p) = (starRingEnd ℂ) (evalAt (refl z) p) := by
  rw [star', map_finsuppSum, evalAt_apply, map_finsuppSum]
  refine Finsupp.sum_congr ?_
  intro l _
  rw [evalAt_single, map_mul, monomialChar_apply, monomialChar_apply, map_prod]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro i _
  simp [refl_val, Units.val_zpow_eq_zpow_val, zpow_neg, map_zpow₀, map_inv₀]

private theorem refl_comp {n : ℕ} (z : Fin n → ℂˣ) (σ : Equiv.Perm (Fin n)) :
    refl (z ∘ σ) = refl z ∘ σ := rfl

private theorem refl_eq {n : ℕ} (z : Fin n → ℂˣ) (hz : ∀ i, ‖(z i : ℂ)‖ = 1) : refl z = z := by
  funext i
  apply Units.ext
  rw [refl_val, Complex.inv_def, Complex.conj_conj, Complex.normSq_conj, Complex.normSq_eq_norm_sq, hz i]
  simp

end UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.starEx_pf :
    UpperTheory.Gal.Gen.StarEx := by
  intro n p hp
  refine ⟨star' p, ?_, fun z hz => ?_⟩
  · intro σ
    refine eq_of_forall_evalAt fun z => ?_
    rw [evalAt_permAct, evalAt_star', evalAt_star', refl_comp, ← evalAt_permAct, hp σ]
  · rw [evalAt_star', refl_eq z hz]
end

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma pt_coe {n : ℕ} (θ : Fin n → UnitAddCircle) (i : Fin n) :
    ((pt θ i : ℂˣ) : ℂ) = ((AddCircle.toCircle (θ i) : Circle) : ℂ) := rfl

private lemma eval_cons_pt {n : ℕ} (s : UnitAddCircle) (θ : Fin n → UnitAddCircle)
    (p : MvPolynomial (Fin (n + 1)) ℂ) :
    MvPolynomial.eval (fun i => (pt (Fin.cons s θ : Fin (n + 1) → UnitAddCircle) i : ℂ)) p =
      Polynomial.eval ((AddCircle.toCircle s : Circle) : ℂ)
        (Polynomial.map (MvPolynomial.eval (fun i => (pt θ i : ℂ))) (MvPolynomial.finSuccEquiv ℂ n p)) := by
  rw [← MvPolynomial.eval_eq_eval_mv_eval']
  have h : (fun i => (pt (Fin.cons s θ : Fin (n + 1) → UnitAddCircle) i : ℂ)) =
      (Fin.cons ((AddCircle.toCircle s : Circle) : ℂ) (fun i => (pt θ i : ℂ)) : Fin (n + 1) → ℂ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [pt_coe]
  rw [h]

private lemma continuous_eval_pt {n : ℕ} (p : MvPolynomial (Fin n) ℂ) :
    Continuous fun θ : Fin n → UnitAddCircle => MvPolynomial.eval (fun i => (pt θ i : ℂ)) p := by
  have h1 : Continuous fun x : Fin n → ℂ => MvPolynomial.eval x p := MvPolynomial.continuous_eval p
  have h2 : Continuous fun θ : Fin n → UnitAddCircle => (fun i => (pt θ i : ℂ)) := by
    refine continuous_pi fun i => ?_
    simp only [pt_coe]
    exact continuous_subtype_val.comp ((AddCircle.continuous_toCircle).comp (continuous_apply i))
  exact h1.comp h2

private lemma circle_zero_null (r : Polynomial ℂ) (hr : r ≠ 0) :
    volume {s : UnitAddCircle | r.eval ((AddCircle.toCircle s : Circle) : ℂ) = 0} = 0 := by
  haveI : NullSingletonClass (volume : Measure UnitAddCircle) := ⟨fun x => by
    have h := AddCircle.volume_closedBall (T := (1 : ℝ)) (x := x) 0
    simpa using h⟩
  have hinj : Function.Injective fun s : UnitAddCircle => ((AddCircle.toCircle s : Circle) : ℂ) :=
    Circle.coe_injective.comp (AddCircle.injective_toCircle one_ne_zero)
  have hfin : ({s : UnitAddCircle | r.eval ((AddCircle.toCircle s : Circle) : ℂ) = 0}).Finite := by
    refine Set.Finite.of_finite_image (f := fun s : UnitAddCircle => ((AddCircle.toCircle s : Circle) : ℂ)) ?_ hinj.injOn
    refine (Polynomial.finite_setOf_isRoot hr).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    exact hs
  exact hfin.measure_zero _

theorem UpperTheory.Gal.Gen.nullZero_pf :
    UpperTheory.Gal.Gen.NullZero := by
  intro n
  induction n with
  | zero =>
    intro p hp
    obtain ⟨a, rfl⟩ : ∃ a, p = MvPolynomial.C a := ⟨_, MvPolynomial.eq_C_of_isEmpty p⟩
    have ha : a ≠ 0 := by
      rintro rfl
      simp at hp
    refine Filter.Eventually.of_forall fun θ => ?_
    simpa using ha
  | succ n ih =>
    intro p hp
    have hq : MvPolynomial.finSuccEquiv ℂ n p ≠ 0 := by
      simpa using hp
    have hc := ih (MvPolynomial.finSuccEquiv ℂ n p).leadingCoeff (Polynomial.leadingCoeff_ne_zero.mpr hq)
    have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) 0
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => UnitAddCircle) 0 with he
    have hclosed : IsClosed {θ : Fin (n + 1) → UnitAddCircle |
        MvPolynomial.eval (fun i => (pt θ i : ℂ)) p = 0} :=
      isClosed_eq (continuous_eval_pt p) continuous_const
    have hm : MeasurableSet {z : UnitAddCircle × (Fin n → UnitAddCircle) |
        MvPolynomial.eval (fun i => (pt (e.symm z) i : ℂ)) p ≠ 0} :=
      e.symm.measurable hclosed.measurableSet.compl
    have hsymm : ∀ (s : UnitAddCircle) (θ : Fin n → UnitAddCircle),
        e.symm (s, θ) = (Fin.cons s θ : Fin (n + 1) → UnitAddCircle) := by
      intro s θ
      simp [he, MeasurableEquiv.piFinSuccAbove, Fin.insertNth_zero']
    have hprod : ∀ᵐ z ∂(volume.prod volume : Measure (UnitAddCircle × (Fin n → UnitAddCircle))),
        MvPolynomial.eval (fun i => (pt (e.symm z) i : ℂ)) p ≠ 0 := by
      refine (Measure.ae_prod_iff_ae_ae hm).2 ?_
      refine (Measure.ae_ae_comm hm).2 ?_
      filter_upwards [hc] with θ' hθ'
      have hr : Polynomial.map (MvPolynomial.eval (fun i => (pt θ' i : ℂ)))
          (MvPolynomial.finSuccEquiv ℂ n p) ≠ 0 := by
        intro h
        apply hθ'
        rw [Polynomial.leadingCoeff, ← Polynomial.coeff_map, h, Polynomial.coeff_zero]
      refine ae_iff.2 (measure_mono_null ?_ (circle_zero_null _ hr))
      intro s hs
      have hs' : MvPolynomial.eval (fun i => (pt (e.symm (s, θ')) i : ℂ)) p = 0 := by
        by_contra h
        exact hs h
      rw [hsymm, eval_cons_pt] at hs'
      exact hs'
    have := hmp.quasiMeasurePreserving.ae hprod
    filter_upwards [this] with θ hθ
    rw [e.symm_apply_apply] at hθ
    exact hθ
end

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private lemma pt_val {n : ℕ} (θ : Fin n → UnitAddCircle) (i : Fin n) :
    ((pt θ i : ℂˣ) : ℂ) = ((AddCircle.toCircle (θ i) : Circle) : ℂ) := rfl

private lemma pt_cont {n : ℕ} (i : Fin n) :
    Continuous fun θ : Fin n → UnitAddCircle => ((pt θ i : ℂˣ) : ℂ) := by
  simp only [pt_val]
  fun_prop

private lemma pt_norm {n : ℕ} (θ : Fin n → UnitAddCircle) (i : Fin n) :
    ‖((pt θ i : ℂˣ) : ℂ)‖ = 1 := by
  rw [pt_val]
  exact Circle.norm_coe _

private lemma half_cont {X : Type*} [TopologicalSpace X] {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {n : ℕ}
    (u : X → Fin n → ℂˣ) (hc : ∀ i, Continuous fun x => ((u x i : ℂˣ) : ℂ))
    (hn : ∀ x i, ‖((u x i : ℂˣ) : ℂ)‖ = 1) :
    Continuous fun x => half (t : ℂ) (u x) := by
  unfold half
  refine continuous_finsetProd _ (fun p _ => ?_)
  have h1 := hc p.1
  have h2 := hc p.2
  have hne : ∀ x, ((u x p.2 : ℂˣ) : ℂ) ≠ 0 := fun x => Units.ne_zero _
  have hq : Continuous fun x => ((u x p.1 : ℂˣ) : ℂ) / ((u x p.2 : ℂˣ) : ℂ) := h1.div h2 hne
  refine (continuous_const.sub hq).div (continuous_const.sub (continuous_const.mul hq)) (fun x => ?_)
  intro h
  have hnq : ‖((u x p.1 : ℂˣ) : ℂ) / ((u x p.2 : ℂˣ) : ℂ)‖ = 1 := by
    rw [norm_div, hn, hn, div_one]
  have h' := congrArg norm (sub_eq_zero.mp h).symm
  rw [norm_one, norm_mul, hnq, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] at h'
  linarith

theorem UpperTheory.Gal.Gen.densCont_pf :
    UpperTheory.Gal.Gen.DensCont := by
  intro n t ht0 ht1
  have hinvc : ∀ i, Continuous fun θ : Fin n → UnitAddCircle => (((pt θ)⁻¹ i : ℂˣ) : ℂ) := by
    intro i
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val]
    exact (pt_cont i).inv₀ (fun θ => Units.ne_zero _)
  have hinvn : ∀ (θ : Fin n → UnitAddCircle) i, ‖(((pt θ)⁻¹ i : ℂˣ) : ℂ)‖ = 1 := by
    intro θ i
    simp only [Pi.inv_apply, Units.val_inv_eq_inv_val, norm_inv, pt_norm, inv_one]
  refine ⟨half_cont ht0 ht1 _ pt_cont pt_norm, ?_, ?_, pt_norm⟩
  · exact (half_cont ht0 ht1 _ pt_cont pt_norm).mul (half_cont ht0 ht1 _ hinvc hinvn)
  · intro p
    simp only [evalAt_apply, monomialChar_apply, Units.val_zpow_eq_zpow_val]
    unfold Finsupp.sum
    refine continuous_finsetSum _ (fun l _ => ?_)
    refine continuous_const.mul (continuous_finsetProd _ (fun i _ => ?_))
    exact (pt_cont i).zpow₀ _ (fun θ => Or.inl (Units.ne_zero _))
end

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem qInv_props (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] : 0 ≤ ((qF F : ℝ))⁻¹ ∧ ((qF F : ℝ))⁻¹ < 1 := by
  have h : 1 < qF F := by
    haveI := fintypeResidue' (F := F)
    exact Finite.one_lt_card
  have h' : (1 : ℝ) < (qF F : ℝ) := by exact_mod_cast h
  exact ⟨by positivity, inv_lt_one_of_one_lt₀ h'⟩

theorem UpperTheory.Gal.Gen.gammaInt_pf :
    UpperTheory.Gal.Gen.RInt → UpperTheory.Gal.Gen.DensCont → UpperTheory.Gal.Gen.GammaInt := by
  intro hR hD F _ _ _ _ n _ _ μ _ g
  obtain ⟨ht0, ht1⟩ := qInv_props F
  have htc : (((((qF F : ℝ))⁻¹ : ℝ)) : ℂ) = ((qF F : ℂ))⁻¹ := by push_cast; rfl
  have hv : vPoly n ((qF F : ℂ))⁻¹ ≠ 0 := vPoly_ne_zero injective_qInv_pow n
  have hint := hR n _ ht0 ht1
  have hcont := (hD n _ ht0 ht1).2.2.1
  rw [htc] at hint
  obtain ⟨l, hl, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
  have hdt : Cartan.diagPow F n l = Iwasawa.torusPow F n l := by
    apply Units.ext
    rw [Cartan.coe_diagPow, Iwasawa.coe_torusPow]
  have hΓ : ∀ z : Fin n → ℂˣ, zonalSpherical μ z (k₁ * Cartan.diagPow F n l * k₂) =
      (vPoly n ((qF F : ℂ))⁻¹)⁻¹ * (halfModulus F l * evalAt z (hlR ((qF F : ℂ))⁻¹ l)) := by
    intro z
    rw [zonalSpherical_mul_right z _ hk₂, zonalSpherical_mul_left z hk₁, hdt,
      eq_inv_mul_iff_mul_eq₀ hv]
    exact macdonald_formula_hlR z hl
  refine ⟨?_, ?_⟩
  · simp only [hΓ]
    exact continuous_const.mul (continuous_const.mul (hcont _))
  · have hI : ∫ θ : Fin n → UnitAddCircle,
        zonalSpherical μ (pt θ) (k₁ * Cartan.diagPow F n l * k₂) * dens ((qF F : ℂ))⁻¹ (pt θ) =
        (vPoly n ((qF F : ℂ))⁻¹)⁻¹ * halfModulus F l *
          ∫ θ : Fin n → UnitAddCircle, evalAt (pt θ) (hlR ((qF F : ℂ))⁻¹ l) * dens ((qF F : ℂ))⁻¹ (pt θ) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp only [hΓ]
      ring
    rw [hI, hint l hl, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    have hdom0 : Cartan.IsDominant (0 : Fin n → ℤ) := fun _ _ _ => le_rfl
    have hd0 : Cartan.diagPow F n 0 = 1 := by
      apply Units.ext
      rw [Cartan.coe_diagPow]
      simp
    by_cases h0 : l = 0
    · subst h0
      rw [if_pos rfl, halfModulus_zero, one_mul, if_pos]
      rw [hd0, mul_one]
      exact mul_mem hk₁ hk₂
    · rw [if_neg h0, mul_zero, if_neg]
      intro hg
      have hk : k₁⁻¹ * (k₁ * Cartan.diagPow F n l * k₂) * k₂⁻¹ ∈ GLnLocal.integralGL F n :=
        mul_mem (mul_mem (inv_mem hk₁) hg) (inv_mem hk₂)
      refine h0 (Cartan.eq_of_mul_diagPow_eq F n hdom0 hl hk (one_mem _) ?_).symm
      rw [hd0]
      group
end

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

private theorem rhoPair_dual {n : ℕ} (l : Fin n → ℤ) :
    rhoPair (fun i => -l (Fin.rev i)) = rhoPair l := by
  unfold rhoPair
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
  simp only [Fin.revPerm_apply, Fin.val_rev]
  rw [Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ n)]
  push_cast
  ring

private theorem conj_vPoly (n : ℕ) (t : ℝ) :
    (starRingEnd ℂ) (vPoly n (t : ℂ)) = vPoly n (t : ℂ) := by
  unfold vPoly
  simp [map_prod, map_div₀]


theorem UpperTheory.Gal.Gen.gammaConj_pf :
    UpperTheory.Gal.Gen.RConj → UpperTheory.Gal.Gen.GammaConj := by
  intro hR F _ _ _ _ n _ _ μ _
  show ∀ z, _
  intro z hinj hz g
  obtain ⟨l, hl, k₁, hk₁, k₂, hk₂, rfl⟩ := Cartan.exists_eq_mul_diagPow_mul F n g
  have htp : Cartan.diagPow F n l = Iwasawa.torusPow F n l := by
    apply Units.ext
    rw [Cartan.coe_diagPow, Iwasawa.coe_torusPow]
  have hl' : Antitone (fun i : Fin n => -l (Fin.rev i)) := by
    intro i j hij
    show -l (Fin.rev j) ≤ -l (Fin.rev i)
    exact neg_le_neg (hl (Fin.rev_le_rev.mpr hij))
  have hinv : (k₁ * Cartan.diagPow F n l * k₂)⁻¹ =
      k₂⁻¹ * Iwasawa.torusPow F n (-l) * k₁⁻¹ := by
    rw [Iwasawa.torusPow_neg, ← htp]
    group
  have hcomp : Iwasawa.torusPow F n (fun i : Fin n => -l (Fin.rev i)) =
      Iwasawa.torusPow F n ((-l) ∘ Fin.revPerm) := rfl
  have hZinv : zonalSpherical μ z (k₁ * Cartan.diagPow F n l * k₂)⁻¹ =
      zonalSpherical μ z (Iwasawa.torusPow F n (fun i : Fin n => -l (Fin.rev i))) := by
    rw [hinv, zonalSpherical_mul_right z _ (inv_mem hk₁), zonalSpherical_mul_left z (inv_mem hk₂),
      hcomp, zonalSpherical_torusPow_comp]
  have hZ : zonalSpherical μ z (k₁ * Cartan.diagPow F n l * k₂) =
      zonalSpherical μ z (Iwasawa.torusPow F n l) := by
    rw [zonalSpherical_mul_right z _ hk₂, zonalSpherical_mul_left z hk₁, htp]
  rw [hZinv, hZ]
  have hv : vPoly n ((qF F : ℂ))⁻¹ ≠ 0 := vPoly_ne_zero injective_qInv_pow n
  have hcast : (((qF F : ℝ)⁻¹ : ℝ) : ℂ) = ((qF F : ℂ))⁻¹ := by simp
  have m1 := macdonald_formula_hlR (μ := μ) z hl'
  have m2 := macdonald_formula_hlR (μ := μ) z hl
  have hc := hR n ((qF F : ℝ))⁻¹ l z hinj hz
  rw [hcast] at hc
  have hhm : halfModulus F (fun i : Fin n => -l (Fin.rev i)) = halfModulus F l := by
    rw [halfModulus_eq, halfModulus_eq, rhoPair_dual]
  have hhmr : (starRingEnd ℂ) (halfModulus F l) = halfModulus F l := by
    rw [halfModulus_eq, map_zpow₀]
    simp [sqrtQ]
  have hvr : (starRingEnd ℂ) (vPoly n ((qF F : ℂ))⁻¹) = vPoly n ((qF F : ℂ))⁻¹ := by
    rw [← hcast]
    exact conj_vPoly n _
  apply mul_left_cancel₀ hv
  rw [m1, hhm, hc]
  have m2c := congrArg (starRingEnd ℂ) m2
  rw [map_mul, map_mul, hvr, hhmr] at m2c
  rw [m2c]
end

section

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.symEx_pf :
    UpperTheory.Gal.Gen.SymEx := by
  intro n Φ
  refine ⟨polyEmb (n := n) (∏ σ : Equiv.Perm (Fin n), MvPolynomial.rename σ Φ), ?_, ?_, ?_⟩
  · show ∀ τ : Equiv.Perm (Fin n), permAct τ _ = _
    intro τ
    rw [← polyEmb_rename]
    congr 1
    rw [map_prod]
    simp_rw [MvPolynomial.rename_rename]
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)
  · intro z
    rw [evalAt_polyEmb, map_prod]
    refine Finset.prod_congr rfl (fun σ _ => ?_)
    rw [MvPolynomial.aeval_rename]
    rfl
  · intro hΦ
    refine ⟨∏ σ : Equiv.Perm (Fin n), MvPolynomial.rename σ Φ, ?_, fun z => ?_⟩
    · rw [Finset.prod_ne_zero_iff]
      intro σ _ h
      apply hΦ
      exact MvPolynomial.rename_injective _ σ.injective (by rw [h, map_zero])
    · rw [evalAt_polyEmb]
      rfl
end
