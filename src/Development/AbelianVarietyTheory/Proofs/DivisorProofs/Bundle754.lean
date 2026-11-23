module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle149
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle051
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle356
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle712
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle616
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle206
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle005
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.SemidirectProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle714
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle005
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.StarVirtualCharacterEqApplyInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle308
public import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle003
public import ReciprocityTheory.Chebotarev.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle160
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle002

@[expose] public section

section

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.FrameModel

theorem det_append_eq_mul_det : ∀ (C : Type) [Field C] (w : Valuation C NNReal) (ℓ : C), 0 < w ℓ → w ℓ < 1 → ∀ (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (p q : ℕ) (Fil : Submodule w.valuationSubring (S → Fin (p + q) → C)) (τ : S), Function.Injective a → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsFiltration a Fil → ∀ (x : Fin (p + q) → Fin (p + q) → C) (u : Fin p → Fin (p + q) → C) (m : Fin q → Fin (p + q) → C), GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis w x (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) τ) → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis w (fun i => (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ).mkQ (u i)) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.lie (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a (p + q)) Fil) τ) → GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.IsLatticeBasis w m (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenQuot (W := fun _ => Fin (p + q) → C) Fil τ) → ∃ c : C, w c = ∏ s ∈ Finset.univ.erase τ, w ((a τ : C) - (a s : C)) ^ (p + q - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s)) ∧ (Matrix.of (Fin.append u m)).det = c * (Matrix.of x).det := by
  intro C _ w ℓ hℓ0 hℓ1 S _ _ a p q Fil τ ha hFil x u m hx hu hm
  set F := GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil τ with hF
  have hfin : Module.finrank C F = q := by
    have hsp : F = Submodule.span C (Set.range m) := by
      rw [hF, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace, ← hm.2, Submodule.span_span_of_tower]
    rw [hsp, finrank_span_eq_card hm.1, Fintype.card_fin]
  have hd0 : GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun s hs => sub_ne_zero.mpr ?_
    exact ha.ne (Finset.ne_of_mem_erase hs).symm
  have h1 := GlobalTheory.T.latticeDetRelation_herbrand_eigenspace C w ℓ hℓ0 hℓ1 S a p q Fil τ ha hFil hfin
  rw [GlobalTheory.T.piEigenSublattice_free_eq_differentScaled C w S a (p + q) τ ha] at h1
  have h2 := GlobalTheory.T.latticeDetRelation_of_lsmul_shift C w ℓ hℓ0 hℓ1 p q _ _ _ _ _ _ hd0 h1
  obtain ⟨x', u', m', c, hx', hu', hm', hmF, ⟨hc0, hcv⟩, hdet⟩ := h2
  obtain ⟨P, hP, hPdet⟩ := GlobalTheory.DetRelCompare.transition x' x _ hx' hx
  obtain ⟨A, hA, hAdet⟩ := GlobalTheory.DetRelCompare.transition _ _ _ hu' hu
  obtain ⟨B, hB, hBdet⟩ := GlobalTheory.DetRelCompare.transition m' m _ hm' hm
  have hx'0 : (Matrix.of x').det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_row_iff_isUnit.mp hx'.1)).ne_zero
  have happ0 : (Matrix.of (Fin.append u' m')).det ≠ 0 := by
    intro h0
    exact hx'0 (by rw [hdet, h0, mul_zero])
  have hrel := GlobalTheory.DetRelCompare.det_append_eq F u u' m m' A B hA hB hu'.1 hmF happ0
  have hxP : (Matrix.of x).det = P.det * (Matrix.of x').det := by
    have hmat : Matrix.of x = P * Matrix.of x' := by
      ext i k
      simp [Matrix.mul_apply, hP i, Finset.sum_apply]
    rw [hmat, Matrix.det_mul]
  have hP0 : P.det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hPdet
    exact zero_ne_one hPdet
  refine ⟨A.det * B.det * (P.det * c)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_mul, map_inv₀, map_mul, hAdet, hBdet, hPdet, one_mul, one_mul, one_mul]
    have hlam : Real.log (w ℓ : ℝ) ≠ 0 :=
      (Real.log_neg (NNReal.coe_pos.mpr hℓ0) (NNReal.coe_lt_one.mpr hℓ1)).ne
    have hds : ∀ s ∈ Finset.univ.erase τ, ((w ((a τ : C) - (a s : C)) : NNReal) : ℝ) ≠ 0 := by
      intro s hs
      rw [NNReal.coe_ne_zero, Valuation.ne_zero_iff]
      exact sub_ne_zero.mpr (Subtype.coe_injective.ne (ha.ne (Finset.ne_of_mem_erase hs).symm))
    have hdiff : ((GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen a τ : w.valuationSubring) : C)
        = ∏ s ∈ Finset.univ.erase τ, ((a τ : C) - (a s : C)) := by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.diffGen]
    have hle : ∀ s, Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) ≤ p + q := fun s =>
      (Submodule.finrank_le _).trans_eq (Module.finrank_fin_fun C)
    have hlogc : Real.log (w c : ℝ) = - ∑ s ∈ Finset.univ.erase τ,
        ((p + q - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s) : ℕ) : ℝ)
          * Real.log (w ((a τ : C) - (a s : C)) : ℝ) := by
      have e := hcv
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.addVal] at e
      rw [hdiff, map_prod, NNReal.coe_prod, Real.log_prod hds, div_eq_iff hlam] at e
      rw [e, sub_mul, Finset.sum_mul, mul_assoc, div_mul_cancel₀ _ hlam, Finset.mul_sum,
        ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Nat.cast_sub (hle s)]
      field_simp
      ring
    have hwc : 0 < ((w c : NNReal) : ℝ) :=
      NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff w).mpr hc0))
    apply NNReal.coe_injective
    rw [NNReal.coe_inv, NNReal.coe_prod]
    simp only [NNReal.coe_pow]
    have hpos2 : 0 < ∏ s ∈ Finset.univ.erase τ, ((w ((a τ : C) - (a s : C)) : NNReal) : ℝ)
        ^ (p + q - Module.finrank C (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.filSpace Fil s)) :=
      Finset.prod_pos fun s hs => pow_pos (lt_of_le_of_ne (NNReal.coe_nonneg _) (hds s hs).symm) _
    rw [← Real.exp_log (inv_pos.mpr hwc), ← Real.exp_log hpos2, Real.log_inv, hlogc, neg_neg,
      Real.log_prod fun s hs => pow_ne_zero _ (hds s hs)]
    simp only [Real.log_pow]
  · rw [hrel, hxP, hdet]
    field_simp

end GlobalTheory.FrameModel

namespace GlobalTheory.FrameModel

section Small

variable {C : Type} [Field C] (v : Valuation C NNReal) {O : Type} [CommRing O] [Algebra O C]

end Small

end GlobalTheory.FrameModel

end

section

noncomputable section

open NumberField MeasureTheory

namespace GlobalTheory.HeckeMellin

theorem archFactor_mul_pSeries_eq_integral : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ), (∃ i, n i ≠ 0) → ∀ (F : NumberField.RingOfIntegers K → ℂ) (C : ℝ), (∀ α, ‖F α‖ ≤ C) → (∀ (u : (NumberField.RingOfIntegers K)ˣ) (α : NumberField.RingOfIntegers K), F ((u : NumberField.RingOfIntegers K) * α) * GlobalTheory.HeckeStrip.wt φ n (((u : NumberField.RingOfIntegers K) * α : NumberField.RingOfIntegers K) : K) = F α * GlobalTheory.HeckeStrip.wt φ n (α : K)) → ∀ p : (I → ℝ) → ℝ, Measurable p → (∀ y, 0 ≤ p y) → (∀ y, HasSum (fun u : (NumberField.RingOfIntegers K)ˣ => p (y + GlobalTheory.HeckeTheta.ulog φ u)) 1) → ∀ s : ℂ, 1 < s.re → GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.pSeries F φ n s = 2 ^ Fintype.card I * ∫ y, (p y : ℂ) * GlobalTheory.HeckeTheta.theta (fun α : NumberField.RingOfIntegers K => GlobalTheory.HeckeTheta.emb φ (α : K)) F n y * Complex.exp (s * ((∑ i, y i : ℝ) : ℂ)) := by
  intro K _ _ _ I _ φ hφ n hn F C hF hinv p hp hp0 hsum s hs
  haveI : Countable (𝓞 K) := (RingOfIntegers.basis K).equivFun.injective.countable
  haveI : Countable (𝓞 K)ˣ := (Units.val_injective (α := 𝓞 K)).countable
  have hs0 : 0 < s.re := by linarith
  set tm : 𝓞 K → (I → ℝ) → ℂ := fun α => GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) with htm
  have hulog_inv : ∀ u : (𝓞 K)ˣ, GlobalTheory.HeckeTheta.ulog φ u⁻¹ = - GlobalTheory.HeckeTheta.ulog φ u := by
    intro u; funext i
    simp only [GlobalTheory.HeckeTheta.ulog, Pi.neg_apply]
    rw [← Real.log_inv, ← inv_pow, ← norm_inv, ← map_inv₀]
    congr 4
    have h := congrArg (fun x : 𝓞 K => (x : K)) (Units.inv_mul u)
    push_cast at h
    exact eq_inv_of_mul_eq_one_left h
  have hsum' : ∀ y, HasSum (fun u : (𝓞 K)ˣ => p (y - GlobalTheory.HeckeTheta.ulog φ u)) 1 := by
    intro y
    rw [← (Equiv.inv (𝓞 K)ˣ).hasSum_iff]
    simpa [Function.comp_def, hulog_inv, sub_neg_eq_add] using hsum y
  have hp1 : ∀ y, p y ≤ 1 := fun y => by
    have h := le_hasSum (hsum y) 1 (fun u _ => hp0 _)
    have h1 : GlobalTheory.HeckeTheta.ulog φ (1 : (𝓞 K)ˣ) = 0 := by funext i; simp [GlobalTheory.HeckeTheta.ulog]
    simpa [h1] using h
  have hemb0 : GlobalTheory.HeckeTheta.emb φ ((0 : 𝓞 K) : K) = 0 := by funext i; simp [GlobalTheory.HeckeTheta.emb]
  have htm0 : tm 0 = 0 := by funext y; simp only [htm, hemb0, GlobalTheory.HeckeMellin.term_zero hn]; rfl
  have hint : ∀ α : 𝓞 K, Integrable (tm α) := by
    intro α
    by_cases h : α = 0
    · subst h; rw [htm0]; exact integrable_zero _ _ _
    · exact (GlobalTheory.T.heckeMellinGaussIntegral_nonzero_integer K I φ hφ n s hs0 α h).1
  have hshift : ∀ (u : (𝓞 K)ˣ) (α : 𝓞 K) y, tm ((u : 𝓞 K) * α) y =
      GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) * tm α (y + GlobalTheory.HeckeTheta.ulog φ u) := by
    intro u α y
    have : (((u : 𝓞 K) * α : 𝓞 K) : K) = ((u : 𝓞 K) : K) * (α : K) := by push_cast; rfl
    simp only [htm, this]
    exact GlobalTheory.T.heckeMellinGaussIntegrand_unit_mul K I φ hφ n s u α y
  have hwtu : ∀ u : (𝓞 K)ˣ, ‖GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K)‖ = 1 := fun u =>
    GlobalTheory.HeckeStrip.norm_wt φ n (by
      have := u.ne_zero
      exact_mod_cast this)
  have hgen : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) ≠ 0 := by
    intro J h
    haveI := J.2.2
    exact J.2.1 ((Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero J.1).2 h)
  have hspan : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, Ideal.span {(haveI := J.2.2; Submodule.IsPrincipal.generator J.1)} = J.1 := by
    intro J; haveI := J.2.2; exact Ideal.span_singleton_generator J.1

  have horb : ∀ g : 𝓞 K, g ≠ 0 → HasSum (fun u : (𝓞 K)ˣ => ∫ y, p y * ‖tm ((u : 𝓞 K) * g) y‖) (∫ y, ‖tm g y‖) ∧
      HasSum (fun u : (𝓞 K)ˣ => F ((u : 𝓞 K) * g) * ∫ y, (p y : ℂ) * tm ((u : 𝓞 K) * g) y) (F g * ∫ y, tm g y) := by
    intro g hg
    have hO := GlobalTheory.T.orbit_unfold_integral_partition_of_unity I (𝓞 K)ˣ (GlobalTheory.HeckeTheta.ulog φ) p hp hp0 hsum' (tm g) (hint g)
    constructor
    · refine (congrArg (fun f => HasSum f _) (funext fun u => ?_)).mpr hO.2
      simp only [hshift, norm_mul, hwtu, one_mul]
    · refine (congrArg (fun f => HasSum f _) (funext fun u => ?_)).mpr (hO.1.mul_left (F g))
      have hw : F ((u : 𝓞 K) * g) * GlobalTheory.HeckeStrip.wt φ n ((u : 𝓞 K) : K) = F g := by
        have h1 := hinv u g
        have hgK : (g : K) ≠ 0 := by exact_mod_cast hg
        have : (((u : 𝓞 K) * g : 𝓞 K) : K) = ((u : 𝓞 K) : K) * (g : K) := by push_cast; rfl
        rw [this, GlobalTheory.HeckeStrip.wt_mul] at h1
        have hne : GlobalTheory.HeckeStrip.wt φ n (g : K) ≠ 0 := by
          rw [← norm_ne_zero_iff, GlobalTheory.HeckeStrip.norm_wt φ n hgK]; exact one_ne_zero
        exact mul_right_cancel₀ hne (by rw [mul_assoc, h1])
      simp only [hshift]
      rw [← hw, mul_assoc]
      congr 1
      rw [← integral_const_mul]
      congr 1; funext y; ring

  set cst : ℝ := ∏ i, (2 * Real.pi) ^ (-(s.re + (|n i| : ℝ) / 2)) * Real.Gamma (s.re + (|n i| : ℝ) / 2) with hcst
  have hnorm : ∀ J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal}, ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖ = cst * ((Ideal.absNorm J.1 : ℕ) : ℝ) ^ (-s.re) := by
    intro J
    rw [(GlobalTheory.T.heckeMellinGaussIntegral_nonzero_integer K I φ hφ n s hs0 _ (hgen J)).2.2, hspan J]
  have hb : Summable (fun J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal} => ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) := by
    simp only [hnorm]
    exact (((ReciprocityTheory.Cheb.summable_absNorm_rpow_ideal K hs).comp_injective Subtype.val_injective).mul_left cst)
  have hR := GlobalTheory.T.sum_nonzero_integers_principal_ideals_units K ℝ (fun α => ∫ y, p y * ‖tm α y‖) (by simp [htm0])
    (fun J => ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) (fun J u => ∫ y, p y * ‖tm ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1)) y‖)
    (fun J => ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) (fun J => (horb _ (hgen J)).1)
    (fun J u => le_of_eq (Real.norm_of_nonneg (integral_nonneg fun y => mul_nonneg (hp0 y) (norm_nonneg _))))
    (fun J => (horb _ (hgen J)).1) hb
  have hI := GlobalTheory.T.hasSum_integral_theta_mellin_interchange I (𝓞 K) (fun α => GlobalTheory.HeckeTheta.emb φ (α : K)) F C hF n s p hp hp0 hp1 hint hR.summable
  have hU := GlobalTheory.T.sum_nonzero_integers_principal_ideals_units K ℂ (fun α => F α * ∫ y, (p y : ℂ) * tm α y) (by simp [htm0])
    (fun J => F (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) * ∫ y, tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y) (fun J u => C * ∫ y, p y * ‖tm ((u : 𝓞 K) * (haveI := J.2.2; Submodule.IsPrincipal.generator J.1)) y‖)
    (fun J => C * ∫ y, ‖tm (haveI := J.2.2; Submodule.IsPrincipal.generator J.1) y‖) (fun J => (horb _ (hgen J)).2)
    (fun J u => by
      rw [norm_mul]
      refine mul_le_mul (hF _) ((norm_integral_le_integral_norm _).trans (le_of_eq ?_)) (norm_nonneg _)
        ((norm_nonneg _).trans (hF 0))
      congr 1; funext y; rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hp0 y)])
    (fun J => (horb _ (hgen J)).1.mul_left C) (hb.mul_left C)
  rw [hI.unique hU, GlobalTheory.HeckeStrip.pSeries, ← tsum_mul_left, ← tsum_mul_left]
  congr 1; funext J
  have h3 := (GlobalTheory.T.heckeMellinGaussIntegral_nonzero_integer K I φ hφ n s hs0 _ (hgen J)).2.1
  rw [hspan J] at h3
  simp only [GlobalTheory.HeckeStrip.pval]
  linear_combination (-F (haveI := J.2.2; Submodule.IsPrincipal.generator J.1)) * h3

end GlobalTheory.HeckeMellin
end
end

section

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

namespace GlobalTheory.FlagQuotHaar

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def HaarChart (X : Data E r) (c : ℝ≥0∞) : Prop :=
  ∀ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) →
    ∫⁻ g, φ (frameOf X g) ∂haarR X = c * ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X)

def trF {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r) (e : X.Ψ ≃ X'.Ψ)
    (y : Frame X.Ψ r) : Frame X'.Ψ r :=
  fun τ' => (mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ * mat y (e.symm τ') : Matrix (Fin r) (Fin r) ℂ)

end

end GlobalTheory.FlagQuotHaar
end

section

open NumberField
open scoped ContDiff

theorem _root_.GlobalTheory.T.contDiffOn_invSet_of_smooth_along_prod_exp : ∀ (E : Type) [Field E] [NumberField E] (d : ℕ) (f : GlobalTheory.CuspRep.Lie E d → ℂ)
    (S : Set (Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E))), Submodule.span ℝ S = ⊤ →
    (∀ (k : ℕ) (X : Fin k → Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)), (∀ i, X i ∈ S) →
      ∀ y ∈ GlobalTheory.CuspRep.invSet E d, ContDiff ℝ ∞ fun t : Fin k → ℝ =>
        f (GlobalTheory.CuspRep.toL (Matrix.of y * (List.ofFn fun i => NormedSpace.exp (t i • X i)).prod))) →
    ContDiffOn ℝ ∞ f (GlobalTheory.CuspRep.invSet E d) := by
  first | exact @GlobalTheory.SecondKind.contDiffOn_of_prodExp | exact GlobalTheory.SecondKind.contDiffOn_of_prodExp | (intros; apply GlobalTheory.SecondKind.contDiffOn_of_prodExp <;> assumption)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.CliffTwo

def twistRep {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (ν : H →* ℂˣ) : Representation ℂ H V where
  toFun x := ((ν x : ℂˣ) : ℂ) • ρ x
  map_one' := by simp
  map_mul' x y := by rw [map_mul, map_mul, Units.val_mul, smul_mul_smul_comm]

theorem twistRep_apply {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ H V)
    (ν : H →* ℂˣ) (x : H) : twistRep ρ ν x = ((ν x : ℂˣ) : ℂ) • ρ x := rfl

theorem isIrreducible_twistRep {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ H V} (h : ρ.IsIrreducible) (ν : H →* ℂˣ) :
    (twistRep ρ ν).IsIrreducible := by
  let f : Subrepresentation (twistRep ρ ν) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        have := S.toSubmodule.smul_mem (((ν g)⁻¹ : ℂˣ) : ℂ) (S.apply_mem_toSubmodule g hv)
        simpa [twistRep_apply, smul_smul] using this⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv =>
        S.toSubmodule.smul_mem _ (S.apply_mem_toSubmodule g hv)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact f.isSimpleOrder_iff.2 h

theorem isIrrChar_mul_char {H : Type} [Group H] {χ : H → ℂ} (hχ : IsIrrChar ℂ ℂ χ) (ν : H →* ℂˣ) :
    IsIrrChar ℂ ℂ (fun x => χ x * ((ν x : ℂˣ) : ℂ)) := by
  obtain ⟨n, ρ, hρ, hc⟩ := hχ
  refine ⟨n, twistRep ρ ν, isIrreducible_twistRep hρ ν, fun g => ?_⟩
  simp only [hc, Representation.character, twistRep_apply, map_smul, smul_eq_mul,
    Algebra.algebraMap_self, RingHom.id_apply]
  ring

end GlobalTheory.CliffTwo


open GlobalTheory.CliffTwo in
theorem GlobalTheory.Shin.coset_pair_eq_zero_or_twist :
    ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ),
    (Nat.card Γ).Prime → s ≠ 1 → ∀ χ χ' : G ⋊[φ] Γ → ℂ, IsIrrChar ℂ ℂ χ → IsIrrChar ℂ ℂ χ' →
    ∑ᶠ g, χ (inl g * inr s) * star (χ' (inl g * inr s)) = 0 ∨
      ∃ η : G ⋊[φ] Γ →* ℂˣ, (∀ g, η (inl g) = 1) ∧ ∀ x, χ x = χ' x * (η x : ℂ) := by
  intro G Γ _ _ _ _ φ s hp hs χ χ' hχ hχ'
  haveI : Finite (G ⋊[φ] Γ) := Finite.of_equiv _ (SemidirectProduct.equivProd (φ := φ)).symm
  haveI : Fact (Nat.card Γ).Prime := ⟨hp⟩
  have hgen : ∀ t : Γ, t ∈ Subgroup.zpowers s := by
    intro t; rw [zpowers_eq_top_of_prime_card rfl hs]; trivial
  have hζ := Complex.isPrimitiveRoot_exp (Nat.card Γ) hp.ne_zero
  obtain ⟨η, hη1, -, hsum⟩ := GlobalTheory.Shin.CosetFourier.fourier_coset_sums G Γ φ s hgen _ hζ
  have hS := (hsum χ χ').2
  by_cases h0 : ∑ᶠ g, χ (inl g * inr s) * star (χ' (inl g * inr s)) = 0
  · exact Or.inl h0
  right
  have hne : ∑ a ∈ Finset.range (Nat.card Γ), Complex.exp (2 * ↑Real.pi * Complex.I / ↑(Nat.card Γ)) ^ a *
      ∑ᶠ x, χ x * star (χ' x * (η x : ℂ) ^ a) ≠ 0 := by
    rw [← hS]; exact mul_ne_zero (by exact_mod_cast hp.ne_zero) h0
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hT : ∑ᶠ x, χ x * star (χ' x * (η x : ℂ) ^ a) ≠ 0 := right_ne_zero_of_mul ha
  have hpow : ∀ x, ((η ^ a) x : ℂ) = (η x : ℂ) ^ a := fun x => by simp
  have hψ : IsIrrChar ℂ ℂ (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) := isIrrChar_mul_char hχ' (η ^ a)
  refine ⟨η ^ a, fun g => by simp [hη1], fun x => ?_⟩
  by_contra hx
  have hne' : χ ≠ fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ) := fun e => hx (congrFun e x)
  have hpair : pair χ (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) = 0 := by
    first | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne (G ⋊[φ] Γ) χ _ hχ hψ hne' | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne χ _ hχ hψ hne' | exact GlobalTheory.BI.pair_eq_zero_of_isIrrChar_ne hχ hψ hne'
  have hvirt : (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) ∈ Virt ℂ ℂ (G ⋊[φ] Γ) := by
    obtain ⟨n, ρ, -, hc⟩ := hψ
    exact AddSubgroup.subset_closure ⟨n, ρ, hc⟩
  have hstar : ∀ g, star ((fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) g) = (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) g⁻¹ := by
    first | exact GlobalTheory.CuspGL.star_virt_eq_inv (G ⋊[φ] Γ) _ hvirt | exact GlobalTheory.CuspGL.star_virt_eq_inv _ hvirt | exact GlobalTheory.CuspGL.star_virt_eq_inv hvirt
  apply hT
  have hcard : (Nat.card (G ⋊[φ] Γ) : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have : ∑ᶠ x, χ x * star (χ' x * (η x : ℂ) ^ a) =
      ∑ᶠ x, χ x * (fun x => χ' x * (((η ^ a) x : ℂˣ) : ℂ)) x⁻¹ := by
    congr 1; ext x; have hx := hstar x; simp only [hpow] at hx ⊢; rw [← hx]
  rw [this]
  unfold pair at hpair
  exact (mul_eq_zero.1 hpair).resolve_left (inv_ne_zero hcard)
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

theorem _root_.GlobalTheory.T.finsum_semidirect_coset_character_orth_zero : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ X Y : G ⋊[φ] Γ → ℂ, IsChar ℂ ℂ X → IsChar ℂ ℂ Y → ∑ᶠ g, X (inl g) * star (Y (inl g)) = 0 → ∑ᶠ g, X (inl g * inr s) * star (Y (inl g * inr s)) = 0 := by
  first | (exact @GlobalTheory.Shin.finsum_coset_mul_star_eq_zero) | (exact GlobalTheory.Shin.finsum_coset_mul_star_eq_zero) | (intros; apply GlobalTheory.Shin.finsum_coset_mul_star_eq_zero <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH
open scoped CategoryTheory.Obj
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

theorem spMap_fractionRing_specializes (V : Type) [CommRing V] [IsDomain V] (w : Sp V) (p : Sp (FractionRing V)) :
    (spMap (algebraMap V (FractionRing V))) p ⤳ w := by
  refine (PrimeSpectrum.le_iff_specializes (R := V) _ _).1 ?_
  show Ideal.comap (algebraMap V (FractionRing V)) p.asIdeal ≤ w.asIdeal
  have hp : p.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ p.asIdeal (PrimeSpectrum.isPrime p)
  rw [hp]
  intro x hx
  have hx' : algebraMap V (FractionRing V) x = 0 := Ideal.mem_bot.1 (Ideal.mem_comap.1 hx)
  rw [(injective_iff_map_eq_zero _).1 (IsFractionRing.injective V (FractionRing V)) x hx']
  exact w.asIdeal.zero_mem

theorem exists_emb_fractionRing_of_dominant : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ξ : Sp V ⟶ M.Z), (∃ w, ξ w = genericPoint M.Z) → ∃ emb : Ω →+* FractionRing V, ∀ (U : M.Z.Opens) (f : Γ(M.Z, U)), ξ (IsLocalRing.closedPoint V) ∈ U → emb (valF M.pt U f) = algebraMap V (FractionRing V) (valR ξ U f) := by
  intro o Ω _ _ _ M V _ _ _ ξ ⟨w, hw⟩
  set z := ξ (IsLocalRing.closedPoint V) with hzdef
  let g0 : M.O z →+* V :=
    (Scheme.stalkClosedPointTo (R := CommRingCat.of V) ξ).hom.comp (M.stalkEquiv z).symm.toRingHom
  have hg0 : ∀ (U : M.Z.Opens) (f : Γ(M.Z, U)) (hz : z ∈ U),
      g0 ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩ = valR ξ U f := by
    intro U f hz
    have h : ⊤ ≤ ξ ⁻¹ᵁ U := (GlobalTheory.Points.le_preimage_iff ξ U).2 hz
    have e1 : (M.stalkEquiv z).symm ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩ = M.Z.presheaf.germ U z hz f := by
      rw [RingEquiv.symm_apply_eq, RatModel.stalkEquiv_germ]
    have e2 := congrArg (fun φ => φ.hom f) (GlobalTheory.Points.germ_stalkClosedPointTo_eq_valMap ξ U h)
    change (Scheme.stalkClosedPointTo (R := CommRingCat.of V) ξ).hom ((M.stalkEquiv z).symm ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩) = _
    rw [e1]
    rw [GlobalTheory.Points.valR_eq ξ U h]
    exact e2
  have hinj0 : Function.Injective g0 := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨x, hx⟩ h0
    obtain ⟨U, f, hz, rfl⟩ := RatModel.mem_O.1 hx
    rw [hg0 U f hz] at h0
    have hU : (U : Set M.Z).Nonempty := ⟨z, hz⟩
    by_cases hf : f = 0
    · subst hf
      apply Subtype.ext
      show valF M.pt U 0 = 0
      rw [← M.res_apply U hU, map_zero]
    · exfalso
      have hb : M.Z.basicOpen f ≠ ⊥ := fun hb => hf ((basicOpen_eq_bot_iff f).1 hb)
      obtain ⟨y, hy⟩ : ((M.Z.basicOpen f : M.Z.Opens) : Set M.Z).Nonempty := by
        rw [Set.nonempty_iff_ne_empty]
        exact fun h => hb (SetLike.coe_injective h)
      have hgen : genericPoint M.Z ∈ M.Z.basicOpen f :=
        (genericPoint_specializes y).mem_open (M.Z.basicOpen f).isOpen hy
      let eta : Sp (FractionRing V) ⟶ M.Z := spMap (algebraMap V (FractionRing V)) ≫ ξ
      have heta : ⊤ ≤ eta ⁻¹ᵁ M.Z.basicOpen f := by
        intro p _
        have hs : eta p ⤳ genericPoint M.Z := by
          rw [← hw]
          exact (spMap_fractionRing_specializes V w p).map ξ.continuous
        exact hs.mem_open (M.Z.basicOpen f).isOpen hgen
      have hetaU : ⊤ ≤ eta ⁻¹ᵁ U := heta.trans (eta.preimage_mono (M.Z.basicOpen_le f))
      have hu := (GlobalTheory.Points.le_preimage_basicOpen_iff eta hetaU f).1 heta
      rw [GlobalTheory.Points.valR_spMap_comp _ ξ U ((GlobalTheory.Points.le_preimage_iff ξ U).2 hz), h0, map_zero] at hu
      exact not_isUnit_zero hu
  let g : M.O z →+* FractionRing V := (algebraMap V (FractionRing V)).comp g0
  have hinj : Function.Injective g := (IsFractionRing.injective V (FractionRing V)).comp hinj0
  refine ⟨IsFractionRing.lift hinj, fun U f hz => ?_⟩
  have e : valF M.pt U f = algebraMap (M.O z) Ω ⟨valF M.pt U f, RatModel.valF_mem_O hz f⟩ := rfl
  rw [e, IsFractionRing.lift_algebraMap]
  show algebraMap V (FractionRing V) (g0 _) = _
  rw [hg0 U f hz]

end GlobalTheory.ZH.RatModel
end
end
