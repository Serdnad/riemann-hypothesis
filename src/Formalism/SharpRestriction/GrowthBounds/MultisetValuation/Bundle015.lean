module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle006
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle012
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle009
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle013
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle007
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle010
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle001
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.SubstitutionOfVariables
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LocalComponentGL
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

section IntRL

variable {ι K : Type} [Field K] {R : Subring K}

theorem en_IntR_mul {f g : MvPowerSeries ι K} (hf : IntR R f) (hg : IntR R g) : IntR R (f * g) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_mul]
  exact R.sum_mem fun x _ => R.mul_mem (hf _) (hg _)

theorem en_IntR_one : IntR R (1 : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_one]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

theorem en_IntR_X (i : ι) : IntR R (MvPowerSeries.X i : MvPowerSeries ι K) := by
  classical
  intro n
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact R.one_mem
  · exact R.zero_mem

theorem en_IntR_pow {f : MvPowerSeries ι K} (hf : IntR R f) (k : ℕ) : IntR R (f ^ k) := by
  induction k with
  | zero => rw [pow_zero]; exact en_IntR_one
  | succ k ih => rw [pow_succ]; exact en_IntR_mul ih hf

theorem en_IntR_prod {α : Type} (s : Finset α) (f : α → MvPowerSeries ι K) (h : ∀ a ∈ s, IntR R (f a)) :
    IntR R (∏ a ∈ s, f a) :=
  Finset.prod_induction f (IntR R) (fun _ _ => en_IntR_mul) en_IntR_one h

end IntRL

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

theorem en_places_add (j : ℕ) (i0 : X.Pl → ℕ) (gP : X.Pl → ℚ) (hLow : ∀ v, LowAtI X Y j v (i0 v) (gP v))
    (U1 : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc) (hU1 : IntR Y.Oc (inParamK p Y.Kc U1)) (I : X.ColCh j) :
    geP Y (applyD (X.PI j I i0) (X.ThZA Y.Kc j ((∏ v, en_F X Y j v) * U1))) ((∑ v, gP v : ℚ) : ℝ) := by
  classical
  have e1 : X.ThZA Y.Kc j ((∏ v, en_F X Y j v) * U1) = (∏ v, X.ThZA Y.Kc j (en_F X Y j v)) *
      MvPowerSeries.subst (fun i => X.ThZA Y.Kc j (en_Ec p Y.Kc i)) (inParamK p Y.Kc U1) := by
    rw [en_ThZA_mul, en_ThZA_prod]
    congr 1
    conv_lhs => rw [← en_Ec_inParamK p Y.Kc U1]
    unfold Sys.ThZA
    rw [MvPowerSeries.subst_comp_subst_apply (en_Ec_hs p Y.Kc) (en_coordZA_hs X Y.Kc j)]
  have ha : MvPowerSeries.HasSubst (fun i => X.ThZA Y.Kc j (en_Ec p Y.Kc i)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun i =>
      MvPowerSeries.constantCoeff_subst_eq_zero (en_coordZA_hs X Y.Kc j) (en_coordZA_zero X Y.Kc j)
        (en_Ec_zero p Y.Kc i)
  rw [en_applyD_eq, e1]
  obtain ⟨B, hB⟩ := Gen.jp_subst_expand (en_mapP Y.Kc (X.ZA j) (X.FrI j) (X.PI j I i0))
    (∏ v, X.ThZA Y.Kc j (en_F X Y j v)) (fun i => X.ThZA Y.Kc j (en_Ec p Y.Kc i)) ha (inParamK p Y.Kc U1)
  rw [hB]
  refine valuation_coeff_ge_sum Y _ _ _ fun β _ => valuation_coeff_ge_smul Y (hU1 β) ?_
  set Ub : X.Pl → MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc := fun v =>
    ∏ i ∈ β.support.filter (fun i => en_pi X j i = v), (en_Ec p Y.Kc i) ^ (β i) with hUb
  have e2 : (β.prod fun i e => X.ThZA Y.Kc j (en_Ec p Y.Kc i) ^ e) = ∏ v, X.ThZA Y.Kc j (Ub v) := by
    unfold Finsupp.prod
    rw [← Finset.prod_fiberwise β.support (en_pi X j)]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hUb, en_ThZA_prod]
    exact Finset.prod_congr rfl fun i _ => (en_ThZA_pow X Y.Kc j _ _).symm
  have e3 : (∏ v, X.ThZA Y.Kc j (en_F X Y j v)) * ∏ v, X.ThZA Y.Kc j (Ub v) =
      ∏ v, X.ThZA Y.Kc j (en_F X Y j v * Ub v) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun v _ => (en_ThZA_mul X Y.Kc j _ _).symm
  have hG : ∀ v, X.ThZA Y.Kc j (en_F X Y j v * Ub v) ∈ Gen.SuppOn (Sigma.fst : X.ZA j → X.Pl) v := fun v =>
    en_ThZA_supp X Y.Kc j v (Subring.mul_mem _ (en_F_supp X Y j v) (Subring.prod_mem _ fun i hi =>
      Subring.pow_mem _ (by
        have := en_Ec_supp p Y.Kc (en_pi X j) i
        rw [(Finset.mem_filter.1 hi).2] at this
        exact this) _))
  have e4 : ∏ v, X.ThZA Y.Kc j (en_F X Y j v * Ub v) =
      ∏ v, Gen.atP v (Gen.resP v (X.ThZA Y.Kc j (en_F X Y j v * Ub v))) :=
    Finset.prod_congr rfl fun v _ => Gen.eq_atP v _ (hG v)
  have e5 : en_mapP Y.Kc (X.ZA j) (X.FrI j) (X.PI j I i0) =
      ∏ v, MvPolynomial.rename (Sigma.mk v) (en_Ploc X Y j I i0 v) := by
    rw [PI_eq_prod, map_prod]
    exact Finset.prod_congr rfl fun v _ => en_mapP_PIvS X Y j I i0 v
  rw [e2, e3, e4, e5, Gen.jp_prod]
  refine valuation_coeff_ge_prod_rat Y _ _ _ fun v _ => ?_
  have e6 : Gen.jp (en_Ploc X Y j I i0 v) (Gen.resP v (X.ThZA Y.Kc j (en_F X Y j v * Ub v))) =
      applyD (PIvS X j I (fun _ => i0 v) v) (X.ThZA Y.Kc j (en_F X Y j v * Ub v)) := by
    rw [en_applyD_eq, ← PIvS_congr, en_mapP_PIvS]
    conv_rhs => rw [Gen.eq_atP v _ (hG v)]
    rw [Gen.jp_rename]
  rw [e6]
  have hint : IntR Y.Oc (inParamK p Y.Kc (Ub v)) := by
    rw [hUb, en_inParamK_prod]
    refine en_IntR_prod _ _ fun i _ => ?_
    rw [en_inParamK_pow, en_inParamK_Ec]
    exact en_IntR_pow (en_IntR_X i) _
  exact fun n => hLow v (Ub v) hint I n

def KernelProductForm (D : Formalism.BasicNotions.D7) : Prop :=
  admitted D X Y → ∀ j < X.mm, ∀ (La : X.Lt j) (La' : X.Lt (j + 1)), (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 →
    ∀ (φ : Y.Frm j La La'), ∃ U1 : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc, IntR Y.Oc (inParamK p Y.Kc U1) ∧
      Y.ThA j La La' φ = (∏ v, en_F X Y j v) * U1

variable {X Y}

theorem restPlaces_of (D : Formalism.BasicNotions.D7) (h : KernelProductForm X Y D) : RestPlaces X Y D := by
  intro hA j hj i0 gP hLow La La' h1 h2 φ I n
  obtain ⟨U1, hU1, e⟩ := h hA j hj La La' h1 h2 φ
  rw [e]
  have := en_places_add X Y j i0 gP hLow U1 hU1 I n
  push_cast at this
  exact this

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF Gser)

attribute [local instance] Formalism.InvariantFactorPaths.G7.WModel.nf sx_charZero

variable (p : ℕ) [hp : Fact p.Prime]

theorem sx_logF_eq : logF p = lgF (K0 p) p := by
  ext n
  simp only [logF, lgF, PowerSeries.coeff_mk, pow_mul]

theorem sx_logF_const : PowerSeries.constantCoeff (logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [logF, PowerSeries.coeff_mk]

def sx_lX {σ : Type} (i : σ) : MvPowerSeries σ (K0 p) :=
  PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) (logF p)

private theorem constantCoeff_subst_X_logF_eq_zero {σ : Type} (i : σ) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) (logF p)) = 0 := by
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [sx_logF_const]
  · simp [MvPowerSeries.constantCoeff_X, zero_pow hd.ne']

private theorem hs_lemma_2 {σ : Type} [Finite σ] :
    MvPowerSeries.HasSubst (fun i : σ => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ (K0 p)) (logF p)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => constantCoeff_subst_X_logF_eq_zero p i)

theorem sx_inParam_X {σ : Type} [Finite σ] (i : σ) : inParam p (MvPowerSeries.X i) = sx_lX p i := by
  unfold inParam sx_lX
  exact MvPowerSeries.subst_X (hs_lemma_2 p) i

theorem sx_inParam_add {σ : Type} [Finite σ] (f g : MvPowerSeries σ (K0 p)) :
    inParam p (f + g) = inParam p f + inParam p g := by
  unfold inParam
  exact MvPowerSeries.subst_add (hs_lemma_2 p) f g

theorem sx_inParam_mul {σ : Type} [Finite σ] (f g : MvPowerSeries σ (K0 p)) :
    inParam p (f * g) = inParam p f * inParam p g := by
  unfold inParam
  exact MvPowerSeries.subst_mul (hs_lemma_2 p) f g

theorem sx_inParam_C_mul {σ : Type} [Finite σ] (a : K0 p) (g : MvPowerSeries σ (K0 p)) :
    inParam p (MvPowerSeries.C a * g) = MvPowerSeries.C a * inParam p g := by
  unfold inParam
  rw [MvPowerSeries.subst_mul (hs_lemma_2 p), MvPowerSeries.subst_C]

theorem sx_subst_ps {σ τ : Type} {a : σ → MvPowerSeries τ (K0 p)} (ha : MvPowerSeries.HasSubst a)
    {g : MvPowerSeries σ (K0 p)} (hg : MvPowerSeries.constantCoeff g = 0) (f : PowerSeries (K0 p)) :
    MvPowerSeries.subst a (PowerSeries.subst g f) = PowerSeries.subst (MvPowerSeries.subst a g) f :=
  MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hg).const ha f

theorem sx_inParam_subst {σ τ : Type} [Finite σ] [Finite τ] (a a' : σ → MvPowerSeries τ (K0 p))
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (ha' : ∀ i, MvPowerSeries.constantCoeff (a' i) = 0)
    (h : ∀ i, PowerSeries.subst (a' i) (logF p) = inParam p (a i)) (f : MvPowerSeries σ (K0 p)) :
    inParam p (MvPowerSeries.subst a f) = MvPowerSeries.subst a' (inParam p f) := by
  have hA : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  have hA' : MvPowerSeries.HasSubst a' := MvPowerSeries.hasSubst_of_constantCoeff_zero ha'
  unfold inParam
  rw [MvPowerSeries.subst_comp_subst_apply hA (hs_lemma_2 p), MvPowerSeries.subst_comp_subst_apply (hs_lemma_2 p) hA']
  congr 1
  funext s
  rw [sx_subst_ps p hA' (by simp) (logF p), MvPowerSeries.subst_X hA']
  exact (h s).symm

theorem sx_simeq_of {σ : Type} [Finite σ] {f g : MvPowerSeries σ (K0 p)} (h : Simeq p f g) :
    Formalism.InvariantFactorPaths.G7.Simeq (inParam p f) (inParam p g) := by
  obtain ⟨h0, w, _, hw⟩ := h
  have h1 : MvPowerSeries.constantCoeff (inParam p (f - g)) = 0 := th_inParam_const p h0
  rw [th_inParam_sub] at h1 hw
  refine ⟨h1, ?_⟩
  rw [← sx_expS_eq p h1, sx_integral_iff, hw]
  exact ⟨1 + w, by rw [map_add (f := _), map_one]⟩

theorem integralExp_of_equiv {σ : Type} {f g : MvPowerSeries σ (K0 p)} (h : Formalism.InvariantFactorPaths.G7.Simeq f g) : E0 p (f - g) := by
  obtain ⟨h0, h1⟩ := h
  rw [← sx_expS_eq p h0, sx_integral_iff] at h1
  obtain ⟨w, hw⟩ := h1
  refine ⟨h0, w - 1, ?_, ?_⟩
  · have h2 : MvPowerSeries.constantCoeff (expS p (f - g)) = 1 := by
      rw [sx_expS_eq p h0]
      exact Formalism.InvariantFactorPaths.G7.DworkIntegrality.constantCoeff_mvExp h0
    rw [hw] at h2
    have h3 : algebraMap (WW p) (K0 p) (MvPowerSeries.constantCoeff w) = 1 := by
      rw [← h2, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
        MvPowerSeries.coeff_map]
    have h4 : MvPowerSeries.constantCoeff w = 1 :=
      IsFractionRing.injective (WW p) (K0 p) (by rw [h3, map_one])
    rw [map_sub, h4, map_one, sub_self]
  · show expS p (f - g) = _
    rw [hw, map_sub, map_one]
    ring

theorem equiv_zero_of_integralExp {σ : Type} {f : MvPowerSeries σ (K0 p)} (h : E0 p f) : Formalism.InvariantFactorPaths.G7.Simeq f 0 := by
  obtain ⟨h0, w, _, hw⟩ := h
  rw [Formalism.InvariantFactorPaths.G7.Simeq, sub_zero]
  refine ⟨h0, ?_⟩
  rw [← sx_expS_eq p h0, sx_integral_iff]
  exact ⟨1 + w, by rw [map_add (f := _), map_one]; exact hw⟩

theorem integralExp_param_of_equiv_zero {σ : Type} [Finite σ] {f : MvPowerSeries σ (K0 p)} (h : Simeq p f 0) : E0 p (inParam p f) := by
  have := integralExp_of_equiv p (sx_simeq_of p h)
  have e : inParam p (0 : MvPowerSeries σ (K0 p)) = 0 := by
    have := th_inParam_sub p (0 : MvPowerSeries σ (K0 p)) 0
    simpa using this
  rwa [e, sub_zero] at this

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end
