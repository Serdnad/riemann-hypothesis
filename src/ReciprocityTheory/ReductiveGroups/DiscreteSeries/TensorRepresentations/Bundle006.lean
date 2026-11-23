module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.LowFockB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Bundle001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.AnalyticVectors.Taylor
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.CoefCExpEntrySummable
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Bundle005
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open Finset
open scoped Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def coefAm (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  cond dual (g⁻¹)ᵀ g

def coefBm (dual : Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  cond dual (-Xᵀ) X

theorem coefD_Am_exp (dual : Bool) (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    coefAm dual (NormedSpace.exp ((s : ℂ) • X)) = NormedSpace.exp ((s : ℂ) • coefBm dual X) := by
  cases dual
  · rfl
  · simp only [coefAm, coefBm, cond_true]
    rw [← Matrix.exp_neg, ← Matrix.exp_transpose]
    congr 1
    rw [Matrix.transpose_neg, Matrix.transpose_smul, smul_neg]

section Alg

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

def coefPm (B : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ (Fin n → M) :=
  LinearMap.pi fun c => ∑ d, B c d • LinearMap.proj d

theorem coefPm_apply (B : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → M) (c : Fin n) :
    coefPm B u c = ∑ d, B c d • u d := by
  simp [coefPm, LinearMap.sum_apply]

theorem coefPm_pow (B : Matrix (Fin n) (Fin n) ℂ) (j : ℕ) (u : Fin n → M) (c : Fin n) :
    ((coefPm (M := M) B) ^ j) u c = ∑ d, (B ^ j) c d • u d := by
  induction j generalizing c with
  | zero =>
    simp only [pow_zero, Module.End.one_apply, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq]
    simp
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply, coefPm_apply, pow_succ']
    simp_rw [ih, Matrix.mul_apply, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]

theorem coefD_diag_pow (A : Module.End ℂ M) (k : ℕ) (u : Fin n → M) (c : Fin n) :
    ((diagOp (n := n) A) ^ k) u c = (A ^ k) (u c) := by
  induction k generalizing u with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih, diagOp_coord, ← Module.End.mul_apply, ← pow_succ]

theorem coefD_comm (A : Module.End ℂ M) (B : Matrix (Fin n) (Fin n) ℂ) :
    Commute (coefPm (M := M) B) (diagOp A) := by
  refine LinearMap.ext fun u => funext fun c => ?_

  simp only [Module.End.mul_apply, coefPm_apply, diagOp_coord, map_sum, map_smul]

theorem coefD_sum_ite (c : Fin n) (f : Fin n → Fin n → M) :
    ∑ x, ∑ y, (if c = x then f x y else 0) = ∑ y, f c y := by
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

theorem coefD_sum_ite' (c : Fin n) (f : Fin n → Fin n → M) :
    ∑ x, ∑ y, (if c = y then f x y else 0) = ∑ x, f x c := by
  simp [Finset.sum_ite_eq]

theorem coefD_tensAct_eq (dual : Bool) (E : Fin n → Fin n → Module.End ℂ M)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    actM (tensF dual E) X = coefPm (coefBm dual X) + diagOp (actM E X) := by
  refine LinearMap.ext fun u => funext fun c => ?_
  simp only [actM, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, coefPm_apply, diagOp_coord, Pi.add_apply]
  cases dual
  · simp only [tensF, cond_false, coefBm, tensV_coord, smul_add, Finset.sum_add_distrib, smul_ite,
      smul_zero, coefD_sum_ite]
    rw [add_comm]
  · simp only [tensF, cond_true, coefBm, tensVd_coord, smul_sub, Finset.sum_sub_distrib, smul_ite,
      smul_zero, coefD_sum_ite', Matrix.neg_apply, Matrix.transpose_apply, neg_smul,
      Finset.sum_neg_distrib]
    abel

theorem coefD_tensAct_pow (dual : Bool) (E : Fin n → Fin n → Module.End ℂ M)
    (X : Matrix (Fin n) (Fin n) ℂ) (m : ℕ) (u : Fin n → M) (c : Fin n) :
    ((actM (tensF dual E) X) ^ m) u c = ∑ kl ∈ antidiagonal m, (m.choose kl.1 : ℂ) •
      ∑ d, ((coefBm dual X) ^ kl.1) c d • ((actM E X) ^ kl.2) (u d) := by
  rw [coefD_tensAct_eq, (coefD_comm (actM E X) (coefBm dual X)).add_pow', LinearMap.sum_apply,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun kl _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, ← Nat.cast_smul_eq_nsmul ℂ, Module.End.mul_apply,
    coefPm_pow]
  simp_rw [coefD_diag_pow]

end Alg

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H}
  {E : Fin n → Fin n → Module.End ℂ D}

def coefTG (dual : Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (g : Matrix (Fin n) (Fin n) ℂ)
    (f : Fin n → H) : Fin n → H :=
  fun c => ∑ d, coefAm dual g c d • σ g (f d)

theorem coefD_tensGrp_eq (dual : Bool) (g : Matrix (Fin n) (Fin n) ℂ) (f : Fin n → H) (c : Fin n) :
    coefTG dual σ g f c = ∑ d, coefAm dual g c d • σ g (f d) := rfl

theorem coefD_comb (s : ℂ) (m : ℕ) (B : Matrix (Fin n) (Fin n) ℂ) (L : Fin n → Fin n → ℕ → ℂ) :
    s ^ m / (m.factorial : ℂ) * ∑ c, ∑ kl ∈ antidiagonal m, (m.choose kl.1 : ℂ) *
        ∑ d, (B ^ kl.1) c d * L c d kl.2 =
      ∑ c, ∑ d, ∑ kl ∈ antidiagonal m,
        s ^ kl.1 / (kl.1.factorial : ℂ) * (B ^ kl.1) c d * (s ^ kl.2 / (kl.2.factorial : ℂ) * L c d kl.2) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun kl hkl => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
  rw [← mul_assoc, ← hkl, coefC_choose_coef, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

theorem coefD_taylor (dual : Bool) (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) (Λ : (Fin n → H) →L[ℂ] ℂ) (w : Fin n → D) (s : ℝ)
    (hb : ∀ d, ∃ a : ℕ → ℝ, (∀ m, ‖((((actM E X) ^ m) (w d) : D) : H)‖ ≤ a m) ∧
      Summable fun m : ℕ => a m * |s| ^ m / (m.factorial : ℝ)) :
    HasSum (fun m : ℕ => (s : ℂ) ^ m / (m.factorial : ℂ) *
        Λ (fun c => ((((actM (tensF dual E) X) ^ m) w c : D) : H)))
      (Λ (coefTG dual σ (NormedSpace.exp ((s : ℂ) • X)) (fun d => ((w d : D) : H)))) := by
  set lc : Fin n → (H →L[ℂ] ℂ) := fun c => Λ.comp (ContinuousLinearMap.single ℂ (fun _ : Fin n => H) c)
  have hΛ : ∀ u : Fin n → H, Λ u = ∑ c, lc c (u c) := by
    intro u
    conv_lhs => rw [← Finset.univ_sum_single u]

    rw [map_sum]
    rfl
  set B := coefBm dual X
  set Y := actM E X
  set L : Fin n → Fin n → ℕ → ℂ := fun c d k => lc c ((((Y ^ k) (w d) : D) : H))

  have hpair : ∀ c d, HasSum (fun m => ∑ kl ∈ antidiagonal m,
      (s : ℂ) ^ kl.1 / (kl.1.factorial : ℂ) * (B ^ kl.1) c d * ((s : ℂ) ^ kl.2 / (kl.2.factorial : ℂ) * L c d kl.2))
      (coefAm dual (NormedSpace.exp ((s : ℂ) • X)) c d *
        lc c (σ (NormedSpace.exp ((s : ℂ) • X)) ((w d : D) : H))) := by
    intro c d
    obtain ⟨a, ha, hs⟩ := hb d
    have hA := coefC_exp_entry_hasSum B s c d
    rw [← coefD_Am_exp] at hA
    have hA' := coefC_exp_entry_summable B s c d
    have horb := hasSum_orbit_of_bound hσ hD hX (w d) a ha 0 s (by simpa using hs)
    rw [exp_zero_smul, hσ.1.1] at horb
    have horb' := horb.mapL (lc c)
    have hσs : HasSum (fun k : ℕ => (s : ℂ) ^ k / (k.factorial : ℂ) * L c d k)
        (lc c (σ (NormedSpace.exp ((s : ℂ) • X)) ((w d : D) : H))) := by
      refine horb'.congr_fun fun k => ?_
      simp only [L, Y, ContinuousLinearMap.one_apply, map_smul, smul_eq_mul, sub_zero]
      push_cast
      ring
    have hσ' : Summable fun k : ℕ => ‖(s : ℂ) ^ k / (k.factorial : ℂ) * L c d k‖ := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (hs.mul_left ‖lc c‖)
      rw [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
      have h1 : ‖L c d k‖ ≤ ‖lc c‖ * a k := ((lc c).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left (ha k) (norm_nonneg _))
      calc |s| ^ k / (k.factorial : ℝ) * ‖L c d k‖ ≤ |s| ^ k / (k.factorial : ℝ) * (‖lc c‖ * a k) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ‖lc c‖ * (a k * |s| ^ k / (k.factorial : ℝ)) := by ring
    have hmul := coefC_hasSum_mul hA hσs hA' hσ'
    exact hmul
  have htot := hasSum_sum fun c (_ : c ∈ (Finset.univ : Finset (Fin n))) =>
    hasSum_sum fun d (_ : d ∈ (Finset.univ : Finset (Fin n))) => hpair c d
  have hR : Λ (coefTG dual σ (NormedSpace.exp ((s : ℂ) • X)) (fun d => ((w d : D) : H))) =
      ∑ c, ∑ d, coefAm dual (NormedSpace.exp ((s : ℂ) • X)) c d *
        lc c (σ (NormedSpace.exp ((s : ℂ) • X)) ((w d : D) : H)) := by
    rw [hΛ]
    refine Finset.sum_congr rfl fun c _ => ?_

    rw [coefD_tensGrp_eq, map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [hR]
  refine htot.congr_fun fun m => ?_
  rw [hΛ]

  simp only [coefD_tensAct_pow, Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, smul_eq_mul]
  rw [← coefD_comb]

end Rep

end ReciprocityTheory.ChartRestriction.DS
end
end

section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

def lowerWedgeAlt (ε : Fin n → Bool) : LfIdx ε :=
  ⟨(lfPhysModes ε).filter fun m => (finProdFinEquiv.symm m).2 < (finProdFinEquiv.symm m).1, filter_subset _ _⟩

theorem mem_lowerWedge_iff (ε : Fin n → Bool) (x : Fin n × Fin n) :
    finProdFinEquiv x ∈ (lowerWedgeAlt ε).1 ↔ ε x.1 = true ∧ ε x.2 = false ∧ x.2 < x.1 := by
  simp only [lowerWedgeAlt, lfPhysModes, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply,
    and_assoc]

theorem lf_rhoHol_sub_rhoN (ε : Fin n → Bool) (c : Fin n) :
    (rhoHol ε - rhoN ε) c = if ε c = true then ((univ.filter fun a => ε a = false ∧ a < c).card : ℝ)
      else -((univ.filter fun i => ε i = true ∧ c < i).card : ℝ) := by
  rw [cfa_rho_coord]
  cases hc : ε c <;> simp [hc, Finset.sum_boole]

theorem lowerWedge_weight (ε : Fin n → Bool) (c : Fin n) :
    sgE ε cpFock cmFock c c (fockBasis n (lowerWedgeAlt ε).1) =
      (((rhoHol ε - rhoN ε) c : ℝ) : ℂ) • fockBasis n (lowerWedgeAlt ε).1 := by
  have hw : fockWt ε (lowerWedgeAlt ε).1 c = (rhoHol ε - rhoN ε) c := by
    rw [cfa_rho_coord, fockWt, Finset.sum_apply]
    have hS : (lowerWedgeAlt ε).1 = univ.filter fun k => ε (finProdFinEquiv.symm k).1 = true ∧
        ε (finProdFinEquiv.symm k).2 = false ∧ (finProdFinEquiv.symm k).2 < (finProdFinEquiv.symm k).1 := by
      ext k
      simp only [lowerWedgeAlt, lfPhysModes, Finset.mem_filter, Finset.mem_univ, true_and, and_assoc]
    rw [hS, Finset.sum_filter, ← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    simp only [Equiv.symm_apply_apply]
    have key : ∀ i b : Fin n, (if ε i = true ∧ ε b = false ∧ b < i then modeWt ε (i, b) c else 0) =
        (if c = i then (if ε i = true ∧ ε b = false ∧ b < i then (1 : ℝ) else 0) else 0) -
        (if c = b then (if ε i = true ∧ ε b = false ∧ b < i then (1 : ℝ) else 0) else 0) := by
      intro i b
      by_cases h : ε i = true ∧ ε b = false ∧ b < i
      · simp only [if_pos h]
        simp only [modeWt, if_pos (And.intro h.1 h.2.1), root, Pi.sub_apply, Pi.single_apply]
      · simp only [if_neg h]
        simp
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => key i b]
    simp only [Finset.sum_sub_distrib]
    congr 1
    · rw [Finset.sum_comm]
      simp
    · simp
  rw [fockBasis_wt, hw]

theorem lowerWedge_killed_by_lowering (ε : Fin n → Bool) {a b : Fin n} (hba : b < a) (he : ε a = ε b) :
    sgE ε cpFock cmFock a b (fockBasis n (lowerWedgeAlt ε).1) = 0 := by
  have hab : a ≠ b := (ne_of_lt hba).symm
  unfold sgE
  split_ifs with h1 h2
  · rw [LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    have hxm : ε x = false := (Finset.mem_filter.1 hx).2
    rw [Module.End.mul_apply]
    by_cases hbx : finProdFinEquiv (b, x) ∈ (lowerWedgeAlt ε).1
    · obtain ⟨σ, -, hσ, -⟩ := lf_cm_basis_of_mem (x := (b, x)) hbx
      dsimp only at hσ
      rw [hσ, map_smul]
      have hxb : x < b := ((mem_lowerWedge_iff ε (b, x)).1 hbx).2.2
      have hmem : finProdFinEquiv (a, x) ∈ (lowerWedgeAlt ε).1.erase (finProdFinEquiv (b, x)) := by
        rw [Finset.mem_erase]
        exact ⟨fun h => hab (congrArg Prod.fst (finProdFinEquiv.injective h)),
          (mem_lowerWedge_iff ε (a, x)).2 ⟨h1.1, hxm, hxb.trans hba⟩⟩
      have h0 := lf_cp_basis_of_mem (x := (a, x)) hmem
      dsimp only at h0
      rw [h0, smul_zero]
    · have h0 := lf_cm_basis_of_not_mem (x := (b, x)) hbx
      dsimp only at h0
      rw [h0, map_zero]
  · rw [LinearMap.neg_apply, LinearMap.sum_apply, neg_eq_zero]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hip : ε i = true := (Finset.mem_filter.1 hi).2
    rw [Module.End.mul_apply]
    by_cases hia : finProdFinEquiv (i, a) ∈ (lowerWedgeAlt ε).1
    · obtain ⟨σ, -, hσ, -⟩ := lf_cm_basis_of_mem (x := (i, a)) hia
      dsimp only at hσ
      rw [hσ, map_smul]
      have hai : a < i := ((mem_lowerWedge_iff ε (i, a)).1 hia).2.2
      have hmem : finProdFinEquiv (i, b) ∈ (lowerWedgeAlt ε).1.erase (finProdFinEquiv (i, a)) := by
        rw [Finset.mem_erase]
        exact ⟨fun h => hab (congrArg Prod.snd (finProdFinEquiv.injective h)).symm,
          (mem_lowerWedge_iff ε (i, b)).2 ⟨hip, h2.2, hba.trans hai⟩⟩
      have h0 := lf_cp_basis_of_mem (x := (i, b)) hmem
      dsimp only at h0
      rw [h0, smul_zero]
    · have h0 := lf_cm_basis_of_not_mem (x := (i, a)) hia
      dsimp only at h0
      rw [h0, map_zero]
  · exfalso
    cases hb : ε b <;> simp_all

end ReciprocityTheory.ChartRestriction.DS
end
end
