module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle002
public import Mathlib.CategoryTheory.Category.Basic
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle004
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle005
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle006
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.TGK

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [Fintype P] [DecidableEq P]

def cLam (lam : TV n M P →ₗ[ℂ] ℂ) (I : P → Fin n) : M →ₗ[ℂ] ℂ :=
  lam ∘ₗ LinearMap.single ℂ (fun _ : P → Fin n => M) I

theorem cLam_sum (lam : TV n M P →ₗ[ℂ] ℂ) (v : TV n M P) : lam v = ∑ I, cLam lam I (v I) := by
  conv_lhs => rw [← Finset.univ_sum_single v]

  rw [map_sum]
  rfl

omit [DecidableEq P] in
theorem cprod_one (I J : P → Fin n) :
    ∏ p, (1 : Matrix (Fin n) (Fin n) ℂ) (I p) (J p) = if I = J then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · obtain ⟨p, hp⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ p) (Matrix.one_apply_ne hp)

theorem cprod_erase (I J : P → Fin n) (p : P) (x : ℂ) :
    (∏ q ∈ Finset.univ.erase p, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q)) * x =
      ∑ b, if J = Function.update I p b then x else 0 := by
  by_cases h : ∀ q, q ≠ p → I q = J q
  · rw [Finset.prod_eq_one, one_mul, Finset.sum_eq_single (J p)]
    · rw [if_pos]; funext q; by_cases hq : q = p
      · subst hq; simp
      · simp [Function.update_of_ne hq, h q hq]
    · intro b _ hb; rw [if_neg]; intro hJ; apply hb; rw [hJ]; simp
    · simp
    · intro q hq; rw [h q (Finset.ne_of_mem_erase hq)]; simp
  · push Not at h
    obtain ⟨q, hqp, hq⟩ := h
    have h0 : ∏ q ∈ Finset.univ.erase p, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q) = 0 :=
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hqp, Finset.mem_univ q⟩) (Matrix.one_apply_ne hq)
    rw [h0, zero_mul]
    refine (Finset.sum_eq_zero fun b _ => if_neg ?_).symm
    intro hJ; apply hq; rw [hJ, Function.update_of_ne hqp]

theorem csum_erase (I : P → Fin n) (p : P) (φ : (P → Fin n) → ℂ) :
    ∑ J, (∏ q ∈ Finset.univ.erase p, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q)) * φ J =
      ∑ b, φ (Function.update I p b) := by
  simp_rw [cprod_erase]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp

omit [Fintype P] [DecidableEq P] in
theorem ckey (I : P → Fin n) (S : Finset P) (F : Fin n → Fin n → ℂ) (h : Fin n → P → ℂ) :
    ∑ a, ∑ b, F a b * ∑ p ∈ S, (if I p = a then h b p else 0) = ∑ p ∈ S, ∑ b, F (I p) b * h b p := by
  simp_rw [Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp

def cD {ι : Type} [DecidableEq ι] (bar : ι → ι) (τ : ι) (X : Matrix (Fin n) (Fin n) ℂ) (σ : ι) (i j : Fin n) : ℂ :=
  (if σ = τ then X i j else 0) + (if σ = bar τ then star (X i j) else 0)

theorem cderiv_entry {ι Γ : Type} [DecidableEq ι] (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (bar : ι → ι) (τ : ι)
    (hne : bar τ ≠ τ) (hconj : ∀ σ γ i j, κ (bar σ) γ i j = star (κ σ γ i j))
    (X : Matrix (Fin n) (Fin n) ℂ) (c : ℝ → Γ)
    (hd : ∀ i j, HasDerivAt (fun t => κ τ (c t) i j) (X i j) 0)
    (hoth : ∀ τ', τ' ≠ τ → τ' ≠ bar τ → ∀ t, κ τ' (c t) = 1) (σ : ι) (i j : Fin n) :
    HasDerivAt (fun t => κ σ (c t) i j) (cD bar τ X σ i j) 0 := by
  unfold cD
  by_cases h1 : σ = τ
  · subst h1
    rw [if_pos rfl, if_neg (fun h => hne h.symm), add_zero]
    exact hd i j
  · by_cases h2 : σ = bar τ
    · subst h2
      rw [if_neg h1, if_pos rfl, zero_add]
      simp_rw [hconj τ]
      exact (hd i j).star
    · rw [if_neg h1, if_neg h2, add_zero]
      rw [show (fun t => κ σ (c t) i j) = fun _ => (1 : Matrix (Fin n) (Fin n) ℂ) i j from
        funext fun t => by rw [hoth σ h1 h2 t]]
      exact hasDerivAt_const _ _

omit [DecidableEq P] in
theorem cpart {ι : Type} [DecidableEq ι] (lab : P → ι) (bar : ι → ι) (τ : ι) (X : Matrix (Fin n) (Fin n) ℂ)
    (I : P → Fin n) (h : Fin n → P → ℂ) :
    ∑ p, ∑ b, cD bar τ X (lab p) (I p) b * h b p =
      ∑ p ∈ fib lab τ, ∑ b, X (I p) b * h b p + ∑ p ∈ fib lab (bar τ), ∑ b, star (X (I p) b) * h b p := by
  unfold fib
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold cD
  split_ifs <;> simp [add_mul, Finset.sum_add_distrib]

theorem actT_der {ι Γ : Type} [DecidableEq ι] [Group Γ] (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (E : ι → Fin n → Fin n → Module.End ℂ M) (ρ : Γ → Module.End ℂ M) (bar : ι → ι) (τ : ι) (hne : bar τ ≠ τ)
    (hρ1 : ρ 1 = 1) (hκ1 : ∀ σ, κ σ 1 = 1) (hconj : ∀ σ γ i j, κ (bar σ) γ i j = star (κ σ γ i j))
    (X : Matrix (Fin n) (Fin n) ℂ) (c : ℝ → Γ) (hc0 : c 0 = 1)
    (hd : ∀ i j, HasDerivAt (fun t => κ τ (c t) i j) (X i j) 0)
    (hoth : ∀ τ', τ' ≠ τ → τ' ≠ bar τ → ∀ t, κ τ' (c t) = 1)
    (hρ : ∀ y (lam : M →ₗ[ℂ] ℂ), HasDerivAt (fun t => lam (ρ (c t) y))
      (lam ((∑ a, ∑ b, (X a b • E τ a b + star (X a b) • E (bar τ) a b)) y)) 0)
    (y : TV n M P) (lam : TV n M P →ₗ[ℂ] ℂ) :
    HasDerivAt (fun t => lam (actT lab κ ρ (c t) y))
      (lam ((∑ a, ∑ b, (X a b • tE (fib lab τ) (E τ) a b + star (X a b) • tE (fib lab (bar τ)) (E (bar τ)) a b)) y))
      0 := by
  have hf : (fun t => lam (actT lab κ ρ (c t) y)) = fun t => ∑ I, ∑ J,
      (∏ p, κ (lab p) (c t) (I p) (J p)) * cLam lam I (ρ (c t) (y J)) := by
    funext t
    rw [cLam_sum]
    refine Finset.sum_congr rfl fun I _ => ?_

    rw [actT_apply, map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [hf]
  have hg : ∀ I J : P → Fin n, HasDerivAt (fun t => ∏ p, κ (lab p) (c t) (I p) (J p))
      (∑ p, (∏ q ∈ Finset.univ.erase p, (1 : Matrix (Fin n) (Fin n) ℂ) (I q) (J q)) •
        cD bar τ X (lab p) (I p) (J p)) 0 := by
    intro I J
    have := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun p t => κ (lab p) (c t) (I p) (J p)) (x := 0)
      (fun p _ => cderiv_entry κ bar τ hne hconj X c hd hoth (lab p) (I p) (J p))
    simp only [hc0, hκ1] at this
    exact this
  have hall : HasDerivAt (fun t => ∑ I, ∑ J,
      (∏ p, κ (lab p) (c t) (I p) (J p)) * cLam lam I (ρ (c t) (y J))) _ 0 :=
    HasDerivAt.fun_sum fun I _ => HasDerivAt.fun_sum fun J _ => (hg I J).fun_mul (hρ (y J) (cLam lam I))
  refine hall.congr_deriv ?_
  simp only [hc0, hκ1, hρ1, Module.End.one_apply]
  rw [cLam_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.sum_add_distrib]
  simp_rw [cprod_one, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [Finset.sum_mul, smul_eq_mul, mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [csum_erase, Function.update_self]
  rw [cpart lab bar τ X I (fun b p => cLam lam I (y (Function.update I p b)))]

  simp only [LinearMap.sum_apply, LinearMap.add_apply, LinearMap.smul_apply, Finset.sum_apply, Pi.add_apply,
  Pi.smul_apply, tE_apply, map_sum, map_add, map_smul, smul_eq_mul, apply_ite (cLam lam I), map_zero,
  mul_add, Finset.sum_add_distrib]
  rw [ckey I (fib lab τ) (fun a b => X a b) (fun b p => cLam lam I (y (Function.update I p b))),
    ckey I (fib lab (bar τ)) (fun a b => star (X a b)) (fun b p => cLam lam I (y (Function.update I p b)))]
  ring

end PositivityTheory.Rg.Cz.TGK

end
end

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace TensorGLSums

theorem glSum {R : Type*} [Ring R] {n : ℕ} {ι : Type*} [DecidableEq ι] (S : Finset ι) (L : Fin n → Fin n → R)
    (e : ι → Fin n → Fin n → R) (hL : GlRel L) (hLe : ∀ p a b c d, Commute (L a b) (e p c d))
    (he : ∀ p q a b c d, e p a b * e q c d - e q c d * e p a b =
      if p = q then (if b = c then e p a d else 0) - (if d = a then e p c b else 0) else 0) :
    GlRel (fun a b => L a b + ∑ p ∈ S, e p a b) := by
  intro a b c d
  have key : ∀ x y u v : R, (x + u) * (y + v) - (y + v) * (x + u) =
      (x * y - y * x) + (x * v - v * x) + (u * y - y * u) + (u * v - v * u) := by
    intros; noncomm_ring
  simp only
  rw [key, hL]
  have h1 : L a b * ∑ p ∈ S, e p c d - (∑ p ∈ S, e p c d) * L a b = 0 := by
    rw [sub_eq_zero]; exact (Commute.sum_right _ _ _ fun p _ => hLe p a b c d).eq
  have h2 : (∑ p ∈ S, e p a b) * L c d - L c d * ∑ p ∈ S, e p a b = 0 := by
    rw [sub_eq_zero]; exact (Commute.sum_left _ _ _ fun p _ => (hLe p c d a b).symm).eq
  have h3 : (∑ p ∈ S, e p a b) * (∑ q ∈ S, e q c d) - (∑ q ∈ S, e q c d) * (∑ p ∈ S, e p a b) =
      ∑ p ∈ S, ((if b = c then e p a d else 0) - (if d = a then e p c b else 0)) := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (s := S) (t := S)
      (f := fun q p => e q c d * e p a b), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [← Finset.sum_sub_distrib]
    simp_rw [he p]
    rw [Finset.sum_ite_eq]
    simp [hp]
  rw [h1, h2, h3]
  split_ifs <;> simp [Finset.sum_sub_distrib] <;> abel

theorem omComm {R : Type*} [Ring R] {n : ℕ} (L e : Fin n → Fin n → R) (hL : GlRel L)
    (hLe : ∀ a b c d, Commute (L a b) (e c d)) (he : ∀ a b c d, e a b * e c d = if b = c then e a d else 0)
    (c d : Fin n) : Commute (∑ a, ∑ b, L a b * e b a) (L c d + e c d) := by
  rw [Commute, SemiconjBy, ← sub_eq_zero]
  have hterm : ∀ a b, L a b * e b a * (L c d + e c d) - (L c d + e c d) * (L a b * e b a) =
      ((if b = c then L a d * e b a else 0) - (if d = a then L c b * e b a else 0)) +
      ((if a = c then L a b * e b d else 0) - (if d = b then L a b * e c a else 0)) := by
    intro a b
    have h1 : e b a * L c d = L c d * e b a := ((hLe c d b a).eq).symm
    have h2 : e c d * L a b = L a b * e c d := ((hLe a b c d).eq).symm
    have h3 := hL a b c d
    have e1 := he b a c d
    have e2 := he c d b a
    calc L a b * e b a * (L c d + e c d) - (L c d + e c d) * (L a b * e b a)
        = (L a b * L c d - L c d * L a b) * e b a + L a b * (e b a * e c d - e c d * e b a) := by
          have k1 : L a b * e b a * L c d = L a b * L c d * e b a := by rw [mul_assoc, h1, ← mul_assoc]
          have k2 : e c d * (L a b * e b a) = L a b * e c d * e b a := by rw [← mul_assoc, h2]
          rw [mul_add, add_mul, k1, k2]
          noncomm_ring
      _ = _ := by
          rw [h3, e1, e2]
          split_ifs <;> simp [sub_mul, mul_sub]
  have hx : (∑ a, ∑ b, L a b * e b a) * (L c d + e c d) - (L c d + e c d) * (∑ a, ∑ b, L a b * e b a) =
      ∑ a, ∑ b, (L a b * e b a * (L c d + e c d) - (L c d + e c d) * (L a b * e b a)) := by
    simp only [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hx]
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_comm (f := fun a b => if d = a then L c b * e b a else 0)]
  rw [Finset.sum_comm (f := fun a b => if a = c then L a b * e b d else 0)]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  abel

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] {P : Type} [DecidableEq P]

theorem eAt_mul (p : P) (a b c d : Fin n) :
    (eAt p a b * eAt p c d : Module.End ℂ (TV n M P)) = if b = c then eAt p a d else 0 := by
  refine LinearMap.ext fun f => funext fun I => ?_
  by_cases hbc : b = c
  · subst hbc
    simp [Module.End.mul_apply, eAt_apply, Function.update_idem]
  · simp [Module.End.mul_apply, eAt_apply, hbc]

theorem eAt_comm {p q : P} (h : p ≠ q) (a b c d : Fin n) :
    (eAt p a b * eAt q c d : Module.End ℂ (TV n M P)) = eAt q c d * eAt p a b := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, eAt_apply, Function.update_of_ne h, Function.update_of_ne (Ne.symm h),
    Function.update_comm h]
  split_ifs <;> rfl

theorem pm_eAt (σ : Equiv.Perm P) (p : P) (a b : Fin n) :
    (pm σ * eAt p a b : Module.End ℂ (TV n M P)) = eAt (σ p) a b * pm σ := by
  refine LinearMap.ext fun f => funext fun I => ?_
  simp only [Module.End.mul_apply, eAt_apply, pm_apply, Function.comp_apply]
  rw [Function.update_comp_equiv]
  simp

omit [DecidableEq P] in
theorem glLift (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) :
    GlRel (fun a b => (lift (E a b) : Module.End ℂ (TV n M P))) := by
  intro a b c d
  have := congrArg (liftA n M P) (hE a b c d)
  simp only [map_sub, map_mul, apply_ite (liftA n M P), map_zero] at this
  exact this

end TensorGLSums

open TensorGLSums in
theorem tensorGl_holds : TensorGl := by
  intro n M _ _ P _ _ E hE S
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact glSum S _ _ (glLift E hE) (fun p a b c d => lift_comm_eAt _ _ _ _) fun p q a b c d => by
      by_cases hpq : p = q
      · subst hpq; rw [if_pos rfl, eAt_mul, eAt_mul]
      · rw [if_neg hpq, eAt_comm hpq, sub_self]
  · intro p hp a b
    have hsplit : tE S E a b = (lift (E a b) + eAt p a b) + ∑ q ∈ S.erase p, eAt q a b := by
      rw [tE, add_assoc]; congr 1; exact (Finset.add_sum_erase S (fun q => eAt q a b) hp).symm
    rw [hsplit]
    refine Commute.add_right ?_ (Commute.sum_right _ _ _ fun q hq => ?_)
    · exact omComm (fun a b => lift (E a b)) (fun a b => eAt p a b) (glLift E hE)
        (fun a b c d => lift_comm_eAt _ _ _ _) (fun a b c d => eAt_mul p a b c d) a b
    · have hqp : q ≠ p := Finset.ne_of_mem_erase hq
      refine Commute.sum_left _ _ _ fun a' _ => Commute.sum_left _ _ _ fun b' _ => ?_
      exact Commute.mul_left (lift_comm_eAt _ _ _ _) (eAt_comm (Ne.symm hqp) _ _ _ _)
  · intro σ hσ a b
    rw [tE, Commute, SemiconjBy, mul_add, add_mul, (lift_comm_pm _ σ).eq, Finset.mul_sum, Finset.sum_mul]
    congr 1
    simp_rw [pm_eAt]
    exact Finset.sum_equiv σ (fun p => (hσ p).symm) fun p _ => rfl
  · intro σ p
    simp only [Om, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [← mul_assoc, ← (lift_comm_pm _ σ).eq, mul_assoc, pm_eAt, mul_assoc]

end PositivityTheory.Rg.Cz

end
end

section

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace SemiInvariantDeterminant

theorem det_bar {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] {n : ℕ} {bar : ι → ι}
    {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} (hK : IsKD bar κ) (τ : ι) (γ : Γ) :
    (κ (bar τ) γ).det = star (κ τ γ).det := by
  have e : κ (bar τ) γ = (starRingEnd ℂ).mapMatrix (κ τ γ) := by
    ext i j; exact hK.conj τ γ i j
  rw [e, ← RingHom.map_det]
  rfl

theorem det_mul_star {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] {n : ℕ} {bar : ι → ι}
    {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} (hK : IsKD bar κ) (τ : ι) (γ : Γ) :
    (κ τ γ).det * star (κ τ γ).det = 1 := by
  have := congrArg Matrix.det (hK.unit τ γ)
  rwa [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this

end SemiInvariantDeterminant

open SemiInvariantDeterminant in
theorem semiZero_of (hQ : QdetFacts) (_hW : WallAlg) (hL : LieInv) (hWQ : WallQuot) : SemiZero := by
  intro n hn M _ _ ι _ _ Γ _ _ bar κ E ρ hK hG s φ hφ hS
  obtain ⟨lab, c, ξ, -, hact, I, w, hw, hwξ⟩ := hS
  have hρ : ∀ γ, ρ γ (ξ I) = (∏ τ, (κ τ γ).det ^ c τ) • ξ I := by
    intro γ
    have h := congrFun (hact γ) I
    rw [actT_apply, Pi.smul_apply] at h
    rw [← h, Fintype.sum_unique]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
    rw [Subsingleton.elim (default : Fin 0 → Fin n) I]
  obtain ⟨N, F, hFgl, -, hFch, hFE, hN⟩ := hWQ n M ι E hG.gl hG.comm (fun _ _ => s) φ (by
    intro τ u
    rw [hφ τ u, Finset.prod_const, Finset.card_univ, Fintype.card_fin])
  have hξN : N.mkQ (ξ I) ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hN]
    push Not
    exact ⟨w, hw, hwξ⟩
  have htr : ∀ τ', N.mkQ ((∑ a, E τ' a a) (ξ I)) = (∑ a, F τ' a a) (N.mkQ (ξ I)) := by
    intro τ'

    simp only [LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun a _ => LinearMap.congr_fun (hFE τ' a a) (ξ I)
  have hc : ∀ τ, c τ = c (bar τ) := by
    intro τ
    have hl := hL n M ι Γ bar κ E ρ hK hG c (ξ I) hρ τ
    have h1 : N.mkQ ((∑ a, E τ a a) (ξ I)) = N.mkQ ((∑ a, E (bar τ) a a) (ξ I)) := by
      rw [htr, htr, (hQ n (M ⧸ N) (F τ) (hFgl τ)).2.2.1 _ (hFch τ),
        (hQ n (M ⧸ N) (F (bar τ)) (hFgl (bar τ))).2.2.1 _ (hFch (bar τ))]
    have h2 : (∑ a, E τ a a) (ξ I) - (∑ a, E (bar τ) a a) (ξ I) =
        ((n : ℂ) * ((c τ - c (bar τ) : ℤ) : ℂ)) • ξ I := by
      rw [LinearMap.sum_apply, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
      simp only [hl, if_true]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    have h3 : ((n : ℂ) * ((c τ - c (bar τ) : ℤ) : ℂ)) • N.mkQ (ξ I) = 0 := by
      rw [← map_smul, ← h2, map_sub, h1, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd (Nat.cast_eq_zero.mp h) (by omega)
      · exact sub_eq_zero.mp (Int.cast_eq_zero.mp h)
    · exact absurd h hξN
  have hχ : ∀ γ, (∏ τ, (κ τ γ).det ^ c τ) = 1 := by
    intro γ
    refine Finset.prod_involution (fun τ _ => bar τ) ?_ ?_ (fun _ _ => Finset.mem_univ _)
      (fun τ _ => hK.invol τ)
    · intro τ _
      rw [det_bar hK, ← hc τ, ← mul_zpow, det_mul_star hK, _root_.one_zpow]
    · intro τ _ _
      exact hK.ne τ
  exact ⟨ξ I, fun γ => by rw [hρ, hχ, one_smul], w, hw, hwξ⟩

end PositivityTheory.Rg.Cz

end
end
