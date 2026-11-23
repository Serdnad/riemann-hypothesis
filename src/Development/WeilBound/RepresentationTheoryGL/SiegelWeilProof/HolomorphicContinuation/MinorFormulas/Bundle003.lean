module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.Bundle001
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.MinorB
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.Bundle002
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP.Mi

variable {R : Type} [CommRing R] {ρ : ℕ}

theorem del_C_mul (p q : Fin ρ) (r : R) (g : Pm R ρ) : del p q (C r * g) = C r * del p q g := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, MvPolynomial.derivation_C, mul_zero, add_zero]

theorem opE_C_mul' (α : R) (p q : Fin ρ) (r : R) (g : Pm R ρ) : opE α p q (C r * g) = C r * opE α p q g := by
  simp only [opE, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, del_C_mul]
  ring

theorem del_det_pow (p q : Fin ρ) (k : ℕ) :
    del p q ((Xm R ρ).det ^ k) = (k : Pm R ρ) * X (q, p) * (Xm R ρ).det ^ k := by
  rw [Derivation.leibniz_pow, delDet, smul_eq_mul, nsmul_eq_mul]
  rcases k with _ | k
  · simp
  · rw [pow_succ]
    push_cast
    ring

theorem opE_det_pow_mul (α : R) (p q : Fin ρ) (k : ℕ) (g : Pm R ρ) :
    opE α p q ((Xm R ρ).det ^ k * g) = (Xm R ρ).det ^ k * opE (α + k) p q g := by
  simp only [opE, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, del_det_pow]
  simp only [map_add (f := _), map_natCast]
  ring

theorem foldr_det_pow (α : R) (k : ℕ) (σ : Equiv.Perm (Fin ρ)) (L : List (Fin ρ)) (g : Pm R ρ) :
    (L.foldr (fun j h => opE α j (σ j) ∘ₗ h) LinearMap.id) ((Xm R ρ).det ^ k * g) =
      (Xm R ρ).det ^ k * (L.foldr (fun j h => opE (α + k) j (σ j) ∘ₗ h) LinearMap.id) g := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.foldr_cons, LinearMap.comp_apply, ih, opE_det_pow_mul]

theorem detE_det_pow_mul (α : R) (k : ℕ) (g : Pm R ρ) :
    detE α ((Xm R ρ).det ^ k * g) = (Xm R ρ).det ^ k * detE (α + k) g := by
  simp only [detE, LinearMap.sum_apply, LinearMap.smul_apply, foldr_det_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_smul_comm]

theorem foldr_C_mul (α : R) (r : R) (σ : Equiv.Perm (Fin ρ)) (L : List (Fin ρ)) (g : Pm R ρ) :
    (L.foldr (fun j h => opE α j (σ j) ∘ₗ h) LinearMap.id) (C r * g) =
      C r * (L.foldr (fun j h => opE α j (σ j) ∘ₗ h) LinearMap.id) g := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.foldr_cons, LinearMap.comp_apply, ih, opE_C_mul']

theorem detE_C_mul (α : R) (r : R) (g : Pm R ρ) : detE α (C r * g) = C r * detE α g := by
  simp only [detE, LinearMap.sum_apply, LinearMap.smul_apply, foldr_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_smul_comm]

theorem iter : Iter := by
  intro R _ ρ α N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih]
    have hc : (∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (C α + (l : Pm R ρ) - (i : Pm R ρ))) =
        C (∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (α + (l : R) - (i : R))) := by
      simp [map_prod]
    set r := ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (α + (l : R) - (i : R))
    have h1 : (C r : Pm R ρ) = C r * 1 := (mul_one _).symm
    rw [hc, mul_comm, detE_det_pow_mul, h1, detE_C_mul, core]
    rw [Finset.prod_range_succ, hc]
    simp only [map_prod, map_sub, map_add (f := _), map_natCast]
    ring

end PositivityTheory.Rg.Sw.SP.Mi
end
end

section

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

theorem hasDerivAt_eval {ι : Type} [Fintype ι] [DecidableEq ι] (g : ℂ → ι → ℂ) (g' : ι → ℂ)
    (hg : ∀ k, HasDerivAt (fun t => g t k) (g' k) 0) (P : MvPolynomial ι ℂ) :
    HasDerivAt (fun t => MvPolynomial.eval (g t) P)
      (∑ k, MvPolynomial.eval (g 0) (MvPolynomial.pderiv k P) * g' k) 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const (0 : ℂ) a
  | add p q hp hq =>
    have e1 : (fun t => MvPolynomial.eval (g t) (p + q)) =
        fun t => MvPolynomial.eval (g t) p + MvPolynomial.eval (g t) q := by
      funext t; rw [map_add (f := _)]
    rw [e1]
    refine (hp.add hq).congr_deriv ?_
    simp only [map_add (f := _), add_mul, Finset.sum_add_distrib]
  | mul_X p k0 hp =>
    have h := hp.mul (hg k0)
    have e1 : (fun t => MvPolynomial.eval (g t) (p * MvPolynomial.X k0)) =
        fun t => MvPolynomial.eval (g t) p * g t k0 := by
      funext t; rw [map_mul, MvPolynomial.eval_X]
    rw [e1]
    refine h.congr_deriv ?_
    symm
    simp only [Derivation.leibniz, MvPolynomial.pderiv_X, smul_eq_mul, map_add (f := _), map_mul, MvPolynomial.eval_X,
      add_mul, Finset.sum_add_distrib]
    have e : ∑ k, MvPolynomial.eval (g 0) p * MvPolynomial.eval (g 0) ((Pi.single k (1 : MvPolynomial ι ℂ) : ι → MvPolynomial ι ℂ) k0) * g' k =
        MvPolynomial.eval (g 0) p * g' k0 := by
      rw [Finset.sum_eq_single k0]
      · simp
      · intro b _ hb
        simp [Pi.single_apply, Ne.symm hb]
      · simp
    rw [e, Finset.sum_mul]
    have e2 : ∑ k, g 0 k0 * MvPolynomial.eval (g 0) (MvPolynomial.pderiv k p) * g' k =
        ∑ k, MvPolynomial.eval (g 0) (MvPolynomial.pderiv k p) * g' k * g 0 k0 :=
      Finset.sum_congr rfl fun k _ => by ring
    rw [e2]
    ring

def cB (s : ℂ) (b : Bool) : ℂ := if b then Complex.I * s else -(Complex.I * s)

def alB (m : ℕ) (b : Bool) : Polynomial ℂ := if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X

theorem smulC (a : ℂ) (P : Fm n) : a • P = MvPolynomial.C (Polynomial.C a) * P := by
  rw [Algebra.smul_def, MvPolynomial.algebraMap_apply, Polynomial.algebraMap_apply]
  rfl

def multPart (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) : Fm n →ₗ[ℂ] Fm n :=
  (-(cB s b)) • (LinearMap.mulLeft ℂ (MvPolynomial.C (alB m b) * yv b l k)).restrictScalars ℂ

def derPart (s : ℂ) (b : Bool) (k l : Fin n) : Fm n →ₗ[ℂ] Fm n :=
  ∑ a : Fin n, ∑ d : Fin n, (-(cB s b)) •
    (LinearMap.mulLeft ℂ (yv b a k * yv b l d) ∘ₗ (MvPolynomial.pderiv (b, a, d)).toLinearMap.restrictScalars ℂ)

theorem opH_eq (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) : opH s m b k l = multPart s m b k l + derPart s b k l := by
  cases b <;> rfl

theorem multPart_apply (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) (Q : Fm n) :
    multPart s m b k l Q = MvPolynomial.C (Polynomial.C (-(cB s b))) * (MvPolynomial.C (alB m b) * yv b l k * Q) := by
  rw [multPart, LinearMap.smul_apply, smulC]
  rfl

theorem derPart_apply (s : ℂ) (b : Bool) (k l : Fin n) (Q : Fm n) :
    derPart s b k l Q = ∑ a : Fin n, ∑ d : Fin n, MvPolynomial.C (Polynomial.C (-(cB s b))) *
      (yv b a k * yv b l d * MvPolynomial.pderiv (b, a, d) Q) := by
  rw [derPart, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [LinearMap.smul_apply, smulC]
  rfl

end PositivityTheory.Rg.Sw.SP
end
end

section

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP

variable {n : ℕ}

abbrev wz (n i : ℕ) : Fm n := MvPolynomial.C (Polynomial.X ^ i)

theorem divZ_iff (i : ℕ) (Q : Fm n) : DivZ i Q ↔ ∃ R : Fm n, Q = R * wz n i := by
  constructor
  · intro h
    have hmem : Q ∈ Ideal.map (MvPolynomial.C : Polynomial ℂ →+* Fm n)
        (Ideal.span {(Polynomial.X ^ i : Polynomial ℂ)}) := by
      rw [MvPolynomial.mem_map_C_iff]
      intro e
      exact Ideal.mem_span_singleton.mpr (h e)
    rw [Ideal.map_span, Set.image_singleton] at hmem
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
    exact ⟨a, ha.symm⟩
  · rintro ⟨R, rfl⟩ e
    rw [mul_comm, MvPolynomial.coeff_C_mul]
    exact dvd_mul_right _ _

theorem divZ_zero (i : ℕ) : DivZ i (0 : Fm n) := fun e => by simp

theorem divZ_add {i : ℕ} {P Q : Fm n} (hP : DivZ i P) (hQ : DivZ i Q) : DivZ i (P + Q) := fun e => by
  rw [MvPolynomial.coeff_add]; exact dvd_add (hP e) (hQ e)

theorem divZ_mul {i j : ℕ} {P Q : Fm n} (hP : DivZ i P) (hQ : DivZ j Q) : DivZ (i + j) (P * Q) := by
  obtain ⟨R₁, rfl⟩ := (divZ_iff i P).1 hP
  obtain ⟨R₂, rfl⟩ := (divZ_iff j Q).1 hQ
  refine (divZ_iff _ _).2 ⟨R₁ * R₂, ?_⟩
  simp only [wz, pow_add, map_mul]
  ring

def cc (s : ℂ) (b : Bool) : ℂ := if b then Complex.I * s else -(Complex.I * s)

def aa (m : ℕ) (b : Bool) : Polynomial ℂ := if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X

theorem opH_apply (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) (Q : Fm n) :
    opH s m b k l Q = (-(cc s b)) • (MvPolynomial.C (aa m b) * yv b l k * Q) +
      ∑ a : Fin n, ∑ d : Fin n, (-(cc s b)) • (yv b a k * yv b l d * pderiv (b, a, d) Q) := by
  cases b <;>
  simp only [opH, cc, aa, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe,
    Bool.false_eq_true, if_true, if_false]

def RCP (T : Fm n →ₗ[ℂ] Fm n) : Prop := ∀ (R : Fm n) (q : Polynomial ℂ), T (R * MvPolynomial.C q) = T R * MvPolynomial.C q

theorem opH_rcp (s : ℂ) (m : ℕ) (b : Bool) (k l : Fin n) : RCP (opH s m b k l) := by
  intro R q
  have hd : ∀ v, pderiv v (R * MvPolynomial.C q) = pderiv v R * MvPolynomial.C q := by
    intro v
    rw [Derivation.leibniz, pderiv_C, smul_zero, zero_add, smul_eq_mul, mul_comm]
  rw [opH_apply, opH_apply]
  simp only [hd, add_mul, Finset.sum_mul, smul_mul_assoc, mul_assoc]

theorem rcp_comp {T U : Fm n →ₗ[ℂ] Fm n} (hT : RCP T) (hU : RCP U) : RCP (T ∘ₗ U) := fun R q => by
  simp only [LinearMap.comp_apply, hU R q, hT _ q]

theorem rcp_add {T U : Fm n →ₗ[ℂ] Fm n} (hT : RCP T) (hU : RCP U) : RCP (T + U) := fun R q => by
  simp only [LinearMap.add_apply, hT R q, hU R q, add_mul]

theorem divZ_of_rcp {T : Fm n →ₗ[ℂ] Fm n} (hT : RCP T) {i : ℕ} {Q : Fm n} (hQ : DivZ i Q) : DivZ i (T Q) := by
  obtain ⟨R, rfl⟩ := (divZ_iff i Q).1 hQ
  exact (divZ_iff i _).2 ⟨T R, hT R _⟩

def LCP (Q' : Fm n) (T : Fm n →ₗ[ℂ] Fm n) : Prop := ∀ R : Fm n, T (Q' * R) = Q' * T R

theorem opH_false_lcp (s : ℂ) (m : ℕ) (k l : Fin n) {Q' : Fm n}
    (hQ : ∀ a d : Fin n, pderiv (false, a, d) Q' = 0) : LCP Q' (opH s m false k l) := by
  intro R
  have hd : ∀ a d : Fin n, pderiv (false, a, d) (Q' * R) = Q' * pderiv (false, a, d) R := by
    intro a d
    rw [Derivation.leibniz, hQ a d, smul_zero, add_zero, smul_eq_mul]
  rw [opH_apply, opH_apply, mul_add, Finset.mul_sum]
  congr 1
  · rw [mul_smul_comm]; exact congrArg _ (by ring)
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [hd, mul_smul_comm]; exact congrArg _ (by ring)

theorem lcp_comp {Q' : Fm n} {T U : Fm n →ₗ[ℂ] Fm n} (hT : LCP Q' T) (hU : LCP Q' U) : LCP Q' (T ∘ₗ U) := fun R => by
  simp only [LinearMap.comp_apply, hU R, hT _]

theorem lcp_add {Q' : Fm n} {T U : Fm n →ₗ[ℂ] Fm n} (hT : LCP Q' T) (hU : LCP Q' U) : LCP Q' (T + U) := fun R => by
  simp only [LinearMap.add_apply, hT R, hU R, mul_add]

theorem lcp_smul {Q' : Fm n} (c : ℂ) {T : Fm n →ₗ[ℂ] Fm n} (hT : LCP Q' T) : LCP Q' (c • T) := fun R => by
  simp only [LinearMap.smul_apply, hT R, mul_smul_comm]

theorem lcp_id {Q' : Fm n} : LCP Q' (LinearMap.id : Fm n →ₗ[ℂ] Fm n) := fun _ => rfl

theorem lcp_sum {Q' : Fm n} {ι : Type*} (t : Finset ι) (T : ι → Fm n →ₗ[ℂ] Fm n) (hT : ∀ i ∈ t, LCP Q' (T i)) :
    LCP Q' (∑ i ∈ t, T i) := by
  classical
  induction t using Finset.induction_on with
  | empty => intro R; simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha]
    exact lcp_add (hT a (Finset.mem_insert_self a t)) (ih fun i hi => hT i (Finset.mem_insert_of_mem hi))

theorem lcp_foldr {Q' : Fm n} {ρ : ℕ} (f : Fin ρ → Fm n →ₗ[ℂ] Fm n) (hf : ∀ k, LCP Q' (f k)) (L : List (Fin ρ)) :
    LCP Q' (L.foldr (fun k g => f k ∘ₗ g) LinearMap.id) := by
  induction L with
  | nil => exact lcp_id
  | cons a L ih => exact lcp_comp (hf a) ih

theorem lcp_iterate {Q' : Fm n} {T : Fm n →ₗ[ℂ] Fm n} (hT : LCP Q' T) (N : ℕ) (R : Fm n) :
    T^[N] (Q' * R) = Q' * T^[N] R := by
  induction N generalizing R with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hT R, ih]

theorem minorOp_false_lcp (s : ℂ) (m : ℕ) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) {Q' : Fm n}
    (hQ : ∀ a d : Fin n, pderiv (false, a, d) Q' = 0) : LCP Q' (minorOp s m false I J) := by
  unfold minorOp
  refine lcp_sum _ _ fun σ _ => lcp_smul _ (lcp_foldr _ (fun k => opH_false_lcp s m _ _ hQ) _)

def AT (n : ℕ) : Subalgebra (Polynomial ℂ) (Fm n) :=
  Algebra.adjoin (Polynomial ℂ) (Set.range fun v : Fin n × Fin n => (MvPolynomial.X (true, v.1, v.2) : Fm n))

theorem pderiv_false_AT {Q : Fm n} (hQ : Q ∈ AT n) (a d : Fin n) : pderiv (false, a, d) Q = 0 := by
  induction hQ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    exact pderiv_X_of_ne (by simp)
  | algebraMap r => rw [MvPolynomial.algebraMap_eq, pderiv_C]
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
  | mul x y _ _ hx hy => rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]

theorem pderiv_true_AT {Q : Fm n} (hQ : Q ∈ AT n) (a d : Fin n) : pderiv (true, a, d) Q ∈ AT n := by
  classical
  induction hQ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [pderiv_X, Pi.single_apply]
    split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  | algebraMap r => rw [MvPolynomial.algebraMap_eq, pderiv_C]; exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Subalgebra.add_mem _ hx hy
  | mul x y hx' hy' hx hy =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx' hy) (Subalgebra.mul_mem _ hy' hx)

theorem smul_mem_AT (c : ℂ) {Q : Fm n} (hQ : Q ∈ AT n) : c • Q ∈ AT n := by
  rw [← algebraMap_smul (Polynomial ℂ) c Q]
  exact Subalgebra.smul_mem _ hQ _

theorem yv_true_mem (i j : Fin n) : yv true i j ∈ AT n := Algebra.subset_adjoin ⟨(i, j), rfl⟩

theorem opH_true_AT (s : ℂ) (m : ℕ) (k l : Fin n) {Q : Fm n} (hQ : Q ∈ AT n) : opH s m true k l Q ∈ AT n := by
  rw [opH_apply]
  refine Subalgebra.add_mem _ (smul_mem_AT _ ?_) (Subalgebra.sum_mem _ fun a _ => Subalgebra.sum_mem _ fun d _ =>
    smul_mem_AT _ ?_)
  · refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ (yv_true_mem _ _)) hQ
    rw [← MvPolynomial.algebraMap_eq]; exact Subalgebra.algebraMap_mem _ _
  · exact Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (yv_true_mem _ _) (yv_true_mem _ _)) (pderiv_true_AT hQ a d)

theorem foldr_AT {ρ : ℕ} (f : Fin ρ → Fm n →ₗ[ℂ] Fm n) (hf : ∀ k Q, Q ∈ AT n → f k Q ∈ AT n) (L : List (Fin ρ))
    {Q : Fm n} (hQ : Q ∈ AT n) : (L.foldr (fun k g => f k ∘ₗ g) LinearMap.id) Q ∈ AT n := by
  induction L with
  | nil => exact hQ
  | cons a L ih => exact hf a _ ih

theorem minorOp_true_AT (s : ℂ) (m : ℕ) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) {Q : Fm n} (hQ : Q ∈ AT n) :
    minorOp s m true I J Q ∈ AT n := by
  unfold minorOp
  rw [LinearMap.sum_apply]
  exact Subalgebra.sum_mem _ fun σ _ => by
    rw [LinearMap.smul_apply]
    exact smul_mem_AT _ (foldr_AT _ (fun k Q hQ => opH_true_AT s m _ _ hQ) _ hQ)

theorem iterate_AT {T : Fm n →ₗ[ℂ] Fm n} (hT : ∀ Q, Q ∈ AT n → T Q ∈ AT n) (N : ℕ) {Q : Fm n} (hQ : Q ∈ AT n) :
    T^[N] Q ∈ AT n := by
  induction N generalizing Q with
  | zero => exact hQ
  | succ N ih => rw [Function.iterate_succ_apply]; exact ih (hT Q hQ)

end PositivityTheory.Rg.Sw.SP
end
end

section

noncomputable section

open Matrix Filter Topology

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

def Ym (s : ℂ) (B : MC n) : Matrix (Fin n) (Fin n) ℂ := (1 - (Complex.I * s) • Matrix.of B)⁻¹

def Yp (s : ℂ) (B : MC n) : Matrix (Fin n) (Fin n) ℂ := (1 + (Complex.I * s) • Matrix.of B)⁻¹

def vals (s : ℂ) (B : MC n) : Bool × Fin n × Fin n → ℂ := fun k => if k.1 then Yp s B k.2.1 k.2.2 else Ym s B k.2.1 k.2.2

def evQ (s z : ℂ) (Q : Fm n) (B : MC n) : ℂ :=
  MvPolynomial.eval (vals s B) (MvPolynomial.map (Polynomial.evalRingHom z) Q)

def fQ (s z : ℂ) (m : ℕ) (Q : Fm n) (B : MC n) : ℂ := clsC s z m 0 1 B * evQ s z Q B

def HYm : Prop :=
  ∀ (n : ℕ) (s : ℂ) (x v : MC n), (1 - (Complex.I * s) • Matrix.of x).det ≠ 0 → ∀ a d : Fin n,
    HasDerivAt (fun t : ℂ => Ym s (x + t • v) a d) (((Complex.I * s) • (Ym s x * Matrix.of v * Ym s x)) a d) 0

def HYp : Prop :=
  ∀ (n : ℕ) (s : ℂ) (x v : MC n), (1 + (Complex.I * s) • Matrix.of x).det ≠ 0 → ∀ a d : Fin n,
    HasDerivAt (fun t : ℂ => Yp s (x + t • v) a d) ((-(Complex.I * s) • (Yp s x * Matrix.of v * Yp s x)) a d) 0

def HCls : Prop :=
  ∀ (n : ℕ) (s : ℂ), (s = 1 ∨ s = -1) → ∀ (z : ℂ) (m : ℕ) (x v : MC n), x ∈ OmS s →
    HasDerivAt (fun t : ℂ => clsC s z m 0 1 (x + t • v))
      (clsC s z m 0 1 x * (Complex.I * s * ((m : ℂ) + z) * (Ym s x * Matrix.of v).trace -
        Complex.I * s * z * (Yp s x * Matrix.of v).trace)) 0

end PositivityTheory.Rg.Sw.SP
end
end

section

noncomputable section

open MeasureTheory Matrix

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.WR PositivityTheory.Rg.Sw.WR.Z

variable {n : ℕ}

theorem differentiable_class_function_param (s : ℂ) (p q : ℕ) (R : MvPolynomial (Bool × Fin n × Fin n) ℂ) (B : MC n) :
    Differentiable ℂ (fun z : ℂ => clsC s z p q R B) := by
  unfold clsC
  fun_prop

theorem factor (hE : Ext) (hCh : Chain) (hBr : Bridge) {s : ℂ} (hs : s = 1 ∨ s = -1) (m N r : ℕ)
    (hdiv : DivZ r ((cayF (n := n) s m)^[N] 1)) (y : E n) :
    ∃ q : ℂ → ℂ, Differentiable ℂ q ∧ ∀ z, (Delta^[N] (cls s z m 0 1)) y = z ^ r * q z := by
  obtain ⟨hO, hherm, han⟩ := hE n s hs
  set P : Fm n := (cayF (n := n) s m)^[N] 1 with hP
  choose d hd using hdiv
  set v : Bool × Fin n × Fin n → ℂ := fun k => if k.1 then (1 + (Complex.I * s) • Matrix.of (herm y : MC n))⁻¹ k.2.1 k.2.2
    else (1 - (Complex.I * s) • Matrix.of (herm y : MC n))⁻¹ k.2.1 k.2.2 with hv
  refine ⟨fun z => clsC s z m 0 1 (herm y) * ∑ e ∈ P.support, (d e).eval z * ∏ i ∈ e.support, v i ^ e i, ?_, ?_⟩
  · refine (differentiable_class_function_param s m 0 1 _).mul ?_
    exact Differentiable.fun_sum fun e _ => (Polynomial.differentiable _).mul (differentiable_const _)
  · intro z
    have hcls : cls s z m 0 1 = fun y : E n => clsC s z m 0 1 (herm y) := funext fun y => ((han z m 0 1).2 y).symm
    rw [hcls, hCh n (OmS s) (clsC s z m 0 1) hO hherm (han z m 0 1).1 N y, hBr n s hs m N z (herm y) (hherm y)]
    rw [MvPolynomial.eval_map, MvPolynomial.eval₂_eq]
    simp only [← hv, ← hP, Polynomial.coe_evalRingHom]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hd e, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    ring

end PositivityTheory.Rg.Sw.SP
end
end
