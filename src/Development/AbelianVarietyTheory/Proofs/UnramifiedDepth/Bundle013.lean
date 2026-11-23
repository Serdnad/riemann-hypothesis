module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle004
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantCoeffEv
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
import Mathlib.RingTheory.Radical.NatInt
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
import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open Formalism.L2.FormalSeriesBounds

noncomputable section

namespace GlobalTheory.CayleyCapelli

open MvPolynomial Formalism.IncomingBounds ReciprocityTheory.PGsh GlobalTheory.DetPowPairing

variable {σ : Type} {C : Type} [Field C]

theorem wt_eq (A : σ →₀ ℕ) : wt C A = (mfact A : C) := by
  simp [_root_.GlobalTheory.DetPowPairing.wt, mfact, Finsupp.prod, Nat.cast_prod]

theorem mfact_ne_zero [CharZero C] (A : σ →₀ ℕ) : (mfact A : C) ≠ 0 := by
  rw [Nat.cast_ne_zero, mfact, Finsupp.prod]
  exact Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _

theorem jetAt0_coe (P Q : MvPolynomial σ C) :
    jetAt0 P (Q : MvPowerSeries σ C) = pair P Q := by
  rw [pair_eq, jetAt0]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_coe, wt_eq]

theorem pair_diffOp [CharZero C] (B : σ →₀ ℕ) (P Q : MvPolynomial σ C) :
    pair (monomial B (1 : C)) (diffOp P Q) = pair (monomial B (1 : C) * P) Q := by
  classical
  have hinner : ∀ m : σ →₀ ℕ, AddMonoidAlgebra.coeff (∑ a ∈ Q.support, if m ≤ a then
      monomial (a - m) (AddMonoidAlgebra.coeff P m * AddMonoidAlgebra.coeff Q a * ((mfact a : C) / (mfact (a - m) : C))) else 0) B =
      AddMonoidAlgebra.coeff P m * AddMonoidAlgebra.coeff Q (B + m) * ((mfact (B + m) : C) / (mfact B : C)) := by
    intro m
    rw [coeff_sum, Finset.sum_eq_single (B + m)]
    · rw [if_pos (le_add_self), coeff_monomial, add_tsub_cancel_right, if_pos rfl]
    · intro a _ ha
      split_ifs with hma
      · rw [coeff_monomial, if_neg]
        intro hB
        exact ha (by rw [← hB, tsub_add_cancel_of_le hma])
      · simp
    · intro hQ
      rw [notMem_support_iff] at hQ
      rw [hQ, if_pos (le_add_self), coeff_monomial, add_tsub_cancel_right, if_pos rfl, mul_zero, zero_mul]
  have hP : monomial B (1 : C) * P = ∑ m ∈ P.support, monomial (B + m) (AddMonoidAlgebra.coeff P m) := by
    conv_lhs => rw [P.as_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [monomial_mul, one_mul]

  rw [pair_monomial, diffOp, coeff_sum, hP, map_sum, LinearMap.sum_apply, wt_eq, one_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hinner, pair_monomial, wt_eq]
  have := mfact_ne_zero (C := C) B
  field_simp

theorem eq_of_pair [CharZero C] {P Q : MvPolynomial σ C}
    (h : ∀ B : σ →₀ ℕ, pair (monomial B (1 : C)) P = pair (monomial B (1 : C)) Q) : P = Q := by
  ext B
  have hB := h B
  rw [pair_monomial, pair_monomial, one_mul, wt_eq] at hB
  exact mul_left_cancel₀ (mfact_ne_zero B) hB

theorem detL_eq (n : ℕ) : detL C n = rename Sum.inl (cayDet n C) := by
  rw [detL, cayDet, AlgHom.map_det]
  congr 1
  ext b c
  simp [Matrix.mvPolynomialX]

theorem list_rename {ι τ : Type} (g : σ → τ) (hg : Function.Injective g) (f : ι → σ) (l : List ι)
    (Q : MvPolynomial σ C) :
    ((l.map fun j => ((pderiv (g (f j)) : Derivation C _ _) :
        MvPolynomial τ C →ₗ[C] MvPolynomial τ C)).prod : Module.End C (MvPolynomial τ C))
        (rename g Q) =
      rename g (((l.map fun j => ((pderiv (f j) : Derivation C _ _) :
        MvPolynomial σ C →ₗ[C] MvPolynomial σ C)).prod : Module.End C (MvPolynomial σ C)) Q) := by
  induction l with
  | nil => simp
  | cons j l ih =>
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]
    exact pderiv_rename hg _ _

theorem pair_detL (n : ℕ) (P : MvPolynomial (PVar n) C) (Q : MvPolynomial (Fin n × Fin n) C) :
    pair (P * detL C n) (rename Sum.inl Q) = pair P (rename Sum.inl (cayOp n C Q)) := by
  have hσ : ∀ τ : Equiv.Perm (Fin n), pair (P * ∏ i, (X (Sum.inl (τ i, i)) : MvPolynomial (PVar n) C))
      (rename Sum.inl Q) = pair P (rename Sum.inl (cayMono n C τ Q)) := by
    intro τ
    have h1 := pair_list (C := C) (fun j : Fin n => (Sum.inl (τ j, j) : PVar n)) (List.finRange n) P
      (rename Sum.inl Q)
    have h2 := list_rename (C := C) (Sum.inl : Fin n × Fin n → PVar n) Sum.inl_injective
      (fun j : Fin n => (τ j, j)) (List.finRange n) Q
    rw [Fin.prod_univ_def, h1, h2]
    rfl

  rw [detL, Matrix.det_apply', Finset.mul_sum, map_sum, LinearMap.sum_apply, cayOp, LinearMap.sum_apply,
  map_sum, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [LinearMap.smul_apply, map_zsmul, map_zsmul, ← hσ τ, mul_left_comm, ← zsmul_eq_mul, map_zsmul,
    LinearMap.smul_apply]
  rfl

theorem pair_detL_pow (n s : ℕ) (P : MvPolynomial (PVar n) C) :
    pair (P * detL C n) (detL C n ^ (s + 1)) =
      ((∏ c ∈ Finset.range n, (s + 1 + c) : ℕ) : C) * pair P (detL C n ^ s) := by
  have e : detL C n ^ (s + 1) = rename Sum.inl (cayDet n C ^ (s + 1)) := by rw [detL_eq, map_pow]
  rw [e, pair_detL, cayley n C (s + 1), Nat.add_sub_cancel, map_nsmul, map_nsmul,
    nsmul_eq_mul, map_pow, ← detL_eq]

theorem cayleyId : CayleyId := by
  intro K _ _ n s
  refine eq_of_pair fun B => ?_
  rw [pair_diffOp, pair_detL_pow, map_smul, smul_eq_mul]
  push_cast
  rfl

theorem pair_pow_self (n x : ℕ) :
    pair (detL C n ^ x) (detL C n ^ x) =
      ((∏ t ∈ Finset.Icc 1 x, ∏ c ∈ Finset.range n, (t + c) : ℕ) : C) := by
  induction x with
  | zero =>
    rw [pow_zero, ← MvPolynomial.C_1, MvPolynomial.C_apply, pair_monomial, wt_eq]
    simp [mfact]
  | succ x ih =>
    have h := pair_detL_pow n x (detL C n ^ x)
    rw [← pow_succ] at h
    rw [h, ih, Finset.prod_Icc_succ_top (by omega), Nat.cast_mul, mul_comm]

theorem prod_Icc_mul_factorial (x c : ℕ) :
    (∏ t ∈ Finset.Icc 1 x, (t + c)) * c.factorial = (x + c).factorial := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [Finset.prod_Icc_succ_top (by omega), mul_right_comm, ih, show x + 1 + c = (x + c) + 1 by omega,
      Nat.factorial_succ, mul_comm]

theorem prod_eq_capNat (n x : ℕ) :
    (∏ t ∈ Finset.Icc 1 x, ∏ c ∈ Finset.range n, (t + c)) = capNat n x := by
  rw [capNat, Finset.prod_comm]
  refine Finset.prod_congr rfl fun a _ => ?_
  exact (Nat.div_eq_of_eq_mul_left (Nat.factorial_pos a) (prod_Icc_mul_factorial x a).symm).symm

theorem main : F1 ∧ CapacityFactorialProduct := by
  refine ⟨cayleyId, ?_⟩
  intro K _ _ n x
  refine ⟨by rw [jetAt0_coe, pair_pow_self], prod_eq_capNat n x,
    fun c => Nat.factorial_dvd_factorial (by omega), ?_⟩
  rw [← prod_eq_capNat]
  refine Finset.prod_ne_zero_iff.2 fun t ht => Finset.prod_ne_zero_iff.2 fun c _ => ?_
  rw [Finset.mem_Icc] at ht
  omega

end GlobalTheory.CayleyCapelli
end
end

section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.MultiplicativeSeries

open GlobalTheory.GaugeAdjoint

variable {R : Type} [CommRing R] {d m n : ℕ}

theorem ev_mul {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0) (f g : PS R m d) :
    ev a (f * g) = ev a f * ev a g :=
  subst_mul (hasSubst_pts ha) f g

theorem ev_sum {a : Fin m → Pt R n d} (ha : ∀ j i, constantCoeff (a j i) = 0) {ι : Type}
    (t : Finset ι) (f : ι → PS R m d) : ev a (∑ i ∈ t, f i) = ∑ i ∈ t, ev a (f i) := by
  unfold ev

  rw [← coe_substAlgHom (hasSubst_pts ha), map_sum]

theorem ev_self_one (f : PS R 1 d) : ev (n := 1) ![pt R d 0] f = f := by
  have e : (fun q : Fin 1 × Fin d => (![pt R d 0] : Fin 1 → Pt R 1 d) q.1 q.2) = X := by
    funext q
    obtain ⟨j, i⟩ := q
    fin_cases j
    rfl
  rw [ev, e, subst_self]
  rfl

theorem ev_self_two (f : PS R 2 d) : ev (n := 2) ![pt R d 0, pt R d 1] f = f := by
  have e : (fun q : Fin 2 × Fin d => (![pt R d 0, pt R d 1] : Fin 2 → Pt R 2 d) q.1 q.2) = X := by
    funext q
    obtain ⟨j, i⟩ := q
    fin_cases j <;> rfl
  rw [ev, e, subst_self]
  rfl

theorem axis_law (G : FGLaw R d) :
    (fun i => ev (n := 1) ![pt R d 0, 0] (G.F i)) = pt R d 0 := by
  funext i
  rw [← G.comm i, ev_ev_two (const_pt 1) (const_pt 0) const_axis, axis_pt_zero, axis_pt_one,
    G.unit i]
  rfl

theorem partial_eq (G : FGLaw R d) (s : PS R 1 d)
    (h : ev (n := 2) ![G.add (pt R d 0) (pt R d 1)] s =
      ev (n := 2) ![pt R d 0] s * ev (n := 2) ![pt R d 1] s) (i : Fin d) :
    ∑ j, ev (n := 1) ![pt R d 0, 0] (pderiv (R := R) ((1 : Fin 2), i) (G.F j)) *
        pderiv (R := R) ((0 : Fin 1), j) s =
      C (coeff (Finsupp.single ((0 : Fin 1), i) 1) s) * s := by
  have hadd : G.add (pt R (n := 2) d 0) (pt R d 1) = G.F := funext fun j => ev_self_two _
  rw [hadd] at h
  have h0 : pderiv (R := R) ((1 : Fin 2), i) (ev (n := 2) ![pt R d 0] s) = 0 := by
    rw [pderiv_ev (const_one (const_pt 0))]
    simp [pderiv_pt]
  have h1 : pderiv (R := R) ((1 : Fin 2), i) (ev (n := 2) ![pt R d 1] s) =
      ev (n := 2) ![pt R d 1] (pderiv (R := R) ((0 : Fin 1), i) s) := by
    rw [pderiv_ev (const_one (const_pt 1))]
    simp [pderiv_pt]
  have hd := congrArg (fun f => ev (n := 1) ![pt R d 0, 0] (pderiv (R := R) ((1 : Fin 2), i) f)) h
  beta_reduce at hd
  rw [Derivation.leibniz, h0, h1, smul_zero, add_zero, smul_eq_mul, ev_mul const_axis,
    axis_pderiv, ev_ev_one (const_pt 0) const_axis, axis_pt_zero, ev_self_one,
    pderiv_ev (const_one G.const), Fin.sum_univ_one, ev_sum const_axis] at hd
  rw [mul_comm, ← hd]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ev_mul const_axis, ev_ev_one G.const const_axis, axis_law, ev_self_one, mul_comm]
  rfl

theorem main :
  (∀ (R : Type) [CommRing R] (d : ℕ) (G : FGLaw R d) (s : PS R 1 d),
    ev (n := 2) ![G.add (pt R d 0) (pt R d 1)] s = ev (n := 2) ![pt R d 0] s * ev (n := 2) ![pt R d 1] s →
    ∀ u : Fin d → R, Dof G.F u s = C (∑ i, u i * coeff (Finsupp.single ((0 : Fin 1), i) 1) s) * s) := by
  intro R _ d G s h u

  rw [Dof, map_sum, Finset.sum_mul]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, mul_assoc, ← partial_eq G s h i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => mul_assoc _ _ _

end GlobalTheory.MultiplicativeSeries
end
