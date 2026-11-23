module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle003
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AxisPderivComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle008
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle003
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SumSplitsEvalTwoWord
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle005

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.ChartTrans

namespace GlobalTheory.HomChain

variable {k : Type} [CommRing k] {d : ℕ}

theorem law_right_unit (G : FGLaw k d) (i : Fin d) :
    ev (n := 1) ![pt k (n := 1) d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS k 1 d) := by
  have hs : ∀ j, GP ((![pt k (n := 2) d 1, pt k (n := 2) d 0] : Fin 2 → Pt k 2 d) j) :=
    pair_points_zero_constant (gp_pt 1) (gp_pt 0)
  rw [← G.comm i, gt_ev_ev' _ _ axis_GP hs, eval_pair_points, evP_pt _ axis_GP, evP_pt _ axis_GP]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact G.unit i

theorem dof_hom (G G' : FGLaw k d) (α : Pt k 1 d) (hα : ∀ i, constantCoeff (α i) = 0)
    (hom : comp1 α (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      G'.add (comp1 α (pt k (n := 2) d 0)) (comp1 α (pt k (n := 2) d 1)))
    (u : Fin d → k) (g : PS k 1 d) :
    Dof G.F u (ev (n := 1) ![α] g) = ev (n := 1) ![α] (Dof G'.F ((dLin α).mulVec u) g) := by
  have hφ : GP α := hα
  have h0 : GP (comp1 α (pt k (n := 2) d 0)) := gp_comp1 α _ hφ (gp_pt 0)
  have h1 : GP (comp1 α (pt k (n := 2) d 1)) := gp_comp1 α _ hφ (gp_pt 1)
  have hΦ := pair_points_zero_constant h0 h1
  have hF : GP G.F := G.const
  have hF' : GP G'.F := G'.const
  have eF : G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1) = G.F := by
    funext i
    have e : (![pt k (n := 2) d 0, pt k (n := 2) d 1] : Fin 2 → Pt k 2 d) = pt k d := by
      funext j; fin_cases j <;> rfl
    change ev ![pt k (n := 2) d 0, pt k (n := 2) d 1] (G.F i) = _
    rw [e]
    exact congrFun (MvPowerSeries.subst_self (R := k) (σ := Fin 2 × Fin d)) (G.F i)
  have key : ev (n := 2) ![G.F] (ev (n := 1) ![α] g) =
      ev ![comp1 α (pt k (n := 2) d 0), comp1 α (pt k (n := 2) d 1)] (ev (n := 2) ![G'.F] g) := by
    rw [gt_ev_ev' _ _ (single_point_zero_constant hF) (single_point_zero_constant hφ), vec1, gt_ev_ev' _ _ hΦ (single_point_zero_constant hF'), vec1]
    have : evP ![G.F] α = evP ![comp1 α (pt k (n := 2) d 0), comp1 α (pt k (n := 2) d 1)] G'.F := by
      rw [eF] at hom
      exact hom
    rw [this]
  have pderiv_ev {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j))
      (f : PS k m d) (v : Fin n × Fin d) :
      pderiv (R := k) v (ev V f) =
        ∑ j : Fin m, ∑ l : Fin d, ev V (pderiv (R := k) (j, l) f) * pderiv (R := k) v (V j l) := by
    unfold ev
    rw [GlobalTheory.FormalCalc.pderiv_subst (gt_hasSubst V hV), Fintype.sum_prod_type]
  have dof_eq (L : FGLaw k d) (v : Fin d → k) (f : PS k 1 d) :
      Dof L.F v f = ∑ i, C (v i) *
        ev ![pt k (n := 1) d 0, 0] (pderiv (R := k) ((1 : Fin 2), i) (ev ![L.F] f)) := by
    have hL := single_point_zero_constant L.const
    have eval_axis (h : PS k 1 d) : ev ![pt k (n := 1) d 0, 0] (ev ![L.F] h) = h := by
      rw [gt_ev_ev' _ _ axis_GP hL, vec1,
        show evP ![pt k (n := 1) d 0, 0] L.F = pt k d 0 from funext (law_right_unit L),
        gt_ev_pt_self]
    unfold Dof
    simp only [pderiv_ev _ hL, Fin.sum_univ_one, ev_sum _ axis_GP, gt_ev_mul _ axis_GP,
      eval_axis, Finset.mul_sum, Finset.sum_mul, Matrix.cons_val_zero]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have axis_pderiv_comp (H : PS k 2 d) (i : Fin d) :
      ev ![pt k (n := 1) d 0, 0] (pderiv (R := k) ((1 : Fin 2), i)
        (ev ![comp1 α (pt k (n := 2) d 0), comp1 α (pt k (n := 2) d 1)] H)) =
      ∑ l, C (dLin α l i) *
        ev ![α] (ev ![pt k (n := 1) d 0, 0] (pderiv (R := k) ((1 : Fin 2), l) H)) := by
    have eval_comp (K : PS k 2 d) :
        ev ![pt k (n := 1) d 0, 0]
          (ev ![comp1 α (pt k (n := 2) d 0), comp1 α (pt k (n := 2) d 1)] K) =
        ev ![α] (ev ![pt k (n := 1) d 0, 0] K) := by
      rw [gt_ev_ev' _ _ axis_GP hΦ, eval_pair_points, evP_comp1 _ axis_GP α _ (gp_pt 0),
        evP_comp1 _ axis_GP α _ (gp_pt 1), evP_pt _ axis_GP, evP_pt _ axis_GP,
        gt_ev_ev' _ _ (single_point_zero_constant hφ) axis_GP, eval_pair_points,
        evP_pt _ (single_point_zero_constant hφ), evP_zero _ (single_point_zero_constant hφ)]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [gt_comp1_pt_right, gt_comp1_zero α hφ]
    have pderiv_comp_pt (b : Fin 2) (l : Fin d) :
        pderiv (R := k) ((1 : Fin 2), i) (comp1 α (pt k (n := 2) d b) l) =
          if (1 : Fin 2) = b then
            ev ![pt k (n := 2) d b] (pderiv (R := k) ((0 : Fin 1), i) (α l)) else 0 := by
      change pderiv (R := k) ((1 : Fin 2), i) (ev ![pt k (n := 2) d b] (α l)) = _
      rw [pderiv_ev _ (single_point_zero_constant (gp_pt b)), Fin.sum_univ_one]
      simp only [Matrix.cons_val_zero, pt]
      split_ifs with h
      · subst b
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          rw [pderiv_X_of_ne (by simpa using hj), mul_zero]
        · simp
      · refine Finset.sum_eq_zero fun j _ => ?_
        rw [pderiv_X_of_ne (fun h' => h (congrArg Prod.fst h').symm), mul_zero]
    have eval_linear (l : Fin d) : ev ![pt k (n := 1) d 0, 0]
        (ev ![pt k (n := 2) d 1] (pderiv (R := k) ((0 : Fin 1), i) (α l))) = C (dLin α l i) := by
      rw [gt_ev_ev' _ _ axis_GP (single_point_zero_constant (gp_pt 1)), vec1, evP_pt _ axis_GP]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [ev_at_zero, ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv]
      simp [dLin]
    rw [pderiv_ev _ hΦ, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pderiv_comp_pt,
      one_ne_zero, if_false, if_true, mul_zero, Finset.sum_const_zero, zero_add]
    rw [ev_sum _ axis_GP]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [gt_ev_mul _ axis_GP, eval_comp, eval_linear, mul_comm]
  rw [dof_eq G, dof_eq G', key,
    ev_sum _ (single_point_zero_constant hφ)]
  simp only [axis_pderiv_comp, ev_C_mul _ (single_point_zero_constant hφ)]

  simp only [Matrix.mulVec, dotProduct, map_sum,
  map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.HomChain
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory

theorem wickVanish_of_half : GE.HalfSt → G2.WickOperatorVanishing := by
  intro hH k _ _ d F ι _ u c P q hc hq0 hq1 hq2 hP m G
  obtain ⟨Y, hY⟩ := GE.exp_cut m q hq0 0
  have hY' : FB.expS k (m • q) = 1 + q * Y := by
    rw [hY]
    simp
  rw [hY', mul_add, mul_one, GE.dpolyOf_add_f, map_add (f := _),
    show G * (q * Y) = (G * Y) * q by ring, hH k d F ι u c q hc hq0 hq1 hq2 P (G * Y), hP,
    GE.dpolyOf_zero_P, map_zero, mul_zero, add_zero]

end GlobalTheory
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.HalfIdentity

variable {k : Type} [CommRing k] {d : ℕ}

section

variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)

theorem T_replicate (n : ℕ) (l : ι) (f : PS k 1 d) :
    G2.T F u (List.replicate n l) f = (Dof F (u l))^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, G2.T_cons, ih, Function.iterate_succ_apply']

theorem foldr_eq_T_word (L : List ι) (m : ι →₀ ℕ) (f : PS k 1 d) :
    L.foldr (fun l g => (Dof F (u l))^[m l] g) f = G2.T F u (G2.word L m) f := by
  induction L with
  | nil => rfl
  | cons l L ih => rw [List.foldr_cons, ih, G2.word_cons, G2.T_append, T_replicate]

variable [Fintype ι]

theorem dmonOf_eq_T_word (m : ι →₀ ℕ) (f : PS k 1 d) :
    DmonOf F u m f = G2.T F u (G2.word (Finset.univ : Finset ι).toList m) f :=
  foldr_eq_T_word F u _ m f

theorem dpolyOf_monomial (m : ι →₀ ℕ) (a : k) (f : PS k 1 d) :
    DpolyOf F u (MvPolynomial.monomial m a) f = C a * DmonOf F u m f := by
  classical
  rw [GE.dpolyOf_eq_sum_of_subset F u _ {m} MvPolynomial.support_monomial_subset,
    Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

theorem secondOrder_add (c : ι → ι → k) (P Q : MvPolynomial ι k) :
    secondOrder k c (P + Q) = secondOrder k c P + secondOrder k c Q := by
  simp only [secondOrder, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem secondOrder_monomial (c : ι → ι → k) (m : ι →₀ ℕ) (a : k) :
    secondOrder k c (MvPolynomial.monomial m a) =
      ∑ x, ∑ y, MvPolynomial.monomial (m - Finsupp.single y 1 - Finsupp.single x 1)
        (a * (c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k))) := by
  unfold secondOrder
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.pderiv_monomial, MvPolynomial.C_mul_monomial]
  congr 1
  push_cast
  ring

end

theorem halfSt : GE.HalfSt := by
  intro k _ _ d F ι _ u c q hc hq0 hq1 hq2 P A
  classical
  induction P using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
    rw [secondOrder_add, GE.dpolyOf_add_P, GE.dpolyOf_add_P, map_add (f := _), map_add (f := _), hP, hQ, mul_add]
  | monomial m a =>
    have h2 : algebraMap ℚ k (1 / 2) * 2 = 1 := by
      rw [show (2 : k) = algebraMap ℚ k 2 from (map_ofNat _ 2).symm, ← map_mul]
      norm_num
    have key := G2.sum_splits_evalTwo_word c hc (Finset.univ : Finset ι).toList (Finset.nodup_toList _) m
      (fun w => constantCoeff (G2.T F u w A))
    simp only [Finset.sum_map_toList] at key

    rw [dpolyOf_monomial, dmonOf_eq_T_word, map_mul, constantCoeff_C,
    G2.cc_T_mul_q c F u q hq0 hq1 hq2, secondOrder_monomial, GE.dpolyOf_sum_P, map_sum]
    have hR : ∑ x, constantCoeff (DpolyOf F u
        (∑ y, MvPolynomial.monomial (m - Finsupp.single y 1 - Finsupp.single x 1)
          (a * (c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k)))) A) =
        a * ∑ x, ∑ y, c x y * ((m y * (m - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k) *
          constantCoeff (G2.T F u (G2.word (Finset.univ : Finset ι).toList
            (m - Finsupp.single y 1 - Finsupp.single x 1)) A) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_

      rw [GE.dpolyOf_sum_P, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [dpolyOf_monomial, dmonOf_eq_T_word, map_mul, constantCoeff_C, mul_assoc]
    rw [hR, ← key]
    linear_combination (-(a * ((G2.splits (G2.word (Finset.univ : Finset ι).toList m)).map
      (fun p => constantCoeff (G2.T F u p.1 A) * G2.ev2 c p.2)).sum)) * h2

end GlobalTheory.HalfIdentity
end
end

section

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.LogLinear

variable {k : Type} [CommRing k] {d : ℕ}

theorem eq_zero_of_additive [Algebra ℚ k] (G : FGLaw k d) (g : PS k 1 d)
    (hadd : ev (n := 2) ![G.add (pt k d 0) (pt k d 1)] g =
      ev (n := 2) ![pt k d 0] g + ev (n := 2) ![pt k d 1] g)
    (hlin : ∀ i, coeff (Finsupp.single ((0 : Fin 1), i) 1) g = 0) : g = 0 := by
  have hc {n : ℕ} (x : Pt k n d) (y : Fin 0 → Pt k n d) :
      (Fin.cons x y : Fin (0 + 1) → Pt k n d) = ![x] := by
    funext j
    fin_cases j
    rfl
  refine GlobalTheory.AdditiveSeries.eq_zero_of_additive_of_pderiv k d G 0 g ?_ fun i => ?_
  · simpa only [hc] using hadd
  · rw [hc]
    ext m
    obtain rfl : m = 0 := Subsingleton.elim _ _
    rw [coeff_zero_eq_constantCoeff_apply, gt_const_ev_eq _ (single_point_zero_constant gp_zero₂),
      ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]
    simp [hlin i]

theorem ev_sum_C_mul {m n : ℕ} (V : Fin m → Pt k n d) (hV : ∀ j, GP (V j)) (c : Fin d → k)
    (f : Fin d → PS k m d) : ev V (∑ j, C (c j) * f j) = ∑ j, C (c j) * ev V (f j) := by
  unfold ev

  rw [← coe_substAlgHom (gt_hasSubst V hV), map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, coe_substAlgHom, subst_C]

theorem dLin_comp1 (φ ψ : Pt k 1 d) (hψ : GP ψ) : dLin (comp1 φ ψ) = dLin φ * dLin ψ := by
  ext i j
  refine (FormalCalc.coeff_single_subst
    (a := fun p : Fin 1 × Fin d => (![ψ] : Fin 1 → Pt k 1 d) p.1 p.2)
    (fun p => single_point_zero_constant hψ p.1 p.2) (φ i) _).trans ?_
  rw [Fintype.sum_prod_type, Fin.sum_univ_one, Matrix.mul_apply]
  rfl

theorem germ_comp_additive_at_points {n : ℕ} (G : FGLaw k d) (ψ : Pt k 1 d)
    (hψ : comp1 ψ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ψ (pt k (n := 2) d 0) + comp1 ψ (pt k (n := 2) d 1))
    (a b : Pt k n d) (ha : GP a) (hb : GP b) :
    comp1 ψ (G.add a b) = comp1 ψ a + comp1 ψ b := by
  have hV := pair_points_zero_constant ha hb
  have e := congrArg (evP ![a, b]) hψ
  have e2 : ∀ u v : Pt k 2 d, evP ![a, b] (u + v) = evP ![a, b] u + evP ![a, b] v := fun u v =>
    funext fun i => gt_ev_add _ hV _ _
  rw [e2, evP_comp1 _ hV _ _ (gp_addOf _ G.const _ _ (gp_pt 0) (gp_pt 1)),
    evP_addOf _ hV _ _ _ (gp_pt 0) (gp_pt 1), evP_comp1 _ hV _ _ (gp_pt 0),
    evP_comp1 _ hV _ _ (gp_pt 1), evP_pt _ hV, evP_pt _ hV] at e
  exact e

theorem formalGroup_log_endomorphism_linear :
    ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (ℓ α : Pt k 1 d),
      (∀ i, MvPowerSeries.constantCoeff (ℓ i) = 0) → dLin ℓ = 1 →
      comp1 ℓ (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
        comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) →
      (∀ i, MvPowerSeries.constantCoeff (α i) = 0) →
      comp1 α (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
        G.add (comp1 α (pt k (n := 2) d 0)) (comp1 α (pt k (n := 2) d 1)) →
      ∀ i, comp1 ℓ α i = ∑ j, MvPowerSeries.C (dLin α i j) * ℓ j := by
  intro k _ _ d G ℓ α _ h1 hadd hα hhom i
  have hS : GP (G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) :=
    gp_addOf _ G.const _ _ (gp_pt _) (gp_pt _)
  have hev (a : Pt k 2 d) (ha : GP a) :
      ev ![a] (comp1 ℓ α i - ∑ j, C (dLin α i j) * ℓ j) =
        comp1 ℓ (comp1 α a) i - ∑ j, C (dLin α i j) * comp1 ℓ a j := by
    rw [gt_ev_sub _ (single_point_zero_constant ha), ev_sum_C_mul _ (single_point_zero_constant ha), ← gt_comp1_comp1 ℓ α hα a ha]
    rfl
  rw [← sub_eq_zero]
  refine eq_zero_of_additive G _ ?_ fun l => ?_
  · rw [hev _ hS, hev _ (gp_pt _), hev _ (gp_pt _), hhom, hadd,
      germ_comp_additive_at_points G ℓ hadd _ _ (gp_comp1 α _ hα (gp_pt _)) (gp_comp1 α _ hα (gp_pt _))]
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  · have h2 : dLin (comp1 ℓ α) i l = (dLin α * dLin ℓ) i l := by
      rw [dLin_comp1 ℓ α hα, h1, one_mul, mul_one]

    rw [map_sub, map_sum, sub_eq_zero]
    simp only [coeff_C_mul]
    exact h2

end GlobalTheory.LogLinear
end
end
