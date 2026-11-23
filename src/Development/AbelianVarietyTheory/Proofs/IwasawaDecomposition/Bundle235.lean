module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle192
public import Formalism.DegreeFormula.PointDegree.PermExpInj
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle225
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumSumEqSumPair
public import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExtremalUnitVectorSameHighestImage
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle008

@[expose] public section

section

noncomputable section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric
open Classical

namespace GlobalTheory.Schubert.RelKill

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem esymm_cons_succ {R : Type*} [CommSemiring R] (a : R) (s : Multiset R) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]

theorem coeff_prod_one_add {R : Type*} [CommSemiring R] (s : Multiset R) (n : ℕ) :
    ((s.map fun a => (1 + Polynomial.C a * Polynomial.X : Polynomial R)).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, Polynomial.coeff_add,
      Polynomial.coeff_C_mul]
    cases n with
    | zero => simp [ih, Multiset.esymm]
    | succ n => rw [Polynomial.coeff_X_mul, ih, ih, esymm_cons_succ]

theorem esymm_add {R : Type*} [CommSemiring R] (s t : Multiset R) (n : ℕ) :
    (s + t).esymm n = ∑ i ∈ Finset.range (n + 1), s.esymm i * t.esymm (n - i) := by
  rw [← coeff_prod_one_add, Multiset.map_add (f := _), Multiset.prod_add, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_add]

theorem univ_map_eq_range {R : Type*} [Zero R] (m : ℕ) (f : Fin m → R) :
    (Finset.univ : Finset (Fin m)).val.map f =
      (Multiset.range m).map (fun i => if h : i < m then f ⟨i, h⟩ else 0) := by
  have h1 : Multiset.range m = (Finset.univ : Finset (Fin m)).val.map Fin.val := by
    rw [Fin.univ_val_map, List.ofFn_eq_map, List.map_coe_finRange_eq_range]; rfl
  rw [h1, Multiset.map_map]
  refine Multiset.map_congr rfl fun i _ => ?_
  simp [i.2]

variable {H : Host E} (Dw : Datum H)

def rootSeq (τ : GlobalTheory.AllWt.Psi H) (i : ℕ) : MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ :=
  if h : i < Dw.p + Dw.q then X (τ, ⟨i, h⟩) else 0

theorem flagMap_chernRoots_X (x : E →+* ℂ) (a : ℕ) :
    flagMap Dw (chernRoots Dw.mult (X (x, a))) =
      ((Finset.univ : Finset (Fin (Dw.mult x))).val.map (fun i => flagRoot Dw ⟨x, i⟩)).esymm a := by
  rw [chernRoots, aeval_X, flagMap, aeval_rename, aeval_esymm_eq_multiset_esymm]
  rfl

theorem roots_mem (τ : GlobalTheory.AllWt.Psi H) :
    (Finset.univ : Finset (Fin (Dw.mult τ.1))).val.map (fun i => flagRoot Dw ⟨τ.1, i⟩) =
      (Multiset.range Dw.p).map (rootSeq Dw τ) := by
  rw [univ_map_eq_range]
  have hm := GlobalTheory.PointChern.mult_of_mem Dw τ.2
  rw [show Multiset.range (Dw.mult τ.1) = Multiset.range Dw.p by rw [hm]]
  refine Multiset.map_congr rfl fun i hi => ?_
  rw [Multiset.mem_range] at hi
  have hi' : i < Dw.mult τ.1 := by omega
  have hi2 : i < Dw.p + Dw.q := by omega
  rw [dif_pos hi', rootSeq, dif_pos hi2, flagRoot, dif_pos τ.2]

theorem range_reflect (q : ℕ) : (Multiset.range q).map (fun i => q - 1 - i) = Multiset.range q := by
  have hinj : ∀ x ∈ Multiset.range q, ∀ y ∈ Multiset.range q, q - 1 - x = q - 1 - y → x = y := by
    intro x hx y hy h; rw [Multiset.mem_range] at hx hy; omega
  refine (Multiset.Nodup.ext ((Multiset.nodup_range q).map_on hinj) (Multiset.nodup_range q)).2 fun a => ?_
  simp only [Multiset.mem_map, Multiset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro ha; exact ⟨q - 1 - a, by omega, by omega⟩

theorem roots_conj (τ : GlobalTheory.AllWt.Psi H) :
    (Finset.univ : Finset (Fin (Dw.mult (conjEmb τ.1)))).val.map
        (fun i => flagRoot Dw ⟨conjEmb τ.1, i⟩) =
      ((Multiset.range Dw.q).map (fun i => rootSeq Dw τ (Dw.p + i))).map Neg.neg := by
  rw [univ_map_eq_range]
  have hn := GlobalTheory.AllWt.conj_not_mem τ
  have hm := GlobalTheory.PointChern.mult_of_not_mem Dw hn
  rw [show Multiset.range (Dw.mult (conjEmb τ.1)) = Multiset.range Dw.q by rw [hm]]
  conv_rhs => rw [← range_reflect Dw.q, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun i hi => ?_
  rw [Multiset.mem_range] at hi
  have hi' : i < Dw.mult (conjEmb τ.1) := by omega
  have hi2 : Dw.p + (Dw.q - 1 - i) < Dw.p + Dw.q := by omega
  have h' : conjEmb (conjEmb τ.1) (H.rt : E) = H.rt0 := by
    rw [GlobalTheory.AllWt.conjEmb_conjEmb]; exact τ.2
  have e : (⟨conjEmb (conjEmb τ.1), h'⟩ : GlobalTheory.AllWt.Psi H) = τ :=
    Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb _)
  simp only [dif_pos hi', flagRoot, dif_neg hn, Function.comp_apply, rootSeq, dif_pos hi2, e]

theorem rename_esymm (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) :
    rename (fun i : Fin (Dw.p + Dw.q) => (τ, i)) (esymm (Fin (Dw.p + Dw.q)) ℝ k) =
      ((Multiset.range Dw.p).map (rootSeq Dw τ) +
        (Multiset.range Dw.q).map (fun i => rootSeq Dw τ (Dw.p + i))).esymm k := by
  rw [← aeval_X_left_apply (rename _ _), aeval_rename, aeval_esymm_eq_multiset_esymm, univ_map_eq_range, Multiset.range_add, Multiset.map_add (f := _),
    Multiset.map_map]
  rfl

theorem flagMap_relPoly (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) :
    flagMap Dw (chernRoots Dw.mult (GlobalTheory.PointChern.relPoly τ k)) =
      rename (fun i : Fin (Dw.p + Dw.q) => (τ, i)) (esymm (Fin (Dw.p + Dw.q)) ℝ k) := by

  rw [rename_esymm, esymm_add, GlobalTheory.PointChern.relPoly, map_sum, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_mul, map_mul, map_mul, flagMap_chernRoots_X, flagMap_chernRoots_X, roots_mem, roots_conj,
    Multiset.esymm_neg]
  have hC : flagMap Dw (chernRoots Dw.mult (C ((-1 : ℝ) ^ (k - a)))) = (-1) ^ (k - a) := by
    simp [flagMap, chernRoots]
  rw [hC]
  have h1 : ((-1 : MvPolynomial (GlobalTheory.AllWt.Psi H × Fin (Dw.p + Dw.q)) ℝ) ^ (k - a)) * (-1) ^ (k - a) = 1 := by
    rw [← mul_pow]; simp
  linear_combination (((Multiset.range Dw.p).map (rootSeq Dw τ)).esymm a *
    ((Multiset.range Dw.q).map (fun i => rootSeq Dw τ (Dw.p + i))).esymm (k - a)) * h1

end GlobalTheory.Schubert.RelKill

namespace GlobalTheory.Schubert

end GlobalTheory.Schubert
end
end

section

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

noncomputable section

namespace GlobalTheory.SchubertPoint

theorem sign_revPerm_real (n : ℕ) :
    ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤ) : ℝ) = (-1) ^ (∑ i : Fin n, (i : ℕ)) := by
  induction n with
  | zero =>
    rw [Subsingleton.elim (Fin.revPerm : Equiv.Perm (Fin 0)) 1]; simp
  | succ n ih =>
    have key : finRotate (n + 1) * (Fin.revPerm : Equiv.Perm (Fin (n + 1))) =
        Equiv.Perm.decomposeFin.symm (0, (Fin.revPerm : Equiv.Perm (Fin n))) := by
      ext i
      cases i using Fin.cases with
      | zero => simp
      | succ j =>
        simp [Equiv.Perm.decomposeFin_symm_apply_succ, Fin.rev_succ]
    have hs := congrArg Equiv.Perm.sign key
    rw [Equiv.Perm.sign_mul, sign_finRotate, Equiv.Perm.decomposeFin.symm_sign] at hs
    simp only [if_true, one_mul, Nat.add_sub_cancel] at hs
    rw [Fin.sum_univ_castSucc, pow_add]
    simp only [Fin.coe_castSucc, Fin.val_last]
    rw [← ih]
    have : Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (n + 1))) =
        (-1) ^ n * Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) := by
      rw [← hs, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]; simp
    rw [this]; push_cast; ring

theorem esymm_self (n : ℕ) : esymm (Fin n) ℝ n = ∏ i : Fin n, X i := by
  have h : Finset.powersetCard n (Finset.univ : Finset (Fin n)) = {Finset.univ} := by
    simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin n))
  rw [esymm, h]
  simp

def revTail (p q : ℕ) : Equiv.Perm (Fin (p + q)) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr 1 Fin.revPerm)

theorem revTail_castAdd (p q : ℕ) (i : Fin p) : revTail p q (Fin.castAdd q i) = Fin.castAdd q i := by
  simp [revTail, Equiv.permCongr_apply]

theorem revTail_natAdd (p q : ℕ) (j : Fin q) : revTail p q (Fin.natAdd p j) = Fin.natAdd p (Fin.rev j) := by
  simp [revTail, Equiv.permCongr_apply]

theorem sign_revTail (p q : ℕ) :
    ((Equiv.Perm.sign (revTail p q) : ℤ) : ℝ) = (-1) ^ (∑ j : Fin q, (j : ℕ)) := by
  rw [revTail, Equiv.Perm.sign_permCongr, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_one, one_mul]
  exact sign_revPerm_real q

theorem sum_tail (q : ℕ) : ∑ j : Fin q, (q - 1 - (j : ℕ)) = ∑ j : Fin q, (j : ℕ) := by
  refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
  simp [Fin.val_rev]; omega

def tailSgn (p q : ℕ) (k : Fin (p + q)) : ℝ := if (k : ℕ) < p then (-1) ^ (p + q - 1 - (k : ℕ)) else 1

theorem schubPoint_eq (ι : Type) [Fintype ι] [DecidableEq ι] (p q : ℕ) :
    (∏ τ : ι, ((∏ i : Fin p, (-X (τ, Fin.castAdd q i) : MvPolynomial (ι × Fin (p + q)) ℝ) ^ (p + q - 1 - (i : ℕ))) *
      ∏ j : Fin q, X (τ, Fin.natAdd p j) ^ (j : ℕ))) =
    C (∏ x : ι × Fin (p + q), tailSgn p q x.2) * monomial (Formalism.DegreeFormula.permExp (fun _ : ι => revTail p q)) 1 := by
  have h : C (∏ x : ι × Fin (p + q), tailSgn p q x.2) * monomial (Formalism.DegreeFormula.permExp (fun _ : ι => revTail p q)) 1 =
      ∏ x : ι × Fin (p + q), (C (tailSgn p q x.2) * X x ^ (Formalism.DegreeFormula.permExp (fun _ : ι => revTail p q) x)) := by
    rw [Finset.prod_mul_distrib, ← map_prod, monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by intro i; simp)]
  rw [h, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Fin.prod_univ_add]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    simp only [tailSgn, Formalism.DegreeFormula.permExp, revTail_castAdd, Finsupp.equivFunOnFinite_symm_apply_apply,
      Fin.coe_castAdd]
    rw [if_pos i.2, neg_pow, map_pow, map_neg, map_one]
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp only [tailSgn, Formalism.DegreeFormula.permExp, revTail_natAdd, Finsupp.equivFunOnFinite_symm_apply_apply,
      Fin.coe_natAdd, Fin.val_rev]
    rw [if_neg (by omega), C_1, one_mul]
    congr 1
    omega

theorem degFl_schubPoint (ι : Type) [Fintype ι] [DecidableEq ι] (p q : ℕ) :
    Formalism.DegreeFormula.degFl ι (p + q) (∏ τ : ι, ((∏ i : Fin p, (-X (τ, Fin.castAdd q i) : MvPolynomial (ι × Fin (p + q)) ℝ) ^
      (p + q - 1 - (i : ℕ))) * ∏ j : Fin q, X (τ, Fin.natAdd p j) ^ (j : ℕ))) = 1 := by
  rw [schubPoint_eq]
  unfold Formalism.DegreeFormula.degFl
  rw [Finset.sum_eq_single (fun _ => revTail p q)]
  · rw [coeff_C_mul, coeff_monomial, if_pos rfl, mul_one]
    have hA : ∏ x : ι × Fin (p + q), tailSgn p q x.2 =
        ((-1 : ℝ) ^ (∑ i : Fin p, (p + q - 1 - (i : ℕ)))) ^ Fintype.card ι := by
      rw [Fintype.prod_prod_type]
      dsimp only
      rw [Finset.prod_const, Finset.card_univ]
      congr 1
      rw [Fin.prod_univ_add]
      simp [tailSgn, Finset.prod_pow_eq_pow_sum]
    have hB : ∏ τ : ι, ((Equiv.Perm.sign ((fun _ : ι => revTail p q) τ) : ℤ) : ℝ) =
        ((-1 : ℝ) ^ (∑ j : Fin q, (j : ℕ))) ^ Fintype.card ι := by
      rw [Finset.prod_const, sign_revTail, Finset.card_univ]
    have hD : Formalism.DegreeFormula.dimFl ι (p + q) =
        Fintype.card ι * ((∑ i : Fin p, (p + q - 1 - (i : ℕ))) + ∑ j : Fin q, (j : ℕ)) := by
      unfold Formalism.DegreeFormula.dimFl
      congr 1
      rw [← Formalism.DegreeFormula.PermutationPointDegree.sum_delta, Fin.sum_univ_add, ← sum_tail]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Fin.coe_natAdd]; omega
    have e : ∀ a b c : ℕ, (-1 : ℝ) ^ (c * (a + b)) * (((-1) ^ b) ^ c * ((-1) ^ a) ^ c) = 1 := by
      intro a b c
      rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      exact Even.neg_one_pow ⟨c * (a + b), by ring⟩
    rw [hA, hB, hD]
    exact e _ _ _
  · intro σ _ hσ
    rw [coeff_C_mul, coeff_monomial, if_neg, mul_zero, mul_zero]
    intro h
    exact hσ (Formalism.DegreeFormula.PermutationPointDegree.permExp_inj _ _ h).symm
  · simp

section Host

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def conjOff (H : Host E) : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} ≃ GlobalTheory.AllWt.Psi H where
  toFun τ := ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_mem τ.2⟩
  invFun τ := ⟨conjEmb τ.1, GlobalTheory.AllWt.conj_not_mem τ⟩
  left_inv τ := Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1)
  right_inv τ := Subtype.ext (GlobalTheory.AllWt.conjEmb_conjEmb τ.1)

theorem flagMap_chernRoots_pointPoly {H : Host E} (Dw : Datum H) :
    GlobalTheory.Schubert.flagMap Dw (GlobalTheory.GoodMetric.chernRoots Dw.mult (GlobalTheory.LieBase.pointPoly H Dw)) =
      ∏ τ : GlobalTheory.AllWt.Psi H, (∏ i : Fin Dw.p, (-X (τ, Fin.castAdd Dw.q i))) ^ Dw.q := by
  rw [GlobalTheory.LieBase.pointPoly, map_prod, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.PointChern.mult_of_mem Dw τ.2
  have he : Dw.p + Dw.q - Dw.mult τ.1 = Dw.q := by omega
  rw [he, map_pow, map_pow]
  congr 1
  simp only [map_mul, GlobalTheory.GoodMetric.chernRoots, GlobalTheory.Schubert.flagMap, aeval_C, aeval_X, algebraMap_eq,
    esymm_self, map_prod, rename_X]
  have h1 : ∀ i : Fin (Dw.mult τ.1), GlobalTheory.Schubert.flagRoot Dw ⟨τ.1, i⟩ =
      X (τ, Fin.castAdd Dw.q (finCongr hm i)) := by
    intro i
    rw [GlobalTheory.Schubert.flagRoot, dite_eq_left τ.2]
    rfl
  simp only [h1]
  have h2 : (∏ i : Fin (Dw.mult τ.1), (-X (τ, Fin.castAdd Dw.q (finCongr hm i)) : MvPolynomial _ ℝ)) =
      C ((-1 : ℝ) ^ Dw.mult τ.1) * ∏ i : Fin (Dw.mult τ.1), X (τ, Fin.castAdd Dw.q (finCongr hm i)) := by
    simp only [← neg_one_mul (X _ : MvPolynomial _ ℝ), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, map_pow, map_neg, map_one]
  rw [← h2]
  exact Fintype.prod_equiv (finCongr hm) _ _ fun i => rfl

theorem flagMap_fibrePoint {H : Host E} (Dw : Datum H) :
    GlobalTheory.Schubert.flagMap Dw (GlobalTheory.GoodMetric.fibrePoint Dw.mult) =
      (∏ τ : GlobalTheory.AllWt.Psi H, ∏ i : Fin Dw.p, (-X (τ, Fin.castAdd Dw.q i)) ^ (Dw.p - 1 - (i : ℕ))) *
        ∏ τ : GlobalTheory.AllWt.Psi H, ∏ j : Fin Dw.q, X (τ, Fin.natAdd Dw.p j) ^ (j : ℕ) := by
  rw [GlobalTheory.GoodMetric.fibrePoint, map_prod]
  simp only [map_pow, map_neg, GlobalTheory.Schubert.flagMap, aeval_X]
  rw [Fintype.prod_sigma, ← Fintype.prod_subtype_mul_prod_subtype (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)]
  congr 1
  · refine Finset.prod_congr rfl fun τ _ => ?_
    have hm : Dw.mult τ.1 = Dw.p := GlobalTheory.PointChern.mult_of_mem Dw τ.2
    refine Fintype.prod_equiv (finCongr hm) _ _ fun i => ?_
    rw [GlobalTheory.Schubert.flagRoot, dite_eq_left τ.2]
    congr 1
    simp only [finCongr_apply, Fin.coe_cast]
    omega
  · refine Fintype.prod_equiv (conjOff H) _ _ fun τ => ?_
    have hm : Dw.mult τ.1 = Dw.q := GlobalTheory.PointChern.mult_of_not_mem Dw τ.2
    refine Fintype.prod_equiv ((finCongr hm).trans Fin.revPerm) _ _ fun i => ?_
    rw [GlobalTheory.Schubert.flagRoot, dite_eq_right τ.2, neg_neg]
    have hi : (i : ℕ) < Dw.q := hm ▸ i.2
    congr 1
    · congr 1
      refine Prod.ext rfl (Fin.ext ?_)
      simp [Fin.val_rev]
      omega
    · simp [Fin.val_rev]
      omega

end Host

theorem schubGam_pointPoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H),
    GlobalTheory.Schubert.schubGam Dw (GlobalTheory.LieBase.pointPoly H Dw) = 1 := by
  intro E _ _ _ H Dw
  rw [GlobalTheory.Schubert.schubGam_apply, map_mul, flagMap_chernRoots_pointPoly, flagMap_fibrePoint]
  have h : (∏ τ : GlobalTheory.AllWt.Psi H, (∏ i : Fin Dw.p, (-X (τ, Fin.castAdd Dw.q i) : MvPolynomial _ ℝ)) ^ Dw.q) *
      ((∏ τ : GlobalTheory.AllWt.Psi H, ∏ i : Fin Dw.p, (-X (τ, Fin.castAdd Dw.q i)) ^ (Dw.p - 1 - (i : ℕ))) *
        ∏ τ : GlobalTheory.AllWt.Psi H, ∏ j : Fin Dw.q, X (τ, Fin.natAdd Dw.p j) ^ (j : ℕ)) =
      ∏ τ : GlobalTheory.AllWt.Psi H, ((∏ i : Fin Dw.p, (-X (τ, Fin.castAdd Dw.q i)) ^ (Dw.p + Dw.q - 1 - (i : ℕ))) *
        ∏ j : Fin Dw.q, X (τ, Fin.natAdd Dw.p j) ^ (j : ℕ)) := by
    rw [← mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    congr 1
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← pow_add]
    congr 1
    have := i.2
    omega
  rw [h]
  exact degFl_schubPoint _ _ _

end GlobalTheory.SchubertPoint
end
end

section

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PointFormSign

theorem curvPoly_eq_smul_sum {n m : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) :
    curvPoly G v = ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
      (curv G v (coordVec a) (coordVec b)).map C := by
  ext i j
  simp [curvPoly, Matrix.sum_apply, mul_comm]

theorem sqPoly_eq_smul_sum {n m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) :
    sqPoly T = ∑ a, ∑ b, (X (a, b) : MvPolynomial (Fin n × Fin n) ℂ) •
      (T (coordVec a) * (T (coordVec b))ᴴ).map C := by
  refine Matrix.ext fun i j => ?_
  simp only [sqPoly, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_comm]

theorem curvPoly_of_negSq {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (S : Matrix (Fin m) (Fin m) ℂ)
    (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ)
    (h : ∀ ξ η, curv G v ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S) :
    curvPoly G v = S⁻¹.map C * (-(sqPoly T)) * S.map C := by
  have key : ∀ M : Matrix (Fin m) (Fin m) ℂ,
      (S⁻¹ * (-M) * S).map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ) = -(S⁻¹.map C * M.map C * S.map C) := by
    intro M
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_neg _ (fun a => map_neg C a), Matrix.mul_neg, Matrix.neg_mul]
  rw [curvPoly_eq_smul_sum, sqPoly_eq_smul_sum]
  simp only [h, key]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Finset.sum_neg_distrib, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_neg]

theorem charpolyRev_neg_coeff_dim {R : Type*} [CommRing R] [Nontrivial R] {m : ℕ} (P : Matrix (Fin m) (Fin m) R) :
    (Matrix.charpolyRev (-P)).coeff m = P.det := by
  rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
    Polynomial.revAt_le le_rfl, Nat.sub_self]
  have h := Matrix.det_eq_sign_charpoly_coeff (-P)
  rw [Matrix.det_neg, Fintype.card_fin] at h
  have h2 : ((-1 : R) ^ m) * ((-1) ^ m) = 1 := by rw [← mul_pow]; simp
  calc (-P).charpoly.coeff 0 = ((-1) ^ m * (-1) ^ m) * (-P).charpoly.coeff 0 := by rw [h2, one_mul]
    _ = P.det := by rw [mul_assoc, ← h, ← mul_assoc, h2, one_mul]

theorem chernPoly_top_of_negSq {n m r : ℕ} (G : V n → Matrix (Fin m) (Fin m) ℂ) (v : V n) (S : Matrix (Fin m) (Fin m) ℂ)
    (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) (hS : IsUnit S.det)
    (h : ∀ ξ η, curv G v ξ η = S⁻¹ * (-(T ξ * (T η)ᴴ)) * S) :
    chernPoly G v m = (-1) ^ m * (sqPoly T).det := by
  rw [chernPoly, charpolyRev_neg_coeff_dim, curvPoly_of_negSq G v S T h, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_neg, Fintype.card_fin]
  have h1 : (S⁻¹.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ)).det * (S.map C).det = 1 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← RingHom.map_det, ← map_mul,
      ← Matrix.det_mul, Matrix.nonsing_inv_mul _ hS, Matrix.det_one, map_one]
  calc (S⁻¹.map C).det * ((-1) ^ m * (sqPoly T).det) * (S.map C).det
      = ((S⁻¹.map (C : ℂ →+* MvPolynomial (Fin n × Fin n) ℂ)).det * (S.map C).det) * ((-1) ^ m * (sqPoly T).det) := by ring
    _ = (-1) ^ m * (sqPoly T).det := by rw [h1, one_mul]

end GlobalTheory.PointFormSign
end
end

section

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem det_blockSum {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) : (blockSum a b).det = a.det * b.det := by
  rw [blockSum, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

theorem neg_blockSum {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) : -(blockSum a b) = blockSum (-a) (-b) := by
  ext i j
  simp only [blockSum, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.neg_apply]
  rcases finSumFinEquiv.symm i with x | x <;> rcases finSumFinEquiv.symm j with y | y <;> simp

theorem one_sub_smul_blockSum {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R)
    (b : Matrix (Fin N) (Fin N) R) :
    (1 - (Polynomial.X : Polynomial R) • (blockSum a b).map Polynomial.C) =
      blockSum (1 - (Polynomial.X : Polynomial R) • a.map Polynomial.C)
        (1 - (Polynomial.X : Polynomial R) • b.map Polynomial.C) := by
  rw [blockSum_map]
  ext i j
  simp only [blockSum, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply]
  rw [show (1 : Matrix (Fin (M + N)) (Fin (M + N)) (Polynomial R)) i j =
      (1 : Matrix (Fin M ⊕ Fin N) (Fin M ⊕ Fin N) (Polynomial R)) (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) by
    simp [Matrix.one_apply]]
  rcases finSumFinEquiv.symm i with x | x <;> rcases finSumFinEquiv.symm j with y | y <;>
    simp [Matrix.one_apply]

theorem charpolyRev_neg_blockSum : ∀ {R : Type} [CommRing R] {M N : ℕ} (a : Matrix (Fin M) (Fin M) R) (b : Matrix (Fin N) (Fin N) R), Matrix.charpolyRev (-(blockSum a b)) = Matrix.charpolyRev (-a) * Matrix.charpolyRev (-b) := by
  intro R _ M N a b
  rw [neg_blockSum, Matrix.charpolyRev, Matrix.charpolyRev, Matrix.charpolyRev, one_sub_smul_blockSum, det_blockSum]

end GlobalTheory.GoodMetric.ChernSpan
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_extremalUnitVector_same_highestImage : ∀ (n : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (X : Type) [AddCommGroup X] [Module ℂ X] (ε : Fin n → Bool) (lam μ : Fin n → ℝ) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (π : Matrix (Fin n) (Fin n) ℂ → (X →ₗ[ℂ] X)) (L : Submodule ℂ H) (φ : H →ₗ[ℂ] X) (v : H), IsURepOn (UJset ε) σ → L ≤ lowKSub ε lam σ → IsKStableOn ε σ L → (∀ k ∈ Formalism.REAL.Kset ε, ∀ x ∈ L, φ (σ k x) = π k (φ x)) → v ∈ L → ‖v‖ = 1 → (∀ t : Fin n → ℝ, π (Matrix.diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I)) (φ v) = Complex.exp (((∑ a, μ a * t a : ℝ) : ℂ) * Complex.I) • φ v) → (∀ (ν : Fin n → ℝ) (y : X), y ∈ Submodule.span ℂ {z | ∃ k ∈ Formalism.REAL.Kset ε, z = π k (φ v)} → y ≠ 0 → (∀ t : Fin n → ℝ, π (Matrix.diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I)) y = Complex.exp (((∑ a, ν a * t a : ℝ) : ℂ) * Complex.I) • y) → ∑ a : Fin n, ν a * (if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ)) ≤ ∑ a : Fin n, μ a * (if ε a then -((a : ℕ) : ℝ) else ((a : ℕ) : ℝ))) → ∃ x ∈ L, ‖x‖ = 1 ∧ IsWtOn (Formalism.REAL.Kset ε) σ (fun a => Formalism.QuantumDeterminants.lowK ε lam (revNeg ε a)) x ∧ φ x = φ v := by
  first | exact @GlobalTheory.ExtRep.exists_extremal_same_image | exact GlobalTheory.ExtRep.exists_extremal_same_image | (intros; apply GlobalTheory.ExtRep.exists_extremal_same_image <;> assumption)
end
