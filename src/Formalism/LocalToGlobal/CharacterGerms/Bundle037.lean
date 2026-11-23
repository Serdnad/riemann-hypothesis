module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle023
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTSelf
public import Formalism.LocalToGlobal.CharacterGerms.Bundle005
import Formalism.LocalToGlobal.CharacterGerms.RowTiePAddCvSelf
public import Formalism.LocalToGlobal.CharacterGerms.Bundle017
public import Formalism.LocalToGlobal.CharacterGerms.Bundle035
public import Formalism.LocalToGlobal.CharacterGerms.Bundle015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle019
public import Formalism.LocalToGlobal.CharacterGerms.TripleMultiplicationConstantCoeff
public import Formalism.LocalToGlobal.CharacterGerms.GermEvalOneStandardPointSelf
public import Formalism.LocalToGlobal.CharacterGerms.IndexRaiseFirst
public import Formalism.LocalToGlobal.CharacterGerms.PderivDoubleMultiplicationJacobian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace IndependenceBoundPlain

variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type}
  [Fintype κ] (X : RawChart C d I κ)

def PlainCoefficientIdentity (H : ∀ g, X.CartHyp V g) : Prop :=
  X.AltC → ∀ g a, X.big g a →
    ∃ M : JJ I g → JJ I g → C, ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (H g)).Good a w x →
      (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) →
      ∃ c1 : JJ I g → C, (∀ q, X.ty (1 - g) q ≠ a + 2 → c1 q = 0) ∧
        ∀ q, V.MM ((RawChart.cart (H g)).c0' x q ^ V.l - ∑ q', c1 q' * M q' q)

theorem independence_bound_raw [IsAlgClosed C] [NeZero d] (hrk : X.RankHyp) (H : ∀ g, X.CartHyp V g) (hR2 : RawChart.RankMaximalCondition H)
    (hcoef : PlainCoefficientIdentity X H) : RawChart.IndependenceBoundCondition H := by
  intro hAlt g a hbig N w x hg hV hind
  have key : ∀ g' : Fin 2, X.big g' a → X.big g' (a + 2) := by
    obtain ⟨hd, hpar⟩ := hAlt
    have hev := ValuationNonnegativity.even_val_add_two hd a
    have e1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b := fun b => by
      simpa using hrk.big_compl 0 b
    intro g' hb
    fin_cases g'
    · exact (hpar (a + 2)).2 (hev.2 ((hpar a).1 hb))
    · simp only [Fin.mk_one] at hb ⊢
      rw [e1, hpar] at hb ⊢
      rwa [hev]
  have hsmall : ¬ X.big (1 - g) (a + 2) := fun h2 => (hrk.big_compl g (a + 2)).1 h2 (key g hbig)
  have hcard : Fintype.card {q : JJ I g // X.ty (1 - g) q = a + 2} = X.j' := by
    rw [Fintype.card_subtype]; exact hrk.rk_small (1 - g) (a + 2) hsmall
  obtain ⟨M, hM⟩ := hcoef hAlt g a hbig
  let σ := (Fintype.equivFinOfCardEq hcard).symm
  have hspan : ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (H g)).Good a w x →
      (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) →
      ∃ b : Fin X.j' → C, ∀ q, V.MM ((RawChart.cart (H g)).c0' x q ^ V.l - ∑ r, b r * M (σ r).1 q) := by
    intro w x hg hV
    obtain ⟨c1, hsupp, hc1⟩ := hM w x hg hV
    refine ⟨fun r => c1 (σ r).1, fun q => ?_⟩
    have hsum : ∑ q', c1 q' * M q' q = ∑ r, c1 (σ r).1 * M (σ r).1 q := by
      rw [← Finset.sum_filter_of_ne (p := fun q' => X.ty (1 - g) q' = a + 2)
        (fun q' _ hne => by
          by_contra hq
          exact hne (by rw [hsupp q' hq, zero_mul]))]
      rw [Finset.sum_subtype (Finset.univ.filter fun q' => X.ty (1 - g) q' = a + 2)
        (p := fun q' => X.ty (1 - g) q' = a + 2) (fun q' => by simp)]
      exact (Equiv.sum_comp σ (fun s => c1 s.1 * M s.1 q)).symm
    rw [← hsum]
    exact hc1 q
  exact ValuationNonnegativity.independence_bound_of_span_raw (RawChart.cart (H g)) a _ (hR2 hAlt g a hbig) (fun r => M (σ r).1) hspan
    N w x hg hV hind

end IndependenceBoundPlain

section Closed

def CoefficientIdentitySelfConjugate : Prop :=
  AllSelf fun _ _ V _ _ _ _ X => X.RankHyp → ∀ H : ∀ g, X.CartHyp V g, IndependenceBoundPlain.PlainCoefficientIdentity X H

theorem independence_bound_self_conj (h : CoefficientIdentitySelfConjugate) : IndependenceBoundSelfConjugate := by
  unfold IndependenceBoundSelfConjugate AllSelf
  intro C _ _ V O _ _ dd Y d _ I0 _ p hrk H hR2
  have := Y.algClosed
  exact IndependenceBoundPlain.independence_bound_raw (Y.rawSelf p) hrk H hR2 (h C V O dd Y d I0 p hrk H)

end Closed

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

def AllStartSelfSt : Prop :=
  AllSelf fun C _ V _ I _ _ X => ∀ (g : Fin 2) (w : I g → C), (∀ c, V.Ge 0 (w c)) →
    ∃ L ∈ X.AllSet V g, ∀ c, L 1 (Sum.inl c) = w c

theorem ptExSelf_of_start (hS : AllStartSelfSt) : PTExSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g a w hw _
  obtain ⟨L0, hL0, hL01⟩ := hS C V O dd Y d I0 p g w hw
  set X := Y.rawSelf p with hX
  let M : Set (ℕ → I0 ⊕ I0 → C) := {m | ∀ L ∈ X.AllSet V g, m * L ∈ X.AllSet V g}
  have hAdd := addCvSelf_holds C V O dd Y d I0 p
  have h1 : (1 : ℕ → I0 ⊕ I0 → C) ∈ M := fun L hL => by rwa [one_mul]
  have hadd : ∀ m m', m ∈ M → m' ∈ M → m + m' ∈ M := fun m m' hm hm' L hL => by
    rw [add_mul]; exact X.allSet_add V g hAdd (fun g c x => Y.rawSelf_u_integral p g c x) (hm L hL) (hm' L hL)
  have hmul : ∀ m m', m ∈ M → m' ∈ M → m * m' ∈ M := fun m m' hm hm' L hL => by
    rw [mul_assoc]; exact hm _ (hm' L hL)
  have hteich : ∀ c : C, V.Ge 0 c → (fun n (_ : I0 ⊕ I0) => c ^ n) ∈ M := fun c hc L hL =>
    X.allSet_teich V g c hc hL
  have hlim : ∀ (m : ℕ → ℕ → I0 ⊕ I0 → C) (m' : ℕ → I0 ⊕ I0 → C), (∀ k, m k ∈ M) → VLim V m m' → m' ∈ M :=
    fun m m' hm hmm' L hL => X.allSet_lim (Y.self_chart_log_constantCoeff p) (Y.self_chart_exp_constantCoeff p) (Y.rawSelf_lgex p) (Y.rawSelf_exlg p)
      (fun k => hm k L hL) (hmm'.mul_right L)
  have hroot : ∀ q : ℕ, q.Prime → q ≠ V.l → ∃ ζ : C, IsPrimitiveRoot ζ q := by
    intro q hq _
    have := Y.algClosed
    have : NeZero (q : C) := ⟨Nat.cast_ne_zero.mpr hq.ne_zero⟩
    exact HasEnoughRootsOfUnity.exists_primitiveRoot C q
  have hind := TypAr.typ_gen M hroot h1 hadd hmul hteich hlim
  have hL := hind L0 hL0
  refine ⟨_, X.typ_link V g hL ?_, ?_⟩
  · intro n k hn
    simp only [Pi.mul_apply]
    rw [if_neg hn, zero_mul]
  · intro c
    simp only [Pi.mul_apply, pow_zero]
    rw [if_pos ⟨0, pow_zero _⟩, one_mul, hL01 c]

theorem ptSelf_of_start (hS : AllStartSelfSt) (hAct : OActSelfSt) (hStab : HStabSelfSt) : PTSelfSt :=
  ptSelf_of_act (ptExSelf_of_start hS) hAct limSelf_holds hStab

end Formalism.L2.FormalSeriesBounds
end
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.FunEq

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval Formalism.L2.FormalSeriesBounds.FirstUnitSeriesIntegrality Formalism.L2.FormalSeriesBounds.MulLFrob Formalism.L2.FormalSeriesBounds.LiftedCoordinateEvaluation
  ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ} {V : VF C} {O : Type} [CommRing O] [StarRing O]

theorem pderiv_first_unit_series_maximal (Y : FBChart C V O dd) (i : Fin dd) : MaximalIdealCongruence.MMS V (pderiv (R := C) ((0 : Fin 2), i) Y.u1) := by
  have hu : Y.u1 = FB.expS C (evl Y V.l Y.h - (V.l : C) • Y.h) := rfl
  have hE0 : constantCoeff (evl Y V.l Y.h - (V.l : C) • Y.h) = 0 := by
    rw [map_sub, show (V.l : C) • Y.h = ((V.l : ℕ) : PS C 2 dd) * Y.h by
      rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul], map_mul, PartialDerivEval.h_const, mul_zero, sub_zero]
    exact FirstUnitSeriesIntegrality.height_multiple_constantCoeff Y V.l
  have hd : pderiv (R := C) ((0 : Fin 2), i) Y.u1 =
      (V.l : PS C 2 dd) * (Y.u1 * ∑ m, (Pm Y m - evl Y V.l (Pm Y m)) * logJacobianTwoPoints Y m i) := by
    rw [hu, PartialDerivEval.pderiv_expS hE0, dE, ← hu]; ring
  have hint : IntS V (Y.u1 * ∑ m, (Pm Y m - evl Y V.l (Pm Y m)) * logJacobianTwoPoints Y m i) := by
    refine PartialDerivEval.intS_mul (first_unit_series_integral C V O dd Y)
      (PartialDerivEval.intS_sum _ fun m _ => PartialDerivEval.intS_mul ?_ ?_)
    · have hP : IntS V (Pm Y m) := by
        refine PartialDerivEval.intS_ev constant_zero_lift_triple (fun k j => ?_) (PartialDerivEval.intS_pderiv Y.intPh1 _)
        fin_cases k
        · exact PartialDerivEval.intS_X _
        · exact PartialDerivEval.intS_zero
        · exact PartialDerivEval.intS_X _
      have hP' : IntS V (evl Y V.l (Pm Y m)) := by
        refine PartialDerivEval.intS_ev (constant_zero_double_multiplication Y V.l) (fun k j => ?_) hP
        fin_cases k
        · exact FirstUnitSeriesIntegrality.double_multiplication_integral Y.B.G Y.intF V.l j
        · exact PartialDerivEval.intS_X _
      rw [sub_eq_add_neg]
      exact PartialDerivEval.intS_add hP (PartialDerivEval.intS_neg hP')
    · refine PartialDerivEval.intS_ev (PartialDerivEval.z0_1 _ z0P0) (fun k j => ?_) (MulLFrob.JL_int Y m i)
      fin_cases k
      exact PartialDerivEval.intS_X _
  rw [hd]; exact MaximalIdealCongruence.mms_l_mul hint

theorem int_two {w : Pt C 3 dd} (P : Pt C 3 dd) (hP : ∀ j, IntS V (P j)) (hw : ∀ j, IntS V (w j)) :
    ∀ k j, IntS V ((![P, w] : Fin 2 → Pt C 3 dd) k j) := fun k j => by
  fin_cases k
  · exact hP j
  · exact hw j

theorem triple_coordinate_integral (k : Fin 3) (j : Fin dd) : IntS V ((p3 k : Pt C 3 dd) j) := intS_X _

theorem UU_int (Y : FBChart C V O dd) {w : Pt C 3 dd} (hw0 : ∀ j, constantCoeff (w j) = 0)
    (hw : ∀ j, IntS V (w j)) : IntS V (UU Y w) :=
  intS_ev (constant_zero_two_points _ (z0p3 0) hw0) (int_two _ (triple_coordinate_integral 0) hw) (first_unit_series_integral C V O dd Y)

theorem UU_frob (Y : FBChart C V O dd) {w : Pt C 3 dd} (hw0 : ∀ j, constantCoeff (w j) = 0)
    (hw : ∀ j, IntS V (w j)) (hd : ∀ i j, pderiv (R := C) ((0 : Fin 3), i) (w j) = 0) : FrobD V (UU Y w) := by
  intro i
  unfold UU
  rw [d_ev_keep hw0 i (hd i)]
  exact MaximalIdealCongruence.MMS.ev_of (constant_zero_two_points _ (z0p3 0) hw0) (int_two _ (triple_coordinate_integral 0) hw) (pderiv_first_unit_series_maximal Y i)

theorem UU_one (Y : FBChart C V O dd) {w : Pt C 3 dd} (hw0 : ∀ j, constantCoeff (w j) = 0) :
    ev (rz 2) (UU Y w) = 1 := by
  have hz := constant_zero_two_points (p3 0) (z0p3 0) hw0
  have hw' : ∀ j, constantCoeff (ev (rz (C := C) (dd := dd) 2) (w j)) = 0 := fun j => const_ev (constant_zero_restrict_points 2) (hw0 j)
  have hE0 : constantCoeff (ev (n := 3) ![m3 Y.B.G V.l, w] Y.h - (V.l : C) • ev (n := 3) ![p3 0, w] Y.h) = 0 := by
    rw [map_sub, eval_height_constantCoeff Y (triple_multiplication_constantCoeff _ _) hw0, show (V.l : C) • ev (n := 3) ![p3 0, w] Y.h =
      MvPowerSeries.C (V.l : C) * ev (n := 3) ![p3 0, w] Y.h from MvPowerSeries.smul_eq_C_mul _ _, map_mul,
      eval_height_constantCoeff Y (z0p3 0) hw0, mul_zero, sub_zero]
  rw [UU_eq Y w hw0, ev_ex (constant_zero_restrict_points 2) _ hE0, ev_sub (constant_zero_restrict_points 2), ev_smulC (constant_zero_restrict_points 2),
    ev_ev (constant_zero_two_points _ (triple_multiplication_constantCoeff _ _) hw0) (constant_zero_restrict_points 2), ev_ev hz (constant_zero_restrict_points 2)]
  have e1 : (fun k j => ev (rz (C := C) (dd := dd) 2) ((![m3 Y.B.G V.l, w] : Fin 2 → Pt C 3 dd) k j)) =
      ![0, fun j => ev (rz 2) (w j)] := by
    funext k j; fin_cases k
    · exact restrict_triple_multiplication _ _ j
    · rfl
  have e2 : (fun k j => ev (rz (C := C) (dd := dd) 2) ((![p3 0, w] : Fin 2 → Pt C 3 dd) k j)) =
      ![0, fun j => ev (rz 2) (w j)] := by
    funext k j; fin_cases k
    · exact ev_X (constant_zero_restrict_points 2) 0 j
    · rfl
  rw [e1, e2, height_at_zero_first Y _ hw', smul_zero, sub_zero, ex_zero]

theorem constant_zero_triple_multiplication (Y : FBChart C V O dd) : Z0 (![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) := fun k j => by
  fin_cases k
  · exact triple_multiplication_constantCoeff _ _ j
  · exact z0p3 1 j
  · exact z0p3 2 j

theorem QQ_int (Y : FBChart C V O dd) : IntS V (QQ Y) := by
  refine intS_ev (constant_zero_triple_multiplication Y) (fun k j => ?_) Y.intPh2
  fin_cases k
  · exact triple_multiplication_integral _ Y.intF _ j
  · exact intS_X _
  · exact intS_X _

theorem pderiv_triple_multiplication (Y : FBChart C V O dd) (k i : Fin dd) :
    pderiv (R := C) ((0 : Fin 3), i) (m3 Y.B.G V.l k) = ev ![(p3 0 : Pt C 3 dd)] (Jac (mulL Y.B.G.F V.l) k i) := by
  show pderiv (R := C) ((0 : Fin 3), i) (ev ![(p3 0 : Pt C 3 dd)] (mulL Y.B.G.F V.l k)) = _
  rw [pderiv_eval_single (P := (p3 0 : Pt C 3 dd)) (z0p3 0), Finset.sum_eq_single i (fun j _ hj => by
      show _ * pderiv (R := C) _ (pt C (n := 3) dd 0 j) = 0
      rw [LiftedCoordinateEvaluation.pderiv_pt_same, if_neg hj, mul_zero]) (fun h => absurd (Finset.mem_univ i) h)]
  show _ * pderiv (R := C) _ (pt C (n := 3) dd 0 i) = _
  rw [LiftedCoordinateEvaluation.pderiv_pt_same, if_pos rfl, mul_one]
  rfl

theorem pderiv_triple_multiplication_maximal (Y : FBChart C V O dd) (k i : Fin dd) : MaximalIdealCongruence.MMS V (pderiv (R := C) ((0 : Fin 3), i) (m3 Y.B.G V.l k)) := by
  rw [pderiv_triple_multiplication, jac_l, Matrix.smul_apply, ev_eq_alg (z0_1 _ (z0p3 0)), map_nsmul, ← ev_eq_alg (z0_1 _ (z0p3 0)),
    nsmul_eq_mul]
  refine MaximalIdealCongruence.mms_l_mul (intS_ev (z0_1 _ (z0p3 0)) (fun k' j => by fin_cases k'; exact intS_X _) ?_)
  rw [Matrix.mul_apply]
  refine intS_sum _ fun j _ => intS_mul ?_ (JL_int Y j i)
  refine intS_ev (z0_1 _ (multiplication_constantCoeff_zero Y.B.G V.l)) (fun k' j' => ?_) (JF_int Y k j)
  fin_cases k'
  exact mulL_int Y.B.G Y.intF V.l j'

theorem QQ_frob (Y : FBChart C V O dd) : FrobD V (QQ Y) := by
  intro i
  unfold QQ
  rw [pderiv_eval_triple (constant_zero_triple_multiplication Y)]
  have h1 : ∑ j, ev ![m3 Y.B.G V.l, p3 1, p3 2] (pderiv (R := C) ((1 : Fin 3), j) Y.B.ph2) *
      pderiv (R := C) ((0 : Fin 3), i) ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) 1 j) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      show _ * pderiv (R := C) _ (pt C (n := 3) dd 1 j) = 0
      rw [LiftedCoordinateEvaluation.pderiv_pt_ne _ _ _ (by decide : (1 : Fin 3) ≠ 0), mul_zero]
  have h2 : ∑ j, ev ![m3 Y.B.G V.l, p3 1, p3 2] (pderiv (R := C) ((2 : Fin 3), j) Y.B.ph2) *
      pderiv (R := C) ((0 : Fin 3), i) ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) 2 j) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      show _ * pderiv (R := C) _ (pt C (n := 3) dd 2 j) = 0
      rw [LiftedCoordinateEvaluation.pderiv_pt_ne _ _ _ (by decide : (2 : Fin 3) ≠ 0), mul_zero]
  rw [h1, h2, add_zero, add_zero]
  refine MaximalIdealCongruence.mms_sum _ fun j _ => MaximalIdealCongruence.MMS.mul_left ?_ (pderiv_triple_multiplication_maximal Y j i)
  refine intS_ev (constant_zero_triple_multiplication Y) (fun k m => ?_) (intS_pderiv Y.intPh2 _)
  fin_cases k
  · exact triple_multiplication_integral _ Y.intF _ m
  · exact intS_X _
  · exact intS_X _

theorem rz_eq : (rz (C := C) (dd := dd) 2) = ![0, pt C (n := 2) dd 0, pt C dd 1] := by
  funext k j
  fin_cases k <;> rfl

theorem QQ_one (Y : FBChart C V O dd) : ev (rz 2) (QQ Y) = 1 := by
  unfold QQ
  rw [ev_ev (constant_zero_triple_multiplication Y) (constant_zero_restrict_points 2)]
  have e : (fun k j => ev (rz (C := C) (dd := dd) 2)
      ((![m3 Y.B.G V.l, p3 1, p3 2] : Fin 3 → Pt C 3 dd) k j)) = ![0, pt C (n := 2) dd 0, pt C dd 1] := by
    funext k j; fin_cases k
    · exact restrict_triple_multiplication _ _ j
    · exact ev_X (constant_zero_restrict_points 2) 1 j
    · exact ev_X (constant_zero_restrict_points 2) 2 j
  rw [e]
  exact Y.B.cocycleRight_zero_fst

theorem second_pairing_restrict_one (Y : FBChart C V O dd) : ev (rz 2) Y.B.ph2 = 1 := by
  rw [rz_eq]; exact Y.B.cocycleRight_zero_fst

theorem second_pairing_pow_restrict_one (Y : FBChart C V O dd) : ev (rz 2) (Y.B.ph2 ^ V.l) = 1 := by
  rw [ev_eq_alg (constant_zero_restrict_points 2), map_pow, ← ev_eq_alg (constant_zero_restrict_points 2), second_pairing_restrict_one, one_pow]

theorem second_pairing_pow_frobenius (Y : FBChart C V O dd) : FrobD V (Y.B.ph2 ^ V.l) := by
  intro i
  rw [Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul]
  exact MaximalIdealCongruence.mms_l_mul (intS_mul (intS_pow Y.intPh2 _) (intS_pderiv Y.intPh2 _))

end Formalism.L2.FormalSeriesBounds.FunEq
end
end
