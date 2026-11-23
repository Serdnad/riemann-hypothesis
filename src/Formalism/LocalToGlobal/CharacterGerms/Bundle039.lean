module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle002
public import Formalism.LocalToGlobal.CharacterGerms.Bundle003
public import Formalism.LocalToGlobal.CharacterGerms.Bundle038
public import Formalism.LocalToGlobal.CharacterGerms.IteratePderivTripleMultiplication
import Formalism.LocalToGlobal.CharacterGerms.Bundle037
import Formalism.LocalToGlobal.CharacterGerms.Bundle004
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePStartSelf
public import Formalism.LocalToGlobal.CharacterGerms.Bundle019
public import Formalism.LocalToGlobal.CharacterGerms.Bundle018
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyDelta
public import Formalism.LocalToGlobal.CharacterGerms.Bundle021
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyRes2
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePSplitLA
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

theorem frobPow_smul : ∀ (C : Type) [Field C] (V : VF C) (σ : Type) (f : MvPowerSeries σ C), IntS V f →
    ∀ μ : σ →₀ ℕ, V.MM (MvPowerSeries.coeff (V.l • μ) (f ^ V.l) - MvPowerSeries.coeff μ f ^ V.l) := by
  intro C _ V σ f hf μ
  have hl : 0 < V.l := V.l_prime.pos
  have h := PhPowP.frobPowMv f hf (V.l • μ)
  have hdiv : ∀ t, V.l ∣ (V.l • μ) t := fun t => by simp [Finsupp.smul_apply]
  have hdl : PhPowP.divL V.l (V.l • μ) = μ := by
    ext t
    rw [PhPowP.divL_apply, Finsupp.smul_apply, smul_eq_mul, Nat.mul_div_cancel_left _ hl]
  rw [if_pos hdiv, hdl] at h
  exact h

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

theorem aOf_eq (Y : FBChart C V O dd) (u : Fin dd → C) :
    Y.aOf u = ∑ i, MvPowerSeries.C (u i ^ V.l * ((V.l.factorial : C))⁻¹) *
      ev (rz 1) ((pderiv (R := C) ((0 : Fin 2), i))^[V.l] Y.u1) := by
  ext ν

  rw [map_sum]
  simp only [coeff_C_mul]
  show (∑ i, u i ^ V.l * coeff (Finsupp.single ((0 : Fin 2), i) V.l +
    ν.mapDomain (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2))) Y.u1) = _
  have hup : (fun q : Fin 1 × Fin dd => ((1 : Fin 2), q.2)) = up 1 := by
    funext q; obtain ⟨q1, q2⟩ := q; fin_cases q1; rfl
  rw [hup]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_rz_iter]
  have hf : (V.l.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp

theorem link (Y : FBChart C V O dd) (u : Fin dd → C) (W : Pt C 2 dd) (hW : ∀ j, constantCoeff (W j) = 0)
    (Wup : Pt C 3 dd) (hW0 : ∀ j, constantCoeff (Wup j) = 0)
    (hd : ∀ i j, pderiv (R := C) ((0 : Fin 3), i) (Wup j) = 0)
    (hr : ∀ j, ev (rz 2) (Wup j) = W j) (γ : Fin 2 × Fin dd →₀ ℕ) :
    coeff γ (ev (n := 2) ![W] (Y.aOf u)) = Phi V u (UU Y Wup) γ := by
  have hz1 := z0_1 W hW
  have hz2 := constant_zero_two_points (p3 0) (z0p3 0) hW0
  rw [aOf_eq, ev_sum hz1]

  simp only [PartialDerivEval.ev_mul hz1, PartialDerivEval.ev_C, map_sum, coeff_C_mul]
  unfold Phi
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : ev ![W] (ev (rz 1) ((pderiv (R := C) ((0 : Fin 2), i))^[V.l] Y.u1)) =
      ev (n := 2) ![0, W] ((pderiv (R := C) ((0 : Fin 2), i))^[V.l] Y.u1) := by
    rw [ev_ev (constant_zero_restrict_points 1) hz1]
    congr 1
    funext k j
    fin_cases k
    · exact ev_zero hz1
    · exact ev_X hz1 0 j
  have e2 : ev (rz 2) ((pderiv (R := C) ((0 : Fin 3), i))^[V.l] (UU Y Wup)) =
      ev (n := 2) ![0, W] ((pderiv (R := C) ((0 : Fin 2), i))^[V.l] Y.u1) := by
    unfold UU
    rw [d_ev_keep_iter hW0 i (hd i), ev_ev hz2 (constant_zero_restrict_points 2)]
    congr 1
    funext k j
    fin_cases k
    · exact ev_X (constant_zero_restrict_points 2) 0 j
    · exact hr j
  have h3 := coeff_rz_iter 2 i V.l (UU Y Wup) γ
  rw [e2] at h3
  rw [e1, h3]
  have hf : (V.l.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  field_simp
  rfl

theorem coeff_U_eq (Y : FBChart C V O dd) (u : Fin dd → C) (hu : ∀ i, V.Ge 0 (u i)) (γ : Fin 2 × Fin dd →₀ ℕ) :
    V.MM (Phi V u (UU Y (SS Y.B.G)) γ - Phi V u (UU Y (p3 1)) γ - Phi V u (UU Y (p3 2)) γ -
      Phi V u (Y.B.ph2 ^ V.l) γ + Phi V u (QQ Y) γ) := by
  have hU : ∀ {w : Pt C 3 dd}, (∀ j, constantCoeff (w j) = 0) → (∀ j, IntS V (w j)) →
      (∀ i j, pderiv (R := C) ((0 : Fin 3), i) (w j) = 0) →
      IntS V (UU Y w) ∧ FrobD V (UU Y w) ∧ ev (rz 2) (UU Y w) = 1 :=
    fun hw0 hw hd => ⟨UU_int Y hw0 hw, UU_frob Y hw0 hw hd, UU_one Y hw0⟩
  obtain ⟨iS, fS, oS⟩ := hU (triple_sum_constantCoeff Y.B.G) (SS_int Y.B.G Y.intF) (SS_d Y.B.G)
  obtain ⟨i1, f1, o1⟩ := hU (z0p3 1) (fun j => triple_coordinate_integral 1 j) (fun i j => triple_point_pderiv_first_zero 1 (by decide) i j)
  obtain ⟨i2, f2, o2⟩ := hU (z0p3 2) (fun j => triple_coordinate_integral 2 j) (fun i j => triple_point_pderiv_first_zero 2 (by decide) i j)
  have iQ := QQ_int Y
  have iP : IntS V (Y.B.ph2 ^ V.l) := intS_pow Y.intPh2 _
  have i12 : IntS V (UU Y (p3 1) * UU Y (p3 2)) := intS_mul i1 i2
  have f12 : FrobD V (UU Y (p3 1) * UU Y (p3 2)) := frobD_mul i1 i2 f1 f2
  have o12 : ev (rz 2) (UU Y (p3 1) * UU Y (p3 2)) = 1 := by
    rw [PartialDerivEval.ev_mul (constant_zero_restrict_points 2), o1, o2, one_mul]
  unfold Phi
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine GmExArith.mm_sum fun i _ => ?_
  have cS := coeff_mul_cong iS iQ (frobX_of iS fS) (frobX_of iQ (QQ_frob Y)) oS (QQ_one Y) i γ
  have cR1 := coeff_mul_cong i12 iP (frobX_of i12 f12) (frobX_of iP (second_pairing_pow_frobenius Y)) o12 (second_pairing_pow_restrict_one Y) i γ
  have cR2 := coeff_mul_cong i1 i2 (frobX_of i1 f1) (frobX_of i2 f2) o1 o2 i γ
  rw [ident] at cS
  have e : u i ^ V.l * coeff (ix i V.l γ) (UU Y (SS Y.B.G)) - u i ^ V.l * coeff (ix i V.l γ) (UU Y (p3 1)) -
      u i ^ V.l * coeff (ix i V.l γ) (UU Y (p3 2)) - u i ^ V.l * coeff (ix i V.l γ) (Y.B.ph2 ^ V.l) +
      u i ^ V.l * coeff (ix i V.l γ) (QQ Y) =
      u i ^ V.l * (-(coeff (ix i V.l γ) (UU Y (p3 1) * UU Y (p3 2) * Y.B.ph2 ^ V.l) -
        coeff (ix i V.l γ) (UU Y (SS Y.B.G)) - coeff (ix i V.l γ) (QQ Y)) +
        (coeff (ix i V.l γ) (UU Y (p3 1) * UU Y (p3 2) * Y.B.ph2 ^ V.l) -
          coeff (ix i V.l γ) (UU Y (p3 1) * UU Y (p3 2)) - coeff (ix i V.l γ) (Y.B.ph2 ^ V.l)) +
        (coeff (ix i V.l γ) (UU Y (p3 1) * UU Y (p3 2)) - coeff (ix i V.l γ) (UU Y (p3 1)) -
          coeff (ix i V.l γ) (UU Y (p3 2)))) := by ring
  rw [e]
  exact GmExArith.mm_int_mul ((hu i).pow _) (GmExArith.mm_add (GmExArith.mm_add (GmExArith.mm_neg cS) cR1) cR2)

end Formalism.L2.FormalSeriesBounds.FunEq

namespace Formalism.L2.FormalSeriesBounds

open FunEq MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem funEqCore_holds : FunEqCoreSt := by
  intro C _ _ V O _ _ dd Y u hu hV1 μ
  have hS := link Y u (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C dd 1))
    (fun j => PartialDerivEval.const_ev (PartialDerivEval.z0_pp 0 1) (Y.B.G.const j)) (SS Y.B.G) (triple_sum_constantCoeff _) (SS_d _)
    (fun j => by
      show ev (rz 2) (ev (n := 3) ![p3 1, p3 2] (Y.B.G.F j)) = _
      rw [PartialDerivEval.ev_ev (PartialDerivEval.z0_pp 1 2) (constant_zero_restrict_points 2)]
      congr 1
      funext k m
      fin_cases k
      · exact PartialDerivEval.ev_X (constant_zero_restrict_points 2) 1 m
      · exact PartialDerivEval.ev_X (constant_zero_restrict_points 2) 2 m) μ
  have h1 := link Y u (pt C (n := 2) dd 0) (fun j => PartialDerivEval.z0_pt 0 j) (p3 1) (z0p3 1)
    (fun i j => triple_point_pderiv_first_zero 1 (by decide) i j) (fun j => PartialDerivEval.ev_X (constant_zero_restrict_points 2) 1 j) μ
  have h2 := link Y u (pt C (n := 2) dd 1) (fun j => PartialDerivEval.z0_pt 1 j) (p3 2) (z0p3 2)
    (fun i j => triple_point_pderiv_first_zero 2 (by decide) i j) (fun j => PartialDerivEval.ev_X (constant_zero_restrict_points 2) 2 j) μ
  unfold cobd
  rw [map_sub, map_sub, map_sub, hS, h1, h2]
  have hA := coeff_U_eq Y u hu μ
  have hB := phiP Y u hu μ
  have hC := phiQ Y u hu hV1 μ
  have e : Phi V u (UU Y (SS Y.B.G)) μ - Phi V u (UU Y (p3 1)) μ - Phi V u (UU Y (p3 2)) μ -
      coeff μ (frobTw V.l (Y.chartLinearTerm u)) =
      (Phi V u (UU Y (SS Y.B.G)) μ - Phi V u (UU Y (p3 1)) μ - Phi V u (UU Y (p3 2)) μ -
        Phi V u (Y.B.ph2 ^ V.l) μ + Phi V u (QQ Y) μ) +
      (Phi V u (Y.B.ph2 ^ V.l) μ - coeff μ (frobTw V.l (Y.chartLinearTerm u))) - Phi V u (QQ Y) μ := by ring
  rw [e]
  exact GmExArith.mm_sub (GmExArith.mm_add hA hB) hC

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace ProjLieSelf

open PartialDerivEval RowTiePE0 RowTiePProj RowTiePLSmall RowTiePLie RowTiePSplit RowTiePKey

theorem keySelf (hE : KeyEigSt) {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O]
    {dd : ℕ} (Y : FBChart C V O dd) {d : ℕ} [NeZero d] {I0 : Type} [Fintype I0] (p : SelfData Y d I0) (ε : O)
    (hε : ∃ y, ε * ε - ε = (V.l : O) * y) (hε1 : ∀ a, V.MM (p.em a ε - 1))
    (hεx : ∀ x : O, (∀ a, V.MM (p.em a x)) → ∃ y, ε * x = (V.l : O) * y) (e : Pt C 1 dd)
    (he : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (ε ^ V.l ^ n) i))) (x : O) :
    Polynomial.aeval (linM (Y.B.A.act x)) (∏ c : ZMod d, (Polynomial.X - Polynomial.C (p.em c x))) * linM e = 0 := by
  let K : KeyData C V O dd d :=
    { ρ := linHom Y
      ρ_int := fun x i j => Y.intAct x i _
      P := linM e
      em := p.em
      em_int := p.em_int
      em_frob := p.em_frob
      ε := ε
      ε_idem := hε
      ε_one := hε1
      ε_ann := hεx
      P_lim := fun N i j => he N i _ }
  exact keyLA_of hE RowTiePKeyRes.keyRes_holds keyDelta_holds C V Y.algClosed Y.cpl O dd d K x

end ProjLieSelf


open PartialDerivEval RowTiePE0 RowTiePProj RowTiePLSmall RowTiePLie RowTiePSplit RowTiePKey in
theorem projLieSelf_of (hE : KeyEigSt) : ProjLieSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p ε hε hε1 hεx e he v
  obtain ⟨e0, hidem, hcomm⟩ := proj_core Y ε hε e he
  have hinj : Function.Injective (fun c : ZMod d => p.em c) := by
    intro c c' h
    by_contra hne
    obtain ⟨x, hx⟩ := p.em_sep c c' hne
    have h2 : p.em c = p.em c' := h
    rw [h2, sub_self, AddValuation.map_zero] at hx
    simp at hx
  have hPP : linM e * linM e = linM e := by rw [← lin_comp1 e0, hidem]
  have hPM : ∀ x, linM e * linHom Y x = linHom Y x * linM e := fun x => by
    show linM e * linM (Y.B.A.act x) = linM (Y.B.A.act x) * linM e
    rw [← lin_comp1 (Y.B.A.const x), ← lin_comp1 e0, hcomm x]
  obtain ⟨w, hw, hwe⟩ := split_holds C O dd (ZMod d) (linHom Y) (linM e) (fun c => p.em c) hPP hPM hinj
    (fun x => ProjLieSelf.keySelf hE Y p ε hε hε1 hεx e he x) v
  have hb : ∀ c, ∃ b : I0 → C, (∀ c', p.ty0 c' ≠ c → b c' = 0) ∧ w c = ∑ c', b c' • p.e c' := fun c =>
    p.e_full c (w c) fun x => by rw [linAct_eq]; exact hwe c x
  choose b _ hbw using hb
  refine ⟨fun c' => ∑ c, b c c', ?_⟩
  rw [linAct_eq, hw]
  simp_rw [hbw, Finset.sum_smul]
  exact Finset.sum_comm

theorem allStartSelf_of_eig (hE : RowTiePKey.KeyEigSt) : AllStartSelfSt := allStartSelf_of (projLieSelf_of hE)

end Formalism.L2.FormalSeriesBounds
end
end
