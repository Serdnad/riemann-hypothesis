module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
public import Formalism.DropLevelBounds.ConstantCoeffVanishing.UbintConstantCoeffEqZero
public import Formalism.LocalToGlobal.CharacterGerms.Bundle007
public import Formalism.LocalToGlobal.CharacterGerms.LemmaMLin
public import Formalism.LocalToGlobal.CharacterGerms.RowTieJet
public import Formalism.LocalToGlobal.CharacterGerms.Bundle011
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
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjFB

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

theorem cc_smul {σ : Type} (c : C) {F : MvPowerSeries σ C} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (c • F) = 0 := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, hF, mul_zero]

theorem expS_copies (Y : FBChart C V O dd) (n : ℕ) :
    FB.expS C ((Y.k : C) • ∑ b : Fin n, ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0)) =
      ∏ b : Fin n, ev (n := n) ![pt C dd b] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) := by
  have ha : ∀ b : Fin n, ∀ s : Fin 1 × Fin dd, MvPowerSeries.constantCoeff (![pt C dd b] s.1 s.2) = 0 := by
    intro b s
    simp [pt]
  have hc : ∀ b : Fin n, MvPowerSeries.constantCoeff (ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0)) = 0 := fun b =>
    (ordGE_one_iff _).1 (ordGE_subst (VP.og (a := fun s : Fin 1 × Fin dd => ![pt C dd b] s.1 s.2) (ha b))
      ((ordGE_one_iff _).2 (VP.cc_hL Y)))
  have hs : ∀ b : Fin n, ev (n := n) ![pt C dd b] ((Y.k : C) • Y.B.hL C Y.h Y.w0) =
      (Y.k : C) • ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0) := fun b =>
    MvPowerSeries.subst_smul (hasSubst_of_ordGE (VP.og (a := fun s : Fin 1 × Fin dd => ![pt C dd b] s.1 s.2) (ha b))) _ _

  rw [VP.expS_eq _ (cc_smul _ (by rw [map_sum]; exact Finset.sum_eq_zero fun b _ => hc b)), Finset.smul_sum,
  Formalism.UnitaryBoundIntegral.ubint_mvExp_sum _ _ (fun b _ => cc_smul _ (hc b))]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [VP.expS_eq _ (cc_smul _ (VP.cc_hL Y))]
  show _ = MvPowerSeries.subst (fun s : Fin 1 × Fin dd => ![pt C dd b] s.1 s.2) (mvExp _)
  rw [VP.subst_exp (ha b) (cc_smul _ (VP.cc_hL Y))]
  exact congrArg mvExp (hs b).symm

theorem rowCopy_mul_exp {J : Fin 2 → Type} {n : ℕ} (b : Fin n) (F L : MvPowerSeries (WV J) C) :
    rowCopy b (F * mvExp L) = rowCopy b F * mvExp (rowCopy b L) := by
  rw [rtj_rowCopy_eq, rtj_rowCopy_eq, rtj_rowCopy_eq, map_mul]
  congr 1
  ext x
  rw [MvPowerSeries.coeff_rename]
  show _ = ∑ k ∈ Finset.range (x.degree + 1),
    MvPowerSeries.coeff x ((MvPowerSeries.rename (rtjR b) L) ^ k) / (k.factorial : C)
  simp_rw [← map_pow, MvPowerSeries.coeff_rename, Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => ?_
  have hdeg : y.degree = x.degree := by
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Set.mem_preimage] at hy
    rw [← hy, Finsupp.degree_mapDomain]
  show ∑ k ∈ Finset.range (y.degree + 1), _ = _
  rw [hdeg]

end VP

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}

def P2 (a b : Fin dd → MvPowerSeries τ C) : Fin 2 × Fin dd → MvPowerSeries τ C :=
  fun q => if q.1 = 0 then a q.2 else b q.2

def P3 (a b c : Fin dd → MvPowerSeries τ C) : Fin 3 × Fin dd → MvPowerSeries τ C :=
  fun q => if q.1 = 0 then a q.2 else if q.1 = 1 then b q.2 else c q.2

theorem constantCoeff_pair_substitution {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (q : Fin 2 × Fin dd) :
    MvPowerSeries.constantCoeff (P2 a b q) = 0 := by
  unfold P2
  split_ifs
  exacts [ha _, hb _]

theorem constantCoeff_triple_substitution {a b c : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) (hc : ∀ i, MvPowerSeries.constantCoeff (c i) = 0)
    (q : Fin 3 × Fin dd) : MvPowerSeries.constantCoeff (P3 a b c q) = 0 := by
  unfold P3
  split_ifs
  exacts [ha _, hb _, hc _]

theorem integral_pair_substitution {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, IntS V (a i)) (hb : ∀ i, IntS V (b i))
    (q : Fin 2 × Fin dd) : IntS V (P2 a b q) := by
  unfold P2
  split_ifs
  exacts [ha _, hb _]

theorem integral_triple_substitution {a b c : Fin dd → MvPowerSeries τ C} (ha : ∀ i, IntS V (a i)) (hb : ∀ i, IntS V (b i))
    (hc : ∀ i, IntS V (c i)) (q : Fin 3 × Fin dd) : IntS V (P3 a b c q) := by
  unfold P3
  split_ifs
  exacts [ha _, hb _, hc _]

theorem subst_sub' {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f g : MvPowerSeries σ C) :
    MvPowerSeries.subst a (f - g) = MvPowerSeries.subst a f - MvPowerSeries.subst a g := by
  rw [← MvPowerSeries.coe_substAlgHom (VP.hs ha)]
  exact map_sub _ f g

theorem subst_add' {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f g : MvPowerSeries σ C) :
    MvPowerSeries.subst a (f + g) = MvPowerSeries.subst a f + MvPowerSeries.subst a g := by
  rw [← MvPowerSeries.coe_substAlgHom (VP.hs ha)]
  exact map_add _ f g

theorem cc_pt {n : ℕ} (g : Fin n) (i : Fin dd) : MvPowerSeries.constantCoeff (pt C dd g i) = 0 := MvPowerSeries.constantCoeff_X _

theorem toK_eq {n : ℕ} (f : PS C n dd) : FB.toK C f = f := by
  unfold FB.toK
  simp

variable (Y : FBChart C V O dd)

def hAt (a b : Fin dd → MvPowerSeries τ C) : MvPowerSeries τ C := MvPowerSeries.subst (P2 a b) Y.h

def actAt (x : O) (a : Fin dd → MvPowerSeries τ C) : Fin dd → MvPowerSeries τ C :=
  fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (Y.B.A.act x i)

def addAt (a b : Fin dd → MvPowerSeries τ C) : Fin dd → MvPowerSeries τ C :=
  fun i => MvPowerSeries.subst (P2 a b) (Y.B.G.F i)

theorem cc_hAt {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) : MvPowerSeries.constantCoeff (hAt Y a b) = 0 := by
  unfold hAt
  exact VP.cc_subst (constantCoeff_pair_substitution ha hb) (cc_h Y)

theorem cc_actAt (x : O) {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (i : Fin dd) : MvPowerSeries.constantCoeff (actAt Y x a i) = 0 := by
  unfold actAt
  exact VP.cc_subst (fun q : Fin 1 × Fin dd => ha q.2) (Y.B.A.const x i)

theorem eval_two_points_eq_subst {n m : ℕ} (a b : Pt C n dd) (f : PS C 2 dd) (_hm : m = 2) : ev ![a, b] f = MvPowerSeries.subst (P2 a b) f := by
  unfold ev
  congr 1
  funext q
  rcases q with ⟨i, k⟩
  fin_cases i <;> simp [P2]

theorem actK_eq (x : O) (i : Fin dd) : Y.B.actK C x i = Y.B.A.act x i := by
  unfold FB.actK
  exact toK_eq _

theorem compose_one_action_eq_actAt {n : ℕ} (x : O) (a : Pt C n dd) : comp1 (Y.B.actK C x) a = actAt Y x a := by
  funext i
  simp only [comp1, ev, actAt, actK_eq, Matrix.cons_val_fin_one]

variable {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
  (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0)

include ha hb

theorem pair_subst_coordinate (g : Fin 2) (i : Fin dd) :
    MvPowerSeries.subst (P2 a b) (pt C dd g i) = P2 a b (g, i) := by
  rw [show pt C dd g i = (MvPowerSeries.X (g, i) : MvPowerSeries (Fin 2 × Fin dd) C) from rfl]
  exact VP.subst_X (constantCoeff_pair_substitution ha hb) (g, i)

theorem sy_at : MvPowerSeries.subst (P2 a b) Y.B.sy = mvExp (hAt Y b a - hAt Y a b) := by
  obtain ⟨-, -, -, -, hsy, -⟩ := Y.gauge
  rw [toK_eq] at hsy
  have hP10 : ∀ q, MvPowerSeries.constantCoeff (P2 (pt C dd 1) (pt C dd 0) q : PS C 2 dd) = 0 :=
    constantCoeff_pair_substitution (cc_pt 1) (cc_pt 0)
  have hswap : MvPowerSeries.subst (P2 a b) (ev ![pt C dd 1, pt C dd 0] Y.h) = hAt Y b a := by
    rw [eval_two_points_eq_subst (m := 2) _ _ _ rfl, VP.subst_subst hP10 (constantCoeff_pair_substitution ha hb)]
    unfold hAt
    congr 1
    funext q
    rcases q with ⟨i, k⟩
    fin_cases i
    · show MvPowerSeries.subst (P2 a b) (pt C dd 1 k) = b k
      rw [pair_subst_coordinate ha hb]
      rfl
    · show MvPowerSeries.subst (P2 a b) (pt C dd 0 k) = a k
      rw [pair_subst_coordinate ha hb]
      rfl
  have hcc : MvPowerSeries.constantCoeff (ev ![pt C dd 1, pt C dd 0] Y.h - Y.h) = 0 := by
    rw [map_sub, eval_two_points_eq_subst (m := 2) _ _ _ rfl, VP.cc_subst hP10 (cc_h Y), cc_h Y, sub_zero]
  rw [hsy, expS_eq _ hcc, subst_exp (constantCoeff_pair_substitution ha hb) hcc, subst_sub' (constantCoeff_pair_substitution ha hb), hswap]
  rfl

theorem actAt_pt (x : O) (g : Fin 2) (i : Fin dd) :
    MvPowerSeries.subst (P2 a b) (actAt Y x (pt C dd g) i) = actAt Y x (fun j => P2 a b (g, j)) i := by
  unfold actAt
  rw [VP.subst_subst (fun q : Fin 1 × Fin dd => cc_pt g q.2) (constantCoeff_pair_substitution ha hb)]
  congr 1
  funext q
  exact pair_subst_coordinate ha hb g q.2

theorem ad_at (x : O) :
    MvPowerSeries.subst (P2 a b) (Y.B.ad x) = mvExp (hAt Y (actAt Y x a) b - hAt Y a (actAt Y (star x) b)) := by
  obtain ⟨-, -, -, -, -, had⟩ := Y.gauge
  have hx := had x
  rw [toK_eq, compose_one_action_eq_actAt Y x, compose_one_action_eq_actAt Y (star x)] at hx
  have hA0 : ∀ i, MvPowerSeries.constantCoeff (actAt Y x (pt C dd 0) i : PS C 2 dd) = 0 :=
    cc_actAt Y x (cc_pt (n := 2) 0)
  have hA1 : ∀ i, MvPowerSeries.constantCoeff (actAt Y (star x) (pt C dd 1) i : PS C 2 dd) = 0 :=
    cc_actAt Y (star x) (cc_pt (n := 2) 1)
  have hQ1 : ∀ q, MvPowerSeries.constantCoeff (P2 (actAt Y x (pt C dd 0)) (pt C dd 1) q : PS C 2 dd) = 0 :=
    constantCoeff_pair_substitution hA0 (cc_pt (n := 2) 1)
  have hQ2 : ∀ q, MvPowerSeries.constantCoeff (P2 (pt C dd 0) (actAt Y (star x) (pt C dd 1)) q : PS C 2 dd) = 0 :=
    constantCoeff_pair_substitution (cc_pt (n := 2) 0) hA1
  have e1 : MvPowerSeries.subst (P2 a b) (ev ![actAt Y x (pt C dd 0), pt C dd 1] Y.h) = hAt Y (actAt Y x a) b := by
    rw [eval_two_points_eq_subst (m := 2) _ _ _ rfl, VP.subst_subst hQ1 (constantCoeff_pair_substitution ha hb)]
    unfold hAt
    congr 1
    funext q
    rcases q with ⟨i, k⟩
    fin_cases i
    · show MvPowerSeries.subst (P2 a b) (actAt Y x (pt C dd 0) k) = actAt Y x a k
      rw [actAt_pt Y ha hb]
      rfl
    · show MvPowerSeries.subst (P2 a b) (pt C dd 1 k) = b k
      rw [pair_subst_coordinate ha hb]
      rfl
  have e2 : MvPowerSeries.subst (P2 a b) (ev ![pt C dd 0, actAt Y (star x) (pt C dd 1)] Y.h) =
      hAt Y a (actAt Y (star x) b) := by
    rw [eval_two_points_eq_subst (m := 2) _ _ _ rfl, VP.subst_subst hQ2 (constantCoeff_pair_substitution ha hb)]
    unfold hAt
    congr 1
    funext q
    rcases q with ⟨i, k⟩
    fin_cases i
    · show MvPowerSeries.subst (P2 a b) (pt C dd 0 k) = a k
      rw [pair_subst_coordinate ha hb]
      rfl
    · show MvPowerSeries.subst (P2 a b) (actAt Y (star x) (pt C dd 1) k) = actAt Y (star x) b k
      rw [actAt_pt Y ha hb]
      rfl
  have hcc : MvPowerSeries.constantCoeff (ev ![actAt Y x (pt C dd 0), pt C dd 1] Y.h -
      ev ![pt C dd (0 : Fin 2), actAt Y (star x) (pt C dd (1 : Fin 2))] Y.h) = 0 := by
    rw [map_sub, eval_two_points_eq_subst (m := 2) _ _ _ rfl, eval_two_points_eq_subst (m := 2) _ _ _ rfl, VP.cc_subst hQ1 (cc_h Y),
      VP.cc_subst hQ2 (cc_h Y), sub_zero]
  rw [hx, expS_eq _ hcc, subst_exp (constantCoeff_pair_substitution ha hb) hcc, subst_sub' (constantCoeff_pair_substitution ha hb), e1, e2]

end VP

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePLSmall

open PartialDerivEval RowTiePE0 RowTiePProj

section Main

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem lg_const (Y : FBChart C V O dd) (i : Fin dd) : constantCoeff (Y.lg i) = 0 := by
  have h := Y.lg_lin i 0 (by simp)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  simp [MvPowerSeries.coeff_X]
  exact (Finsupp.single_ne_zero.2 one_ne_zero).symm

theorem germEval_oneStandardPoint_self (f : PS C 1 dd) : ev (n := 1) ![pt C dd 0] f = f := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  have : (fun p : Fin 1 × Fin dd => (![pt C dd 0] : Fin 1 → Pt C 1 dd) p.1 p.2) = X := by
    funext p
    obtain ⟨k, j⟩ := p
    fin_cases k
    rfl
  rw [this, subst_self]
  rfl

theorem formalGroupLaw_ev_x_zero (Y : FBChart C V O dd) {n : ℕ} (A : Pt C n dd) (hA : ∀ j, constantCoeff (A j) = 0) (i : Fin dd) :
    ev (![A, 0] : Fin 2 → Pt C n dd) (Y.B.G.F i) = A i := by
  have hZ : Z0 (![A, 0] : Fin 2 → Pt C n dd) := z0_p0 A hA
  conv_lhs => rw [← Y.B.G.comm i]
  rw [ev_ev (z0_pp 1 0) hZ]
  have e1 : (fun k j => ev (![A, 0] : Fin 2 → Pt C n dd) ((![pt C dd 1, pt C dd 0] : Fin 2 → Pt C 2 dd) k j)) =
      ![0, A] := by
    funext k j; fin_cases k
    · exact ev_X hZ 1 j
    · exact ev_X hZ 0 j
  rw [e1]
  have hB : Z0 (![A] : Fin 1 → Pt C n dd) := z0_1 _ hA
  have hU : Z0 (![0, pt C dd 0] : Fin 2 → Pt C 1 dd) := by
    intro k j; fin_cases k
    · simp
    · exact z0_pt 0 j
  have e2 : (![0, A] : Fin 2 → Pt C n dd) =
      fun k j => ev (![A] : Fin 1 → Pt C n dd) ((![0, pt C dd 0] : Fin 2 → Pt C 1 dd) k j) := by
    funext k j; fin_cases k
    · exact (ev_zero hB).symm
    · exact (ev_X hB 0 j).symm
  rw [e2, ← ev_ev hU hB, Y.B.G.unit i, ev_X hB]
  rfl

theorem lg_addOf (Y : FBChart C V O dd) {n : ℕ} (P Q : Pt C n dd) (hP : ∀ j, constantCoeff (P j) = 0)
    (hQ : ∀ j, constantCoeff (Q j) = 0) (i : Fin dd) :
    ev ![addOf Y.B.G.F P Q] (Y.lg i) = ev ![P] (Y.lg i) + ev ![Q] (Y.lg i) := by
  have hPQ : Z0 (![P, Q] : Fin 2 → Pt C n dd) := constant_zero_two_points P Q hP hQ
  have h := congrArg (ev (![P, Q] : Fin 2 → Pt C n dd)) (Y.lg_add i)
  rw [ev_add hPQ] at h
  have hA : Z0 (![addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)] : Fin 1 → Pt C 2 dd) :=
    z0_1 _ (fun j => const_addOf Y 0 1 j)
  rw [ev_ev hA hPQ, ev_ev (z0_1 _ (z0_pt 0)) hPQ, ev_ev (z0_1 _ (z0_pt 1)) hPQ] at h
  have e1 : (fun k j => ev (![P, Q] : Fin 2 → Pt C n dd)
      ((![addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)] : Fin 1 → Pt C 2 dd) k j)) =
      ![addOf Y.B.G.F P Q] := by
    funext k j
    rw [Fin.fin_one_eq_zero k]
    show ev (![P, Q] : Fin 2 → Pt C n dd) (ev ![pt C (n := 2) dd 0, pt C (n := 2) dd 1] (Y.B.G.F j)) =
      ev ![P, Q] (Y.B.G.F j)
    rw [ev_ev (z0_pp 0 1) hPQ]
    congr 1
    funext k' j'
    fin_cases k'
    · exact ev_X hPQ 0 j'
    · exact ev_X hPQ 1 j'
  have e2 : (fun k j => ev (![P, Q] : Fin 2 → Pt C n dd) ((![pt C (n := 2) dd 0] : Fin 1 → Pt C 2 dd) k j)) = ![P] := by
    funext k j
    rw [Fin.fin_one_eq_zero k]
    exact ev_X hPQ 0 j
  have e3 : (fun k j => ev (![P, Q] : Fin 2 → Pt C n dd) ((![pt C (n := 2) dd 1] : Fin 1 → Pt C 2 dd) k j)) = ![Q] := by
    funext k j
    rw [Fin.fin_one_eq_zero k]
    exact ev_X hPQ 1 j
  rw [e1, e2, e3] at h
  exact h

theorem lg_act_nat (Y : FBChart C V O dd) (k : ℕ) (i : Fin dd) :
    ev ![Y.B.A.act (k : O)] (Y.lg i) = MvPowerSeries.C (k : C) * Y.lg i := by
  have act0 := Y.B.A.const
  induction k with
  | zero =>
    have h0 : Y.B.A.act ((0 : ℕ) : O) = addOf Y.B.G.F (Y.B.A.act ((0 : ℕ) : O)) (Y.B.A.act ((0 : ℕ) : O)) := by
      have := Y.B.A.add_act 0 0
      rw [add_zero] at this
      rw [Nat.cast_zero]; exact this
    have h := lg_addOf Y (Y.B.A.act ((0 : ℕ) : O)) (Y.B.A.act ((0 : ℕ) : O)) (act0 _) (act0 _) i
    rw [← h0] at h
    simp only [Nat.cast_zero, map_zero, zero_mul] at h ⊢
    linear_combination -h
  | succ k ih =>
    have h1 : Y.B.A.act ((k + 1 : ℕ) : O) = addOf Y.B.G.F (Y.B.A.act (k : O)) (pt C dd 0) := by
      rw [Nat.cast_succ, Y.B.A.add_act, Y.B.A.one_act]
    rw [h1, lg_addOf Y _ _ (act0 _) (z0_pt 0) i, ih, germEval_oneStandardPoint_self, Nat.cast_succ, map_add (f := _), map_one]
    ring

theorem ex_lg_comp (Y : FBChart C V O dd) {n : ℕ} (φ : Pt C n dd) (hφ : ∀ j, constantCoeff (φ j) = 0) (i : Fin dd) :
    ev ![fun j => ev ![φ] (Y.lg j)] (Y.ex i) = φ i := by
  have hφ1 : Z0 (![φ] : Fin 1 → Pt C n dd) := z0_1 φ hφ
  have hlg : Z0 (![Y.lg] : Fin 1 → Pt C 1 dd) := z0_1 _ (lg_const Y)
  have e1 : (![fun j => ev ![φ] (Y.lg j)] : Fin 1 → Pt C n dd) =
      fun k j => ev (![φ] : Fin 1 → Pt C n dd) ((![Y.lg] : Fin 1 → Pt C 1 dd) k j) := by
    funext k j; rw [Fin.fin_one_eq_zero k]; rfl
  rw [e1, ← ev_ev hlg hφ1]
  have e2 : ev (![Y.lg] : Fin 1 → Pt C 1 dd) (Y.ex i) = pt C dd 0 i := congrFun Y.ex_lg i
  rw [e2]
  exact ev_X hφ1 0 i

end Main

end RowTiePLSmall

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def exZero (Y : FBChart C V O dd) : Fin 2 × Fin dd → MvPowerSeries (Fin dd) C :=
  fun q => if q.1 = 0 then un1 (Y.ex q.2) else 0

def ExpODESt (Y : FBChart C V O dd) : Prop :=
  ∀ i j : Fin dd, MvPowerSeries.pderiv (R := C) i (un1 (Y.ex j)) =
    MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.FK C j))

namespace VP

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

theorem cc_exZero (q : Fin 2 × Fin dd) : MvPowerSeries.constantCoeff (exZero Y q) = 0 := by
  unfold exZero
  split_ifs
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.ex q.2) = 0
    rw [Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact Y.ex_const _
  · exact map_zero _

theorem subst_zero' {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.subst a (0 : MvPowerSeries σ C) = 0 := by
  rw [← MvPowerSeries.coe_substAlgHom (Formalism.L2.FormalSeriesBounds.VP.hs ha), map_zero]

theorem constantCoeff_two_points_zero {n : ℕ} (b : Fin n) (q : Fin 2 × Fin dd) :
    MvPowerSeries.constantCoeff ((![pt C dd b, 0] : Fin 2 → Pt C n dd) q.1 q.2) = 0 := by
  rcases q with ⟨i, j⟩
  fin_cases i
  · simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  · simp

end VP

end Formalism.L2.FormalSeriesBounds
end
end
