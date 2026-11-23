module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieDefs
public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
public import Formalism.FormalGroupLog.FormalGroupLogProofs.ChainRule
public import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
public import Formalism.LocalToGlobal.CharacterGerms.Bundle011
public import Formalism.LocalToGlobal.CharacterGerms.Bundle014
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePLSmallMain
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePFBMapSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.Bundle001
public import Formalism.LocalToGlobal.CharacterGerms.CharacteristicFromRanks
public import Formalism.LocalToGlobal.CharacterGerms.Bundle016
public import Formalism.LocalToGlobal.CharacterGerms.Bundle007
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.CharacterGerms.Bundle015
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGerm
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.LocalToGlobal.CharacterGerms.CoeffSubstEqSum
import Formalism.LocalToGlobal.CharacterGerms.Bundle001

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds PartialDerivEval RowTiePCEq ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

namespace RowTiePCEqSum

theorem subst_zero_const {σ τ : Type} [Finite σ] (f : MvPowerSeries σ C) (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst (fun _ : σ => (0 : MvPowerSeries τ C)) f = 0 := by
  ext e
  rw [MvPowerSeries.coeff_subst MvPowerSeries.HasSubst.zero, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro n
  by_cases hn : n = 0
  · subst hn
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hn
    have hs' : n s ≠ 0 := by simpa using hs
    have : (n.prod fun s e => (0 : MvPowerSeries τ C) ^ e) = 0 :=
      Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.2 hs') (zero_pow hs')
    rw [this, map_zero, smul_zero]

theorem hasSubst_unit {τ : Type} {T : MvPowerSeries τ C} (hT : MvPowerSeries.constantCoeff T = 0) :
    MvPowerSeries.HasSubst (fun _ : Unit => T) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hT)

theorem subst_lin {σ τ : Type} {a : σ → MvPowerSeries τ C} (ha : MvPowerSeries.HasSubst a) {ι : Type}
    (s : Finset ι) (r : ι → C) (F : ι → MvPowerSeries σ C) :
    MvPowerSeries.subst a (∑ i ∈ s, r i • F i) = ∑ i ∈ s, r i • MvPowerSeries.subst a (F i) := by

  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  first
  | exact map_smul _ _ _
  | exact AlgHom.map_smul_of_tower _ _ _

theorem coeff_subst_tyS {τ : Type} [Finite τ] {l : ℕ} (hl : 2 ≤ l) {T : MvPowerSeries τ C}
    (hT : MvPowerSeries.constantCoeff T = 0) (a : ℕ → C) (μ : τ →₀ ℕ) :
    MvPowerSeries.coeff μ (MvPowerSeries.subst (fun _ : Unit => T) (tyS l a)) =
      ∑ s ∈ Finset.range (μ.degree + 1), a s * MvPowerSeries.coeff μ (T ^ (l ^ s)) := by
  set N := μ.degree + 1 with hN
  set P : PowerSeries C := ∑ s ∈ Finset.range N, a s • PowerSeries.X ^ (l ^ s) with hP
  have hPc : ∀ m < l ^ N, PowerSeries.coeff m (tyS l a) = PowerSeries.coeff m P := by
    intro m hm

    rw [hP, map_sum]
    simp only [PowerSeries.coeff_smul, PowerSeries.coeff_X_pow]
    by_cases h : ∃ s', l ^ s' = m
    · obtain ⟨s', rfl⟩ := h
      rw [coeff_tyS_pow hl, Finset.sum_eq_single s']
      · simp
      · intro s _ hs
        rw [if_neg, smul_zero]
        intro h
        exact hs (Nat.pow_right_injective hl h).symm
      · intro h
        exfalso
        apply h
        rw [Finset.mem_range]
        exact (Nat.pow_lt_pow_iff_right (by omega)).1 hm
    · push Not at h
      rw [coeff_tyS_of_ne a m h]
      symm
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [if_neg (h s).symm, smul_zero]
  have hAg : Formalism.G.LogCR.Agree N (tyS l a : MvPowerSeries Unit C) (P : MvPowerSeries Unit C) := by
    intro e he
    have hes : e = Finsupp.single () (e ()) := Finsupp.unique_single e
    rw [hes] at he ⊢
    rw [Finsupp.degree_single] at he
    exact hPc _ (lt_of_lt_of_le he (Nat.lt_pow_self (by omega)).le)
  have h1 := Formalism.G.LogCR.Agree.subst (a := fun _ : Unit => T) (a' := fun _ : Unit => T) (fun _ => hT) (fun _ => hT) hAg
    (fun _ _ _ => rfl) μ (by omega)

  rw [h1, hP, ← MvPowerSeries.coe_substAlgHom (hasSubst_unit hT), map_sum, map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_smul, map_pow, MvPowerSeries.coe_substAlgHom]
  rw [show (PowerSeries.X : PowerSeries C) = (MvPowerSeries.X () : MvPowerSeries Unit C) from rfl,
    MvPowerSeries.subst_X (hasSubst_unit hT), MvPowerSeries.coeff_smul]

section Add

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)

end Add

end RowTiePCEqSum


end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePLie

open PartialDerivEval RowTiePE0 RowTiePProj RowTiePLSmall RowTiePSplit

section Lin

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

def linM (φ : Pt C 1 dd) : Matrix (Fin dd) (Fin dd) C :=
  Matrix.of fun i j => coeff (Finsupp.single ((0 : Fin 1), j) 1) (φ i)

theorem linAct_eq (φ : Pt C 1 dd) (v : Fin dd → C) : linAct φ v = Matrix.mulVec (linM φ) v := by
  funext i
  rfl

theorem coeff_single_cc {σ : Type} (s : σ) (f : MvPowerSeries σ C) :
    coeff (Finsupp.single s 1) f = constantCoeff (MvPowerSeries.pderiv (R := C) s f) := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

theorem cc_subst {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, constantCoeff (a s) = 0)
    (g : MvPowerSeries σ C) : constantCoeff (MvPowerSeries.subst a g) = constantCoeff g := by
  rw [MvPowerSeries.constantCoeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha), finsum_eq_single _ 0]
  · simp
  · intro d hd
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => a s ^ e) = 0 := by
      rw [map_finsuppProd]
      obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp hd
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs)
      show MvPowerSeries.constantCoeff (a s ^ d s) = 0
      rw [map_pow, ha s, zero_pow hs]
    rw [h0, smul_zero]

theorem lin_comp1 {φ ψ : Pt C 1 dd} (hψ : ∀ k, constantCoeff (ψ k) = 0) :
    linM (comp1 φ ψ) = linM φ * linM ψ := by
  ext i j
  simp only [linM, Matrix.of_apply, Matrix.mul_apply, coeff_single_cc]
  show constantCoeff (MvPowerSeries.pderiv (R := C) ((0 : Fin 1), j)
    (MvPowerSeries.subst (fun p : Fin 1 × Fin dd => (![ψ] : Fin 1 → Pt C 1 dd) p.1 p.2) (φ i))) = _

  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 1 × Fin dd => (![ψ] : Fin 1 → Pt C 1 dd) p.1 p.2)
  (fun p => (z0_1 ψ hψ) p.1 p.2), map_sum, Fintype.sum_prod_type, Fin.sum_univ_one]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, cc_subst (a := fun p : Fin 1 × Fin dd => (![ψ] : Fin 1 → Pt C 1 dd) p.1 p.2)
    (fun p => (z0_1 ψ hψ) p.1 p.2)]
  rfl

theorem lin_pt : linM (pt C (n := 1) dd 0) = 1 := by
  ext i j
  simp only [linM, pt, Matrix.of_apply, Matrix.one_apply, MvPowerSeries.coeff_X]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg, if_neg h]
    intro h2
    apply h
    have h3 := (Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)).mp h2
    exact (Prod.mk.inj h3).2.symm

theorem cc_pderiv_X {σ : Type} [DecidableEq σ] (s t : σ) : constantCoeff (MvPowerSeries.pderiv (R := C) s (X t : MvPowerSeries σ C)) = if t = s then 1 else 0 := by
  rw [MvPowerSeries.pderiv_X]
  by_cases h : t = s
  · subst h
    simp
  · simp [Pi.single_apply, h]

theorem formal_group_coeff_first_linear {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) (i j : Fin dd) :
    constantCoeff (MvPowerSeries.pderiv (R := C) ((0 : Fin 2), j) (Y.B.G.F i)) = if i = j then 1 else 0 := by
  have hA : Z0 (![pt C (n := 1) dd 0, 0] : Fin 2 → Pt C 1 dd) := z0_p0 _ (z0_pt 0)
  have h := congrArg (fun f => constantCoeff (MvPowerSeries.pderiv (R := C) ((0 : Fin 1), j) f)) (formalGroupLaw_ev_x_zero Y (pt C (n := 1) dd 0) (z0_pt 0) i)
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev at h

  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 2 × Fin dd => (![pt C (n := 1) dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
  (fun p => hA p.1 p.2), map_sum, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp only [map_mul, cc_subst (a := fun p : Fin 2 × Fin dd => (![pt C (n := 1) dd 0, 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
    (fun p => hA p.1 p.2), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, pt, Pi.zero_apply, map_zero,
    mul_zero, Finset.sum_const_zero, add_zero, cc_pderiv_X, Prod.mk.injEq, true_and, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [h]

theorem formal_group_coeff_second_linear {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) (i j : Fin dd) :
    constantCoeff (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), j) (Y.B.G.F i)) = if i = j then 1 else 0 := by
  have hA : Z0 (![0, pt C (n := 1) dd 0] : Fin 2 → Pt C 1 dd) := by
    intro k j'; fin_cases k
    · simp
    · exact z0_pt 0 j'
  have h := congrArg (fun f => constantCoeff (MvPowerSeries.pderiv (R := C) ((0 : Fin 1), j) f)) (Y.B.G.unit i)
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev at h

  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 2 × Fin dd => (![0, pt C (n := 1) dd 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
  (fun p => hA p.1 p.2), map_sum, Fintype.sum_prod_type, Fin.sum_univ_two] at h
  simp only [map_mul, cc_subst (a := fun p : Fin 2 × Fin dd => (![0, pt C (n := 1) dd 0] : Fin 2 → Pt C 1 dd) p.1 p.2)
    (fun p => hA p.1 p.2), Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, pt, Pi.zero_apply, map_zero,
    mul_zero, Finset.sum_const_zero, zero_add, cc_pderiv_X, Prod.mk.injEq, true_and, mul_ite, mul_one,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [h]

theorem lin_addOf {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) {A B : Pt C 1 dd}
    (hA : ∀ k, constantCoeff (A k) = 0) (hB : ∀ k, constantCoeff (B k) = 0) :
    linM (addOf Y.B.G.F A B) = linM A + linM B := by
  have hZ : Z0 (![A, B] : Fin 2 → Pt C 1 dd) := constant_zero_two_points A B hA hB
  ext i j
  simp only [linM, Matrix.of_apply, Matrix.add_apply, coeff_single_cc]
  show constantCoeff (MvPowerSeries.pderiv (R := C) ((0 : Fin 1), j)
    (MvPowerSeries.subst (fun p : Fin 2 × Fin dd => (![A, B] : Fin 2 → Pt C 1 dd) p.1 p.2) (Y.B.G.F i))) = _

  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 2 × Fin dd => (![A, B] : Fin 2 → Pt C 1 dd) p.1 p.2)
  (fun p => hZ p.1 p.2), map_sum, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [map_mul, cc_subst (a := fun p : Fin 2 × Fin dd => (![A, B] : Fin 2 → Pt C 1 dd) p.1 p.2)
    (fun p => hZ p.1 p.2), formal_group_coeff_first_linear Y, formal_group_coeff_second_linear Y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Lin

section Glue

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def linHom (Y : FBChart C V O dd) : O →+* Matrix (Fin dd) (Fin dd) C where
  toFun x := linM (Y.B.A.act x)
  map_one' := by rw [Y.B.A.one_act]; exact lin_pt
  map_mul' x y := by rw [Y.B.A.mul_act]; exact lin_comp1 (Y.B.A.const y)
  map_zero' := by
    have e := Y.B.A.add_act 0 0
    rw [add_zero] at e
    have h : linM (Y.B.A.act 0) = linM (Y.B.A.act 0) + linM (Y.B.A.act 0) := by
      conv_lhs => rw [e]
      exact lin_addOf Y (Y.B.A.const 0) (Y.B.A.const 0)
    have h2 := congrArg (fun M => M - linM (Y.B.A.act 0)) h
    simp only [sub_self, add_sub_cancel_right] at h2
    exact h2.symm
  map_add' x y := by rw [Y.B.A.add_act]; exact lin_addOf Y (Y.B.A.const x) (Y.B.A.const y)

theorem proj_core (Y : FBChart C V O dd) (ε : O) (hε : ∃ y, ε * ε - ε = (V.l : O) * y) (e : Pt C 1 dd)
    (he : ∀ (N : ℕ) i μ, ∃ n0 : ℕ, ∀ n ≥ n0,
      V.Ge N (MvPowerSeries.coeff μ (e i) - MvPowerSeries.coeff μ (Y.B.A.act (ε ^ V.l ^ n) i))) :
    (∀ i, MvPowerSeries.constantCoeff (e i) = 0) ∧ comp1 e e = e ∧
      (∀ a, comp1 e (Y.B.A.act a) = comp1 (Y.B.A.act a) e) := by
  have hT := tends_of_endomorphism_limit Y he
  have e0 : ∀ i, constantCoeff (e i) = 0 := const_of_lim Y hT
  have act0 : ∀ x i, constantCoeff (Y.B.A.act x i) = 0 := Y.B.A.const
  refine ⟨e0, ?_, ?_⟩
  · funext i
    have L := TendsS.comp1 (φ := fun n => Y.B.A.act (ε ^ V.l ^ n)) (b := fun n => Y.B.A.act (ε ^ V.l ^ n))
      (fun n => act0 _) e0 hT hT i
    have R := tendsS_of_small lSmall_holds Y (x := fun n => ε ^ V.l ^ n * ε ^ V.l ^ n) (sq_cong hε) hT i
    have eq : (fun n => comp1 (Y.B.A.act (ε ^ V.l ^ n)) (Y.B.A.act (ε ^ V.l ^ n)) i) =
        fun n => Y.B.A.act (ε ^ V.l ^ n * ε ^ V.l ^ n) i := funext fun n => by rw [Y.B.A.mul_act]
    rw [eq] at L
    exact L.unique R
  · intro a
    funext i
    have L := TendsS.comp1 (φ := fun n => Y.B.A.act (ε ^ V.l ^ n)) (b := fun _ => Y.B.A.act a)
      (fun _ => act0 a) (act0 a) hT (fun _ => TendsS.const _) i
    have R := TendsS.comp1 (φ := fun _ => Y.B.A.act a) (b := fun n => Y.B.A.act (ε ^ V.l ^ n))
      (fun n => act0 _) e0 (fun _ => TendsS.const _) hT i
    have eq : (fun n => comp1 (Y.B.A.act (ε ^ V.l ^ n)) (Y.B.A.act a) i) =
        fun n => comp1 (Y.B.A.act a) (Y.B.A.act (ε ^ V.l ^ n)) i := funext fun n => by
      rw [← Y.B.A.mul_act, ← Y.B.A.mul_act, mul_comm]
    rw [eq] at L
    exact L.unique R

end Glue

end RowTiePLie

end Formalism.L2.FormalSeriesBounds
end
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ CharacteristicFromRanks ValuationFitting
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (IsCh dl res HasAF)

section Series

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ}
variable {R : Type} [CommRing R] [Algebra R C]

abbrev toC {n : ℕ} (f : PS R n dd) : PS C n dd := MvPowerSeries.map (algebraMap R C) f

theorem mpt_pt {n : ℕ} (j : Fin n) : MapFB.mpt (algebraMap R C) (pt R dd j) = pt C dd j := by
  funext i
  simp [MapFB.mpt, pt]

theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin dd) : MvPowerSeries.constantCoeff (pt R dd j i) = 0 := by
  simp [pt]

theorem isChar_of_isCh (Y : FBChart C V OE dd) (hR : ∀ x : R, V.Ge 0 (algebraMap R C x))
    (FR : Fin dd → PS R 2 dd) (hF : ∀ i, Y.B.G.F i = toC (FR i))
    (hF0 : ∀ i, MvPowerSeries.constantCoeff (FR i) = 0) {u : PS R 1 dd} (hu : IsCh FR u) :
    Y.IsChar (toC u) := by
  refine ⟨fun μ => ?_, ?_, ?_⟩
  · rw [MvPowerSeries.coeff_map]; exact hR _
  · rw [MvPowerSeries.constantCoeff_map, hu.1, map_one]
  · have h := congrArg (MvPowerSeries.map (algebraMap R C)) hu.2
    have hadd : ∀ i, MvPowerSeries.constantCoeff (addOf FR (pt R (n := 2) dd 0) (pt R (n := 2) dd 1) i) = 0 := by
      intro i
      refine MapFB.cc_ev _ ?_ _ (hF0 i)
      intro j i'
      fin_cases j <;> simp [pt]
    rw [map_mul, MapFB.map_ev1 _ _ hadd, MapFB.map_ev1 _ _ (cc_pt 0), MapFB.map_ev1 _ _ (cc_pt 1), mpt_pt, mpt_pt] at h
    have e : MapFB.mpt (algebraMap R C) (addOf FR (pt R (n := 2) dd 0) (pt R (n := 2) dd 1)) =
        addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) := by
      funext i
      show MvPowerSeries.map (algebraMap R C) (ev ![pt R (n := 2) dd 0, pt R (n := 2) dd 1] (FR i)) = _
      rw [MapFB.map_ev2 _ _ _ (cc_pt 0) (cc_pt 1), mpt_pt, mpt_pt]
      show _ = ev ![pt C (n := 2) dd 0, pt C (n := 2) dd 1] (Y.B.G.F i)
      rw [hF i]
    rw [e] at h
    exact h

end Series

section Len

theorem lenCoker_mono {R : Type} [CommRing R] (v : AddValuation R (WithTop ℝ)) {m h h' : ℕ}
    (B : Matrix (Fin m) (Fin h') R) (f : Fin h → Fin h') :
    S4.lenCoker v B ≤ S4.lenCoker v (B.submatrix id f) := by
  unfold S4.lenCoker
  refine Finset.le_inf fun g _ => ?_
  exact Finset.inf_le (f := fun g : Fin m → Fin h' => v (B.submatrix id g).det) (Finset.mem_univ (f ∘ g))

variable {C : Type} [Field C] {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C] {dd : ℕ}

theorem lenCoker_le_of_hasLen (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ))
    (h1 : (vm (V.l : C) : ℝ) < 1) {s N : ℕ} (W : Fin s → Fin dd → R) (u : Fin N → PS R 1 dd) {x : NNReal}
    (hx : ReciprocityTheory.PGsh.Up.HasLen vm R
      ((Fin s → R) ⧸ Submodule.span R (Set.range fun k => res W (dl (u k)))) x)
    {S : ℝ} (hS : vm (V.l : C) ^ S ≤ x) :
    S4.lenCoker V.v (Matrix.of fun c k => ∑ i, dlogC (toC (C := C) (u k)) i * algebraMap R C (W c i)) ≤
      ((S : ℝ) : WithTop ℝ) := by
  set α : Matrix (Fin s) (Fin N) R := Matrix.of fun c k => res W (dl (u k)) c with hα
  have hr : LinearMap.range α.mulVecLin = Submodule.span R (Set.range fun k => res W (dl (u k))) := by
    rw [Matrix.range_mulVecLin]
    rfl
  rw [← hr] at hx
  have hSr : (vm (V.l : C) : ℝ) ^ S ≤ (x : ℝ) := by exact_mod_cast hS
  have hpos : 0 < (x : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos h0 S) hSr
  have e := lenCoker_eq_logb hT hv h0 h1 α hx hpos
  have e2 : (Matrix.of fun c k => ∑ i, dlogC (toC (C := C) (u k)) i * algebraMap R C (W c i)) =
      Matrix.of fun c k => algebraMap R C (α c k) := by
    ext c k

    simp only [Matrix.of_apply, hα, res, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, map_sum, map_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e2, e]
  refine WithTop.coe_le_coe.mpr ?_
  have h2 : Real.logb (vm (V.l : C) : ℝ) x ≤ Real.logb (vm (V.l : C) : ℝ) ((vm (V.l : C) : ℝ) ^ S) :=
    (Real.logb_le_logb_of_base_lt_one h0 h1 hpos (Real.rpow_pos_of_pos h0 S)).mpr hSr
  rwa [Real.logb_rpow h0 (ne_of_lt h1)] at h2

end Len

section Sum

theorem frobSum_conj_alt {d : ℕ} {l : ℕ} (hl : 1 < l) (n j j' : ℕ) (big : ZMod d → Prop)
    (halt : ∀ b, big (b + 1) ↔ ¬ big b) (q : ZMod d → ℕ)
    (hqb : ∀ b, big b → q b = j') (hqs : ∀ b, ¬ big b → q b = n + j) (a : ZMod d) (ha : big a) :
    S4.frobSum l q a = upB l (n + j) j' (gam l) := by
  rw [S4.frobSum_alt hl j' 0 (n + j) big halt q (fun b hb => by rw [hqb b hb]; rfl) hqs a ha]
  have h1 := S4.one_div_eq_gam_add_rho hl
  have hg : gam l = S4.gam l := rfl
  have hdiv : (j' : ℝ) / ((l : ℝ) - 1) = j' * (S4.gam l + S4.rho l) := by rw [← h1]; ring
  unfold upB
  rw [hg, hdiv]
  push_cast
  ring

theorem frobSum_conj_all {d : ℕ} {l : ℕ} (hl : 1 < l) (n j j' : ℕ) (q : ZMod d → ℕ) (hq : ∀ b, q b = j')
    (a : ZMod d) : S4.frobSum l q a = upB l (n + j) j' 0 := by
  rw [S4.frobSum_const hl j' q hq a]
  unfold upB
  ring

end Sum

section Core

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

end Core

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end
