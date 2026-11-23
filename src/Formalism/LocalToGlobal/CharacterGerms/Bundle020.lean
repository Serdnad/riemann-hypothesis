module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle014
import Formalism.LocalToGlobal.CharacterGerms.Bundle011
public import Formalism.LocalToGlobal.CharacterGerms.TripleSubstSecondCoordinate
public import Formalism.LocalToGlobal.CharacterGerms.Bundle018
public import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrI
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
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
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ τ' : Type}

def mapAt (ε : Pt C 1 dd) (a : Fin dd → MvPowerSeries τ C) : Fin dd → MvPowerSeries τ C :=
  fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => a q.2) (ε i)

theorem comp_eq_map_at {n : ℕ} (ε : Pt C 1 dd) (a : Pt C n dd) : comp1 ε a = mapAt ε a := by
  unfold comp1 mapAt ev
  funext i
  congr 1
  funext p
  first
    | (rw [Fin.fin_one_eq_zero p.1]; rfl)
    | (simp [Fin.fin_one_eq_zero p.1])

theorem cc_mapAt {ε : Pt C 1 dd} (hε : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0) {a : Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.constantCoeff (mapAt ε a i) = 0 := by
  unfold mapAt
  have hb : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => a q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => ha q.2)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst hb]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases he : e = 0
  · rw [he, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hε i, zero_smul]
  · rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    obtain ⟨s, hs⟩ := Finsupp.ne_iff.1 he
    have hmem : s ∈ e.support := Finsupp.mem_support_iff.2 (by simpa using hs)
    have h0 : MvPowerSeries.constantCoeff (e.prod fun s k => a s.2 ^ k) = 0 := by
      rw [Finsupp.prod, map_prod]
      apply Finset.prod_eq_zero hmem
      rw [map_pow, ha s.2, zero_pow (Finsupp.mem_support_iff.1 hmem)]
    rw [h0, smul_zero]

theorem mapAt_subst [Finite τ] {A : τ → MvPowerSeries τ' C} (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0)
    (ε : Pt C 1 dd) {u : Fin dd → MvPowerSeries τ C} (hu : ∀ i, MvPowerSeries.constantCoeff (u i) = 0) (i : Fin dd) :
    MvPowerSeries.subst A (mapAt ε u i) = mapAt ε (fun i => MvPowerSeries.subst A (u i)) i := by
  unfold mapAt
  have hb : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => u q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => hu q.2)
  have hA' : MvPowerSeries.HasSubst A := MvPowerSeries.hasSubst_of_constantCoeff_zero hA
  rw [MvPowerSeries.subst_comp_subst_apply hb hA']

theorem subst_pow' {σ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) (k : ℕ) :
    MvPowerSeries.subst a (f ^ k) = MvPowerSeries.subst a f ^ k := by
  have hb : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  first
    | exact MvPowerSeries.subst_pow hb f k
    | (rw [← MvPowerSeries.coe_substAlgHom hb, map_pow])

variable (Y : FBChart C V O dd)

theorem cmp_at {ε ε' : Pt C 1 dd} (hε : ∀ i, MvPowerSeries.constantCoeff (ε i) = 0)
    (hε' : ∀ i, MvPowerSeries.constantCoeff (ε' i) = 0) {a b : Fin dd → MvPowerSeries τ C}
    (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    MvPowerSeries.subst (P2 a b) (FB.expS C (ev (n := 2) ![comp1 ε (pt C dd 0), pt C dd 1] Y.h -
      ev (n := 2) ![pt C dd 0, comp1 ε' (pt C dd 1)] Y.h)) =
      mvExp (hAt Y (mapAt ε a) b - hAt Y a (mapAt ε' b)) := by
  rw [eval_two_points_eq_subst _ _ _ rfl, eval_two_points_eq_subst _ _ _ rfl, comp_eq_map_at, comp_eq_map_at]
  have k0 := cc_pt (C := C) (dd := dd) (0 : Fin 2)
  have k1 := cc_pt (C := C) (dd := dd) (1 : Fin 2)
  have hP := constantCoeff_pair_substitution ha hb
  have e0 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (0 : Fin 2) i)) = a := funext fun i => pair_subst_coordinate ha hb 0 i
  have e1 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (1 : Fin 2) i)) = b := funext fun i => pair_subst_coordinate ha hb 1 i
  have hcc : MvPowerSeries.constantCoeff (hAt Y (mapAt ε (pt C dd (0 : Fin 2))) (pt C dd (1 : Fin 2)) -
      hAt Y (pt C dd (0 : Fin 2)) (mapAt ε' (pt C dd (1 : Fin 2)))) = 0 := by
    rw [map_sub, cc_hAt Y (cc_mapAt hε k0) k1, cc_hAt Y k0 (cc_mapAt hε' k1), sub_zero]
  show MvPowerSeries.subst (P2 a b) (FB.expS C (hAt Y (mapAt ε (pt C dd (0 : Fin 2))) (pt C dd (1 : Fin 2)) -
      hAt Y (pt C dd (0 : Fin 2)) (mapAt ε' (pt C dd (1 : Fin 2))))) = _
  rw [expS_eq _ hcc, subst_exp hP hcc, subst_sub' hP, hAt_subst Y hP (cc_mapAt hε k0) k1,
    hAt_subst Y hP k0 (cc_mapAt hε' k1), e0, e1]
  congr 3
  · funext i; rw [mapAt_subst hP ε k0, e0]
  · funext i; rw [mapAt_subst hP ε' k1, e1]

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

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

variable (Y : FBChart C V O dd)

theorem coordinateChange_comp1_intertwines_action {n : ℕ} (x : O) (a : Pt C n dd) : comp1 (Y.B.A.act x) a = actAt Y x a := by
  unfold actAt
  unfold comp1
  funext i
  unfold ev
  first
  | rfl
  | (congr 1; funext q; simp)
  | (congr 1; funext q; skip)

theorem addOf_eq' {n : ℕ} (a b : Pt C n dd) : addOf Y.B.G.F a b = addAt Y a b := by
  unfold addAt
  unfold addOf
  funext i
  unfold ev
  first
  | rfl
  | (congr 1; funext q; unfold P2; rfl)
  | (congr 1; funext q; unfold P2; obtain ⟨j, k⟩ := q; fin_cases j <;> simp)

theorem actAt_addAt (x : O) {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    actAt Y x (addAt Y a b) = addAt Y (actAt Y x a) (actAt Y x b) := by
  have h := Y.B.A.hom x
  rw [show Y.B.G.add (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) = addAt Y (pt C dd 0) (pt C dd 1) from addOf_eq' Y _ _,
    show Y.B.G.add (comp1 (Y.B.A.act x) (pt C (n := 2) dd 0)) (comp1 (Y.B.A.act x) (pt C (n := 2) dd 1)) =
      addAt Y (comp1 (Y.B.A.act x) (pt C dd 0)) (comp1 (Y.B.A.act x) (pt C dd 1)) from addOf_eq' Y _ _,
    coordinateChange_comp1_intertwines_action, coordinateChange_comp1_intertwines_action, coordinateChange_comp1_intertwines_action] at h
  have k0 := cc_pt (C := C) (dd := dd) (0 : Fin 2)
  have k1 := cc_pt (C := C) (dd := dd) (1 : Fin 2)
  have hP := constantCoeff_pair_substitution ha hb
  have e0 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (0 : Fin 2) i)) = a := funext fun i => pair_subst_coordinate ha hb 0 i
  have e1 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (1 : Fin 2) i)) = b := funext fun i => pair_subst_coordinate ha hb 1 i
  funext i
  have h2 := congrArg (MvPowerSeries.subst (P2 a b)) (congrFun h i)
  rw [actAt_subst Y hP (cc_addAt Y k0 k1), addAt_subst Y hP (cc_actAt Y x k0) (cc_actAt Y x k1)] at h2
  have e2 : (fun i => MvPowerSeries.subst (P2 a b) (addAt Y (pt C dd (0 : Fin 2)) (pt C dd (1 : Fin 2)) i)) =
      addAt Y a b := by
    funext j
    rw [addAt_subst Y hP k0 k1, e0, e1]
  have e3 : (fun i => MvPowerSeries.subst (P2 a b) (actAt Y x (pt C dd (0 : Fin 2)) i)) = actAt Y x a := by
    funext j
    rw [actAt_subst Y hP k0, e0]
  have e4 : (fun i => MvPowerSeries.subst (P2 a b) (actAt Y x (pt C dd (1 : Fin 2)) i)) = actAt Y x b := by
    funext j
    rw [actAt_subst Y hP k1, e1]
  rw [e2, e3, e4] at h2
  exact h2

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

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

open Formalism.IncomingBounds ValuationFitting
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF IsLocalRing

def PlaceSt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE]
    [Module.Finite ℤ OE] (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsLocalRing R] [Algebra ℤ_[l] R],
    (l : R) ∈ maximalIdeal R → ¬ ((l : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) →
    ∀ (d : ℕ) [NeZero d] (em : ZMod d → OE →+* R),
      (∀ a x, em (a + 1) x - em a x ^ l ∈ maximalIdeal R) →
      (∀ a a', a ≠ a' → ∃ x, em a x - em a' x ∉ maximalIdeal R) →
      (∃ ε : OE, (∃ y, ε * ε - ε = (l : OE) * y) ∧ (∀ a, em a ε - 1 ∈ maximalIdeal R) ∧
        ∀ x : OE, (∀ a, em a x ∈ maximalIdeal R) → ∃ y, ε * x = (l : OE) * y) → PlaceIn l OE R d em

def EigFreeSt : Prop :=
  ∀ (C : Type) [Field C] (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], vm.Integers R →
    ∀ (n : ℕ) (ι : Type) (L : ι → Matrix (Fin n) (Fin n) R) (χ : ι → R),
      ∃ (s : ℕ) (W : Fin s → Fin n → R), (∀ i a, (L a).mulVec (W i) = χ a • W i) ∧
        ∀ v : Fin n → R, (∀ a, (L a).mulVec v = χ a • v) → ∃! c : Fin s → R, ∑ i, c i • W i = v

section Eig

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]
variable {R : Type} [CommRing R] [Algebra R C]

theorem linAct_toC {Y : FBChart C V OE dd} (actR : OE → Fin dd → PS R 1 dd)
    (hact : ∀ a i, Y.B.A.act a i = toC (actR a i)) (x : OE) (v : Fin dd → R) (i : Fin dd) :
    algebraMap R C ((linPart (actR x)).mulVec v i) = linAct (Y.B.A.act x) (fun j => algebraMap R C (v j)) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [linAct, hact, toC, MvPowerSeries.coeff_map, linPart, Matrix.mulVec, dotProduct, Matrix.of_apply,
    map_sum, map_mul]

end Eig

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end
