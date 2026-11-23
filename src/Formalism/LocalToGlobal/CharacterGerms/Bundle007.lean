module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
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
import Mathlib.Data.Finsupp.WellFounded
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
import Mathlib.Topology.Sheaves.Presheaf
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle005

@[expose] public section

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

section Inv

variable {C : Type} [Field C] {V : VF C} {σ : Type}

theorem inv_int {c : C} (hc : V.v c = 0) : V.Ge 0 c⁻¹ := by
  simp [VF.Ge, AddValuation.map_inv, hc]

theorem intInv {U : MvPowerSeries σ C} (hU : IntS V U) (h0 : V.v (MvPowerSeries.constantCoeff U) = 0) :
    ∃ U' : MvPowerSeries σ C, IntS V U' ∧ U' * U = 1 := by
  have hc0 : MvPowerSeries.constantCoeff U ≠ 0 := by
    intro h
    simp [h] at h0
  refine ⟨U⁻¹, ?_, MvPowerSeries.inv_mul_cancel _ hc0⟩
  have hge0 : V.Ge 0 (0 : C) := by simp [VF.Ge]
  have hmul : ∀ a b : C, V.Ge 0 a → V.Ge 0 b → V.Ge 0 (a * b) := by
    intro a b ha hb
    unfold VF.Ge at *
    rw [AddValuation.map_mul]
    simpa using add_le_add ha hb
  have hadd : ∀ a b : C, V.Ge 0 a → V.Ge 0 b → V.Ge 0 (a + b) :=
    fun a b ha hb => le_trans (le_min ha hb) (V.v.map_add a b)
  have hneg : ∀ a : C, V.Ge 0 a → V.Ge 0 (-a) := by
    intro a ha
    unfold VF.Ge at *
    rwa [AddValuation.map_neg]
  intro μ
  induction μ using WellFoundedLT.induction with
  | _ μ ih =>
    rw [MvPowerSeries.coeff_inv]
    split_ifs with hμ
    · exact inv_int h0
    · refine hmul _ _ (hneg _ (inv_int h0)) ?_
      refine Finset.sum_induction _ (V.Ge 0) hadd hge0 (fun x _ => ?_)
      split_ifs with hlt
      · exact hmul _ _ (hU x.1) (ih x.2 hlt)
      · exact hge0

theorem IntS_prod {ι : Type} (s : Finset ι) {F : ι → MvPowerSeries σ C} (h : ∀ i ∈ s, IntS V (F i)) :
    IntS V (∏ i ∈ s, F i) := by
  classical
  have hge : ∀ c : C, (c = 0 ∨ c = 1) → V.Ge 0 c := by
    rintro c (rfl | rfl)
    · simp [VF.Ge]
    · simp [VF.Ge]
  have hone : IntS V (1 : MvPowerSeries σ C) := by
    intro μ
    rw [MvPowerSeries.coeff_one]
    split_ifs
    · exact hge 1 (Or.inr rfl)
    · exact hge 0 (Or.inl rfl)
  have hmul : ∀ F G : MvPowerSeries σ C, IntS V F → IntS V G → IntS V (F * G) := by
    intro F G hF hG μ
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_induction _ (V.Ge 0) (fun a b ha hb => ?_) (hge 0 (Or.inl rfl)) (fun q _ => ?_)
    · exact le_trans (le_min ha hb) (V.v.map_add a b)
    · have h1 := add_le_add (hF q.1) (hG q.2)
      unfold VF.Ge
      rw [AddValuation.map_mul]
      simpa using h1
  induction s using Finset.induction_on with
  | empty => simpa using hone
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact hmul _ _ (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem IntS_X (s : σ) : IntS V (MvPowerSeries.X s : MvPowerSeries σ C) := by
  intro μ
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · simp [VF.Ge]
  · simp [VF.Ge]

end Inv

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

private theorem cc_ev_lemma {m n : ℕ} (a : Fin m → Pt C n dd)
    (ha : ∀ j i, MvPowerSeries.constantCoeff (a j i) = 0) (f : PS C m dd) :
    MvPowerSeries.constantCoeff (ev a f) = MvPowerSeries.constantCoeff f := by
  have hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin dd => a p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)
  unfold ev
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro d hd
    obtain ⟨s, hs'⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    have h0 : MvPowerSeries.constantCoeff (d.prod fun s e => (a s.1 s.2) ^ e) = 0 := by
      rw [Finsupp.prod, map_prod]
      exact Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hs') (by rw [map_pow, ha, zero_pow hs'])
    rw [h0, smul_zero]

theorem cc_h (Y : FBChart C V O dd) : MvPowerSeries.constantCoeff Y.h = 0 := by
  have hax := Y.gauge.ax0
  have e : MvPowerSeries.constantCoeff (ev (n := 1) ![0, pt C dd 0] Y.h) = MvPowerSeries.constantCoeff Y.h :=
    cc_ev_lemma _ (fun j i => by fin_cases j <;> simp [pt]) _
  rw [← e, hax, map_zero]

theorem cc_hL (Y : FBChart C V O dd) : MvPowerSeries.constantCoeff (Y.B.hL C Y.h Y.w0) = 0 := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.FB.hL
  rw [cc_ev_lemma _ ?_ _]
  · exact cc_h Y
  · intro j i
    fin_cases j
    · simp [pt]
    · show MvPowerSeries.constantCoeff (comp1 (Y.B.actK C Y.w0) (pt C dd 0) i) = 0
      simp only [comp1]
      rw [cc_ev_lemma _ (fun j i => by rw [Fin.fin_one_eq_zero j]; simp [pt]) _]
      simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.FB.actK, MvPowerSeries.constantCoeff_map, Y.B.A.const]

end VP

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

section VanS

variable {τ : Type}

def Van (T : Set τ) (f : MvPowerSeries τ C) : Prop :=
  ∀ ν : τ →₀ ℕ, (∀ w ∈ ν.support, w ∉ T) → coeff ν f = 0

theorem Van.mul_right {T : Set τ} {f : MvPowerSeries τ C} (hf : Van T f) (g : MvPowerSeries τ C) :
    Van T (f * g) := by
  intro ν hν
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨a, b⟩ hab
  have hab' : a + b = ν := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
  have h0 : coeff a f = 0 := hf a fun w hw => hν w (by
    rw [← hab', Finsupp.mem_support_iff, Finsupp.add_apply]
    have := Finsupp.mem_support_iff.1 hw
    omega)
  simp [h0]

theorem Van.const {T : Set τ} {f : MvPowerSeries τ C} (hf : Van T f) : constantCoeff f = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact hf 0 (by simp)

theorem Van.smul {T : Set τ} {f : MvPowerSeries τ C} (hf : Van T f) (c : C) : Van T (c • f) := by
  intro ν hν
  rw [coeff_smul, hf ν hν, mul_zero]

theorem Van.subst {σ : Type} [Finite σ] {T : Set τ} (S : Set σ) {a : σ → MvPowerSeries τ C}
    (ha0 : ∀ s, constantCoeff (a s) = 0) (haS : ∀ s ∈ S, Van T (a s)) {f : MvPowerSeries σ C}
    (hf : ∀ e : σ →₀ ℕ, (∀ s ∈ e.support, s ∉ S) → coeff e f = 0) : Van T (MvPowerSeries.subst a f) := by
  intro ν hν
  rw [coeff_subst (hasSubst_of_constantCoeff_zero ha0)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e
  by_cases h : ∀ s ∈ e.support, s ∉ S
  · rw [hf e h, zero_smul]
  · push Not at h
    obtain ⟨s, hs, hsS⟩ := h
    have hv : Van T (e.prod fun s m => a s ^ m) := by
      unfold Finsupp.prod
      rw [← Finset.mul_prod_erase _ _ hs]
      apply Van.mul_right
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Finsupp.mem_support_iff.1 hs)
      show Van T (a s ^ e s)
      rw [hm, pow_succ']
      exact (haS s hsS).mul_right _
    rw [hv ν hν, smul_zero]

end VanS

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem van_lin (g : Fin 2) (b : I g → C) :
    Van {w : WV I | w.1 = g} (∑ c : I g, b c • (MvPowerSeries.X (⟨g, c⟩ : WV I) : MvPowerSeries (WV I) C)) := by
  intro ν hν

  rw [map_sum]
  apply Finset.sum_eq_zero
  intro c _
  rw [coeff_smul, coeff_X, if_neg, mul_zero]
  intro h
  exact hν ⟨g, c⟩ (by rw [h]; simp) rfl

theorem van_expPt (hex : ∀ x, constantCoeff (X.ex x) = 0) (g : Fin 2) (x : κ) :
    Van {w : WV I | w.1 = g} (X.expPt g x) := by
  unfold expPt
  refine Van.subst Set.univ (fun i => (van_lin g _).const) (fun i _ => van_lin g _) ?_
  intro e he
  have he0 : e = 0 := by
    rw [← Finsupp.support_eq_empty]
    exact Finset.eq_empty_of_forall_notMem fun s hs => he s hs (Set.mem_univ s)
  rw [he0, coeff_zero_eq_constantCoeff_apply]
  exact hex x

theorem van_hRow (hex : ∀ x, constantCoeff (X.ex x) = 0) (g : Fin 2)
    (hh : ∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e X.h = 0) :
    Van {w : WV I | w.1 = g} X.hRow := by
  unfold hRow
  apply Van.smul
  refine Van.subst {s : Fin 2 × κ | s.1 = g} (fun s => (X.van_expPt hex s.1 s.2).const) ?_ hh
  rintro ⟨g', x⟩ hs
  have hg : g' = g := hs
  subst hg
  exact X.van_expPt hex g' x

theorem axes_of (hex : ∀ x, constantCoeff (X.ex x) = 0)
    (hh : ∀ (g : Fin 2) (e : Fin 2 × κ →₀ ℕ), (∀ s ∈ e.support, s.1 ≠ g) → coeff e X.h = 0) : X.AxesSt := by
  intro μ h
  rcases h with h | h
  · exact X.van_hRow hex 1 (hh 1) μ fun w hw hw1 => by
      have h0 := h w hw
      have h1 : w.1 = 1 := hw1
      rw [h0] at h1
      exact absurd h1 (by decide)
  · exact X.van_hRow hex 0 (hh 0) μ fun w hw hw0 => by
      have h1 := h w hw
      have h0 : w.1 = 0 := hw0
      rw [h1] at h0
      exact absurd h0 (by decide)

end RawChart

section FBpart

variable {dd : ℕ}

theorem fin_two_eq_one_sub_of_ne' : ∀ g g' : Fin 2, g' ≠ g → g' = 1 - g := by decide

theorem coeff_of_ev_zero (h : PS C 2 dd) (g : Fin 2) (a : Fin 2 → Pt C 1 dd) (hag : a g = 0)
    (hao : ∀ g', g' ≠ g → a g' = pt C dd 0) (hz : ev a h = 0) :
    ∀ e : Fin 2 × Fin dd →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e h = 0 := by
  intro e he
  set b : Fin 1 × Fin dd → PS C 2 dd := fun q => X (1 - g, q.2) with hb
  have hbS : HasSubst b := hasSubst_of_constantCoeff_zero fun q => constantCoeff_X _
  have haS : HasSubst (fun p : Fin 2 × Fin dd => a p.1 p.2) := by
    apply hasSubst_of_constantCoeff_zero
    intro s
    by_cases hs : s.1 = g
    · rw [hs, hag]; simp
    · rw [hao _ hs]; exact constantCoeff_X _
  have key : MvPowerSeries.subst b (ev a h) =
      rescale (fun s : Fin 2 × Fin dd => if s.1 = g then (0 : C) else 1) h := by
    unfold ev
    rw [subst_comp_subst_apply haS hbS, rescale_eq_subst]
    congr 1
    funext s
    by_cases hs : s.1 = g
    · have h1 : a s.1 s.2 = 0 := by rw [hs, hag]; rfl
      rw [h1, ← coe_substAlgHom hbS, map_zero]
      simp [hs]
    · have h1 : a s.1 s.2 = X ((0 : Fin 1), s.2) := by rw [hao _ hs]; rfl
      rw [h1, subst_X hbS]
      have h2 : s = (1 - g, s.2) := Prod.ext (fin_two_eq_one_sub_of_ne' g s.1 hs) rfl
      simp only [Pi.smul_apply', if_neg hs, one_smul, hb]
      rw [← h2]
  have h3 := congrArg (coeff e) key
  rw [hz, ← coe_substAlgHom hbS, map_zero, map_zero, coeff_rescale] at h3
  have h4 : (e.prod fun s m => (if s.1 = g then (0 : C) else 1) ^ m) = 1 := by
    unfold Finsupp.prod
    apply Finset.prod_eq_one
    intro s hs
    show (if s.1 = g then (0 : C) else 1) ^ e s = 1
    rw [if_neg (he s hs), one_pow]
  rw [h4, one_mul] at h3
  exact h3.symm

theorem constantCoeff_uncurry (f : PS C 1 dd) : constantCoeff (un1 f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply]
  show coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) f = coeff 0 f
  rw [Finsupp.mapDomain_zero]

theorem axesFB : AxesFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p
  apply RawChart.axes_of
  · intro x
    show constantCoeff (un1 (Y.ex x)) = 0
    rw [constantCoeff_uncurry]
    exact Y.ex_const x
  · intro g
    show ∀ e : Fin 2 × Fin dd →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ g) → coeff e Y.h = 0
    fin_cases g
    · refine coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl ?_ Y.gauge.ax0
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' 0 g' hg']
      rfl
    · refine coeff_of_ev_zero Y.h 1 ![pt C dd 0, 0] rfl ?_ Y.gauge.ax1
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' 1 g' hg']
      rfl

end FBpart

end Formalism.L2.FormalSeriesBounds
end
end

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

def FBChart.IsChar (Y : FBChart C V O dd) (χ : PS C 1 dd) : Prop :=
  IntS V χ ∧ MvPowerSeries.constantCoeff χ = 1 ∧
    ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] χ = ev (n := 2) ![pt C dd 0] χ * ev (n := 2) ![pt C dd 1] χ

def dlogC (χ : PS C 1 dd) (i : Fin dd) : C := MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) 1) χ

section Chart

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Chart

end Formalism.L2.FormalSeriesBounds
end
end
