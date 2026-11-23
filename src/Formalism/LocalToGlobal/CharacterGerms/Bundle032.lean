module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle030
public import Formalism.LocalToGlobal.CharacterGerms.GermLiftSelfSt
import Formalism.LocalToGlobal.CharacterGerms.Bundle015
import Formalism.LocalToGlobal.CharacterGerms.Bundle027
public import Formalism.LocalToGlobal.CharacterGerms.Bundle007
public import Formalism.LocalToGlobal.CharacterGerms.Bundle026
public import Formalism.LocalToGlobal.CharacterGerms.Bundle009
import Formalism.LocalToGlobal.CharacterGerms.Bundle011
public import Formalism.LocalToGlobal.CharacterGerms.Bundle014
public import Formalism.LocalToGlobal.CharacterGerms.RowTiePHStab
public import Formalism.LocalToGlobal.CharacterGerms.Bundle029
import Formalism.LocalToGlobal.CharacterGerms.Bundle008
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Defs

variable {C : Type} [Field C]

def frobTw {σ : Type} (l : ℕ) (c : MvPowerSeries σ C) : MvPowerSeries σ C :=
  fun μ => if ∀ s, l ∣ μ s then (MvPowerSeries.coeff (μ.mapRange (fun n => n / l) (Nat.zero_div l)) c) ^ l else 0

def cobd {dd : ℕ} (F : Fin dd → PS C 2 dd) (b : PS C 1 dd) : PS C 2 dd :=
  ev (n := 2) ![addOf F (pt C dd 0) (pt C dd 1)] b - ev (n := 2) ![pt C dd 0] b - ev (n := 2) ![pt C dd 1] b

end Defs

def FirstStepFirstHalfCondition : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I),
    (Y.raw p).RankHyp → ∀ Hc : ∀ g, (Y.raw p).CartHyp V g, (Y.raw p).AltC →
    ∀ (g : Fin 2) (a : ZMod d), (Y.raw p).big g a →
    ∀ (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C), (RawChart.cart (Hc g)).Good a w x →
    (∀ q, V.MM ((RawChart.cart (Hc g)).c0' x q)) →
    ∀ (γ : Fin dd → PowerSeries C) (lam : JJ I g → PowerSeries C), (Y.raw p).TyWit V g x γ lam →
      ∃ A : PS C 1 dd, IntS V A ∧
        (∀ j : Fin dd, V.MM (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) A)) ∧
        ∀ μ, V.MM (MvPowerSeries.coeff μ
          (cobd Y.B.G.F A - frobTw V.l (Y.chartLinearTerm (fun i => PowerSeries.coeff 1 (γ i)))))

def FirstStepSecondHalfCondition : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C), IsAlgClosed C →
    ∀ (dd : ℕ) (G : FGLaw C dd), (∀ i, IntS V (G.F i)) →
    ∀ (A : PS C 1 dd) (c : PS C 2 dd), IntS V A → IntS V c →
      (∀ j : Fin dd, V.MM (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) A)) →
      (∀ μ, V.MM (MvPowerSeries.coeff μ (cobd G.F A - frobTw V.l c))) →
      ∃ b : PS C 1 dd, IntS V b ∧ ∀ μ, V.MM (MvPowerSeries.coeff μ (c - cobd G.F b))

theorem intS_c2lin {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
    (Y : FBChart C V O dd) (u : Fin dd → C) (hu : ∀ i, V.Ge 0 (u i)) : IntS V (Y.chartLinearTerm u) := by
  intro μ
  show V.Ge 0 (∑ i, u i * MvPowerSeries.coeff
    (μ.mapDomain (fun p : Fin 2 × Fin dd => (p.1.succ, p.2)) + Finsupp.single ((0 : Fin 3), i) 1) Y.B.ph2)
  exact VF.Ge.sum fun i _ => by simpa using (hu i).mul (Y.intPh2 _)

end Formalism.L2.FormalSeriesBounds
end
end

section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

def RawChart.TCoordSt {C : Type} [Field C] {V : VF C} {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]
    {X : RawChart C d I κ} (Hc : ∀ g, X.CartHyp V g) : Prop :=
  ∀ (S : ∀ g, Sys (RawChart.cart (Hc g))) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) →
    ∀ (g : Fin 2) (c : I g), ∃ T : MvPowerSeries κ C, IntS V T ∧ MvPowerSeries.constantCoeff T = 0 ∧
      MvPowerSeries.subst (fun x => X.expPt g x) T = upG g (t g c)

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type}
  [∀ o g, Fintype (I o g)]

theorem cc_toAllS (o : Orb) (F : MvPowerSeries (WV (I o)) C) :
    MvPowerSeries.constantCoeff (toAllS o F) = MvPowerSeries.constantCoeff F := by
  unfold toAllS
  exact VP.cc_subst_eq (fun _ => MvPowerSeries.constantCoeff_X _) F

theorem toAllS_subst {κ : Type} [Finite κ] (o : Orb) {E : κ → MvPowerSeries (WV (I o)) C}
    (hE : ∀ x, MvPowerSeries.constantCoeff (E x) = 0) (T : MvPowerSeries κ C) :
    toAllS o (MvPowerSeries.subst E T) = MvPowerSeries.subst (fun x => toAllS o (E x)) T := by
  unfold toAllS
  exact VP.subst_subst hE (fun _ => MvPowerSeries.constantCoeff_X _) T

theorem germLift_gen {σ : Type} [Finite σ] {A : σ → MvPowerSeries (WVO I) C}
    (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0) (o : Orb) (t : ∀ g, I o g → MvPowerSeries (I o g) C)
    (ht0 : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0)
    (hT : ∀ w : WV (I o), ∃ T : MvPowerSeries σ C, IntS V T ∧ MvPowerSeries.constantCoeff T = 0 ∧
      MvPowerSeries.subst A T = toAllS o (upG w.1 (t w.1 w.2))) :
    ∀ F ∈ IntGerm V t, ∃ G : MvPowerSeries σ C, IntS V G ∧ MvPowerSeries.subst A G = toAllS o F := by
  intro F hF
  obtain ⟨γ, hγ, rfl⟩ := hF
  choose T hTi hT0 hTA using hT
  have hE : ∀ w : WV (I o), MvPowerSeries.constantCoeff (upG w.1 (t w.1 w.2)) = 0 := fun w => by
    unfold upG
    exact VP.cc_subst (fun _ => MvPowerSeries.constantCoeff_X _) (ht0 _ _)
  refine ⟨MvPowerSeries.subst T γ, IntS.subst hT0 hTi hγ, ?_⟩
  rw [VP.subst_subst hT0 hA, toAllS_subst o hE]
  congr 1
  funext w
  exact hTA w

theorem tLift_gen {σ κ : Type} [Finite σ] [Finite κ] {A : σ → MvPowerSeries (WVO I) C}
    (hA : ∀ s, MvPowerSeries.constantCoeff (A s) = 0) (o : Orb) {E : κ → MvPowerSeries (WV (I o)) C}
    {π : κ → MvPowerSeries σ C} (hπi : ∀ x, IntS V (π x)) (hπ0 : ∀ x, MvPowerSeries.constantCoeff (π x) = 0)
    (hπ : ∀ x, MvPowerSeries.subst A (π x) = toAllS o (E x))
    {T : MvPowerSeries κ C} (hTi : IntS V T) (hT0 : MvPowerSeries.constantCoeff T = 0) :
    ∃ T' : MvPowerSeries σ C, IntS V T' ∧ MvPowerSeries.constantCoeff T' = 0 ∧
      MvPowerSeries.subst A T' = toAllS o (MvPowerSeries.subst E T) := by
  have hπA : ∀ x, MvPowerSeries.constantCoeff (MvPowerSeries.subst A (π x)) = 0 := fun x => VP.cc_subst hA (hπ0 x)
  have hE : ∀ x, MvPowerSeries.constantCoeff (E x) = 0 := fun x => by
    rw [← cc_toAllS o (E x), ← hπ x]
    exact hπA x
  refine ⟨MvPowerSeries.subst π T, IntS.subst hπ0 hπi hTi, VP.cc_subst hπ0 hT0, ?_⟩
  rw [VP.subst_subst hπ0 hA, toAllS_subst o hE]
  congr 1
  funext x
  exact hπ x

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb]

section Pairs

variable {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

end Pairs

section Self

variable {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

def ProjSelfSt (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) : Prop :=
  SelfSep Y p → ∀ (o : Orb) (g : Fin 2), ∃ π : Fin 2 × Fin dd → PS C 2 dd, (∀ x, IntS V (π x)) ∧
    (∀ x, MvPowerSeries.constantCoeff (π x) = 0) ∧
    ∀ x, pull2 Y p (π x) = toAllS (I := IS I0) o ((Y.rawSelf (p o)).expPt g x)

theorem germLiftSelf_of (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
    (hP : ProjSelfSt Y p) (hT : ∀ o, RawChart.TCoordSt (H o).cartH) : GermLiftSelfSt Y p H := by
  intro hsep o S t hS F hF
  unfold pull2
  have hA : ∀ q : Fin 2 × Fin dd, MvPowerSeries.constantCoeff (VP.linPt Y (uS Y p) q) = 0 := VP.cc_linPt Y (uS Y p)
  refine VP.germLift_gen (I := IS I0) hA o t (fun g c => (hS g).1 c) (fun w => ?_) F hF
  obtain ⟨π, hπi, hπ0, hπ⟩ := hP hsep o w.1
  obtain ⟨T, hTi, hT0, hTe⟩ := hT o S t hS w.1 w.2
  obtain ⟨T', h1, h2, h3⟩ := VP.tLift_gen (I := IS I0) hA o hπi hπ0 hπ hTi hT0
  exact ⟨T', h1, h2, by rw [h3, hTe]⟩

end Self

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
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

namespace VP

theorem cc_mvExp' {σ : Type} (h : MvPowerSeries σ C) : MvPowerSeries.constantCoeff (mvExp h) = 1 := by
  show (∑ k ∈ Finset.range ((0 : σ →₀ ℕ).degree + 1), MvPowerSeries.coeff 0 (h ^ k) / (k.factorial : C)) = 1
  simp

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))

theorem pullback_two_var_mul (F G : PS C 2 dd) : pull2 Y p (F * G) = pull2 Y p F * pull2 Y p G := by
  unfold pull2
  exact linPull_mul _ _ F G

theorem pullback_two_var_prod {ι : Type} (s : Finset ι) (F : ι → PS C 2 dd) :
    pull2 Y p (∏ i ∈ s, F i) = ∏ i ∈ s, pull2 Y p (F i) := by
  unfold pull2
  exact linPull_prod _ _ s F

theorem pullback_two_var_one : pull2 Y p (1 : PS C 2 dd) = 1 := by
  have h := pullback_two_var_prod Y p (∅ : Finset Unit) (fun _ => (1 : PS C 2 dd))
  simpa using h

theorem pullS_exp {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n) (E : PS C 1 dd) (hE : MvPowerSeries.constantCoeff E = 1) :
    pullS Y p pl (∏ b : Fin n, ev (n := n) ![pt C dd b] E) =
      ∏ ρ : Fin N, rowOf ρ (pull2 Y p (∏ col : Fin 2, ev (n := 2) ![pt C dd col] E)) := by
  have hprod : pullS Y p pl (∏ b : Fin n, ev (n := n) ![pt C dd b] E) =
      ∏ b : Fin n, pullS Y p pl (ev (n := n) ![pt C dd b] E) := by
    unfold pullS
    exact linPull_prod _ _ _ _
  rw [hprod]
  have hoff : ∀ b ∈ (Finset.univ : Finset (Fin n)), b ∉ Finset.univ.map pl →
      pullS Y p pl (ev (n := n) ![pt C dd b] E) = 1 := by
    intro b _ hb
    have hb' : b ∉ Set.range pl := by simpa using hb
    rw [pullS_off (b := b) (hb := hb'), hE, map_one]
  rw [← Finset.prod_subset (Finset.subset_univ (Finset.univ.map pl)) hoff, Finset.prod_map,
    Fintype.prod_prod_type]
  simp_rw [pullS_col]
  refine Finset.prod_congr rfl fun ρ _ => ?_
  rw [pullback_two_var_prod, rowOf_prod]

end VP

theorem valuation_eq_self_of_unit_germ (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
    (Ls : LetSys C dd) (n : ℕ) (h2 : UnitSelfSt Y p) (h3 : GermLiftSelfSt Y p H) : ValEqSelfSt Y p H Ls n := by
  intro hs N pl P hP Po hQ kind hk S t ht gr hg
  obtain ⟨U, hUi, hU0, hU⟩ := h2 hs
  obtain ⟨U', hU'i, hUU⟩ := VP.intInv hUi hU0
  choose G hGi hG using fun (o : Orb) (ρ : Fin N) => h3 hs o (S o) (t o) (ht o) (gr o ρ) (hg o ρ)
  obtain ⟨co, hco, hQe⟩ := hQ
  refine ⟨∏ ρ, ev (n := n) ![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] (U' * ∏ o, G o ρ), ?_, ?_⟩
  · refine VP.IntS_prod _ fun ρ _ => ?_
    unfold ev
    refine IntS.subst (VP.cc_ptPl pl ρ) (fun q => ?_) (hU'i.mul (VP.IntS_prod _ fun o _ => hGi o ρ))
    obtain ⟨g, i⟩ := q
    fin_cases g <;> exact VP.IntS_X _
  · have hk0 : MvPowerSeries.constantCoeff ((Y.k : C) • Y.B.hL C Y.h Y.w0) = 0 := VP.cc_smul _ (VP.cc_hL Y)
    have hE1 : MvPowerSeries.constantCoeff (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) = 1 := by
      rw [VP.expS_eq _ hk0, VP.cc_mvExp']
    have hrow : ∀ ρ : Fin N,
        rowOf ρ (pull2 Y p (U' * ∏ o, G o ρ)) *
          rowOf ρ (pull2 Y p (∏ col : Fin 2, ev (n := 2) ![pt C dd col]
            (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)))) =
        ∏ o, MvPowerSeries.rename (VP.eAll (I := IS I0) N o)
          (rowCopy ρ (gr o ρ) * mvExp (rowCopy ρ (Y.rawSelf (p o)).hRow)) := by
      intro ρ
      rw [← VP.rowOf_mul, hU, VP.pullback_two_var_mul, VP.pullback_two_var_prod]
      have e2 : (pull2 Y p U' * ∏ o, pull2 Y p (G o ρ)) *
          (pull2 Y p U * ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow)) =
          ∏ o, toAllS (I := IS I0) o (gr o ρ * mvExp (Y.rawSelf (p o)).hRow) := by
        have e3 : pull2 Y p U' * pull2 Y p U = 1 := by rw [← VP.pullback_two_var_mul, hUU, VP.pullback_two_var_one]
        calc (pull2 Y p U' * ∏ o, pull2 Y p (G o ρ)) *
              (pull2 Y p U * ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow))
            = (pull2 Y p U' * pull2 Y p U) *
                ((∏ o, pull2 Y p (G o ρ)) * ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow)) := by ring
          _ = ∏ o, toAllS (I := IS I0) o (gr o ρ * mvExp (Y.rawSelf (p o)).hRow) := by
              rw [e3, one_mul, ← Finset.prod_mul_distrib]
              exact Finset.prod_congr rfl fun o _ => by rw [hG o ρ, VP.toAllS_mul]
      rw [e2, VP.rowOf_prod]
      exact Finset.prod_congr rfl fun o _ => by rw [VP.rowOf_toAllS, VP.rowCopy_mul_exp]
    have hser : pullS Y p pl ((∏ ρ, ev (n := n) ![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] (U' * ∏ o, G o ρ)) *
        FB.expS C ((Y.k : C) • ∑ b : Fin n, ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0))) =
        ∏ o, MvPowerSeries.rename (VP.eAll (I := IS I0) N o)
          (∏ ρ, (rowCopy ρ (gr o ρ) * mvExp (rowCopy ρ (Y.rawSelf (p o)).hRow))) := by
      have hpl : ∀ ρ : Fin N, VP.linPull Y (MS Y p pl)
          (ev (n := n) ![pt C dd (pl (ρ, 0)), pt C dd (pl (ρ, 1))] (U' * ∏ o, G o ρ)) =
          rowOf ρ (pull2 Y p (U' * ∏ o, G o ρ)) := fun ρ => VP.pullS_plane Y p pl ρ _
      rw [VP.expS_copies, show pullS Y p pl (_ * _) = _ from VP.linPull_mul Y _ _ _,
        show VP.linPull Y (MS Y p pl) (∏ b : Fin n, _) = _ from VP.pullS_exp Y p pl _ hE1,
        VP.linPull_prod, Finset.prod_congr rfl fun ρ _ => hpl ρ,
        ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun ρ _ => hrow ρ, Finset.prod_comm]
      exact Finset.prod_congr rfl fun o _ => (map_prod _ _ _).symm
    unfold FBChart.nab nabValN
    rw [VP.logCoordG Y (MS Y p pl) (Ls.cp n) (Ls.uv n) P co
      (fun ℓ hℓ b i => VP.hco_of_img Y p pl (Ls.cp n) (Ls.uv n) ℓ (co ℓ) (hco ℓ hℓ) b i), ← hQe]
    rw [show VP.linPull Y (MS Y p pl) _ = _ from hser, VP.jet_orb]
    exact Finset.prod_congr rfl fun o _ =>
      leaf_holds C V d (fun _ => I0 o) (Fin 2 × Fin dd) (Y.rawSelf (p o)) (H o) N (Po o) (kind o) (hk o) (gr o)

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

section Rename₂

theorem coeff_rename_outside {σ τ : Type} [Finite σ] (φ : σ → τ) (F : MvPowerSeries σ C) (ν : τ →₀ ℕ) {s : τ}
    (hs : ν s ≠ 0) (hr : ∀ x, φ x ≠ s) :
    coeff ν (MvPowerSeries.subst (fun x => (X (φ x) : MvPowerSeries τ C)) F) = 0 := by
  refine coeff_subst_rename_out φ F ν fun e' he => hs ?_
  rw [← he]
  exact Finsupp.mapDomain_notin_range _ _ (by rintro ⟨x, hx⟩; exact hr x hx)

variable {dd : ℕ}

theorem coeff_hCol (h : PS C 2 dd) (col c1 c2 : Fin 2) (i j : Fin dd) :
    coeff (E2 ((0 : Fin 2), (c1, i)) ((1 : Fin 2), (c2, j))) (hCol col h) =
      if c1 = col ∧ c2 = col then coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) h else 0 := by
  unfold hCol
  split_ifs with hc
  · obtain ⟨h1, h2⟩ := hc
    rw [h1, h2]
    have hφ : Function.Injective (fun p : Fin 2 × Fin dd => (p.1, (col, p.2))) := by
      intro a b hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext hab.1 hab.2.2
    have he : E2 ((0 : Fin 2), (col, i)) ((1 : Fin 2), (col, j)) =
        (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)).mapDomain (fun p : Fin 2 × Fin dd => (p.1, (col, p.2))) := by
      simp [E2, Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    rw [he, coeff_subst_rename_inj _ hφ]
  · by_cases h1 : c1 = col
    · have h2 : c2 ≠ col := fun h2 => hc ⟨h1, h2⟩
      refine coeff_rename_outside _ h (E2 _ _) (s := ((1 : Fin 2), (c2, j))) ?_ ?_
      · simp [E2, Finsupp.single_apply]
      · intro x hx
        simp only [Prod.mk.injEq] at hx
        exact h2 hx.2.1.symm
    · refine coeff_rename_outside _ h (E2 _ _) (s := ((0 : Fin 2), (c1, i))) ?_ ?_
      · simp [E2, Finsupp.single_apply]
      · intro x hx
        simp only [Prod.mk.injEq] at hx
        exact h1 hx.2.1.symm

end Rename₂

section Self

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I0 : Type} [Fintype I0]

theorem coeff_E2_sum_hCol_eq_ite (h : PS C 2 dd) (c1 c2 : Fin 2) (i j : Fin dd) :
    coeff (E2 ((0 : Fin 2), (c1, i)) ((1 : Fin 2), (c2, j))) (∑ col, hCol col h) =
      if c1 = c2 then coeff (E2 ((0 : Fin 2), i) ((1 : Fin 2), j)) h else 0 := by

  rw [map_sum]
  simp only [coeff_hCol]
  rw [Fin.sum_univ_two]
  by_cases h12 : c1 = c2
  · subst h12
    fin_cases c1 <;> simp
  · fin_cases c1 <;> fin_cases c2 <;> simp_all

theorem FBChart.self_raw_first_pairing_eq (Y : FBChart C V O dd) (p : SelfData Y d I0) (w v : Fin 2 × Fin dd → C) :
    (Y.rawSelf p).sg1 w v = -∑ col, bil Y.h (fun i => w (col, i)) (fun j => v (col, j)) := by
  have hsg : ∀ x : Fin 2 × Fin dd, MvPowerSeries.coeff (Finsupp.single x 1) ((Y.rawSelf p).sg v) =
      -∑ i : Fin 2 × Fin dd, v i *
        (if x.1 = i.1 then MvPowerSeries.coeff (E2 ((0 : Fin 2), x.2) ((1 : Fin 2), i.2)) Y.h else 0) := by
    intro x
    show (-∑ i, v i * MvPowerSeries.coeff ((Finsupp.single x 1).mapDomain (fun y => ((0 : Fin 2), y)) +
      Finsupp.single ((1 : Fin 2), i) 1) (∑ col, hCol col Y.h)) = _
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.mapDomain_single]
    rw [show Finsupp.single ((0 : Fin 2), x) 1 + Finsupp.single ((1 : Fin 2), i) 1 =
      E2 ((0 : Fin 2), (x.1, x.2)) ((1 : Fin 2), (i.1, i.2)) from rfl, coeff_E2_sum_hCol_eq_ite]
  simp only [RawChart.sg1, hsg, bil, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Fin.isValue, if_true, zero_ne_one, one_ne_zero, if_false, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib, neg_add]
  congr 1 <;> (congr 1; exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring)

end Self

theorem hStabSelf_holds : HStabSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g c q hty
  have hne : p.ty0 c ≠ p.ty0 q + p.hd := by
    rcases fin_two_eq_zero_or_eq_one g with rfl | rfl
    · exact hty
    · intro e
      apply hty
      show p.ty0 c + p.hd = p.ty0 q
      rw [e, add_assoc, p.hd_two, add_zero]
  obtain ⟨a, ha⟩ := p.em_sep _ _ hne
  have hb := Y.bil_ad a (p.e c) (p.e q)
  rw [p.e_eig c a, p.e_eig q (star a), p.em_conj, bil_smul_left, bil_smul_right, ← sub_mul] at hb
  have hint : V.Ge 0 (bil (Y.B.ad a) (p.e c) (p.e q)) := bil_int (Y.intAd a) (p.e_int c) (p.e_int q)
  rw [hb] at hint
  have hβ : V.Ge 0 (bil Y.h (p.e c) (p.e q)) := by
    unfold VF.Ge at hint ⊢
    rwa [V.v.map_mul, ha, zero_add] at hint
  have hgm : ∀ a r s, V.Ge 0 (p.gm a r s) := by
    obtain ⟨M, hM⟩ := p.gm_lim 0
    intro a r s
    have h1 : V.Ge 0 (p.gm a r s - p.em a (M r s)) := by simpa using hM a r s
    have h2 := h1.add (p.em_int a (M r s))
    simpa using h2
  show V.Ge 0 ((Y.rawSelf p).sg1 (fun x => p.gm (p.ty0 c) x.1 g * p.e c x.2)
    (fun x => p.gm (p.ty0 q) x.1 (1 - g) * p.e q x.2))
  rw [Y.self_raw_first_pairing_eq]
  apply VF.Ge.neg
  apply VF.Ge.sum
  intro col _
  show V.Ge 0 (bil Y.h (p.gm (p.ty0 c) col g • p.e c) (p.gm (p.ty0 q) col (1 - g) • p.e q))
  rw [bil_smul_left, bil_smul_right]
  exact (hgm _ _ _).mul_int ((hgm _ _ _).mul_int hβ)

end Formalism.L2.FormalSeriesBounds
end
end
