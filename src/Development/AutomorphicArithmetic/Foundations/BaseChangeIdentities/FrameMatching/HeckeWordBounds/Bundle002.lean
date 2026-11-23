module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.HeckeLevelWordBase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.ChainSc

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical



open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {hR : Rd.ReadLimit}
  {π : Submodule ℂ (UA E n → ℂ)} {S T : Finset (Pl E)} {F₀ : Frame0 hR π S} (F : RunFrame F₀ T)

private theorem lw_cons (w : List (F.Γ × Bool)) (ws : List (List (F.Γ × Bool))) :
    lw F (w :: ws) = (List.replicate F.m (Sum.inl ()) ++ w.map (lt F)) ++ lw F ws := by
  simp [UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw]

private theorem count_lt (w : List (F.Γ × Bool)) : (w.map (lt F)).countP Sum.isLeft = 0 := by
  rw [List.countP_eq_zero]
  intro a ha
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 ha
  rcases p with ⟨(_ | _ | x), b⟩ <;> simp [lt]

private theorem count_lw (ws : List (List (F.Γ × Bool))) :
    (lw F ws).countP Sum.isLeft = F.m * ws.length := by
  induction ws with
  | nil => simp [UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw]
  | cons w ws ih =>
    rw [lw_cons, List.countP_append, List.countP_append, ih, count_lt, List.countP_replicate]
    simp <;> ring

private theorem atPlace_append (w : Pl E) (l₁ l₂ : List (LL F.d)) :
    atPlace F.d w (l₁ ++ l₂) = atPlace F.d w l₁ ++ atPlace F.d w l₂ := by
  simp [atPlace, List.filterMap_append]

private theorem atPlace_rep (w : Pl E) (k : ℕ) :
    atPlace F.d w (List.replicate k (Sum.inl ())) = [] := by
  induction k with
  | zero => simp [atPlace]
  | succ k ih => simpa [atPlace, List.replicate_succ] using ih

private theorem atPlace_lw (w : Pl E) (ws : List (List (F.Γ × Bool))) :
    atPlace F.d w (lw F ws) = atPlace F.d w (ws.flatten.map (lt F)) := by
  induction ws with
  | nil => simp [UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw, atPlace]
  | cons v ws ih =>
    rw [lw_cons, atPlace_append, atPlace_append, ih, atPlace_rep, List.flatten_cons, List.map_append,
      atPlace_append, List.nil_append]

private theorem sph_word (w : Pl E) (l : List (F.Γ × Bool)) :
    U.UGen.sph (l.map (ul F)) w = MLM.wordUS F.d w (atPlace F.d w (l.map (lt F))) := by
  induction l with
  | nil => simp [U.UGen.sph, MLM.wordUS, atPlace]
  | cons p l ih =>
    have hs : ∀ (x : U.UGen E n) (l' : List (U.UGen E n)), U.UGen.sph (x :: l') w =
        Sum.elim (fun _ => U.UGen.sph l' w) (fun y : Σ w : Pl E, UL n w → ℂ =>
          if h : y.1 = w then lconv (h ▸ y.2) (U.UGen.sph l' w) else U.UGen.sph l' w) x := fun _ _ => rfl
    rcases p with ⟨(u | y | x), b⟩
    · have h1 : atPlace F.d w (lt F (Sum.inl u, b) :: l.map (lt F)) = atPlace F.d w (l.map (lt F)) := by
        simp [atPlace, lt]
      rw [List.map_cons, List.map_cons, h1, ← ih, hs]
      cases b <;> simp [ul, RunFrame.ug, U.UGen.adj]
    · have h1 : atPlace F.d w (lt F (Sum.inr (Sum.inl y), b) :: l.map (lt F)) = atPlace F.d w (l.map (lt F)) := by
        simp [atPlace, lt]
      rw [List.map_cons, List.map_cons, h1, ← ih, hs]
      cases b <;> simp [ul, RunFrame.ug, U.UGen.adj]
    · rw [List.map_cons, List.map_cons, hs]
      by_cases h : x.1.1 = w
      · subst h
        have h1 : atPlace F.d x.1.1 (lt F (Sum.inr (Sum.inr x), b) :: l.map (lt F)) =
            (x.2.1, x.2.2, b) :: atPlace F.d x.1.1 (l.map (lt F)) := by
          simp [atPlace, lt]
        rw [h1]
        have h2 : MLM.wordUS F.d x.1.1 ((x.2.1, x.2.2, b) :: atPlace F.d x.1.1 (l.map (lt F))) =
            lconv (if b then lstar (F.d.hU x.1.1 x.2.1) else F.d.hU x.1.1 x.2.1)
              (MLM.wordUS F.d x.1.1 (atPlace F.d x.1.1 (l.map (lt F)))) := rfl
        rw [h2, ← ih]
        cases b <;> simp [ul, RunFrame.ug, U.UGen.adj]
      · have h1 : atPlace F.d w (lt F (Sum.inr (Sum.inr x), b) :: l.map (lt F)) =
            atPlace F.d w (l.map (lt F)) := by
          simp [atPlace, lt, h]
        rw [h1, ← ih]
        cases b <;> simp [ul, RunFrame.ug, U.UGen.adj, h]

end

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.usph_pf :
    USph := by
  intro hR E _ _ _ n π S T F₀ F ws
  refine ⟨count_lw F ws, fun w => ?_⟩
  rw [atPlace_lw, sph_word]

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical



open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} (l : List (BGen B)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ s, Sum.inr s ∈ l → s.T ≤ R ∧ s.r + B.c ≤ R := by
  induction l with
  | nil => exact ⟨0, le_rfl, by simp⟩
  | cons g l ih =>
    obtain ⟨R, hR, hs⟩ := ih
    rcases g with c | t
    · refine ⟨R, hR, fun s hm => ?_⟩
      rcases List.mem_cons.1 hm with h | h
      · cases h
      · exact hs s h
    · refine ⟨max R (max t.T (t.r + B.c)), le_max_of_le_left hR, fun s hm => ?_⟩
      rcases List.mem_cons.1 hm with h | h
      · cases h
        exact ⟨le_max_of_le_right (le_max_left _ _), le_max_of_le_right (le_max_right _ _)⟩
      · exact ⟨(hs s h).1.trans (le_max_left _ _), (hs s h).2.trans (le_max_left _ _)⟩

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.twok_pf :
    BlockWordOperators → TwOk := by
  intro hW hR E _ _ _ n π S T F₀ F h i
  have hadj := (hW E (F.B i) [] (F.t₂ i) 0 (by simp) (h.tok i).2 le_rfl (by simp)).2.2.2.2.1
  have hgl : ∀ p, (gl F i p).Ok ∧ (gl F i p).op = if p.2 then star (F.g p.1 i).op else (F.g p.1 i).op := by
    rintro ⟨x, s⟩
    cases s with
    | false => exact ⟨h.ok x i, rfl⟩
    | true =>
      refine ⟨(hadj _ (h.ok x i)).1, ?_⟩
      show (F.g x i).adj.op = star (F.g x i).op
      rw [(hadj _ (h.ok x i)).2, ContinuousLinearMap.star_eq_adjoint]
  have hbw : ∀ w, ∀ g ∈ bw F i w, g.Ok := by
    intro w g hg
    rcases List.mem_append.1 hg with hg | hg
    · rw [List.eq_of_mem_replicate hg]
      exact h.βok i
    · obtain ⟨p, -, rfl⟩ := List.mem_map.1 hg
      exact (hgl p).1
  refine ⟨hgl, hbw, fun ws => ?_⟩
  obtain ⟨R, hR0, hRs⟩ := exists_bound (Sum.inr (F.t₁ i) :: (ws.map (bw F i)).flatten)
  refine (hW E (F.B i) _ (F.t₂ i) R ?_ (h.tok i).2 hR0 hRs).1
  intro g hg
  rcases List.mem_cons.1 hg with rfl | hg
  · exact (h.tok i).1
  · obtain ⟨l, hl, hgl'⟩ := List.mem_flatten.1 hg
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hl
    exact hbw w g hgl'

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical



open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem val_one_of_ordL {E : Type} [Field E] [NumberField E] {w : Pl E} (u : (w.adicCompletion E)ˣ)
    (hu : ordL (u : w.adicCompletion E) = 0) : Valued.v (u : w.adicCompletion E) = 1 := by
  have h1 : Valued.v (u : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).mpr u.ne_zero
  unfold ordL at hu
  rw [dite_eq_right h1] at hu
  rw [← WithZero.coe_unzero h1]
  have e : Multiplicative.toAdd (WithZero.unzero h1) = 0 := by omega
  have e' : WithZero.unzero h1 = 1 := by
    rw [← ofAdd_toAdd (WithZero.unzero h1), e]; rfl
  rw [e']; rfl

theorem frfacts_pf : FrFacts := by
  intro hR E _ _ _ n π S T F₀ F
  have hsame := F.same
  unfold RF_same at hsame
  obtain ⟨hS₀, hBad, hμ, -⟩ := hsame
  have hloc : ∀ w, F.d.μ w = F₀.μ.loc w := fun w => by rw [hμ]; exact F₀.μloc w
  refine ⟨hloc, fun w u => ?_, fun w hw hB hs => ?_, ?_⟩
  · rw [hloc]
    exact F₀.hμ.1 _
  · have hT : w ∉ F.d.T := fun h => hB (by simp [LocData.B, h])
    have hS : w ∉ F.d.S₀ := fun h => hB (by simp [LocData.B, h])
    have hb : w ∉ F.d.Bad := fun h => hB (by simp [LocData.B, h])
    refine ⟨hs, hT, hS, hb, fun u hu => ?_⟩
    rw [hloc]
    exact (F₀.good w hw (hS₀ ▸ hS) (hBad ▸ hb)).2 u (val_one_of_ordL u hu)
  · intro w hw
    have hw' : w ∈ F.d.T ∪ F.d.S₀ := by simpa [LocData.P] using hw
    rcases Finset.mem_union.mp hw' with h | h
    · exact (F.T_in w h).1
    · exact (F₀.S₀ w (hS₀ ▸ h)).1

end UpperTheory.BaseChangeIdentities.FrameWordIdentity

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical



open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.adelWord_of_parts :
    AdelRep → FinConv → PsiWord → ProdOk → LocOk → FrFacts → TwOk → AdelWord := by
  intro hAR hFC hPW hPO hLO hFR hTw hR E _ _ _ n π S T F₀ F hS i ws
  have hle := F₀.C.le i
  have hsec := F₀.hSec
  have hP := (hFR hR E n π S T F₀ F).2.2.2
  have hne : ∀ w ∈ F.d.P, Nonempty (F.d.kap w) := fun w _ => (hLO E n F.d F.ok _ hle).1 w
  have hL0 := hPO E n F.d F.ok (lw F ws) _ hle
  have ht := hPW hR E n π S T F₀ F i ws
  have hok := (hTw hR E n π S T F₀ F hS i).2.2 ws
  have key := hAR E F.d.kap F₀.Sec F.d.P (F.B i) (Equiv.refl _) hsec hP hne (F₀.u₁ _) (F₀.u₂ _)
    (F₀.A i).Ta (F₀.A i).Tb F.d.one (fun _ => F.d.eL _) [] (tw F i ws)
    (prodL F.d (lw F ws) (F₀.C.a i)) (by simp) hL0 ht
  refine ⟨key.2.2, (hFC E (F.B i) F₀.Sec hsec).1, fun v => ?_⟩
  exact (F₀.A i).lef v _ _ _ _ _ (hok.ka v) (hok.kb v)

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical



open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.testword_pf :
    PTTest → LocMatch → PsiWord → ProdOk → USph → TwOk → FrFacts → LocOk → TestWord := by
  intro hPT hLM hPsi hProd hSph hTw hFr hLoc hR E _ _ _ n π S T F₀ F hE hF i
  obtain ⟨c₀, hc₀, H⟩ := hPT E (F.B i)
  refine ⟨c₀, hc₀, fun ws hws => ?_⟩
  obtain ⟨-, hnorm, hgood, hP⟩ := hFr hR E n π S T F₀ F
  obtain ⟨hcount, hsph⟩ := hSph hR E n π S T F₀ F ws
  have hk : 1 ≤ ws.length := List.length_pos_iff.2 hws
  have hL := hLM E hE n F.d F.ok F.mok F₀.Sec F₀.hSec F.levOff F.T_ne hnorm hgood (lw F ws) F.m ws.length
    F.m_pos hk hcount (ws.flatten.map (ul F)) (fun w _ => hsph w)
  have hle := F₀.C.le i
  have hreg := (hL.2.2 (F₀.C.a i) hle).2
  exact H F.d.kap F₀.Sec F.d.P (Equiv.refl _) F₀.hSec hP (fun w _ => (hLoc E n F.d F.ok _ hle).1 w)
    (F₀.u₁ _) (F₀.u₂ _) (F₀.hu _).1 (F₀.hu _).2 (F₀.A i).Ta (F₀.A i).Tb F.d.one (tw F i ws)
    (prodL F.d (lw F ws) (F₀.C.a i)) ⟨(F₀.A i).vca, (F₀.A i).vcb⟩ ((hTw hR E n π S T F₀ F hF i).2.2 ws)
    (hProd E n F.d F.ok _ _ hle) (hPsi hR E n π S T F₀ F i ws) hreg

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical



open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem val_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} (s t : PT B)
    (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b) :
    (s.mul t).val χa χb = s.val χa χb * t.val χa χb := by
  simp only [PT.val, PT.mul, valA, Pi.mul_apply, Finset.prod_mul_distrib]
  ring

private theorem val_wd {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} (w : List (BGen B)) (t₀ : PT B)
    (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b) :
    (BGen.wd w t₀).val χa χb = (w.map (Sum.elim (fun _ => (1 : ℂ)) fun s : PT B => s.val χa χb)).prod * t₀.val χa χb := by
  induction w with
  | nil => simp [BGen.wd]
  | cons g w ih =>
    rcases g with c | s
    · have e : BGen.wd (Sum.inl c :: w) t₀ = BGen.wd w t₀ := rfl
      rw [e, ih]; simp
    · have e : BGen.wd (Sum.inr s :: w) t₀ = s.mul (BGen.wd w t₀) := rfl
      rw [e, val_mul, ih]; simp [mul_assoc]

private theorem sc_val {E : Type} [Field E] [NumberField E] [IsCMField E] {B : Block E} (w : List (BGen B))
    (χa : InfinitePlace E → Inf B.a) (χb : InfinitePlace E → Inf B.b) :
    BGen.sc w * (w.map (Sum.elim (fun _ => (1 : ℂ)) fun s : PT B => s.val χa χb)).prod =
      (w.map (Sum.elim id fun s : PT B => s.val χa χb)).prod := by
  induction w with
  | nil => simp [BGen.sc]
  | cons g w ih =>
    have hs : BGen.sc (g :: w) = Sum.elim id (fun _ => 1) g * BGen.sc w := by simp [BGen.sc]
    rw [hs, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ← ih]
    rcases g with c | s <;> simp <;> ring

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.archsc_pf :
    BlockWordOperators → TwOk → ArchLet → ArchSc := by
  intro _ _ hL hR E _ _ _ n π S T F₀ F hS i ws
  obtain ⟨hg, hβ, h1, h2⟩ := hL hR E n π S T F₀ F hS i
  set χa := (F₀.A i).χa
  set χb := (F₀.A i).χb
  set f : BGen (F.B i) → ℂ := Sum.elim id fun s : PT (F.B i) => s.val χa χb with hf
  have hv : (tw F i ws).val χa χb =
      ((ws.map (bw F i)).flatten.map (Sum.elim (fun _ => (1 : ℂ)) fun s : PT (F.B i) => s.val χa χb)).prod := by
    have e : tw F i ws = (F.t₁ i).mul (BGen.wd (ws.map (bw F i)).flatten (F.t₂ i)) := rfl
    rw [e, val_mul, val_wd, h1, h2]; simp
  rw [hv, sc_val]
  have hw : ∀ w : List (F.Γ × Bool), ((bw F i w).map f).prod = ((w.map (ul F)).map (Sum.elim id fun _ => (1 : ℂ))).prod := by
    intro w
    have hb : f (Sum.inr (F.β i)) = 1 := hβ
    simp only [bw, List.map_append, List.map_replicate, List.prod_append, hb, List.prod_replicate, one_pow, one_mul,
      List.map_map]
    congr 1
    apply List.map_congr_left
    intro p _
    exact hg p
  simp only [U.UGen.sc]
  clear hv
  induction ws with
  | nil => simp
  | cons w ws ih =>
    simp only [List.map_cons, List.flatten_cons, List.map_append, List.prod_append]
    rw [ih]
    congr 1
    exact hw w

end
end

section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical



open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2

namespace UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem frameWord_length_eq_one_of_hyp (h : LocWord) : heckeLevelWordBase := by
  intro E _ _ _ n d hd a ha p
  exact (h E n d hd a ha [Sum.inl ()] 0 (by simp)).1 p

theorem wordId_of (h1 : TestWord) (h2 : TraceWord) : WordId := by
  intro hR E _ _ _ hE n _ π S T F₀ F hS
  choose c₀ hc₀ hc using h1 hR E n π S T F₀ F hE hS
  exact ⟨fun i => F₀.C.c i * (F.B i).vol, c₀, hc₀, fun ws hws => ⟨fun i => hc i ws hws, h2 hR E n π S T F₀ F hE hS ws hws⟩⟩

end UpperTheory.BaseChangeIdentities.FrameWordIdentity

end
end
