module

public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.HeckeLevelWordBase
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeWordBounds.ChainSc
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle003
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

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf)
open scoped Classical



open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.B3 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcN.F2
open UpperTheory.BaseChangeIdentities.FrameWordIdentity

attribute [local instance] borelG borelF borelA GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.uok_pf :
    U.UAdj → HuHecke → UOk := by
  intro hA hH hR E _ _ _ n π S T F₀ F hE p
  have hB : ∀ {w : Pl E}, F.d.Good w → w ∉ F.d.B := by
    intro w hw
    obtain ⟨-, hT, hS, hB, -⟩ := hw
    simp [LocData.B, hT, hS, hB]
  have hok : ∀ x, (F.ug x).Ok F₀.Sec F.d.B := by
    intro x
    rcases x with _ | x | x
    · exact trivial
    · exact trivial
    · exact ⟨x.1.2.1, hB x.1.2.2, hH E n F.d F.ok _ x.1.2.2 x.2.1⟩
  obtain ⟨x, b⟩ := p
  have hadj := hA E hE n F₀.Sec F₀.lam F.d.KU F.fam F.d.B (F.d.gU F.m) F.R F.levOff (F.ug x) (hok x)
  cases b
  · simpa [ul] using hok x
  · simpa [ul] using hadj

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

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.prodok_pf :
    TMul → LocOk → heckeLevelWordBase → ProdOk := by
  intro hT hL hW E _ _ _ n d hd ls a ha
  have hk := (hL E n d hd a ha).1
  have hbase : LM.Ok d.P (d.eL a) := (hL E n d hd a ha).2.2.2 _ (Or.inl rfl)
  have hfix := (hL E n d hd a ha).2.2.1
  have hrest : LM.Ok d.P (List.foldr LM.mul (d.eL a) (List.map (locL d a ha) ls)) := by
    induction ls with
    | nil => simpa using hbase
    | cons p ls ih =>
      simp only [List.map_cons, List.foldr_cons]
      exact hT E a (n - a) d.kap d.P hk _ _ (hW E n d hd a ha p).1 ih
  rw [prodL, dite_eq_left ha, List.foldr_cons]
  exact hT E a (n - a) d.kap d.P hk _ _ hfix hrest

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

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.psiword_pf :
    PsiGen → PsiLet → heckeLevelWordBase → LocOk → MLM.MatchLMId → FrFacts → PsiWord := by
  intro hG hPL hW hLO hId hFF hR E _ _ _ n π S T F₀ F i ws
  have ha : F₀.C.a i ≤ n := F₀.C.le i
  have hE := hW E n F.d F.ok (F₀.C.a i) ha (.inr (.inl ()))
  have hB := hW E n F.d F.ok (F₀.C.a i) ha (.inl ())
  have hFx : (F.d.fixL (F₀.C.a i)).Ok F.d.P := (hLO E n F.d F.ok (F₀.C.a i) ha).2.2.1
  have hFe : ((F.d.eL (F₀.C.a i)).mul (F.d.fixL (F₀.C.a i))).Eqv F.d.P (F.d.fixL (F₀.C.a i)) :=
    (hId E n F.d F.ok (F₀.C.a i) ha _ (Or.inr (Or.inl rfl))).2
  have hP : (↑F.d.P : Set (Pl E)) ⊆ F₀.Sec := (hFF hR E n π S T F₀ F).2.2.2
  let l : List (BGen (F.B i) × LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) :=
    (Sum.inr (F.t₁ i), F.d.fixL (F₀.C.a i)) ::
      (ws.map fun w => List.replicate F.m
          ((Sum.inr (F.β i), F.d.betaL (F₀.C.a i) ha) : BGen (F.B i) × LM F.d.kap (F₀.C.a i) (n - F₀.C.a i)) ++
        w.map fun p => (gl F i p, locL F.d (F₀.C.a i) ha (lt F p))).flatten
  have e1 : l.map Prod.fst = Sum.inr (F.t₁ i) :: (ws.map (bw F i)).flatten := by
    simp only [l, bw, List.map_cons, List.map_flatten, List.map_map, Function.comp_def, List.map_append, List.map_replicate]
    rfl
  have e2 : (l.map Prod.snd).foldr LM.mul (F.d.eL (F₀.C.a i)) = prodL F.d (UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw F ws) (F₀.C.a i) := by
    have : l.map Prod.snd = F.d.fixL (F₀.C.a i) :: (UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw F ws).map (locL F.d (F₀.C.a i) ha) := by
      simp only [l, UpperTheory.BaseChangeIdentities.FrameWordIdentity.lw, List.map_cons, List.map_flatten, List.map_map, Function.comp_def, List.map_append, List.map_replicate]
      rfl
    rw [this, prodL, dite_eq_left ha]
  have hl : ∀ x ∈ l, x.2.Ok F.d.P ∧ ((F.d.eL (F₀.C.a i)).mul x.2).Eqv F.d.P x.2 ∧
      ((∃ c, x.1 = Sum.inl c ∧ x.2 = F.d.eL (F₀.C.a i)) ∨
        ∃ s, x.1 = Sum.inr s ∧ s.ψ = fm F₀.Sec F.d.P (F.B i) (Equiv.refl _) x.2) := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨hFx, hFe, Or.inr ⟨_, rfl, rfl⟩⟩
    · obtain ⟨y, hy, hxy⟩ := List.mem_flatten.1 hx
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy
      rcases List.mem_append.1 hxy with h | h
      · rw [List.eq_of_mem_replicate h]
        exact ⟨hB.1, hB.2.1, Or.inr ⟨_, rfl, rfl⟩⟩
      · obtain ⟨p, -, rfl⟩ := List.mem_map.1 h
        have hp := hW E n F.d F.ok (F₀.C.a i) ha (lt F p)
        refine ⟨hp.1, hp.2.1, ?_⟩
        rcases hPL hR E n π S T F₀ F i p with ⟨c, h1, h2⟩ | ⟨s, h1, h2⟩
        · exact Or.inl ⟨c, h1, h2⟩
        · exact Or.inr ⟨s, h1, h2⟩
  have key := hG E F.d.kap F₀.Sec F.d.P (F.B i) (Equiv.refl _) F₀.hSec hP (F₀.u₁ _) (F₀.u₂ _)
    (F.d.eL (F₀.C.a i)) (F.t₂ i) hE.1 hE.2.1 rfl l hl
  rw [e1, e2] at key
  exact key

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

theorem _root_.UpperTheory.BaseChangeIdentities.FrameWordIdentity.traceword_pf :
    U.UWord → LocMatch → ChainSc → FBL.EllHom → AdelWord → ArchSc → USph → UOk → FrFacts → TraceWord := by
  intro hUW hLM hCS hEH hAW hAS hUS hUO hFF hR E _ _ _ n π S T F₀ F hE hF ws hws
  obtain ⟨hμ, hnorm, hgood, hP⟩ := hFF hR E n π S T F₀ F
  obtain ⟨hcnt, hsph⟩ := hUS hR E n π S T F₀ F ws
  have hk : 1 ≤ ws.length := List.length_pos_iff.2 hws
  obtain ⟨hHecke, hsep, hall⟩ := hLM E hE n F.d F.ok F.mok F₀.Sec F₀.hSec F.levOff F.T_ne hnorm hgood (lw F ws) F.m ws.length
    F.m_pos hk hcnt (ws.flatten.map (ul F)) (fun w _ => hsph w)
  have hlU : ∀ x ∈ ws.flatten.map (ul F), U.UGen.Ok F₀.Sec F.d.B x := by
    intro x hx
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
    exact (hUO hR E n π S T F₀ F hE p).1
  obtain ⟨hT, htr⟩ := hUW E hE n F₀.Sec F₀.lam F.d.KU F.fam F.d.B (F.d.gU F.m) F.R F.levOff hHecke ws.length _ hlU
  rw [htr hsep]
  have hch := hCS E n F₀.μ F₀.e F₀.lam F₀.C F₀.Sec F₀.hSec F.d.KU _ F.levOff.2.1 hT F₀.u₁ F₀.u₂ F₀.hu
    (fun a => (prodL F.d (lw F ws) a).tr F.d.P F.d.one) (fun a => (prodL F.d (lw F ws) a).t)
    (fun a ha => by
      obtain ⟨⟨h1, h2, h3, h4⟩, -⟩ := hall a ha
      refine ⟨h1, h2, h3, fun w hw => ?_⟩
      rw [← hμ w]
      exact h4 w hw)
    (fun i => by
      obtain ⟨-, w, hw, hns, hreg⟩ := hall (F₀.C.a i) (F₀.C.le i)
      refine ⟨w, hw, ?_⟩
      have : seen ((prodL F.d (lw F ws) (F₀.C.a i)).tr F.d.P F.d.one) (prodL F.d (lw F ws) (F₀.C.a i)).t w =
          (prodL F.d (lw F ws) (F₀.C.a i)).tr F.d.P F.d.one w := by
        funext y
        simp [seen, hns]
      rw [this]
      exact hreg)
    (fun i v => (tw F i ws).va v ((F₀.A i).χa v) * (tw F i ws).vb v ((F₀.A i).χb v))
    (fun i => (tw F i ws).arch (F₀.A i).Ta (F₀.A i).Tb)
    (fun i v => ((hAW hR E n π S T F₀ F hF i ws).2.2 v))
    (fun i => BGen.sc (ws.map (bw F i)).flatten) (U.UGen.sc (ws.flatten.map (ul F)))
    (fun i => by
      rw [Finset.prod_mul_distrib]
      exact hAS hR E n π S T F₀ F hF i ws)
  rw [hch]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨h1, h2, -⟩ := hAW hR E n π S T F₀ F hF i ws
  rw [h1, hEH]
  field_simp

end
end
