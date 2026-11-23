module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle113
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle116
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle128
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle449
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle457
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle367
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle060
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle373
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle143
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle420
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle497
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeMeasureValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle493
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle290
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle341
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle159
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle329
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle339
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle134
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle468
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle486
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle129
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle130
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle416

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
theorem GlobalTheory.PenBridge.rd_mem_KO_off_twist_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t₀ (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀), J₀.Reads → ∀ (α₀ : J₀.Ch j) t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i, ¬ _root_.GlobalTheory.PenBridge.finitePlaceCondition J₀ (J.G i).q.v → ∀ g ∈ J₀.A.U j (J₀.ι j α₀), _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj g i ∈ KO (J.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _ j hj t₀ J₀ hJ₀ α₀ t J _ i _
  have hjm : j ≤ B.R.m := by omega
  obtain ⟨ε, hε, hε'⟩ := (J.G i).q.above
  have und : (J.pl i).under (𝓞 (I.rec7 l Z).host.F) = (J.G i).q.v :=
    GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (J.G i).idem hε hε'
  have hv := (GlobalTheory.Mem.Col2.TC.underQ_notMem I hW.tr.ok l u (W.P.I.tup t) (J.G i).q.v
    ⟨J.pl i, (hW.tq.Q t _).1 (J.mem i), und⟩).1
  have hlb := (hJ₀.is.reads j hjm).lb (J₀.ι j α₀)
  have hfr : ∀ e : j = (J.G i).s + 1, ∃ pos, IsStdFr pos (_root_.GlobalTheory.PenBridge.frameAtLevel J j i e) := by
    intro e
    subst e
    exact ⟨_, (ha.stdQ _ _).1 _ _⟩
  obtain ⟨pos, hpos⟩ := hfr (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)
  have key : ∀ g ∈ J₀.A.U j (J₀.ι j α₀),
      GlobalTheory.LevIdx.locHom (J.G i).q _ (_root_.GlobalTheory.PenBridge.frameAtLevel J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)) g ∈ KO (J.G i).k _ := by
    refine GlobalTheory.LevProd.OffTwist.locHom_mem_KO (J.G i).q _ (rankN (I.rec7 l Z) j hjm) _ hpos (B.T u) hv
      (J₀.A.K j hjm (J₀.ι j α₀)).lev.Lb (fun x hx r => ?_) (fun s => ?_) (σ := sigD _) (J := gramN (I.rec7 l Z) j hjm) _ (fun g hg => ?_)
    · obtain ⟨c, hc, -⟩ := (hlb x).1 hx r
      exact ⟨c, hc⟩
    · refine (hlb _).2 fun r => ?_
      by_cases h : r = s
      · subst h
        refine ⟨(B.T u : ℕ), (Pi.single_eq_same _ _).trans (map_natCast (algebraMap (𝓞 B.host.E) B.host.E) _).symm, fun _ => ⟨_, (l.pr.piT_norm u).symm⟩⟩
      · exact ⟨0, (Pi.single_eq_of_ne h _).trans (map_zero (algebraMap (𝓞 B.host.E) B.host.E)).symm, fun _ => dvd_zero _⟩
    · obtain ⟨κ, hκ⟩ := ((hJ₀.is.U j hjm _ g).1 hg).2
      exact ⟨κ.1, hκ, (J₀.A.K j hjm (J₀.ι j α₀)).lev.Uloc_lev _
        ((((J₀.A.K j hjm (J₀.ι j α₀)).lev.U_eq κ.1).1 κ.2).2 _)⟩
  intro g hg
  exact (GlobalTheory.PenBridge.toSum0_mem_KO_iff _).2 (key g hg)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LevProd.OffTwist

theorem gl_mem_level_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m) t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) t₂ (J₂ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₂), J₂.Reads → ∀ i : Fin J₂.r, ¬ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J (J₂.G i).q.v → ∀ (gl : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J₂.G i).k →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), (∀ y, SuppAt (J₂.G i).q.e _ (gl y) ∧ (mt _ (gl y)).map (J₂.G i).q.pr = ((J₂.G i).FX j (Nat.le_succ_of_le (_root_.GlobalTheory.LevProd.step_index_le_s_alt J₂ i hj))).β * y.val * ((J₂.G i).FX j (Nat.le_succ_of_le (_root_.GlobalTheory.LevProd.step_index_le_s_alt J₂ i hj))).γ) → ∀ y ∈ KO (J₂.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j), gl y ∈ J.A.U j (J.ι j α) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α t₂ J₂ hJ₂ i hv gl hgl y hy
  have hjm : j ≤ B.R.m := by omega
  have hok : I.Ok := hW.tr.ok
  have hsup : gl y ∈ GlobalTheory.FinPl.grpAt _ (· = (J₂.G i).q.v) :=
    GlobalTheory.SuppGrp.mem_grpAt_of_suppAt _ _ (J₂.G i).q _ _ (hgl y).1 _ rfl
  have hsd : IsSelfDualC ((I.rec7 l Z).sp.X j) (a.g.x j).L := (ha.x j hjm).sd
  have hKO : GlobalTheory.LevIdx.locHom (J₂.G i).q _ ((J₂.G i).FX j (Nat.le_succ_of_le (_root_.GlobalTheory.LevProd.step_index_le_s_alt J₂ i hj))) (gl y) ∈ KO _ _ :=
    (GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 (hgl y).2 ▸ hy
  have hm := GlobalTheory.LevProd.SamePlace.moves_of_mem_KO (J₂.G i).q _ hsd ((J₂.G i).latX j _) hKO
  haveI : Submodule.IsLattice (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E (a.g.x j).L := hsd.1
  have hfg : (a.g.x j).L.FG := Submodule.IsLattice.fg (A := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E) (a.g.x j).L
  have hu₂ : I.UnderQ (W.P.I.tup t₂) (J₂.G i).q.v :=
    ⟨J₂.pl i, (hW.tq.Q t₂ (J₂.pl i)).1 (J₂.mem i), ((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t₂ J₂ hJ₂).2 i).symm⟩
  obtain ⟨hTv, hgv⟩ := GlobalTheory.Mem.Col2.TC.underQ_notMem I hok l u _ _ hu₂
  have hbad : (J₂.G i).q.v ∉ J.A.bad j := fun h => by
    rcases hJ.is.bad_le j hjm _ h with (h0 | h0) | ⟨P, hP, e⟩
    · exact hgv 0 h0
    · exact hgv 1 h0
    · obtain ⟨i', hi'⟩ := hJ.surj P ((hW.tq.Q t P).2 hP)
      refine hv ⟨i', ?_⟩
      rw [(_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t J hJ).2 i', hi']
      exact e
  have hlb := (hJ.is.reads j hjm).lb (J.ι j α)
  refine (hJ.is.U j hjm _ _).2 ⟨GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ hsup, ?_⟩
  obtain ⟨-, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have hd : X.piT u ∣ ((B.T u : ℕ) : 𝓞 B.host.E) := ⟨_, (hPr.piT_norm u).symm⟩
  exact exists_mem_level (I.rec7 l Z) _ _ _ (J.A.K j hjm (J.ι j α)).lev (X.piT u) hd hlb (a.g.x j).L hfg
    (fun x => ((hat.pinX.xs j hjm).2.2 x).trans
      (forall_congr' fun r => ⟨fun h => ⟨⟨x r, h⟩, rfl⟩, fun ⟨s, hs⟩ => hs ▸ s.2⟩)) _ hbad hTv _ hsup hm
end GlobalTheory.LevProd.OffTwist
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.LevProd.SamePlace
open GlobalTheory.FinPl (Lat latV Moves SplitPt)
open GlobalTheory.IwaPlace (hermAt)
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (q : SplitPt D k) {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y) {L : Lat V}

theorem phi_mem_KO_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t₀ (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀), J₀.Reads → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i₀ i, (J₀.G i₀).q.v = (J.G i).q.v → ∀ g ∈ GfC _, _root_.GlobalTheory.LevProd.localHomProduct J₀ j hj g i₀ ∈ KO (J₀.G i₀).k _ → _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ KO (J.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ j hj t₀ J₀ _ t J _ i₀ i hv g _ h0
  have hsd : IsSelfDualC ((I.rec7 l Z).sp.X j) (a.g.x j).L :=
    (ha.x j (by have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)).sd
  have hm := moves_of_mem_KO (J₀.G i₀).q ((J₀.G i₀).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J₀ i₀ hj; omega)) hsd
    ((J₀.G i₀).latX j _) h0
  exact GlobalTheory.SplitInt.mem_KO_of_moves (J.G i).q _ ((J.G i).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega)) (a.g.x j).L
    (· = (J₀.G i₀).q.v) hv.symm ((J.G i).latX j _) g hm _ ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 rfl)
end GlobalTheory.LevProd.SamePlace
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
noncomputable section
namespace GlobalTheory.LevProd.OffTwist
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.LevProd.OffTwist
theorem GlobalTheory.LevProd.phi_mem_KO_of_not_twAt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t₀ (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀), J₀.Reads → ∀ (α₀ : J₀.Ch j) t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i, ¬ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J₀ (J.G i).q.v → ∀ g ∈ J₀.A.U j (J₀.ι j α₀), _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ KO (J.G i).k _ := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _ j hj t₀ J₀ hJ₀ α₀ t J _ i _
  have hjm : j ≤ B.R.m := by omega
  obtain ⟨ε, hε, hε'⟩ := (J.G i).q.above
  have und : (J.pl i).under (𝓞 (I.rec7 l Z).host.F) = (J.G i).q.v :=
    GlobalTheory.IdemUnder.under_eq_of_isIdemAt _ _ _ _ ε (J.G i).idem hε hε'
  have hv := (GlobalTheory.Mem.Col2.TC.underQ_notMem I hW.tr.ok l u (W.P.I.tup t) (J.G i).q.v
    ⟨J.pl i, (hW.tq.Q t _).1 (J.mem i), und⟩).1
  have hlb := (hJ₀.is.reads j hjm).lb (J₀.ι j α₀)
  refine GlobalTheory.LevProd.OffTwist.locHom_mem_KO (J.G i).q _ (rankN (I.rec7 l Z) j hjm) _ ((ha.stdQ _ _).1 j _) (B.T u) hv
    (J₀.A.K j hjm (J₀.ι j α₀)).lev.Lb (fun x hx r => ?_) (fun s => ?_) (σ := sigD _) (J := gramN (I.rec7 l Z) j hjm) _ (fun g hg => ?_)
  · obtain ⟨c, hc, -⟩ := (hlb x).1 hx r
    exact ⟨c, hc⟩
  · refine (hlb _).2 fun r => ?_
    by_cases h : r = s
    · subst h
      refine ⟨(B.T u : ℕ), (Pi.single_eq_same _ _).trans (map_natCast (algebraMap (𝓞 B.host.E) B.host.E) _).symm, fun _ => ⟨_, (l.pr.piT_norm u).symm⟩⟩
    · exact ⟨0, (Pi.single_eq_of_ne h _).trans (map_zero (algebraMap (𝓞 B.host.E) B.host.E)).symm, fun _ => dvd_zero _⟩
  · obtain ⟨κ, hκ⟩ := ((hJ₀.is.U j hjm _ g).1 hg).2
    exact ⟨κ.1, hκ, (J₀.A.K j hjm (J₀.ι j α₀)).lev.Uloc_lev _
      ((((J₀.A.K j hjm (J₀.ι j α₀)).lev.U_eq κ.1).1 κ.2).2 _)⟩
end
end
end

section



section
noncomputable section
namespace GlobalTheory.LevProd.Fwd
section Columns
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Col2.PtExist
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
end Columns
section Local
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV _root_.Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
end Local
section Split
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.L2.Forms IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.AdForm GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Split
end GlobalTheory.LevProd.Fwd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
namespace GlobalTheory.LevProd.Fwd
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}

theorem mem_prCat_of_pr_eq (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (hJ : J.Reads) (j : ℕ) (hj : j + 2 ≤ B.R.m) (β : J.Ch₀ j)
    (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (hg : g ∈ J.A.U j β)
    (y : Fin J.r → (Formalism.L2.Col.Sp B.fields.E (B.R.N j) ≃ₗ[B.fields.E] Formalism.L2.Col.Sp B.fields.E (B.R.N j)))
    (hy : ∀ i r s, (J.G i).q.pr (mt _ g (Fin.cast (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)).symm r)
      (Fin.cast (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)).symm s)) = (J.G i).q.pr (incA (I.rec7 l Z) (y i (Pi.single s 1) r))) (i : Fin J.r) :
    y i ∈ Formalism.L2.Col.prCat (Pr := B.primes X) (I.cst (W.P.I.tup t)).sharp j (J.P i).1
      ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j β).get (show j < B.R.m by omega)) (J.P i)) := by
  have hjm : j ≤ B.R.m := by omega
  have hA := hJ.is
  have hI := hW.tr.ok
  have hL := hI.idx_ok (W.P.I.tup t)
  obtain ⟨hP⟩ := hW.tr.pins
  obtain ⟨c, rfl⟩ := hA.chOf_onto j hjm β
  obtain ⟨-, κ, hκ⟩ := (hA.U j hjm _ g).1 hg
  have hd : Disjoint (B.primes X).vGs (I.Q (W.P.I.tup t)) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I _) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have huni : κ.1 ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N j) := by
    have hgram := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 j hjm).1
    have huni : ∀ (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hjm) (B.T u)
        (I.rec7 l Z).R.f (J.A.bad j)) (x : TC.GA B (B.R.N j)), x ∈ S.U → x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N j) := by
      intro S x hx
      have h := ((S.U_eq x).1 hx).1
      rw [hgram] at h
      exact h
    exact huni _ κ.1 κ.2
  have hloc : ∀ PP i, J.pl i = PP →
      GlobalTheory.Mem.ColAd.locM (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) PP κ.1 = GlobalTheory.Mem.ColAd.ratM PP (y i) := by
    rintro _ i rfl
    exact locM_of_pr (J.G i).q (J.pl i) (J.G i).idem _ _ g κ.1 hκ (y i) (hy i)
  have hsurj : ∀ P : I.Q (W.P.I.tup t), ∃ i, J.pl i = P.1 := fun P => hJ.surj P.1 ((hW.tq.Q t P.1).2 P.2)
  choose ι hι using hsurj
  have hmem : J.pl i ∈ I.Q (W.P.I.tup t) := (hW.tq.Q t _).1 (J.mem i)
  obtain ⟨κ', hκ', e'⟩ := mem_levQ I hI (hA.reads j hjm) c κ.1 huni κ.2 (fun P => by
      rw [hJ.std j (by omega)]
      refine Matrix.ext fun r s => ?_
      refine (GlobalTheory.Fam.MovedJoin.adAt_kStd_of_twist hI _ ⟨P.1, Finset.mem_union_right _ P.2⟩
        (Finset.disjoint_right.1 hd P.2) u _ r s).trans ?_
      rw [Matrix.one_apply]
      split_ifs <;> simp)
    (fun P => y (ι P)) (fun P => hloc _ _ (hι P)) ⟨J.pl i, hmem⟩
  have hii : ι ⟨J.pl i, hmem⟩ = i := hJ.inj (hι ⟨J.pl i, hmem⟩)
  rw [hii] at e'
  have hb : levQAt I.sel (I.tup (W.P.I.tup t)) (I.idx (W.P.I.tup t)) (I.Tp (W.P.I.tup t)) j c.1 =
      (I.idx (W.P.I.tup t)).levQ j ((J.A.b0 j (J.A.chOf j c)).get (show j < B.R.m by omega)) := by
    rw [← (hA.rep j hjm c).1]
    unfold levQAt Idx.get
    conv_lhs => rw [← Option.some_get (c.1.2.2 (show j < B.R.m by omega))]
    rfl
  rw [hb, hL.grpQ, Subgroup.mem_subgroupOf, e'] at hκ'
  have hPi : J.P i = ⟨J.pl i, Finset.mem_union_right _ hmem⟩ := Subtype.ext (hJ.eq i)
  rw [hPi]
  exact hκ'
end GlobalTheory.LevProd.Fwd
namespace GlobalTheory.LevProd
open GlobalTheory.LevProd.Fwd

theorem phi_mem_H_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j), ∀ g ∈ J.A.U j (J.ι j α), ∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj t J hJ α g hg
  have hjm : j ≤ B.R.m := by omega
  have hL := hW.tr.ok.idx_ok (W.P.I.tup t)
  obtain ⟨hP⟩ := hW.tr.pins
  have hrk := rankN (I.rec7 l Z) j hjm
  have hstd := fun i : Fin J.r => (ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; exact this.trans (Nat.le_succ _))
  choose e he hF using hstd
  let e₀ : Fin J.r → (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j ≃ Fin ((I.rec7 l Z).R.N j)) := fun i => (e i).trans (finCongr hrk)
  have key := fun i : Fin J.r => prCat_iff _ _ _ I.Ch I.sel _ (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i) _ _ _ _
      (J.G i).ν (J.G i).unitVol hL.cst_ok (hJ.tw i) j ((J.G i).s - j) (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega) _ _
      (hJ.rep i j ((J.G i).s - j) (Nat.add_sub_cancel' (_root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj)) (by omega) (J.ι j α)) (e₀ i) (fun r => he i r)
  have hHo : ∀ i, IsOpen (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) := fun i => by
    have h := (key i).1
    rw [hJ.sec j hjm α i] at h
    exact h
  have hHr : ∀ i y, y ∈ Formalism.L2.Col.prCat (Pr := B.primes X) (I.cst (W.P.I.tup t)).sharp j (J.P i).1
      ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j (J.ι j α)).get (show j < B.R.m by omega)) (J.P i)) →
      GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (e₀ i) y ∈ _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i := fun i y hy => by
    have h := ((key i).2 y).1 hy
    rw [hJ.sec j hjm α i] at h
    exact h
  have hUo := (GlobalTheory.ChartReps.twDat_reps I hW.tr.ok hP l Z u _ _ J.A hJ.is j hjm (J.ι j α)).1.opn
  have hgl := fun i : Fin J.r => GlobalTheory.LocEmb.exists_gl _ _ (J.G i).q ((I.rec7 l Z).sp.X j)
    (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ((J.G i).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J i hj; omega))
  choose gl hglc hglp _ using hgl
  have hAt : ∀ i x, gl i x ∈ GlobalTheory.FinPl.grpAt _ (· = (J.G i).q.v) := fun i x =>
    GlobalTheory.SuppGrp.mem_grpAt_of_suppAt _ _ _ _ _ (hglp i x).1 _ rfl
  have hVo : ∀ i, IsOpen {x | gl i x ∈ J.A.U j (J.ι j α)} := fun i =>
    hUo.preimage (f := fun x => (⟨gl i x, GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hAt i x)⟩ : GfC _)) ((hglc i).subtype_mk _)
  have hy : ∀ i, ∃ y, GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (e₀ i) y ∈
      (fun v => (_root_.GlobalTheory.LevProd.localHomProduct J j hj g i)⁻¹ * v) ⁻¹' ((_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i : Set _) ∩ {x | gl i x ∈ J.A.U j (J.ι j α)}) := fun i =>
    GlobalTheory.denseGL_completion _ (J.G i).compl.dense (e₀ i) (_root_.GlobalTheory.LevProd.localHomProduct J j hj g i) _
      (((hHo i).inter (hVo i)).preimage (continuous_const.mul continuous_id))
      (by
        rw [Set.mem_preimage, inv_mul_cancel]
        exact ⟨one_mem _, by rw [Set.mem_setOf_eq, map_one]; exact one_mem _⟩)
  choose y hy using hy
  set x : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k := fun i =>
    (_root_.GlobalTheory.LevProd.localHomProduct J j hj g i)⁻¹ * GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (e₀ i) (y i) with hx
  have hphi : ∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj (gl i (x i)) = Pi.mulSingle i (x i) := by
    intro i
    funext i'
    show GlobalTheory.LevIdx.locHom (J.G i').q _ ((J.G i').FX j _) (gl i (x i)) = _
    by_cases h : i' = i
    · subst h
      rw [Pi.mulSingle_eq_same]
      exact ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 ((hglp i' (x i')).2)).symm
    · rw [Pi.mulSingle_eq_of_ne h]
      exact locHom_eq_one (J.G i).q (J.G i').q _ _
        (fun hv => h ((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hat t J hJ).1 hv)) (hAt i _)
  have hg' : g * ((List.finRange J.r).map fun i => gl i (x i)).prod ∈ J.A.U j (J.ι j α) := by
    refine mul_mem hg (Subgroup.list_prod_mem _ fun z hz => ?_)
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hz
    exact (hy i).2
  have hφ' : ∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj (g * ((List.finRange J.r).map fun i => gl i (x i)).prod) i =
      GlobalTheory.VolBridge.locHom ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (e₀ i) (y i) := by
    intro i
    rw [map_mul, map_list_prod, List.map_map]
    simp only [Function.comp_def, hphi]
    rw [list_prod_mulSingle x, Pi.mul_apply]
    exact mul_inv_cancel_left _ _
  intro i
  have h1 := hHr i _ (_root_.GlobalTheory.LevProd.Fwd.mem_prCat_of_pr_eq hW J hJ j hj _ _ hg' y (fun i r s => by
    obtain ⟨r, rfl⟩ := (e₀ i).surjective r
    obtain ⟨s, rfl⟩ := (e₀ i).surjective s
    exact (locHom_std (J.G i).q _ _ (e i) (hF i) _ r s).symm.trans (congrArg (fun z => z.val r s) (hφ' i))) i)
  have h2 : x i ∈ _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i := (hy i).1
  have h3 := mul_mem h1 (inv_mem h2)
  rw [hx] at h3
  simpa using h3
end GlobalTheory.LevProd
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] _root_.GlobalTheory.Fam.GeometricFamily.fld _root_.GlobalTheory.Fam.GeometricFamily.val _root_.GlobalTheory.Fam.GeometricFamily.top _root_.GlobalTheory.Fam.GeometricFamily.loc
set_option genSizeOfSpec false
set_option genInjectivity false
noncomputable section
namespace GlobalTheory.QPl.PinComb
variable {D : D7} {c : Comm D}
variable {v : VCom c} {χ : ℕ → (AE D)ˣ →* Circle}
end GlobalTheory.QPl.PinComb
open GlobalTheory.QPl.PinComb in
theorem GlobalTheory.QPl.PinComb.famOf_pinTup_combAt_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t, ∀ j,
    GlobalTheory.FinPl.CombAt (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).eQ j) ∧ (∀ h, GlobalTheory.FinPl.CombAt (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).eQT j h)) ∧
    ∀ α γ, GlobalTheory.FinPl.CombAt (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).dQ j α γ) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a _ _ J _ row col hCh sc cT t j
  exact pinTup_combAt _ sc cT j
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.all_true_family_geometry_column_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {hT : GatTies (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Gi : Formalism.MainNotions.G.Inst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L} {Gl : Formalism.MainNotions.G.LatInst (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)} {cX : ExtraC} {ex : Extra (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (g : GlobalTheory.Fam.Geo (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (c₀ : ℕ → ℂ) (v : VCom (commOf (_root_.GlobalTheory.Fam.pk_z W) u g)) (ζ₀ : Fin g.Lz.rank → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E), GlobalTheory.AdForm.PinX I l Z (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ g.x g.vac c₀ → v.NT = (_root_.GlobalTheory.Fam.pk_z W).ΛX → (∀ p, p ∈ v.tP ↔ ((B.T u : ℕ) : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → IsLineVec g.Lz ζ₀ → (∀ r, vecB (g.oT B.R.m rfl) ζ₀ r = (show Fin (B.R.N B.R.m) → (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E from TC.z0 X u) (Fin.cast (Formalism.L2.Forms.rankN (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) _ le_rfl) r)) → GlobalTheory.AdForm.IsEmbTop (D := _root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) (TC.z0 X u) ((g.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) → (∀ x : GlobalTheory.FinPl.Pl (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G), ((B.T u : ℕ) : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ x.asIdeal → ∃ LZ : GlobalTheory.FinPl.Lat g.Lz, GlobalTheory.FinPl.OrthAt (g.oT B.R.m rfl) (g.x B.R.m).L (_root_.GlobalTheory.Fam.pk_z W).ΛX LZ x) → (∀ j h, (v.τ j h)ᴴ * ((g.bes j 0 h).L.gram * v.τ j h) = (-((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.xi0 * star (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.xi0)) • g.Lz.gram ∧ v.τ j h *ᵥ ζ₀ = (-(_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.xi0 ^ (B.R.m / 2)) • (g.bes j 0 h).ζ) → ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type) (o : TDat (commOf (_root_.GlobalTheory.Fam.pk_z W) u g) k ι), PreT v o ∧ o.ζ₀ = ζ₀ ∧ GlobalTheory.AdForm.StdT I l Z u o.p o.β o.Q fun j => (g.x j).L := by
  first | exact @_root_.GlobalTheory.LevPrimeData.data_preT_alt | exact _root_.GlobalTheory.LevPrimeData.data_preT_alt | (intros; apply _root_.GlobalTheory.LevPrimeData.data_preT_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.true_geometry_chain_descent_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j, j + 1 ≤ B.R.m → IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.g.vac j) ∧ IsLatVac (heisO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _) (stdHom _ _) (a.g.vac j) ∧ IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (a.v.dT j) (a.g.vac j)) := by
  first | exact @_root_.GlobalTheory.Fam.VacTheta.main_alt_alt | exact _root_.GlobalTheory.Fam.VacTheta.main_alt_alt | (intros; apply _root_.GlobalTheory.Fam.VacTheta.main_alt_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.type_primes_disjoint' : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ u : B.Word, Disjoint ((B.primes X).vT u) (B.primes X).vGs := by
  first | exact @_root_.GlobalTheory.Mem.Col2.DisjProof.vT_disjoint_vGs_alt | exact _root_.GlobalTheory.Mem.Col2.DisjProof.vT_disjoint_vGs_alt | (intros; apply _root_.GlobalTheory.Mem.Col2.DisjProof.vT_disjoint_vGs_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TopVol GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.true_geometry_subspace_property_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ U : Subgroup (GA (I.rec7 l Z) (I.rec7 l Z).sp.X'), U ≤ GfC _ → IsCompact (U : Set (GA (I.rec7 l Z) (I.rec7 l Z).sp.X')) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC (I.rec7 l Z).sp.X')) : Set (GfC (I.rec7 l Z).sp.X')) → volLev a.g.volT U ≠ 0 := by
  first | exact @_root_.GlobalTheory.TopVol.volLev_top_ne_zero_alt | exact _root_.GlobalTheory.TopVol.volLev_top_ne_zero_alt | (intros; apply _root_.GlobalTheory.TopVol.volLev_top_ne_zero_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel
namespace GlobalTheory.LevUnif
theorem unif_of_gRead_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))), _root_.GlobalTheory.Fam.LocalGroupReading (a.fam row col) a.G a.pl → ∀ n : Fin a.n, valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((Formalism.L2.Col.qOf (a.pl n).1 : ℕ) : (a.G n).k)) < valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a row col hR n
  exact _root_.GlobalTheory.LevelUnif.valuation_uniformizer_sub_q_lt (D := I.rec7 l Z) _ _ _ hR hW.lev.1 n
end GlobalTheory.LevUnif
end
end
