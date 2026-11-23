module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle111
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle113
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle409
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle396
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle453
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle297
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle443
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle128
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle539
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle369
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle493
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle482
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle420
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle115
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle166
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle738
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle304
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle594
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle571
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle836
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle517
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle410
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle835
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle008
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle185
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle180
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle179
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle043
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle175
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.Fam
namespace VolMid
end VolMid
open VolMid
theorem volLev_mul_wt_mid_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j, j + 2 ≤ B.R.m → ∃ v : ℂ, v ≠ 0 ∧ ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α, (GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) : ℂ) * J.wt j α = v := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT j hj
  obtain ⟨Up, hUpf, hUpc, hK⟩ := _root_.GlobalTheory.T.true_geometry_step_value_alt W hW u a ha haT j hj
  have step : ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α : J.Ch j,
      (GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) : ℂ) * J.wt j α = (GlobalTheory.SeeSaw.volLev (a.g.x j).vol Up : ℂ) ∧
        J.wt j α ≠ 0 ∧ GlobalTheory.SeeSaw.volLev (a.g.x j).vol (J.A.U j (J.ι j α)) ≠ 0 := by
    intro t J hJ α
    obtain ⟨H, φ, hH, hφK, hφs, hU⟩ := hK t J hJ α
    have hidx := relIndex_eq_prod_of_pi φ Up (J.A.U j (J.ι j α)) (fun i => KO (J.G i).k _) H hφK hφs hU
    have hreps := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hW.tr.ok hW.tr.pins.some l Z u (W.P.I.tup t) J.Ch₀ J.A hJ.is j (by omega) (J.ι j α)).1
    have hvol := GlobalTheory.T.archimedeanLevelVolume_mul_relIndex (I.rec7 l Z) _ (a.g.x j).vol (J.A.U j (J.ι j α)) Up (fun g hg => ((hU g).1 hg).1) hUpf hUpc
      hreps.opn
    have hwt : J.wt j α = ((J.A.U j (J.ι j α)).relIndex Up : ℂ) := by
      rw [hidx, _root_.GlobalTheory.Fam.QuadraticExtensionData.wt]
      push_cast
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [(hH i).2.2.2]
      exact GlobalTheory.T.inv_haarVolume_toReal_eq_relIndex_integral (J.G i) _ (J.E i) j (H i) (hH i).1 (hH i).2.1 (hH i).2.2.1
    refine ⟨?_, ?_, GlobalTheory.AdForm.PinInhab.volLev_ne_zero hW.tr.ok haT.pinX.inf j _ _ hreps⟩
    · rw [hwt, ← hvol]; push_cast; ring
    · rw [hwt, hidx]; push_cast; exact Finset.prod_ne_zero_iff.2 fun i _ => by exact_mod_cast (hH i).2.2.1
  by_cases hex : ∃ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.Reads ∧ Nonempty (J.Ch j)
  · obtain ⟨t, J, hJ, ⟨α⟩⟩ := hex
    refine ⟨GlobalTheory.SeeSaw.volLev (a.g.x j).vol Up, ?_, fun t' J' hJ' α' => (step t' J' hJ' α').1⟩
    obtain ⟨h1, h2, h3⟩ := step t J hJ α
    rw [← h1]
    exact mul_ne_zero (by exact_mod_cast h3) h2
  · exact ⟨1, one_ne_zero, fun t J hJ α => absurd ⟨t, J, hJ, ⟨α⟩⟩ hex⟩
end GlobalTheory.Fam
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
namespace GlobalTheory.Fam
theorem colOf_readS_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (k : _root_.GlobalTheory.Fam.FamilyConstants a),
    ∃ S' : ∀ (t : W.P.T) j, type_of% (k.ε 0) → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j → GlobalTheory.AdForm.ColT I l u (W.P.I.tup t) j,
    ∀ t, (∀ j, j ≤ B.R.m → ∀ η φ, (J t).A.RamL (J t).ι j φ → (J t).A.RamL (J t).ι j (S' t j η φ)) ∧
      ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (kom : ∀ (_ : W.P.T) j, Om ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1))) (dd : ∀ t j, (J t).Ch j → (J t).Ch (j + 1) → WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) →₀ ℂ) (s : ∀ t j, (J t).Ch j → ℂ) (cV cK : W.P.T → ℕ → ℂ) (cP : W.P.T → ℂ),
        @ReadS _ _ _ a.fld a.val a.top a.loc _ a.o ((a.fam row (_root_.GlobalTheory.Fam.columnChoiceOfCoefficients a J kom dd (fun t j => S' t j (k.ε j)) s cV cK cP)).t t) k.ε (S' t 0) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ha hat J hJ k
  letI := a.fld; letI := a.val; letI := a.top; letI := a.loc
  choose S hS using fun t => GlobalTheory.T.levelPrimeOperators_act_ramifiedColumns_vanishing I hW.tr.ok hW.tr.pins.some l Z u (W.P.I.tup t) _ _ (J t).A (J t).ι (hJ t).is (_root_.GlobalTheory.Fam.pk_z W).θ
    hat.pinX.inf a.k a.ι a.o.p a.o.β a.o.Q (fun j => (a.g.x j).L) hat.std a.o.I a.o.q a.o.χ a.o.hχ
  refine ⟨S, fun t => ⟨fun j hj η φ hφ => ((hS t j hj φ hφ).2 η).1, fun row kom dd s cV cK cP => ?_⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro j hj ψ hψ α y
    have h := (hS t j hj ψ hψ).1 ((J t).ι j α) y
    change (if hj' : j ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ j hj' ((J t).ι j α) ψ y else 0) ∈ a.o.Ram j
    have hj2 : j ≤ B.R.m := hj
    rw [dite_eq_left hj2]
    exact h
  · intro j hj ψ hψ α y
    have hj' : j ≤ B.R.m := by change j + 2 ≤ B.R.m at hj; omega
    change (if h : j ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ j h ((J t).ι j α) (S t j (k.ε j) ψ) y else 0) =
      a.o.S k.ε j (if h : j ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ j h ((J t).ι j α) ψ y else 0)
    rw [dite_eq_left hj', dite_eq_left hj']
    exact ((hS t j hj' ψ hψ).2 (k.ε j)).2 _ y
  · intro η ψ hψ
    have h0 : (0 : ℕ) ≤ B.R.m := Nat.zero_le _
    refine ⟨((hS t 0 h0 ψ hψ).2 η).1, fun α y => ?_⟩
    change (if h : 0 ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ 0 h ((J t).ι 0 α) (S t 0 η ψ) y else 0) =
      a.o.S (fun _ => η) 0 (if h : 0 ≤ B.R.m then (J t).A.rd (_root_.GlobalTheory.Fam.pk_z W).θ 0 h ((J t).ι 0 α) ψ y else 0)
    rw [dite_eq_left h0, dite_eq_left h0]
    exact ((hS t 0 h0 ψ hψ).2 η).2 _ y
end GlobalTheory.Fam
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
namespace GlobalTheory.PenLev

theorem mem_tuple_free_level_of_mem_K_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ κ, GlobalTheory.FinPl.InK _ (a.g.x j).L (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) κ → κ ∈ _root_.GlobalTheory.PenLev.baseLevelSubgroup a j hj := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ κ hκ
  have hch : ∀ i, Nonempty ((J.E i).Ch j) := fun i => by
    obtain ⟨y, -⟩ := (J.E i).cos_all 0 (zero_mem _)
    rw [_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i]
    exact ⟨y⟩
  let α : J.Ch j := fun i => (hch i).some
  rw [← _root_.GlobalTheory.T.true_geometry_tuple_free_relation_alt W hW u a ha hTr j hj t J hJ α, _root_.GlobalTheory.PenLev.mem_relax_iff']
  refine ⟨Subgroup.mem_sup_right hκ.1, GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ hκ.1, fun i => ?_⟩
  change GlobalTheory.PenBridge.toSum0 _ _ _ ∈ _
  rw [GlobalTheory.PenBridge.toSum0_mem_KO_iff]
  exact GlobalTheory.SplitInt.mem_KO_of_moves (J.G i).q _ (_root_.GlobalTheory.PenBridge.frameAtLevel J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)) (a.g.x j).L
    (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) ⟨i, rfl⟩ (_root_.GlobalTheory.PenBridge.int_in_frame_at_level J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)) κ hκ.2 _
    ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).2 rfl)
end GlobalTheory.PenLev
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
namespace GlobalTheory.PenLev

theorem tuple_free_level_moves_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ g ∈ _root_.GlobalTheory.PenLev.baseLevelSubgroup a j hj, GlobalTheory.FinPl.Moves _ g (a.g.x j).L (a.g.x j).L (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ g hg
  have hch : ∀ i, Nonempty ((J.E i).Ch j) := fun i => by
    obtain ⟨y, -⟩ := (J.E i).cos_all 0 (zero_mem _)
    rw [_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i]
    exact ⟨y⟩
  let α : J.Ch j := fun i => (hch i).some
  rw [← _root_.GlobalTheory.T.true_geometry_tuple_free_relation_alt W hW u a ha hTr j hj t J hJ α, _root_.GlobalTheory.PenLev.mem_relax_iff'] at hg
  obtain ⟨-, -, hK⟩ := hg
  have hsd : IsSelfDualC ((I.rec7 l Z).sp.X j) (a.g.x j).L :=
    (ha.x j (by have h2 : (I.rec7 l Z).R.m = B.R.m := rfl; omega)).sd
  have hP : _root_.GlobalTheory.PenBridge.finitePlaceCondition J = (· ∈ Finset.univ.image fun i => (J.G i).q.v) := by
    funext p
    simp [_root_.GlobalTheory.PenBridge.finitePlaceCondition]
  rw [hP]
  refine GlobalTheory.FinPl.MovesPl.moves_of_places _ _ _ _ _ fun v hv => ?_
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hv
  refine GlobalTheory.LevProd.SamePlace.moves_of_mem_KO (J.G i).q (_root_.GlobalTheory.PenBridge.frameAtLevel J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)) hsd
    (_root_.GlobalTheory.PenBridge.int_in_frame_at_level J j i _) ?_
  have h1 := hK i
  rw [_root_.GlobalTheory.PenBridge.reductionHomAtLastLevel, MonoidHom.pi_apply, _root_.GlobalTheory.PenBridge.rd_at_apply] at h1
  exact (GlobalTheory.PenBridge.toSum0_mem_KO_iff _).1 h1
end GlobalTheory.PenLev
end
end
end

section



section
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

theorem _root_.GlobalTheory.T.placed_bessel_pair_relation_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → 1 ≤ D.R.rS → ∀ u u' (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (f' : _root_.GlobalTheory.Fam.FamilyCharacter W u') (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)) (B' : SBes W.S.X W.Q.instEq u' W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → _root_.GlobalTheory.MiTop.PlacedConditions f' B' → ∀ a₀ a a₀' a', _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → _root_.GlobalTheory.MiTop.IsTranslate' f' B' a₀' a' → ∀ z ∈ GfC (D.sp.Y 0), z ∈ Subgroup.center (GA D (D.sp.Y 0)) → ∀ k ∈ _root_.GlobalTheory.MiTop.rJ_z W, _root_.GlobalTheory.MiTop.translationElement f B a₀ a = z * _root_.GlobalTheory.MiTop.translationElement f' B' a₀' a' * k → Formalism.IndefR.Lev.finE (Yc D 0) (show GA D (Yc D 0) from z) ∈ Formalism.L2.DIV.St (W.Q.Rl.βY 0) := by
  first | exact @_root_.GlobalTheory.MiTop.finE_centralRatio_mem_St_alt | exact _root_.GlobalTheory.MiTop.finE_centralRatio_mem_St_alt | (intros; apply _root_.GlobalTheory.MiTop.finE_centralRatio_mem_St_alt <;> assumption)
end
end

section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NLink
theorem splitPrime_hyps_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → ∀ i, TwistedPlaces.TwLoc D i → D.nd.l i ∉ TwistedPlaces.gset D → KillingConditions.RangeAD L X.exc (D.nd.l i) → TwistedPlaces.SplitK D (D.nd.l i) → ∃ ep, EmbeddingTypes.hypDecl i (X.dc i) ep ∧ (∀ v ∈ placesOver D.host.E (D.nd.l i), v.asIdeal.ramificationIdx ℤ = 1) ∧ ∀ π ∈ D.nd.Zgood i, EmbeddingTypes.admitted i (X.r i) (X.ρ i) π (X.dc i) ep (X.eS i) (X.c0 i) (X.cB i) := by
  intro Pr D L P nch HW F Cm X C₂ S i hTw hg hR hSp
  have fa := S.facts
  have hJ : AdmissibleParameterJ.ConclusionJa D := (_root_.GlobalTheory.JumpStatement.holds_all_alt D L (fa.admJ L S.par)).1
  have hb : ((0 : ℕ) : ℝ) ≤ L.sc.b := by
    rw [Nat.cast_zero]; exact (Real.exp_pos _).le
  have hL : (1 : ℝ) ≤ L.sc.L := by have := S.big; linarith
  have hub := _root_.GlobalTheory.T.split_bound_of_params_alt Pr.font Pr.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 S.canon P hL le_rfl hb
    (fa.admJ L S.par) S.par67 fa.toCore.admA fa.Conclusion1.1 fa.Conclusion1.2.2 fa.Conclusion2.1 fa.Conclusion2.2.2 fa.rhoBar fa.large.2.1
    fa.large.2.2 fa.nct fa.trip fa.same fa.block fa.muUnr fa.depthG
  obtain ⟨_, _, _, _, _, _, _, hRest, hTB, hRow, _⟩ := hub
  obtain ⟨hDecl, hRam, hType, hPt, _⟩ := hRow i hTw hg hR hSp
  refine ⟨hJ.choose, hDecl hJ, hRam, ?_⟩
  intro π hπ
  have sp := _root_.GlobalTheory.T.set_pt_of_setup_not_twisted Pr D L P nch HW F Cm X C₂ S i hg π hπ
  obtain ⟨g1, _, g3, g4, _, g5x, g6, bk, cont, ss, dec, eps, tie, shape, font, h2, cft⟩ := sp
  have hG2 := _root_.GlobalTheory.T.admG2_of_setup_jumps Pr D L P nch HW F Cm X C₂ S hJ.choose hJ.choose_spec i
  have hG5 := _root_.GlobalTheory.T.admG5_of_setup Pr D L P nch HW F Cm X C₂ S i hg π hπ
  obtain ⟨lc, lr⟩ := _root_.GlobalTheory.T.liftExponentColumn_and_dualPlaces Pr D L P nch HW F Cm X C₂ S i hTw hg hR hSp
  have hH0 := _root_.GlobalTheory.T.h0_column_length_bound_of_setup Pr D L P nch HW F Cm X C₂ S i hTw hg hR hSp π hπ
  obtain ⟨sub, acont, a56⟩ := _root_.GlobalTheory.T.ambSub_ambCont_h0_of_setup Pr D L P nch HW F Cm X C₂ S i hg π hπ
  obtain ⟨l51, l52, _⟩ := GlobalTheory.charpoly_span_and_hom_relations_of_admissible D i (X.r i) (X.ρ i) π g1
  obtain ⟨unr, dual, t2, aw, fil, h1f, a51, _⟩ := hPt π hπ
  have blk := (hRest i hg π hπ).block
  obtain ⟨M0, h0, jtb⟩ := hTB i hR π
  have tb9 : TruncatedSeriesCountingIdentities.admTB i (X.r i) π (X.cB i) :=
    GlobalTheory.T.localBlochKatoCondition_of_wachModules D HW F i (X.r i) (X.ρ i) π M0 h0 (X.cB i)
      (GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler Pr.bk Pr.tate Pr.euler D HW F Cm) (GlobalTheory.T.crystallineLatticeWachModuleExists_proof D HW F Cm) (GlobalTheory.crysOnCond_all D HW F) font jtb
  have tb : EmbeddingTypes.admTB i (X.r i) π (X.dc i) (X.cB i) := fun w hw _ C hC => tb9 w hw C hC
  have bka : LargeLevelLemmas.BlochKatoAnnihilators i := GlobalTheory.T.blochKatoAnnihilator_all_of_tateDuality_eulerChar Pr.bk Pr.tate Pr.euler D i
  have fin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i := GlobalTheory.T.tateFinitenessAll_of_localTateDuality Pr.tate D i
  exact ⟨g1, hG2, g3, g4, hG5, g5x, g6, a56, a51, l51, l52, ⟨bk, bka⟩, lc, lr, hH0, tb, unr, cont, ss, dec, eps, tie,
    shape, font, h2, fin, cft, blk, dual, t2, aw, fil, h1f, sub, acont, hType _⟩
end GlobalTheory.NLink
end
end
