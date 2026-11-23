module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle113
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle128
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle396
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle422
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle468
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle485
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle493
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle057
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle484
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle058
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle277
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle326
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle131
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationTwist
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle444
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnCharacterReductionEqExp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle130
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle115
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle365
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle126
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle565
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle110
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousOfCond
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIdAtOfSupp
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle034

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
noncomputable section
namespace GlobalTheory.LevProd
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word} {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
theorem exists_continuous_section_localHomProduct_twAt (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 2 ≤ B.R.m) :
    ∃ (n : ℕ) (ρ : Fin n → Fin J.r)
      (Ψ : (∀ m : Fin n, GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G (ρ m)).k) →
        GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)),
      Continuous Ψ ∧ (∀ x, Ψ x ∈ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J)) ∧
      ∀ g ∈ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J), Ψ (fun m => _root_.GlobalTheory.LevProd.localHomProduct J j hj g (ρ m)) = g := by
  classical
  let v : Fin J.r → GlobalTheory.FinPl.Pl (I.rec7 l Z) := fun i => (J.G i).q.v
  let f : Fin J.r → Fin J.r := fun i => (Finset.univ.filter (fun i' => v i' = v i)).min' ⟨i, by simp⟩
  have hf : ∀ i, v (f i) = v i := fun i =>
    (Finset.mem_filter.1 (Finset.min'_mem (Finset.univ.filter (fun i' => v i' = v i)) ⟨i, by simp⟩)).2
  have hf2 : ∀ i i', v i = v i' → f i = f i' := by
    intro i i' h
    simp only [f, h]
  let R := {i : Fin J.r // f i = i}
  let e : R ≃ Fin (Fintype.card R) := Fintype.equivFin R
  let ρ : Fin (Fintype.card R) → Fin J.r := fun m => (e.symm m).1
  have hinj : Function.Injective fun m => (J.G (ρ m)).q.v := by
    intro m m' h
    have h1 : f (ρ m) = f (ρ m') := hf2 _ _ h
    rw [(e.symm m).2, (e.symm m').2] at h1
    exact e.symm.injective (Subtype.ext h1)
  obtain ⟨Ψ, hc, hin, -, huniq⟩ := GlobalTheory.FixLev.exists_section ((I.rec7 l Z).sp.X j)
    (fun m => (J.G (ρ m)).k) (fun m => (J.G (ρ m)).q) hinj
    (fun _ => XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)
    (fun m => (J.G (ρ m)).FX j (by have := _root_.GlobalTheory.LevProd.step_index_le_s_alt J (ρ m) hj; omega))
  have hP : (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) fun p => ∃ m, p = (J.G (ρ m)).q.v) =
      GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J) := by
    congr 1
    funext p
    apply propext
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨ρ m, rfl⟩
    · rintro ⟨i, rfl⟩
      have hfix : f (f i) = f i := hf2 _ _ (hf i)
      refine ⟨e ⟨f i, hfix⟩, ?_⟩
      show v i = v (e.symm (e ⟨f i, hfix⟩)).1
      rw [e.symm_apply_apply]
      exact (hf i).symm
  refine ⟨Fintype.card R, ρ, Ψ, hc, fun x => hP.le (hin x), fun g hg => huniq g (hP.ge hg) _ fun m => ?_⟩
  exact (GlobalTheory.LevIdx.eq_locHom_iff _ _ _ g _).2 rfl
theorem isCompact_relax' (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (hR : J.Reads) (j : ℕ) (hj : j + 2 ≤ B.R.m) (α : J.Ch j) :
    IsCompact (_root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) := by
  classical
  have hU := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hW.tr.ok hW.tr.pins.some l Z u (W.P.I.tup t) J.Ch₀ J.A hR.is j (by omega) (J.ι j α)).1
  haveI hNn : (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J)).Normal := by
    unfold GlobalTheory.FinPl.grpAt GlobalTheory.FinPl.congGrp
    infer_instance
  obtain ⟨n, ρ, Ψ, hc, hin, huniq⟩ := _root_.GlobalTheory.LevProd.exists_continuous_section_localHomProduct_twAt J j hj
  let Kp : Set ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
    Set.pi Set.univ fun i => (KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) : Set _)
  have hKpc : IsCompact Kp := isCompact_univ_pi fun i => SplitFlip.isCompact_KO
  have hKpcl : IsClosed Kp := isClosed_set_pi fun i _ => Subgroup.isClosed_of_isOpen _ SplitFlip.isOpen_KO
  have hphi : Continuous (_root_.GlobalTheory.LevProd.localHomProduct J j hj) := continuous_pi fun i => GlobalTheory.LevIdx.continuous_locHom _ _ _
  let C : Set ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) :=
    (fun p : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) × ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) =>
      (_root_.GlobalTheory.LevProd.localHomProduct J j hj p.1)⁻¹ * p.2) '' ((J.A.U j (J.ι j α) : Set _) ×ˢ Kp)
  have hCc : IsCompact C := (hU.cpt.prod hKpc).image ((hphi.comp continuous_fst).inv.mul continuous_snd)
  let F : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) × ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k) →
      GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) := fun p => p.1 * Ψ (fun m => p.2 (ρ m))
  have hF : Continuous F :=
    continuous_fst.mul (hc.comp (continuous_pi fun m => (continuous_apply (ρ m)).comp continuous_snd))
  let S := ((J.A.U j (J.ι j α) : Set _) ×ˢ C) ∩ F ⁻¹' (_root_.GlobalTheory.LevProd.localHomProduct J j hj ⁻¹' Kp)
  have hSc : IsCompact S := (hU.cpt.prod hCc).inter_right ((hKpcl.preimage hphi).preimage hF)
  have heq : (_root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) = F '' S := by
    ext g
    constructor
    · intro hg
      have hg1 := Subgroup.mem_inf.1 (hg : g ∈ _root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α)
      have hsup : g ∈ ((J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J) : Subgroup _) : Set _) :=
        (Subgroup.mem_inf.1 hg1.1).1
      have hK : _root_.GlobalTheory.LevProd.localHomProduct J j hj g ∈ Kp := Subgroup.mem_comap.1 hg1.2
      rw [Subgroup.mul_normal] at hsup
      obtain ⟨x, hx, y, hy, rfl⟩ := hsup
      have hFy : F (x, _root_.GlobalTheory.LevProd.localHomProduct J j hj y) = x * y := by
        show x * Ψ (fun m => _root_.GlobalTheory.LevProd.localHomProduct J j hj y (ρ m)) = x * y
        rw [huniq y hy]
      refine ⟨(x, _root_.GlobalTheory.LevProd.localHomProduct J j hj y), ⟨⟨hx, ⟨(x, _root_.GlobalTheory.LevProd.localHomProduct J j hj (x * y)), ⟨hx, hK⟩, ?_⟩⟩, ?_⟩, hFy⟩
      · show (_root_.GlobalTheory.LevProd.localHomProduct J j hj x)⁻¹ * _root_.GlobalTheory.LevProd.localHomProduct J j hj (x * y) = _root_.GlobalTheory.LevProd.localHomProduct J j hj y
        rw [map_mul, inv_mul_cancel_left]
      · show _root_.GlobalTheory.LevProd.localHomProduct J j hj (F (x, _root_.GlobalTheory.LevProd.localHomProduct J j hj y)) ∈ Kp
        rw [hFy]
        exact hK
    · rintro ⟨⟨x, z⟩, ⟨⟨hx, -⟩, hK⟩, rfl⟩
      show F (x, z) ∈ _root_.GlobalTheory.LevProd.relaxedLevelSubgroup J j hj α
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, Subgroup.mem_comap.2 hK⟩
      · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right (hin _))
      · exact Subgroup.mul_mem _ (hU.le hx) (GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hin _))
  rw [heq]
  exact hSc.image hF
theorem isCompact_upperLevelSubgroup : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), IsCompact (_root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj
  unfold _root_.GlobalTheory.LevProd.upperLevelSubgroup
  split_ifs with h
  · exact _root_.GlobalTheory.LevProd.isCompact_relax' hW _ h.choose_spec.choose_spec.1 j hj _
  · rw [Subgroup.coe_bot]
    exact isCompact_singleton
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
namespace GlobalTheory.QPl.EpsSupp
end GlobalTheory.QPl.EpsSupp
open GlobalTheory.QPl.EpsSupp in
theorem GlobalTheory.Fam.famOf_eps_mem_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ (J : ∀ t, _root_.GlobalTheory.Fam.QuadraticExtensionData a t), (∀ t, (J t).Reads) → ∀ (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t)
    (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))) (hCh : ∀ t, (col t).Ch = (J t).Ch) (sc cT : ℕ → ℂ) t, ∀ j α, ∀ g ∈ (((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).ε j α).support,
    g ∈ GlobalTheory.FinPl.grpAt (Yc (I.rec7 l Z) j) (· ∈ ((_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t).pinTup sc cT).Q) ∧ g * a.g.b j ∈ GfC (Yc (I.rec7 l Z) j) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W _ u a ha _ J _ row col hCh sc cT t j α g hg
  have h1 := eps_mem_grpAt (_root_.GlobalTheory.Fam.familyOfRowColumnChoices a J row col hCh t) sc cT (fun i β => ((J t).E i).εL_zero β) j α g hg
  refine ⟨h1, mul_mem (GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ h1) ?_⟩
  rw [← (ha.tie row col).1.b j]
  exact ha.vis.b j
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LowJoin
open GlobalTheory.TwBridge GlobalTheory.StepData GlobalTheory.SplitWeil
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
section Place
variable {c : Comm (I.rec7 l Z)} {v : VCom c} {Bs : GlobalTheory.Fam.Base c} {PP : Pl (I.rec7 l Z).host.E}
end Place

theorem exists_quadratic_extension_readsLow : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.ReadsLow := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a _ ha hc t
  have hI := hW.tr.ok
  have hm := B.R.two_le_m
  obtain ⟨Ch₀, -, A, hA, hlast, hne, -, hstd, -⟩ := GlobalTheory.T.exists_tupleAdelicData_standardBasePoints I hI hW.tr.pins.some l Z u (W.P.I.tup t)
  have hχ : ∀ j (hj : j < B.R.m), ChrEq (D := I.rec7 l Z) (_root_.GlobalTheory.Fam.chrK_alt W t j) (I.C.mu0 ⟨j, hj⟩ * I.xi (W.P.I.tup t)) := fun j hj =>
    GlobalTheory.Mem.TupChar.chrEq_mul (hW.tr.chr ⟨j, hj⟩) (hW.tq.xi t)
  let e := ((_root_.GlobalTheory.Fam.pk_z W).Q t).equivFin
  let pl : Fin ((_root_.GlobalTheory.Fam.pk_z W).Q t).card → Pl (I.rec7 l Z).host.E := fun i => (e.symm i).1
  have mem : ∀ i, pl i ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t := fun i => (e.symm i).2
  have plinj : Function.Injective pl := Subtype.val_injective.comp e.symm.injective
  have plsurj : ∀ PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Q t, ∃ i, pl i = PP := fun PP h => ⟨e ⟨PP, h⟩, by simp [pl]⟩
  let P : Fin ((_root_.GlobalTheory.Fam.pk_z W).Q t).card → BadPr I (W.P.I.tup t) := fun i => ⟨pl i, Finset.mem_union_right _ ((hW.tq.Q t _).1 (mem i))⟩
  have hoff : ∀ i, (P i).1 ∉ (B.primes X).vGs := fun i => TC.Q_notMem_of_ok hI _ _ ((hW.tq.Q t _).1 (mem i))
  let G := fun i => a.Q (pl i) ⟨t, mem i⟩
  have hs : ∀ i, (G i).s + 1 + 1 = B.R.m := fun i => (G i).hs
  choose E hψ sg hE using fun i => exists_good hI hW.tr.tw (P i) (hoff i) (G i) rfl hc ha.pinX.std (_root_.GlobalTheory.Fam.chrK_alt W t) hχ
  let Rel : ∀ i j, Formalism.L2.Col.AutY B.fields B.R j → (E i).Ch j → Prop := fun i j γ y => ∀ d (h : j + d = (G i).s),
    IsGL (X := B.fields) (R := B.R) (k := (G i).k) ((G i).q.pr.comp (incA (I.rec7 l Z))) γ ((E i).rep j d h y)
  have hrel : ∀ i j d (h : j + d = (G i).s) γ y, IsGL (X := B.fields) (R := B.R) (k := (G i).k)
      ((G i).q.pr.comp (incA (I.rec7 l Z))) γ ((E i).rep j d h y) → Rel i j γ y := fun i j d h γ y h1 d' h' => by
    obtain rfl : d' = d := by omega
    exact h1
  have hd : ∀ i j, j ≤ B.R.m - 2 → ∃ d, j + d = (G i).s := fun i j hj => ⟨(G i).s - j, by have := hs i; omega⟩
  have hbij := exists_bij (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr hI.ch_ok hI.sel_ok (hI.sharp _) (hI.idx_ok (W.P.I.tup t))
    (GlobalTheory.T.twistIndexSet_eq_prod_localRepresentatives _ _ _ _ _ _ _ _ _ _ _ (hI.idx_ok _) (idxProd hI hW.tr.tw _)) (h_one hW.tr.tw _) P
    (fun i i' h => plinj (congrArg (fun Q : BadPr I (W.P.I.tup t) => Q.1) h)) hoff
    (fun Q hQ => (plsurj Q.1 ((hW.tq.Q t _).2 ((Finset.mem_union.1 Q.2).resolve_left hQ))).imp fun i h => Subtype.ext h)
    (fun i => (E i).Ch) Rel
    (fun i j hj b => by
      obtain ⟨d, h⟩ := hd i j hj
      obtain ⟨g, hg, -⟩ := GlobalTheory.T.existsUnique_completionMatrix_of_rationalTwistAut B.fields B.R (G i).k ((G i).q.pr.comp (incA (I.rec7 l Z))) j (d + 1)
        (by have := hs i; simp only [Formalism.L2.Col.cOf]; omega) ((I.idx _).h j b (P i))
      obtain ⟨y, -, rfl⟩ := ((E i).rep_bij j d h).surjOn (((hE i).rat j d h ⟨b⟩).ge ⟨b, hg⟩)
      exact ⟨y, hrel i j d h _ _ hg⟩)
    (fun i j hj h0 y => by
      obtain ⟨d, h⟩ := hd i j hj
      obtain ⟨b, hb⟩ := ((hE i).rat j d h h0).le (((E i).rep_bij j d h).mapsTo (Set.mem_univ y))
      exact ⟨b, hrel i j d h _ _ hb⟩)
    (fun i j hj γ γ' y y' h1 h2 => by
      obtain ⟨d, h⟩ := hd i j hj
      exact (isGL_unique (h1 d h) (h2 d h)).trans
        ⟨fun e => ((E i).rep_bij j d h).injOn (Set.mem_univ _) (Set.mem_univ _) e, fun e => e ▸ rfl⟩)
    (fun i j hj h0 ⟨y⟩ => by
      obtain ⟨d, h⟩ := hd i (j + 1) hj
      exact (hE i).next j d h h0 ⟨_, ((E i).rep_bij (j + 1) d h).mapsTo (Set.mem_univ y)⟩)
    (fun i j hj ⟨y⟩ => by
      obtain ⟨d, h⟩ := hd i (j + 1) hj
      obtain ⟨g, hg, -⟩ := Set.mem_iUnion₂.1
        (((E i).reps.bij j d h).mapsTo (((E i).rep_bij (j + 1) d h).mapsTo (Set.mem_univ y)))
      obtain ⟨y', -, -⟩ := ((E i).rep_bij j _ _).surjOn hg
      exact ⟨y'⟩)
  have hup : ∀ j, B.R.m ≤ j → ∀ i, Nonempty (Unique ((E i).Ch j)) := fun j hj i => by
    rcases hj.eq_or_lt with h | h
    · rw [← h, ← hs i]
      exact Fintype.card_eq_one_iff_nonempty_unique.1 (E i).one
    · exact (hE i).up j (by rw [hs i]; exact h)
  have key : ∀ j, ∃ (π : ∀ i, Ch₀ j → (E i).Ch j) (ι : (∀ i, (E i).Ch j) → Ch₀ j),
      (∀ i d (h : j + d = (G i).s) (hj : j < B.R.m) β, IsGL (X := B.fields) (R := B.R) (k := (G i).k)
        ((G i).q.pr.comp (incA (I.rec7 l Z))) ((I.idx (W.P.I.tup t)).h j ((A.b0 j β).get hj) (P i)) ((E i).rep j d h (π i β))) ∧
      (j + 1 ≠ B.R.m → (∀ y i, π i (ι y) = y i) ∧ (j ≤ B.R.m → Function.Surjective ι)) := by
    intro j
    rcases lt_trichotomy (j + 1) B.R.m with hj | hj | hj
    · obtain ⟨φ, h1, h2⟩ := hbij j (by omega)
      let f := Equiv.ofBijective _ (h1.comp (get_bij hA j hj))
      exact ⟨fun i β => f β i, f.symm, fun i d h _ β => h2 _ i d h, fun _ =>
        ⟨fun y i => congrFun (f.apply_symm_apply y) i, fun _ => f.symm.surjective⟩⟩
    · have h1 : ∀ i, Nonempty ((E i).Ch j) := fun i => by
        rw [show j = (G i).s + 1 by have := hs i; omega]
        exact ⟨((E i).cos_all 0 (zero_mem _)).choose⟩
      have h2 : Nonempty ((I.idx (W.P.I.tup t)).β j) := by
        rw [show j = B.R.m - 2 + 1 by omega]
        exact ⟨(hI.idx_ok _).last_uniq.choose⟩
      exact ⟨fun i _ => (h1 i).some, fun _ => (hne j ⟨Idx.of h2.some (by omega)⟩).some,
        fun i d h => by have := hs i; omega, fun h => absurd hj h⟩
    · have h1 := fun i => (hup j (by omega) i).some
      refine ⟨fun i _ => default, fun _ => (hne j ⟨Idx.top _ _ _ (by omega)⟩).some, fun i d h hj' => by omega,
        fun _ => ⟨fun y i => Subsingleton.elim _ _, fun hj' β => ⟨default, ?_⟩⟩⟩
      obtain rfl : j = B.R.m := by omega
      exact hlast.some.instSubsingleton.elim _ _
  choose π ι k1 k2 using key
  refine ⟨⟨Ch₀, A, _, pl, mem, E, P, hψ, sg, fun i j => π j i, ι⟩, hA, plinj, plsurj,
    fun j hj => (GlobalTheory.ChrEqUnique.chrEq_unique _).2.1 _ _ _ (hA.chr ⟨j, hj⟩) (hχ j hj), fun i => ?_, fun _ => rfl,
    fun i => (hE i).sign, fun i => (hE i).tw, fun i => (hE i).M, fun i j => k1 j i, hstd, hlast, fun j _ hj => (k2 j hj).1,
    fun j hj y y' h => funext fun i => ?_, (k2 0 (by omega)).2 (by omega), (k2 _ (by omega)).2 le_rfl,
    fun j hj hj' γ hγ => absurd ((k2 _ hj').2 hj γ) hγ⟩
  · exact res_of_tw hI (hE i).tw (hW.lev.2.2 t ▸ hW.pk.bot.hyp.2.2.2.1.lev.xiR t _ (mem i))
  · exact ((k2 j hj).1 y i).symm.trans ((congrArg (π j i) h).trans ((k2 j hj).1 y' i))
end GlobalTheory.LowJoin
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

theorem _root_.GlobalTheory.T.true_geometry_commutation_twist_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ n : Fin a.n, (∀ x : (I.rec7 l Z).host.E, (ofSplit (a.G n).q).pr x ∈ 𝒪[(a.G n).k] ↔ Formalism.L2.Col.IntAt (a.pl n).1 x) ∧ valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((Formalism.L2.Col.qOf (a.pl n).1 : ℕ) : (a.G n).k)) < valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) := by
  first | exact @_root_.GlobalTheory.LevelUnif.int_and_unif_alt | exact _root_.GlobalTheory.LevelUnif.int_and_unif_alt | (intros; apply _root_.GlobalTheory.LevelUnif.int_and_unif_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.true_geometry_final_index_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → ∀ (i : Fin a.n) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) (i0 : Fin 2) (h : ((I.rec7 l Z).host.g i0 : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal), (a.G i).q.v = v → (∀ r c : Fin ((I.rec7 l Z).sp.X 0).rank, ((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c ∈ 𝒪[(a.G i).k] ∧ (c ≤ r → valuation (a.G i).k (((mt ((I.rec7 l Z).sp.X 0) κ).map (a.G i).q.pr) r c - (1 : Matrix (Fin ((I.rec7 l Z).sp.X 0).rank) (Fin ((I.rec7 l Z).sp.X 0).rank) (a.G i).k) r c) < 1)) → Formalism.L2.Forms.InJ (I.rec7 l Z).R.k (I.rec7 l Z).R.t ((I.rec7 l Z).R.N 0) false (Formalism.L2.Forms.redM (I.rec7 l Z).host.F v ((_root_.GlobalTheory.MiTop.formsAtZero W u).gl.mat i0 v h 1 (Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) y.1))) := by
  first | exact @_root_.GlobalTheory.FamTrace.RedAt.inJ_red_alt | exact _root_.GlobalTheory.FamTrace.RedAt.inJ_red_alt | (intros; apply _root_.GlobalTheory.FamTrace.RedAt.inJ_red_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.true_geometry_lattice_forward_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → (y : GL _ _) ∈ (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.U → GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun _ => _root_.True) := by
  first | exact @_root_.GlobalTheory.FamTrace.LatFwd.lattice_forward_preserves_base_alt | exact _root_.GlobalTheory.FamTrace.LatFwd.lattice_forward_preserves_base_alt | (intros; apply _root_.GlobalTheory.FamTrace.LatFwd.lattice_forward_preserves_base_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.true_geometry_compact_level_property_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.True → ∀ κ ∈ GfC ((I.rec7 l Z).sp.X 0), ∀ y : Formalism.UG.UPts (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), GlobalTheory.AdForm.finM ((I.rec7 l Z).sp.X 0) (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) κ = y.1.1 → GlobalTheory.FinPl.Moves ((I.rec7 l Z).sp.X 0) κ (a.g.x 0).L (a.g.x 0).L (fun _ => _root_.True) → ∀ v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F), ((((I.rec7 l Z).mem u).A.T : ℕ) : 𝓞 (I.rec7 l Z).host.F) ∉ v.asIdeal → Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) v) (y : GL _ _) ∈ Formalism.UG.levelVL (Formalism.L2.Forms.sigD (I.rec7 l Z)) (Formalism.L2.Forms.gramN (I.rec7 l Z) 0 (Nat.zero_le _)) v (_root_.GlobalTheory.MiTop.formsAtZero W u).cls0.lev.Lb := by
  first | exact @_root_.GlobalTheory.FinPl.AwayLevel.mem_levelVL_base_alt | exact _root_.GlobalTheory.FinPl.AwayLevel.mem_levelVL_base_alt | (intros; apply _root_.GlobalTheory.FinPl.AwayLevel.mem_levelVL_base_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.true_geometry_row_column_entry_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col t (Ch₀ : ℕ → Type) (A : TwDat I l Z u (W.P.I.tup t) Ch₀) ι w c₀, PinChL (_root_.GlobalTheory.Fam.pk_z W) a.g (col t) c₀ A ι w → (∀ β, A.kb 0 β = TC.kStd X u (B.R.N 0)) → ∀ α, (∀ φ, _root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ ∈ ((a.fam row col).t t).Ram 0 ∧ ∀ y, ((a.fam row col).t t).rd 0 α (_root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ) y = (GlobalTheory.Core.Mi.chart0 (_root_.GlobalTheory.MiTop.formsAtZero W u)).rd W.Q.Rl.θ ((I.rec7 l Z).eMu u φ).1 y) ∧ ∀ ψ ∈ ((a.fam row col).t t).Ram 0, ∃ φ, ψ = _root_.GlobalTheory.MiTop.col0_alt (a.fam row col) t φ := by
  first | exact @_root_.GlobalTheory.Fam.zero_forms_alt | exact _root_.GlobalTheory.Fam.zero_forms_alt | (intros; apply _root_.GlobalTheory.Fam.zero_forms_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FamTraceChiColChar
open GlobalTheory.LocMod.PinEx GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum GlobalTheory.SplitWeil
theorem psi_uniformizer_eq_psi_zero_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ (i : Fin a.n) (j : Fin 2) (h : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).asIdeal) (z : 𝓞 (I.rec7 l Z).host.E) (w : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletionIntegers (I.rec7 l Z).host.F), (w : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletion (I.rec7 l Z).host.F) = (_root_.GlobalTheory.MiTop.formsAtZero W u).gl.phi j _ h ((z : (I.rec7 l Z).host.E) ⊗ₜ[(I.rec7 l Z).host.F] (1 : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletion (I.rec7 l Z).host.F)) → ((a.G i).S.ψ ((((a.G i).S.ϖ⁻¹ : (a.G i).kˣ) : (a.G i).k) * (ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E)) : ℂ) = (_root_.GlobalTheory.MiTop.formsAtZero W u).gl.psi0 j _ h (IsLocalRing.residue _ w) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hA u a ha _ row col _ i j h z w hw
  obtain ⟨hS⟩ := hA.tr.std
  have hR := (ha.tie row col).2
  have hPP : (a.pl i).1 ∈ (B.primes X).vGs := (hA.lev.2.1 _).1 (a.pl i).2
  have hid := (hR.idem i).1
  have hsq := GlobalTheory.LevelUnif.norm_notMem_sq (D := I.rec7 l Z) (hA.lev.1.1 _ (a.pl i).2)
  have hu := _root_.GlobalTheory.LevelUnif.valuation_uniformizer_sub_q_lt (D := I.rec7 l Z) _ _ _ hR hA.lev.1 i
  obtain ⟨s, hs⟩ := GlobalTheory.Mem.TypePrimes.Red.exists_hostXi0_inverse_integer (I.rec7 l Z).host
  have hsP : s ∉ (a.pl i).1.asIdeal := fun hm => by
    have h1 := (prO_lt (a.G i).q hid s).1 hm
    have h2 := xi_unit (a.G i).q (a.G i).unit (GlobalTheory.LocMod.Witness.xi_ne _)
    have h3 : (ofSplit (a.G i).q).xi * prO (a.G i).q s = 1 :=
      (((a.G i).q.pr.comp (incA (I.rec7 l Z))).map_mul _ _).symm.trans
        ((congrArg ((a.G i).q.pr.comp (incA (I.rec7 l Z))) hs).trans (map_one _))
    have h4 := congrArg (valuation (a.G i).k) h3
    rw [map_mul, h2, one_mul, map_one] at h4
    exact h1.ne h4
  obtain ⟨hp, b, hz, e⟩ := columnCharacter_reduction_eq_exp I hA.tr.ok (_root_.GlobalTheory.MiTop.formsAtZero W u).gl (hS u).gl.piG (hS u).gl.psi (a.pl i).1 hPP j h z w hw hs hsP
  exact (weil_unif_eq_exp (a.G i).q hid (a.G i).S.cond W.Q.stdChar (a.G i).char hp rfl hsq (a.G i).S.unif hu
    hs hz).trans e.symm
end GlobalTheory.FamTraceChiColChar
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
noncomputable section
namespace GlobalTheory.MiTop
end GlobalTheory.MiTop
theorem GlobalTheory.MiTop.tOf_fix_eR_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (hr : 1 ≤ D.R.rS) u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → ∀ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → ∀ c : AE D, Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) = Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) := by
  intro D L hT Gi Gl Kc Yd cX ex W hP hr u f B hB a₀ a hA c
  have hId : GlobalTheory.Core.Mi.IdE W.S.X := hP.bot.idE
  set v0 : Fin (D.sp.Y 0).rank → AE D := fun i => Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩
    (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))) with hv0
  have hv : (fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i)))) = c • v0 := rfl
  rw [hv]
  set x : GA D (D.sp.Y 0) := (iotaX W.S.X W.Q.instEq).symm (1, W.S.X.xu u) with hxdef
  set E : GA D (D.sp.Y 0) := embA B.d B.o (a₀ * a) with hEdef
  set b : GA D (D.sp.Y 0) := (show GA D (D.sp.Y 0) from f.g.b 0) with hbdef
  have hx : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) x) v0 = v0 := by
    refine GlobalTheory.MiTop.fixAux W.S.X W.Q.instEq hId {W.S.X.eR ⟨0, hr⟩} _ rfl x ?_
    have e : iotaX W.S.X W.Q.instEq x = (1, W.S.X.xu u) := (iotaX W.S.X W.Q.instEq).apply_symm_apply _
    rw [e]
    refine ⟨Subgroup.one_mem _, ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (W.S.X.xu_fix u ⟨0, hr⟩).1
  have hE : Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) E⁻¹) v0 = v0 := by
    refine GlobalTheory.MiTop.fixAux W.S.X W.Q.instEq hId (Formalism.L2.SG.PoincareInHH.PoincareSetting.fixSet W.S.X u) (W.S.X.eR ⟨0, hr⟩) (Or.inl (Or.inl ⟨⟨0, hr⟩, rfl⟩)) E⁻¹ ?_
    exact (B.tieH E⁻¹).1 ((embA B.d B.o).range.inv_mem ⟨a₀ * a, rfl⟩)
  have e : (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)⁻¹ = b⁻¹ * (E⁻¹ * x) := by
    show (x⁻¹ * E * b)⁻¹ = _
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  rw [e]
  show Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) b⁻¹ * (Formalism.L2.Theta.mt (D.sp.Y 0) E⁻¹ * Formalism.L2.Theta.mt (D.sp.Y 0) x)) (c • v0) = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul, hx, hE]
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.Glob
theorem open_and_linked_of_stronger_extension_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (N N' : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N' K B f T w Z Wt p0 t nch n xd c → Nonempty (N K B f T w Z Wt p0 t nch n xd c)) → (∀ H : ∀ 𝒜 : FamClass, RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜 → Prop, _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L H) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ) (fun Q L => Row Q L H)) ∧ (_root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) → _root_.GlobalTheory.Fc.S0.OpenParameterStatements (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ)) := by
  intro hL N N' S Γ hN
  obtain ⟨hB, hG, hLk, -⟩ := _root_.GlobalTheory.HeightCounting.Up.rows_of_stronger_nExt_alt hL N N' S Γ hN
  have m : ∀ H : ∀ 𝒜 : FamClass, RawSel _root_.GlobalTheory.Fc.BundleCondition 𝒜 → Prop, _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N S Γ) (fun Q L => Row Q L H) → _root_.GlobalTheory.Fc.RL.LinkedAt (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N' S Γ) (fun Q L => Row Q L H) :=
    fun H h => GlobalTheory.HeightCounting.Up.eventually_coreProperty_mono_fewerCores hB hG (fun _ _ hS h => GlobalTheory.HeightCounting.Up.row_mono_id hS hLk h) h
  exact ⟨m, fun o => ⟨m _ o.hPA, m _ o.hLamP, m _ o.hDivG, m _ o.hDcPtG, m _ o.selJ, m _ o.tie, m _ o.lab, m _ o.good, m _ o.geo, m _ o.mi, m _ o.kap, m _ o.df⟩⟩
end GlobalTheory.Glob
end
end
