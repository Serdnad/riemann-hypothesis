module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle113
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle128
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle146
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle148
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle457
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle087
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTupleFreeValue
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle129
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle134
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle396
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle422
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle493
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle115
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle147
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MiStarOfMid
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle335
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricLevelsCharactersDoubleCosetsAgreeRation
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

theorem _root_.GlobalTheory.T.true_geometry_lattice_final_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t₀ (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀), J₀.Reads → ∀ (α₀ : J₀.Ch j) t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i, ¬ _root_.GlobalTheory.LevProd.quadraticTwistAtPlace J₀ (J.G i).q.v → ∀ g ∈ J₀.A.U j (J₀.ι j α₀), _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ KO (J.G i).k _ := by
  first | exact @_root_.GlobalTheory.LevProd.phi_mem_KO_of_not_twAt_alt | exact _root_.GlobalTheory.LevProd.phi_mem_KO_of_not_twAt_alt | (intros; apply _root_.GlobalTheory.LevProd.phi_mem_KO_of_not_twAt_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

theorem _root_.GlobalTheory.T.true_geometry_lattice_closed_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t₀ (J₀ : _root_.GlobalTheory.Fam.QuadraticExtensionData a t₀), J₀.Reads → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ i₀ i, (J₀.G i₀).q.v = (J.G i).q.v → ∀ g ∈ GfC _, _root_.GlobalTheory.LevProd.localHomProduct J₀ j hj g i₀ ∈ KO (J₀.G i₀).k _ → _root_.GlobalTheory.LevProd.localHomProduct J j hj g i ∈ KO (J.G i).k _ := by
  first | exact @_root_.GlobalTheory.LevProd.SamePlace.phi_mem_KO_alt | exact _root_.GlobalTheory.LevProd.SamePlace.phi_mem_KO_alt | (intros; apply _root_.GlobalTheory.LevProd.SamePlace.phi_mem_KO_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_quadratic_extension_reads_low_of_true : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ t, ∃ J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J.ReadsLow := by
  first | exact @_root_.GlobalTheory.LowJoin.exists_quadratic_extension_readsLow | exact _root_.GlobalTheory.LowJoin.exists_quadratic_extension_readsLow | (intros; apply _root_.GlobalTheory.LowJoin.exists_quadratic_extension_readsLow <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

theorem _root_.GlobalTheory.T.is_compact_upper_level_subgroup : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), IsCompact (_root_.GlobalTheory.LevProd.upperLevelSubgroup a j hj : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) := by
  first | exact @_root_.GlobalTheory.LevProd.isCompact_upperLevelSubgroup | exact _root_.GlobalTheory.LevProd.isCompact_upperLevelSubgroup | (intros; apply _root_.GlobalTheory.LevProd.isCompact_upperLevelSubgroup <;> assumption)
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
namespace GlobalTheory.LevProd
theorem H_le_KO_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) i, _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i ≤ KO (J.G i).k _ :=
  fun W hW u a ha hat j hj t J hJ α i => (_root_.GlobalTheory.LevProd.loc_level_alt W hW u a ha hat j hj t J hJ α i).1
end GlobalTheory.LevProd
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

theorem _root_.GlobalTheory.T.true_geometry_lattice_transport_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j) i, _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i ≤ KO (J.G i).k _ ∧ MeasurableSet (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i : Set (GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k)) ∧ (_root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i).relIndex (KO (J.G i).k _) ≠ 0 := by
  first | exact @_root_.GlobalTheory.LevProd.loc_level_alt | exact _root_.GlobalTheory.LevProd.loc_level_alt | (intros; apply _root_.GlobalTheory.LevProd.loc_level_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

theorem _root_.GlobalTheory.T.true_geometry_lattice_conjugate_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ (α : J.Ch j), ∀ n ∈ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.LevProd.quadraticTwistAtPlace J), (∀ i, _root_.GlobalTheory.LevProd.localHomProduct J j hj n i ∈ _root_.GlobalTheory.LevProd.levelSubgroupAtPlace J j hj α i) → n ∈ J.A.U j (J.ι j α) := by
  first | exact @_root_.GlobalTheory.LevProd.Bwd.mem_level_alt | exact _root_.GlobalTheory.LevProd.Bwd.mem_level_alt | (intros; apply _root_.GlobalTheory.LevProd.Bwd.mem_level_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open ValuativeRel

theorem _root_.GlobalTheory.T.true_geometry_line_choice_value : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u) (row : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u a.g t) (col : ∀ t : W.P.T, ColCh (D := I.rec7 l Z) u ((I.rec7 l Z).chTw u (W.P.I.tup t))), _root_.GlobalTheory.Fam.LocalGroupReading (a.fam row col) a.G a.pl → ∀ n : Fin a.n, valuation (a.G n).k ((((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) - ((Formalism.L2.Col.qOf (a.pl n).1 : ℕ) : (a.G n).k)) < valuation (a.G n).k (((a.G n).S.ϖ : (a.G n).kˣ) : (a.G n).k) := by
  first | exact @_root_.GlobalTheory.LevUnif.unif_of_gRead_alt | exact _root_.GlobalTheory.LevUnif.unif_of_gRead_alt | (intros; apply _root_.GlobalTheory.LevUnif.unif_of_gRead_alt <;> assumption)
end
end

section



section
noncomputable section
section LocalPart
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
open GlobalTheory.SymBridge (toLoc IsOrd yPos xPos IsCompl)
open GlobalTheory.PenVol GlobalTheory.TwBridge.Lev GlobalTheory.TwBridge.LevOrb
open scoped TensorProduct
namespace GlobalTheory.PenLoc
section Stab
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A : Type} [Fintype A] [DecidableEq A]
  {J : Subgroup (GL (A ⊕ Fin 0) k)}
end Stab
section Read
variable {k : Type} [Field k] {R : Type} [CommRing R] {Y : Type} [Fintype Y] [DecidableEq Y] {n : ℕ}
end Read
section Cong
variable {F E k : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
end Cong
section Seam
open Formalism.L2.Ker Formalism.MainNotions
variable {D : D7} {X : Fields} (s : Seam D X) {n : ℕ}
end Seam
end GlobalTheory.PenLoc
end LocalPart
section GlobalPart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel
namespace GlobalTheory.PenLoc
section Split
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end Split
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
  {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}

theorem bc_prV_of_mem_UPts (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (hTr : a.True) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (hJ : J.Reads) (i : Fin J.r) (j : ℕ)
    (e : j = (J.G i).s + 1) (hm : j ≤ B.R.m) (β : J.Ch₀ j) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (κ : GL (Fin (B.R.N j)) (EF (I.rec7 l Z))) (hg : κ.1 = finM _ (rankN (I.rec7 l Z) j hm) g)
    (hκ : κ ∈ Formalism.UG.UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) j hm) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) :
    Formalism.UG.bc (Formalism.UG.prV (E := (I.rec7 l Z).host.E) (J.G i).q.v) κ ∈ (J.A.K j hm β).lev.Uloc (J.G i).q.v ↔
      _root_.GlobalTheory.PenBridge.reductionHomAtLevel J j i e g ∈ GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J
        (box _ ((J.G i).ϖ ^ (J.E i).M)) ((J.E i).cos (cast (congrArg (J.E i).Ch e) (J.π i j β))) := by
  subst e
  obtain ⟨e', he', hF⟩ := (ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 ((J.G i).s + 1) le_rfl
  let e : XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1) ≃ Fin (B.R.N ((J.G i).s + 1)) :=
    e'.trans (finCongr (rankN (I.rec7 l Z) ((J.G i).s + 1) hm))
  have he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e := fun x => he' x
  obtain ⟨K, hKJ, hK, -⟩ := (_root_.GlobalTheory.Fam.QuadraticExtensionData.Reads.movedAt W hW u a ha t J hJ i).pen hm β e he
  have hKe : GlobalTheory.TwBridge.Lev.phi (E := B.fields.E) ((J.G i).q.pr.comp (incA (I.rec7 l Z))) ((Equiv.sumEmpty _ (Fin 0)).trans e)
      (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 ((J.G i).s + 1) β).1.1 (J.P i)) = K := by
    refine Units.ext (Matrix.ext ?_)
    rintro (x | x) (y | y)
    · exact (hK (e' x) y).trans (GlobalTheory.Fam.MovedJoin.frameβ_mul_std _ e' hF _ x y)
    · exact y.elim0
    · exact x.elim0
    · exact x.elim0
  have hv : Formalism.L2.Col.IsOver (J.G i).q.v (J.pl i) :=
    congrArg HeightOneSpectrum.asIdeal ((_root_.GlobalTheory.Fam.QJPlaces.places_under_alt W hW u a ha hTr t J hJ).2 i)
  have hrd : _root_.GlobalTheory.PenBridge.reductionHomAtLevel J _ i rfl g = locG ((J.G i).q.prF (J.G i).idem) ((Equiv.sumEmpty _ (Fin 0)).trans e) κ := by
    refine Units.ext (Matrix.ext ?_)
    rintro (x | x) (y | y)
    · refine (locHom_std (J.G i).q _ _ e' hF g x y).trans ?_
      refine ((J.G i).q.prF_toEAf (J.G i).idem _).symm.trans (congrArg _ ?_)
      exact (congrFun (congrFun hg (e x)) (e y)).symm
    · exact y.elim0
    · exact x.elim0
    · exact x.elim0
  rw [hrd]
  refine (uloc_iff hW.tr.ok hW.tr.pins.some J.A hJ.is (J.P i) (J.G i).q (J.pl i) (hJ.eq i) (J.G i).idem (J.G i).s
    ((J.E i).tw (J.hψ i) (J.sg i)) _ (fun _ => rfl) (hJ.tw i) hm β e he (hKe ▸ hKJ) (J.E i).M (hJ.M i) _ hv κ hκ).trans ?_
  exact Iff.of_eq (congrArg (fun c => locG ((J.G i).q.prF (J.G i).idem) ((Equiv.sumEmpty _ (Fin 0)).trans e) κ ∈
    GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J
      (box _ ((J.G i).ϖ ^ (J.E i).M)) c) (hJ.cos i β e he).symm)
end GlobalTheory.PenLoc

open scoped Pointwise in
theorem GlobalTheory.PenLoc.level_iff_relax_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∀ α : J.Ch j, ∃ c : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k, (∀ i, c i ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J) ∧ ∀ g, g ∈ J.A.U j (J.ι j α) ↔ g ∈ _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α ∧ ∀ i, c i * _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj g i * (c i)⁻¹ ∈ GlobalTheory.PenVol.cosStab (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J (GlobalTheory.StepData.box _ ((J.G i).ϖ ^ (J.E i).M)) ((J.E i).cos (cast (congrArg (J.E i).Ch (show j = (J.G i).s + 1 by exact _root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i)) (α i))) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α
  have hm : j ≤ B.R.m := by omega
  refine ⟨1, fun i => one_mem _, fun g => ?_⟩
  simp only [Pi.one_apply, one_mul, inv_one, mul_one]
  have key := fun i => _root_.GlobalTheory.PenLoc.bc_prV_of_mem_UPts hW ha hTr J hJ i j (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i) hm (J.ι j α)
  simp only [hJ.sec j hm α] at key
  have fwd := fun x (hx : x ∈ J.A.U j (J.ι j α)) i =>
    ((hJ.is.U j hm _ x).1 hx).2.elim fun κ hκ =>
      (key i x κ.1 hκ (((J.A.K j hm _).lev.U_eq _).1 κ.2).1).1 ((((J.A.K j hm _).lev.U_eq _).1 κ.2).2 _)
  constructor
  · intro hg
    exact ⟨(_root_.GlobalTheory.PenLev.mem_relax_iff' J j hj α g).2 ⟨Subgroup.mem_sup_left hg, ((hJ.is.U j hm _ g).1 hg).1,
      fun i => (J.E i).le _ _ _ (GlobalTheory.PenVol.cosStab_le _ _ _ (fwd g hg i))⟩, fwd g hg⟩
  · rintro ⟨hr, hH⟩
    obtain ⟨hs, hgf, -⟩ := (_root_.GlobalTheory.PenLev.mem_relax_iff' J j hj α g).1 hr
    have hN : (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.finitePlaceCondition J)).Normal := by
      unfold GlobalTheory.FinPl.grpAt GlobalTheory.FinPl.congGrp; exact MonoidHom.normal_ker _
    have : g ∈ ((J.A.U j (J.ι j α) : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) *
        (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)))) := by
      rw [← Subgroup.mul_normal]; exact hs
    obtain ⟨x, hx, n, hn, rfl⟩ := this
    refine mul_mem hx ?_
    have hnf : n ∈ GfC ((I.rec7 l Z).sp.X j) := (Subgroup.mul_mem_cancel_left _ ((hJ.is.U j hm _ x).1 hx).1).1 hgf
    obtain ⟨φ, hφ⟩ := GlobalTheory.FinPartIso.exists_finIso (I.rec7 l Z) _ _ (rankN (I.rec7 l Z) j hm)
    refine (hJ.is.U j hm _ n).2 ⟨hnf, ⟨(φ ⟨n, hnf⟩).1, ((J.A.K j hm _).lev.U_eq _).2 ⟨(φ ⟨n, hnf⟩).2, fun v => ?_⟩⟩, hφ ⟨n, hnf⟩⟩
    by_cases hv : _root_.GlobalTheory.PenBridge.finitePlaceCondition J v
    · obtain ⟨i, rfl⟩ := hv
      refine (key i n _ (hφ ⟨n, hnf⟩) (φ ⟨n, hnf⟩).2).2 ?_
      have h2 := hH i
      rw [map_mul, Pi.mul_apply] at h2
      exact (Subgroup.mul_mem_cancel_left _ (fwd x hx i)).1 h2
    · rw [GlobalTheory.PenLoc.bc_prV_eq_one _ hn _ _ (hφ ⟨n, hnf⟩) v hv]
      exact one_mem _
end GlobalPart
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
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
  {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
def localHomProductLastLevel (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 1 = B.R.m) :
    GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →*
      ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1)) (J.G i).k) :=
  Pi.monoidHom fun i => GlobalTheory.LevIdx.locHom (J.G i).q _ (_root_.GlobalTheory.PenBridge.frameAtLevel J j i (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj i))
theorem reductionHom_mem_KO_iff_localHomProduct (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 1 = B.R.m) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (i : Fin J.r) :
    _root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj g i ∈ KO (J.G i).k _ ↔ _root_.GlobalTheory.PenLev.localHomProductLastLevel J j hj g i ∈ KO (J.G i).k _ :=
  GlobalTheory.PenBridge.toSum0_mem_KO_iff _
theorem exists_continuous_section_localHomProduct_upper (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (j : ℕ) (hj : j + 1 = B.R.m) :
    ∃ (n : ℕ) (ρ : Fin n → Fin J.r)
      (Ψ : (∀ m : Fin n, GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G (ρ m)).s + 1)) (J.G (ρ m)).k) →
        GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)),
      Continuous Ψ ∧ (∀ x, Ψ x ∈ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.PenBridge.finitePlaceCondition J)) ∧
      ∀ g ∈ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.PenBridge.finitePlaceCondition J), Ψ (fun m => _root_.GlobalTheory.PenLev.localHomProductLastLevel J j hj g (ρ m)) = g := by
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
    (fun m => XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G (ρ m)).s + 1))
    (fun m => _root_.GlobalTheory.PenBridge.frameAtLevel J j (ρ m) (_root_.GlobalTheory.PenBridge.eq_s_succ_of_succ_eq_m J hj (ρ m)))
  have hP : (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) fun p => ∃ m, p = (J.G (ρ m)).q.v) =
      GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) := by
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
theorem isCompact_relax' (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (hR : J.Reads) (j : ℕ) (hj : j + 1 = B.R.m) (α : J.Ch j) :
    IsCompact (_root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) := by
  classical
  have hU := (GlobalTheory.T.chartLevels_reps_represent_unitaryDoubleCosets I hW.tr.ok hW.tr.pins.some l Z u (W.P.I.tup t) J.Ch₀ J.A hR.is j (by omega) (J.ι j α)).1
  haveI hNn : (GlobalTheory.FinPl.grpAt ((I.rec7 l Z).sp.X j) (_root_.GlobalTheory.PenBridge.finitePlaceCondition J)).Normal := by
    unfold GlobalTheory.FinPl.grpAt GlobalTheory.FinPl.congGrp
    infer_instance
  obtain ⟨n, ρ, Ψ, hc, hin, huniq⟩ := _root_.GlobalTheory.PenLev.exists_continuous_section_localHomProduct_upper J j hj
  let Kp : Set ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1)) (J.G i).k) :=
    Set.pi Set.univ fun i => (KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1)) : Set _)
  have hKpc : IsCompact Kp := isCompact_univ_pi fun i => SplitFlip.isCompact_KO
  have hKpcl : IsClosed Kp := isClosed_set_pi fun i _ => Subgroup.isClosed_of_isOpen _ SplitFlip.isOpen_KO
  have hphi : Continuous (_root_.GlobalTheory.PenLev.localHomProductLastLevel J j hj) := continuous_pi fun i => GlobalTheory.LevIdx.continuous_locHom _ _ _
  have hmemK : ∀ g, g ∈ (Subgroup.pi Set.univ fun i =>
      KO (J.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0)).comap
        (_root_.GlobalTheory.PenBridge.reductionHomAtLastLevel J j hj) ↔ _root_.GlobalTheory.PenLev.localHomProductLastLevel J j hj g ∈ Kp := by
    intro g
    simp only [Subgroup.mem_comap, Subgroup.mem_pi, Set.mem_univ, true_implies, Kp, Set.mem_pi, SetLike.mem_coe]
    exact forall_congr' fun i => _root_.GlobalTheory.PenLev.reductionHom_mem_KO_iff_localHomProduct J j hj g i
  let C : Set ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1)) (J.G i).k) :=
    (fun p : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) ×
        ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1)) (J.G i).k) =>
      (_root_.GlobalTheory.PenLev.localHomProductLastLevel J j hj p.1)⁻¹ * p.2) '' ((J.A.U j (J.ι j α) : Set _) ×ˢ Kp)
  have hCc : IsCompact C := (hU.cpt.prod hKpc).image ((hphi.comp continuous_fst).inv.mul continuous_snd)
  let F : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) ×
      ((i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1)) (J.G i).k) →
      GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) := fun p => p.1 * Ψ (fun m => p.2 (ρ m))
  have hF : Continuous F :=
    continuous_fst.mul (hc.comp (continuous_pi fun m => (continuous_apply (ρ m)).comp continuous_snd))
  let S := ((J.A.U j (J.ι j α) : Set _) ×ˢ C) ∩ F ⁻¹' (_root_.GlobalTheory.PenLev.localHomProductLastLevel J j hj ⁻¹' Kp)
  have hSc : IsCompact S := (hU.cpt.prod hCc).inter_right ((hKpcl.preimage hphi).preimage hF)
  have heq : (_root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) = F '' S := by
    ext g
    constructor
    · intro hg
      have hg1 := Subgroup.mem_inf.1 (hg : g ∈ _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α)
      have hsup : g ∈ ((J.A.U j (J.ι j α) ⊔ GlobalTheory.FinPl.grpAt _ (_root_.GlobalTheory.PenBridge.finitePlaceCondition J) : Subgroup _) : Set _) :=
        (Subgroup.mem_inf.1 hg1.1).1
      have hK : _root_.GlobalTheory.PenLev.localHomProductLastLevel J j hj g ∈ Kp := (hmemK g).1 hg1.2
      rw [Subgroup.mul_normal] at hsup
      obtain ⟨x, hx, y, hy, rfl⟩ := hsup
      have hFy : F (x, _root_.GlobalTheory.PenLev.localHomProductLastLevel J j hj y) = x * y := by
        show x * Ψ (fun m => _root_.GlobalTheory.PenLev.localHomProductLastLevel J j hj y (ρ m)) = x * y
        rw [huniq y hy]
      refine ⟨(x, _root_.GlobalTheory.PenLev.localHomProductLastLevel J j hj y), ⟨⟨hx, ⟨(x, _root_.GlobalTheory.PenLev.localHomProductLastLevel J j hj (x * y)), ⟨hx, hK⟩, ?_⟩⟩, ?_⟩, hFy⟩
      · show (_root_.GlobalTheory.PenLev.localHomProductLastLevel J j hj x)⁻¹ * _root_.GlobalTheory.PenLev.localHomProductLastLevel J j hj (x * y) = _root_.GlobalTheory.PenLev.localHomProductLastLevel J j hj y
        rw [map_mul, inv_mul_cancel_left]
      · show _root_.GlobalTheory.PenLev.localHomProductLastLevel J j hj (F (x, _root_.GlobalTheory.PenLev.localHomProductLastLevel J j hj y)) ∈ Kp
        rw [hFy]
        exact hK
    · rintro ⟨⟨x, z⟩, ⟨⟨hx, -⟩, hK⟩, rfl⟩
      show F (x, z) ∈ _root_.GlobalTheory.PenLev.relaxedLevelSubgroup J j hj α
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, ?_⟩, (hmemK _).2 hK⟩
      · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right (hin _))
      · exact Subgroup.mul_mem _ (hU.le hx) (GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hin _))
  rw [heq]
  exact hSc.image hF
theorem isCompact_baseLevelSubgroup : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ j (hj : j + 1 = B.R.m), IsCompact (_root_.GlobalTheory.PenLev.baseLevelSubgroup a j hj : Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hat j hj
  unfold _root_.GlobalTheory.PenLev.baseLevelSubgroup
  split_ifs with h
  · exact _root_.GlobalTheory.PenLev.isCompact_relax' hW _ h.choose_spec.choose_spec.1 j hj _
  · rw [Subgroup.coe_bot]
    exact isCompact_singleton
end GlobalTheory.PenLev
end
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.true_geometry_psi_value_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ (i : Fin a.n) (j : Fin 2) (h : ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).asIdeal) (z : 𝓞 (I.rec7 l Z).host.E) (w : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletionIntegers (I.rec7 l Z).host.F), (w : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletion (I.rec7 l Z).host.F) = (_root_.GlobalTheory.MiTop.formsAtZero W u).gl.phi j _ h ((z : (I.rec7 l Z).host.E) ⊗ₜ[(I.rec7 l Z).host.F] (1 : ((a.pl i).1.under (𝓞 (I.rec7 l Z).host.F)).adicCompletion (I.rec7 l Z).host.F)) → ((a.G i).S.ψ ((((a.G i).S.ϖ⁻¹ : (a.G i).kˣ) : (a.G i).k) * (ofSplit (a.G i).q).pr (z : (I.rec7 l Z).host.E)) : ℂ) = (_root_.GlobalTheory.MiTop.formsAtZero W u).gl.psi0 j _ h (IsLocalRing.residue _ w) := by
  first | exact @_root_.GlobalTheory.FamTraceChiColChar.psi_uniformizer_eq_psi_zero_alt | exact _root_.GlobalTheory.FamTraceChiColChar.psi_uniformizer_eq_psi_zero_alt | (intros; apply _root_.GlobalTheory.FamTraceChiColChar.psi_uniformizer_eq_psi_zero_alt <;> assumption)
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

theorem _root_.GlobalTheory.T.placed_bessel_translate_vector_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (hr : 1 ≤ D.R.rS) u (f : _root_.GlobalTheory.Fam.FamilyCharacter W u) (B : SBes W.S.X W.Q.instEq u W.Q.Rl.ψ (D.sp.X 0)), _root_.GlobalTheory.MiTop.PlacedConditions f B → ∀ a₀ a, _root_.GlobalTheory.MiTop.IsTranslate' f B a₀ a → ∀ c : AE D, Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (_root_.GlobalTheory.MiTop.translationElement f B a₀ a)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) = Matrix.mulVec (Formalism.L2.Theta.mt (D.sp.Y 0) (show GA D (D.sp.Y 0) from f.g.b 0)⁻¹) ((fun i => c * Formalism.L2.Theta.incA D (W.S.X.ιE (W.S.X.eR ⟨0, hr⟩ (Fin.cast (GlobalTheory.Core.Mi.rank_eq W.S.X W.Q.instEq) i))))) := by
  first | exact @_root_.GlobalTheory.MiTop.tOf_fix_eR_alt | exact _root_.GlobalTheory.MiTop.tOf_fix_eR_alt | (intros; apply _root_.GlobalTheory.MiTop.tOf_fix_eR_alt <;> assumption)
end
end
