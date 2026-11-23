module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle077
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle121
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle081
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle074
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VanishingGramTermsBoundParams
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2437
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2399
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardLatticesDiagonal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle123
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle113
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle069
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle064
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle116
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle068
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle122
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle124
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle514
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle497
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle066
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
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

@[expose] public section

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.base_chain_step_theta_lift_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j, j + 1 < D.R.m → Lift.IsIo (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).ν (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).fd (thetaKO (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).ω) (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).pt (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).It ((_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).CC (_root_.GlobalTheory.BaseChain.com_z W)) ((_root_.GlobalTheory.BaseChain.stageOfSpaceY W j).CC (_root_.GlobalTheory.BaseChain.com_z W)) (_root_.GlobalTheory.BaseChain.transitionBetweenSpacesY f j).io := by
  first | exact @_root_.GlobalTheory.BaseChain.stepY_isIo_alt | exact _root_.GlobalTheory.BaseChain.stepY_isIo_alt | (intros; apply _root_.GlobalTheory.BaseChain.stepY_isIo_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.base_chain_top_theta_functions_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ j (h : j + 2 * 0 + 2 = D.R.m), (∀ φ, IsThetaFunO (_root_.GlobalTheory.BaseChain.com_z W).ψ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).V (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).V ((_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt φ)) ∧ IsItW (_root_.GlobalTheory.BaseChain.com_z W).θ (_root_.GlobalTheory.BaseChain.stageOfSpaceY W (j + 1)).M (_root_.GlobalTheory.BaseChain.stageOfSpaceX W).M (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).ω (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).pt (_root_.GlobalTheory.BaseChain.transitionToSpaceX f j h).It := by
  first | exact @_root_.GlobalTheory.BaseChainTop.theta_and_it_alt | exact _root_.GlobalTheory.BaseChainTop.theta_and_it_alt | (intros; apply _root_.GlobalTheory.BaseChainTop.theta_and_it_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

theorem _root_.GlobalTheory.T.descent_data_step_exponents_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ (a : Fin n → ℕ) (ha : ∀ i, j + a i = (G i).s), ∃ κ : ℂ, κ ≠ 0 ∧ ∀ x : WO (Yc D j) (Yc D (j + 1)), (if IsHalf (∑ i, (G i).q.e) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x) ∧ IsIntM (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)) then omegaG (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))) * omegaQ ∅ (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B).r (fun _ => 1) 1 (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))) else 0) = κ * (if IsHalf (∑ i, (G i).q.e) x then ∏ i, ((G i).S.T (Fin D.R.t)).Phi j (a i) (ha i) ((ofSplit (G i).q).down ((G i).FY j (a i + 1) (by have := ha i; omega)) ((G i).FY (j + 1) (a i) (by have := ha i; omega)) x) else 0) := by
  first | exact @_root_.GlobalTheory.MovedDat.moved_datum_eq_prod_alt | exact _root_.GlobalTheory.MovedDat.moved_datum_eq_prod_alt | (intros; apply _root_.GlobalTheory.MovedDat.moved_datum_eq_prod_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.self_dual_frame_vacuum_step_alt : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ (j : ℕ), j < D.R.m → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : GlobalTheory.FinPl.Lat V) (β : GL (Fin V.rank) (Lev.EAf D)) (vac : WO (Yc D j) V → ℂ), IsSDFrame V β Λ 1 ∨ IsSDFrame V β Λ (D.host.g 0 * D.host.g 1) → IsVacO (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) V (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart M) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Λ vac → ∃ dG, _root_.GlobalTheory.Fam.IsDivisorGlobal W j M Λ β vac dG ∧ ∀ t, ∃ dQ, _root_.GlobalTheory.Fam.IsDivisorRational W t j M Λ β vac dQ ∧ ∀ v, IsStepVecOf (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ (Yc D j) V (cart ((_root_.GlobalTheory.Fam.pk_z W).MY j)) (cart M) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) Λ ((_root_.GlobalTheory.Fam.pk_z W).βY j) β ((_root_.GlobalTheory.Fam.pk_z W).datYt t j (_root_.GlobalTheory.Fam.complexLevelStructure W)) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).Q t) ((_root_.GlobalTheory.Fam.pk_z W).xiR t) vac v ↔ v = comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ dQ (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ dG vac) := by
  first | exact @_root_.GlobalTheory.FamSplit.split_datum_alt | exact _root_.GlobalTheory.FamSplit.split_datum_alt | (intros; apply _root_.GlobalTheory.FamSplit.split_datum_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.lift_s_eq_ci_smul_io : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ f : _root_.GlobalTheory.Fam.FamilyCharacter W u, f.RowOK → ∀ t j, j + 1 < D.R.m → ∀ (G : (f.t t).CC (j + 1)) P v, liftS ((f.t t).om j) (f.c.vol (j + 1)).μ (f.c.vol (j + 1)).𝓕 (G.1 v) ((f.t t).pt j P) = (f.t t).cI j • ((f.t t).io j G).1 (f.c.It j P v) := by
  first | exact @_root_.GlobalTheory.Fam.LiftVol.liftS_pt_eq_cI_smul_io | exact _root_.GlobalTheory.Fam.LiftVol.liftS_pt_eq_cI_smul_io | (intros; apply _root_.GlobalTheory.Fam.LiftVol.liftS_pt_eq_cI_smul_io <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.exists_pairwise_same_choices_at_geo : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word), _root_.GlobalTheory.Fam.PackageHypotheses W → ∀ g : GlobalTheory.Fam.Geo D, ∃ r : ∀ t, RowCh (_root_.GlobalTheory.Fam.pk_z W) (_root_.GlobalTheory.Fam.complexLevelStructure W) u g t, (∀ t, (r t).Is) ∧ ∀ t t', (r t).Same (r t') := by
  first | exact @_root_.GlobalTheory.Fam.LiftSide.exists_characters_is_and_same_of_pkHyp | exact _root_.GlobalTheory.Fam.LiftSide.exists_characters_is_and_same_of_pkHyp | (intros; apply _root_.GlobalTheory.Fam.LiftSide.exists_characters_is_and_same_of_pkHyp <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.dataNW_all_linked_good_members : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), GlobalTheory.Fc.RowE (Bl.IsGoodE p.s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) (fun _ D _ _ _ => GlobalTheory.Core.Deg.DataNW D) := by
  first | exact @_root_.GlobalTheory.Fam.MemberData.dataNW_of_isGoodE_of_isLinked | exact _root_.GlobalTheory.Fam.MemberData.dataNW_of_isGoodE_of_isLinked | (intros; apply _root_.GlobalTheory.Fam.MemberData.dataNW_of_isGoodE_of_isLinked <;> assumption)
end
end

section

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
namespace GlobalTheory.BadOnRec
end GlobalTheory.BadOnRec
namespace GlobalTheory.BadOnRec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
section General
open scoped TensorProduct
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : Full D} [inst : Algebra T.J.Q.c.F D.what₂.LL] {R : RealDat D A T.J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
  {h : LawsP T.toTop} {fw : FWTie T.J R κ v₀} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ}
  {ι : Fin D.R.m} {wL wF : WeightFamilies.Wt D ((ι : ℕ) + 1)} {nT : ℕ}
  {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
  {O : OnObj S P oc} {v : HeightOneSpectrum (𝓞 D.what₂.LL)} {i : Bs.J}
  {z : (Fin (O.nZ i) → D.what₂.LL) ≃ₗ[D.what₂.LL]
    D.what₂.LL ⊗[(recB h.toLawsCore).KO] (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {act : P → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι) → (recB h.toLawsCore).Cusp ((ι : ℕ) + 1) (κ ι)}
  {inc : P →* G}
  {ℓ : G → (LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((ι : ℕ) + 1)) T.Q.l)} {ph : ℂ}
  {y : (Fin (O.nX v i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (srcDim A ι (R.mu v) F.P0 F.ψ0⁻¹) → D.what₂.LL)}
end General
end GlobalTheory.BadOnRec
namespace GlobalTheory.BadOnRec
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] runAlgBad
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}
theorem bad_rec_alt (hR : p.PointConditions') (hm : More p) {Pm : ParameterChoice' D L} {Tp : ParamsT D L Pm} {r : TwoRuns p.T p.P.Gp}
    {c : OnConst} {O : Obj p c} (hrec : RecAt p Tp r O) {del : ℝ} (j : Fin D.R.m) (hbad : BadW p j del) :
    (1 - del) * O.d0 j ≤ ((S2 p).D : ℝ) := by
  obtain ⟨hC, hOk, -, -, hRk, -⟩ := _root_.GlobalTheory.T.links2_of_single_index_twisted _ _ _ _ _ _ _ _ _ _ p hR hm.1
  obtain ⟨hc, hinj, z, act, y, ht⟩ := hrec.1.tied
  have hU : (F2 p).P0 ≤ (mirIncl (R2 p)).range := fun g hg => by
    obtain ⟨u, -, e⟩ := (mem_base_iff hC.grp.levels g).1 hg
    exact ⟨u, e⟩
  obtain ⟨v₁, -⟩ := exists_place3 D.what₂.LL
  have hmem := mem_eig_iff (ht v₁ j).1 (ht v₁ j).2 hC.grp hU
  have hf := finrank_eq_of_bij _ (GlobalTheory.OnTies.toForms_bijective (hrec.1.ok.laws v₁).p (fw2 p) j (z j)) _ _ hmem
  have hd0 : O.d0 j = (finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j) : ℝ) := by
    unfold OnObj.d0
    exact congrArg (fun n : ℕ => (n : ℝ)) hf
  have hV : ∀ x ∈ GlobalTheory.CovTop.spType (R2 p) (F2 p) j, goodOp (R2 p) j x ∈ GlobalTheory.CovTop.spType (R2 p) (F2 p) j :=
    fun x hx g => by
      rw [← GlobalTheory.BigOn.goodOp_rho_comm hOk.irr j (g : p.P.Gp) x, hx g, map_smul]
  have hsplit := finrank_inf_range_add_inf_ker (goodOp (R2 p) j)
    (fun x => LinearMap.congr_fun (goodOp_idem hOk.irr j) x) _ hV
  have hD : (S2 p).D = finrank D.what₂.LL ((R2 p).WL (F2 p) false j) := (hRk.2 j).symm
  have hbad' : (finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j ⊓ LinearMap.ker (goodOp (R2 p) j) :
      Submodule D.what₂.LL _) : ℝ) ≤ del * finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j) := hbad
  have hs : (finrank D.what₂.LL ((R2 p).WL (F2 p) false j) : ℝ) +
      (finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j ⊓ LinearMap.ker (goodOp (R2 p) j) : Submodule D.what₂.LL _) : ℝ) =
      finrank D.what₂.LL (GlobalTheory.CovTop.spType (R2 p) (F2 p) j) := by
    exact_mod_cast hsplit
  rw [hd0, hD]
  nlinarith
end Point
end GlobalTheory.BadOnRec
namespace GlobalTheory.BigOn
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem badSt_of_badW_alt : _root_.GlobalTheory.ShareOn.BadWeightStatement → _root_.GlobalTheory.BigOn.BadPlacesStatement := by
  intro hB
  refine (hB.and GlobalTheory.T.badShareSize_bounds_along_family).imp fun Fm CH _ H => ?_
  obtain ⟨⟨x1, H1⟩, ⟨x2, H2⟩⟩ := H
  refine ⟨0, fun c _ _ => ⟨max x1 x2, fun x hx hle i p hR hm r O hrec => ?_⟩⟩
  have hb := H1 x hx ((le_max_left _ _).trans hle) i p hR hm r hrec.1.ok hrec.2
  have hq := (H2 x hx ((le_max_right _ _).trans hle) i).2.2.1
  intro j
  exact ⟨_, (Real.exp_pos _).le, hq, _root_.GlobalTheory.BadOnRec.bad_rec_alt hR hm hrec j (hb j)⟩
end GlobalTheory.BigOn
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.level_group_reference_tuple_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T), (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t = (q.w.D q.Z).what₂.mu0 → LevG ((_root_.GlobalTheory.Fam.packB_alt b).R.T.cols.forms u).clsP.toG 1 (levS _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) := by
  first | exact @_root_.GlobalTheory.Fam.BaseLevel.levG_base_of_bWit_alt | exact _root_.GlobalTheory.Fam.BaseLevel.levG_base_of_bWit_alt | (intros; apply _root_.GlobalTheory.Fam.BaseLevel.levG_base_of_bWit_alt <;> assumption)
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.level_character_twisted_class_alt : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (_root_.GlobalTheory.Fam.packB_alt b).P.T) (h : (_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t ≠ (q.w.D q.Z).what₂.mu0) (g : GA (q.w.D q.Z) (q.w.D q.Z).sp.X') (κ : ((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.U), GlobalTheory.Core.Rk.Top.HasMat g κ.1 → (levChi _ (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).βX (datXP (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)) (_root_.GlobalTheory.Fam.complexLevelStructure (_root_.GlobalTheory.Fam.packB_alt b)) t)) g = star ((((_root_.GlobalTheory.Fam.packB_alt b).R.T.tw.pt.cls u ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t) h).lev.chi κ : ℂˣ) : ℂ) := by
  first | exact @_root_.GlobalTheory.TopVal.LevTw.levChi_of_bWit_alt | exact _root_.GlobalTheory.TopVal.LevTw.levChi_of_bWit_alt | (intros; apply _root_.GlobalTheory.TopVal.LevTw.levChi_of_bWit_alt <;> assumption)
end
end

section



section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fc.TieOfLink
theorem tie_of_rpk_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) {x : TwIn O.ex} (y : _root_.GlobalTheory.Mem.R3.RealInAlt x b.R b.S) (r : _root_.GlobalTheory.Mem.R3.RecursiveInput y)
    (e : _root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y)
    (hpsi : PsiPPTie D (divisionPairOfAdelicFormsFaceColumnsData x).P0 (divisionPairOfAdelicFormsFaceColumnsData x).ψ0 (divisionPairOfAdelicFormsFaceColumnsData x).Ps (divisionPairOfAdelicFormsFaceColumnsData x).ψs (divisionPairOfAdelicFormsFaceColumnsData x).I.eG)
    (h3 : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree (_root_.GlobalTheory.Mem.R3.realisationOfInput y)) (hp : ∃ pins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput y), _root_.Formalism.IndefR.IndefiniteRealisationCompatible pins (_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r)) :
    Nonempty b.Comparison₂ := by
  let hasPins (z : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S) : Prop :=
    ∃ Rr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion z.B.Q,
      PsiPPTie D z.P.P0 z.P.ψ0 z.P.Ps z.P.ψs z.P.I.eG ∧
      _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree z.B.Q ∧
      ∃ pins : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation z.B.Q,
        _root_.Formalism.IndefR.IndefiniteRealisationCompatible pins Rr
  have hInput : hasPins (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y) :=
    ⟨_root_.GlobalTheory.Mem.R3.realisationRecursionOfInput r, hpsi, h3, hp⟩
  have hBundle : hasPins (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) := e.symm ▸ hInput
  obtain ⟨Rr, h⟩ := hBundle
  exact ⟨⟨Rr, h⟩⟩
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx}
theorem nonempty_tie_of_wit (q : WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c) (w : _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b)
    (hF0 : HEq (w.a.Zsc (zsOf q.x.what₂.r.z.R q.x.what₂.r.z.F)).F0 (F0K K.s (q.w.D q.Z)))
    (hp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput w.y.y))
    (hloc : _root_.Formalism.IndefR.principalLevelFrame.RowLocPinAlt b.R.T.n.gal.lp w.x.R.θ w.x.Y.PY (w.x.R.MY 0)
      (fun b => levS _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 b)))
      (fun b => Formalism.IndefR.Lev.levChi _ (w.x.R.βY 0) (w.x.R.dat0 (w.x.R.toRealDat.levR w.x.F.lv2 b))) (fun _ => w.x.R.e0) w.x.Y.eFT) :
    Nonempty b.Comparison₂ := by
  have hI := _root_.GlobalTheory.T.recursion_local_row_condition_alt _ _ _ _ _ _ _ _ q.O.ex w.x b.R b.S w.y.y w.y.r
  have h3 : _root_.Formalism.IndefR.IndefiniteRealisationNormalisationDegreeThree (_root_.GlobalTheory.Mem.R3.realisationOfInput w.y.y) := by
    obtain ⟨x, a, ax, y⟩ := w
    cases ax
    exact _root_.GlobalTheory.Mem.R3.realPins3_realTOf_alt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.what₂ a b.R b.S y.y hF0
  exact _root_.GlobalTheory.Fc.TieOfLink.tie_of_rpk_alt b w.y.y w.y.r w.y.eq hI.2.2 h3 ⟨hp, hI.1 hp hloc⟩
theorem hasTie_of_linked {hL : _root_.UpperTheory.Zero.LLC.RecTExists} (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL) (Q : V4.Slot) :
    RowE Q (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage p) fun _ => _root_.GlobalTheory.Fc.HasCompatibility := by
  have hH := EvP.of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev
  refine ((((((_root_.GlobalTheory.T.bWit_zsc_F0_heq_F0K_local_of_sc_eq hL p).and (_root_.GlobalTheory.T.bWit_C_eq_cf_of_sc_eq hL p)).and (_root_.GlobalTheory.T.bWit_Pg_eq_image_plMap_of_sc_eq hL p)).and (_root_.GlobalTheory.T.theta_level_conjugate_character_alt hL p)).and (_root_.GlobalTheory.T.local_level_character_pin_of_witness hL p)).and hH).mono
    fun κ K _ h β _ c b hl => ?_
  obtain ⟨⟨⟨⟨⟨h0, hc⟩, hg⟩, ht⟩, hl'⟩, hh⟩ := h
  obtain ⟨q, b', ⟨w⟩, e⟩ := hl
  have eO : (⟨β.D, β.O⟩ : Σ D : D7, Obj D) = ⟨q.w.D q.Z, q.O⟩ := congrArg (fun s => (⟨s.1, s.2.1⟩ : Σ D : D7, Obj D)) e
  have hsc : q.O.L.sc = K.s := by
    have := congrArg (fun s : Σ D : D7, Obj D => s.2.L.sc) eO
    exact this.symm.trans β.sc
  have hfd := (hh (q.w.st q.Z) q.x.isOver).2.2.1
  have hp : _root_.Formalism.IndefR.IndefiniteRealisationNormalisation (_root_.GlobalTheory.Mem.R3.realisationOfInput w.y.y) :=
    _root_.GlobalTheory.Mem.R3.realPins_realTOf_alt _ _ _ _ _ _ _ _ q.O.ex w.x b'.R b'.S w.y.y (hc q c b' w hsc) hfd (hg q c b' w hsc)
      (ht q c b' w hsc).1 (ht q c b' w hsc).2.1 (ht q c b' w hsc).2.2
  have h' : _root_.GlobalTheory.Fc.HasCompatibility _ _ c b' := _root_.GlobalTheory.Fc.TieOfLink.nonempty_tie_of_wit q b' w (h0 q c b' w hsc) hp (hl' q c b' w hsc)
  have tr : ∀ s : Σ (D : D7) (O : Obj D), _root_.GlobalTheory.Fc.BundleCondition D O c, s = ⟨q.w.D q.Z, q.O, b'⟩ → _root_.GlobalTheory.Fc.HasCompatibility s.1 s.2.1 c s.2.2 := by
    rintro s rfl; exact h'
  exact tr _ e
end GlobalTheory.Fc.TieOfLink
end
end
end

section



section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Fam.BundleLev
theorem lev_of_btw_alt {D : D7} {O : Obj D} {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition D O c) (x : R3.TwIn O.ex) (y : _root_.GlobalTheory.Mem.Top.Bl.TwistedBundle b x) :
    (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Pg = x.R.Pg ∧ ∀ t, (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).xiH t = x.R.toLevCh.xiH (x.Y.tupT ((_root_.GlobalTheory.Fam.packB_alt b).P.I.tup t)) := by
  have key : ∀ k : _root_.GlobalTheory.Mem.Top.Bl.RealPackage b.R b.S, k = _root_.GlobalTheory.Mem.Top.Bl.realPackageOfRealInput y.y →
      k.B.Q.Rl.toRealDat.Pg = x.R.Pg ∧ ∀ t, k.B.Q.Rl.toRealDat.xiH t = x.R.toLevCh.xiH (x.Y.tupT (k.P.I.tup t)) := by
    intro k hk
    subst hk
    refine ⟨rfl, fun t => ?_⟩
    exact (congrArg x.R.toLevCh.xiH (x.Y.tupT_tup t)).symm
  exact key (_root_.GlobalTheory.Mem.Top.Bl.realPackageOfBundle b) y.eq

theorem pg_eq_vGs_and_xiH_eq_xi_of_twArgs {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) (x : R3.TwIn q.O.ex)
    (a : R3.TwArgs q.O.ex q.x.what₂) (ax : HEq a.x x) :
    x.R.Pg = (q.B.primes q.w.px).vGs ∧
      ∀ μ, Formalism.IndefR.RecTie.Used0 (q.w.D q.Z) μ → x.R.toLevCh.xiH (x.Y.tupT μ) = q.w.I.xi μ := by
  have h := GlobalTheory.Mem.R3.twArgs_lev K _ _ _ q.w q.Z _ _ _ _ _ _ _ _ q.O.ex q.x.what₂ a
  have e : a.x = x := eq_of_heq ax
  subst e
  exact ⟨eq_of_heq h.2.1, fun μ hμ => eq_of_heq (h.2.2.1 μ hμ).2⟩

theorem levTrue_packB_of_bWit : ∀ {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : _root_.GlobalTheory.Fc.BundleCondition (q.w.D q.Z) q.O c), _root_.GlobalTheory.Mem.Top.Bl.BundleWitness q b → _root_.GlobalTheory.Fam.LevelCondition' (_root_.GlobalTheory.Fam.packB_alt b) := by
  intro hL p K q c b hw
  have h1 := _root_.GlobalTheory.Fam.BundleLev.lev_of_btw_alt b hw.x hw.y
  have h2 := _root_.GlobalTheory.Fam.BundleLev.pg_eq_vGs_and_xiH_eq_xi_of_twArgs q hw.x hw.a hw.ax
  have hPg : (_root_.GlobalTheory.Fam.pk_z (_root_.GlobalTheory.Fam.packB_alt b)).Pg = (q.B.primes q.w.px).vGs := h1.1.trans h2.1
  refine ⟨?_, ?_, ?_⟩
  · rw [hPg]
    exact ColTest.isTypePlaces_vGs q.w.I q.w.l q.Z q.w.ok
  · intro PP
    rw [hPg]
    exact Iff.rfl
  · intro t
    exact (h1.2 t).trans (h2.2 _ (_root_.GlobalTheory.MiS.Check.used_all_alt (_root_.GlobalTheory.Fam.packB_alt b) t))
end GlobalTheory.Fam.BundleLev
end
end
