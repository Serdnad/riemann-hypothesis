module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LiftNabStdMemLatN
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2497
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransporterMovesFrameReadsInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2458
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2495
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2498
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle059
import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle002

@[expose] public section

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.tameKernel_typePlaceThetaVector_latticeFixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ Q → IsTypeVec R i eg fg → IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) fg ∧ ∀ u ∈ latAll (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i), (IsHalf eQ u ∨ IsHalf (cA D eQ) u) → heisO R.ψ (Vc D i) (Wc D i) u fg = fg := by
  first | exact @GlobalTheory.KerTypeVec.typeVec_fixed | exact GlobalTheory.KerTypeVec.typeVec_fixed | (intros; apply GlobalTheory.KerTypeVec.typeVec_fixed <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.dualWeylTensorLift_equivariant : ∀ (K C : Type) [Field K] [Field C] (e0 : K →+* C) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (Φ : VV K lam →ₛₗ[e0] NablaT C n lamW), Shift lam lamW c → IsPhi e0 lam lamW Φ → ∀ (g : ι → GL (Fin n) K) (v : VV K lam), Φ (rhoK lam (invTrK g) v) = lamG C n lamW c (fun τ => Matrix.GeneralLinearGroup.map e0 (g τ)) (Φ v) := by
  first | exact @GlobalTheory.FrameRead.LiftEquiv.phi_equivariant | exact GlobalTheory.FrameRead.LiftEquiv.phi_equivariant | (intros; apply GlobalTheory.FrameRead.LiftEquiv.phi_equivariant <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.mem_weylLattice_add_iff_det_pow_mul : ∀ (R : Type) [CommRing R] (n k : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R), f ∈ weyl R n n le_rfl (fun a => ν a + k) ↔ ∃ g ∈ weyl R n n le_rfl ν, f = detPol R n ^ k * g := by
  first | exact @GlobalTheory.WeylShift.mem_weyl_add | exact GlobalTheory.WeylShift.mem_weyl_add | (intros; apply GlobalTheory.WeylShift.mem_weyl_add <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.unimodular_matrices_preserve_frame_lattices : ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : Frame l ι n), Function.Injective F.emb → (∀ τ, Antitone (res n (lamW τ))) → ∀ u : ι → GL (Fin n) (PadicAlgCl l), (∀ τ a b, (u τ).val a b ∈ Set.range F.emb ∧ (u τ)⁻¹.val a b ∈ Set.range F.emb) → ∀ z, (z ∈ F.latN lamW → lamG (PadicAlgCl l) n lamW c u z ∈ F.latN lamW) ∧ (z ∈ F.latD lamW → lamG (PadicAlgCl l) n lamW c u z ∈ F.latD lamW) := by
  first | exact @GlobalTheory.FrameRead.lamG_mem_lattices | exact GlobalTheory.FrameRead.lamG_mem_lattices | (intros; apply GlobalTheory.FrameRead.lamG_mem_lattices <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.variableMatrixDetPoly_pow_mul_mem_dualWeyl : ∀ (R : Type) [CommRing R] (n k : ℕ) (ν : Fin n → ℕ) (f : MvPolynomial (Fin n × Fin n) R), f ∈ dualWeyl R n n ν → detPol R n ^ k * f ∈ dualWeyl R n n fun a => ν a + k := by
  first | exact @GlobalTheory.FrameRead.detPol_pow_mul_mem_dualWeyl | exact GlobalTheory.FrameRead.detPol_pow_mul_mem_dualWeyl | (intros; apply GlobalTheory.FrameRead.detPol_pow_mul_mem_dualWeyl <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameRead

theorem lift_nabStd_mem_latN : ∀ (K : Type) [Field K] [NumberField K] (l : ℕ) [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l) (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) (F : Frame l ι n) (Φ : VV K lam →ₛₗ[e0] NablaT (PadicAlgCl l) n lamW), AtPlace w e0 → Function.Injective F.emb → (∀ x : K, ‖e0 x‖ ≤ 1 → e0 x ∈ Set.range F.emb) → Shift lam lamW c → IsPhi e0 lam lamW Φ → ∀ v : VV K lam, (v : Pol K ι n) ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (nabStd K lam) → Φ v ∈ F.latN lamW :=
  _root_.UpperTheory.Reformulated.B.Ga11.lift_nabStd_mem_latN

end GlobalTheory.FrameRead
end
end

section

open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase

theorem _root_.GlobalTheory.T.kernelTrace_algebraic_at_lowestTypes : TraceRat := by
  first | exact @GlobalTheory.TraceRatPf.traceRat | exact GlobalTheory.TraceRatPf.traceRat | (intros; apply GlobalTheory.TraceRatPf.traceRat <;> assumption)
end

section

open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase

theorem _root_.GlobalTheory.T.ownPrime_isUnit_at_place : OwnUnit := by
  first | exact @GlobalTheory.BigOn.Exp.SerBase.ownUnit | exact GlobalTheory.BigOn.Exp.SerBase.ownUnit | (intros; apply GlobalTheory.BigOn.Exp.SerBase.ownUnit <;> assumption)
end

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.transporter_movesAt_of_movesAt_open_set : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' k'' : (uAt r v i).Comp) (a c : GL (Fin D.R.r) D.host.E) (hma : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a) (hmc : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k'') c) (W : Set (Frame ((uAt r v i).X k).Ψ D.R.r)), IsOpen W → W.Nonempty → W ⊆ ((uAt r v i).X k).dom → (∀ (z : Frame ((uAt r v i).X k).Ψ D.R.r) (hz : z ∈ ((uAt r v i).X k).dom), z ∈ W → MovesAt p r i v γ k k' a hma z hz ∧ MovesAt p r i v γ k k'' c hmc z hz) → ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom), MovesAt p r i v γ k k'' c hmc x hx → MovesAt p r i v γ k k' a hma x hx := by
  first | exact @GlobalTheory.ShareOn.movesAt_of_movesAt_open | exact GlobalTheory.ShareOn.movesAt_of_movesAt_open | (intros; apply GlobalTheory.ShareOn.movesAt_of_movesAt_open <;> assumption)
end

section

open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn

theorem _root_.GlobalTheory.T.exists_transporter_moves_frame_reads_inverse : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)), ∃ ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k, ∀ (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k : (uAt r v i).Comp) (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom), ∃ (k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E) (hm : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a), ReadsInv p r i v ψ γ k k' a ∧ MovesAt p r i v γ k k' a hm x hx := by
  first | exact @GlobalTheory.ShareOn.exists_movesAt_readsInv | exact GlobalTheory.ShareOn.exists_movesAt_readsInv | (intros; apply GlobalTheory.ShareOn.exists_movesAt_readsInv <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap


theorem _root_.GlobalTheory.T.lift_vector_three_step_decomposition : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa St : Finset (Pl D.host.E)), Disjoint Sa St → Sa ∪ St = R.Q t → ∀ (eg ea et : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → IsIdemSum et St → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ∃ gA : WO (Vc D i) (Wc D i) → ℂ, ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) gA ∧ ThAt R i (cA D et) gA (adjDat R i St (R.xiR t) (cA D et)) (R.vP i t) := by
  first | exact @GlobalTheory.LiftThreeStep.thetaVector_three_step_decomposition | exact GlobalTheory.LiftThreeStep.thetaVector_three_step_decomposition | (intros; apply GlobalTheory.LiftThreeStep.thetaVector_three_step_decomposition <;> assumption)
end
end

section

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct


attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap


theorem _root_.GlobalTheory.T.theta_half_moves_under_translate_other_places : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa St : Finset (Pl D.host.E)), Sa ⊆ R.Q t → St ⊆ R.Q t → Disjoint Sa St → ∀ (eg ea et : AE D) (fg b Φ f : WO (Vc D i) (Wc D i) → ℂ) (z : GA D (Vc D i)) (c : ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → IsIdemSum et St → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) b → SuppAt ea (Vc D i) z → c ≠ 0 → ThAt R i (cA D et) b Φ f → ThAt R i (cA D et) (c • R.ωP i t (z⁻¹, 1) b) Φ (c • R.ωP i t (z⁻¹, 1) f) := by
  first | exact @GlobalTheory.ThetaBaseMove.thAt_move | exact GlobalTheory.ThetaBaseMove.thAt_move | (intros; apply GlobalTheory.ThetaBaseMove.thAt_move <;> assumption)
end
end
