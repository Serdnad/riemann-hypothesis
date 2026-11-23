module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridCoreNodeUnitReadingIntegralCongruent
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TowerEx
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumThetaJointlyContinuous
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle222
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousIsotropicSandwichMeanTranslation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle565
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitVacuumEntireFactorIsThetaMovedLattices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle568
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle140
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle346
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle133
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemicharacterSqEqOneOnHalfA
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
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle005
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle177
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle333
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate TensorProduct
open Matrix


theorem _root_.GlobalTheory.T.gridCoreNode_unitReading_integral_congruent : All fun {D} _ _ _ {G} W _ => ∀ i, i < D.R.m → ∀ e : AE D, IsIdemSum e G.pl.W0 →
    ∀ g : GA D (G.V (.core i)), ∀ a₁ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))), ∀ a₂ ∈ GlobalTheory.ChiGrid.hatMx (G.modul • GlobalTheory.ChiGrid.homLat (G.Λ (.core i)) (G.Λ (.core i))),
    e • ((1 : WO (G.V (.core i)) (G.V (.core i))) - a₁) = actO (G.V (.core i)) (G.V (.core i)) 1 g (e • (1 - a₂)) →
    ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)),
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • (((Lev.finE (G.V (.core i)) g)⁻¹).1 *ᵥ x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.Λ (.core i)) ∧
      toEAf D e • ((Lev.finE (G.V (.core i)) g).1 *ᵥ x - x) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (G.modul • G.Λ (.core i)) := by
  first | exact @GlobalTheory.UnitRead.unit_read | exact GlobalTheory.UnitRead.unit_read | (intros; apply GlobalTheory.UnitRead.unit_read <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.KerTame

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}

theorem om_heis_apply (hom : IsWeilDatumO ψ S T χS χT om) (p : GA D S × GA D T) (u : WO S T) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (x : WO S T) :
    om p (heisO ψ S T u f) x = ψ (symplOH S T x (actO S T p.1 p.2 u)) * om p f (x + actO S T p.1 p.2 u) := by
  obtain ⟨g, h⟩ := p
  rw [hom.om_heis g h u f hf]; rfl

theorem om_heis_bound (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ (C : ℝ) (A : ℕ), ∀ g h u x, ‖om (g, h) (heisO ψ S T u f) x‖ ≤ C * (quotHeight S g * quotHeight T h) ^ A := by
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.weilRepresentation_thetaFunction_sup_le_quotientHeight D ψ S T χS χT om hom f hf
  refine ⟨C, A, fun g h u x => ?_⟩
  rw [om_heis_apply hom (g, h) u hf x, norm_mul, hom.std.1.2.1, one_mul]
  exact hC g h _

theorem continuous_actO_gen {X : Type} [TopologicalSpace X] {g : X → GA D S} {h : X → GA D T} {u : X → WO S T}
    (hg : Continuous g) (hh : Continuous h) (hu : Continuous u) : Continuous fun t => actO S T (g t) (h t) (u t) := by
  have hmt : ∀ V : HSp D, Continuous (Formalism.L2.Theta.mt V) := fun V =>
    Units.continuous_val.comp continuous_subtype_val
  have hmti : ∀ V : HSp D, Continuous fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹ := fun V =>
    Units.continuous_coe_inv.comp continuous_subtype_val
  unfold actO
  exact (((hmt T).comp hh).matrix_mul hu).matrix_mul ((hmti S).comp hg)

theorem continuous_om_heis (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Continuous fun q : ((GA D S × GA D T) × WO S T) × WO S T => om q.1.1 (heisO ψ S T q.2 f) q.1.2 := by
  have hJ : Continuous fun p : (GA D S × GA D T) × WO S T => om p.1 f p.2 :=
    (@GlobalTheory.Unf.jointCont_all D) ψ S T χS χT om hom f hf
  have hA : Continuous fun q : ((GA D S × GA D T) × WO S T) × WO S T => actO S T q.1.1.1 q.1.1.2 q.2 := by
    exact continuous_actO_gen (continuous_fst.comp (continuous_fst.comp continuous_fst))
      (continuous_snd.comp (continuous_fst.comp continuous_fst)) continuous_snd
  have hB : Continuous fun q : ((GA D S × GA D T) × WO S T) × WO S T =>
      ((q.1.1, q.1.2 + actO S T q.1.1.1 q.1.1.2 q.2) : (GA D S × GA D T) × WO S T) :=
    (continuous_fst.comp continuous_fst).prodMk ((continuous_snd.comp continuous_fst).add hA)
  have hc : Continuous fun q : ((GA D S × GA D T) × WO S T) × WO S T =>
      ψ (symplOH S T q.1.2 (actO S T q.1.1.1 q.1.1.2 q.2)) * om q.1.1 f (q.1.2 + actO S T q.1.1.1 q.1.1.2 q.2) :=
    (hom.std.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH (continuous_snd.comp continuous_fst) hA)).mul (hJ.comp hB)
  exact hc.congr fun q => (om_heis_apply hom q.1.1 q.2 hf q.1.2).symm

end GlobalTheory.KerTame

namespace GlobalTheory.KerTame

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}

theorem om_superpos (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (p : GA D S × GA D T) (m' : Measure (WO S T)) [SFinite m'] (α : WO S T → ℂ) (hα : Integrable α m')
    (hI : IsThetaFunO ψ S T (fun x => ∫ u, α u * heisO ψ S T u f x ∂m')) (x : WO S T) :
    om p (fun x => ∫ u, α u * heisO ψ S T u f x ∂m') x = ∫ u, α u * om p (heisO ψ S T u f) x ∂m' := by
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : SecondCountableTopology (WO S T) := i3
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  have hφ : AEMeasurable (fun u : WO S T => (u, α u)) m' := measurable_id.aemeasurable.prodMk hα.aemeasurable
  set ν : Measure (WO S T × ℂ) := m'.map (fun u => (u, α u)) with hν
  obtain ⟨C1, hC1⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hom.std f hf
  obtain ⟨C2, hC2⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hom.std _ (hom.om_pres p f hf)
  set F : WO S T × ℂ → WO S T → ℂ := fun z => z.2 • heisO ψ S T z.1 f with hF
  have hFth : ∀ z, IsThetaFunO ψ S T (F z) := fun z =>
    GlobalTheory.WeilVacMove.isTheta_smul _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hom.std hf z.1)
  have hc1 : Continuous (Function.uncurry F) := by
    have e : Function.uncurry F = fun q : (WO S T × ℂ) × WO S T => q.1.2 * (ψ (symplOH S T q.2 q.1.1) * f (q.2 + q.1.1)) := by
      funext q; rfl
    rw [e]
    exact (continuous_snd.comp continuous_fst).mul ((hom.std.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_snd
      (continuous_fst.comp continuous_fst))).mul (hf.cont.comp (continuous_snd.add (continuous_fst.comp continuous_fst))))
  have hc2 : Continuous fun q : (WO S T × ℂ) × WO S T => om p (F q.1) q.2 := by
    have e : (fun q : (WO S T × ℂ) × WO S T => om p (F q.1) q.2) =
        fun q => q.1.2 * om p (heisO ψ S T q.1.1 f) q.2 := by
      funext q; simp only [hF, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact (continuous_snd.comp continuous_fst).mul ((continuous_om_heis hom hf).comp
      ((continuous_const.prodMk continuous_snd).prodMk (continuous_fst.comp continuous_fst)))
  have hβ : Integrable (fun z : WO S T × ℂ => ‖z.2‖ * max C1 C2) ν := by
    have hm : Continuous fun z : WO S T × ℂ => ‖z.2‖ * max C1 C2 := (continuous_norm.comp continuous_snd).mul continuous_const
    rw [hν, integrable_map_measure hm.measurable.aestronglyMeasurable hφ]
    exact hα.norm.mul_const _
  have hdom : ∀ z y, ‖F z y‖ ≤ ‖z.2‖ * max C1 C2 ∧ ‖om p (F z) y‖ ≤ ‖z.2‖ * max C1 C2 := by
    intro z y
    constructor
    · show ‖z.2 * (ψ (symplOH S T y z.1) * f (y + z.1))‖ ≤ _
      rw [norm_mul, norm_mul, hom.std.1.2.1, one_mul]
      exact mul_le_mul_of_nonneg_left ((hC1 _).trans (le_max_left _ _)) (norm_nonneg _)
    · simp only [hF, map_smul, Pi.smul_apply, smul_eq_mul]
      obtain ⟨g, h⟩ := p
      rw [norm_mul, om_heis_apply hom (g, h) z.1 hf y, norm_mul, hom.std.1.2.1, one_mul]
      exact mul_le_mul_of_nonneg_left ((hC2 _).trans (le_max_right _ _)) (norm_nonneg _)
  have hint : ∀ y, ∫ z, F z y ∂ν = ∫ u, α u * heisO ψ S T u f y ∂m' := by
    intro y
    rw [hν, integral_map hφ]
    · rfl
    · exact (hc1.comp (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable
  have hint2 : ∫ z, om p (F z) x ∂ν = ∫ u, α u * om p (heisO ψ S T u f) x ∂m' := by
    rw [hν, integral_map hφ]
    · simp only [hF, map_smul, Pi.smul_apply, smul_eq_mul]
    · exact (hc2.comp (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable
  have hI' : IsThetaFunO ψ S T (fun y => ∫ z, F z y ∂ν) := by
    simp only [hint]; exact hI
  have key := GlobalTheory.CommIntBdd.om_integral_comm_dom D ψ S T χS χT om hom (WO S T × ℂ) ν F p
    (fun z => ‖z.2‖ * max C1 C2) hFth hc1 hc2 hβ hdom hI' x
  have e : (fun w' => ∫ z, F z w' ∂ν) = fun y => ∫ u, α u * heisO ψ S T u f y ∂m' := funext hint
  rw [← hint2, ← key, e]

end GlobalTheory.KerTame

namespace GlobalTheory.KerTame

theorem kernel_tame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T),
    IsWeilDatumO ψ S T χS χT om → ∀ (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
    [BorelSpace Y] (m : Measure Y) [SFinite m] (c : Y → ℂ) (g : Y → GA D S) (h : Y → GA D T) (w : Y → WO S T),
    Measurable c → Continuous g → Continuous h → Continuous w →
    (∀ k : ℕ, Integrable (fun y => ‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ k) m) →
    (∀ f, IsThetaFunO ψ S T f → Integrable (fun y => c y * om (g y, h y) f (w y)) m) ∧
      Tame ψ S T fun f => ∫ y, c y * om (g y, h y) f (w y) ∂m := by
  intro D ψ S T χS χT om hom Y _ _ _ _ m _ c g h w hc hg hh hw hint
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : SecondCountableTopology (WO S T) := i3
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : FirstCountableTopology (WO S T) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  have hgh : Continuous fun y => ((g y, h y) : GA D S × GA D T) := hg.prodMk hh

  have hK : ∀ f, IsThetaFunO ψ S T f →
      Continuous fun q : Y × WO S T => om (g q.1, h q.1) (heisO ψ S T q.2 f) (w q.1) := fun f hf =>
    (continuous_om_heis hom hf).comp (((hgh.comp continuous_fst).prodMk (hw.comp continuous_fst)).prodMk continuous_snd)
  have hbd : ∀ f, IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ y u,
      ‖c y * om (g y, h y) (heisO ψ S T u f) (w y)‖ ≤ C * (‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ A) := by
    intro f hf
    obtain ⟨C, A, hC⟩ := om_heis_bound hom hf
    refine ⟨C, A, fun y u => ?_⟩
    rw [norm_mul]
    calc ‖c y‖ * ‖om (g y, h y) (heisO ψ S T u f) (w y)‖
        ≤ ‖c y‖ * (C * (quotHeight S (g y) * quotHeight T (h y)) ^ A) :=
          mul_le_mul_of_nonneg_left (hC _ _ _ _) (norm_nonneg _)
      _ = C * (‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ A) := by ring
  have hintH : ∀ f, IsThetaFunO ψ S T f → ∀ u,
      Integrable (fun y => c y * om (g y, h y) (heisO ψ S T u f) (w y)) m := by
    intro f hf u
    obtain ⟨C, A, hC⟩ := hbd f hf
    exact Integrable.mono' ((hint A).const_mul C)
      (hc.aestronglyMeasurable.mul ((hK f hf).comp (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable)
      (ae_of_all _ fun y => hC y u)
  have hzero : ∀ f : WO S T → ℂ, heisO ψ S T 0 f = f := by
    intro f; funext x; simp [heisO, symplOH, symplO, hO]
  have hintK : ∀ f, IsThetaFunO ψ S T f → Integrable (fun y => c y * om (g y, h y) f (w y)) m := by
    intro f hf
    simpa only [hzero] using hintH f hf 0
  refine ⟨hintK, ?_, ?_, ?_, ?_, ?_⟩
  · intro f f' hf hf'
    simp only [map_add (f := _), Pi.add_apply, mul_add]
    exact integral_add (hintK f hf) (hintK f' hf')
  · intro a f hf
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  · intro f hf
    obtain ⟨C, A, hC⟩ := hbd f hf
    refine continuous_of_dominated (bound := fun y => C * (‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ A))
      (fun u => (hintH f hf u).aestronglyMeasurable) (fun u => ae_of_all _ fun y => hC y u) ((hint A).const_mul C)
      (ae_of_all _ fun y => ?_)
    exact continuous_const.mul ((hK f hf).comp (continuous_const.prodMk continuous_id))
  · intro f hf
    obtain ⟨C, A, hC⟩ := hbd f hf
    exact ⟨∫ y, C * (‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ A) ∂m, fun u =>
      norm_integral_le_of_norm_le ((hint A).const_mul C) (ae_of_all _ fun y => hC y u)⟩
  · intro f hf m' _ α hα hI
    have e1 : ∀ y, om (g y, h y) (fun x => ∫ u, α u * heisO ψ S T u f x ∂m') (w y) =
        ∫ u, α u * om (g y, h y) (heisO ψ S T u f) (w y) ∂m' := fun y =>
      om_superpos hom hf (g y, h y) m' α hα hI (w y)
    simp only [e1]
    simp only [← integral_const_mul]
    rw [integral_integral_swap]
    · refine integral_congr_ae (ae_of_all _ fun u => ?_)
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only
      ring
    · obtain ⟨C, A, hC⟩ := hbd f hf
      refine Integrable.mono' (((hint A).const_mul C).mul_prod hα.norm) ?_ (ae_of_all _ fun q => ?_)
      · exact (hc.aestronglyMeasurable.comp_fst).mul (hα.aestronglyMeasurable.comp_snd.mul
          (hK f hf).measurable.aestronglyMeasurable)
      · calc ‖c q.1 * (α q.2 * om (g q.1, h q.1) (heisO ψ S T q.2 f) (w q.1))‖
            = ‖c q.1 * om (g q.1, h q.1) (heisO ψ S T q.2 f) (w q.1)‖ * ‖α q.2‖ := by
              simp only [norm_mul]; ring
          _ ≤ C * (‖c q.1‖ * (quotHeight S (g q.1) * quotHeight T (h q.1)) ^ A) * ‖α q.2‖ :=
              mul_le_mul_of_nonneg_right (hC _ _) (norm_nonneg _)

end GlobalTheory.KerTame
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.unitVacuumEntireFactor_isTheta_movedLattices : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, Formalism.MainNotions.StandardLatticesGL3.Crv D D.host.ccK δ → δ ≠ 0 → ∀ (Ls : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Formalism.MainNotions.StandardLatticesGL3.SD D Ls → Formalism.MainNotions.StandardLatticesGL3.SD D Lt → ∀ f : WO S T → ℂ, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (GlobalTheory.MovedDict.inV frS Ls) (GlobalTheory.MovedDict.inV frT Lt) f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, Differentiable ℂ Φ → (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → (fun Y => Φ (δ⁻¹ • Y)) ∈ Formalism.MainNotions.TaylorLogMetric.Th D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) Ls Lt := by
  first | exact @GlobalTheory.ThetaLawMoved.theta_of_vacuum_moved | exact GlobalTheory.ThetaLawMoved.theta_of_vacuum_moved | (intros; apply GlobalTheory.ThetaLawMoved.theta_of_vacuum_moved <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer

theorem _root_.GlobalTheory.T.schrodingerDeriv_relation_of_heisenbergDeriv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E),
      ξ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F (D.host.xi0 • S.gram⁻¹) →
    ∀ (κ : Type) [Fintype κ]
      (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F T.gramᵀ) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F JB)) κ),
      (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
        co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F x) =
          (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ L L' : ℝ →+ WO S T,
      Continuous L → (∀ t, (L t).map (finPart D) = 0) → Continuous L' → (∀ t, (L' t).map (finPart D) = 0) →
    ∀ c : ℂ, (fun w => deriv (fun t : ℝ => heisO ψ S T (L' t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) =
        c • (fun w => deriv (fun t : ℝ => heisO ψ S T (L t) (GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ Φ) w) 0) →
      ∀ x, deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L' t)) Φ x) 0 =
        c * deriv (fun t : ℝ => GlobalTheory.WeilM.schr ψ (co.e (L t)) Φ x) 0 := by
  first | exact @GlobalTheory.LineDerivTransfer.schr_deriv_of_heisO_deriv | exact GlobalTheory.LineDerivTransfer.schr_deriv_of_heisO_deriv | (intros; apply GlobalTheory.LineDerivTransfer.schr_deriv_of_heisO_deriv <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

open GlobalTheory.IdemSupport

variable {D : D7}


open Classical in
def cutPart (a : AE D) (V : HSp D) (g : GA D V) : GA D V :=
  if h : a * a = a ∧ cA D a = a then ⟨piece h.1 g.1, piece_mem _ _ h.1 h.2 g.2⟩ else g

theorem mt_cutPart {a : AE D} (h : a * a = a) (hc : cA D a = a) (V : HSp D) (g : GA D V) :
    Formalism.L2.Theta.mt V (cutPart a V g) = a • Formalism.L2.Theta.mt V g + (1 - a) • (1 : Matrix _ _ (AE D)) := by
  have e : cutPart a V g = ⟨piece h g.1, piece_mem _ _ h hc g.2⟩ := dif_pos ⟨h, hc⟩
  rw [e]
  rfl

end GlobalTheory.ExpansionInvariance

namespace GlobalTheory.ExpansionInvariance

open GlobalTheory.IdemSupport

variable {D : D7}

theorem idem_conj_sum {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) :
    (e + cA D e) * (e + cA D e) = e + cA D e ∧ cA D (e + cA D e) = e + cA D e := by
  have h1 : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, he]
  refine ⟨by linear_combination he + h1 + 2 * hc, ?_⟩
  rw [RingHom.map_add (f := _), GlobalTheory.SplitOnto.cA_cA, add_comm]

theorem idem_compl {f : AE D} (hf : f * f = f ∧ cA D f = f) : (1 - f) * (1 - f) = 1 - f ∧ cA D (1 - f) = 1 - f := by
  refine ⟨by linear_combination hf.1, ?_⟩
  rw [RingHom.map_sub, RingHom.map_one, hf.2]

theorem cutPart_mul {f : AE D} (hf : f * f = f ∧ cA D f = f) (V : HSp D) (g : GA D V) :
    g = cutPart f V g * cutPart (1 - f) V g := by
  have h2 := idem_compl hf
  refine GlobalTheory.IdemSupport.mt_inj V ?_
  rw [GlobalTheory.IdemSupport.mt_mul, mt_cutPart hf.1 hf.2, mt_cutPart h2.1 h2.2, sub_sub_cancel]
  exact (mix_split hf.1 rfl rfl).symm

theorem suppAt_cutPart {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (V : HSp D) (g : GA D V) :
    SuppAt e V (cutPart (e + cA D e) V g) := by
  have hf := idem_conj_sum he hc
  exact (supp_iff _ _).2 (smul_mix hf.1 (mt_cutPart hf.1 hf.2 V g))

theorem smul_mt_cutPart_compl {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (V : HSp D) (g : GA D V) :
    e • Formalism.L2.Theta.mt V (cutPart (1 - (e + cA D e)) V g) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  have hf := idem_conj_sum he hc
  have h2 := idem_compl hf
  rw [mt_cutPart h2.1 h2.2, sub_sub_cancel, smul_add, smul_smul, smul_smul]
  have k1 : e * (1 - (e + cA D e)) = 0 := by linear_combination -he - hc
  have k2 : e * (e + cA D e) = e := by linear_combination he + hc
  rw [k1, k2, zero_smul, zero_add]

end GlobalTheory.ExpansionInvariance

namespace GlobalTheory.ExpansionInvariance

variable {D : D7}

theorem actO_cutPart_compl {S T : HSp D} {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (g : GA D S) {z : WO S T}
    (hz : IsHalf e z) : actO S T (cutPart (1 - (e + cA D e)) S g)⁻¹ 1⁻¹ z = z := by
  have hz' : e • z = z := Matrix.ext fun i j => hz i j
  unfold actO
  rw [inv_inv, inv_one, GlobalTheory.IdemSupport.mt_one, Matrix.one_mul]
  conv_lhs => rw [← hz']
  rw [Matrix.smul_mul, ← Matrix.mul_smul, smul_mt_cutPart_compl he hc, Matrix.mul_smul, Matrix.mul_one, hz']

theorem halfInd_cutPart {S T : HSp D} {e : AE D} (he : e * e = e) (hc : e * cA D e = 0) (Λ : AddSubgroup (WO S T))
    (g : GA D S) (x : WO S T) :
    halfInd e Λ (actO S T (cutPart (e + cA D e) S g)⁻¹ 1⁻¹ x) = halfInd e Λ (actO S T g⁻¹ 1⁻¹ x) := by
  have hf := idem_conj_sum he hc
  have hg : g = cutPart (e + cA D e) S g * cutPart (1 - (e + cA D e)) S g := cutPart_mul hf S g
  have key : actO S T g⁻¹ 1⁻¹ x = actO S T (cutPart (1 - (e + cA D e)) S g)⁻¹ 1⁻¹
      (actO S T (cutPart (e + cA D e) S g)⁻¹ 1⁻¹ x) := by
    rw [← GlobalTheory.SplitLinear.actO_mul, ← mul_inv_rev, ← hg, inv_one, mul_one]
  rw [key]
  by_cases hy : IsHalf e (actO S T (cutPart (e + cA D e) S g)⁻¹ 1⁻¹ x)
  · rw [actO_cutPart_compl he hc g hy]
  · unfold halfInd
    rw [if_neg fun h => hy h.2, if_neg fun h => hy (GlobalTheory.ThetaMove.isHalf_of_act _ _ h.2)]

end GlobalTheory.ExpansionInvariance

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinDecomp

theorem mem_of_compl_smul {D : D7} {S T : HSp D} {Λ : AddSubgroup (WO S T)} {e : AE D}
    (he : ∀ u ∈ Λ, e • u ∈ Λ) (hc : ∀ u ∈ Λ, cA D e • u ∈ Λ) {y : WO S T} (hy : y ∈ Λ) :
    (1 - e - cA D e) • y ∈ Λ := by
  rw [sub_smul, sub_smul, one_smul]
  exact Λ.sub_mem (Λ.sub_mem hy (he y hy)) (hc y hy)

theorem half_mul_two (D : D7) : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
  norm_num

theorem symplO_split_two {D : D7} {S T : HSp D} {e : AE D} (h1 : e * e = e) (h2 : e * cA D e = 0)
    {x y z : WO S T} (hzx : (1 - e - cA D e) • x = 2 • z) :
    symplO S T x y = symplO S T (e • x) (cA D e • y) + symplO S T (cA D e • x) (e • y) +
      (symplO S T z ((1 - e - cA D e) • y) + symplO S T z ((1 - e - cA D e) • y)) := by
  have hsplit := GlobalTheory.AdForm.HalfASign.symplO_split (S := S) (T := T) h1 h2 x y
  rw [hzx, two_nsmul, GlobalTheory.PlaceModel.symplO_add_left S T] at hsplit
  exact hsplit

theorem symplO_smul_add_smul_add {D : D7} (S T : HSp D) (e : AE D) (x y : WO S T) :
    symplO S T (e • (x + y)) (cA D e • (x + y)) = symplO S T (e • x) (cA D e • x) + symplO S T (e • x) (cA D e • y) +
      (symplO S T (e • y) (cA D e • x) + symplO S T (e • y) (cA D e • y)) := by
  rw [smul_add, smul_add, GlobalTheory.PlaceModel.symplO_add_left S T, GlobalTheory.PlaceModel.symplO_add_right S T,
    GlobalTheory.PlaceModel.symplO_add_right S T]

theorem symplOH_lamE_arg {D : D7} {S T : HSp D} {e : AE D} (h1 : e * e = e) (h2 : e * cA D e = 0)
    {x y z : WO S T} (hzx : (1 - e - cA D e) • x = 2 • z) :
    symplOH S T (e • x) (cA D e • x) + symplOH S T (e • y) (cA D e • y) + symplOH S T x y =
      symplOH S T (e • (x + y)) (cA D e • (x + y)) +
        (symplO S T (cA D e • x) (e • y) + symplO S T z ((1 - e - cA D e) • y)) := by
  unfold symplOH
  rw [symplO_split_two h1 h2 hzx, symplO_smul_add_smul_add S T e x y,
    GlobalTheory.PlaceModel.symplO_skew S T (cA D e • x) (e • y)]
  have hh := half_mul_two D
  generalize algebraMap D.host.F (AF D.host.F) (1 / 2) = h at hh ⊢
  generalize symplO S T (e • x) (cA D e • x) = a1
  generalize symplO S T (e • y) (cA D e • y) = a2
  generalize symplO S T (e • x) (cA D e • y) = a3
  generalize symplO S T (cA D e • x) (e • y) = a4
  generalize symplO S T z ((1 - e - cA D e) • y) = a5
  linear_combination (a4 + a5) * hh

theorem lamE_add_of_lattice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D), e * e = e → e * cA D e = 0 → (∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) → (∀ u ∈ Λ, e • u ∈ Λ) → (∀ u ∈ Λ, cA D e • u ∈ Λ) → (∀ u ∈ Λ, ∃ z ∈ Λ, (1 - e - cA D e) • u = 2 • z) → ∀ x ∈ Λ, ∀ y ∈ Λ, lamE ψ S T e (x + y) = lamE ψ S T e x * lamE ψ S T e y * ψ (symplOH S T x y) := by
  intro D ψ S T Λ e h1 h2 hψ he hc hr x hx y hy
  obtain ⟨z, hz, hzx⟩ := hr x hx
  have key := symplOH_lamE_arg (y := y) h1 h2 hzx
  have k1 : ψ (symplO S T (cA D e • x) (e • y)) = 1 := hψ _ (hc x hx) _ (he y hy)
  have k2 : ψ (symplO S T z ((1 - e - cA D e) • y)) = 1 := hψ _ hz _ (mem_of_compl_smul he hc hy)
  have := congrArg ψ key
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, k1, k2,
    mul_one, mul_one] at this
  unfold lamE
  exact this.symm

end GlobalTheory.FinDecomp
end
