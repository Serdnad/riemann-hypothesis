module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2039
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle970
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle391
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2855
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle201
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle010
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BaseSplitPrimeInLocalPlaces
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle075
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.PolarizationScalarImPos
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1989
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle024
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle086
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle084
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RallisBottomMinorMatching
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1936
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1879
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1872
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle346
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularisingTranslateCombination
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2860
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host
namespace GlobalTheory.DownLift.AtReal
theorem lift_splits_locally : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → ∀ (D : D7) (cf : CharFrame D)
    (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) j t, GlobalTheory.DownLift.TypeNZ X.R j t := by
  intro hP hH hX D cf nch tp X j t
  have hR : GlobalTheory.RawLift.RallisConv D := GlobalTheory.RawLift.Assembled.rallisConv_of_siegelWeil hP hX.sw D
  have hN : ∀ i t, GlobalTheory.DownLift.NonVan X.R i t := fun i t =>
    _root_.GlobalTheory.T.nonGalois_downLift_nonvanishing hP hX.dbl hX.udbl hX.hl hH D X.G X.Pl0 X.T X.A X.Ks X.R X.F X.given X.full i t
  exact ((GlobalTheory.T.liftInj_and_properties_of_rallis_of_nonVan hP hH D X.G X.Pl0 X.T X.A X.Ks X.R X.F X.given X.full hR hN).2 j t).1
end GlobalTheory.DownLift.AtReal
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host

theorem _root_.GlobalTheory.T.galoisRep_descends_at_real_places : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → _root_.GlobalTheory.NRows.GeometricGaloisRepCompatibility → ∀ (D : D7) (cf : CharFrame D) (nch : NChoice D) (tp : TupTied D cf nch) (X : GlobalTheory.NJoin.RealAt D cf nch tp) j t, GlobalTheory.DownLift.TypeNZ X.R j t := by
  first | exact @_root_.GlobalTheory.DownLift.AtReal.lift_splits_locally | exact _root_.GlobalTheory.DownLift.AtReal.lift_splits_locally | (intros; apply _root_.GlobalTheory.DownLift.AtReal.lift_splits_locally <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqStepK.PiLocalization₂
theorem quadratic_tower_step_base_stage : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → ∃ (B' WW₁ : HSp D) (Y : Tri T A B' WW₁),
        GlobalTheory.SqTower.IsStageC W i j p q Y ∧ GlobalTheory.SqStepK.IsStepB X Y := by
  intro hP _ _
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W S hψ hN i j p q A A' WW X hX
  obtain ⟨hp, hq, hrA, hrA', hnA, hnA', hnW, hXI⟩ := hX
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  have hrk := hXI.rank
  have hb1 : 2 * qq D j + 3 ≤ rankV D i j := by
    simp only [rankV, qq, Formalism.BasicNotions.Ranks.r]; omega
  have hb2 : 2 * pp D j ≤ rankV D (i + 1) (j + 1) := by
    simp only [rankV, pp, Formalism.BasicNotions.Ranks.r]; omega
  obtain ⟨B', Λ₁, ι, x, y, hs, hsig, hsd, hneg⟩ := GlobalTheory.T.hyperbolicPlane_split_selfDual_hermitian_complement D A' X.rA'.Λ q hXI.rigA'.1 hnA' (by omega) (by omega)
  obtain ⟨WW₁, ΛW, ι', x', y', hs', hsig', hsd', hneg'⟩ :=
    GlobalTheory.T.hyperbolicPlane_split_selfDual_hermitian_complement D WW X.rW.Λ (p + q) hXI.rigW.1 (by simpa only [add_assoc] using hnW) (by omega) (by omega)
  obtain ⟨rB, eB, hB⟩ := GlobalTheory.RigExists.exists_rig D B' Λ₁ hsig hsd
  obtain ⟨rW, eW, hW⟩ := GlobalTheory.RigExists.exists_rig D WW₁ ΛW hsig' hsd'
  obtain ⟨Y, e1, e2, e3, hY⟩ := _root_.GlobalTheory.T.exists_small_triple_of_weil_vacuum hP D T A A' WW B' WW₁ X W.ψ W.θ _ _ _ _ rB rW W.θ_is hXI hB hW
    (by have := hs.1; omega) (by have := hs'.1; omega)
  refine ⟨B', WW₁, Y, ⟨hp, by omega, hrA, by have := hs.1; omega, hnA, hneg, hneg', hY⟩, e1, ⟨ι, x, y, ?_⟩, ⟨ι', x', y', ?_⟩⟩
  · rw [e2, eB]; exact hs
  · rw [e3, eW]; exact hs'
end GlobalTheory.SqStepK.PiLocalization₂
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.quadratic_tower_step_stage_induction : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → ∃ (B' WW₁ : HSp D) (Y : Tri T A B' WW₁),
        GlobalTheory.SqTower.IsStageC W i j p q Y ∧ GlobalTheory.SqStepK.IsStepB X Y := by
  first | exact @_root_.GlobalTheory.SqStepK.PiLocalization₂.quadratic_tower_step_base_stage | exact _root_.GlobalTheory.SqStepK.PiLocalization₂.quadratic_tower_step_base_stage | (intros; apply _root_.GlobalTheory.SqStepK.PiLocalization₂.quadratic_tower_step_base_stage <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SqStepBig
theorem quadratic_tower_large_step_stage_dictionary : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW) (lam : T → ℂ) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), GlobalTheory.SqTower.IsStageC W i j p q X →
      Factor X W.ψ W.θ lam → GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank →
      ∃ Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank A'.rank, GlobalTheory.SqStepBig.Over X Γ ∧ Γ.p = p ∧ Γ.q = q ∧ Γ.IsGood Bs ∧
        ∀ R om om' Rf om₀ om₀' Rf₀ (c c₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j t) om om' R Rf →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j μ₀) om₀ om₀' R Rf₀ →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j t) om om' R Rf c →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j μ₀) om₀ om₀' R Rf₀ c₀ →
          ∃ k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))ˣ, c * lam μ₀ =
            (((GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * (c₀ * lam t) := by
  intro hP hK hM
  refine GlobalTheory.SqStepBig.gbig_two (_root_.GlobalTheory.T.exists_good_geometry_over_carried_frames hP) (_root_.GlobalTheory.T.pivot_reduction_divisibility hP hK hM) ?_
  intro D T Lc sc G μ₀ C x b q1 q2 W hψ i j p q A A' WW X lam t Bs hX hF hB
  obtain ⟨FA, FA', FW, Γ, hO, hp, hq, hg, hs⟩ := q1 W hψ i j p q A A' WW X lam t Bs hX hF hB
  refine ⟨Γ, hO, hp, hq, hg, ?_⟩
  intro R om om' Rf om₀ om₀' Rf₀ c c₀ m1 m0 k1 k0
  obtain ⟨h0, Pim, pp, pp', J, hsurj, hJ, hi, hI, hI', P', hP'0, hi'⟩ := id hF
  obtain ⟨P, k, H⟩ := q2 W hψ i j p q A A' WW X lam t Bs hX hF hB FA FA' FW Γ hO hp hq hg hs R P'
    (fun s _ h => hi' s h)
  have key : ∀ s, (s = t ∨ s = μ₀) → ∀ om om' Rf (c : ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' R Rf c →
      ((((GlobalTheory.SqStep.chs G i j s).ν k : ℂ) * lam s) • pp P) = c • pp' P' := by
    intro s hs' om om' Rf c m kc
    apply hJ s
    rw [map_smul, map_smul, mul_smul, ← hI, ← hI' s P' (hi' s)]
    funext h
    simp only [Pi.smul_apply, smul_eq_mul]
    exact H s hs' om om' Rf c m kc h
  have e1 := key t (Or.inl rfl) om om' Rf c m1 k1
  have e0 := key μ₀ (Or.inr rfl) om₀ om₀' Rf₀ c₀ m0 k0
  have e2 : ((((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) * c) • pp' P' =
      ((((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) * c₀) • pp' P' := by
    calc ((((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) * c) • pp' P'
        = (((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) • (c • pp' P') := mul_smul _ _ _
      _ = (((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) • ((((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) • pp P) := by
          rw [e1]
      _ = (((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) • ((((GlobalTheory.SqStep.chs G i j μ₀).ν k : ℂ) * lam μ₀) • pp P) :=
          smul_comm _ _ _
      _ = (((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) • (c₀ • pp' P') := by rw [e0]
      _ = ((((GlobalTheory.SqStep.chs G i j t).ν k : ℂ) * lam t) * c₀) • pp' P' := (mul_smul _ _ _).symm
  have e3 := sub_eq_zero.2 e2
  rw [← sub_smul] at e3
  have hz := (smul_eq_zero.1 e3).resolve_right hP'0
  have hn : (((GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  refine ⟨k, ?_⟩
  rw [Circle.coe_div, div_mul_eq_mul_div, eq_div_iff hn]
  linear_combination hz
end GlobalTheory.SqStepBig
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem _root_.GlobalTheory.T.tower_stage_fit_factor_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D)
    (X : Tri T A A' WW) (lam : T → ℂ) (t : T) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), GlobalTheory.SqTower.IsStageC W i j p q X →
      Factor X W.ψ W.θ lam → GlobalTheory.SqStepBig.Fit G W i j t μ₀ Bs A.rank A'.rank →
      ∃ Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig A.rank A'.rank, GlobalTheory.SqStepBig.Over X Γ ∧ Γ.p = p ∧ Γ.q = q ∧ Γ.IsGood Bs ∧
        ∀ R om om' Rf om₀ om₀' Rf₀ (c c₀ : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j t) om om' R Rf →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ (GlobalTheory.SqStep.chs G i j μ₀) om₀ om₀' R Rf₀ →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j t) om om' R Rf c →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsConst Bs Γ (GlobalTheory.SqStep.chs G i j μ₀) om₀ om₀' R Rf₀ c₀ →
          ∃ k : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E))ˣ, c * lam μ₀ =
            (((GlobalTheory.SqStep.chs G i j t).ν k / (GlobalTheory.SqStep.chs G i j μ₀).ν k : Circle) : ℂ) * (c₀ * lam t) := by
  first | exact @_root_.GlobalTheory.SqStepBig.quadratic_tower_large_step_stage_dictionary | exact _root_.GlobalTheory.SqStepBig.quadratic_tower_large_step_stage_dictionary | (intros; apply _root_.GlobalTheory.SqStepBig.quadratic_tower_large_step_stage_dictionary <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SqTop.BotNeFormula

theorem bottomTheta_ne_zero_of_innerProduct_formula : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → LNe → BotSmall → NormBig → TriEx → BotNe := by
  intro hPr hK hM hI hL hB hN hT
  have hLarge := _root_.GlobalTheory.T.theta_bottom_formula_large hPr hK hM hI hB
  have hSmall := _root_.GlobalTheory.T.theta_bottom_formula_small hPr hK hM hI hB
  have hMatch := _root_.GlobalTheory.T.rallis_bottom_minor_matching hPr hK hM hI hB
  have hBasis := _root_.GlobalTheory.T.exists_bottom_basis_change hPr
  unfold LNe at hL
  unfold BotSmall at hB
  unfold NormBig at hN
  unfold TriEx at hT
  unfold BotNe
  have hLevel := Model.gBig_and hL hB
  have hNorm := Model.gBig_and hN hT
  have hInputs := Model.gBig_and hLevel hNorm
  have hMatchBasis := Model.gBig_and hMatch hBasis
  have hSmallMatch := Model.gBig_and hSmall hMatchBasis
  have hFormulas := Model.gBig_and hLarge hSmallMatch
  have hAll := Model.gBig_and hInputs hFormulas
  apply BotConstPf.gBig_imp hAll
  intro D T Lc sc G μ₀ C x b hLc hData δ t0 Q P P' i j hbot
  have hLValues := hData.1.1.1
  have hTwistEmpty := hData.1.1.2.2.1
  have hNormFormula := hData.1.2.1
  have hTriangle := hData.1.2.2
  have hLargeFormula := hData.2.1
  have hSmallFormula := hData.2.2.1
  have hMinorMatch := hData.2.2.2.1
  have hBasisChange := hData.2.2.2.2
  have hmod : modT G μ₀ = SqNum.condE G.pl := by
    simp only [modT, hTwistEmpty, Finset.prod_empty, mul_one]
  rw [← hmod] at hbot
  obtain ⟨Λ, hΛ, hnz⟩ := (hLValues i j).1 μ₀
  have hh : (h0 D i j : ℤ) ≤ halfRank D i j :=
    Int.ofNat_le.mpr (squareBottomHalfRankSum_le_halfRank D i j)
  obtain ⟨Aa, hAa, hAn⟩ := hNormFormula δ t0 i j
  have hProd : (∏ s ∈ Icc (1 - (e0 D i j : ℤ)) (h0 D i j : ℤ), Λ s) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro s hs
    have ⟨hs₁, hs₂⟩ := Finset.mem_Icc.mp hs
    exact hnz s hs₁ (hs₂.trans hh)
  have hP : P.norm ≠ 0 := fun hz =>
    mul_ne_zero hAa hProd ((hAn μ₀ Q P P' Λ hbot hΛ).symm.trans (Complex.ofReal_eq_zero.mpr hz))
  obtain ⟨h, Tt, hne⟩ := exists_coord_ne_of_norm_ne P hP
  constructor
  · exact ⟨h, Tt, hne⟩
  obtain ⟨ψ, hψ⟩ := GlobalTheory.Ker.Model.exists_stdChar D
  obtain ⟨W, hWψ⟩ := GlobalTheory.GridWeil.exists_weil hPr.weilRepresentationUnitaryPair D T Lc μ₀ hLc sc G ψ hψ
  have hψW : IsStdChar D W.ψ (-1) := hWψ ▸ hψ
  obtain ⟨A, A', WW, X₀, c₀, hX₀, hc₀⟩ := hTriangle W hψW i j
  obtain ⟨X, ζ, hX, hβ, -, hc⟩ := hBasisChange W hψW i j A A' WW X₀ c₀ hX₀ hc₀
  obtain ⟨Ω, -, HA⟩ := hLargeFormula W hψW i j A A' WW X δ t0 hX hβ
  obtain ⟨Ω', -, HB⟩ := hSmallFormula W hψW i j A A' WW X δ t0 hX hβ
  obtain ⟨κ₀, -, HC⟩ := hMinorMatch W hψW i j A A' WW X (fun t => ζ t * c₀ t) hX hc
  obtain ⟨uA, -, -, -, HA⟩ := HA μ₀ Q P P' hbot
  obtain ⟨uB, -, -, -, HB⟩ := HB μ₀ Q P P' hbot
  have ea : P.a = A.rank := hbot.rank.1.trans hX.rank.symm
  have ea' : P'.a = A'.rank := hbot.rank.2.1.trans hX.rank'.symm
  have ed : P.d = WW.rank := by rw [hbot.rank.2.2.1, ← hX.is.rank, hX.rank, hX.rank']
  have hd : P'.d = P.d := hbot.rank.2.2.2
  have ed' : P'.d = WW.rank := hd.trans ed
  obtain ⟨M, -, -, HC⟩ := HC μ₀ Q δ t0 P P' hbot ea ea' ed ed'
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_finiteAdelicPoint_unitaryGroup_gramOne WW hX.stdW.1 h ed.symm
  have hg' := hg.cast hd
  by_contra hz
  push Not at hz
  apply hne
  have e := HA ea ed h g hg Tt
  rw [HC g Tt] at e
  have hs : ∑ T', (M Tt T' : ℂ) * X.I' W.ψ W.θ μ₀ (GlobalTheory.BotFormula.minorF ea' ed' T') g = 0 := by
    apply Finset.sum_eq_zero
    intro T' _
    rw [HB ea' ed' (hd ▸ h) g hg' T', hz, mul_zero, mul_zero]
  rw [hs, mul_zero, mul_zero] at e
  simpa using e
end GlobalTheory.SqTop.BotNeFormula
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.bottomTheta_nonvanishing : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → (∀ D, GlobalTheory.NormSum.Inp D) → LNe → BotSmall → NormBig → TriEx → BotNe := by
  exact _root_.GlobalTheory.SqTop.BotNeFormula.bottomTheta_ne_zero_of_innerProduct_formula
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.RegAt
theorem exists_regulariser_at_place : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → BigR fun {D} _ _ _ _ T _ _ _ _ _ R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ (B : Frames G)
  (ρ : RealMatch W), ρ.Over R → ∀ (t : T) (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ g g₁
  (P : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∃ v ∉ P, ∃ w : GA D (G.V (.grid i j)) →₀ ℂ, zdeg w ≠ 0 ∧
    IntegrableOn (translates w (kerSmall W Θ' g g₁)) (M.fd _) (M.ν _) ∧
    ∀ b ∈ w.support, b ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig (G.V (.grid i j)).gram v) := by
  intro _ hK _ _ _
  obtain ⟨CF0, hH⟩ := standing_all
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS => ?_⟩
  have hst := hx D large₂ he hx0 Γ Pl0 T A Ks R F hS
  intro G W _ B ρ _ t i j M hM Θ Θ' hΘ g g₁ P
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  obtain ⟨e, Bs, Γ', X, om, om', h, hTr, hv, hvP⟩ := squareTriple_avoid hL W t i j (hst G t) P M hM
  obtain ⟨z, Φ, a, C₀, hz, hΦ, hid, hsupp⟩ :=
    translates_kerSmall_le_theta_at hL W B ρ t i j M hM Θ Θ' hΘ g₁ e Bs Γ' X om om' h hTr hv
  have dec := (hK.1 D.host.F D.host.E D.sp.cm.sig Bs _ _ Γ' X om om' hTr).1
  obtain ⟨C, k, hC⟩ := (dec.2 Φ hΦ).1 0
  have hbd : ∀ u, ‖translates z (kerSmall W Θ' g g₁) u‖ ≤
      |C₀| * |C| * (2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁) ^ k := by
    intro u
    obtain ⟨γ, hγ, hle⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight _ g
    have e1 : translates z (kerSmall W Θ' g g₁) u = translates z (kerSmall W Θ' (γ * g) g₁) u := by
      simp only [translates, GlobalTheory.ZConvLeft.kerSmall_rat_left hL W B ρ t i j Θ Θ' hΘ g₁ γ hγ]
    rw [e1]
    have h1 := hC (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))
    rw [pow_zero, mul_one] at h1
    have h2 := GlobalTheory.BlockHeight.ht_blkU_le _ _ e h.JWW (γ * g) g₁
    have h3 : (0 : ℝ) ≤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) := NNReal.coe_nonneg _
    have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ≤
        2 * GlobalTheory.Grow.quotHeight _ g * GlobalTheory.Grow.height _ g₁ :=
      h2.trans (mul_le_mul_of_nonneg_right hle (GlobalTheory.Grow.height_pos _ _).le)
    calc _ ≤ C₀ * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ := hid _ _
      _ ≤ |C₀| * ‖GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.theta om' Φ (a u) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁))‖ :=
          mul_le_mul_of_nonneg_right (le_abs_self C₀) (norm_nonneg _)
      _ ≤ |C₀| * (|C| * (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU _ _ e h.JWW (γ * g, g₁)) : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg h3 k)))
            (abs_nonneg C₀)
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h3 h4 k) (mul_nonneg (abs_nonneg C₀) (abs_nonneg C))
  have hWl := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  haveI : IsFiniteMeasure ((M.ν (.grid i j)).restrict (M.fd (.grid i j))) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hWl.1 hWl.2).ne
  have hcont := GlobalTheory.SmallRoute.continuous_translates_kerSmall hL W B ρ t i j Θ Θ' hΘ g₁ z
  exact ⟨Bs.v₁, hvP, z, hz, Integrable.of_bound ((hcont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable) _
    (.of_forall hbd), hsupp⟩
end GlobalTheory.RegAt
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.exists_regulariser_local : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → BigR fun {D} _ _ _ _ T _ _ _ _ _ R sc => ∀ (G : GridData R.toLevCh sc) (W : G.Weil), W.Over R → ∀ (B : Frames G)
  (ρ : RealMatch W), ρ.Over R → ∀ (t : T) (i j : Fin D.R.m) (M : Vol G), M.Is t → ∀ Θ Θ', IsMatched B t ρ i j Θ Θ' → ∀ g g₁
  (P : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∃ v ∉ P, ∃ w : GA D (G.V (.grid i j)) →₀ ℂ, zdeg w ≠ 0 ∧
    IntegrableOn (translates w (kerSmall W Θ' g g₁)) (M.fd _) (M.ν _) ∧
    ∀ b ∈ w.support, b ∈ Set.range (GlobalTheory.AdelicU.emb D.sp.cm.sig (G.V (.grid i j)).gram v) := by
  first | exact @_root_.GlobalTheory.RegAt.exists_regulariser_at_place | exact _root_.GlobalTheory.RegAt.exists_regulariser_at_place | (intros; apply _root_.GlobalTheory.RegAt.exists_regulariser_at_place <;> assumption)
end
end

section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.BigNZ
open Formalism.IndefR GlobalTheory.RowTest GlobalTheory.RowClaim
theorem large_term_nonzero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → Big fun ch => ∀ i j t, ∃ M : Vol ch.G, M.Is t ∧ ∃ a τ τ' n Φ,
    (∀ w ∈ locPl ch.G t, depthAt ch.G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) ∧ HasFlip ch.S.B t ch.rm i j n Φ τ τ' ∧
    ∃ g g₁, ∫ u in M.fd _, kerBig ch.W (tensT ch.W a τ) g g₁ u ∂M.ν _ ≠ 0 := by
  intro hP hK hLM _ _ _
  obtain ⟨CF0, hH⟩ := standing
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := hH ε CF hCF
  refine ⟨x₀, fun D large₂ he hx0 Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc i j t => ?_⟩
  exact exists_integral_ne_zero hP.strongApproxSU hK hLM hS.core.lev ch.W ch.S.B ch.rm t i j
    (hx D large₂ he hx0 Γ Pl0 T A Ks R F hS ch hch hsc t)
end GlobalTheory.BigNZ
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem _root_.GlobalTheory.T.dominant_term_ne_zero : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → Big fun ch => ∀ i j t, ∃ M : Vol ch.G, M.Is t ∧ ∃ a τ τ' n Φ,
    (∀ w ∈ locPl ch.G t, depthAt ch.G w ≤ n w ∧ IsNatDatum (unifAt w) (n w) (Φ w)) ∧ HasFlip ch.S.B t ch.rm i j n Φ τ τ' ∧
    ∃ g g₁, ∫ u in M.fd _, kerBig ch.W (tensT ch.W a τ) g g₁ u ∂M.ν _ ≠ 0 := by
  first | exact @_root_.GlobalTheory.BigNZ.large_term_nonzero | exact _root_.GlobalTheory.BigNZ.large_term_nonzero | (intros; apply _root_.GlobalTheory.BigNZ.large_term_nonzero <;> assumption)
end
end
