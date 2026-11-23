module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle053
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle563
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2215
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle482
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle380
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle250
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SecOfDm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.FockAnisoFree
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2000
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2083
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2246
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle093
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle090
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

@[expose] public section

section

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn
namespace GlobalTheory.PrimBase
theorem base_of_ties_alt : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → GlobalTheory.LiftRows.Given R.toRealDat F.lv2 ∧ GoodStable A3.A.X ∧ GlobalTheory.CuspMult.CuspDecomp D ∧ GlobalTheory.Chain.LiftInteg D ∧ GlobalTheory.TrCopy.TRLev R.toRealDat F.lv2 R.SF ∧ GlobalTheory.LiftRows.UpInj R.toRealDat ∧ GlobalTheory.LiftRows.UpInjW R.toRealDat := by
  intro hP D G _ _ Pl0 I0 T0 A3 Ks _ _ _ R F hT hM
  have hGiv : GlobalTheory.LiftRows.Given R.toRealDat F.lv2 :=
    GlobalTheory.GivenOfTop.given_of_top R F hT.ok hT.char hT.ex hT.host hT.params hT.ccK hT.guard hT.types
  have hStab : GoodStable A3.A.X := GlobalTheory.T.goodCharacters_dual_stable_of_thetaLift_scalars hP.q12 R.toRealDat F.lv2 hGiv
  have hCD : GlobalTheory.CuspMult.CuspDecomp D := GlobalTheory.CuspDec.cuspDecomp hP.q3 hP.q2 D
  have hLI : GlobalTheory.Chain.LiftInteg D := GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hP.q2 D
  have hCore := GlobalTheory.CoreOfWeak.core_of_weak R F hT.char hT.ex
  have hSch : GlobalTheory.Hk3.SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hP.q2 R.toRealDat
  have hTR : GlobalTheory.TrCopy.TRLev R.toRealDat F.lv2 R.SF :=
    GlobalTheory.T.transfer_eigensystem_parts_three_levels_of_mult_eq R.toRealDat F.lv2 1 hT.ok.ok2 hCore.1 hSch hStab hCD hM R.SF hCore.2.1
  have hFix : ∀ t P, GlobalTheory.Hk3.Good R.toRealDat t P → Formalism.DivisionValues.conjPl P = P → GlobalTheory.Hk3.FixAll R.toRealDat t P :=
    GlobalTheory.FixAllGood.fixAll_of_good R F hT.char hT.ex
  have hU := GlobalTheory.T.thetaLift_scalarIdentity_matching_adjointInjective hP.q5 hP.q3 hP.q4 hP.q6 hP.q2 hP.q1 hP.q7 hP.q8
    (_root_.ResidueKilled.sec_of_dm hP.q9) hP.q10 hP.q11 R.toRealDat F.lv2 hGiv hT.ccK
    hT.char.allPl hFix R.SF hCore.2.1 hTR
  exact ⟨hGiv, hStab, hCD, hLI, hTR, hU.2.2.1, hU.2.2.2⟩
end GlobalTheory.PrimBase
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn

theorem _root_.GlobalTheory.T.lift_data_of_multiplicity_one : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), TiesB R F → GlobalTheory.CuspMult.MultEq R.toRealDat → GlobalTheory.LiftRows.Given R.toRealDat F.lv2 ∧ GoodStable A3.A.X ∧ GlobalTheory.CuspMult.CuspDecomp D ∧ GlobalTheory.Chain.LiftInteg D ∧ GlobalTheory.TrCopy.TRLev R.toRealDat F.lv2 R.SF ∧ GlobalTheory.LiftRows.UpInj R.toRealDat ∧ GlobalTheory.LiftRows.UpInjW R.toRealDat := by
  first | exact @_root_.GlobalTheory.PrimBase.base_of_ties_alt | exact _root_.GlobalTheory.PrimBase.base_of_ties_alt | (intros; apply _root_.GlobalTheory.PrimBase.base_of_ties_alt <;> assumption)
end
end

section

section
namespace UpperTheory.Lit.Sw47
theorem siegelWeil_fock_anisotropic_unconditional (D : Formalism.BasicNotions.D7) :
    GlobalTheory.BottomRallis.SiegelWeilFockAniso D := fa D
end UpperTheory.Lit.Sw47
end
end

section

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SqTower
theorem theta_tower_top_stage_norm_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (ρ : RealMatch W) (i j : Fin D.R.m), ∃ (A A' WW : HSp D) (X : Tri T A A' WW) (c κ : T → ℂ),
      GlobalTheory.SqTower.IsStageC W i j (pp D j) (qq D j) X ∧ X.IsConst W.ψ W.θ c ∧
      (∀ t, κ t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ κ t = D.what₂.embLL ζ * κ μ₀) ∧
      ∀ (t : T) (c' : ℂ), SquareNonzero W S.B ρ t i j → IsSquareConst W S.B ρ t i j c' → c' = κ t * c t := by
  intro hP hK hM
  refine gBig_of₃ (_root_.GlobalTheory.T.exists_grid_of_square_tower hP) (_root_.GlobalTheory.T.exists_factor_of_isStageC hP hK hM) (_root_.GlobalTheory.T.theta_square_norm_comparison hP hK hM) ?_
  intro D T Lc sc G μ₀ C x b hex hfac hcmp W S hstd hN ρ i j
  obtain ⟨X, hT, hX⟩ := hex W i j
  obtain ⟨lam, hl⟩ := hfac W S hstd hN i j (pp D j) (qq D j) _ _ _ X hX
  obtain ⟨κ, hκ, hc⟩ := hcmp W S hstd hN ρ i j X lam hT hX hl
  haveI : Nonempty T := ⟨μ₀⟩
  exact ⟨_, _, _, X, lam, κ, hX, hl.isConst, hκ, hc⟩
end GlobalTheory.SqTower
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

theorem _root_.GlobalTheory.T.witt_tower_top_stage_theta_norm_formula : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (ρ : RealMatch W) (i j : Fin D.R.m), ∃ (A A' WW : HSp D) (X : Tri T A A' WW) (c κ : T → ℂ),
      GlobalTheory.SqTower.IsStageC W i j (pp D j) (qq D j) X ∧ X.IsConst W.ψ W.θ c ∧
      (∀ t, κ t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ κ t = D.what₂.embLL ζ * κ μ₀) ∧
      ∀ (t : T) (c' : ℂ), SquareNonzero W S.B ρ t i j → IsSquareConst W S.B ρ t i j c' → c' = κ t * c t := by
  first | exact @_root_.GlobalTheory.SqTower.theta_tower_top_stage_norm_eq | exact _root_.GlobalTheory.SqTower.theta_tower_top_stage_norm_eq | (intros; apply _root_.GlobalTheory.SqTower.theta_tower_top_stage_norm_eq <;> assumption)
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
namespace GlobalTheory.SqStep
theorem theta_tower_norm_step_small_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ) (Lf : T → ℂ → ℂ),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
        GlobalTheory.SqTower.IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, y t ≠ 0 ∧ lam t * Lf t ((e + 1 : ℕ) : ℂ) = y t * c t) ∧ ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀) := by
  intro hP hK hM
  refine gbig_three (_root_.GlobalTheory.T.seesaw_first_reduction_level hP hK hM) GlobalTheory.T.thetaStepFactor_ratio_unit_gaussSumQuotient GlobalTheory.T.partialHeckeLFunction_square_eq_primitive ?_
  intro D T Lc sc G μ₀ C x b hk ha hl W S hψ hN i j p q A A' WW X lam e Lf hX hF he hLf
  obtain ⟨B, B', WW₁, Y, c, hY, hc, hc0, H⟩ := hk W S hψ hN i j p q A A' WW X lam e hX hF he
  have he1 : 1 ≤ e := by
    obtain ⟨h1, h2, a1, a2, -⟩ := hX
    have e2 : rankV D (↑i + 1) (↑j + 1) = rankV D ↑i ↑j + D.R.t + sLen D := by simp only [rankV]; ring
    have h3 := D.R.three_m_lt_t
    have hpp : pp D j ≤ D.R.m := by unfold pp; omega
    have hqq : qq D j ≤ D.R.m := by unfold qq; omega
    omega
  have hLeq : ∀ t, GlobalTheory.LFun.charL (chs G i j t).ν (G.pl.S0 : Set (HeightOneSpectrum (𝓞 D.host.F))) ((e + 1 : ℕ) : ℂ) =
      Lf t ((e + 1 : ℕ) : ℂ) := fun t => hl i j t (e + 1) (Lf t) (by omega) (hLf t)
  refine ⟨B, B', WW₁, Y, c, fun t => lam t * Lf t ((e + 1 : ℕ) : ℂ) / c t, hY, hc, fun t => ⟨?_, ?_⟩, fun t => ?_⟩
  · obtain ⟨Bs, e₁, e₂, s, 𝔟, 𝔠, -, -, -, hL0, -, -⟩ := H t
    rw [hLeq t] at hL0
    exact div_ne_zero (mul_ne_zero (hF.1 t) hL0) (hc0 t)
  · rw [div_mul_cancel₀ _ (hc0 t)]
  · obtain ⟨Bs, e₁, e₂, s, 𝔟, 𝔠, hfit, hsf, hsf0, -, -, heq⟩ := H t
    rw [hLeq t, hLeq μ₀] at heq
    obtain ⟨bb, g, g', hb, hg, e3⟩ := ha W S hψ hN i j t Bs e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) hfit hsf
    refine ⟨bb, g, g', hb, hg, ?_⟩
    have h0 := hc0 μ₀
    have ht := hc0 t
    rw [e3] at heq
    have key := mul_right_cancel₀ hsf (show (lam t * Lf t ((e + 1 : ℕ) : ℂ) * c μ₀) * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) =
      (D.what₂.embLL (bb * ∏ v ∈ G.pl.S0, ((g v : D.what₂.LL) / (g' v : D.what₂.LL))) * (lam μ₀ * Lf μ₀ ((e + 1 : ℕ) : ℂ)) * c t) *
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.stepFac Bs (chs G i j t) e₁ e₂ s 𝔟 𝔠 (-(e : ℤ)) by linear_combination heq)
    field_simp
    linear_combination key
end GlobalTheory.SqStep
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
theorem _root_.GlobalTheory.T.witt_tower_norm_step_of_small_rank : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW) (lam : T → ℂ) (e : ℕ) (Lf : T → ℂ → ℂ),
      GlobalTheory.SqTower.IsStageC W i j p (q + 1) X → Factor X W.ψ W.θ lam → A.rank = A'.rank + 2 * e →
      (∀ t, IsHeckeL (nuH G t i j) (Lf t)) → ∃ (B B' WW₁ : HSp D) (Y : Tri T B B' WW₁) (c y : T → ℂ),
        GlobalTheory.SqTower.IsStageC W i j p q Y ∧ Y.IsConst W.ψ W.θ c ∧
        (∀ t, y t ≠ 0 ∧ lam t * Lf t ((e + 1 : ℕ) : ℂ) = y t * c t) ∧ ∀ t, GlobalTheory.Square.StepRatio D.what₂.embLL (Qn G t) G.pl.S0 (condExp G.pl) (fun v => Ideal.absNorm v.asIdeal) (y t) (y μ₀) := by
  first | exact @_root_.GlobalTheory.SqStep.theta_tower_norm_step_small_rank | exact _root_.GlobalTheory.SqStep.theta_tower_norm_step_small_rank | (intros; apply _root_.GlobalTheory.SqStep.theta_tower_norm_step_small_rank <;> assumption)
end
end
