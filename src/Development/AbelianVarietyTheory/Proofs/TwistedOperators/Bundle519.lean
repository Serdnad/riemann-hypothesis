module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1651
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle489
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Definitions.Divisors.GridTestLatticeLargestSlopeBound
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle372
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle220
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1857
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle371
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle162
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Dynamics.Ergodic.Action.Regular
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
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelPlusSubgroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OffQOfSizeRows
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle009
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.UnitCharTriangle
import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FlatTensorVacuum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle443
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC


theorem _root_.GlobalTheory.T.heisenbergTranslate_finiteRational_realGaussian : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → IsStdChar D ψ (-1) → IsInfFam θ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ Φ : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank → ℂ, (∀ w : WO S T, w.map (finPart D) = 0 → f w = GlobalTheory.FockPos.gaussO θ frS frT w * Φ (GlobalTheory.FockPos.zCo θ frS frT w)) → ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (X : Formalism.MainNotions.TaylorLogMetric.VC D S.rank T.rank), X = (fun τ a b => -(((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T M τ) * GlobalTheory.FockPos.frAt frS τ) a b)) → ∀ w : WO S T, w.map (finPart D) = 0 → heisO ψ S T (GlobalTheory.VacUnique.finRat S T M) f w = GlobalTheory.FockPos.gaussO θ frS frT w * (Φ (GlobalTheory.FockPos.zCo θ frS frT w + X) * Complex.exp (-(Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, GlobalTheory.FockPos.zCo θ frS frT w τ a b * starRingEnd ℂ (X τ a b)) - (Real.pi : ℂ) * (2 * ((Formalism.L2.Pj.xiR D : ℝ) : ℂ) * ∑ τ, ∑ a, ∑ b, X τ a b * starRingEnd ℂ (X τ a b)) / 2)) := by
  first | exact @GlobalTheory.MovedTrans.heisO_finRat_real | exact GlobalTheory.MovedTrans.heisO_finRat_real | (intros; apply GlobalTheory.MovedTrans.heisO_finRat_real <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC


theorem _root_.GlobalTheory.T.heisenberg_root_smul_finiteRational_latticeDecomp : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f : WO S T → ℂ, IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f → ∀ n : ℕ, 0 < n → ∀ w : WO S T, n • w ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (ζ : ℂ), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ GlobalTheory.VacUnique.finRat S T (n • M) ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧ heisO ψ S T w f = ζ • heisO ψ S T (GlobalTheory.VacUnique.finRat S T M) f := by
  first | exact @GlobalTheory.MultLatDecomp.heisO_eq_root_smul_finRat | exact GlobalTheory.MultLatDecomp.heisO_eq_root_smul_finRat | (intros; apply GlobalTheory.MultLatDecomp.heisO_eq_root_smul_finRat <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

noncomputable section

namespace GlobalTheory.BplusLaws

private theorem norm_besChar_eq_one {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) (d : BesDat A B ι) (n : GA D B) :
    ‖besChar ψ d n‖ = 1 := by
  unfold besChar
  split_ifs with h
  · obtain ⟨a, b, -, -, hv⟩ := h.choose_spec
    rw [hv]
    exact hψ _
  · simp

private theorem coCpt_gridData_V_zero {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    GlobalTheory.Unf.CoCpt (G.V (.top 0)) := by
  have hV := GlobalTheory.FunObj.isV_Xp G
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact (G.V (.top 0)) fun τ =>
    GlobalTheory.DefiniteQuotient.posDef_of_signature (by
      have h1 := hV.sigOK (tauE D τ)
      rw [hV.sig (tauE D τ)] at h1
      exact h1)
  refine ⟨C, hC, fun g => ?_⟩
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
  exact ⟨γ⁻¹, inv_mem hγ, by rwa [← mul_assoc, inv_mul_cancel, one_mul]⟩

private theorem integrableOn_besInt_of_bounded {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)
    (M : Vol G) (hM : M.IsRow) {φ : GA D (G.V (.top 0)) → ℂ} (hφc : Continuous φ) {Cφ : ℝ}
    (hCφ : ∀ g, ‖φ g‖ ≤ Cφ) (hvol : M.ν (.top 0) (M.fd (.top 0)) < ⊤)
    {F : GA D (G.V (.grid D.R.m 0)) → ℂ} (hFc : Continuous F) {K : ℝ}
    (hK : ∀ h (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e), ‖F ((n : GA D _) * embTop G h)‖ ≤ K) :
    (∀ h, IntegrableOn (besInt W φ F h) M.fdN M.νN) ∧
      IntegrableOn (fun h => ∫ n in M.fdN, besInt W φ F h n ∂M.νN) (M.fd (.top 0)) (M.ν (.top 0)) := by
  have hψ : ∀ x, ‖W.ψ x‖ = 1 := W.ψ_std.1.2.1
  obtain ⟨-, -, hBor, -⟩ := GlobalTheory.Per.Inhab.flag_topology _ G.besTop.e_iso
  haveI := GlobalTheory.Unf.EvalCont.firstCountable_GA (G.V (.top 0))
  have hemb : Continuous (embTop G) :=
    GlobalTheory.Per.Inhab.emb_continuous (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
      (fun h => (GlobalTheory.FunObj.embRel_iff _ h _).2 rfl)
  have hχ : Continuous fun n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e => besChar W.ψ G.besTop (n : GA D _) :=
    GlobalTheory.BesselChar.besChar_continuous _ W.ψ_std.1 _
  have hjoint : Continuous fun q : GA D (G.V (.top 0)) × NFlag (G.V (.grid D.R.m 0)) G.besTop.e =>
      besInt W φ F q.1 q.2 := by
    unfold besInt
    refine ((hφc.comp continuous_fst).mul (hFc.comp ?_)).mul ((hχ.comp continuous_snd).star)
    exact (continuous_subtype_val.comp continuous_snd).mul (hemb.comp continuous_fst)
  have hbd : ∀ h n, ‖besInt W φ F h n‖ ≤ Cφ * K := by
    intro h n
    unfold besInt
    rw [norm_mul, norm_mul, norm_star, norm_besChar_eq_one hψ, mul_one]
    exact mul_le_mul (hCφ h) (hK h n) (norm_nonneg _) (le_trans (norm_nonneg _) (hCφ h))
  have hNlt : M.νN M.fdN < ⊤ := by rw [hM.unip.2.2]; exact ENNReal.one_lt_top
  refine ⟨fun h => Measure.integrableOn_of_bounded hNlt.ne ?_ (ae_of_all _ (hbd h)), ?_⟩
  · exact (hjoint.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · have hT : GlobalTheory.Unf.EvalCont.Tame fun h (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e) => besInt W φ F h n :=
      GlobalTheory.Unf.EvalCont.tame_of_bounded hjoint hbd
    have hcont := GlobalTheory.Unf.EvalCont.Tame.continuous_integral M.νN M.fdN hNlt hT
    exact Measure.integrableOn_of_bounded hvol.ne hcont.aestronglyMeasurable
      (ae_of_all _ fun h => norm_setIntegral_le_of_norm_le_const hNlt fun n _ => hbd h n)

theorem bplus_add_bound : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ Ω : Set (GA D (G.V (.grid D.R.m 0))), IsCompact Ω → (∀ (h : GA D (G.V (.top 0))) (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e),
      ∃ γ ∈ GQ (G.V (.grid D.R.m 0)), γ * ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h) ∈ Ω) →
    ∀ φ ∈ contLeft (G.V (.top 0)), ∃ C : ℝ,
      (∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ F' ∈ contLeft (G.V (.grid D.R.m 0)), Bplus W M φ (F + F') = Bplus W M φ F + Bplus W M φ F') ∧
      (∀ φ' ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), Bplus W M (φ + φ') F = Bplus W M φ F + Bplus W M φ' F) ∧
      ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ K : ℝ, (∀ x ∈ Ω, ‖F x‖ ≤ K) → ‖Bplus W M φ F‖ ≤ C * K := by
  intro D T L sc G W M hM Ω hΩc hΩ φ hφ
  have hcpt := coCpt_gridData_V_zero G
  obtain ⟨haar, fund⟩ := GlobalTheory.FunObj.Vol.IsAt.haar_fund hM.top
  have hvol : M.ν (.top 0) (M.fd (.top 0)) < ⊤ := GlobalTheory.Unf.EvalCont.vol_lt_top hcpt ⟨_, _, haar, fund⟩
  have hOrb : ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ K : ℝ, (∀ x ∈ Ω, ‖F x‖ ≤ K) →
      ∀ h (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e), ‖F ((n : GA D _) * embTop G h)‖ ≤ K := by
    intro F hF K hK h n
    obtain ⟨γ, hγ, hmem⟩ := hΩ h n
    rw [← hF.2 γ hγ]
    exact hK _ hmem
  have hconv : ∀ ψ ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)),
      (∀ h, IntegrableOn (besInt W ψ F h) M.fdN M.νN) ∧
        IntegrableOn (fun h => ∫ n in M.fdN, besInt W ψ F h n ∂M.νN) (M.fd (.top 0)) (M.ν (.top 0)) := by
    intro ψ hψ F hF
    obtain ⟨Cψ, hCψ⟩ := GlobalTheory.Unf.EvalCont.bounded_of_contAut hcpt ⟨hψ.2, hψ.1⟩
    obtain ⟨K, hK⟩ := hΩc.exists_bound_of_continuousOn hF.1.continuousOn
    exact integrableOn_besInt_of_bounded W M hM hψ.1 hCψ hvol hF.1 (hOrb F hF K hK)
  obtain ⟨Cφ, hCφ⟩ := GlobalTheory.Unf.EvalCont.bounded_of_contAut hcpt ⟨hφ.2, hφ.1⟩
  refine ⟨Cφ * (M.ν (.top 0)).real (M.fd (.top 0)), ?_, ?_, ?_⟩
  · intro F hF F' hF'
    unfold Bplus
    refine GlobalTheory.Per.Inhab.iterated_add (hconv φ hφ F hF) (hconv φ hφ F' hF') fun h n => ?_
    unfold besInt
    simp only [Pi.add_apply]
    ring
  · intro φ' hφ' F hF
    unfold Bplus
    refine GlobalTheory.Per.Inhab.iterated_add (hconv φ hφ F hF) (hconv φ' hφ' F hF) fun h n => ?_
    unfold besInt
    simp only [Pi.add_apply]
    ring
  · intro F hF K hK
    have hK' := hOrb F hF K hK
    have hNlt : M.νN M.fdN < ⊤ := by rw [hM.unip.2.2]; exact ENNReal.one_lt_top
    have hNr : M.νN.real M.fdN = 1 := by simp [Measure.real, hM.unip.2.2]
    have hbd : ∀ h n, ‖besInt W φ F h n‖ ≤ Cφ * K := by
      intro h n
      unfold besInt
      rw [norm_mul, norm_mul, norm_star, norm_besChar_eq_one W.ψ_std.1.2.1, mul_one]
      exact mul_le_mul (hCφ h) (hK' h n) (norm_nonneg _) (le_trans (norm_nonneg _) (hCφ h))
    unfold Bplus
    calc ‖∫ h in M.fd (.top 0), ∫ n in M.fdN, besInt W φ F h n ∂M.νN ∂M.ν (.top 0)‖
        ≤ (Cφ * K) * (M.ν (.top 0)).real (M.fd (.top 0)) := by
          refine norm_setIntegral_le_of_norm_le_const hvol fun h _ => ?_
          have := norm_setIntegral_le_of_norm_le_const hNlt fun n (_ : n ∈ M.fdN) => hbd h n
          rwa [hNr, mul_one] at this
      _ = Cφ * (M.ν (.top 0)).real (M.fd (.top 0)) * K := by ring

end GlobalTheory.BplusLaws

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
noncomputable section

namespace GlobalTheory.BplusShift

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem embTop_mul (a b : GA D (G.V (.top 0))) : embTop G (a * b) = embTop G a * embTop G b := by
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D _ _ _
    (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have e : ∀ h, embTop G h = s h := fun h => ((embRel_iff _ h _).1 ((hs h _).2 rfl)).symm
  rw [e, e, e, map_mul]

theorem inner_left (W : G.Weil) (M : Vol G) (hM : M.IsRow) {φ : Fn G (.top 0)} {F : Fn G (.grid D.R.m 0)}
    (hφ : φ ∈ contLeft (G.V (.top 0))) (hF : F ∈ contLeft (G.V (.grid D.R.m 0))) {γ : GA D (G.V (.top 0))}
    (hγ : γ ∈ GQ (G.V (.top 0))) (h : GA D (G.V (.top 0))) :
    ∫ n in M.fdN, besInt W φ F (γ * h) n ∂M.νN = ∫ n in M.fdN, besInt W φ F h n ∂M.νN := by
  obtain ⟨_, _, _, _⟩ := GlobalTheory.Per.Inhab.flag_topology _ G.besTop.e_iso
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid D.R.m 0))
  obtain ⟨s, -, hs, hq⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D _ _ _
    (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have e : ∀ h, embTop G h = s h := fun h => ((embRel_iff _ h _).1 ((hs h _).2 rfl)).symm
  have r1 := (hs γ (s γ)).2 rfl
  have r2 := (hs γ⁻¹ (s γ)⁻¹).2 (map_inv s _).symm
  have hδ : s γ ∈ GQ (G.V (.grid D.R.m 0)) := hq _ hγ
  let c : NFlag (G.V (.grid D.R.m 0)) G.besTop.e ≃ₜ* NFlag (G.V (.grid D.R.m 0)) G.besTop.e :=
    { toFun := fun n => ⟨s γ * n * (s γ)⁻¹, (GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop _ _ r1 n n.2).1⟩
      invFun := fun n => ⟨(s γ)⁻¹ * n * (s γ)⁻¹⁻¹, (GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop _ _ r2 n n.2).1⟩
      left_inv := fun n => Subtype.ext (by simp [mul_assoc])
      right_inv := fun n => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hc : ∀ n, c n ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e ↔ n ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e := fun n => by
    change s γ * n.1 * (s γ)⁻¹ ∈ GQ (G.V (.grid D.R.m 0)) ↔ n.1 ∈ GQ (G.V (.grid D.R.m 0))
    rw [Subgroup.mul_mem_cancel_right _ (inv_mem hδ), Subgroup.mul_mem_cancel_left _ hδ]
  have hl : ∀ γ' ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e, ∀ n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e,
      besInt W φ F (γ * h) (γ' * n) = besInt W φ F (γ * h) n := fun γ' hγ' n => by
    have hq' := Subgroup.mem_subgroupOf.1 hγ'
    simp only [besInt, Subgroup.coe_mul]
    rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop _ _ γ'.2 n.2, GlobalTheory.BesselChar.besChar_rat W.ψ W.ψ_std.1 G.besTop _ γ'.2 hq',
      one_mul, mul_assoc γ'.1, hF.2 _ hq']
  refine (GlobalTheory.Mem.TrueRecord.integral_aut _ hM.unip.1 hM.unip.2.1 hM.unip.2.2 c hc _ hl).symm.trans ?_
  congr 1
  funext n
  change φ (γ * h) * F ((s γ * n * (s γ)⁻¹) * embTop G (γ * h)) * star (besChar W.ψ G.besTop (s γ * n * (s γ)⁻¹)) =
    φ h * F (n * embTop G h) * star (besChar W.ψ G.besTop n)
  rw [(GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop _ _ r1 n n.2).2, hφ.2 γ hγ h, e, e, map_mul,
    show s γ * n * (s γ)⁻¹ * (s γ * s h) = s γ * (n * s h) by group, hF.2 _ hδ]

end GlobalTheory.BplusShift


open GlobalTheory.BplusShift in
theorem GlobalTheory.BplusShift.bplus_rTr : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ φ ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ a : GA D (G.V (.top 0)),
      Bplus W M (rTr _ a φ) (rTr _ (embTop G a) F) = Bplus W M φ F := by
  intro D T L sc G W M hM φ hφ F hF a
  have hshift : ∀ h n, besInt W (rTr _ a φ) (rTr _ (embTop G a) F) h n = besInt W φ F (h * a) n := fun h n => by
    simp only [besInt, rTr]
    rw [embTop_mul, mul_assoc (n : GA D (G.V (.grid D.R.m 0)))]
  simp only [Bplus, hshift]
  obtain ⟨hμ, h𝓕⟩ := hM.top.haar_fund
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  haveI := hμ
  haveI : (M.ν (.top 0)).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hμ
  have hmp : MeasurePreserving (· * a) (M.ν (.top 0)) (M.ν (.top 0)) := measurePreserving_mul_right _ a
  have hmp' : MeasurePreserving (· * a⁻¹) (M.ν (.top 0)) (M.ν (.top 0)) := measurePreserving_mul_right _ a⁻¹
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight a)
    (fun h => ∫ n in M.fdN, besInt W φ F h n ∂M.νN) (M.fd (.top 0)), Set.image_mul_right]
  have hF' : IsFundamentalDomain (GQ (G.V (.top 0))) ((· * a⁻¹) ⁻¹' M.fd (.top 0)) (M.ν (.top 0)) :=
    h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (h𝓕.setIntegral_eq hF' fun γ x => inner_left W M hM hφ hF γ.2 x).symm
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

noncomputable section

namespace GlobalTheory.BplusUnip

variable {D : D7}

theorem setIntegral_mul_right {B : HSp D} {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E} (he : IsIsoSub B e)
    {ν : Measure (NFlag B e)} {𝓝 : Set (NFlag B e)} (hN : GlobalTheory.Per.IsUnitN B e ν 𝓝) (f : NFlag B e → ℂ)
    (hf : ∀ γ ∈ NFlagQ B e, ∀ n, f (γ * n) = f n) (y : NFlag B e) :
    ∫ n in 𝓝, f (n * y) ∂ν = ∫ n in 𝓝, f n ∂ν := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag B he
  obtain ⟨u1, u2, u3⟩ := hN
  haveI : DiscreteTopology (NFlagQ B e) := by
    refine DiscreteTopology.of_continuous_injective
      (f := fun γ : NFlagQ B e => (⟨γ.1.1, γ.2⟩ : GQ B)) ?_ ?_
    · exact Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
    · intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun x : GQ B => (x : GA D B)) hab))
  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B ρ e he).1
  have hcov' : ∀ x : NFlag B e, ∃ s ∈ NFlagQ B e, s * x ∈ K := fun x => by
    obtain ⟨γ, hγ, k, hk, e⟩ := hcov x
    exact ⟨γ⁻¹, inv_mem hγ, by rw [e, ← mul_assoc, inv_mul_cancel, one_mul]; exact hk⟩
  have hr : ∀ a : NFlag B e, ν.map (· * a) = ν := fun a =>
    Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice ν (NFlagQ B e) hK hcov' a
  have hmp : MeasurePreserving (· * y) ν ν := ⟨measurable_mul_const y, hr y⟩
  have hmp' : MeasurePreserving (· * y⁻¹) ν ν := ⟨measurable_mul_const y⁻¹, hr y⁻¹⟩
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight y) f 𝓝, Set.image_mul_right]
  have hF : IsFundamentalDomain (NFlagQ B e) ((· * y⁻¹) ⁻¹' 𝓝) ν :=
    u2.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (u2.setIntegral_eq hF fun γ x => hf γ γ.2 x).symm

theorem bplus_rTr_unip : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ (φ : GA D (G.V (.top 0)) → ℂ), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ u ∈ NFlag (G.V (.grid D.R.m 0)) G.besTop.e,
      Bplus W M φ (rTr _ u F) = besChar W.ψ G.besTop u * Bplus W M φ F := by
  intro D T L sc G W M hM φ F hF u hu
  have hn : ∀ n, ‖besChar W.ψ G.besTop n‖ = 1 := fun n => by
    unfold besChar
    split_ifs with h
    · obtain ⟨a, b, -, -, e⟩ := h.choose_spec
      rw [e]
      exact W.ψ_std.1.2.1 _
    · exact norm_one
  have hu1 : besChar W.ψ G.besTop u * star (besChar W.ψ G.besTop u) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hn]
    norm_num
  have inner : ∀ h, ∫ n in M.fdN, besInt W φ (rTr _ u F) h n ∂M.νN =
      besChar W.ψ G.besTop u * ∫ n in M.fdN, besInt W φ F h n ∂M.νN := fun h => by
    have hs : EmbRel _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι (embTop G h) h := (embRel_iff _ h _).2 rfl
    obtain ⟨hy, hyc⟩ := GlobalTheory.BesselChar.besChar_conj W.ψ G.besTop (embTop G h) h hs u hu
    let y : NFlag (G.V (.grid D.R.m 0)) G.besTop.e := ⟨_, hy⟩
    have hinv : ∀ γ ∈ NFlagQ (G.V (.grid D.R.m 0)) G.besTop.e, ∀ n,
        besInt W φ F h (γ * n) = besInt W φ F h n := fun γ hγ n => by
      have hγQ : (γ : GA D (G.V (.grid D.R.m 0))) ∈ GQ (G.V (.grid D.R.m 0)) := Subgroup.mem_subgroupOf.1 hγ
      simp only [besInt, Subgroup.coe_mul]
      rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop _ _ γ.2 n.2,
        GlobalTheory.BesselChar.besChar_rat W.ψ W.ψ_std.1 G.besTop _ γ.2 hγQ, one_mul, mul_assoc (γ : GA D (G.V (.grid D.R.m 0))) (n : GA D (G.V (.grid D.R.m 0))) (embTop G h),
        hF.2 _ hγQ]
    have hpt : ∀ n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e, besInt W φ (rTr _ u F) h n =
        besChar W.ψ G.besTop u * besInt W φ F h (n * y) := fun n => by
      simp only [besInt, rTr, Subgroup.coe_mul, y]
      rw [GlobalTheory.BesselChar.besChar_mul W.ψ G.besTop _ _ n.2 hy, hyc, star_mul]
      have e1 : (n : GA D (G.V (.grid D.R.m 0))) * (embTop G h * u * (embTop G h)⁻¹) * embTop G h =
          (n : GA D (G.V (.grid D.R.m 0))) * embTop G h * u := by group
      rw [e1]
      linear_combination (-(φ h * F ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h * u) *
        star (besChar W.ψ G.besTop (n : GA D (G.V (.grid D.R.m 0)))))) * hu1
    simp_rw [hpt]
    rw [integral_const_mul, setIntegral_mul_right G.besTop.e_iso hM.unip _ hinv y]
  unfold Bplus
  simp_rw [inner]
  exact integral_const_mul _ _

end GlobalTheory.BplusUnip
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped ComplexOrder Classical

namespace GlobalTheory.BotClassFin

variable {D : D7}

def finPart (V : HSp D) (g : GA D V) : GA D V := ((GlobalTheory.AdelicSplit.splitEquiv V).symm g).2.1

theorem continuous_finPart (V : HSp D) : Continuous (finPart V) :=
  continuous_subtype_val.comp (continuous_snd.comp (GlobalTheory.AdelicSplit.splitEquiv V).symm.continuous)

theorem finPart_mem (V : HSp D) (g : GA D V) : finPart V g ∈ GfC V := ((GlobalTheory.AdelicSplit.splitEquiv V).symm g).2.2

theorem finPart_one (V : HSp D) : finPart V 1 = 1 := by
  simp [finPart, map_one]

theorem finHom_finPart (V : HSp D) (g : GA D V) : finHom V (finPart V g) = finHom V g := by
  set p := (GlobalTheory.AdelicSplit.splitEquiv V).symm g with hp
  have e : g = p.1.1 * p.2.1 := ((GlobalTheory.AdelicSplit.splitEquiv V).apply_symm_apply g).symm
  have h1 : finHom V p.1.1 = 1 := p.1.2
  conv_rhs => rw [e]
  rw [map_mul, h1, one_mul]
  rfl

theorem exists_reps_of_open (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) (J : Subgroup (GA D V))
    (hJ : IsOpen (J : Set (GA D V))) :
    ∃ H : Finset (GA D V), (∀ h ∈ H, h ∈ GfC V) ∧
      ∀ h ∈ GfC V, ∃ γ ∈ GQ V, ∃ r ∈ GinfC V, ∃ h₀ ∈ H, ∃ κ ∈ J, κ ∈ GfC V ∧ h = γ * r * h₀ * κ := by
  haveI := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.2.2.2.1
  set L : Subgroup (Bridge.Gf V) := (J ⊓ GfC V).map (finHom V).rangeRestrict with hL
  have hO : GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev V L := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev
    refine Subgroup.isOpen_of_mem_nhds (g := (1 : GA D V)) _ ?_
    have h1 : (finPart V) ⁻¹' (J : Set (GA D V)) ∈ nhds (1 : GA D V) := by
      refine (hJ.preimage (continuous_finPart V)).mem_nhds ?_
      show finPart V 1 ∈ J
      rw [finPart_one]
      exact J.one_mem
    refine Filter.mem_of_superset h1 fun g hg => ?_
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨finPart V g, ⟨hg, finPart_mem V g⟩, ?_⟩)
    exact Subtype.ext (finHom_finPart V g)
  obtain ⟨m, c, hc⟩ := GlobalTheory.RepsObj.exists_cover V hV L hO
  choose x hx using fun a => GlobalTheory.FunObj.ClassFin.gfcToGf_surjective V (c a)
  refine ⟨Finset.univ.image fun a => (x a).1, ?_, ?_⟩
  · intro h hh
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hh
    exact (x a).2
  · intro h hh
    obtain ⟨a, γ, k, e⟩ := hc ((finHom V).rangeRestrict h)
    obtain ⟨κ, ⟨hκJ, hκf⟩, hκ⟩ := Subgroup.mem_map.1 k.2
    have ex : finHom V (x a).1 = (c a).1 := congrArg Subtype.val (hx a)
    have ek : finHom V κ = k.1.1 := congrArg Subtype.val hκ
    have eγ : ((Bridge.ratF V γ : Bridge.Gf V) : _) = finHom V γ.1 := rfl
    have e' : finHom V h = finHom V γ.1 * finHom V (x a).1 * finHom V κ := by
      have := congrArg Subtype.val e
      rw [ex, ek, ← eγ]
      exact this
    refine ⟨γ.1, γ.2, γ.1⁻¹ * h * κ⁻¹ * (x a).1⁻¹, ?_, (x a).1, Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩, κ, hκJ, hκf,
      by group⟩
    show finHom V _ = 1
    simp only [map_mul, map_inv, e']
    group

end GlobalTheory.BotClassFin

end
end
