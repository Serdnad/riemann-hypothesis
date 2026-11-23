module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle276
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemParahoricOfTrivialReduction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle188
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiMapsAndOmegaLaw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle106
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle385
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle278
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle011
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FderivIntegralApplyOfHolomorphicOfDominated
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle204
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle262
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
public import Formalism.LocalToGlobal.Columns.RecLevelTop
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalVolumeLift
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SphericalZero
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SobContId
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SphericalEisensteinSeriesOnGroup
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle006
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle004
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle076
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle463
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.IndefiniteReal.Bundle001
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

@[expose] public section

section

open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens


theorem _root_.GlobalTheory.T.theta_word_limits_smooth_along_real_points : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (u : ℕ → WO S T → ℂ), (∀ j, IsThetaFunO ψ S T (u j)) → ∀ F : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool) → WO S T → ℂ, (∀ l, TendstoUniformly (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) (F l) Filter.atTop) → ∀ (l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool)) (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => F l (w + L t) := by
  first | exact @GlobalTheory.ThetaDens.contDiff_of_tendstoUniformly_words | exact GlobalTheory.ThetaDens.contDiff_of_tendstoUniformly_words | (intros; apply GlobalTheory.ThetaDens.contDiff_of_tendstoUniformly_words <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.PenPsiInv

open GlobalTheory.CongLevel

section Ext

variable {E : Type} [Field E]

theorem resX_extE {n : ℕ} (c : ℕ) (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) (v : Fin (n + c) → E) :
    resX c (extE c κ v) = κ (resX c v) := by
  rw [extE_apply, map_add (f := _), resX_inX]
  abel

theorem atNL_inX {n : ℕ} (c : ℕ) (w : Fin n → E) : atNL E (n + c) n (Loc.inX E n c w) = 0 := by
  unfold atNL
  split_ifs with h
  · rw [LinearMap.proj_apply, inX_apply, dite_eq_right (lt_irrefl n)]
  · rfl

theorem atNL_extE {n : ℕ} (c : ℕ) (κ : (Fin n → E) ≃ₗ[E] (Fin n → E)) (v : Fin (n + c) → E) :
    atNL E (n + c) n (extE c κ v) = atNL E (n + c) n v := by
  rw [extE_apply, map_add (f := _), atNL_inX, add_zero]

theorem joinCol_inFr {n' c' n c : ℕ} (f : Sp E n' ≃ₗ[E] Sp E n') (f' : Sp E n ≃ₗ[E] Sp E n) (x : HomE E n' n)
    (y : Sp E n) :
    joinCol (c' := c') (c := c) (inFr f f' x) (f'.symm y) =
      (extE c f'.symm).toLinearMap ∘ₗ joinCol (c' := c') (c := c) x y ∘ₗ (extE c' f).toLinearMap := by
  apply LinearMap.ext
  intro v
  simp only [joinCol, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.add_apply, LinearMap.smulRight_apply]
  rw [extE_inX]
  congr 1
  have h1 : LinearMap.funLeft E E (Fin.castAdd c') (extE c' f v) = f (LinearMap.funLeft E E (Fin.castAdd c') v) :=
    resX_extE c' f v
  rw [h1, atNL_extE, map_add (f := _), map_smul]
  rfl

end Ext

section Main

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu)

theorem extE_mem_Jat (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)) (hw : w ∈ Pr.vGs)
    (hd : ∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E)))
    (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (hκ : κ ∈ GLint X.E (R.N j) w)
    (hr : ∀ x ∈ stdAt X.E (R.N j) w, redV w (κ x) = redV w x) :
    extE (cOf R j) κ ∈ Jat (Pr := Pr) sharp j w := by
  have h := (Subgroup.mem_inf.1
    (GlobalTheory.Mem.Col2.LevMod.extE_mem_Cbe (Pr := Pr) sharp j w hw hd 1 (one_mem _) κ hκ hr)).2
  rw [Subgroup.mem_comap, inv_one, map_one] at h
  exact h

theorem lamRow_extE (sharp : Bool) (j : ℕ) (w : HeightOneSpectrum (𝓞 X.E)) (hw : w ∈ Pr.vGs)
    (hd : ∀ a : X.E, IntAt w a → redP w a = 0 → IntAt w (a / (qOf w : X.E)))
    (κ : Sp X.E (R.N j) ≃ₗ[X.E] Sp X.E (R.N j)) (hκ : κ ∈ GLint X.E (R.N j) w)
    (hr : ∀ x ∈ stdAt X.E (R.N j) w, redV w (κ x) = redV w x) :
    lamRow Ch mu sharp j w (extE (cOf R j) κ).toLinearMap = 1 := by
  have hq : ((qOf w : ℕ) : X.E) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact fun h0 => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
  have e : (extE (cOf R j) κ).toLinearMap = LinearMap.id + ((qOf w : ℕ) : X.E) •
      (((qOf w : ℕ) : X.E)⁻¹ • ((extE (cOf R j) κ).toLinearMap - LinearMap.id)) := by
    rw [smul_inv_smul₀ hq, add_sub_cancel]
  rw [e]
  refine GlobalTheory.LamRowCong.lamRow_one_add_q Ch mu sharp j w hw _ fun v hv => ?_
  unfold lamYat at hv ⊢
  rw [if_pos hw] at hv ⊢
  exact extE_cong w (qOf w) (cOf R j) (fun i => i + 1) hd κ hκ hr v hv

theorem muAt_det_extE (i : ℕ) {n : ℕ} (c : ℕ)
    (hd : ∀ a : X.E, IntAt P.1 a → redP P.1 a = 0 → IntAt P.1 (a / (qOf P.1 : X.E)))
    (κ : Sp X.E n ≃ₗ[X.E] Sp X.E n) (hκ : κ ∈ GLint X.E n P.1)
    (hr : ∀ x ∈ stdAt X.E n P.1, redV P.1 (κ x) = redV P.1 x) :
    muAt Ch sel mu cst i P ((LinearEquiv.det (extE c κ) : X.Eˣ) : X.E) = 1 := by
  refine GlobalTheory.TwU.MidIndep.muAt_det_cong Ch sel mu cst i P (n + c) 1 le_rfl _ fun v hv => ?_
  rw [pow_one]
  rw [GlobalTheory.DatumLaw.stdAt_eq] at hv ⊢
  exact extE_cong P.1 (qOf P.1) c 0 hd κ hκ hr v hv

end Main

theorem psiAt_one_inFr : ∀ {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X} {R : Formalism.BasicNotions.Ranks} (Ch : Formalism.L2.Col.Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ} (mu : Formalism.L2.DIV.Tup X.F X.E X.K S₀) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu)) (s : ℕ) (P : Formalism.L2.Col.rowSG Pr sel mu), P.1 ∈ Pr.vGs → R.m = s + 2 → (∀ a : X.E, Formalism.L2.Col.IntAt P.1 a → Formalism.L2.Col.redP P.1 a = 0 → Formalism.L2.Col.IntAt P.1 (a / (Formalism.L2.Col.qOf P.1 : X.E))) → ∀ (f : Formalism.L2.Col.Sp X.E (R.N s) ≃ₗ[X.E] Formalism.L2.Col.Sp X.E (R.N s)) (f' : Formalism.L2.Col.Sp X.E (R.N (s + 1)) ≃ₗ[X.E] Formalism.L2.Col.Sp X.E (R.N (s + 1))), f ∈ Formalism.L2.Col.GLint X.E (R.N s) P.1 → (∀ x ∈ Formalism.L2.Col.stdAt X.E (R.N s) P.1, Formalism.L2.Col.redV P.1 (f x) = Formalism.L2.Col.redV P.1 x) → f' ∈ Formalism.L2.Col.GLint X.E (R.N (s + 1)) P.1 → (∀ x ∈ Formalism.L2.Col.stdAt X.E (R.N (s + 1)) P.1, Formalism.L2.Col.redV P.1 (f' x) = Formalism.L2.Col.redV P.1 x) → ∀ (x : Formalism.L2.Col.HomE X.E (R.N s) (R.N (s + 1))) (y : Formalism.L2.Col.Sp X.E (R.N (s + 1))), Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 (Formalism.L2.Col.inFr f f' x) (f'.symm y) = Formalism.L2.Col.PsiAt Ch sel mu cst s P 1 x y := by
  intro X Pr R Ch sel S₀ mu cst s P hP hm hd f f' hf hr hf' hr' x y
  have hi : s + 2 ≤ R.m := hm.ge
  have hg : f'.symm ∈ GLint X.E (R.N (s + 1)) P.1 := inv_mem hf'
  have hgr : ∀ v ∈ stdAt X.E (R.N (s + 1)) P.1, redV P.1 (f'.symm v) = redV P.1 v := fun v hv => by
    have h := hr' _ ((hg v).2 hv)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have h1 := GlobalTheory.DatumLaw.phiAt_target Ch sel mu cst cst.sharp hi P (extE_mem_Jat cst.sharp (s + 1) P.1 hP hd _ hg hgr)
    (joinCol x y ∘ₗ (extE (cOf R s) f).toLinearMap)
  have h2 := GlobalTheory.DatumLaw.phiAt_source Ch sel mu cst cst.sharp hi P (extE_mem_Jat cst.sharp s P.1 hP hd _ hf hr) (joinCol x y)
  rw [muAt_det_extE Ch sel mu cst P s _ hd _ hg hgr, lamRow_extE Ch mu cst.sharp (s + 1) P.1 hP hd _ hg hgr, mul_one, one_mul] at h1
  rw [muAt_det_extE Ch sel mu cst P s _ hd _ hf hr, lamRow_extE Ch mu cst.sharp s P.1 hP hd _ hf hr, mul_one, one_mul] at h2
  unfold PsiAt
  rw [GlobalTheory.SymBridge.PsiStep.omPhi_one_one, GlobalTheory.SymBridge.PsiStep.omPhi_one_one, joinCol_inFr, h1, h2]

end GlobalTheory.PenPsiInv
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.firstOccurrenceRule_thetaChainStep_both_directions : ∀ (D : D7) (X : ProvA), Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisUpDownLine X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFourth X → Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFifth X → ∀ k : Fin D.R.m, ChainPar D k → ∀ τ, RulePar X (parB (Ptw D) k τ) (parB (Ptw D) (k + 1) τ) (expS D k τ) (expT D k τ) ∧ RulePar X (parB (Ptw D) (k + 1) τ) (parB (Ptw D) k τ) (expT D k τ) (expS D k τ) := by
  first | exact @GlobalTheory.StepRule.rulePar_step | exact GlobalTheory.StepRule.rulePar_step | (intros; apply GlobalTheory.StepRule.rulePar_step <;> assumption)
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open Filter Topology Set Metric GlobalTheory.Eis

namespace GlobalTheory.Eis

theorem zetaHolValueAt_of_heightBounds (l1 : ∀ (D : D7) (V : HSp D), ∃ (C : ℝ) (c : ℕ), ∀ g₁ g₂ : GA D V,
    GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c) (l2 : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle) (m : Measure (GA D V)), m.IsHaarMeasure →
    ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → ∀ (C' : ℝ) (c : ℕ),
    (∀ g₁ g₂ : GA D V, GlobalTheory.Grow.height (dblSp V) (io V (g₁, g₂)) ≤ C' * (GlobalTheory.Grow.height V g₁ * GlobalTheory.Grow.height V g₂) ^ c) →
    ∀ (C : ℝ) (N : ℕ), ∃ bound : AutQ V × AutQ V → ℝ, Integrable bound ((autMeasure V m).prod (autMeasure V m)) ∧
      ∀ E : GA D (dblSp V) → ℂ, LeftInv (GQ (dblSp V)) E → (∀ g, ‖E g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) →
        ∀ q, ‖GlobalTheory.Eis.dblIntegrandQ V μ E f₁ f₂ q‖ ≤ bound q) : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (m : Measure (GA D V)), m.IsHaarMeasure → ∀ (Φ : ℂ → GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisContinues V Φ → (∀ g, AnalyticOnNhd ℂ (GlobalTheory.Eis.eisSer V Φ g) (rightOf (V.rank / 2))) → (∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt V Φ s₀ k) → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → GlobalTheory.Eis.IsZetaFamily V μ m Φ f₁ f₂ → ∀ (s₀ : ℂ) (E₀ : GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisValueAt V Φ s₀ E₀ → GlobalTheory.Eis.DblConv V μ m E₀ f₁ f₂ ∧ GlobalTheory.Eis.ZetaHolValueAt V μ m Φ f₁ f₂ s₀ (GlobalTheory.Eis.dblInt V μ m E₀ f₁ f₂) := by
  intro D V μ hμ m hm Φ hE ha hreg f₁ f₂ h₁ h₂ hZ s₀ E₀ hv
  obtain ⟨C', c, hio⟩ := l1 D V
  have key : ∀ (H : ℂ → GA D (dblSp V) → ℂ) (z : ℂ) (r : ℝ), 0 < r →
      (∀ s ∈ ball z r, LeftInv (GQ (dblSp V)) (H s)) →
      (∀ g, DifferentiableOn ℂ (H · g) (ball z r)) →
      ContinuousOn (fun x : ℂ × GA D (dblSp V) => H x.1 x.2) (ball z r ×ˢ univ) →
      (∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball z r, ∀ g, ‖H s g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) →
      (∀ s ∈ ball z r, DblConv V μ m (H s) f₁ f₂) ∧
        DifferentiableOn ℂ (fun s => dblInt V μ m (H s) f₁ f₂) (ball z r) := by
    rintro H z r hr hinv hd hc ⟨C, N, hb⟩
    obtain ⟨bound, hbi, hbd⟩ := l2 D V μ m hm f₁ f₂ h₁ h₂ C' c hio C N
    have hcont : ∀ s ∈ ball z r, Continuous (H s) := fun s hs =>
      hc.comp_continuous (f := fun g => (s, g)) (by fun_prop) fun g => ⟨hs, trivial⟩
    have hli : ∀ s ∈ ball z r, LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ (H s) f₁ f₂) := fun s hs =>
      leftInv_dblIntegrand hμ (hinv s hs) h₁.1 h₂.1
    have hmeas : ∀ s ∈ ball z r, AEStronglyMeasurable (dblIntegrandQ V μ (H s) f₁ f₂)
        ((autMeasure V m).prod (autMeasure V m)) := by
      intro s hs
      have e' : dblIntegrandQ V μ (H s) f₁ f₂ =
          dblIntegrand V μ (H s) f₁ f₂ ∘ Prod.map (sec (GQ V)) (sec (GQ V)) :=
        funext fun q => (congrArg _ (Prod.ext (mk_sec q.1) (mk_sec q.2)).symm).trans (dblIntegrandQ_mk (hli s hs) _ _)
      rw [e']
      exact ((continuous_dblIntegrand hμ (hcont s hs) h₁.continuous h₂.continuous).measurable.comp
        (measurableEmbedding_sec.measurable.prodMap measurableEmbedding_sec.measurable)).aestronglyMeasurable
    refine ⟨fun s hs => ⟨hli s hs, hbi.mono' (hmeas s hs) (ae_of_all _ fun q => hbd (H s) (hinv s hs) (hb s hs) q)⟩, ?_⟩
    have := GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated
      (μ := (autMeasure V m).prod (autMeasure V m)) (F := fun q s => dblIntegrandQ V μ (H s) f₁ f₂ q)
      (isOpen_ball (x := z) (ε := r)) hmeas
      (ae_of_all _ fun q => by
        simp only [dblIntegrandQ, dblIntegrand]
        exact (((hd _).mul_const _).mul_const _).mul_const _)
      fun x hx => ⟨ball z r, isOpen_ball.mem_nhds hx, bound, hbi,
        ae_of_all _ fun q y hy => hbd (H y) (hinv y hy) (hb y hy) q⟩
    exact this.1
  have hinvE : ∀ s, LeftInv (GQ (dblSp V)) (eisCont V Φ s) := fun s => hE.1.leftInv_eisLaurent s 0
  set Z : ℂ → ℂ := fun s => dblInt V μ m (eisCont V Φ s) f₁ f₂ with hZdef
  have hmer : ∀ s₁, MeromorphicAt Z s₁ := by
    intro s₁
    obtain ⟨k, r, H, hr, e, hd, hc, C, N, hb⟩ := hreg s₁
    have hinvH : ∀ s ∈ ball s₁ r, LeftInv (GQ (dblSp V)) (H s) := by
      intro s hs γ hγ g
      rcases eq_or_ne s s₁ with rfl | h0
      · have t1 := ((hd (γ * g)).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := {s}ᶜ))
        have t2 := ((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := {s}ᶜ))
        refine tendsto_nhds_unique t1 (t2.congr' ?_)
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s hr)] with w h1 h2
        rw [e w h2 h1, e w h2 h1, hinvE w γ hγ g]
      · rw [e s hs h0, e s hs h0, hinvE s γ hγ g]
    have han : AnalyticAt ℂ (fun s => dblInt V μ m (H s) f₁ f₂) s₁ :=
      (key H s₁ r hr hinvH hd hc ⟨C, N, hb⟩).2.analyticAt (ball_mem_nhds _ hr)
    have hm1 : MeromorphicAt (fun s => ((s - s₁) ^ k)⁻¹ * dblInt V μ m (H s) f₁ f₂) s₁ := by
      have : MeromorphicAt (fun s : ℂ => s - s₁) s₁ := (MeromorphicAt.id s₁).sub (MeromorphicAt.const _ _)
      exact (this.pow k).inv.mul han.meromorphicAt
    refine hm1.congr ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₁ hr)] with w h1 h2
    have e1 : eisCont V Φ w = ((w - s₁) ^ k)⁻¹ • H w := by
      funext g
      rw [Pi.smul_apply, e w h2 h1 g, smul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ (sub_ne_zero.2 h1)), one_mul]
    have e2 := dblInt_smul (V := V) (μ := μ) (m := m) (E := H w) (f₁ := f₁) (f₂ := f₂) ((w - s₁) ^ k)⁻¹ 1 1
    simp only [one_smul, map_one, mul_one] at e2
    simp only [Z, e1, e2]
  have hext : IsMerExt (zeta V μ m Φ f₁ f₂) univ Z := by
    refine ⟨isRightDomain_univ, fun s _ => hmer s, (V.rank : ℝ) / 2, fun s hs => ?_⟩
    have : eisCont V Φ s = eis V (Φ s) := funext fun g => eqOn_cont (ha g) hs
    simp only [Z, zeta, this]
  obtain ⟨k, hk⟩ := hreg s₀
  obtain ⟨r, hr, hd, hc, C, N, hb⟩ := hk.of_eisValueAt hv
  obtain ⟨hconv, hdiff⟩ := key (eisCont V Φ) s₀ r hr (fun s _ => hinvE s) hd hc ⟨C, N, hb⟩
  have e0 := hv.eisCont_eq
  refine ⟨e0 ▸ hconv s₀ (mem_ball_self hr), hZ, Z, hext.isExtAt trivial, hdiff.analyticAt (ball_mem_nhds _ hr), ?_⟩
  simp only [Z, e0]

theorem zetaHolValueAt_of_eisValueAt : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (m : Measure (GA D V)), m.IsHaarMeasure → ∀ (Φ : ℂ → GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisContinues V Φ → (∀ g, AnalyticOnNhd ℂ (GlobalTheory.Eis.eisSer V Φ g) (rightOf (V.rank / 2))) → (∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt V Φ s₀ k) → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → GlobalTheory.Eis.IsZetaFamily V μ m Φ f₁ f₂ → ∀ (s₀ : ℂ) (E₀ : GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisValueAt V Φ s₀ E₀ → GlobalTheory.Eis.DblConv V μ m E₀ f₁ f₂ ∧ GlobalTheory.Eis.ZetaHolValueAt V μ m Φ f₁ f₂ s₀ (GlobalTheory.Eis.dblInt V μ m E₀ f₁ f₂) :=
  zetaHolValueAt_of_heightBounds GlobalTheory.T.exists_height_doublingEmbedding_le_pow_mul_heights GlobalTheory.T.exists_integrable_bound_doubling_integrand_quotient

end GlobalTheory.Eis
end

section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open Filter Topology Set Metric GlobalTheory.Eis

namespace GlobalTheory.Eis

theorem zetaContinues_of_eisRegularAt {D : D7} {V : HSp D} {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ)
    {m : Measure (GA D V)} (hm : m.IsHaarMeasure) {Φ : ℂ → GA D (dblSp V) → ℂ} (hE : EisContinues V Φ)
    (ha : ∀ g, AnalyticOnNhd ℂ (eisSer V Φ g) (rightOf (V.rank / 2))) (hreg : ∀ s₀, ∃ k, EisRegularAt V Φ s₀ k)
    {f₁ f₂ : GA D V → ℂ} (h₁ : GlobalTheory.Grow.RapidDec V f₁) (h₂ : GlobalTheory.Grow.RapidDec V f₂)
    (hZ : IsZetaFamily V μ m Φ f₁ f₂) : ZetaContinues V μ m Φ f₁ f₂ := by
  obtain ⟨C', c, hio⟩ := GlobalTheory.T.exists_height_doublingEmbedding_le_pow_mul_heights D V
  have key : ∀ (H : ℂ → GA D (dblSp V) → ℂ) (z : ℂ) (r : ℝ), 0 < r →
      (∀ s ∈ ball z r, LeftInv (GQ (dblSp V)) (H s)) →
      (∀ g, DifferentiableOn ℂ (H · g) (ball z r)) →
      ContinuousOn (fun x : ℂ × GA D (dblSp V) => H x.1 x.2) (ball z r ×ˢ univ) →
      (∃ (C : ℝ) (N : ℕ), ∀ s ∈ ball z r, ∀ g, ‖H s g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) →
      (∀ s ∈ ball z r, DblConv V μ m (H s) f₁ f₂) ∧
        DifferentiableOn ℂ (fun s => dblInt V μ m (H s) f₁ f₂) (ball z r) := by
    rintro H z r hr hinv hd hc ⟨C, N, hb⟩
    obtain ⟨bound, hbi, hbd⟩ := GlobalTheory.T.exists_integrable_bound_doubling_integrand_quotient D V μ m hm f₁ f₂ h₁ h₂ C' c hio C N
    have hcont : ∀ s ∈ ball z r, Continuous (H s) := fun s hs =>
      hc.comp_continuous (f := fun g => (s, g)) (by fun_prop) fun g => ⟨hs, trivial⟩
    have hli : ∀ s ∈ ball z r, LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ (H s) f₁ f₂) := fun s hs =>
      leftInv_dblIntegrand hμ (hinv s hs) h₁.1 h₂.1
    have hmeas : ∀ s ∈ ball z r, AEStronglyMeasurable (dblIntegrandQ V μ (H s) f₁ f₂)
        ((autMeasure V m).prod (autMeasure V m)) := by
      intro s hs
      have e' : dblIntegrandQ V μ (H s) f₁ f₂ =
          dblIntegrand V μ (H s) f₁ f₂ ∘ Prod.map (sec (GQ V)) (sec (GQ V)) :=
        funext fun q => (congrArg _ (Prod.ext (mk_sec q.1) (mk_sec q.2)).symm).trans (dblIntegrandQ_mk (hli s hs) _ _)
      rw [e']
      exact ((continuous_dblIntegrand hμ (hcont s hs) h₁.continuous h₂.continuous).measurable.comp
        (measurableEmbedding_sec.measurable.prodMap measurableEmbedding_sec.measurable)).aestronglyMeasurable
    refine ⟨fun s hs => ⟨hli s hs, hbi.mono' (hmeas s hs) (ae_of_all _ fun q => hbd (H s) (hinv s hs) (hb s hs) q)⟩, ?_⟩
    have := GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated
      (μ := (autMeasure V m).prod (autMeasure V m)) (F := fun q s => dblIntegrandQ V μ (H s) f₁ f₂ q)
      (isOpen_ball (x := z) (ε := r)) hmeas
      (ae_of_all _ fun q => by
        simp only [dblIntegrandQ, dblIntegrand]
        exact (((hd _).mul_const _).mul_const _).mul_const _)
      fun x hx => ⟨ball z r, isOpen_ball.mem_nhds hx, bound, hbi,
        ae_of_all _ fun q y hy => hbd (H y) (hinv y hy) (hb y hy) q⟩
    exact this.1
  have hinvE : ∀ s, LeftInv (GQ (dblSp V)) (eisCont V Φ s) := fun s => hE.1.leftInv_eisLaurent s 0
  set Z : ℂ → ℂ := fun s => dblInt V μ m (eisCont V Φ s) f₁ f₂ with hZdef
  have hmer : ∀ s₁, MeromorphicAt Z s₁ := by
    intro s₁
    obtain ⟨k, r, H, hr, e, hd, hc, C, N, hb⟩ := hreg s₁
    have hinvH : ∀ s ∈ ball s₁ r, LeftInv (GQ (dblSp V)) (H s) := by
      intro s hs γ hγ g
      rcases eq_or_ne s s₁ with rfl | h0
      · have t1 := ((hd (γ * g)).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := {s}ᶜ))
        have t2 := ((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
          (nhdsWithin_le_nhds (s := {s}ᶜ))
        refine tendsto_nhds_unique t1 (t2.congr' ?_)
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s hr)] with w h1 h2
        rw [e w h2 h1, e w h2 h1, hinvE w γ hγ g]
      · rw [e s hs h0, e s hs h0, hinvE s γ hγ g]
    have han : AnalyticAt ℂ (fun s => dblInt V μ m (H s) f₁ f₂) s₁ :=
      (key H s₁ r hr hinvH hd hc ⟨C, N, hb⟩).2.analyticAt (ball_mem_nhds _ hr)
    have hm1 : MeromorphicAt (fun s => ((s - s₁) ^ k)⁻¹ * dblInt V μ m (H s) f₁ f₂) s₁ := by
      have : MeromorphicAt (fun s : ℂ => s - s₁) s₁ := (MeromorphicAt.id s₁).sub (MeromorphicAt.const _ _)
      exact (this.pow k).inv.mul han.meromorphicAt
    refine hm1.congr ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₁ hr)] with w h1 h2
    have e1 : eisCont V Φ w = ((w - s₁) ^ k)⁻¹ • H w := by
      funext g
      rw [Pi.smul_apply, e w h2 h1 g, smul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero _ (sub_ne_zero.2 h1)), one_mul]
    have e2 := dblInt_smul (V := V) (μ := μ) (m := m) (E := H w) (f₁ := f₁) (f₂ := f₂) ((w - s₁) ^ k)⁻¹ 1 1
    simp only [one_smul, map_one, mul_one] at e2
    simp only [Z, e1, e2]
  have hext : IsMerExt (zeta V μ m Φ f₁ f₂) univ Z := by
    refine ⟨isRightDomain_univ, fun s _ => hmer s, (V.rank : ℝ) / 2, fun s hs => ?_⟩
    have : eisCont V Φ s = eis V (Φ s) := funext fun g => eqOn_cont (ha g) hs
    simp only [Z, zeta, this]
  exact ⟨hZ, Z, hext⟩

end GlobalTheory.Eis
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

namespace GlobalTheory.TwU.NearOne

theorem congAt_eventually_nhds_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n N : ℕ) (P : HeightOneSpectrum (𝓞 E)), letI := Formalism.L2.Col.rlt_top (F := F) (E := E); ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, GlobalTheory.TwU.CongAt P N u := by
  intro F E _ _ _ _ _ n N P
  letI : TopologicalSpace (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Formalism.L2.Col.rlt_top (F := F) (E := E)
  haveI : IsTopologicalRing (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
  show ∀ᶠ u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ a b, _
  refine Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => ?_
  have hop : IsOpen ((fun y : E ⊗[F] FiniteAdeleRing (𝓞 F) F =>
      Formalism.L2.Col.iA F E (((Formalism.L2.Col.qOf P : ℕ) : E) ^ N)⁻¹ * y) ⁻¹'
      (Formalism.L2.Herm.intAf F E : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) :=
    Formalism.L2.Col.rlt_isOpen_intAf.preimage (continuous_const.mul continuous_id)
  have h0 : (0 : E ⊗[F] FiniteAdeleRing (𝓞 F) F) ∈ (fun y : E ⊗[F] FiniteAdeleRing (𝓞 F) F =>
      Formalism.L2.Col.iA F E (((Formalism.L2.Col.qOf P : ℕ) : E) ^ N)⁻¹ * y) ⁻¹'
      (Formalism.L2.Herm.intAf F E : Set (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
    simp only [Set.mem_preimage, mul_zero]
    exact zero_mem _
  have hcont : Continuous fun u : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) =>
      (u : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b -
        (1 : Matrix (Fin n) (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b :=
    (Units.continuous_val.matrix_elem a b).sub continuous_const
  have ht := hcont.tendsto' 1 0 (by simp)
  filter_upwards [ht (hop.mem_nhds h0)] with u hu
  refine ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
  simpa [Matrix.sub_apply] using hu

end GlobalTheory.TwU.NearOne
end
