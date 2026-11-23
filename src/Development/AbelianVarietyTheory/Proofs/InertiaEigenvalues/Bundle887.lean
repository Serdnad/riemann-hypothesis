module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle854
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.BaseIntSet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle843
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumPairUniformLevelBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle876
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle008
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle857
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle325
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle778
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle643
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle873
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle510
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle596
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle815
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicMatrixExistsPrimePowClearsDenominatorsOver
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.vacuum_pair_uniform_level_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∃ K : ℕ, ∀ (M : ℕ) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (O : Subring ℂ) (Φ φ : WO V W → ℂ), M ≠ 0 → Nat.Coprime M (GlobalTheory.Tow.badN D) → IsIdemSum e P → (∀ PP ∈ P, ((M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → zeta M ∈ O → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.IsLevelFn (cA D e) (latO V W ΛV ΛW fun _ => True) M Φ → (∀ x, Φ x ∈ O) → IsThetaAt ψ (symplO V W) (heisO ψ V W) (cA D e) (latO V W ΛV ΛW fun _ => True) 1 f₀ Φ φ → ((M : ℂ) ^ K) • φ ∈ trSp ψ V W ΛV ΛW f₀ e M O := by
  first | exact @GlobalTheory.LevelFourier.smul_mem_trSp | exact GlobalTheory.LevelFourier.smul_mem_trSp | (intros; apply GlobalTheory.LevelFourier.smul_mem_trSp <;> assumption)
end

section

open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LevelSeries


theorem _root_.GlobalTheory.T.span_finiteTranslates_vacuum_thetaFockVacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ →
    ∀ (e : AE D) (M : ℕ) (O₁ : Subring ℂ), M ≠ 0 → ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O₁,
      IsThetaFunO ψ V W f ∧ ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO 1 (sW τ)) f := by
  first | exact @GlobalTheory.LevelSeries.trSp_theta_fock | exact GlobalTheory.LevelSeries.trSp_theta_fock | (intros; apply GlobalTheory.LevelSeries.trSp_theta_fock <;> assumption)
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

namespace GlobalTheory.FockDerivP

def frONB {D : D7} {V : HSp D} (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hB : ∀ τ, IsONBasis (gramAt D V τ) 1 (B τ) V.rank) : GlobalTheory.ChainFr.Fr V where
  ε _ _ := true
  fr τ := (B τ)⁻¹
  fr_unit τ := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_nonsing_inv_det _
    ((Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hB τ))))
  fr_gram τ := by
    have hu : IsUnit (B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hB τ))
    obtain ⟨ε, hε, hG, -⟩ := hB τ
    have h1 : (fun a => (ε a : ℂ)) = fun _ => 1 := by
      funext a
      rcases hε a with h | h
      · rw [h.1]; simp
      · exact absurd h.2 (not_le.2 a.2)
    rw [h1, Matrix.diagonal_one] at hG
    have hJ : Formalism.REAL.Jm (fun _ : Fin V.rank => true) = 1 := by
      simp [Formalism.REAL.Jm]
    have h2 : ((B τ)⁻¹)ᴴ * (B τ)ᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hu, Matrix.conjTranspose_one]
    calc ((B τ)⁻¹)ᴴ * Formalism.REAL.Jm (fun _ : Fin V.rank => true) * (B τ)⁻¹
        = ((B τ)⁻¹)ᴴ * ((B τ)ᴴ * gramAt D V τ * B τ) * (B τ)⁻¹ := by rw [hJ, hG]
      _ = (((B τ)⁻¹)ᴴ * (B τ)ᴴ) * gramAt D V τ * (B τ * (B τ)⁻¹) := by simp only [Matrix.mul_assoc]
      _ = gramAt D V τ := by rw [h2, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]

theorem frONB_cart {D : D7} {V : HSp D} (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hB : ∀ τ, IsONBasis (gramAt D V τ) 1 (B τ) V.rank) : (frONB B hB).cart = fun _ => 1 := by
  funext τ
  have hu : IsUnit (B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hB τ))
  have hJ : Formalism.REAL.Jm (fun _ : Fin V.rank => true) = 1 := by
    simp [Formalism.REAL.Jm]
  show ((B τ)⁻¹)⁻¹ * Formalism.REAL.Jm (fun _ : Fin V.rank => true) * (B τ)⁻¹ = 1
  rw [hJ, Matrix.mul_one, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_nonsing_inv _ hu]

theorem frONB_onb {D : D7} {V : HSp D} (B : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hB : ∀ τ, IsONBasis (gramAt D V τ) 1 (B τ) V.rank) : (frONB B hB).onb = B := by
  funext τ
  have hu : IsUnit (B τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (GlobalTheory.ConjTwist.isUnit_of_isONBasis (hB τ))
  show ((B τ)⁻¹)⁻¹ = B τ
  rw [Matrix.nonsing_inv_nonsing_inv _ hu]

theorem hasDerivAt_ptP : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∃ a : ℂ, ∀ (P : PolF D (Wc D i).rank (Vc D i).rank) (z : WO (Vc D i) (Wc D i)), HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t (fockT τ (fun _ : Fin (Vc D i).rank => true) (fun j : Fin (Wc D i).rank => decide ((j : ℕ) < pS D i τ)) ((R.MW i (sg0 D A)).fr τ * Y * ((R.MW i (sg0 D A)).fr τ)⁻¹) P + a • P) z) 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t τ Y hY
  have hC := hG.core
  have hB := hC.models.BV i
  set AV := frONB (R.BV i) hB with hAV
  set BW := GlobalTheory.ChainFr.Fr.ofModel (R.MW i (sg0 D A)) with hBW
  have hcA := frONB_cart (R.BV i) hB
  have hoA := frONB_onb (R.BV i) hB
  obtain ⟨hf, hv, -⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  have hvac : GlobalTheory.ChainFr.IsVacF R.ψ R.θ AV BW (R.vP i t) := by
    refine ⟨hf, fun ρ => ?_⟩
    rw [hcA]
    exact hv ρ
  have hI := GlobalTheory.PairInfTypes.infTypesAt D T R.toLevCh A.μ0 hC.lev i t τ
  have hAll := GlobalTheory.LieScalar.lieFockAll D (Vc D i) (Wc D i) AV BW R.θ R.ψ _ _ (R.ωP i t) (R.vP i t) τ _ _
    hC.models.inf (hC.thP.ωP i t) hI.chiV hI.chiW hvac
  refine ⟨((-eS D i τ : ℚ) : ℂ) * Y.trace, fun P z => ?_⟩
  have hpt : GlobalTheory.ChainFr.ptF R.ψ R.θ AV BW (R.vP i t) = R.ptP i t := by
    unfold GlobalTheory.ChainFr.ptF RealDat.ptP
    rw [hcA, hoA]
    rfl
  have hε : BW.ε τ = fun j : Fin (Wc D i).rank => decide ((j : ℕ) < pS D i τ) := by
    funext j
    exact hC.models.order i τ j
  have h := hAll.2 Y hY P z
  rw [hpt, hε] at h
  exact h

end GlobalTheory.FockDerivP

end
end

section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem theoremB_closing : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), ∀ C : ℝ, (320 : ℝ) ≤ C → ArcLiftingSetup.aux₃ D HW F C := by
  intro hBK hTD hEC D HW F Cm C hC
  have h22 : CrystallineLiftingBounds.adm22 D HW F := GlobalTheory.FontaineIneq.one_place_admissible_of_gap_constant_le D HW F
  have h23 : CrystallineLiftingBounds.adm23 D HW F := (GlobalTheory.jumps_exact_adm D HW F).1
  have hN1 : Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  have hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F := GlobalTheory.T.letterConditionGlobal_of_N1used D HW F Cm hN1
  exact GlobalTheory.T.theoremB_of_localFilteredHypotheses D HW F Cm C 10 23 32 32 8 hC h22 h23 hC4 (GlobalTheory.T.localLifting_theoremB_hypotheses_admitted hBK hTD hEC D HW F Cm)

end GlobalTheory
end

section

open NumberField IsDedekindDomain


theorem _root_.GlobalTheory.T.adelicMatrix_exists_prime_pow_clears_denominators_over : ∀ {E : Type} [Field E] [NumberField E] (p : ℕ), p.Prime → ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)), ∃ c : ℕ, ∀ d : ℕ, c ≤ d → ∀ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal → ∀ i j, Valued.v ((((p ^ d : ℕ) : FiniteAdeleRing (𝓞 E) E) * A i j) Q) ≤ 1 := by
  first | exact @GlobalTheory.StdAtPrime.exists_pow_clears_denom_over | exact GlobalTheory.StdAtPrime.exists_pow_clears_denom_over | (intros; apply GlobalTheory.StdAtPrime.exists_pow_clears_denom_over <;> assumption)
end
