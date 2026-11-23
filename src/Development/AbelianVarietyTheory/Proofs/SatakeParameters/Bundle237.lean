module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle228
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle227
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIso
public import Formalism.LocalRingCardinality.DataForced
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle229
public import Formalism.LocalToGlobal.Columns.Bundle023
public import Formalism.LocalToGlobal.Columns.Bundle024
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepDatumLawK1DepthTwiceM
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
public import Formalism.LocalToGlobal.KernelLattices.Bundle003
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle015
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntEasy
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle112
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle210
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntPull
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.FinalEq
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle230
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle231
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RamificationIdxEqOneAndInertiaDegEqOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle002
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle013
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL
theorem _root_.GlobalTheory.T.exists_algebraicWeight_definiteUnitaryAutRep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∃ lam : (E →+* ℂ) → DomWeight a, ∀ τ, HasWeightAt U τ (lam τ) := by
  first | exact @GlobalTheory.Cong.exists_weight_of_isAutRepU | exact GlobalTheory.Cong.exists_weight_of_isAutRepU | (intros; apply GlobalTheory.Cong.exists_weight_of_isAutRepU <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

theorem _root_.GlobalTheory.T.autRepDefiniteUnitary_spanned_by_split_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)), IsAutRepU U → ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ σ : SmIrr (GL (Fin a) (w.adicCompletion E)), IsCompAlong U (locU a w) ((cLoc w).comp (locU a w).subtype) σ.ρ → ∀ φ ∈ U, φ ∈ ⨆ (f : {f : σ.V →ₗ[ℂ] (UA E a → ℂ) // (∀ v, f v ∈ U) ∧ ∀ (x : locU a w) v, f (σ.ρ (cLoc w x) v) = RU E a x (f v)}), LinearMap.range f.1 := by
  first | (exact @GlobalTheory.Cong.span_comp_of_split) | (exact GlobalTheory.Cong.span_comp_of_split) | (intros; apply GlobalTheory.Cong.span_comp_of_split  <;> assumption)
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published
open Polynomial

namespace GlobalTheory.PlaceNormDec

theorem exists_place_normV_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Q : GlobalTheory.RealGal.QCM E Ω) (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w → _root_.ReciprocityTheory.Gal.Dec (F := E) A ≤ (UpperTheory.V.Af.Bc.res E Ω ↥Q.K).range → ∃ w' : HeightOneSpectrum (𝓞 ↥Q.K), w'.under (𝓞 E) = w ∧ _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w' ∧ normV w' = normV w := by
  intro E Ω _ _ _ _ _ Q w A hA hD
  obtain ⟨w', hw', i, hi⟩ := GlobalTheory.PlaceIsoDec.exists_placeIso_of_dec_le_range E Ω (↥Q.K) w A hA hD
  refine ⟨w', ?_, hw', ?_⟩
  · have hl := GlobalTheory.PlaceIsoDec.liesOver_of_isPlaceOver hA hw'
    exact HeightOneSpectrum.ext hl.over.symm
  · obtain ⟨c, -, -, hq, -⟩ := GlobalTheory.WeilTransport.weil_equiv E Ω A w hA (↥Q.K) Ω A w' hw' (RingEquiv.refl Ω) (algebraMap E ↥Q.K) i hi
    exact hq

end GlobalTheory.PlaceNormDec
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
open Formalism.MainNotions.G (HH)

theorem _root_.GlobalTheory.T.inertiaInvolution_realPlacePairs : ∀ (D : D7) (p : ℕ) [Fact p.Prime], p = D.host.d → ∀ ι : ℂ ≃+* ℂ_[p], ∃ (cE s : D.host.E ≃+* D.host.E) (δ : D.host.E), (∀ y, cE y = D.host.conj y) ∧ δ ^ 2 = -(p : D.host.E) ∧ cE δ = -δ ∧ s δ = -δ ∧ (∀ y, s (s y) = y) ∧ (∀ y, s (cE y) = cE (s y)) ∧ Function.Injective (fun z : Bool × HH D => TaylorLogMetric.embT D (tauPl D z)) ∧ (∀ τ ρ, TaylorLogMetric.embT D τ δ = TaylorLogMetric.embT D ρ δ) ∧ (∀ (t : HH D) y, TaylorLogMetric.embT D (tauPl D (true, t)) y = TaylorLogMetric.embT D (tauPl D (false, t)) (s (cE y))) ∧ (∀ τ y, s y = y → ι (TaylorLogMetric.embT D τ y) ∈ Formalism.L2.Th1.CM.MaximalUnramifiedExtension p) ∧ Function.Bijective (tauPl D) ∧ ∀ t : HH D, TaylorLogMetric.tauSg D (tauPl D (false, t)) = tauPl D (true, t) ∧ TaylorLogMetric.tauSg D (tauPl D (true, t)) = tauPl D (false, t) := by
  first | exact @GlobalTheory.InertiaPairs.inertia_pairs | exact GlobalTheory.InertiaPairs.inertia_pairs | (intros; apply GlobalTheory.InertiaPairs.inertia_pairs <;> assumption)
end

section

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker NumberField IsDedekindDomain Classical

theorem _root_.GlobalTheory.T.twTt_k1Depth_twice_m : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) {m2 : ℕ} (w : rowSG Pr sel mu) (hw : w.1 ∉ Pr.vGs) (κ' : ↥(GLint X.E (R.N (m2 + 1 + 1)) w.1)) (hc' : κ'⁻¹ ∈ (twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).H) (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y₁ : Sp X.E (R.N (m2 + 1))), R.m = m2 + 2 → cst.Ok → ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2 → 2 * cst.M ≤ cst.D w → 2 * cst.M ≤ twTopDepth R → ((qOf w.1 : X.E) ^ cst.M) • y₁ ∈ stdAt X.E (R.N (m2 + 1)) w.1 → rhoT Ch sel mu (m2 + 1) w (LinearEquiv.det κ'.1 : X.Eˣ) * topDat Ch sel mu cst (m2 + 1) w (κ'.1.symm.toLinearMap ∘ₗ y) y₁ = (((twTt (R := R) sel mu (m2 + 1 + 1) ⟨w.1, (Finset.mem_union.mp w.2).resolve_left hw⟩).lam ⟨κ'⁻¹, hc'⟩ : X.Kˣ) : X.K) * topDat Ch sel mu cst (m2 + 1) w y y₁ := by
  first | exact @GlobalTheory.lastStepDatumLaw_K1Depth_twiceM | exact GlobalTheory.lastStepDatumLaw_K1Depth_twiceM | (intros; apply GlobalTheory.lastStepDatumLaw_K1Depth_twiceM <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.Col Formalism.L2.DIV Formalism.HermitianLatticesTheory NumberField IsDedekindDomain Classical

namespace GlobalTheory.BadNoConj

theorem sall_noConj_ok : ∀ {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S), X.Ok → Pr.Ok → IsSel X sel → ∀ u : Pr.Word, Pr.T u ∈ S → (∀ i, Pr.g i ∈ S) → ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u := by
  intro X Pr sel S mu hX hPr hsel u hT hg
  have hsplit : ∀ P, P ∈ Sall sel mu u ↔ P ∈ Pr.vT u ∪ Pr.vGs ∨ P ∈ QE sel (mu : Chr X.F X.E X.K) := by
    intro P
    unfold Sall rowSG uSG
    simp only [Finset.mem_union]
    tauto
  have hmix : ∀ P, P ∈ Pr.vT u ∪ Pr.vGs → conjPrime₂ P ∉ QE sel (mu : Chr X.F X.E X.K) := by
    intro P hP hQ
    obtain ⟨π, p, hπ, -, hn, hp, hk⟩ := bad_gen hPr u hP
    have hpS : p ∈ S := by
      rcases hk with ⟨e, -⟩ | ⟨j, e, -⟩
      · rw [e]; exact hT
      · rw [e]; exact hg j
    refine qe_nat_notMem mu hsel hp hpS hQ ?_
    rw [mem_conjP, map_natCast]
    exact hn ▸ P.asIdeal.mul_mem_right _ hπ
  intro P hP hP'
  rcases (hsplit P).1 hP with h | h <;> rcases (hsplit _).1 hP' with h' | h'
  · exact tg_noConj hPr u P h h'
  · exact hmix P h h'
  · exact hmix (conjPrime₂ P) h' (by rw [conjP_twice]; exact h)
  · exact GlobalTheory.NormOneUnit.conjP_notMem_QE mu hX hsel h h'

end GlobalTheory.BadNoConj
end

section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.ThLoc.AllPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem tPull_comp (γ₁ γ₂ : Matrix (Fin N) (Fin N) D.host.E) (γ₁' γ₂' : Matrix (Fin N') (Fin N') D.host.E)
    (z : TaylorLogMetric.VC D N N') :
    Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) γ₂ γ₂' (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) γ₁ γ₁' z) =
      Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ₁ * γ₂) (γ₁' * γ₂') z := by
  funext τ
  show (Matrix.conjTranspose (γ₂'.map (TaylorLogMetric.embT D τ)) *
      (Matrix.conjTranspose (γ₁'.map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) * γ₁.map (TaylorLogMetric.embT D τ)) *
      γ₂.map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ) =
    (Matrix.conjTranspose ((γ₁' * γ₂').map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) * (γ₁ * γ₂).map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ)
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem tPull_one (z : TaylorLogMetric.VC D N N') :
    Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (1 : Matrix (Fin N) (Fin N) D.host.E)
      (1 : Matrix (Fin N') (Fin N') D.host.E) z = z := by
  funext τ
  show (Matrix.conjTranspose ((1 : Matrix (Fin N') (Fin N') D.host.E).map (TaylorLogMetric.embT D τ)) * Matrix.of (z τ) *
      (1 : Matrix (Fin N) (Fin N) D.host.E).map (TaylorLogMetric.embT D τ) : Matrix _ _ ℂ) = z τ
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.conjTranspose_one,
    Matrix.one_mul, Matrix.mul_one]
  rfl

theorem smulLat_star_smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) (hγ : star γ * γ = 1)
    (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) :
    SDLat.smulLat (star γ) (SDLat.smulLat γ M) = M := by
  unfold SDLat.smulLat
  rw [← Submodule.map_comp]
  have h : ((Matrix.toLin' (star γ)).restrictScalars (𝓞 D.host.E)).comp ((Matrix.toLin' γ).restrictScalars (𝓞 D.host.E)) =
      LinearMap.id := by
    refine LinearMap.ext fun x => ?_
    show Matrix.toLin' (star γ) (Matrix.toLin' γ x) = x
    rw [← Matrix.toLin'_mul_apply, hγ, Matrix.toLin'_one, LinearMap.id_apply]
  rw [h, Submodule.map_id]

theorem mem_La_smulLat_iff (γ : Matrix.unitaryGroup (Fin N) D.host.E) (γ' : Matrix.unitaryGroup (Fin N') D.host.E)
    (M : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (M' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (x : TaylorLogMetric.VC D N N') :
    x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
        (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M') ↔
      Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
        (γ' : Matrix (Fin N') (Fin N') D.host.E) x ∈ TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) M M' := by
  have h1 : star (γ : Matrix (Fin N) (Fin N) D.host.E) * γ = 1 := Matrix.mem_unitaryGroup_iff'.mp γ.2
  have h1' : star (γ' : Matrix (Fin N') (Fin N') D.host.E) * γ' = 1 := Matrix.mem_unitaryGroup_iff'.mp γ'.2
  have h2 : (γ : Matrix (Fin N) (Fin N) D.host.E) * star (γ : Matrix (Fin N) (Fin N) D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ.2
  have h2' : (γ' : Matrix (Fin N') (Fin N') D.host.E) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 :=
    Matrix.mem_unitaryGroup_iff.mp γ'.2
  constructor
  · intro hx
    exact Formalism.L2.KerInert.ie_La_pull cc δ _ _ h1' M M' hx
  · intro hx
    have h3 : star (star (γ' : Matrix (Fin N') (Fin N') D.host.E)) * star (γ' : Matrix (Fin N') (Fin N') D.host.E) = 1 := by
      rw [star_star]; exact h2'
    have h := Formalism.L2.KerInert.ie_La_pull cc δ (star (γ : Matrix (Fin N) (Fin N) D.host.E))
      (star (γ' : Matrix (Fin N') (Fin N') D.host.E)) h3 (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) M)
      (SDLat.smulLat (γ' : Matrix (Fin N') (Fin N') D.host.E) M')
    rw [smulLat_star_smulLat _ h1, smulLat_star_smulLat _ h1'] at h
    have h4 := h hx
    rw [AddSubgroup.mem_comap] at h4
    have e : Formalism.L2.KerInert.ieTPullHom cc δ (star (γ : Matrix (Fin N) (Fin N) D.host.E))
        (star (γ' : Matrix (Fin N') (Fin N') D.host.E))
        (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
          (γ' : Matrix (Fin N') (Fin N') D.host.E) x) = x := by
      show Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ x) = x
      rw [tPull_comp, h2, h2', tPull_one]
    rw [e] at h4
    exact h4

end GlobalTheory.ThLoc.AllPlaces

namespace GlobalTheory.ThLoc.AllPlaces

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem formV_eq_Hf (u v : TaylorLogMetric.VC D N N') :
    formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N' u v = TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) u v := rfl

def tPullLin (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) : TaylorLogMetric.VC D N N' →ₗ[ℂ] TaylorLogMetric.VC D N N' where
  toFun := Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) γ γ'
  map_add' := Formalism.L2.KerInert.ie_tPull_add cc δ γ γ'
  map_smul' := Formalism.L2.KerInert.ie_tPull_smul cc δ γ γ'

def tPullEquiv (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (γ : Matrix.unitaryGroup (Fin N) D.host.E)
    (γ' : Matrix.unitaryGroup (Fin N') D.host.E) : TaylorLogMetric.VC D N N' ≃ₗ[ℂ] TaylorLogMetric.VC D N N' :=
  LinearEquiv.ofLinearMap (tPullLin cc δ (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E))
    (tPullLin cc δ (star (γ : Matrix (Fin N) (Fin N) D.host.E)) (star (γ' : Matrix (Fin N') (Fin N') D.host.E)))
    (LinearMap.ext fun z => by
      show Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ z) = z
      rw [tPull_comp, Matrix.mem_unitaryGroup_iff'.mp γ.2, Matrix.mem_unitaryGroup_iff'.mp γ'.2, tPull_one])
    (LinearMap.ext fun z => by
      show Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ (Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) _ _ z) = z
      rw [tPull_comp, Matrix.mem_unitaryGroup_iff.mp γ.2, Matrix.mem_unitaryGroup_iff.mp γ'.2, tPull_one])

end GlobalTheory.ThLoc.AllPlaces


open GlobalTheory.ThLoc.AllPlaces in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem GlobalTheory.ThLoc.latAt_all : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ (X : Fields) (s : Seam D X), s.Ok → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), TaylorLogMetric.admitted D N N' L L' → ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹) (s.laF B.tor L L') (fun z => B.eNat χ N N' L L' (s.flatV N N' z)) p ι := by
  intro D cc δ hcc hδ B χ hχ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' L L' hA p _ ι
  have hp : p.Prime := Fact.out
  have hCM : PI.UG.IsCMUnram D.host.E := D.sp.cm.cmUnram
  obtain ⟨hN, hN', hL, hL'⟩ := hA
  obtain ⟨γ, M, hM, hEq, hLM⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N L hL
  obtain ⟨γ', M', hM', hEq', hLM'⟩ := Formalism.L2.KerInert.wa_main Formalism.L2.KerInert.weak_approximation_places hCM p hp N' L' hL'
  have hAM : TaylorLogMetric.admitted D N N' M M' := ⟨hN, hN', hM, hM'⟩
  have hAL : TaylorLogMetric.admitted D N N' L L' := ⟨hN, hN', hL, hL'⟩
  have hStd := GlobalTheory.T.normalisedThetaFamily_normalised_at_standardPrime D cc δ hcc hδ B χ hχ X s hs a₀ b₀ c₀ ha hd lam hlam hcm hlat N N' M M' hAM p ι hEq hEq'

  let φ : (DVar X.Tau N N' → ℂ) ≃ₗ[ℂ] (DVar X.Tau N N' → ℂ) :=
    (s.flatV N N').trans ((tPullEquiv cc δ γ γ').trans (s.flatV N N').symm)
  have hφ : ∀ z, s.flatV N N' (φ z) = Formalism.L2.KerInert.tPull D (TaylorLogMetric.tor0 D cc δ) (γ : Matrix (Fin N) (Fin N) D.host.E)
      (γ' : Matrix (Fin N') (Fin N') D.host.E) (s.flatV N N' z) := fun z => by
    show s.flatV N N' ((s.flatV N N').symm (tPullEquiv cc δ γ γ' (s.flatV N N' z))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hI : IsIsom (matH (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹))
      (matH (Formalism.L2.AlgTh.hSc X.Tau N N' (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹)) (φ : (DVar X.Tau N N' → ℂ) →ₗ[ℂ] _) := by
    intro x y
    show matH _ (φ x) (φ y) = _
    rw [KS.Lat.form_flat s, KS.Lat.form_flat s, hφ, hφ, formV_eq_Hf, formV_eq_Hf,
      Formalism.L2.KerInert.PullbackComparison.Hf_tPull cc δ _ _ (Matrix.mem_unitaryGroup_iff.mp γ.2) (Matrix.mem_unitaryGroup_iff.mp γ'.2)]
  have hloc := GlobalTheory.T.localNormalisation_transport_isometry a₀ b₀ D.host.d ha hd lam hlam (DVar X.Tau N N') _ (s.laF B.tor M M')
    (fun z => B.eNat χ N N' M M' (s.flatV N N' z)) p ι φ hI hStd.locNorm
  have hΛ : (s.laF B.tor M M').comap (φ : (DVar X.Tau N N' → ℂ) →ₗ[ℂ] _).toAddMonoidHom = s.laF B.tor L L' := by
    ext x
    show s.flatV N N' (φ x) ∈ TaylorLogMetric.La D B.tor M M' ↔ s.flatV N N' x ∈ TaylorLogMetric.La D B.tor L L'
    rw [hφ, hLM, hLM']
    exact (mem_La_smulLat_iff γ γ' M M' _).symm
  have hθ : (fun z => B.eNat χ N N' M M' (s.flatV N N' (φ z))) = fun z => B.eNat χ N N' L L' (s.flatV N N' z) := by
    funext z
    rw [hφ, hLM, hLM']
    have h := (Formalism.L2.PairingIndexBounds.Eq.SqG.eulerProduct_eq_of_curve_ideal B hcc hδ χ hχ).1 N N' ⟨M, hM⟩ ⟨M', hM'⟩ hN hN' γ γ'
    exact congrFun h (s.flatV N N' z)
  rw [hΛ] at hloc
  simp only [hθ] at hloc
  exact ⟨hcm, KS.Lat.selfDual_laF s B hcc hδ hAL, fun x hx => KS.Lat.theta_laF s B (KS.Lat.odd_of_cmOK hcm) hx,
    KS.Lat.eNat_laF s B hcc hδ χ hAL, hloc⟩
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

theorem _root_.GlobalTheory.T.lastStep_data_integralAwayFrom_levels : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), ∀ u μ p Yb d x, Yb ∈ ybSet t.sel (t.tup μ) (t.cst μ) p.deco.1.N → IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl2 (R := D.R) (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) t.m2 p Yb d x)) := by
  first | exact @GlobalTheory.CplTwoInt.xiCpl2_intOff_tied | exact GlobalTheory.CplTwoInt.xiCpl2_intOff_tied | (intros; apply GlobalTheory.CplTwoInt.xiCpl2_intOff_tied <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

theorem _root_.GlobalTheory.T.local_model_bound_place_over_second_embedding : ∀ (D : D7) (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (L : SizeData₂ D) (hT : GatTies D) (X : Inst D L) (Y : LatInst D) (K : Consts) (ce : ErrC) (E : OrbitPlaces.Ent D), LatTied hT X Y → FillsAll hT Y → OrbitPlaces.OrbitLetterBoundsAll 11 1 → OrbitPlaces.Shape D L X E → OrbitPlaces.CLarge 11 1 K ce → ((D.what₂.places.resChar w) : ℝ) ≤ L.sc.X'' D.R.n → ∀ (Lv : Levels (Y.Fl u w hg)) (Ch : Chain Lv) (std : _) (vp : _) (unif : _) (eO : _) (eO_spec : _) (dG : _) (dG_spec : _) (om : _) (Y5 : FormalGroupSystem.Pend (FormalGroupSystem.Sys.mk (D.gat u w hg) (Y.Fl u w hg) Lv Ch std vp unif eO eO_spec dG dG_spec om)), BeProp (D.what₂.places.resChar w) Y5.be → ∀ (v : Fin (D.gat u w hg).P.nV) (t : HH D), (D.gat u w hg).P.n' v = nP D (D.what₂.places.resChar w) → (∀ s : Fin ((D.gat u w hg).P.n' v), hT.gat_pos u w hg ⟨v, s⟩ = tauPl D (posPl D (D.what₂.places.resChar w) (true, t) s.val)) → ∀ i < D.R.m, Y5.LowAt i v (FOrb D (i + 1) (D.what₂.places.resChar w) (true, t) - OrbitPlaces.errF L K ce (i + 1) (D.what₂.places.resChar w) (true, t)) := by
  first | exact @GlobalTheory.TwU.LowF.lowAt_F | exact GlobalTheory.TwU.LowF.lowAt_F | (intros; apply GlobalTheory.TwU.LowF.lowAt_F <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.finrank_maximal_real_even : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] (Q : GlobalTheory.RealGal.QCM E Ω), Even (Module.finrank ℚ (maximalRealSubfield Q.K)) := by
  first | exact @GlobalTheory.RealGal.QCM.even_finrank_maximalRealSubfield | exact GlobalTheory.RealGal.QCM.even_finrank_maximalRealSubfield | (intros; apply GlobalTheory.RealGal.QCM.even_finrank_maximalRealSubfield <;> assumption)
end

section

open NumberField

theorem _root_.GlobalTheory.T.exists_cmQuadratic_adjoin_sqrt_neg_nat : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (p : ℕ), 0 < p → ∀ δ : Ω, δ ^ 2 = -(p : Ω) → δ ∉ Set.range (algebraMap E Ω) → ∃ Q : GlobalTheory.RealGal.QCM E Ω, Q.K = IntermediateField.adjoin E {δ} := by
  first | exact @GlobalTheory.CMSqrtNeg.exists_qcm_adjoin_sqrt_neg | exact GlobalTheory.CMSqrtNeg.exists_qcm_adjoin_sqrt_neg | (intros; apply GlobalTheory.CMSqrtNeg.exists_qcm_adjoin_sqrt_neg <;> assumption)
end
