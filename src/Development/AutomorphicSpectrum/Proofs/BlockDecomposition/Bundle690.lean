module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle553
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle569
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle650
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle487
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle685
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle634
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle608
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureEulerProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle631
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle106
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle663
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle686
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle660
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.OneCoset
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle647
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle598
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetMultiplication
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDiagUnit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle667
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle669
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle676
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle687
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaGLMemIwGL
import GroundTheory.LocalFields.PadicLogSeries
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore

@[expose] public section

section

open scoped Classical

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.ConjSat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem locU_eq_of_under {w u : HeightOneSpectrum (𝓞 E)}
    (h : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : locU n u = locU n w := by
  simp only [locU, h]

abbrev flipGL (w : HeightOneSpectrum (𝓞 E)) :
    GL (Fin n) ((GlobalTheory.ThetaSatake.cw w).adicCompletion E) ≃* GL (Fin n) (w.adicCompletion E) :=
  GlobalTheory.LFun.ConjPlace.invT (GlobalTheory.ThetaSatake.cloc w) n

theorem flipGL_eq (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) ((GlobalTheory.ThetaSatake.cw w).adicCompletion E)) :
    flipGL w g = GlobalTheory.CuspRep.invT n _ (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g) :=
  Units.ext (Matrix.ext fun i j => GlobalTheory.LFun.ConjPlace.invT_val _ g i j)

theorem continuous_flipGL (w : HeightOneSpectrum (𝓞 E)) : Continuous (flipGL (n := n) w) := by
  have : (flipGL (n := n) w : _ → _) = fun g => GlobalTheory.CuspRep.invT n _ (GeneralLinearGroup.map (conjLoc (IsCMField.complexConj E).toRingEquiv w) g) :=
    funext (flipGL_eq w)
  rw [this]
  exact (GlobalTheory.SplitPts.continuous_invT _).comp
    (Continuous.units_map _ (continuous_id.matrix_map (conjLoc_spec _ w).1))

theorem cLoc_eq_flipGL (x : UA E n) (w : HeightOneSpectrum (𝓞 E)) :
    cLoc w x = flipGL w (cLoc (GlobalTheory.ThetaSatake.cw w) x) :=
  (GlobalTheory.BCT.LocCpt.cLoc_eq_invT x w).trans (flipGL_eq w _).symm

def flipIrr {w : HeightOneSpectrum (𝓞 E)} (σ : SmIrr (GLw n w)) : SmIrr (GLw n (GlobalTheory.ThetaSatake.cw w)) where
  V := σ.V
  ρ := σ.ρ.comp (flipGL w).toMonoidHom
  smooth v := (σ.smooth v).preimage (continuous_flipGL w)
  irred := GlobalTheory.ConjPairLoc.irred_comp _ _ (flipGL w).surjective σ.irred

theorem hasSatGL_flipIrr {w : HeightOneSpectrum (𝓞 E)} (σ : SmIrr (GLw n w)) {B : Multiset ℂˣ}
    (h : HasSatGL w σ.ρ B) : HasSatGL (GlobalTheory.ThetaSatake.cw w) (flipIrr σ).ρ (B.map (·⁻¹)) := by
  refine GlobalTheory.ThetaSatake.hasSatGL_of_invT (GlobalTheory.ThetaSatake.cloc w).symm (fun a => ?_)
    (GlobalTheory.ThetaSatake.absNorm_cw w) (LinearEquiv.refl ℂ σ.V) (fun g x => ?_) h
  · have := (conjLoc_spec (IsCMField.complexConj E).toRingEquiv w).2.2 ((GlobalTheory.ThetaSatake.cloc w).symm a)
    exact (this.symm.trans (congrArg _ ((GlobalTheory.ThetaSatake.cloc w).apply_symm_apply a)))
  · change σ.ρ (flipGL w ((flipGL w).symm g)) x = σ.ρ g x
    rw [MulEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.ConjSat


open GlobalTheory.CompanionTheory.ConjSat in
theorem GlobalTheory.CompanionTheory.ConjSat.satConj : PositivityTheory.Rg.BcB.F.RS.SatConj := by
  intro E _ _ _ n π w u B _ _ hc ⟨σ, ⟨hirr, f, f0, hf, hfx⟩, hB⟩
  obtain rfl : u = GlobalTheory.ThetaSatake.cw w := GlobalTheory.CompanionTheory.OneExDatum.eq_cw_of_conjPl hc
  refine ⟨flipIrr σ, ⟨(flipIrr σ).irred, f, f0, hf, fun x v => ?_⟩, hasSatGL_flipIrr σ hB⟩
  have hx : (x : UA E n) ∈ locU n w := locU_eq_of_under hc.1 ▸ x.2
  have := hfx ⟨x, hx⟩ v
  rw [MonoidHom.comp_apply] at this
  change f (σ.ρ (flipGL w (cLoc _ x.1)) v) = _
  rw [← cLoc_eq_flipGL]
  exact this

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

namespace GlobalTheory.CompanionTheory.SiegelND.Integ

theorem integrable_starN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ dx : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n dx →
  ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db →
  ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat Φ →
    Integrable (starN σ J ψ dx Φ) db := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn ψ hψ dx hdx db hdb Φ hΦ
  obtain ⟨μ₁, μ₂, c, h1, h2, s1, s2, hc, hme, hmap⟩ := GlobalTheory.T.adelic_haar_splits_as_arch_times_finite F E σ hCM M n dx hdx.1
  obtain ⟨ν₁, ν₂, c', g1, g2, t1, t2, hc', hme', hmap'⟩ := GlobalTheory.T.hermitian_haar_splits_arch_times_finite F E σ hCM n db hdb.1
  obtain ⟨k, P, Q, hP, hQ, hsum⟩ := id hΦ
  have hpureSB : ∀ i, GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat
      (fun X : Fin n → Fin M → AF F ⊗[F] E => P i (projInf X) * Q i (projFin X)) := fun i =>
    GlobalTheory.Published.SiegelOneVector.isSchwartzBruhat_of_prod (hP i) (hQ i) fun _ => rfl
  have hfac : ∀ i (b : HermR (AF F) σ n), starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b =
      (c.toReal : ℂ) * (starLoc (Ainf F) σ J (psiInf F ψ) μ₁ (P i) (hermInf σ b) *
        starLoc (Af F) σ J (psiFin F ψ) μ₂ (Q i) (hermFin σ b)) := by
    intro i b
    let A : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ := fun x =>
      P i x * psiInf F ψ (algebraMap F (Ainf F) (1 / 2) * Algebra.trace (Ainf F) (Ainf F ⊗[F] E)
        (Matrix.trace (((hermInf σ b : HermR (Ainf F) σ n) : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) *
          gramR (Ainf F) σ J x)))
    let B : (Fin n → Fin M → Af F ⊗[F] E) → ℂ := fun y =>
      Q i y * psiFin F ψ (algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
        (Matrix.trace (((hermFin σ b : HermR (Af F) σ n) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) *
          gramR (Af F) σ J y)))
    let G : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) → ℂ := fun z => A z.1 * B z.2
    have e1 : starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b =
        ∫ X, G (projInf X, projFin X) ∂dx := by
      unfold starN
      refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
      show _ * _ = G _
      rw [GlobalTheory.T.character_trace_pairing_eq_inner_psi F E σ hCM M J n ψ b X]
      simp only [G, A, B]
      ring
    have e2 := hme.integral_map (μ := dx) G
    have e3 : ∫ z, G z ∂μ₁.prod μ₂ = (∫ x, A x ∂μ₁) * ∫ y, B y ∂μ₂ := integral_prod_mul A B
    rw [e1]
    refine e2.symm.trans ?_
    rw [hmap, integral_smul_measure, e3, Complex.real_smul]
    rfl
  have hpure : ∀ i, Integrable (starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X))) db := by
    intro i
    have hA := GlobalTheory.T.archimedean_siegel_weil_integral_identity F E σ hCM M J hJ n hn ψ hψ μ₁ h1 ν₁ g1 (P i) (hP i)
    have hB := GlobalTheory.T.finite_adelic_siegel_weil_integral_identity F E σ hCM M J hJ n hn ψ hψ μ₂ h2 ν₂ g2 (Q i) (hQ i)
    have hAB := hA.mul_prod hB
    have hAB' : Integrable (fun z : HermR (Ainf F) σ n × HermR (Af F) σ n =>
        starLoc (Ainf F) σ J (psiInf F ψ) μ₁ (P i) z.1 * starLoc (Af F) σ J (psiFin F ψ) μ₂ (Q i) z.2)
        (db.map (fun b => (hermInf σ b, hermFin σ b))) := by
      rw [hmap']
      exact hAB.smul_measure hc'
    have := (hme'.integrable_map_iff.1 hAB').const_mul (c.toReal : ℂ)
    refine this.congr (Filter.Eventually.of_forall fun b => ?_)
    exact (hfac i b).symm
  have hdec : starN σ J ψ dx Φ = fun b => ∑ i, starN σ J ψ dx (fun X => P i (projInf X) * Q i (projFin X)) b := by
    funext b
    unfold starN
    rw [← integral_finsetSum _ fun i _ => GlobalTheory.T.twisted_schwartz_function_integrable F E σ hCM M J n ψ hψ dx hdx.1 _ (hpureSB i) b]
    refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    show Φ X * _ = _
    rw [hsum, Finset.sum_mul]
  rw [hdec]
  exact integrable_finsetSum _ fun i _ => hpure i

end GlobalTheory.CompanionTheory.SiegelND.Integ
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestDeg

theorem isHermND_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) :
    IsHermND σ (1 : Matrix (Fin M) (Fin M) E) := by
  refine ⟨fun i j => ?_, by simp⟩
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply, h, Ne.symm h]

theorem exists_test_approx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ n : ℕ, 0 < n → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∃ S₁ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∀ S, S₁ ⊆ S → ∃ (ρ : ℕ → HermR (Ainf F) σ n → ℝ) (U : ℕ → ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (HermR (Fv F v) σ n)), (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : HermR (Ainf F) σ n)).smallSets ∧ (∀ k v, IsCompact (U k v) ∧ IsOpen (U k v) ∧ (0 : HermR (Fv F v) σ n) ∈ U k v) ∧ (∀ v, Filter.Tendsto (fun k => U k v) Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets) ∧ (∀ k v, 0 < (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal) ∧ (∀ k, Integrable (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k))) db ∧ ∀ z, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y * ψ (pairHerm (AF F) σ n y z) ∂db = GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) (-z)) ∧ (∀ k, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db = ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ) * ∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal : ℂ)) ∧ (∀ k y, ‖GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y‖ ≤ ‖∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db‖) ∧ ∀ y, Filter.Tendsto (fun k => GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y / ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) Filter.atTop (nhds ((GlobalTheory.CompanionTheory.SiegelND.Coef.intH σ b n S).indicator (fun _ => (1 : ℂ)) (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ y))) := by
  intro F E _ _ _ _ _ σ hCM n hn ψ hψ db hdb d b laminf lam hinf hlam
  obtain ⟨S₁, h⟩ := GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.exists_testH_approx F E σ hCM (2 * n + 1) 1 (isHermND_one σ _) n
    (by omega) ψ hψ db hdb d b laminf lam hinf hlam
  refine ⟨S₁, fun S hS => ?_⟩
  obtain ⟨ρ, U, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h S hS
  exact ⟨ρ, U, a1, a2, fun k v => ⟨(a3 k v).1, (a3 k v).2.1, (a3 k v).2.2.1⟩, a4, fun k v => (a3 k v).2.2.2, a5, a6, a7, a8⟩

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestDeg
end

section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.RapidDecay.NearCusp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E}

theorem conj_mem_nhds {C : Set (GFin σ J)} (hC : IsCompact C) {V : Set (GFin σ J)} (hV : V ∈ 𝓝 (1 : GFin σ J)) :
    {x : GFin σ J | ∀ h ∈ C, h⁻¹ * x * h ∈ V} ∈ 𝓝 (1 : GFin σ J) := by
  refine hC.eventually_forall_of_forall_eventually (P := fun x h => h⁻¹ * x * h ∈ V) fun y _ => ?_
  have hc : Continuous fun z : GFin σ J × GFin σ J => z.2⁻¹ * z.1 * z.2 :=
    (continuous_snd.inv.mul continuous_fst).mul continuous_snd
  have ht := hc.tendsto ((1 : GFin σ J), y)
  simp only [mul_one, inv_mul_cancel] at ht
  exact ht hV

theorem exists_bound_archMat {Cm : Set (GAd σ J)} (hCm : IsCompact Cm) : ∃ C₀ : ℝ, 0 ≤ C₀ ∧
    ∀ k ∈ Cm, ∀ (w : InfinitePlace F) (τ : EmbOver E w) (i j : Fin n),
      ∑ a, ∑ b, ‖archMat σ J τ (projArch σ J w k⁻¹) i a‖ * ‖archMat σ J τ (projArch σ J w k) b j‖ ≤ C₀ := by
  let T : GAd σ J → ∀ w : InfinitePlace F, EmbOver E w → Fin n → Fin n → ℝ := fun k w τ i j =>
    ∑ a, ∑ b, ‖archMat σ J τ (projArch σ J w k⁻¹) i a‖ * ‖archMat σ J τ (projArch σ J w k) b j‖
  let f : GAd σ J → ℝ := fun k => ∑ w, ∑ τ : EmbOver E w, ∑ i, ∑ j, T k w τ i j
  have hm : ∀ (w : InfinitePlace F) (τ : EmbOver E w), Continuous fun k : GAd σ J => archMat σ J τ (projArch σ J w k) :=
    fun w τ => (GlobalTheory.Orb.continuous_archMat σ J τ).comp (continuous_projArch σ J w)
  have hf : Continuous f := by
    refine continuous_finsetSum _ fun w _ => continuous_finsetSum _ fun τ _ => continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
    exact (((hm w τ).comp continuous_inv).matrix_elem i a).norm.mul (((hm w τ).matrix_elem b j).norm)
  obtain ⟨C, hC⟩ := hCm.exists_bound_of_continuousOn hf.continuousOn
  have hT : ∀ k w τ i j, 0 ≤ T k w τ i j := fun k w τ i j => by positivity
  refine ⟨max C 0, le_max_right _ _, fun k hk w τ i j => ?_⟩
  have h1 : T k w τ i j ≤ f k := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun w => ∑ τ : EmbOver E w, ∑ i, ∑ j, T k w τ i j)
      (fun w _ => by positivity) (Finset.mem_univ w))
    refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, T k w τ i j) (fun τ _ => by positivity)
      (Finset.mem_univ τ))
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, T k w τ i j) (fun i _ => by positivity)
      (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun j => T k w τ i j) (fun j _ => hT k w τ i j) (Finset.mem_univ j)
  exact h1.trans ((Real.le_norm_self _).trans ((hC k hk).trans (le_max_left _ _)))

end GlobalTheory.CompanionTheory.RapidDecay.NearCusp

noncomputable section

namespace GlobalTheory.CompanionTheory.RapidDecay.NearCusp

theorem near_cusp_one (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hCM : IsCMExt F E σ) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (hJ : IsHermND σ J) (r : ℕ)
    (X Y : Matrix (Fin n) (Fin r) E) (hW : IsWittFrame σ J X Y) (Ω Cm : Set (GAd σ J)) (c : ℝ)
    (U : Subgroup (GAd σ J)) (hΩ : IsCompact Ω) (hΩP : Ω ⊆ minParOne σ J X) (hCm : IsCompact Cm) (hc : 0 < c)
    (hU : IsOpen (U : Set (GAd σ J))) (s : Fin r) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm,
      ∀ m ∈ unipRad σ J (pre X s), ∃ γ ∈ ratPts σ J, ∃ u κ : GAd σ J, CloseInf σ J u (M / ratio t s) ∧ κ ∈ U ∧
        κ ∈ finPts σ J ∧ m * (p * a * k) = γ * (p * a * k) * u * κ := by
  have hσ := sigma_sigma hCM
  have hC : GlobalTheory.UAut.IsIsoCols σ J (pre X s) := GlobalTheory.UAut.isIsoCols_of_isWittFrame hW hσ hJ s.2

  let Cf : Set (GFin σ J) := (fun z : GAd σ J × GAd σ J => projFin σ J z.1 * projFin σ J z.2) '' (Ω ×ˢ Cm)
  have hCf : IsCompact Cf := (hΩ.prod hCm).image
    (((continuous_projFin σ J).comp continuous_fst).mul ((continuous_projFin σ J).comp continuous_snd))
  let Uf : Set (GFin σ J) := ofFin σ J ⁻¹' (U : Set (GAd σ J))
  have hUf : Uf ∈ 𝓝 (1 : GFin σ J) :=
    (hU.preimage (continuous_ofFin σ J)).mem_nhds (by simp only [Uf, Set.mem_preimage, map_one]; exact U.one_mem)
  let Wn : Set (GFin σ J) := {x | ∀ h ∈ Cf, h⁻¹ * x * h ∈ Uf}
  have hWn : Wn ∈ 𝓝 (1 : GFin σ J) := conj_mem_nhds hCf hUf
  obtain ⟨Q, hQ, hQm⟩ := GlobalTheory.T.unipotent_radical_compact_fundamental_domain F E σ hCM n J hJ _ (pre X s) hC Wn hWn
  let Q' : Set (GAd σ J) := (fun z : GAd σ J × GAd σ J => z.1⁻¹ * z.2 * z.1) '' (Ω ×ˢ Q)
  have hQ' : IsCompact Q' := (hΩ.prod hQ).image ((continuous_fst.inv.mul continuous_snd).mul continuous_fst)
  obtain ⟨M₁, hM₁, hM₁b⟩ := GlobalTheory.T.torus_conjugate_unipotent_bounded F E σ hCM n J hJ r X Y hW Q' c hQ' hc s
  obtain ⟨C₀, hC₀, hC₀b⟩ := exists_bound_archMat (σ := σ) (J := J) hCm
  refine ⟨C₀ * M₁, mul_nonneg hC₀ hM₁, ?_⟩
  intro p hp t ht a ha k hk m hm
  obtain ⟨γ, hγ, q, hqQ, hqU, hqW, rfl⟩ := hQm m hm
  have hfa : projFin σ J a = 1 := mem_infPts.1 ha.1
  refine ⟨γ, hγ, ofInf σ J (projInf σ J ((p * a * k)⁻¹ * q * (p * a * k))),
    ofFin σ J (projFin σ J ((p * a * k)⁻¹ * q * (p * a * k))), ⟨mem_infPts.2 (projFin_ofInf σ J _), ?_⟩, ?_,
    mem_finPts.2 (projInf_ofFin σ J _), ?_⟩
  · intro w τ i j

    have hpar : p ∈ GlobalTheory.UAut.parFlag σ J (pre X s) fun _ => 0 := GlobalTheory.T.minimal_parabolic_mem_partial_flag F E σ n J r X p (hΩP hp) s
    have hq' : q ∈ GlobalTheory.UAut.unipFlag σ J (pre X s) fun _ => 0 := by rw [GlobalTheory.UAut.unipFlag_const]; exact hqU
    have hnU : p⁻¹ * q * p ∈ unipRad σ J (pre X s) := by
      have := GlobalTheory.UAut.conj_mem_unipFlag hJ hσ hC (fun _ => 0) (inv_mem hpar) hq'
      rwa [inv_inv, GlobalTheory.UAut.unipFlag_const] at this
    have hnQ : p⁻¹ * q * p ∈ Q' := ⟨(p, q), ⟨hp, hqQ⟩, rfl⟩
    have hN := hM₁b _ hnQ hnU t ht a ha w τ
    have ev : (p * a * k)⁻¹ * q * (p * a * k) = k⁻¹ * (a⁻¹ * (p⁻¹ * q * p) * a) * k := by group
    have hB : archMat σ J τ (projArch σ J w k⁻¹) * archMat σ J τ (projArch σ J w k) = 1 := by
      rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]
    have key : archMat σ J τ (projArch σ J w (ofInf σ J (projInf σ J ((p * a * k)⁻¹ * q * (p * a * k))))) - 1 =
        archMat σ J τ (projArch σ J w k⁻¹) * (archMat σ J τ (projArch σ J w (a⁻¹ * (p⁻¹ * q * p) * a)) - 1) *
          archMat σ J τ (projArch σ J w k) := by
      rw [projArch_ofInf, projInfArch_projInf, ev, map_mul (projArch σ J w) _ k, map_mul (projArch σ J w) k⁻¹,
        map_mul (archMat σ J τ), map_mul (archMat σ J τ), Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hB]
    rw [key]
    refine (GlobalTheory.CuspGeo.norm_mul_mul_apply_le _ _ _ _ hN i j).trans ?_
    rw [mul_div_assoc C₀]
    exact mul_le_mul_of_nonneg_right (hC₀b k hk w τ i j) (div_nonneg hM₁ (ratio_pos ht s).le)
  ·
    have hh : projFin σ J p * projFin σ J k ∈ Cf := ⟨(p, k), ⟨hp, hk⟩, rfl⟩
    have e : projFin σ J ((p * a * k)⁻¹ * q * (p * a * k)) =
        (projFin σ J p * projFin σ J k)⁻¹ * projFin σ J q * (projFin σ J p * projFin σ J k) := by
      simp only [map_mul, map_inv, hfa, mul_one]
    have := hqW _ hh
    rw [← e] at this
    exact this
  · rw [mul_assoc (γ * (p * a * k)), ofInf_projInf_mul_ofFin_projFin]
    group

end GlobalTheory.CompanionTheory.RapidDecay.NearCusp

namespace GlobalTheory.CompanionTheory.RapidDecay


open NearCusp in
theorem near_cusp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (Ω Cm : Set (GAd σ J)) (c : ℝ) (U : Subgroup (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → IsCompact Cm → 0 < c → IsOpen (U : Set (GAd σ J)) → ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ Ω, ∀ t ∈ cone r c, ∀ a, IsTorusElt σ J X Y t a → ∀ k ∈ Cm, ∀ s : Fin r, ∀ m ∈ unipRad σ J (pre X s), ∃ γ ∈ ratPts σ J, ∃ u κ : GAd σ J, CloseInf σ J u (M / ratio t s) ∧ κ ∈ U ∧ κ ∈ finPts σ J ∧ m * (p * a * k) = γ * (p * a * k) * u * κ := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y hW Ω Cm c U hΩ hΩP hCm hc hU
  choose M hM0 hM using near_cusp_one F E σ hCM n J hJ r X Y hW Ω Cm c U hΩ hΩP hCm hc hU
  refine ⟨∑ s, M s, Finset.sum_nonneg fun s _ => hM0 s, ?_⟩
  intro p hp t ht a ha k hk s m hm
  obtain ⟨γ, hγ, u, κ, ⟨hu1, hu2⟩, h2, h3, h4⟩ := hM s p hp t ht a ha k hk m hm
  refine ⟨γ, hγ, u, κ, ⟨hu1, fun w τ i j => (hu2 w τ i j).trans ?_⟩, h2, h3, h4⟩
  exact div_le_div_of_nonneg_right (Finset.single_le_sum (fun s _ => hM0 s) (Finset.mem_univ s)) (ratio_pos ht s).le

end GlobalTheory.CompanionTheory.RapidDecay
end
end
end

section

noncomputable section

open NumberField IsDedekindDomain Polynomial Matrix
open GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.Bc.ArchbcB.B.M4 PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.MT PositivityTheory.Rg.BcB.F.MLM
open PositivityTheory.Rg.BcN.F2 (mconv)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.RegPow

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open GlobalTheory.CompanionTheory.MatchPow in
theorem hasVals_nrm (hU : Unr E) {w : Pl E} (hw : ¬ IsSplitAt w) {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {a : ℕ}
    {y : Fin a → ℤ} (hy : StrictAnti y) {δ : GLw a w} (hδ : dcos a w (tdiag ϖ y) δ ≠ 0) :
    HasVals (nrmL a w δ).val.charpoly (nv y) := by
  obtain ⟨m, -, τ, hτ, e⟩ := GlobalTheory.CompanionTheory.ThetaContraction.contr_tw hU w hw ϖ hϖ a y hy δ hδ
  obtain ⟨v, hv, rfl⟩ := GlobalTheory.CompanionTheory.TwSide.exists_diagT_of_mem_TO hτ
  have hdu : m⁻¹ * δ * thL a w m = GlobalTheory.SmGL.diagT (w.adicCompletion E) (Fin a) fun i => ϖ ^ y i * v i := by
    rw [e, tdiag, ← map_mul]
    rfl
  have hord : ∀ i, ordL (((ϖ ^ y i * v i : (w.adicCompletion E)ˣ)) : w.adicCompletion E) = y i := by
    intro i
    simp only [Units.val_mul]
    rw [GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_mul_of_ne (Units.ne_zero _) (Units.ne_zero _),
      GlobalTheory.CompanionTheory.UnitaryContraction.ordL_zpow, hϖ.1,
      GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_congr (b := (1 : w.adicCompletion E)) (by rw [hv, map_one]),
      GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_one]
    simp
  rw [← GlobalTheory.CompanionTheory.MatchLinear.charpoly_nrmL_twConj hU a w δ m, hdu, GlobalTheory.CompanionTheory.TwSide.nrmL_diagT hw, GlobalTheory.SmGL.val_diagT,
    Matrix.charpoly_diagonal]
  exact ⟨fun i => _, rfl, fun i => ⟨Units.ne_zero _, GlobalTheory.CompanionTheory.TwSide.ordL_norm_entry hU _ y hord i⟩⟩


open GlobalTheory.CompanionTheory.MatchPow in
theorem mpow_entT {w : Pl E} {n : ℕ} (a : ℕ) {ϖ : (w.adicCompletion E)ˣ} (hϖ : IsUnifAt ϖ) {J : Type} [Fintype J]
    (c : J → ℂ) (x : J → Fin n → ℤ) (hx : ∀ j, StrictAnti (x j) ∧ Cone (lOf (x j))) (k : ℕ) :
    ∃ (J' : Type) (_ : Fintype J') (c' : J' → ℂ) (x' : J' → Fin n → ℤ),
      (∀ j, StrictAnti (x' j) ∧ Cone (lOf (x' j))) ∧
      ∀ s, mpow w (entT n w ϖ a c x s) (k + 1) = fun y => beta a (n - a) w ^ k * entT n w ϖ a c' x' s y := by
  induction k with
  | zero =>
    refine ⟨J, inferInstance, c, x, hx, fun s => ?_⟩
    funext y
    have := conv_unit (iwahori_pair_le_maximal a (n - a) w) (iwahori_pair_index_ne_zero a (n - a) w)
      (fun k hk z => ((entT_hecke n w ϖ a c x s).2 k hk z).2) y
    rw [pow_zero, one_mul]
    exact this
  | succ k ih =>
    obtain ⟨J', _, c', x', hx', e⟩ := ih
    refine ⟨J × J', inferInstance, fun p => c p.1 * c' p.2, fun p => x p.1 + x' p.2, fun p => ⟨?_, ?_⟩, fun s => ?_⟩
    · exact fun i j hij => add_lt_add ((hx p.1).1 hij) ((hx' p.2).1 hij)
    · rw [lOf_add]
      exact cone_add (hx p.1).2 (hx' p.2).2
    · show mconv _ (mpow w _ (k + 1)) = _
      rw [e, mconv_entT GlobalTheory.CompanionTheory.DcosProduct.dcosMul n ϖ hϖ a c x c' x' hx hx', pow_succ]

theorem regPowT : RegPowT := by
  intro E _ _ _ hU n d _ hm a ha m w hT y hy
  obtain ⟨hw, -, hϖ, hc⟩ := hm.T w hT
  rw [GlobalTheory.CompanionTheory.MatchLMB2.trace_test_function_eq d ha hT m] at hy
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
  obtain ⟨J', _, c', x', hx', e⟩ := mpow_entT a hϖ (GlobalTheory.CompanionTheory.MatchLMPlaces.cc d w) (GlobalTheory.CompanionTheory.MatchLMPlaces.xx d w)
    (fun j => hc j.1 j.2) m
  rw [GlobalTheory.CompanionTheory.MatchLMPlaces.qT_eq d s, GlobalTheory.CompanionTheory.MatchLMPlaces.mpow_scale, e s] at hs
  have h1 : entT n w (d.ϖ w) a c' x' s y ≠ 0 := fun h => hs (by simp [h])
  by_cases hA : MT.admitted n a s
  swap
  · exact absurd (dif_neg hA) h1
  unfold entT at h1
  rw [dite_eq_left hA] at h1
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
  have hd2 : dcos (n - a) w (tdiag (d.ϖ w) (restr (x' j) _ hA.2.2.2.2)) y.2 ≠ 0 := right_ne_zero_of_mul hj
  have hd1 : dcos a w (tdiag (d.ϖ w) (restr (x' j) _ hA.2.2.2.1)) y.1 ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hj)
  obtain ⟨u₁, hQ₁, hu₁⟩ := hasVals_nrm hU hw hϖ (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.restr_strictAnti (hx' j).1 _ hA.2.2.2.1) hd1
  obtain ⟨u₂, hQ₂, hu₂⟩ := hasVals_nrm hU hw hϖ (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.restr_strictAnti (hx' j).1 _ hA.2.2.2.2) hd2
  rw [hQ₁, hQ₂]
  exact GlobalTheory.CompanionTheory.SymmetricIndexRegularity.localization_quotient_separated_dvd (fun z => ordL z) (hx' j).1 _ _ hA.2.2.2.1 hA.2.2.2.2 (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.symIdx_rev n _ s)
    (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.symIdx_rev n _ sᶜ) (GlobalTheory.CompanionTheory.SymmetricIndexRegularity.symIdx_disj n _ _ s (by have := hA.2.2.1; omega)) u₁ u₂
    (fun j => (hu₁ j).2) (fun j => (hu₂ j).2)

end GlobalTheory.CompanionTheory.RegPow

end
end
