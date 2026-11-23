module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import GroundTheory.AutomorphicForms.SmoothRep
public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.Topology.Instances.Matrix
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle101
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Mathlib.Order.CompletePartialOrder
import Aesop.Main
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirVolumeRatios.AdeleLC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle181
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDiff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle239
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle259
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle018
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle280
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.MapUgAlgebraMap
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle281
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalLetter
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle285
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle210
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle223
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableLaplacian
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle279
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
import Mathlib.Topology.UniformSpace.Uniformizable
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle012
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import ReciprocityTheory.NeutralLocalFields.Bundle001

@[expose] public section

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.smooth_rep_is_smooth_foundation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], ∀ (N : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → GroundTheory.Automorphic.IsSmooth π := by
  first | exact @GlobalTheory.CompanionTheory.SmoothTransfer.isSmooth_found | exact GlobalTheory.CompanionTheory.SmoothTransfer.isSmooth_found | (intros; apply GlobalTheory.CompanionTheory.SmoothTransfer.isSmooth_found <;> assumption)
end

section

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

theorem _root_.GlobalTheory.T.admissible_irreducible_central_scalar : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → π.IsIrreducible → IsAdmissible π → ∀ t : kˣ, ∃ c : ℂ, ∀ v, π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v = c • v := by
  first | exact @GlobalTheory.CompanionTheory.SchurCentre.scalar_acts_by_scalar | exact GlobalTheory.CompanionTheory.SchurCentre.scalar_acts_by_scalar | (intros; apply GlobalTheory.CompanionTheory.SchurCentre.scalar_acts_by_scalar <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.subquotient_nontrivial_exists_mem : ∀ {M W X : Type} [Group M] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ M W) (σ : Representation ℂ M X) (S T : Subrepresentation ρ), Nonempty ((subQuot S T).Equiv σ) → Nontrivial X → ∃ s ∈ S.toSubmodule, s ∉ T.toSubmodule := by
  first | exact @GlobalTheory.CompanionTheory.SubQuotNe.exists_mem_not_mem_of_subQuot_equiv | exact GlobalTheory.CompanionTheory.SubQuotNe.exists_mem_not_mem_of_subQuot_equiv | (intros; apply GlobalTheory.CompanionTheory.SubQuotNe.exists_mem_not_mem_of_subQuot_equiv <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

theorem _root_.GlobalTheory.T.subquotient_scalar_action_mod : ∀ {M W X : Type} [Group M] [AddCommGroup W] [Module ℂ W] [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ M W) (σ : Representation ℂ M X) (S T : Subrepresentation ρ), Nonempty ((subQuot S T).Equiv σ) → ∀ (g : M) (c : ℂ), (∀ x, σ g x = c • x) → ∀ s ∈ S.toSubmodule, ρ g s - c • s ∈ T.toSubmodule := by
  first | exact @GlobalTheory.CompanionTheory.SubQuotScalar.sub_smul_mem_of_equiv_subQuot | exact GlobalTheory.CompanionTheory.SubQuotScalar.sub_smul_mem_of_equiv_subQuot | (intros; apply GlobalTheory.CompanionTheory.SubQuotScalar.sub_smul_mem_of_equiv_subQuot <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich

variable {F : Type} [Field F] [NumberField F]

def ballV (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : Set (Fv F v) :=
  {y | Valued.v y ≤ WithZero.exp (-(n : ℤ))}

theorem isClopen_ballV (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) : IsClopen (ballV v n) := by
  obtain ⟨c, hc⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-(n : ℤ)))
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero] at hc
    exact WithZero.exp_ne_zero hc.symm
  have : ballV v n = {y : Fv F v | Valued.v.restrict y ≤ Valued.v.restrict c} := by
    ext y
    simp only [ballV, Set.mem_ofPred_eq, Valuation.restrict_le_iff, hc]
  rw [this]
  exact Valued.isClopen_closedBall _ (by simp [hc0])

theorem ballV_subset (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    ballV v n ⊆ (v.adicCompletionIntegers F : Set (Fv F v)) := by
  intro y hy
  have h1 : (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have h2 : Valued.v y ≤ 1 := le_trans (show Valued.v y ≤ _ from hy) h1
  exact h2

theorem antitone_ballV (v : HeightOneSpectrum (𝓞 F)) : Antitone (ballV (F := F) v) := by
  intro m n hmn y hy
  show Valued.v y ≤ _
  refine le_trans (show Valued.v y ≤ _ from hy) ?_
  rw [WithZero.exp_le_exp]
  omega

theorem iInter_ballV (v : HeightOneSpectrum (𝓞 F)) : ⋂ n, ballV (F := F) v n = {0} := by
  ext y
  simp only [Set.mem_iInter, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hy
    have hv0 : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    have h1 := h (-(Valued.v y).log + 1).toNat
    have h2 : Valued.v y ≤ WithZero.exp (-(((-(Valued.v y).log + 1).toNat : ℕ) : ℤ)) := h1
    conv_lhs at h2 => rw [← WithZero.exp_log hv0]
    rw [WithZero.exp_le_exp] at h2
    have := Int.self_le_toNat (-(Valued.v y).log + 1)
    omega
  · rintro rfl n
    simp [ballV]

theorem nhdsNE_Fv (v : HeightOneSpectrum (𝓞 F)) : (𝓝[≠] (0 : Fv F v)).NeBot := by
  letI : NontriviallyNormedField (v.adicCompletion F) :=
    Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
  exact NormedField.nhdsNE_neBot (0 : v.adicCompletion F)

theorem tendsto_real_ballV {v : HeightOneSpectrum (𝓞 F)} {lam : Measure (Fv F v)} (hstd : IsStdV v lam) :
    Tendsto (fun n => lam.real (ballV v n)) atTop (𝓝 0) := by
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := hstd.1
  haveI := nhdsNE_Fv v
  have hfin : ∀ n, lam (ballV v n) ≠ ∞ := fun n =>
    ne_top_of_le_ne_top (by rw [hstd.2]; exact ENNReal.one_ne_top) (measure_mono (ballV_subset v n))
  have h := tendsto_measure_iInter_atTop (μ := lam) (s := ballV v)
    (fun n => (isClopen_ballV v n).isOpen.measurableSet.nullMeasurableSet) (antitone_ballV v) ⟨0, hfin 0⟩
  rw [iInter_ballV, measure_singleton] at h
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  simpa [Measure.real, Function.comp_def] using h2

theorem exists_sandwich : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (C : ℝ) (g : Fv F v → ℝ), IsStdV v lam → (∀ s, 0 ≤ g s) → GoodFac v lam C g → ∀ η : ℝ, 0 < η → ∃ ψm ψp : Fv F v → ℝ, Continuous ψm ∧ HasCompactSupport ψm ∧ Continuous ψp ∧ HasCompactSupport ψp ∧ (∀ s, 0 ≤ ψm s) ∧ (∀ s, s ≠ 0 → ψm s ≤ g s ∧ g s ≤ ψp s) ∧ 1 - η ≤ ∫ s, ψm s ∂lam ∧ ∫ s, ψp s ∂lam ≤ 1 + η := by
  intro F _ _ v lam C g hstd hg0 hg η hη
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := hstd.1
  haveI := nhdsNE_Fv v
  obtain ⟨hcont, hout, hint, -, hone⟩ := hg
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 1 + |C| := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hKdef]; positivity
  have hq : (1 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le
  have hgK : ∀ s, s ≠ 0 → g s ≤ K := by
    intro s hs
    by_cases hO : s ∈ v.adicCompletionIntegers F
    · have h1 := hint s hO hs
      have h2 : C / (Ideal.absNorm v.asIdeal : ℝ) ≤ |C| :=
        (div_le_self (abs_nonneg C) hq |>.trans' (div_le_div_of_nonneg_right (le_abs_self C) (by linarith)))
      have h3 := (abs_le.1 h1).2
      rw [hKdef]; linarith
    · rw [hout s hO]; exact hK0.le
  have hgi : Integrable g lam := by
    by_contra h
    rw [integral_undef h] at hone
    norm_num at hone
  have hnz : ∀ᵐ s ∂lam, s ≠ 0 := by
    have : ({0}ᶜ : Set (Fv F v)) ∈ ae lam := compl_mem_ae_iff.2 (measure_singleton 0)
    exact this
  have hlim : Tendsto (fun n => K * lam.real (ballV v n)) atTop (𝓝 0) := by
    simpa using (tendsto_real_ballV hstd).const_mul K
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  obtain ⟨B, hB⟩ : ∃ B, B = ballV v n := ⟨_, rfl⟩
  rw [← hB] at hn
  have hBc : IsClopen B := hB ▸ isClopen_ballV v n
  have hBO : B ⊆ (v.adicCompletionIntegers F : Set (Fv F v)) := hB ▸ ballV_subset v n
  have h0B : (0 : Fv F v) ∈ B := by rw [hB]; simp [ballV]
  have hBm : MeasurableSet B := hBc.isOpen.measurableSet
  have hBfin : lam B ≠ ∞ :=
    ne_top_of_le_ne_top (by rw [hstd.2]; exact ENNReal.one_ne_top) (measure_mono hBO)
  have hcomp : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    Formalism.L2.S.S7.AdeleLC.isCompact_integers v
  have hψm : Continuous (Bᶜ.indicator g) := by
    refine continuous_indicator ?_ ?_
    · intro a ha
      rw [hBc.compl.frontier_eq] at ha
      exact absurd ha (Set.notMem_empty a)
    · rw [hBc.compl.isClosed.closure_eq]
      refine hcont.mono ?_
      intro s hs h0
      exact hs (by rw [Set.mem_singleton_iff.1 h0]; exact h0B)
  have hψb : Continuous (B.indicator fun _ => K) :=
    by
    refine continuous_indicator ?_ continuous_const.continuousOn
    intro a ha
    rw [hBc.frontier_eq] at ha
    exact absurd ha (Set.notMem_empty a)
  have hIm : ∫ s, Bᶜ.indicator g s ∂lam = ∫ s in Bᶜ, g s ∂lam := integral_indicator hBm.compl
  have hsplit : ∫ s in B, g s ∂lam + ∫ s in Bᶜ, g s ∂lam = 1 := by
    rw [integral_add_compl hBm hgi, hone]
  have hpos : 0 ≤ ∫ s in B, g s ∂lam := setIntegral_nonneg hBm fun s _ => hg0 s
  have hconst : ∫ s in B, K ∂lam = K * lam.real B := by
    rw [setIntegral_const, smul_eq_mul, mul_comm]
  have hup : ∫ s in B, g s ∂lam ≤ K * lam.real B := by
    rw [← hconst]
    refine integral_mono_ae hgi.integrableOn (integrableOn_const hBfin) ?_
    exact ae_restrict_of_ae (hnz.mono fun s hs => hgK s hs)
  have hi1 : Integrable (Bᶜ.indicator g) lam := hgi.indicator hBm.compl
  have hi2 : Integrable (B.indicator fun _ => K) lam :=
    (integrable_indicator_iff hBm).2 (integrableOn_const hBfin)
  have hIp : ∫ s, (Bᶜ.indicator g s + B.indicator (fun _ => K) s) ∂lam =
      ∫ s in Bᶜ, g s ∂lam + K * lam.real B := by
    rw [integral_add hi1 hi2, hIm, integral_indicator hBm, hconst]
  refine ⟨Bᶜ.indicator g, fun s => Bᶜ.indicator g s + B.indicator (fun _ => K) s, hψm, ?_,
    hψm.add hψb, ?_, fun s => Set.indicator_nonneg (fun s _ => hg0 s) s, ?_, ?_, ?_⟩
  · refine HasCompactSupport.intro hcomp fun s hs => ?_
    simp [Set.indicator, hout s hs]
  · refine HasCompactSupport.intro hcomp fun s hs => ?_
    have hsB : s ∉ B := fun h => hs (hBO h)
    simp [hsB, hout s hs]
  · intro s hs
    by_cases hsB : s ∈ B
    · simp only [Set.indicator, Set.mem_compl_iff, hsB, not_true_eq_false, if_false, if_true, zero_add]
      exact ⟨hg0 s, hgK s hs⟩
    · simp [Set.indicator, hsB]
  · rw [hIm]; linarith
  · rw [hIp]; linarith

end GlobalTheory.CompanionTheory.Mass.MeanV.Sandwich

end
end

section

set_option maxSynthPendingDepth 1

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.CompanionTheory.HCRep

open AutomorphicForm GlobalTheory.CompanionTheory.ArchSmooth

theorem exists_monic_aeval_add {M : Type*} [AddCommGroup M] [Module ℂ M] (Ω T : Module.End ℂ M)
    (hc : Commute Ω T) (W : Submodule ℂ M) [FiniteDimensional ℂ W] (hT : ∀ w ∈ W, T w ∈ W)
    (q : Polynomial ℂ) (hq : q.Monic) (hqW : ∀ w ∈ W, Polynomial.aeval Ω q w = 0) {v : M} (hv : v ∈ W) :
    ∃ P : Polynomial ℂ, P.Monic ∧ 0 < P.natDegree ∧ Polynomial.aeval (Ω + T) P v = 0 := by
  classical
  let V : Submodule ℂ M := ⨆ m : Fin (q.natDegree + 1), W.map (Ω ^ (m : ℕ))
  have hVfd : FiniteDimensional ℂ V := Submodule.finiteDimensional_iSup _
  have hmem : ∀ (i : ℕ), i < q.natDegree + 1 → ∀ w ∈ W, (Ω ^ i) w ∈ V := fun i hi w hw =>
    Submodule.mem_iSup_of_mem (⟨i, hi⟩ : Fin (q.natDegree + 1)) ⟨w, hw, rfl⟩
  have hpow : ∀ (m : ℕ), ∀ w ∈ W, (Ω ^ m) w ∈ V := by
    intro m w hw
    have e : (Ω ^ m) w = Polynomial.aeval Ω (Polynomial.X ^ m %ₘ q) w := by
      have h1 := Polynomial.modByMonic_add_div (Polynomial.X ^ m : Polynomial ℂ) q
      have h2 : Polynomial.aeval Ω (q * (Polynomial.X ^ m /ₘ q)) w = 0 := by
        rw [mul_comm, map_mul, Module.End.mul_apply, hqW w hw, map_zero]
      have h3 := congrArg (fun p => Polynomial.aeval Ω p w) h1
      simp only [map_add (f := _), LinearMap.add_apply, h2, add_zero, map_pow, Polynomial.aeval_X] at h3
      exact h3.symm
    rw [e, Polynomial.aeval_eq_sum_range' (n := q.natDegree + 1)
      (Nat.lt_succ_of_le (Polynomial.natDegree_modByMonic_le _ hq)), LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun i hi => by
      rw [LinearMap.smul_apply]
      exact V.smul_mem _ (hmem i (Finset.mem_range.1 hi) w hw)
  have hst : ∀ x ∈ V, (Ω + T) x ∈ V := by
    intro x hx
    have hle : V ≤ V.comap (Ω + T) := by
      refine iSup_le fun m => ?_
      rintro _ ⟨w, hw, rfl⟩
      have e : (Ω + T) ((Ω ^ (m : ℕ)) w) = (Ω ^ ((m : ℕ) + 1)) w + (Ω ^ (m : ℕ)) (T w) := by
        rw [LinearMap.add_apply, pow_succ', Module.End.mul_apply, ← Module.End.mul_apply T,
          ((hc.pow_left (m : ℕ)).eq).symm, Module.End.mul_apply]
      change (Ω + T) ((Ω ^ (m : ℕ)) w) ∈ V
      rw [e]
      exact V.add_mem (hpow _ w hw) (hpow _ _ (hT w hw))
    exact hle hx
  have hv' : v ∈ V := by simpa using hpow 0 v hv
  exact AutomorphicForm.exists_monic_aeval_apply_eq_zero (Ω + T) V hst hv'

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem exists_aeval_lapOp_eq_zero (φ : Sm E a) (hA : IsAutForm φ) {d : ℕ}
    (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra) (ε : Fin d → ℝ)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (horth : ∀ i j, archTraceForm E a (b i) (b j) = if i = j then ε i else 0)
    (hskew : ∀ i, ε i = -1 → b i ∈ archSkew E a) :
    ∃ P : Polynomial ℂ, P.Monic ∧ 0 < P.natDegree ∧ Polynomial.aeval (lapOp (⇑b)) P φ = 0 := by
  classical
  set Ω := omegaOp (E := E) (a := a) (⇑b) ε with hΩ
  set W := Submodule.span ℂ (Set.range fun k => cptRep E a k φ) with hWdef
  haveI : FiniteDimensional ℂ W := hA.kfin
  have hZ : Ω ∈ Zalg E a := by
    rw [hΩ, GlobalTheory.T.omega_operator_eq_casimir_sum  E a d b ε hε horth]
    refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun w _ => Subalgebra.add_mem _ ?_ ?_) _
    · exact GlobalTheory.T.casimir_mem_center_enveloping E a _
    · exact GlobalTheory.T.casimir_mem_center_enveloping E a _
  set Vz := Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a) with hVz
  haveI : FiniteDimensional ℂ Vz := hA.zfin
  have hVs : ∀ w ∈ Vz, Ω w ∈ Vz := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => Ω w ∈ Vz) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨z, hz, rfl⟩
      exact Submodule.subset_span ⟨Ω * z, Subalgebra.mul_mem _ hZ hz, rfl⟩
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
    · intro c x _ hx; rw [map_smul]; exact Submodule.smul_mem _ c hx
  have hφV : φ ∈ Vz := Submodule.subset_span ⟨1, Subalgebra.one_mem _, rfl⟩
  obtain ⟨q, hqm, -, hq⟩ := AutomorphicForm.exists_monic_aeval_apply_eq_zero Ω Vz hVs hφV
  have hqW : ∀ w ∈ W, Polynomial.aeval Ω q w = 0 := by
    intro w hw
    refine Submodule.span_induction (p := fun w _ => Polynomial.aeval Ω q w = 0) ?_ ?_ ?_ ?_ hw
    · rintro _ ⟨k, rfl⟩
      have hcomm : ∀ m, cptRep E a k (Ω m) = Ω (cptRep E a k m) := fun m =>
        (congrArg (fun T : Module.End ℂ (Sm E a) => T m)
          (GlobalTheory.T.omega_operator_commutes_infinite_gl E a d b ε hε horth (Unitary.toUnits k))).symm
      have := AutomorphicForm.map_aeval_apply_of_intertwine (cptRep E a k) hcomm q φ
      rw [hq, map_zero] at this
      exact this.symm
    · rw [map_zero]
    · intro x y _ _ hx hy; rw [map_add (f := _), hx, hy, add_zero]
    · intro c x _ hx; rw [map_smul, hx, smul_zero]
  have hlap : Commute Ω (lapOp (⇑b)) := by
    simp only [lapOp, Commute, SemiconjBy]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : Ω * liB (b i) = liB (b i) * Ω := omegaOp_comm_liB b ε hε horth (b i)
    rw [← mul_assoc, h1, mul_assoc, h1, mul_assoc]
  have hTW : ∀ w ∈ W, (lapOp (⇑b) - Ω) w ∈ W := by
    intro w hw
    have e : (lapOp (E := E) (a := a) (⇑b) - Ω) w =
        ∑ i, ((1 : ℂ) - (ε i : ℂ)) • liB (b i) (liB (b i) w) := by
      simp only [hΩ, lapOp, omegaOp, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
        Module.End.mul_apply]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      module
    rw [e]
    refine Submodule.sum_mem _ fun i _ => ?_
    rcases hε i with h | h
    · simp [h]
    · refine W.smul_mem _ ?_
      have hs := mem_archSkew.1 (hskew i h)
      have hfd : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)) := hA.kfin
      exact GlobalTheory.T.compact_span_finite_dim_stable E a φ (b i) hs hfd _ (GlobalTheory.T.compact_span_finite_dim_stable E a φ (b i) hs hfd _ hw)
  have hφW : φ ∈ W := by
    refine Submodule.subset_span ⟨1, ?_⟩
    change cptRep E a 1 φ = φ
    rw [map_one]
    rfl
  have hc : Commute Ω (lapOp (⇑b) - Ω) := by
    refine LinearMap.ext fun x => ?_
    have h2 := LinearMap.congr_fun hlap.eq x
    simp only [Module.End.mul_apply] at h2 ⊢
    rw [LinearMap.sub_apply, LinearMap.sub_apply, map_sub, h2]
  have hsum : Ω + (lapOp (⇑b) - Ω) = lapOp (⇑b) := LinearMap.ext fun x => by simp
  obtain ⟨P, hP1, hP2, hP3⟩ := exists_monic_aeval_add Ω (lapOp (⇑b) - Ω) hc W hTW q hqm hqW hφW
  refine ⟨P, hP1, hP2, ?_⟩
  rwa [hsum] at hP3

theorem sliceL_aeval_lapOp {d : ℕ} (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra E a).lieSubalgebra)
    (P : Polynomial ℂ) (ψ : Sm E a) (g : AdelicGLn.AdelicGL E a) :
    sliceL g (smL E a (Polynomial.aeval (lapOp (⇑b)) P ψ)) =
      Polynomial.aeval ((isExpLieAlgebra E a).laplacian (F := ℂ) b) P (sliceL g (smL E a ψ)) := by
  refine AutomorphicForm.map_aeval_apply_of_intertwine ((sliceL g).comp (smL E a)) (fun m => ?_) P ψ

  simp only [LinearMap.comp_apply, smL_lapOp, map_sum, sliceL_uAction,
  IsExpLieAlgebra.laplacian, LinearMap.sum_apply, Module.End.mul_apply,
  IsExpLieAlgebra.rightUAction_ι]

theorem uJ_eq_conv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (hs : φ.1 ∈ AutomorphicForm.archSmooth E a), IsAutForm φ → (∀ [MeasurableSpace (AutomorphicForm.archGroup E a)] [BorelSpace (AutomorphicForm.archGroup E a)]
    (μ : MeasureTheory.Measure (AutomorphicForm.archGroup E a)) [μ.IsHaarMeasure]
    (k : ℕ) (J : Fin k → Fin (CuspidalSpectrum.archDim E a)),
    ∃ D : AutomorphicForm.archGroup E a → ℂ, Continuous D ∧ HasCompactSupport D ∧ ∀ g : AdelicGLn.AdelicGL E a,
      ((AutomorphicForm.uAction (CuspidalSpectrum.uJ (K := E) (n := a) k J) (⟨φ.1, hs⟩ : ↥(AutomorphicForm.archSmooth E a)) :
        ↥(AutomorphicForm.archSmooth E a)) : AdelicGLn.AdelicGL E a → ℂ) g = ∫ y, φ.1 (g * AutomorphicForm.infEmb E a y) * D y ∂μ) := by
  intro E _ _ _ a φ hs hA _ _ μ _ k J
  obtain ⟨d, b, ε, hε, horth, hskew⟩ := exists_archCartanBasis (K := E) (n := a)
  obtain ⟨P, hm, hd, hP⟩ := exists_aeval_lapOp_eq_zero φ hA b ε hε horth hskew
  exact GlobalTheory.T.laplacian_monic_annihilator_measure E a (smL E a φ) d b P hm hd
    (fun g => by rw [← sliceL_aeval_lapOp, hP, map_zero, map_zero]) μ k J

end GlobalTheory.CompanionTheory.HCRep

end
end

section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem _root_.GlobalTheory.T.cone_series_special_value_rational : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (u : (Fin r → ℕ) → ℚ) (cs : List (Fin r)) (p K l : ℕ), 0 < l → (∀ m, ∃ z : ℤ, (l : ℚ) ^ K * u m = z) → (∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) → ∃ (q : ℚ) (z : ℤ), ∑' m, (u m : ℂ) * DL cs (coneTerm a b (-(p : ℂ))) m = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.value_neg_nat_mem | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.value_neg_nat_mem | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.value_neg_nat_mem <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.filtration_divided_power_structures : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), R.PdI (A.Fil0 1) ∧ R.PdI A.PFil0 ∧ ∀ x ∈ A.Fil0 1, ∀ (k : ℕ) (y : A.Acr0), (k.factorial : A.Acr0) * y = x ^ k → y ∈ A.Fil0 k := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.pdI_main | exact GlobalTheory.CompanionTheory.PerfFil.pdI_main | (intros; apply GlobalTheory.CompanionTheory.PerfFil.pdI_main <;> assumption)
end

section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

theorem _root_.GlobalTheory.T.graded_filtration_generated_by_dividedXi : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n r : ℕ), (∀ z ∈ A.Fil n r, ∃ w : A.W, z - A.toAcr n w * A.dxi n r ∈ A.Fil n (r + 1)) ∧ ∀ w : A.W, A.toAcr n w * A.dxi n r ∈ A.Fil n (r + 1) ↔ A.th w ∈ Ideal.span {(l : A.U) ^ n} := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.graded_mod_pow | exact GlobalTheory.CompanionTheory.PerfFil.graded_mod_pow | (intros; apply GlobalTheory.CompanionTheory.PerfFil.graded_mod_pow <;> assumption)
end

section

noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal
open scoped Classical

theorem _root_.GlobalTheory.T.local_character_induced_tied_six : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied6 l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ)
      (J : (↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) → ℤ),
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ J → PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ⁻¹ (-J) := by
  first | exact @GlobalTheory.CompanionTheory.DeRhamChar.isdRJ_inv | exact GlobalTheory.CompanionTheory.DeRhamChar.isdRJ_inv | (intros; apply GlobalTheory.CompanionTheory.DeRhamChar.isdRJ_inv <;> assumption)
end
end

section


theorem _root_.GlobalTheory.T.kernel_regularity : PositivityTheory.RgBcC.Fc.KerCore := by
  first | exact @GlobalTheory.CompanionTheory.KerFc.kerCore | exact GlobalTheory.CompanionTheory.KerFc.kerCore | (intros; apply GlobalTheory.CompanionTheory.KerFc.kerCore <;> assumption)
end
