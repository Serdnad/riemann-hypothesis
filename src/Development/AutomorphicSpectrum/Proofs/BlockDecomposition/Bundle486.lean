module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle061
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle455
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle106
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle032
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle055
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilFreeOfCongruentMatrix
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.ProdFirstProjectionSmul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle132
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle157
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle311
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle156
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle456
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle457
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle460
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle089
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle035
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepMetricSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core


theorem _root_.GlobalTheory.T.lattice_level_open_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M N : ℕ), 0 < N →
    IsOpen (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) ∧
    IsCompact (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_isOpen_isCompact | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_isOpen_isCompact | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_isOpen_isCompact <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core


theorem _root_.GlobalTheory.T.lattice_levels_neighbourhood_basis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ),
    ∀ U ∈ nhds (0 : Fin n → Fin M → Af F ⊗[F] E), ∃ N : ℕ, 0 < N ∧
      (latN b n M N : Set (Fin n → Fin M → Af F ⊗[F] E)) ⊆ U := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_small | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_small | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.latN_small <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core


theorem _root_.GlobalTheory.T.rational_tuple_in_lattice_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n N : ℕ), 0 < N →
    ∃ s : ℕ, 0 < s ∧ ∀ ρ : Fin M → Fin n → 𝓞 E, ratTuple J s ρ ∈ latN b n M N := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem.ratTuple_mem_latN | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem.ratTuple_mem_latN | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatMem.ratTuple_mem_latN <;> assumption)
end

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ScaleFib


open scoped Pointwise in
theorem map_mul_fv {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v))
    [lam.IsAddHaarMeasure] (x : Fv F v) (hx : x ≠ 0) (a : ℝ≥0) (ha : ‖x‖ = (a : ℝ)⁻¹) :
    lam.map (fun y => x * y) = a • lam := by
  open scoped Pointwise in
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  have hu : IsUnit x := hx.isUnit
  have hc : ((distribHaarChar (Fv F v) hu.unit : ℝ≥0) : ℝ) = (a : ℝ)⁻¹ := by
    have h := GlobalTheory.CompanionTheory.SW.ProdFormula.distribHaarChar_eq_nnnorm v x hx
    have he : Units.mk0 x hx = hu.unit := by
      ext
      simp
    rw [he] at h
    simpa [ha] using congrArg (fun z : ℝ≥0 => (z : ℝ)) h
  have hc' : distribHaarChar (Fv F v) hu.unit⁻¹ = a := by
    rw [map_inv]
    apply NNReal.coe_injective
    push_cast
    rw [hc]
    simp
  have hm : Measurable fun y : Fv F v => x * y := (continuous_const.mul continuous_id).measurable
  ext B hB
  rw [Measure.map_apply hm hB, Measure.smul_apply]
  have e : (fun y => x * y) ⁻¹' B = hu.unit⁻¹ • B := by
    ext y
    rw [Set.mem_smul_set_iff_inv_smul_mem]
    simp [Units.smul_def]
  rw [e, ← distribHaarChar_mul, hc']
  rfl

theorem mass_scalT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ (c : Fv F v ⊗[F] E) (a : ℝ≥0) (t : Fv F v), IsUnit c → a ≠ 0 → (coordK (Fv F v) b lam).map (fun x => c * x) = a • coordK (Fv F v) b lam → algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ c * c → ‖t‖ = (a : ℝ)⁻¹ → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), MeasurableSet A → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) {y | scalT c y ∈ A} = (a : ℝ≥0∞) ^ (M - 1) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) A := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM h₂ d b v lam hlam m hm c a t hcu ha hk hts hnorm A hA
  have hloc := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hloc
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : lam.IsAddHaarMeasure := hlam.1
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam ‹_›
  haveI := hK
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [hσ.2.2.1]; norm_num)
  have hd : d = 2 := by
    rw [← hσ.2.2.1, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have ht : t ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    exact inv_ne_zero ha' hnorm.symm
  have hs := map_mul_fv v lam t ht a hnorm
  set f : Fv F v ⊗[F] E → Fv F v ⊗[F] E := fun y => c * y with hf
  have hfm : Measurable f := (continuous_const.mul continuous_id).measurable
  have hk1 := GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin M) (coordK (Fv F v) b lam) f hfm _ hk
  have hk2 := GlobalTheory.CompanionTheory.SW.Dil.pi_map_scale (ι := Fin 1) (Measure.pi fun _ : Fin M => coordK (Fv F v) b lam)
    (fun x i => f (x i)) (measurable_pi_iff.2 fun i => hfm.comp (measurable_pi_apply i)) _ hk1
  simp only [Fintype.card_fin, pow_one] at hk2
  let g : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E) := Matrix.of fun _ _ => c
  have hg : IsUnit g.det := by
    rw [Matrix.det_fin_one]
    exact hcu
  have hrm : (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g) =
      fun X p i => f (X p i) := by
    funext X p i
    simp only [rmul, Fin.sum_univ_one, g, Matrix.of_apply, hf]
    rw [Subsingleton.elim p 0, mul_comm]
  obtain ⟨-, -, -, hmem, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hσ M J hJ (Fv F v) 1
  let τ : HermR (Fv F v) σ 1 → HermR (Fv F v) σ 1 := fun S =>
    ⟨cT (sigR (Fv F v) σ) g * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) * g, hmem S g⟩
  have hτ : ∀ S, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) = cT (sigR (Fv F v) σ) g * S * g :=
    fun S => rfl
  have hτe : ∀ S i j, (τ S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j =
      algebraMap (Fv F v) (Fv F v ⊗[F] E) t * (S : Matrix (Fin 1) (Fin 1) (Fv F v ⊗[F] E)) i j := by
    intro S i j
    rw [hτ, hts]
    obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp only [Matrix.mul_apply, Fin.sum_univ_one, cT, Matrix.map_apply, Matrix.transpose_apply, g,
      Matrix.of_apply]
    ring
  have hτm : Measurable τ := by
    haveI : BorelSpace (HermR (Fv F v) σ 1) := ⟨rfl⟩
    have h1 : Continuous τ :=
      ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const).subtype_mk _
    exact h1.measurable
  have hc := GlobalTheory.CompanionTheory.SW.Dil.coordHerm_map (Fv F v) σ hσ b lam t ht a hs τ hτm hτe
  have hrmap : Measurable fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => rmul (Fv F v) X g := by
    rw [hrm]
    exact measurable_pi_iff.2 fun p => measurable_pi_iff.2 fun i =>
      hfm.comp ((measurable_pi_apply i).comp (measurable_pi_apply p))
  have hfree : IsOpen {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} :=
    GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.isOpen_free b (Fv F v) hloc (PI.VolStabSW.TensAllW.lip_field _)
  have key := GlobalTheory.CompanionTheory.WeilSiegel.Free.Scale.free_rmul σ hσ J hJ (Fv F v) hloc 1
    (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m (hW 1 M) (hH 1) hm hfree g hg τ hτ _ _
    (by rw [hrm]; exact hk2) hc (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂)
  have hτs : τ (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) =
      hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ := by
    have h0 : hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂ = 0 := by
      apply Subtype.ext
      funext i j
      simp [hermOf]
    rw [h0]
    apply Subtype.ext
    rw [hτ]
    simp
  rw [hτs] at key
  have key2 := congrArg (fun μ' : Measure (Fin 1 → Fin M → Fv F v ⊗[F] E) => μ' A) key
  simp only [Measure.smul_apply, Measure.map_apply hrmap hA] at key2
  have e1 : a ^ M = a * a ^ (M - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hM]
  rw [e1, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, ENNReal.coe_mul, mul_assoc] at key2
  have ha0 : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha
  have key3 := (ENNReal.mul_right_inj ha0 ENNReal.coe_ne_top).1 key2
  have hset : {y : Fin 1 → Fin M → Fv F v ⊗[F] E | scalT c y ∈ A} =
      (fun X => rmul (Fv F v) X g) ⁻¹' A := by
    rw [hrm]
    rfl
  rw [hset, ← key3]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ScaleFib
end
end

section

set_option maxSynthPendingDepth 1

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount
open GroundTheory.Automorphic.HarishChandra

namespace GlobalTheory.CompanionTheory.PresRho

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n : ℕ}

theorem exists_exp {μ : Fin n → ℤ} {x : U n} (h : x ∈ lowSpanW μ ⊔ vermaIdeal (rhoVec n))
    (hx : x ∉ vermaIdeal (rhoVec n)) : ∃ m : Fin n × Fin n →₀ ℕ, LowExp m ∧ wt m = μ := by
  by_contra hne
  have hbot : lowSpanW μ = ⊥ := by
    refine Submodule.span_eq_bot.2 ?_
    rintro _ ⟨m, hm, hw, rfl⟩
    exact absurd ⟨m, hm, hw⟩ hne
  rw [hbot, bot_sup_eq] at h
  exact hx h

theorem lowExp_wt_zero {m : Fin n × Fin n →₀ ℕ} (hm : LowExp m) (h : wt m = 0) : m = 0 := by
  refine GlobalTheory.T.eq_zero_of_low_exponent_casimir m hm (fun i j hij => ⟨1, by simp [h]⟩) ?_
  simp [h]

theorem mem_of_adW_zero {x : U n} (h : x ∈ lowSpanW (0 : Fin n → ℤ) ⊔ vermaIdeal (rhoVec n)) :
    ∃ c : ℂ, x - c • 1 ∈ vermaIdeal (rhoVec n) := by
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.1 h
  clear h
  have : ∃ c : ℂ, y = c • 1 := by
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, hm, hw0, rfl⟩ := hx
      exact ⟨1, by rw [lowExp_wt_zero hm hw0]; simp⟩
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, rfl⟩ := hx
      obtain ⟨d, rfl⟩ := hy
      exact ⟨c + d, by rw [add_smul]⟩
    | smul r x _ hx =>
      obtain ⟨c, rfl⟩ := hx
      exact ⟨r * c, by rw [mul_smul]⟩
  obtain ⟨c, rfl⟩ := this
  exact ⟨c, by simpa using hw⟩

theorem mem_Jp_of_adW {A : Type} [AddCommGroup A] [Module ℂ A]
    (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A) (ht0 : t ≠ 0)
    (hd : ∀ k, φ (e (k, k)) t = rhoVec n k • t)
    (hu : ∀ a : Fin n × Fin n, IsUpper a → φ (e a) t = 0) :
    ∀ (N : ℕ) (μ : Fin n → ℤ) (x : U n), -ht μ < N → IsAdW μ x → φ x t = 0 → x ∈ Jp n := by
  intro N
  induction N with
  | zero =>
    intro μ x hN hx h0
    by_contra hJ
    obtain ⟨m, hm, rfl⟩ := exists_exp (GlobalTheory.T.weight_vector_mem_low_span_sup_verma μ x hx) fun h => hJ (vermaIdeal_le_Jp h)
    have := ht_wt_nonpos hm
    push_cast at hN
    omega
  | succ N ih =>
    intro μ x hN hx h0
    by_contra hJ
    obtain ⟨m, hm, rfl⟩ := exists_exp (GlobalTheory.T.weight_vector_mem_low_span_sup_verma μ x hx) fun h => hJ (vermaIdeal_le_Jp h)
    have hup : ∀ a : Fin n × Fin n, IsUpper a → e a * x ∈ Jp n := by
      intro a ha
      refine ih _ _ ?_ (hx.e_mul a) (by simp [h0])
      rw [ht_add_rootAt, ht_rootAt]
      have h1 : (a.1 : ℕ) < a.2 := ha
      push_cast at hN
      omega
    have hm0 : m = 0 := GlobalTheory.T.eq_zero_of_low_exponent_casimir m hm
      (fun i j hij => GlobalTheory.T.nat_of_simple_lowering_nilpotent (wt m) x i j hx hup hJ hij (GlobalTheory.T.simple_lowering_pow_mem_ideal i j x hij))
      (GlobalTheory.T.casimir_eq_of_singular_weight_vector (wt m) x hx hup hJ)
    subst hm0
    have hw0 : wt (0 : Fin n × Fin n →₀ ℕ) = 0 := by ext k; simp [wt]
    rw [hw0] at hx
    obtain ⟨c, hc⟩ := mem_of_adW_zero (GlobalTheory.T.weight_vector_mem_low_span_sup_verma 0 x hx)
    have h1 := act_eq_zero_of_mem φ t hd hu hc
    rw [map_sub, LinearMap.sub_apply, h0, zero_sub, map_smul, map_one] at h1
    have hc0 : c = 0 := by
      by_contra hne
      simp [hne, ht0] at h1
    rw [hc0, zero_smul, sub_zero] at hc
    exact hJ (vermaIdeal_le_Jp hc)

theorem word_mem_lowSpan {l : List (Fin n × Fin n)} (hl : ∀ p ∈ l, p.2 < p.1) :
    word l ∈ lowSpan n := by
  refine (Submodule.span_le.2 ?_) (word_mem_canonSpan closed_lower l hl)
  rintro _ ⟨m, hm, -, -, rfl⟩
  exact Submodule.subset_span ⟨m, hm, rfl⟩

theorem rho_cast (a : Fin n) : ((rhoV n a : ℝ) : ℂ) = rhoVec n a := by
  simp [rhoV, rhoVec]

theorem act_eq_zero_of_sqSpan {Z : Type} [AddCommGroup Z] [Module ℂ Z]
    {F : Fin n → Fin n → Module.End ℂ Z} (φ : U n →ₐ[ℂ] Module.End ℂ Z)
    (hφ : ∀ i j, φ (e (i, j)) = F i j) (z : Z)
    (hz : ∀ i j : Fin n, (j : ℕ) = i + 1 → ((F j i) ^ 2) z = 0) {x : U n}
    (hx : x ∈ sqSpan n) : φ x z = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨u, i, j, hij, rfl⟩ := hx
    simp only [map_mul, map_pow, hφ, Module.End.mul_apply]
    rw [hz i j hij, map_zero]
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => simp [hx]

theorem pres_rho : ∀ {n : ℕ} {A Z : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup Z] [Module ℂ Z]
    (G : Fin n → Fin n → Module.End ℂ A) (F : Fin n → Fin n → Module.End ℂ Z),
    Formalism.REAL.GlRel G → Formalism.REAL.GlRel F → ∀ t : A, t ≠ 0 →
    (∀ a, G a a t = ((rhoV n a : ℝ) : ℂ) • t) → (∀ a b, a < b → G a b t = 0) →
    ∀ z : Z, (∀ i j : Fin n, (j : ℕ) = i + 1 → ((F j i) ^ 2) z = 0) →
    ∀ (s : Finset (List (Fin n × Fin n))) (coef : List (Fin n × Fin n) → ℂ), (∀ l ∈ s, ∀ p ∈ l, p.2 < p.1) →
    ∑ l ∈ s, coef l • (l.map fun p => G p.1 p.2).prod t = 0 →
    ∑ l ∈ s, coef l • (l.map fun p => F p.1 p.2).prod z = 0 := by
  intro n A Z _ _ _ _ G F hG hF t ht0 hd hu z hz s coef hs hsum
  obtain ⟨φ, hφ⟩ := exists_act G hG
  obtain ⟨ψ, hψ⟩ := exists_act F hF
  have hd' : ∀ k, φ (e (k, k)) t = rhoVec n k • t := fun k => by
    rw [hφ, hd, rho_cast]
  have hu' : ∀ a : Fin n × Fin n, IsUpper a → φ (e a) t = 0 := fun a ha => by
    rw [show e a = e (a.1, a.2) from rfl, hφ]; exact hu _ _ ha
  set Y : U n := ∑ l ∈ s, coef l • word l with hY
  have hYlow : Y ∈ lowSpan n :=
    Submodule.sum_mem _ fun l hl => Submodule.smul_mem _ _ (word_mem_lowSpan (hs l hl))
  have hYt : φ Y t = 0 := by

    rw [hY, map_sum, LinearMap.sum_apply, ← hsum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, LinearMap.smul_apply, act_word φ hφ]
  have hYJ : Y ∈ Jp n := by
    refine (Submodule.span_le.2 ?_) (GlobalTheory.T.annihilator_spanned_by_weight_vectors φ t hd' Y hYt)
    rintro y ⟨μ, hy, h0⟩
    exact mem_Jp_of_adW φ t ht0 hd' hu' (-ht μ + 1).toNat μ y (by omega) hy h0
  have hYs := GlobalTheory.T.low_span_inf_ideal_le_square_span Y hYlow hYJ
  have h := act_eq_zero_of_sqSpan ψ hψ z hz hYs

  rw [hY, map_sum, LinearMap.sum_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, LinearMap.smul_apply, act_word ψ hψ]

end GlobalTheory.CompanionTheory.PresRho
end
end

section

open GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G GlobalTheory.CompanionTheory.MPDict

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.MPSmooth

theorem smooth_of_isHermRep : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)),
    IsHermRep M A → Geo.IsSmoothHerm A :=
  GlobalTheory.CompanionTheory.MPDict.SmoothRep.isSmoothHerm_of_isHermRep

end GlobalTheory.CompanionTheory.MPSmooth
end

section

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

theorem _root_.GlobalTheory.T.complex_points_second_countable : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ),
    GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) D → SecondCountableTopology (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.ArchEq.secondCountable_cxPts | exact GlobalTheory.CompanionTheory.MixZ.ArchEq.secondCountable_cxPts | (intros; apply GlobalTheory.CompanionTheory.MixZ.ArchEq.secondCountable_cxPts <;> assumption)
end

section

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

theorem dict_ptIdeal_injective {m : ℕ} (n : Fin (m + 1) → ℕ) :
    Function.Injective (ptIdeal : MP ℤ m n → Ideal (Geo.MRing (Bk n))) := fun x y h =>
  (((GlobalTheory.T.specializes_iff_point_ideal_le m n x y).2 h.le).antisymm ((GlobalTheory.T.specializes_iff_point_ideal_le m n y x).2 h.ge)).eq

end GlobalTheory.CompanionTheory.MPDict
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.rank_one_free_fibre_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW (Fv F v) b lam 1 M) (fun X : Fin 1 → Fin M → Fv F v ⊗[F] E => algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (gramR (Fv F v) σ J X 0 0)) id {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} lam Set.univ (fun s => m (hermScal (Fv F v) σ s)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.isFibreFamily_length | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.isFibreFamily_length | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.isFibreFamily_length <;> assumption)
end
