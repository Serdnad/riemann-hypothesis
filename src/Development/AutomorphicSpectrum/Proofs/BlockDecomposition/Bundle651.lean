module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle045
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle025
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle034
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle028
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle084
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
public import Development.WeilBound.CoreStatements.ThetaDilations.Bundle001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle008
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import GroundTheory.GlobalFields.LocalFieldAtPlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle452
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle636
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle637
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle638
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle472
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHighestWeightHermitianDerivation
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle608
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle631
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle633
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle622
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockTriangularMemMinimalParabolic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.ThetaFrame

theorem free_act {S : Type} [CommRing S] {M n : ℕ} (g : GL (Fin M) S) {Y : Fin n → Fin M → S}
    (hY : LinearIndependent S Y) :
    LinearIndependent S fun a => (g : Matrix (Fin M) (Fin M) S) *ᵥ Y a := by
  have hk : LinearMap.ker (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) S)) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y h
    have h2 := congrArg (Matrix.mulVec ((g⁻¹ : GL (Fin M) S) : Matrix (Fin M) (Fin M) S)) h
    simpa [Matrix.mulVec_mulVec] using h2
  exact hY.map' _ hk

theorem free_of_unit {S : Type} [CommRing S] {M : ℕ} {Y : Fin 1 → Fin M → S} {i : Fin M}
    (hu : IsUnit (Y 0 i)) : LinearIndependent S Y := by
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have h1 := congrFun hg i
  simp only [Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
  rw [Subsingleton.elim a 0]
  exact hu.mul_left_eq_zero.1 h1

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem free_ratTup (R : Type) [CommRing R] [Algebra F R] {M : ℕ} {X : Fin 1 → Fin M → E}
    (hX : LinearIndependent E X) : LinearIndependent (R ⊗[F] E) (ratTup (F := F) R X) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 (hX.ne_zero 0)
  exact free_of_unit (i := i) ((isUnit_iff_ne_zero.2 hi).map (inclR (F := F) R))

variable [NumberField F]

theorem projInf_ratTup {M n : ℕ} (X : Fin n → Fin M → E) :
    projInf (ratTup (F := F) (AF F) X) = ratTup (Ainf F) X := by
  funext a i
  simp [projInf, ratTup, inclR]

theorem projV_ratTup (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ} (X : Fin n → Fin M → E) :
    projV v (projFin (ratTup (F := F) (AF F) X)) = ratTup (Fv F v) X := by
  funext a i
  simp [projV, projFin, ratTup, inclR]

theorem act_rat_free {σ : E →ₐ[F] E} {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (γ : HFinIn (AF F) σ J)
    {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    ∃ X' : Fin n → Fin M → E, LinearIndependent E X' ∧
      actW (AF F) σ J γ.1 (ratTup (AF F) X) = ratTup (AF F) X' := by
  obtain ⟨γ, g, -, e⟩ := γ
  refine ⟨fun a => g.val *ᵥ X a, free_act g hX, funext fun a => funext fun i => ?_⟩
  have e' : (HA.mat (AF F) σ J γ).val = g.val.map (inclR (AF F)) := (congrArg Units.val e).symm

  simp only [actW, actTup, e', ratTup, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

end Rat

theorem theta_inv_of_stable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) (hμ : IsHaarH F E σ M J μ)
    (h𝓕 : IsFDH F E σ M J μ 𝓕) (n : ℕ) (S : Set (Fin n → Fin M → E))
    (hS : ∀ (γ : HFinIn (AF F) σ J) (X : Fin n → Fin M → E), X ∈ S →
      ∃ X' ∈ S, actW (AF F) σ J γ.1 (ratTup (AF F) X) = ratTup (AF F) X')
    (h : HA (AF F) σ J) :
    (thetaMeas σ J μ 𝓕 S).map (actW (AF F) σ J h) = thetaMeas σ J μ 𝓕 S := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  obtain ⟨ac, a1, a2, ag⟩ := hact n
  have hl := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 n S
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  have hri : Function.Injective (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _) := fun X Y h =>
    funext fun a => funext fun i => hinj (congrFun (congrFun h a) i)
  have hm : Measurable (actW (AF F) σ J h : (Fin n → Fin M → _) → _) :=
    (ac.comp (continuous_const.prodMk continuous_id)).measurable
  have hfin := ((GlobalTheory.T.unitary_group_finite_volume F E σ hcm M J hJ).2 μ hμ).2 𝓕 h𝓕
  have : μ.IsHaarMeasure := hμ
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : Countable Γ := (GlobalTheory.T.arithmetic_unitary_group_discrete F E σ hcm M J hJ).1
  have h𝓕' : IsFundamentalDomain Γ 𝓕 μ := h𝓕
  obtain ⟨-, _, -⟩ := GlobalTheory.T.finite_covolume_unimodular (HA (AF F) σ J) Γ μ 𝓕 h𝓕' hfin
  refine Measure.ext_of_lintegral _ fun Φ hΦ => ?_
  rw [lintegral_map hΦ hm, hl (fun X => Φ (actW (AF F) σ J h X)) (hΦ.comp hm), hl _ hΦ]
  congr 1
  set f : HA (AF F) σ J → ℝ≥0∞ := fun g => ∑' X : S,
    Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) with hf
  have hle : ∀ (γ : Γ) g, f (γ • g) ≤ f g := fun γ g => by
    choose t hts ht using fun X : S => hS γ⁻¹ X.1 X.2
    have ht' : ∀ X, actW (AF F) σ J (γ : HA (AF F) σ J)⁻¹ (ratTup (AF F) X.1) = ratTup (AF F) (t X) := ht
    have hti : Function.Injective fun X => (⟨t X, hts X⟩ : S) := fun X Y e => by
      have h1 := congrArg (actW (AF F) σ J γ) ((ht' X).trans ((congrArg (fun Z => ratTup (AF F) Z.1) e).trans (ht' Y).symm))
      simp only [← a2, mul_inv_cancel, a1] at h1
      exact Subtype.ext (hri h1)
    refine le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hti _)
    rw [Subgroup.smul_def, smul_eq_mul, mul_inv_rev, a2, ht']
  have hinv : ∀ (γ : Γ) g, f (γ • g) = f g := fun γ g =>
    (hle γ g).antisymm (by simpa using hle γ⁻¹ (γ • g))
  have hD := h𝓕'.preimage_of_equiv (measurePreserving_mul_right μ h).quasiMeasurePreserving (e := id)
    Function.bijective_id fun γ g => (mul_assoc _ _ _)
  rw [h𝓕'.setLIntegral_eq hD f hinv, ← (measurePreserving_mul_right μ h).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulRight _)]
  simp only [hf, mul_inv_rev, ← a2, mul_inv_cancel_left]

theorem measurableSet_free (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧
      LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))} := by
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB 1 M
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; norm_num)
  obtain ⟨c1, c2, c3, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hcm _ (Module.finBasis F E) 1 M
  have o1 : IsOpen {X : Fin 1 → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    PI.VolStabSW.TensAllW.isOpen_linIndep (Module.finBasis F E) (Ainf F) (PI.VolStabSW.isOpen_units_Ainf F)
      (PI.VolStabSW.lip_ainf F)
  have o2 : ∀ v, IsOpen {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := fun v =>
    PI.VolStabSW.TensAllW.isOpen_linIndep (Module.finBasis F E) (Fv F v) (PI.VolStabSW.isOpen_units_Fv F v)
      (PI.VolStabSW.TensAllW.lip_field _)
  have m1 : MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F))} :=
    (isClosed_eq (hg 1 M J) continuous_const).measurableSet
  have m2 : MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) (projInf X)} :=
    (o1.preimage c1).measurableSet
  have m3 : MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun v => (((o2 v).preimage (c3 v)).preimage c2).measurableSet
  exact m1.inter (m2.inter m3)

theorem theta_frames_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsLocallyFiniteMeasure (thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) ∧ (∀ h : HA (AF F) σ J, (thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))).map (actW (AF F) σ J h) = thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) ∧ thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)) {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧ LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))}ᶜ = 0 := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM μ 𝓕 hμ h𝓕
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB 1 M
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm M J hJ (AF F)
  obtain ⟨ac, a1, a2, ag⟩ := hact 1
  have hrat := (GlobalTheory.T.gram_matrix_local_global F E σ hcm M J hJ 1 0 0).2
  obtain ⟨pinf, p, hp, -, -⟩ := GlobalTheory.T.adelic_unitary_group_projections F E σ hcm M J hJ
  have hl := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 1
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  refine ⟨⟨fun X => ?_⟩, fun h => ?_, ?_⟩
  · obtain ⟨K, hK, hX⟩ := exists_compact_mem_nhds X
    obtain ⟨N, r, hN, hr, hsub⟩ := (GlobalTheory.T.adelic_tuple_compact_sets F E σ hcm _ (Module.finBasis F E) 1 M).2 K hK
    obtain ⟨C, hC⟩ := GlobalTheory.T.theta_measure_nonzero_vectors_bound F E σ hcm M J hJ hM _ (Module.finBasis F E) μ 𝓕 hμ h𝓕 N hN
    refine ⟨K, hX, lt_of_le_of_lt (le_trans ?_ ((measure_mono (fun X hX => hsub X hX)).trans (hC r hr))) ENNReal.ofReal_lt_top⟩
    have hm : Measurable (K.indicator (1 : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)) := measurable_one.indicator hK.measurableSet
    rw [← lintegral_indicator_one hK.measurableSet, ← lintegral_indicator_one hK.measurableSet,
      hl _ _ hm, hl _ _ hm]
    have hs : framesE σ J (0 : Matrix (Fin 1) (Fin 1) E) ⊆ {X | X ≠ 0} :=
      fun X hX h0 => hX.1.ne_zero 0 (congrFun h0 0)
    exact mul_le_mul_right (lintegral_mono fun h => ENNReal.tsum_mono_subtype (fun X => K.indicator
      (1 : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞) (actW (AF F) σ J h⁻¹ (ratTup (AF F) X))) hs) _
  · refine theta_inv_of_stable F E σ hcm M J hJ μ 𝓕 hμ h𝓕 1 _ (fun γ X hX => ?_) h
    obtain ⟨X', hX', e⟩ := act_rat_free γ hX.1
    refine ⟨X', ⟨hX', ?_⟩, e⟩
    refine Matrix.map_injective hinj ?_
    show (gramE σ J X').map (inclR (AF F)) = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F))
    rw [← hrat, ← e]
    refine (ag _ _).trans ?_
    rw [hrat, hX.2]
  · have hc := (measurableSet_free F E σ hcm M J).compl
    rw [← lintegral_indicator_one hc, hl _ _ (measurable_one.indicator hc)]
    have e : ∀ (h : HA (AF F) σ J) (X : framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)), Set.indicator
        {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧
          LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))}ᶜ
        (1 : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
        (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)) = 0 := fun h X => by
      apply Set.indicator_of_notMem
      rw [Set.notMem_compl_iff]
      refine ⟨?_, ?_, fun v => ?_⟩
      · rw [ag, hrat, X.2.2]
      · rw [(hp 1 h⁻¹ _).1, projInf_ratTup]
        exact free_act (HA.mat (Ainf F) σ J (pinf h⁻¹)) (free_ratTup _ X.2.1)
      · rw [(hp 1 h⁻¹ _).2 v, projV_ratTup]
        exact free_act (HA.mat (Fv F v) σ J (p v h⁻¹)) (free_ratTup _ X.2.1)
    simp only [e, tsum_zero, lintegral_zero, mul_zero]

end GlobalTheory.CompanionTheory.WeilSiegel.Free.ThetaFrame
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

theorem _root_.GlobalTheory.T.local_volume_unramified_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)) m, μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree (Fv F v) σ J n μ ν m → ∀ h : HA (Fv F v) σ (blockOne (algebraMap F E t) J), m (hermOf (Fv F v) σ T hT) {X | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} = (latV b v).indicator (fun _ => m (hermOf (Fv F v) σ T hT) (latV b v)) (actW (Fv F v) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageGoodFree.stage_good_free | exact GlobalTheory.CompanionTheory.SW.StageGoodFree.stage_good_free | (intros; apply GlobalTheory.CompanionTheory.SW.StageGoodFree.stage_good_free <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.fibre_measure_extension_by_one_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ S ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))), ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) = (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) * (cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) ^ n * Pint σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.lintegral_fibSF_of_mem | exact GlobalTheory.CompanionTheory.SW.StageF.lintegral_fibSF_of_mem | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.lintegral_fibSF_of_mem <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.fibre_measure_extension_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ {X | LinearIndependent (R ⊗[F] E) X} → ∀ S ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))), Integrable φ (fibSF σ J t m₁ m' s B₀ a κ₁ cm S) ∧ ∫ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) = ((κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) * cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n : ℝ≥0) : ℝ) * Preal σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.integrable_fibSF_and_integral | exact GlobalTheory.CompanionTheory.SW.StageF.integrable_fibSF_and_integral | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.integrable_fibSF_and_integral <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.fibre_measure_extension_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (UsetF σ J t B₀ : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = MidF σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.lintegral_UsetF_eq_MidF | exact GlobalTheory.CompanionTheory.SW.StageF.lintegral_UsetF_eq_MidF | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.lintegral_UsetF_eq_MidF <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.fibre_measure_extension_sigma_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ {X | LinearIndependent (R ⊗[F] E) X} → ContinuousOn (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => Preal σ J t m₁ m' s φ z.1 z.2.1 z.2.2) ({α : R | IsUnit α} ×ˢ (Set.univ ×ˢ Set.univ)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.ContTwoF.cont_double_free | exact GlobalTheory.CompanionTheory.SW.StageF.ContTwoF.cont_double_free | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.ContTwoF.cont_double_free <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.fibre_measure_extension_by_one_formula : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S : HermR R σ (n + 1), fibSF σ J t m₁ m' s B₀ a κ₁ cm S (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩ UsetF σ J t B₀)ᶜ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.fibSF_support | exact GlobalTheory.CompanionTheory.SW.StageF.fibSF_support | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.fibSF_support <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.fibre_measure_extension_symmetric : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → Measurable (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => Pint σ J t m₁ m' s φ z.1 z.2.1 z.2.2) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.measurable_PintF | exact GlobalTheory.CompanionTheory.SW.StageF.measurable_PintF | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.measurable_PintF <;> assumption)
end

section

open Matrix
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

theorem GlobalTheory.T.exists_highest_weight_hermitian_derivation :
    ∀ {n : ℕ} (ν : Fin n → ℤ), Antitone ν →
    ∃ (L : Type) (_ : NormedAddCommGroup L) (_ : InnerProductSpace ℂ L)
      (_ : FiniteDimensional ℂ L) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (L →ₗ[ℂ] L))
      (K : Fin n → Fin n → Module.End ℂ L) (v : L),
      Formalism.REAL.GlRel K ∧ (∀ a b (x y : L), ⟪K a b x, y⟫_ℂ = ⟪x, K b a y⟫_ℂ) ∧
      IsDerivK σ K ∧ v ≠ 0 ∧ Formalism.REAL.KHighest (fun _ => true) K (wtR ν) v ∧
      (∀ w : L, (∀ a b, a < b → K a b w = 0) → ∃ c : ℂ, w = c • v) ∧
      ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ),
        k.1 = diagonal z → Function.Injective z → LinearMap.trace ℂ L (σ k) = weylChar ν z :=
  @GlobalTheory.CompanionTheory.RmModel.rmModel
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef

theorem schwartzBruhat_eq_sum_pureTuples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), IsSchwartzBruhat Φ → ∃ (N : ℕ) (φ : Fin N → (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : Fin N → (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))) (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ i, IsSchwartzArch (φ i)) ∧ (∀ i v, IsCompact (A i v) ∧ IsOpen (A i v)) ∧ (∀ i v, v ∉ S → A i v = latV b v) ∧ ∀ X, Φ X = ∑ i, pureN (φ i) (A i) X := by
  intro F E _ _ _ _ _ σ _ M J _ n _ d b Φ hΦ
  classical
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨k, Φinf, Φf, hinf, hf, hsum⟩ := hΦ
  choose s A S hA hAS hdec using fun i => GlobalTheory.CompanionTheory.WhitFree.DecN.exists_box_combN b (Φf i) (hf i)
  let e := Fintype.equivFin (Σ i : Fin k, (s i))
  refine ⟨Fintype.card (Σ i : Fin k, (s i)),
    fun j Z => Φinf (e.symm j).1 Z * Φf (e.symm j).1 (e.symm j).2,
    fun j => A (e.symm j).1 (e.symm j).2, Finset.univ.biUnion S, ?_, ?_, ?_, ?_⟩
  · intro j
    exact GlobalTheory.CompanionTheory.WhitFree.DecN.isSchwartzArch_const_mulN (hinf _) _
  · intro j v
    exact hA _ _ v
  · intro j v hv
    exact hAS _ _ (e.symm j).2.2 v
      (fun h => hv (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, h⟩))
  · intro X
    rw [hsum X]
    symm
    refine (Equiv.sum_comp e.symm (fun p : (Σ i : Fin k, (s i)) =>
      pureN (fun Z => Φinf p.1 Z * Φf p.1 p.2) (A p.1 p.2) X)).trans ?_
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hdec i (projFin X), Finset.mul_sum, ← Finset.sum_coe_sort (s i)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    unfold GlobalTheory.CompanionTheory.SiegelND.Coef.pureN
    exact mul_assoc _ _ _

end GlobalTheory.CompanionTheory.SiegelND.Coef
end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal

theorem _root_.GlobalTheory.T.factorizable_schwartz_orbital_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : (∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))), IsSchwartzArch φ → (∀ v, IsCompact (A v) ∧ IsOpen (A v)) → (∀ v, v ∉ S → A v = latV b v) → IsSchwartzBruhat (pureN φ A) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.pureN_isSchwartzBruhat | exact GlobalTheory.CompanionTheory.SiegelND.Coef.pureN_isSchwartzBruhat | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.pureN_isSchwartzBruhat <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

theorem _root_.GlobalTheory.T.block_triangular_mem_minimal_parabolic : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (A : Type) [CommRing A] [Algebra F A] [TopologicalSpace A] (p : HA A σ J) (B : Matrix (Fin r) (Fin r) (A ⊗[F] E)), B.BlockTriangular id → (matHom A σ J p).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B → ∃ m : HA A σ J, (matHom A σ J m).1 = leviMat σ J A X Y (matHom A σ J p).1 ∧ (∃ d : Fin r → A ⊗[F] E, (matHom A σ J m).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * diagonal d) ∧ (∃ d' : Fin r → A ⊗[F] E, (matHom A σ J m).1 * Y.map (inclR (F := F) A) = Y.map (inclR (F := F) A) * diagonal d') ∧ (∃ B' : Matrix (Fin r) (Fin r) (A ⊗[F] E), B'.BlockTriangular id ∧ (∀ i, B' i i = 1) ∧ (matHom A σ J (m⁻¹ * p)).1 * X.map (inclR (F := F) A) = X.map (inclR (F := F) A) * B') ∧ ∀ z : Fin n → A ⊗[F] E, ((cT (σ : E →+* E) X * J).map (inclR (F := F) A)) *ᵥ z = 0 → ∃ a : Fin r → A ⊗[F] E, ((matHom A σ J (m⁻¹ * p)).1 - 1) *ᵥ z = X.map (inclR (F := F) A) *ᵥ a := by
  first | exact @GlobalTheory.CompanionTheory.KFin.LeviPt.exists_levi | exact GlobalTheory.CompanionTheory.KFin.LeviPt.exists_levi | (intros; apply GlobalTheory.CompanionTheory.KFin.LeviPt.exists_levi <;> assumption)
end
