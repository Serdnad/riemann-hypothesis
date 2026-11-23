module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle042
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle025
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle024
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.WeilBound.CoreStatements.ThetaDilations.Bundle001
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
public import GroundTheory.GlobalFields.TateThesis.Bundle006
public import GroundTheory.IdeleRoots.TorusPowers.HeckeTensor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle006
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle727
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle728
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormulaOfComponents
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityRatioFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarFibrationFormula
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle726

@[expose] public section

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem actW_rat_one {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix (Fin 1) (Fin 1) E) (g : HA (AF F) σ J) (X : Fin 1 → Fin 1 → E) (a i : Fin 1) :
    actW (AF F) σ J g (ratTup (AF F) X) a i = (ue (AF F) σ J g : AF F ⊗[F] E) * inclR (AF F) (X a i) := by
  have e : ((ue (AF F) σ J g : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (HA.mat (AF F) σ J g).val 0 0 := by
    simp [ue, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  rw [e]
  simp only [actW, actTup, Matrix.mulVec, dotProduct, ratTup, Fin.sum_univ_one, Subsingleton.elim i 0,
    Subsingleton.elim a 0]

theorem mean_eq_lint : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ 1 J μ → IsFDH F E σ 1 J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ x : (AF F ⊗[F] E)ˣ, mean σ J μ 𝓕 φ A x = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, Th φ A (x * ue (AF F) σ J h⁻¹) ∂μ ∧ Measurable fun h : HA (AF F) σ J => Th φ A (x * ue (AF F) σ J h⁻¹) := by
  intro F E _ _ _ _ _ σ hcm J hJ μ 𝓕 hμ h𝓕 d b S φ A hT x
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨_, _, _, _, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (AF F)
  have := hB 1 1
  obtain ⟨_, _, _, _, _, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hcm 1 J hJ (AF F)
  obtain ⟨ac, -, -, -⟩ := hact 1
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨k1, -, -, -, -, -, -, k8, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)
  have := k8 1 1
  obtain ⟨t1, t2, t3, t4, t5, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 1
  obtain ⟨hφc, -, hφ0, -, hAS, hAoff⟩ := hT
  have hs : ∀ v, Continuous fun X : Fin 1 → Fin 1 → AF F ⊗[F] E => projV v (projFin X) := fun v => (t3 v).comp t2
  have hP : IsOpen {X : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} := by
    have e : {X : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin X) ∈ A v} =
        (⋂ v ∈ S, (fun X => projV v (projFin X)) ⁻¹' A v) ∩ intOff b S := by
      ext X
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, intOff]
      refine ⟨fun h => ⟨fun v _ => h v, fun v hv => hAoff v hv ▸ h v⟩, fun h v => ?_⟩
      by_cases hv : v ∈ S
      · exact h.1 v hv
      · rw [hAoff v hv]; exact h.2 v hv
    rw [e]
    exact (isOpen_biInter_finset fun v hv => (hAS v hv).2.1.preimage (hs v)).inter (t5 S)
  have hPsi : Measurable (Psi φ A) :=
    (ENNReal.measurable_ofReal.comp (hφc.comp t1).measurable).indicator hP.measurableSet
  have hmul : Continuous fun (Y : Fin 1 → Fin 1 → AF F ⊗[F] E) (a i : Fin 1) => (x : AF F ⊗[F] E) * Y a i :=
    continuous_pi fun a => continuous_pi fun i => continuous_const.mul (continuous_apply_apply a i)
  set Φ : (Fin 1 → Fin 1 → AF F ⊗[F] E) → ℝ≥0∞ := fun Y => Psi φ A fun a i => (x : AF F ⊗[F] E) * Y a i with hΦd
  have hΦ : Measurable Φ := hPsi.comp hmul.measurable
  have hQ : MeasurableSet {X : Fin 1 → Fin 1 → AF F ⊗[F] E | ∀ v, projV v (projFin fun a i => (x : AF F ⊗[F] E) * X a i) ∈ A v} :=
    (hP.preimage hmul).measurableSet
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  have hterm : ∀ (h : HA (AF F) σ J), Th φ A (x * ue (AF F) σ J h⁻¹) =
      ∑' X : ({X : Fin 1 → Fin 1 → E | X ≠ 0} : Set _), Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)) := fun h => by
    refine tsum_congr fun X => ?_
    simp only [hΦd]
    congr 1
    funext a i
    rw [actW_rat_one, Units.val_mul, mul_assoc]
  refine ⟨?_, ?_⟩
  · simp only [hterm]
    rw [← PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm 1 J hJ μ 𝓕 hμ h𝓕 1 _ Φ hΦ, mean, ← lintegral_indicator hQ]
    refine lintegral_congr fun X => ?_
    simp only [hΦd, Psi, Set.indicator, Set.mem_setOf_eq]
  · simp only [hterm]
    exact Measurable.tsum fun X => hΦ.comp (ac.comp (continuous_inv.prodMk continuous_const)).measurable

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem isNm_ue_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ h : HA (AF F) σ J, IsNm σ (ue (AF F) σ J h) 1 := by
  intro F E _ _ _ _ _ σ _ J hJ h
  have hg : cT (sigR (AF F) σ) ((HA.mat (AF F) σ J h : GL (Fin 1) (AF F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)) * JR (AF F) J *
      ((HA.mat (AF F) σ J h : GL (Fin 1) (AF F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)) = JR (AF F) J := h.2
  have hx : ((ue (AF F) σ J h : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      ((HA.mat (AF F) σ J h : GL (Fin 1) (AF F ⊗[F] E)) :
      Matrix (Fin 1) (Fin 1) (AF F ⊗[F] E)) 0 0 := by
    simp only [ue, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
  have he := congrFun (congrFun hg 0) 0
  simp only [Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, cT, JR, Matrix.transpose_apply,
    Matrix.map_apply, Fin.default_eq_zero, Fin.isValue] at he
  have hj : J 0 0 ≠ 0 := by
    have := hJ.2
    rwa [Matrix.det_fin_one] at this
  have hu : IsUnit (inclR (F := F) (AF F) (J 0 0)) := (IsUnit.mk0 _ hj).map (inclR (F := F) (AF F))
  show ((1 : (AF F)ˣ) : AF F) ⊗ₜ[F] (1 : E) = sigR (AF F) σ _ * _
  rw [hx, Units.val_one, ← Algebra.TensorProduct.one_def]
  apply hu.mul_left_cancel
  rw [mul_one]
  exact he.symm.trans (by ring)

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
end

section

set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MdBase

section

open NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global
  GroundTheory.Global.AdeleBaseChange MeasureTheory.Measure
open scoped ENNReal NNReal NumberField.AdeleRing

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem map_smul_pi (n : ℕ) (a : IdeleGroup K) :
    (Measure.pi fun _ : Fin n ↦ adeleMeasure K).map (fun x i ↦ a • x i) =
      (Real.toNNReal ((IdeleGroup.ideleModule K a : ℝ))⁻¹) ^ n •
        Measure.pi fun _ : Fin n ↦ adeleMeasure K := by
  have hsm : Measurable fun y : 𝔸[K] ↦ a • y := (Homeomorph.smul a).continuous.measurable
  have hmeas : Measurable fun x : Fin n → 𝔸[K] ↦ fun i ↦ a • x i :=
    Measurable.of_eval fun i ↦ hsm.comp (measurable_pi_apply i)
  set c : ℝ≥0 := Real.toNNReal ((IdeleGroup.ideleModule K a : ℝ))⁻¹ with hcdef
  have hmap : (adeleMeasure K).map (fun y ↦ a • y) = c • adeleMeasure K := by
    rw [map_smul_adeleMeasure]
    rfl
  have h1 : (Measure.pi fun _ : Fin n ↦ adeleMeasure K).map (fun x i ↦ a • x i) =
      Measure.pi fun _ : Fin n ↦ c • adeleMeasure K := by
    refine (pi_eq fun s hs ↦ ?_).symm
    rw [map_apply hmeas (MeasurableSet.univ_pi hs)]
    have hpre : (fun x : Fin n → 𝔸[K] ↦ fun i ↦ a • x i) ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i ↦ (fun y ↦ a • y) ⁻¹' s i := by
      ext x
      simp
    rw [hpre, pi_pi]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [← hmap, map_apply hsm (hs i)]
  have h2 : (Measure.pi fun _ : Fin n ↦ c • adeleMeasure K) =
      c ^ n • Measure.pi fun _ : Fin n ↦ adeleMeasure K := by
    refine pi_eq fun s hs ↦ ?_
    rw [Measure.smul_apply, pi_pi, ENNReal.smul_def, smul_eq_mul]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ENNReal.coe_pow]
  rw [h1, h2]

theorem ideleModule_ideleEmbedding (x : IdeleGroup K) :
    (IdeleGroup.ideleModule L (ideleEmbedding K L x) : ℝ) =
      (IdeleGroup.ideleModule K x : ℝ) ^ Module.finrank K L := by
  have := isModuleTopology_adeleRing (K := K) (L := L)
  set n := Module.finrank K L with hn
  let e : 𝔸[L] ≃ₗ[𝔸[K]] (Fin n → 𝔸[K]) := (adeleBasis (Module.finBasis K L)).equivFun
  have hce : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hcs : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let h : 𝔸[L] ≃ₜ (Fin n → 𝔸[K]) :=
    { toEquiv := e.toEquiv, continuous_toFun := hce, continuous_invFun := hcs }
  set μ : Measure (Fin n → 𝔸[K]) := Measure.pi fun _ ↦ adeleMeasure K with hμ
  set ν : Measure 𝔸[L] := μ.map e.symm with hν
  have hms : Measurable e.symm := hcs.measurable
  haveI : ν.IsAddHaarMeasure :=
    isAddHaarMeasure_map _ e.symm.toLinearMap.toAddMonoidHom hcs e.symm.surjective
      h.symm.isClosedEmbedding.tendsto_cocompact
  set X := ideleEmbedding K L x with hX
  have hcomp : (fun y : 𝔸[L] ↦ X • y) ∘ e.symm = e.symm ∘ (fun v i ↦ x • v i) := by
    funext v
    have hv : (fun i ↦ x • v i) = (x : 𝔸[K]) • v := by
      funext i
      simp [Units.smul_def]
    simp only [Function.comp_apply]
    rw [hv, map_smul, Units.smul_def]
    change (X : 𝔸[L]) * e.symm v = (x : 𝔸[K]) • e.symm v
    rw [Algebra.smul_def (x : 𝔸[K]), algebraMap_adeleRing]
    rfl
  have hsmL : Measurable fun y : 𝔸[L] ↦ X • y := (Homeomorph.smul X).continuous.measurable
  have hsmK : Measurable fun v : Fin n → 𝔸[K] ↦ fun i ↦ x • v i :=
    Measurable.of_eval fun i ↦
      (Homeomorph.smul x).continuous.measurable.comp (measurable_pi_apply i)
  set c : ℝ≥0 := Real.toNNReal ((IdeleGroup.ideleModule K x : ℝ))⁻¹ with hcdef
  have h1 : ν.map (fun y ↦ X • y) = c ^ n • ν := by
    rw [hν, Measure.map_map hsmL hms, hcomp, ← Measure.map_map hms hsmK, hμ, map_smul_pi,
      Measure.map_smul]
    exact hms.aemeasurable
  have hc := isAddLeftInvariant_eq_smul ν (adeleMeasure L)
  set C := ν.addHaarScalarFactor (adeleMeasure L)
  have hC0 : (C : ℝ≥0∞) ≠ 0 := by
    intro h0
    have : ν = 0 := by rw [hc, ENNReal.coe_eq_zero.1 h0, zero_smul]
    exact (NeZero.ne ν) this
  obtain ⟨S, hS, hS0⟩ := exists_compact_mem_nhds (0 : 𝔸[L])
  have hpos : adeleMeasure L S ≠ 0 := (measure_pos_of_mem_nhds _ hS0).ne'
  have htop : adeleMeasure L S ≠ ⊤ := hS.measure_lt_top.ne
  rw [hc, Measure.map_smul, map_smul_adeleMeasure] at h1
  swap
  · exact hsmL.aemeasurable
  have h2 := congrArg (fun m : Measure 𝔸[L] ↦ m S) h1
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
  rw [mul_left_comm] at h2
  have hne : (C : ℝ≥0∞) * adeleMeasure L S ≠ 0 := mul_ne_zero hC0 hpos
  have hnt : (C : ℝ≥0∞) * adeleMeasure L S ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top htop
  have h3 := (ENNReal.mul_left_inj hne hnt).1 h2
  have hK0 : (0 : ℝ) ≤ (IdeleGroup.ideleModule K x : ℝ)⁻¹ :=
    inv_nonneg.2 (IdeleGroup.ideleModule K x).2.le
  have h4 : ((c ^ n : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (((IdeleGroup.ideleModule K x : ℝ))⁻¹ ^ n) := by
    rw [ENNReal.ofReal_pow hK0, ENNReal.coe_pow]
    rfl
  rw [h4] at h3
  have h5 := (ENNReal.ofReal_eq_ofReal_iff (inv_nonneg.2 (IdeleGroup.ideleModule L X).2.le)
    (pow_nonneg hK0 n)).1 h3
  rw [inv_pow] at h5
  exact inv_inj.1 h5

end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
  PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

theorem ideleModule_ideleEquiv_ofF : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ a : (AF F)ˣ,
    (IdeleGroup.ideleModule E (GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (ofF a)) : ℝ) = md a ^ 2 := by
  intro F E _ _ _ _ _ σ hcm a
  have he : GroundTheory.BlockD.ThmBHecke.ideleEquiv F E (ofF a) = ideleEmbedding F E a :=
    Units.ext (GroundTheory.BlockD.ThmBHecke.adeleEquiv_algebraMap (a : AF F))
  rw [he, ideleModule_ideleEmbedding, hcm.2.2.1]
  rfl

end

end GlobalTheory.CompanionTheory.SW.MdBase
end
end

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

theorem md_ray : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ), IsRay θ r →
    ∀ δ : ℝ, 0 < δ → md (r δ) = δ ^ Module.finrank ℚ F := by
  intro F _ _ hF θ r hr δ hδ
  obtain ⟨h1, h2⟩ := hr δ hδ
  have hw : ∀ w : InfinitePlace F, ‖(θ δ) w‖ = δ := by
    intro w
    have hreal : w.IsReal := hF.isReal w
    have hu := congrArg (fun f : ℝ →+* ℝ => f δ)
      (Subsingleton.elim ((InfinitePlace.Completion.extensionEmbeddingOfIsReal hreal).comp
        ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp θ)) (RingHom.id ℝ))
    have hu' : InfinitePlace.Completion.extensionEmbeddingOfIsReal hreal ((θ δ) w) = δ := hu
    have hn := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hreal).norm_map_of_map_zero
      (map_zero _) ((θ δ) w)
    rw [hu', Real.norm_eq_abs, abs_of_pos hδ] at hn
    exact hn.symm
  change (∏ w, ‖((r δ : AF F)).1 w‖ ^ w.mult) * (∏ᶠ v, ‖((r δ : AF F)).2 v‖) = δ ^ Module.finrank ℚ F
  rw [h1, h2]
  simp only [hw]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq]
  simp

end GlobalTheory.CompanionTheory.BasePsi

end
end

section

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

variable {F : Type} [Field F] [NumberField F]

theorem rv_zero_apply (v : HeightOneSpectrum (𝓞 F)) (s : Fv F v) :
    rv v 0 s = if s ≠ 0 ∧ s ∈ v.adicCompletionIntegers F then 1 else 0 := by
  unfold rv
  rw [tsum_eq_single 0]
  · have h : (s ∈ v.adicCompletionIntegers F) ↔ Valued.v s ≤ 1 :=
      HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F v
    simp [h]
  · intro i hi
    simp [hi]

theorem rv_zero_of_mem (v : HeightOneSpectrum (𝓞 F)) {s : Fv F v} (h0 : s ≠ 0)
    (hs : s ∈ v.adicCompletionIntegers F) : rv v 0 s = 1 := by
  rw [rv_zero_apply, if_pos ⟨h0, hs⟩]

theorem rv_zero_of_not_mem (v : HeightOneSpectrum (𝓞 F)) {s : Fv F v}
    (hs : s ∉ v.adicCompletionIntegers F) : rv v 0 s = 0 := by
  rw [rv_zero_apply, if_neg fun h => hs h.2]

theorem pure_rv_zero_apply (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ) :
    PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) a =
      if ∀ v, v ∉ S → (a : AF F).2 v ∈ v.adicCompletionIntegers F then
        ENNReal.ofReal (G (a : AF F).1 * ∏ v ∈ S, g v ((a : AF F).2 v)) else 0 := by
  have hne : ∀ v : HeightOneSpectrum (𝓞 F), (a : AF F).2 v ≠ 0 := fun v =>
    IdeleGroup.finite_ne_zero a v
  unfold PositivityTheory.Rg.Base1.pure
  split_ifs with h
  · rw [finprod_eq_one_of_forall_eq_one (fun v : {v // v ∉ S} => rv_zero_of_mem v.1 (hne v.1) (h v.1 v.2)),
      mul_one]
  · push_neg at h
    obtain ⟨v, hvS, hv⟩ := h
    have hfin : (Function.mulSupport fun v : {v // v ∉ S} => rv v.1 0 ((a : AF F).2 v.1)).Finite := by
      have hco : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
          (a : AF F).2 v ∈ v.adicCompletionIntegers F := (a : AF F).2.2
      refine Set.Finite.subset (Set.Finite.preimage Subtype.val_injective.injOn hco) ?_
      intro w hw
      by_contra hmem
      exact hw (rv_zero_of_mem w.1 (hne w.1) (not_not.1 hmem))
    rw [finprod_eq_zero _ (⟨v, hvS⟩ : {v // v ∉ S}) (rv_zero_of_not_mem v hv) hfin, mul_zero,
      ENNReal.ofReal_zero]

end GlobalTheory.CompanionTheory.BasePsi

end
end

section

open PositivityTheory.Rg.Base1

theorem _root_.GlobalTheory.T.existence_test_functions : TestEx := by
  first | exact @GlobalTheory.CompanionTheory.SW.BaseTest.testEx | exact GlobalTheory.CompanionTheory.SW.BaseTest.testEx | (intros; apply GlobalTheory.CompanionTheory.SW.BaseTest.testEx <;> assumption)
end

section

open PositivityTheory.Rg.Base1

theorem _root_.GlobalTheory.T.hermitian_existence_principle : HEx := by
  first | exact @GlobalTheory.CompanionTheory.RgBase.hEx | exact GlobalTheory.CompanionTheory.RgBase.hEx | (intros; apply GlobalTheory.CompanionTheory.RgBase.hEx <;> assumption)
end

section

open PositivityTheory.Rg.Base1

theorem _root_.GlobalTheory.T.similitude_of_scalar_formula : Scal → Simil := by
  first | exact @GlobalTheory.CompanionTheory.SW.BaseSimil.simil | exact GlobalTheory.CompanionTheory.SW.BaseSimil.simil | (intros; apply GlobalTheory.CompanionTheory.SW.BaseSimil.simil <;> assumption)
end

section

open PositivityTheory.Rg.Base1

theorem _root_.GlobalTheory.T.hasse_principle_hermitian : Hasse := by
  first | exact @GlobalTheory.CompanionTheory.SW.BaseHasse.hasse | exact GlobalTheory.CompanionTheory.SW.BaseHasse.hasse | (intros; apply GlobalTheory.CompanionTheory.SW.BaseHasse.hasse <;> assumption)
end

section

open PositivityTheory.Rg.Base1

theorem _root_.GlobalTheory.T.counting_formula_of_components : Tate → PsiSide → Ratio → HEx → TestEx → Dens → LSide → ThetaId → Cnt := by
  first | exact @GlobalTheory.CompanionTheory.RgBaseCnt.cnt_of | exact GlobalTheory.CompanionTheory.RgBaseCnt.cnt_of | (intros; apply GlobalTheory.CompanionTheory.RgBaseCnt.cnt_of <;> assumption)
end

section

open PositivityTheory.Rg.Base1

theorem _root_.GlobalTheory.T.local_density_ratio_formula : Ratio := by
  first | exact @GlobalTheory.CompanionTheory.RatioBase.ratio | exact GlobalTheory.CompanionTheory.RatioBase.ratio | (intros; apply GlobalTheory.CompanionTheory.RatioBase.ratio <;> assumption)
end

section

open PositivityTheory.Rg.Base1

theorem _root_.GlobalTheory.T.scalar_fibration_formula : Scal := by
  first | exact @GlobalTheory.CompanionTheory.RgBase.ScalFib.scal | exact GlobalTheory.CompanionTheory.RgBase.ScalFib.scal | (intros; apply GlobalTheory.CompanionTheory.RgBase.ScalFib.scal <;> assumption)
end
