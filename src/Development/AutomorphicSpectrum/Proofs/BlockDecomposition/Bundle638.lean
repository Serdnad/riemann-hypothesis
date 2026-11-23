module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle452
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle037
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle045
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle046
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle508
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle507
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle605
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle511
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle626
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle622
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle630
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle629
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
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.MeasurableLIntegral
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle002
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF



theorem fibSF_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ S : HermR R σ (n + 1), fibSF σ J t m₁ m' s B₀ a κ₁ cm S (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩ UsetF σ J t B₀)ᶜ = 0 := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D S
  by_cases hS : S ∈ BsetF R σ B₀
  swap
  · simp [fibSF, hS]
  obtain ⟨m₀, D₀⟩ := GlobalTheory.T.local_fibre_measure_extension_by_one F E σ M J t n R d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨h1, h2, h3, h4, -⟩ := id D.hR
  have hk := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  have hH := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R
  obtain ⟨-, -, hscH, -, hbH, hactH⟩ := hH
  obtain ⟨-, -, hscK, hT2K, -, -, -, hbor, -, hgram⟩ := hk
  obtain ⟨hcont, -, -, hpres⟩ := hactH (n + 1)
  have hcoord := (GlobalTheory.T.gram_block_one_schur_coordinates F E σ M J t n R d b lam m₁ m₀ s B₀ a κ₁ cm D₀).2
  have hker₁ := GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  obtain ⟨hsf', -, -, hfib'⟩ := GlobalTheory.T.local_fibre_measure_orthogonal_sum F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  obtain ⟨-, hlf₁, -⟩ := hker₁
  haveI := hbor (n + 1) (M + 1)
  haveI := hbor n M
  haveI := hbor 1 (M + 1)
  haveI := hlf₁ (hermScal R σ (algebraMap F R t))
  haveI := hsf' (schur R σ t a S)
  let α : R ⊗[F] E := ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E)
  let c := cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))
  let f : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) → (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
    fun p => actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec α c p.2)
  have hα : IsUnit α := by
    have hu : α * (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))))⁻¹ : Rˣ) : R) ⊗ₜ[F] (1 : E) = 1 := by
      simp [α, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.one_def]
    exact IsUnit.of_mul_eq_one _ hu
  have hfm : Measurable f := by
    have := hcont.measurable.comp
      ((D.hs.comp measurable_fst).prodMk ((measurable_vec α c).comp measurable_snd))
    exact this
  have hopen := GlobalTheory.T.linearly_independent_frames_open F E σ D.hCM R D.hR (n + 1) (M + 1)
  have hcl : MeasurableSet ((gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩
      {X : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X})ᶜ) :=
    ((isClosed_singleton.preimage (hgram (n + 1) (M + 1) (blockOne (algebraMap F E t) J))).measurableSet.inter
      hopen.measurableSet).compl
  have hae : ∀ᵐ p ∂((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))),
      gramR R σ (blockOne (algebraMap F E t) J) (f p) = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∧
        LinearIndependent (R ⊗[F] E) (f p) := by
    have h := (Measure.quasiMeasurePreserving_snd (μ := m₁ (hermScal R σ (algebraMap F R t)))
      (ν := m' (schur R σ t a S))).ae (hfib' (schur R σ t a S))
    filter_upwards [h] with p hp
    refine ⟨?_, ?_⟩
    · change gramR R σ (blockOne (algebraMap F E t) J)
        (actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec α c p.2)) = _
      rw [hpres]
      exact hcoord S p.2 hS hp.1
    · exact (GlobalTheory.T.linearIndependent_unitary_action_iff F E R σ (M + 1) (n + 1) _ (s p.1) (vec α c p.2)).2
        ((GlobalTheory.T.linearIndependent_extend_by_unit_vector (R ⊗[F] E) M n α hα c p.2).2 hp.2)
  have hsub : (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩
      UsetF σ J t B₀)ᶜ ⊆
      (gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩
      {X : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X})ᶜ := by
    intro x hx hxS
    exact hx ⟨hxS.1, ⟨⟨S, hS, (Set.mem_singleton_iff.1 hxS.1).symm⟩, hxS.2⟩⟩
  refine measure_mono_null hsub ?_
  have hmap : (((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map f)
      ((gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' {(S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))} ∩
      {X : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X})ᶜ) = 0 := by
    rw [Measure.map_apply hfm hcl]
    refine measure_mono_null ?_ (ae_iff.1 hae)
    intro p hp hpS
    exact hp hpS
  unfold fibSF
  rw [Set.indicator_of_mem hS, Measure.smul_apply]
  change _ • (((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map f) _ = 0
  rw [hmap, smul_zero]

end GlobalTheory.CompanionTheory.SW.StageF
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology ProbabilityTheory
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.StageF

theorem measurable_PintF (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ)
    (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
    (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
    (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0)
    (D : HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (hφ : Measurable φ) :
    Measurable (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n =>
      Pint σ J t m₁ m' s φ z.1 z.2.1 z.2.2) := by
  obtain ⟨iTR, iLR, iSR, iTR2, -⟩ := D.hR
  haveI := iTR
  haveI := iLR
  haveI := iSR
  haveI := iTR2
  obtain ⟨iTK, iLK, iSK, iT2K, -, -, -, iBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI := iTK
  haveI := iLK
  haveI := iSK
  haveI := iT2K
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨-, ⟨κ, hκs, hκm⟩, -, -⟩ :=
    GlobalTheory.T.local_fibre_measure_orthogonal_sum F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  obtain ⟨-, hloc₁, -⟩ :=
    GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  obtain ⟨-, -, iSH, -, iBH, hH⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R
  haveI := iSH
  haveI := iBH
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := iBor n M
  haveI : BorelSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := iBor (n + 1) (M + 1)
  haveI : BorelSpace (Fin 1 → Fin (M + 1) → R ⊗[F] E) := iBor 1 (M + 1)
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hact := (hH (n + 1)).1
  have hten : Measurable (fun r : R => r ⊗ₜ[F] (1 : E)) := by
    haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
    have hc : Continuous (fun r : R => r • (1 : R ⊗[F] E)) :=
      Continuous.smul (f := fun r : R => r) (g := fun _ : R => (1 : R ⊗[F] E))
        continuous_id continuous_const
    have he : (fun r : R => r ⊗ₜ[F] (1 : E)) = fun r : R => r • (1 : R ⊗[F] E) := by
      funext r
      simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
    rw [he]
    exact hc.measurable
  haveI : IsSFiniteKernel κ := hκs
  let κ' : Kernel ((R × (Fin n → R ⊗[F] E) × HermR R σ n) × (Fin 1 → Fin (M + 1) → R ⊗[F] E))
      (Fin n → Fin M → R ⊗[F] E) :=
    κ.comap (fun p => p.1.2.2) (measurable_snd.comp (measurable_snd.comp measurable_fst))
  haveI := hloc₁ (hermScal R σ (algebraMap F R t))
  have hvec : Measurable (fun q : ((R × (Fin n → R ⊗[F] E) × HermR R σ n) ×
      (Fin 1 → Fin (M + 1) → R ⊗[F] E)) × (Fin n → Fin M → R ⊗[F] E) =>
        (vec (q.1.1.1 ⊗ₜ[F] (1 : E)) q.1.1.2.1 q.2 : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) :=
    measurable_vec_triple.comp ((hten.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      (((measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_fst)))).prodMk
        measurable_snd))
  have hΦ : Measurable (fun q : ((R × (Fin n → R ⊗[F] E) × HermR R σ n) ×
      (Fin 1 → Fin (M + 1) → R ⊗[F] E)) × (Fin n → Fin M → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) (s q.1.2)
          (vec (q.1.1.1 ⊗ₜ[F] (1 : E)) q.1.1.2.1 q.2)) :=
    hact.measurable.comp ((D.hs.comp (measurable_snd.comp measurable_fst)).prodMk hvec)
  have hinner := Measurable.lintegral_kernel_prod_right' (κ := κ') (hφ.comp hΦ)
  have hfin := Measurable.lintegral_prod_right' (ν := m₁ (hermScal R σ (algebraMap F R t))) hinner
  have hm'κ : m' = fun S => κ S := funext fun S => (hκm S).symm
  rw [hm'κ]
  exact hfin

end GlobalTheory.CompanionTheory.SW.StageF
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal

namespace GlobalTheory.CompanionTheory.KFin

section SwapHerm

variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {c : R →+* R} {h : V → V → R}

theorem swapHerm_zero_right (hH : IsHerm c h) (x : V) : h x 0 = 0 := by
  have := hH.smul_right 0 x 0
  simpa using this

theorem swapHerm_add_left (hH : IsHerm c h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hH.symm z (x + y), hH.add_right, map_add (f := _), ← hH.symm z x, ← hH.symm z y]

theorem swapHerm_smul_left (hH : IsHerm c h) (a : R) (x y : V) : h (a • x) y = c a * h x y := by
  rw [hH.symm y (a • x), hH.smul_right, map_mul, ← hH.symm y x]

theorem swapHerm_sub_right (hH : IsHerm c h) (x y z : V) : h x (y - z) = h x y - h x z := by
  have := hH.add_right x (y - z) z
  rw [sub_add_cancel] at this
  exact eq_sub_of_add_eq this.symm

theorem swapHerm_part {e e' : R} (hce : c e = e') (hH : IsHerm c h) {a : V} (ha : e • a = a) (z : V) :
    h a z = e' * h a z := by
  calc h a z = h (e • a) z := by rw [ha]
    _ = e' * h a z := by rw [swapHerm_smul_left hH, hce]

theorem swapHerm_self {e e' : R} (hee : e * e' = 0) (hce : c e = e') (hH : IsHerm c h) {a : V}
    (ha : e • a = a) : h a a = 0 := by
  have h1 : h a a = e * h a a := by
    calc h a a = h a (e • a) := by rw [ha]
      _ = e * h a a := hH.smul_right e a a
  have h2 := swapHerm_part hce hH ha a
  rw [h1, h2, ← mul_assoc, hee, zero_mul]

theorem swapHerm_exists_ne (hP : IsPerfect h) {a : V} (ha : a ≠ 0) : ∃ y, h a y ≠ 0 := by
  by_contra hne
  push_neg at hne
  exact ha (hP.nondeg a hne)

theorem swapHerm_pair_ne {e e' : R} (hee : e * e' = 0) (hce : c e = e') (hce' : c e' = e)
    (hu : ∀ u, e * u ≠ 0 → e' * u ≠ 0 → IsUnit u) (hH : IsHerm c h) (hP : IsPerfect h)
    (hno : ∀ x y, h x x = 0 → h x y ≠ 1) {a b : V} (ha : e • a = a) (hb : e' • b = b)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) : h a b ≠ 0 := by
  intro hab
  have hee' : e' * e = 0 := by rw [mul_comm]; exact hee
  have haa : h a a = 0 := swapHerm_self hee hce hH ha
  have hbb : h b b = 0 := swapHerm_self hee' hce' hH hb
  have hba : h b a = 0 := by rw [hH.symm a b, hab, map_zero]
  have hxx : h (a + b) (a + b) = 0 := by
    rw [swapHerm_add_left hH, hH.add_right, hH.add_right, haa, hab, hba, hbb]; ring
  obtain ⟨y1, hy1⟩ := swapHerm_exists_ne hP ha0
  obtain ⟨y2, hy2⟩ := swapHerm_exists_ne hP hb0
  have hex : ∃ y, h a y ≠ 0 ∧ h b y ≠ 0 := by
    by_cases h1 : h b y1 = 0
    · by_cases h2 : h a y2 = 0
      · refine ⟨y1 + y2, ?_, ?_⟩
        · rw [hH.add_right, h2, add_zero]; exact hy1
        · rw [hH.add_right, h1, zero_add]; exact hy2
      · exact ⟨y2, h2, hy2⟩
    · exact ⟨y1, hy1, h1⟩
  obtain ⟨y, hya, hyb⟩ := hex
  have hpa : h a y = e' * h a y := swapHerm_part hce hH ha y
  have hpb : h b y = e * h b y := swapHerm_part hce' hH hb y
  have hunit : IsUnit (h (a + b) y) := by
    apply hu
    · rw [swapHerm_add_left hH, mul_add, hpa, ← mul_assoc, hee, zero_mul, zero_add, ← hpb]; exact hyb
    · rw [swapHerm_add_left hH, mul_add, hpb, ← mul_assoc, hee', zero_mul, add_zero, ← hpa]; exact hya
  obtain ⟨U, hU⟩ := hunit
  apply hno (a + b) ((↑U⁻¹ : R) • y) hxx
  rw [hH.smul_right, ← hU, Units.inv_mul]

theorem swapHerm_partner {e e' : R} (he : e + e' = 1) (hee : e * e' = 0) (hce : c e = e')
    (hH : IsHerm c h) (hP : IsPerfect h) {a : V} (ha : e • a = a) (ha0 : a ≠ 0) :
    ∃ b : V, e' • b = b ∧ b ≠ 0 := by
  obtain ⟨y, hy⟩ := swapHerm_exists_ne hP ha0
  have hidem : e' * e' = e' := by
    have h0 : e' * e = 0 := by rw [mul_comm]; exact hee
    calc e' * e' = e' * (e + e') - e' * e := by ring
      _ = e' := by rw [he, h0, mul_one, sub_zero]
  refine ⟨e' • y, by rw [← mul_smul, hidem], fun h0 => hy ?_⟩
  have h1 : h a (e' • y) = h a y := by rw [hH.smul_right, ← swapHerm_part hce hH ha y]
  rw [← h1, h0, swapHerm_zero_right hH]

theorem swapHerm_coord {e e' : R} (he : e + e' = 1) (hee : e * e' = 0) (hce : c e = e') (hce' : c e' = e)
    (hu : ∀ u, e * u ≠ 0 → e' * u ≠ 0 → IsUnit u) (hH : IsHerm c h) (hP : IsPerfect h)
    (hno : ∀ x y, h x x = 0 → h x y ≠ 1) {a b : V} (ha : e • a = a) (hb : e' • b = b)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) {z : V} (hz : e' • z = z) : ∃ ρ : R, z = ρ • b := by
  have hβ := swapHerm_pair_ne hee hce hce' hu hH hP hno ha hb ha0 hb0
  have hee' : e' * e = 0 := by rw [mul_comm]; exact hee
  have hidem : e * e = e := by
    calc e * e = e * (e + e') - e * e' := by ring
      _ = e := by rw [he, hee, mul_one, sub_zero]
  have he0 : e ≠ 0 := by
    intro h0; apply ha0; rw [← ha, h0, zero_smul]
  have hpβ : h a b = e' * h a b := swapHerm_part hce hH ha b
  have hpγ : h a z = e' * h a z := swapHerm_part hce hH ha z
  have hunit : IsUnit (e + h a b) := by
    apply hu
    · rw [mul_add, hidem, hpβ, ← mul_assoc, hee, zero_mul, add_zero]; exact he0
    · rw [mul_add, hee', zero_add, ← hpβ]; exact hβ
  obtain ⟨U, hU⟩ := hunit
  have hβU : h a b = e' * ↑U := by rw [hU, mul_add, hee', zero_add, ← hpβ]
  refine ⟨h a z * ↑U⁻¹, ?_⟩
  by_contra hne
  have hw : e' • (z - (h a z * ↑U⁻¹) • b) = z - (h a z * ↑U⁻¹) • b := by
    rw [smul_sub, hz, smul_comm, hb]
  have hw0 : z - (h a z * ↑U⁻¹) • b ≠ 0 := sub_ne_zero.mpr hne
  apply swapHerm_pair_ne hee hce hce' hu hH hP hno ha hw ha0 hw0
  rw [swapHerm_sub_right hH, hH.smul_right, hβU,
    show h a z * ↑U⁻¹ * (e' * ↑U) = h a z * e' * (↑U⁻¹ * ↑U) by ring, Units.inv_mul, mul_one,
    mul_comm, ← hpγ, sub_self]

theorem swapHerm_gen {e e' : R} (he : e + e' = 1) (hee : e * e' = 0) (hce : c e = e') (hce' : c e' = e)
    (hu : ∀ u, e * u ≠ 0 → e' * u ≠ 0 → IsUnit u) (hH : IsHerm c h) (hP : IsPerfect h)
    (hno : ∀ x y, h x x = 0 → h x y ≠ 1) {a b : V} (ha : e • a = a) (hb : e' • b = b)
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    (∀ x, ∃ r : R, x = r • (a + b)) ∧ IsUnit (h (a + b) (a + b)) := by
  have hee' : e' * e = 0 := by rw [mul_comm]; exact hee
  have he' : e' + e = 1 := by rw [add_comm]; exact he
  have hidem : e * e = e := by
    calc e * e = e * (e + e') - e * e' := by ring
      _ = e := by rw [he, hee, mul_one, sub_zero]
  have hidem' : e' * e' = e' := by
    calc e' * e' = e' * (e + e') - e' * e := by ring
      _ = e' := by rw [he, hee', mul_one, sub_zero]
  have he'a : e' • a = 0 := by rw [← ha, ← mul_smul, hee', zero_smul]
  have heb : e • b = 0 := by rw [← hb, ← mul_smul, hee, zero_smul]
  refine ⟨fun x => ?_, ?_⟩
  · obtain ⟨ρ', hρ'⟩ := swapHerm_coord he hee hce hce' hu hH hP hno ha hb ha0 hb0 (z := e' • x)
      (by rw [← mul_smul, hidem'])
    obtain ⟨ρ, hρ⟩ := swapHerm_coord he' hee' hce' hce (fun u h1 h2 => hu u h2 h1) hH hP hno hb ha hb0 ha0
      (z := e • x) (by rw [← mul_smul, hidem])
    refine ⟨ρ * e + ρ' * e', ?_⟩
    rw [smul_add, add_smul, add_smul, mul_smul, mul_smul, mul_smul, mul_smul, ha, hb, he'a, heb,
      smul_zero, smul_zero, add_zero, zero_add, ← hρ, ← hρ', ← add_smul, he, one_smul]
  · have hβ := swapHerm_pair_ne hee hce hce' hu hH hP hno ha hb ha0 hb0
    have haa : h a a = 0 := swapHerm_self hee hce hH ha
    have hbb : h b b = 0 := swapHerm_self hee' hce' hH hb
    have hpβ : h a b = e' * h a b := swapHerm_part hce hH ha b
    have hpβ' : h b a = e * h b a := swapHerm_part hce' hH hb a
    have hβ' : h b a ≠ 0 := by
      intro h0; apply hβ; rw [hH.symm b a, h0, map_zero]
    rw [swapHerm_add_left hH, hH.add_right, hH.add_right, haa, hbb, zero_add, add_zero]
    apply hu
    · rw [mul_add, hpβ, ← mul_assoc, hee, zero_mul, zero_add, ← hpβ']; exact hβ'
    · rw [mul_add, hpβ', ← mul_assoc, hee', zero_mul, add_zero, ← hpβ]; exact hβ

end SwapHerm

theorem hermitian_split_rank_one_struct {k R V : Type} [Field k] [CommRing R] [AddCommGroup V] [Module R V]
    (φ : R ≃+* k × k) (c : R →+* R) (hc : ∀ r, φ (c r) = (φ r).swap) (h : V → V → R)
    (hH : IsHerm c h) (hP : IsPerfect h) (hno : ∀ x y, h x x = 0 → h x y ≠ 1) :
    Subsingleton V ∨ ∃ w₀ : V, (∀ x, ∃ r : R, x = r • w₀) ∧ IsUnit (h w₀ w₀) := by
  obtain ⟨e, he_def⟩ : ∃ e : R, e = φ.symm (1, 0) := ⟨_, rfl⟩
  obtain ⟨e', he'_def⟩ : ∃ e' : R, e' = φ.symm (0, 1) := ⟨_, rfl⟩
  have hφe : φ e = (1, 0) := by rw [he_def]; simp
  have hφe' : φ e' = (0, 1) := by rw [he'_def]; simp
  have he : e + e' = 1 := φ.injective (by rw [map_add (f := _), hφe, hφe', map_one]; ext <;> simp)
  have hee : e * e' = 0 := φ.injective (by rw [map_mul, hφe, hφe', map_zero]; ext <;> simp)
  have hce : c e = e' := φ.injective (by rw [hc, hφe, hφe']; rfl)
  have hce' : c e' = e := φ.injective (by rw [hc, hφe, hφe']; rfl)
  have hu : ∀ u : R, e * u ≠ 0 → e' * u ≠ 0 → IsUnit u := by
    intro u h1 h2
    have h1' : (φ u).1 ≠ 0 := by
      intro h0; apply h1; apply φ.injective
      rw [map_mul, hφe, map_zero]; ext <;> simp [h0]
    have h2' : (φ u).2 ≠ 0 := by
      intro h0; apply h2; apply φ.injective
      rw [map_mul, hφe', map_zero]; ext <;> simp [h0]
    rw [← isUnit_map_iff φ, Prod.isUnit_iff]
    exact ⟨isUnit_iff_ne_zero.mpr h1', isUnit_iff_ne_zero.mpr h2'⟩
  have hee' : e' * e = 0 := by rw [mul_comm]; exact hee
  have he' : e' + e = 1 := by rw [add_comm]; exact he
  have hidem : e * e = e := by
    calc e * e = e * (e + e') - e * e' := by ring
      _ = e := by rw [he, hee, mul_one, sub_zero]
  have hidem' : e' * e' = e' := by
    calc e' * e' = e' * (e + e') - e' * e := by ring
      _ = e' := by rw [he, hee', mul_one, sub_zero]
  rcases subsingleton_or_nontrivial V with hs | hs
  · exact Or.inl hs
  right
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hv' : v = e • v + e' • v := by rw [← add_smul, he, one_smul]
  by_cases hev : e • v = 0
  · have hb0 : e' • v ≠ 0 := by intro h0; apply hv; rw [hv', hev, h0, add_zero]
    have hb : e' • (e' • v) = e' • v := by rw [← mul_smul, hidem']
    obtain ⟨a, ha, ha0⟩ := swapHerm_partner he' hee' hce' hH hP hb hb0
    exact ⟨_, swapHerm_gen he hee hce hce' hu hH hP hno ha hb ha0 hb0⟩
  · have ha : e • (e • v) = e • v := by rw [← mul_smul, hidem]
    obtain ⟨b, hb, hb0⟩ := swapHerm_partner he hee hce hH hP ha hev
    exact ⟨_, swapHerm_gen he hee hce hce' hu hH hP hno ha hb hev hb0⟩

theorem hermSwap_struct : ∀ {k R V : Type} [Field k] [CommRing R] [AddCommGroup V] [Module R V]
    (φ : R ≃+* k × k) (c : R →+* R), (∀ r, φ (c r) = (φ r).swap) → ∀ h : V → V → R, IsHerm c h →
    IsPerfect h → (∀ x y, h x x = 0 → h x y ≠ 1) →
    Subsingleton V ∨ ∃ w₀ : V, (∀ x, ∃ r : R, x = r • w₀) ∧ IsUnit (h w₀ w₀) := by
  intro k R V _ _ _ _ φ c hc h hH hP hno
  exact hermitian_split_rank_one_struct φ c hc h hH hP hno

end GlobalTheory.CompanionTheory.KFin
end

section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin

theorem leviMat_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (A A' : Type) [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A'] (φ : A →ₐ[F] A')
    (M : Matrix (Fin n) (Fin n) (A ⊗[F] E)) :
    leviMat σ J A' X Y (M.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) =
      (leviMat σ J A X Y M).map (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  let f : (A ⊗[F] E) →+* (A' ⊗[F] E) := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
  have hf : ∀ e : E, f (inclR (F := F) A e) = inclR (F := F) A' e := fun e => by
    simp [f, inclR]
  have hZ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E),
      (Z.map (inclR (F := F) A)).map f = Z.map (inclR (F := F) A') := fun Z => by
    ext i j
    simp [hf]
  have hmul : ∀ {a b c : ℕ} (P : Matrix (Fin a) (Fin b) (A ⊗[F] E)) (Q : Matrix (Fin b) (Fin c) (A ⊗[F] E)),
      (P * Q).map f = P.map f * Q.map f := fun P Q => Matrix.map_mul
  have hadd : ∀ P Q : Matrix (Fin n) (Fin n) (A ⊗[F] E), (P + Q).map f = P.map f + Q.map f :=
    fun P Q => Matrix.map_add f (map_add f) P Q
  have hsub : ∀ P Q : Matrix (Fin n) (Fin n) (A ⊗[F] E), (P - Q).map f = P.map f - Q.map f :=
    fun P Q => Matrix.map_sub f (map_sub f) P Q
  have hone : (1 : Matrix (Fin n) (Fin n) (A ⊗[F] E)).map f = 1 :=
    Matrix.map_one f (map_zero f) (map_one f)
  have hdiag : ∀ d : Fin r → A ⊗[F] E, (diagonal d).map f = diagonal (fun i => f (d i)) := fun d => by
    ext i j
    by_cases h : i = j <;> simp [diagonal, h]
  change leviMat σ J A' X Y (M.map f) = (leviMat σ J A X Y M).map f
  have hentry : ∀ (P : Matrix (Fin r) (Fin r) (A ⊗[F] E)) (i : Fin r), f (P i i) = (P.map f) i i :=
    fun _ _ => rfl
  simp only [leviMat, hadd, hsub, hmul, hone, hdiag, hentry, hZ]

end GlobalTheory.CompanionTheory.KFin
end

section


theorem _root_.GlobalTheory.T.local_good_reduction : PositivityTheory.Rg.BcB.G8.Fin.LocGood := by
  first | exact @GlobalTheory.CompanionTheory.LocGoodProof.locGood | exact GlobalTheory.CompanionTheory.LocGoodProof.locGood | (intros; apply GlobalTheory.CompanionTheory.LocGoodProof.locGood <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU NumberField MeasureTheory
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_selfdual_measure_hermitian_tuples : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ n : ℕ, ∃ μ : Measure (Fin n → Fin M → AF F ⊗[F] E), SdW F E σ M J (AF F) ψ n μ := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN.exists_sdW_tuples | exact GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN.exists_sdW_tuples | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.SdExistN.exists_sdW_tuples <;> assumption)
end
