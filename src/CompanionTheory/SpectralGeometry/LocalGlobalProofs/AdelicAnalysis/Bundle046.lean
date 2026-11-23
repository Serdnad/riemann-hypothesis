module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle018
public import Mathlib.Probability.Kernel.Defs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle024
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import GroundTheory.LocalFields.LocalFourier
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Aesop.Main
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
public import Mathlib.MeasureTheory.Function.Floor
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Kernel.Composition.MapComap
public import Mathlib.Probability.Kernel.MeasurableLIntegral
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
public import Mathlib.Probability.Kernel.Basic

@[expose] public section

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem lintegral_fibS_of_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), ∫⁻ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S) = (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) * (cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) ^ n * Pint σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ S hS
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := D.hR
  have := hTR
  have := hLC
  have := hSC
  have := hT2
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨hKR, hKLC, hKSC, hKT2, -, -, -, hKB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  have := hKR
  have := hKLC
  have := hKSC
  have := hKT2
  obtain ⟨-, -, hHSC, -, hHB, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R
  have := hHSC
  have := hHB
  have := hKB (n + 1) (M + 1)
  have k₁ := (GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁).2.1
  have k' := (GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm').2.1
  have hact' := (hact (n + 1)).1
  have := k₁ (hermScal R σ (algebraMap F R t))
  have := k' (schur R σ t a S)
  have hvec : ∀ (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E),
      Measurable (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X) := by
    intro A c
    refine Measurable.of_eval (fun i => ?_)
    induction i using Fin.cases with
    | zero =>
      have h0 : (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X 0) =
          fun _ => Fin.cons A (fun _ => 0) := rfl
      rw [h0]
      exact measurable_const
    | succ j =>
      refine Measurable.of_eval (fun k => ?_)
      induction k using Fin.cases with
      | zero =>
        have h0 : (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X j.succ 0) = fun _ => c j := rfl
        rw [h0]
        exact measurable_const
      | succ l =>
        have h0 : (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X j.succ l.succ) =
            fun X => X j l := rfl
        rw [h0]
        exact (measurable_pi_apply l).comp (measurable_pi_apply j)
  have hf : ∀ (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E), Measurable (fun p :
      (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec A c p.2)) := fun A c =>
    hact'.measurable.comp ((D.hs.comp measurable_fst).prodMk ((hvec A c).comp measurable_snd))
  have hg : ∀ (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E), Measurable (fun p :
      (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        φ (actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec A c p.2))) := fun A c =>
    hφ.comp (hf A c)
  have hfib := Set.indicator_of_mem hS (fun S : HermR R σ (n + 1) =>
    (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) *
        cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n) •
      ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map (fun p =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1)
          (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
            (cvec R t a S) p.2)))
  have hfib' : fibS σ J t m₁ m' s B₀ a κ₁ cm S = _ := hfib
  rw [hfib', lintegral_smul_measure, lintegral_map hφ (hf _ _),
    lintegral_prod _ (hg _ _).aemeasurable, ENNReal.smul_def, smul_eq_mul]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology ProbabilityTheory
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem isSFiniteKernel_of_forall_univ_lt_top {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (η : Kernel α β) (h : ∀ a, η a Set.univ < ⊤) : IsSFiniteKernel η := by
  classical
  have hmeas : Measurable fun a => η a Set.univ := η.measurable_coe MeasurableSet.univ
  let g : α → ℕ := fun a => ⌊(η a Set.univ).toReal⌋₊
  have hg : Measurable g := Nat.measurable_floor.comp hmeas.ennreal_toReal
  have hB : ∀ j : ℕ, MeasurableSet (g ⁻¹' {j}) := fun j => hg (measurableSet_singleton j)
  let ηs : ℕ → Kernel α β := fun j => Kernel.piecewise (hB j) η 0
  have hfin : ∀ j, IsFiniteKernel (ηs j) := by
    intro j
    refine ⟨⟨(j : ℝ≥0∞) + 1, by simp [ENNReal.add_lt_top], fun a => ?_⟩⟩
    by_cases ha : a ∈ g ⁻¹' {j}
    · have hj : g a = j := ha
      have h1 : (η a Set.univ).toReal < (j : ℝ) + 1 := by
        have := Nat.lt_floor_add_one (η a Set.univ).toReal
        simpa [g, hj] using this
      have h2 : η a Set.univ = ENNReal.ofReal (η a Set.univ).toReal :=
        (ENNReal.ofReal_toReal (h a).ne).symm
      simp only [ηs, Kernel.piecewise_apply, if_pos ha]
      rw [h2]
      refine ENNReal.ofReal_le_of_le_toReal ?_
      rw [ENNReal.toReal_add (by simp) (by simp)]
      simpa using h1.le
    · have ha' : ¬ g a = j := ha
      simp [ηs, Kernel.piecewise_apply, ha']
  have hsum : η = Kernel.sum ηs := by
    ext a s hs
    rw [Kernel.sum_apply, Measure.sum_apply _ hs, tsum_eq_single (g a)]
    · simp [ηs, Kernel.piecewise_apply]
    · intro j hj
      have ha' : ¬ g a = j := fun h' => hj h'.symm
      simp [ηs, Kernel.piecewise_apply, ha']
  rw [hsum]
  exact ⟨⟨fun j => ηs j, hfin, rfl⟩⟩

theorem isSFiniteKernel_of_locallyFinite {α β : Type} [MeasurableSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [BorelSpace β] [T2Space β] [SigmaCompactSpace β]
    (κ : Kernel α β) (h : ∀ a, IsLocallyFiniteMeasure (κ a)) : IsSFiniteKernel κ := by
  let C : ℕ → Set β := disjointed (compactCovering β)
  have hCm : ∀ k, MeasurableSet (C k) := fun k =>
    MeasurableSet.disjointed (fun i => (isCompact_compactCovering β i).measurableSet) k
  have hCd : Pairwise (Function.onFun Disjoint C) := disjoint_disjointed _
  have hCu : ⋃ k, C k = Set.univ := by
    simp only [C, iUnion_disjointed]
    exact iUnion_compactCovering β
  have hCf : ∀ a k, κ a (C k) < ⊤ := fun a k => by
    haveI := h a
    exact (measure_mono (disjointed_subset _ k)).trans_lt
      (isCompact_compactCovering β k).measure_lt_top
  have hk : ∀ k, IsSFiniteKernel (Kernel.restrict κ (hCm k)) := fun k =>
    isSFiniteKernel_of_forall_univ_lt_top _ (fun a => by
      rw [Kernel.restrict_apply]
      simpa using hCf a k)
  have hsum : κ = Kernel.sum fun k => Kernel.restrict κ (hCm k) := by
    ext a s hs
    rw [Kernel.sum_apply]
    simp only [Kernel.restrict_apply]
    rw [← Measure.restrict_iUnion hCd hCm, hCu, Measure.restrict_univ]
  rw [hsum]
  infer_instance

theorem measurable_vec_triple {K : Type} [Zero K] [MeasurableSpace K] {M n : ℕ} :
    Measurable (fun p : K × (Fin n → K) × (Fin n → Fin M → K) =>
      (vec p.1 p.2.1 p.2.2 : Fin (n + 1) → Fin (M + 1) → K)) := by
  refine Measurable.of_eval fun a => Measurable.of_eval fun i => ?_
  induction a using Fin.cases with
  | zero =>
    induction i using Fin.cases with
    | zero => simpa [vec] using measurable_fst
    | succ i => simpa [vec] using measurable_const
  | succ j =>
    induction i using Fin.cases with
    | zero =>
      simp only [vec, Fin.cons_succ, Fin.cons_zero]
      exact (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
    | succ i =>
      simp only [vec, Fin.cons_succ]
      exact (measurable_pi_apply i).comp
        ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))

theorem measurable_Pint (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ)
    (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
    (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
    (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0)
    (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm)
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
  obtain ⟨-, hloc, -, hmeas, -, -⟩ :=
    GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
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
  let κ : Kernel (HermR R σ n) (Fin n → Fin M → R ⊗[F] E) :=
    ⟨m', Measure.measurable_of_measurable_coe _ hmeas⟩
  haveI : IsSFiniteKernel κ := isSFiniteKernel_of_locallyFinite κ hloc
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
  exact Measurable.lintegral_prod_right' (ν := m₁ (hermScal R σ (algebraMap F R t))) hinner

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.LocInv

open GroundTheory.LocalField ValuativeRel MeasureTheory Topology Filter
open scoped NNReal ENNReal

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

theorem measureReal_dual_mul (ψ : AddChar K Circle) (k : ℤ) :
    (selfDualMeasure ψ).real (valBall K (addCharConductor ψ - k)) *
      (selfDualMeasure ψ).real (valBall K k) = 1 := by
  rw [measureReal_valBall _ (addCharConductor ψ - k), measureReal_valBall _ k,
    selfDualMeasure_real_valBall_zero]
  have hq : (0 : ℝ) < residueCard K := by
    exact_mod_cast zero_lt_one.trans one_lt_residueCard
  have h := (inversion_const_eq_one_iff (K := K) (addCharConductor ψ)
    (Real.rpow_nonneg hq.le ((addCharConductor ψ : ℝ) / 2))).mpr rfl
  have e : (residueCard K : ℝ) ^ (-(addCharConductor ψ - k)) * (residueCard K : ℝ) ^ (-k) =
      (residueCard K : ℝ) ^ (-addCharConductor ψ) := by
    rw [← zpow_add₀ hq.ne']
    congr 1
    ring
  rw [← h, ← e]
  ring

theorem tendsto_mean (ψ : AddChar K Circle) {Φ : K → ℂ} (hΦ : Continuous Φ) (z : K) :
    Tendsto (fun k : ℕ =>
      (((selfDualMeasure ψ).real (valBall K (addCharConductor ψ - (k : ℤ))) : ℝ) : ℂ) *
        ∫ x in valBall K (k : ℤ), Φ (x - z) ∂(selfDualMeasure ψ)) atTop (𝓝 (Φ (-z))) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hcont : ContinuousAt (fun h : K => Φ (h - z)) 0 :=
    (hΦ.comp (continuous_id.sub continuous_const)).continuousAt
  have hnh : {h : K | dist (Φ (h - z)) (Φ (-z)) < ε / 2} ∈ 𝓝 (0 : K) := by
    have := hcont.preimage_mem_nhds (Metric.ball_mem_nhds (Φ (0 - z)) (half_pos hε))
    simpa [Metric.ball, zero_sub] using this
  obtain ⟨m, -, hm⟩ := hasBasis_nhds_zero_valBall.mem_iff.mp hnh
  refine ⟨m.toNat, fun k hk => ?_⟩
  have hkm : m ≤ (k : ℤ) := by omega
  have hsub : (valBall K (k : ℤ) : Set K) ⊆ valBall K m := valBall_antitone hkm
  have hmul := measureReal_dual_mul ψ (k : ℤ)
  set c : ℝ := (selfDualMeasure ψ).real (valBall K (addCharConductor ψ - (k : ℤ))) with hcdef
  set v : ℝ := (selfDualMeasure ψ).real (valBall K (k : ℤ)) with hvdef
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hfin : (selfDualMeasure ψ) (valBall K (k : ℤ) : Set K) < ∞ :=
    (isCompact_valBall _).measure_lt_top
  have hint : IntegrableOn (fun x => Φ (x - z)) (valBall K (k : ℤ)) (selfDualMeasure ψ) :=
    (hΦ.comp (continuous_id.sub continuous_const)).continuousOn.integrableOn_compact
      (isCompact_valBall _)
  have hintc : IntegrableOn (fun _ : K => Φ (-z)) (valBall K (k : ℤ)) (selfDualMeasure ψ) :=
    integrableOn_const hfin.ne
  have hdiff : (c : ℂ) * (∫ x in valBall K (k : ℤ), Φ (x - z) ∂(selfDualMeasure ψ)) - Φ (-z) =
      (c : ℂ) * ∫ x in valBall K (k : ℤ), (Φ (x - z) - Φ (-z)) ∂(selfDualMeasure ψ) := by
    rw [integral_sub hint hintc, setIntegral_const, Complex.real_smul, mul_sub, ← mul_assoc,
      ← hvdef]
    have : (c : ℂ) * (v : ℂ) = 1 := by exact_mod_cast hmul
    rw [this, one_mul]
  have hbound : ‖∫ x in valBall K (k : ℤ), (Φ (x - z) - Φ (-z)) ∂(selfDualMeasure ψ)‖ ≤
      ε / 2 * v := by
    refine norm_setIntegral_le_of_norm_le_const hfin fun x hx => ?_
    have := hm (hsub hx)
    rw [Set.mem_setOf_eq, dist_eq_norm] at this
    exact this.le
  rw [dist_eq_norm, hdiff, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0]
  calc c * ‖∫ x in valBall K (k : ℤ), (Φ (x - z) - Φ (-z)) ∂(selfDualMeasure ψ)‖
      ≤ c * (ε / 2 * v) := mul_le_mul_of_nonneg_left hbound hc0
    _ = ε / 2 := by
        rw [show c * (ε / 2 * v) = ε / 2 * (c * v) by ring, hmul, mul_one]
    _ < ε := half_lt_self hε

theorem setIntegral_fourier_mul_char {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {Φ : K → ℂ} (hΦ : Continuous Φ) (hc : HasCompactSupport Φ) (z : K) (k : ℤ) :
    ∫ y in valBall K (addCharConductor ψ - k),
        (∫ x, Φ x * (ψ (x * y) : ℂ) ∂(selfDualMeasure ψ)) * (ψ (y * z) : ℂ) ∂(selfDualMeasure ψ) =
      (((selfDualMeasure ψ).real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) *
        ∫ x in valBall K k, Φ (x - z) ∂(selfDualMeasure ψ) := by
  set μ := selfDualMeasure ψ with hμ
  have hfi : Integrable Φ μ := hΦ.integrable_of_hasCompactSupport hc
  have hψc : Continuous fun x => (ψ x : ℂ) := continuous_subtype_val.comp hψ
  have : IsFiniteMeasure (μ.restrict (valBall K (addCharConductor ψ - k))) :=
    isFiniteMeasure_restrict.mpr (isCompact_valBall _).measure_lt_top.ne
  let G : K → K → ℂ := fun y x => Φ x * (ψ (x * y) : ℂ) * (ψ (y * z) : ℂ)
  have hG : Integrable (Function.uncurry G)
      ((μ.restrict (valBall K (addCharConductor ψ - k))).prod μ) := by
    have hdom : Integrable (fun p : K × K => (1 : ℝ) * ‖Φ p.2‖)
        ((μ.restrict (valBall K (addCharConductor ψ - k))).prod μ) :=
      (integrable_const (1 : ℝ)).mul_prod hfi.norm
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      exact ((hΦ.comp continuous_snd).mul
        (hψc.comp (continuous_snd.mul continuous_fst))).mul
        (hψc.comp (continuous_fst.mul continuous_const))
    · simp [G, Function.uncurry, Circle.norm_coe]
  have hB : ∫ y in valBall K (addCharConductor ψ - k),
        (∫ x, Φ x * (ψ (x * y) : ℂ) ∂μ) * (ψ (y * z) : ℂ) ∂μ =
      ∫ y in valBall K (addCharConductor ψ - k), ∫ x, G y x ∂μ ∂μ := by
    congr 1
    ext y
    exact (integral_mul_const _ _).symm
  have hinner : ∀ x, ∫ y in valBall K (addCharConductor ψ - k), G y x ∂μ =
      (valBall K k : Set K).indicator
        (fun w => ((μ.real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) * Φ (w - z)) (x + z) := by
    intro x
    have e : ∀ y, G y x = Φ x * ((ψ.mulShift (x + z)) y : ℂ) := fun y => by
      simp only [G, AddChar.mulShift_apply]
      rw [mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 3
      ring
    simp only [e]
    rw [integral_const_mul, integral_valBall_char]
    by_cases hxz : x + z ∈ valBall K k
    · have ht : IsTrivialOn (ψ.mulShift (x + z)) (addCharConductor ψ - k) := by
        rw [isTrivialOn_mulShift_iff_mem hψ hψ1]
        simpa using hxz
      rw [if_pos ht, Set.indicator_of_mem (show x + z ∈ (valBall K k : Set K) from hxz),
        add_sub_cancel_right, mul_comm]
    · have ht : ¬ IsTrivialOn (ψ.mulShift (x + z)) (addCharConductor ψ - k) := by
        rw [isTrivialOn_mulShift_iff_mem hψ hψ1]
        simpa using hxz
      rw [if_neg ht, Set.indicator_of_notMem (show x + z ∉ (valBall K k : Set K) from hxz),
        mul_zero]
  rw [hB, integral_integral_swap hG]
  simp only [hinner]
  have hpre : ∫ x, (valBall K k : Set K).indicator
        (fun w => ((μ.real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) * Φ (w - z)) (x + z) ∂μ =
      ∫ x, (valBall K k : Set K).indicator
        (fun w => ((μ.real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) * Φ (w - z)) x ∂μ :=
    integral_add_right_eq_self (fun x => (valBall K k : Set K).indicator
      (fun w => ((μ.real (valBall K (addCharConductor ψ - k)) : ℝ) : ℂ) * Φ (w - z)) x) z
  rw [hpre, integral_indicator (measurableSet_valBall k), integral_const_mul]

theorem iUnion_valBall_sub (n : ℤ) : ⋃ k : ℕ, (valBall K (n - (k : ℤ)) : Set K) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  obtain ⟨m, hm⟩ := exists_mem_valBall_neg_nat x
  refine Set.mem_iUnion.mpr ⟨(n + m).toNat, ?_⟩
  exact valBall_antitone (by omega) hm

theorem inversion {ψ : AddChar K Circle} (hψ : Continuous ψ) (hψ1 : ψ ≠ 1)
    {Φ : K → ℂ} (hΦ : Continuous Φ) (hc : HasCompactSupport Φ)
    (hI : Integrable (fun y => ∫ x, Φ x * (ψ (x * y) : ℂ) ∂(selfDualMeasure ψ))
      (selfDualMeasure ψ)) (z : K) :
    ∫ y, (∫ x, Φ x * (ψ (x * y) : ℂ) ∂(selfDualMeasure ψ)) * (ψ (y * z) : ℂ)
      ∂(selfDualMeasure ψ) = Φ (-z) := by
  have hψc : Continuous fun x => (ψ x : ℂ) := continuous_subtype_val.comp hψ
  have hF : Integrable (fun y => (∫ x, Φ x * (ψ (x * y) : ℂ) ∂(selfDualMeasure ψ)) *
      (ψ (y * z) : ℂ)) (selfDualMeasure ψ) := by
    refine hI.norm.mono' (hI.aestronglyMeasurable.mul
      (hψc.comp (continuous_id.mul continuous_const)).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    simp [Circle.norm_coe]
  have hmono : Monotone fun k : ℕ => (valBall K (addCharConductor ψ - (k : ℤ)) : Set K) :=
    fun a b hab => valBall_antitone (by omega)
  have hlim := tendsto_setIntegral_of_monotone (μ := selfDualMeasure ψ)
    (fun k : ℕ => measurableSet_valBall (K := K) (addCharConductor ψ - (k : ℤ))) hmono
    hF.integrableOn
  rw [iUnion_valBall_sub, setIntegral_univ] at hlim
  refine tendsto_nhds_unique hlim ?_
  refine (tendsto_mean ψ hΦ z).congr fun k => ?_
  exact (setIntegral_fourier_mul_char hψ hψ1 hΦ hc z (k : ℤ)).symm

end GlobalTheory.CompanionTheory.SW.LocInv

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem GlobalTheory.CompanionTheory.SW.selfDual_selfDualMeasure : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K] (ψ : AddChar K Circle), Continuous ψ → ψ ≠ 1 → SelfDual (GroundTheory.LocalField.selfDualMeasure ψ) (fun s t => ((ψ (s * t) : Circle) : ℂ)) := by
  intro K _ _ _ _ _ _ ψ hψ hψ1
  exact ⟨inferInstance, fun Φ hΦ hc hI z => GlobalTheory.CompanionTheory.SW.LocInv.inversion hψ hψ1 hΦ hc hI z⟩
end
end
