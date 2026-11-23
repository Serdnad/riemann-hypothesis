module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaSeriesSummable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle006
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle018
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle032
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle052
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle003
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HarrisTaylorCardKilledByIdealEqAbsNormPow
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.HermitianCharacters.SelfDualLatticeFiltrationCharacter
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalDensityOfSelfDualLatticeLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.theta_series_summable : ∀ (F : Type) [Field F] [NumberField F], ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → ∀ (gf : Matrix ι ι (A F)) (gi : InfinitePlace F → Matrix ι ι ℝ), IsOrth B ρ gf gi → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → (∀ φ : (ι → A F) → ℂ, SB φ → Summable fun x => ‖thTerm B ρ P gf gi φ τ x‖) ∧ ∃ φ : (ι → A F) → ℂ, SB φ ∧ theta B ρ P gf gi φ τ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaSum.theta_summable_and_ne_zero | exact GlobalTheory.CompanionTheory.SW.ThetaSum.theta_summable_and_ne_zero | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaSum.theta_summable_and_ne_zero <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem _root_.GlobalTheory.T.lattice_coset_parametrization : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ)) (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (a : ι → F) (N : ℕ), 0 < N → ∃ e : (ι × InfinitePlace F → ℤ) → ι → F, Function.Injective e ∧ (∀ x : ι → F, toA x - toA a ∈ latN F ι N ↔ x ∈ Set.range e) ∧ ∀ n, emb ρ (e n) = emb ρ a + gM ρ (fun v => b v) N *ᵥ fun p => (n p : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.rational_coset_param | exact GlobalTheory.CompanionTheory.SW.ThW.rational_coset_param | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.rational_coset_param <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem _root_.GlobalTheory.T.schwartz_bruhat_span_indicators : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (ι : Type) [Fintype ι] [DecidableEq ι] (χ : (ι → A F) → (ι → A F) → ℂ) (μ : Measure (ι → A F)), NADual (ι → A F) χ μ → (∀ N : ℕ, 0 < N → IsOpen (latN F ι N : Set (ι → A F))) → ∀ φ : (ι → A F) → ℂ, SB φ → ∃ N : ℕ, 0 < N ∧ ∃ (s : Finset (ι → F)) (c : (ι → F) → ℂ), φ = ∑ a ∈ s, c a • indC N a := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.sb_eq_sum_rational_coset_indicators | exact GlobalTheory.CompanionTheory.SW.ThW.sb_eq_sum_rational_coset_indicators | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.sb_eq_sum_rational_coset_indicators <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem nnreal_eq_of_smul_haar {V : Type} [AddCommGroup V] [TopologicalSpace V] [LocallyCompactSpace V]
    [IsTopologicalAddGroup V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    {c e : ℝ≥0} (h : c • μ = e • μ) : c = e := by
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : V)
  have h1 : μ C ≠ ⊤ := hC.measure_lt_top.ne
  have h2 : μ C ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hC0).ne'
  have h3 : (c : ℝ≥0∞) * μ C = (e : ℝ≥0∞) * μ C := by
    have h' : (c • μ) C = (e • μ) C := by rw [h]
    rwa [Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, ENNReal.smul_def, smul_eq_mul,
      smul_eq_mul] at h'
  have h4 := (ENNReal.mul_left_inj h2 h1).1 h3
  exact_mod_cast h4

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def sclMat : R →* Matrix (Fin 1) (Fin 1) (R ⊗[F] E) where
  toFun u := Matrix.of fun _ _ => u ⊗ₜ[F] (1 : E)
  map_one' := by
    ext i j
    have hi : i = j := Subsingleton.elim _ _
    subst hi
    rw [Matrix.one_apply_eq]
    rfl
  map_mul' u v := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    simp only [Matrix.of_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem sclMat_apply (u : R) (i j : Fin 1) :
    sclMat (F := F) (E := E) R u i j = u ⊗ₜ[F] (1 : E) := rfl

def unitTens : Rˣ →* (R ⊗[F] E)ˣ :=
  Units.map (Algebra.TensorProduct.includeLeft : R →ₐ[F] R ⊗[F] E).toMonoidHom

theorem unitTens_coe (u : Rˣ) :
    ((unitTens (F := F) (E := E) R u : (R ⊗[F] E)ˣ) : R ⊗[F] E) = (u : R) ⊗ₜ[F] (1 : E) := rfl

theorem rmul_sclMat {M : ℕ} (X : Fin 1 → Fin M → R ⊗[F] E) (u : R) :
    rmul R X (sclMat (F := F) (E := E) R u) = scl (u ⊗ₜ[F] (1 : E)) X := by
  funext a i
  have ha : a = 0 := Subsingleton.elim _ _
  subst ha
  simp only [rmul, scl, Fin.sum_univ_one, sclMat_apply]

theorem cT_sclMat_mul (σ : E →ₐ[F] E) (u s : R) :
    ((hermScal R σ (u ^ 2 * s) : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) =
      cT (sigR R σ) (sclMat (F := F) (E := E) R u) *
        ((hermScal R σ s : HermR R σ 1) : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) *
        sclMat (F := F) (E := E) R u := by
  ext i j
  have h1 : sigR R σ (u ⊗ₜ[F] (1 : E)) = u ⊗ₜ[F] (1 : E) := by simp [sigR]
  rw [Matrix.mul_apply, Fin.sum_univ_one, Matrix.mul_apply, Fin.sum_univ_one]
  simp only [cT, Matrix.transpose_apply, Matrix.map_apply, sclMat_apply, h1]
  change (u ^ 2 * s) ⊗ₜ[F] (1 : E) = u ⊗ₜ[F] (1 : E) * s ⊗ₜ[F] (1 : E) * u ⊗ₜ[F] (1 : E)
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  congr 1
  ring

end Alg

theorem fibre_scale_modulus_length_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ) (J₁ : Matrix (Fin N) (Fin N) E), IsHermND σ J₁ → ∀ t : F, t ≠ 0 → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m₁ : HermR R σ 1 → Measure (Fin 1 → Fin N → R ⊗[F] E), IsGramFib R σ J₁ 1 (coordW R b lam 1 N) (coordHerm R σ b lam 1) m₁ → ∃ κ₁ cm : Rˣ → ℝ≥0, Continuous κ₁ ∧ κ₁ 1 = 1 ∧ (∀ u : Rˣ, m₁ (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) = κ₁ u • (m₁ (hermScal R σ (algebraMap F R t))).map (scl ((u : R) ⊗ₜ[F] (1 : E)))) ∧ Continuous cm ∧ (∀ u : Rˣ, (coordK R b lam).map (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) = cm u • coordK R b lam) ∧ ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → cm 1 = c := by
  intro F E _ _ _ _ _ σ hCM N J₁ hJ t ht R _ _ _ _ _ hR d b lam hlam m₁ hm₁
  have hR0 := hR
  obtain ⟨i1, i2, i3, i4, -⟩ := hR0
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  obtain ⟨k1, k2, k3, k4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI := k1
  haveI := k2
  haveI := k3
  haveI := k4
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hK, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  haveI := hK
  obtain ⟨κ, hκc, -, hκ1, hκ⟩ :=
    GlobalTheory.T.gram_fiber_measures_gl_equivariant F E σ hCM N J₁ hJ R hR 1 _ _ m₁ (hW 1 N) (hH 1) hm₁
  have hinc : Continuous (fun r : R => r ⊗ₜ[F] (1 : E)) := by
    haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
    have h : Continuous (fun r : R => r • (1 : R ⊗[F] E)) :=
      Continuous.smul (f := fun r : R => r) (g := fun _ => (1 : R ⊗[F] E)) continuous_id
        continuous_const
    refine h.congr fun r => ?_
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hcs : Continuous (sclMat (F := F) (E := E) R) :=
    continuous_pi fun _ => continuous_pi fun _ => hinc
  have hg : Continuous (Units.map (sclMat (F := F) (E := E) R)) := Continuous.units_map _ hcs
  have hu : Continuous (unitTens (F := F) (E := E) R) := Continuous.units_map _ hinc
  obtain ⟨χ, hχc, hχ⟩ := exists_continuous_modulus_of_continuous_action (R ⊗[F] E) (coordK R b lam)
    (R ⊗[F] E)ˣ
  let tU : (R ⊗[F] E)ˣ :=
    Units.map (inclR R : E →+* R ⊗[F] E).toMonoidHom
      (Units.mk0 (algebraMap F E t) ((map_ne_zero _).2 ht))
  have htU : (tU : R ⊗[F] E) = inclR R (algebraMap F E t) := rfl
  have hq : ∀ u : Rˣ, ((unitTens (F := F) (E := E) R u * tU : (R ⊗[F] E)ˣ) : R ⊗[F] E) =
      (u : R) ⊗ₜ[F] (algebraMap F E t) := by
    intro u
    rw [Units.val_mul, unitTens_coe, htU]
    change (u : R) ⊗ₜ[F] (1 : E) * (1 : R) ⊗ₜ[F] (algebraMap F E t) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  refine ⟨fun u => κ (Units.map (sclMat (F := F) (E := E) R) u),
    fun u => χ (unitTens (F := F) (E := E) R u * tU), hκc.comp hg, by simpa using hκ1, ?_,
    hχc.comp (hu.mul continuous_const), ?_, ?_⟩
  · intro u
    have h := hκ (Units.map (sclMat (F := F) (E := E) R) u) (hermScal R σ (algebraMap F R t))
      (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) (cT_sclMat_mul R σ (u : R) _)
    rw [h]
    congr 2
    funext X
    exact rmul_sclMat R X (u : R)
  · intro u
    have e : (fun y : R ⊗[F] E => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) =
        fun v => (unitTens (F := F) (E := E) R u * tU) • v := by
      funext y
      rw [Units.smul_def, smul_eq_mul, hq]
    rw [e]
    exact hχ _
  · intro c hc
    have e : (fun y : R ⊗[F] E => inclR R (algebraMap F E t) * y) = fun v => tU • v := by
      funext y
      rw [Units.smul_def, smul_eq_mul, htU]
    rw [e, hχ tU] at hc
    have := nnreal_eq_of_smul_haar (coordK R b lam) hc
    simpa using this

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.setLIntegral_Uset_coordW_eq_Mid : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∫⁻ v in (Uset σ J t B₀ a : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)), φ v ∂(coordW R b lam (n + 1) (M + 1)) = Mid σ J t m₁ m' s B₀ a κ₁ b lam φ := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.lintegral_Uset_eq_Mid | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.lintegral_Uset_eq_Mid | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.lintegral_Uset_eq_Mid <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.gram_fiber_cons_integrable_and_continuousOn_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → (∀ S ∈ (Bset R σ t a B₀ : Set (HermR R σ (n + 1))), Integrable φ (fibS σ J t m₁ m' s B₀ a κ₁ cm S)) ∧ ContinuousOn (fun S => ∫ v, φ v ∂(fibS σ J t m₁ m' s B₀ a κ₁ cm S)) (Bset R σ t a B₀ : Set (HermR R σ (n + 1))) := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibS_integrable_continuousOn | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibS_integrable_continuousOn | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.fibS_integrable_continuousOn <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.PiV

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

def ball (v : HeightOneSpectrum (𝓞 F)) (m : ℤ) : AddSubgroup (Fv F v) where
  carrier := {x | Valued.v x ≤ WithZero.exp m}
  add_mem' := by
    intro a b ha hb
    change Valued.v (a + b) ≤ _
    exact (Valuation.map_add _ a b).trans (max_le ha hb)
  zero_mem' := by
    change Valued.v (0 : Fv F v) ≤ _
    simp
  neg_mem' := by
    intro a ha
    change Valued.v (-a) ≤ _
    rw [Valuation.map_neg]
    exact ha

theorem mem_ball (m : ℤ) (x : Fv F v) : x ∈ ball v m ↔ Valued.v x ≤ WithZero.exp m := Iff.rfl

theorem ball_isCompact (m : ℤ) : IsCompact (ball v m : Set (Fv F v)) :=
  (GlobalTheory.LatticeDensity.ball_compact_open v m).1

theorem ball_isOpen (m : ℤ) : IsOpen (ball v m : Set (Fv F v)) :=
  (GlobalTheory.LatticeDensity.ball_compact_open v m).2

theorem ball_le {a b : ℤ} (hab : a ≤ b) : (ball v a : Set (Fv F v)) ⊆ ball v b :=
  fun _ hx => le_trans ((mem_ball _ _).1 hx) (WithZero.exp_le_exp.2 hab)

theorem exists_mem_ball (x : Fv F v) : ∃ m, x ∈ ball v m := by
  by_cases hx : Valued.v x = 0
  · exact ⟨0, by rw [mem_ball, hx]; exact zero_le'⟩
  · exact ⟨WithZero.log (Valued.v x), by rw [mem_ball, WithZero.exp_log hx]⟩

theorem exists_ball_of_isCompact (K : Set (Fv F v)) (hK : IsCompact K) :
    ∃ m, K ⊆ ball v m := by
  refine hK.elim_directed_cover (fun m : ℤ => (ball v m : Set (Fv F v))) ball_isOpen ?_
    (Monotone.directed_le fun a b hab => ball_le hab)
  intro x _
  obtain ⟨m, hm⟩ := exists_mem_ball x
  exact Set.mem_iUnion.2 ⟨m, hm⟩

theorem exists_ball_subset (U : Set (Fv F v)) (hU : U ∈ 𝓝 (0 : Fv F v)) :
    ∃ m, (ball v m : Set (Fv F v)) ⊆ U := by
  obtain ⟨W, hWU, hWo, h0⟩ := mem_nhds_iff.1 hU
  have hcl : ∀ m : ℤ, IsClosed (ball v m : Set (Fv F v)) := fun m => (ball_isCompact m).isClosed
  obtain ⟨n, hn⟩ := (ball_isCompact (v := v) 0).elim_directed_cover
    (fun n : ℕ => W ∪ (ball v (-(n : ℤ)) : Set (Fv F v))ᶜ)
    (fun n => hWo.union (hcl _).isOpen_compl)
    (by
      intro x _
      by_cases hx : x = 0
      · exact Set.mem_iUnion.2 ⟨0, Or.inl (hx ▸ h0)⟩
      · have hv : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
        refine Set.mem_iUnion.2 ⟨(WithZero.log (Valued.v x)).natAbs + 1, Or.inr fun hm => ?_⟩
        have h1 := WithZero.exp_le_exp.1 ((WithZero.exp_log hv).le.trans ((mem_ball _ _).1 hm))
        omega)
    (Monotone.directed_le fun a b hab x hx => hx.imp id fun h hm =>
      h (ball_le (by omega) hm))
  refine ⟨min (-(n : ℤ)) 0, fun x hx => hWU ?_⟩
  rcases hn (ball_le (min_le_right _ _) hx) with h | h
  · exact h
  · exact absurd (ball_le (min_le_left _ _) hx) h

theorem psiV_add (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    psiV F ψ v (x + y) = psiV F ψ v x * psiV F ψ v y := by
  classical
  have h : pairA F 0 (singleV F v (x + y)) =
      pairA F 0 (singleV F v x) + pairA F 0 (singleV F v y) := by
    have : singleV F v (x + y) = singleV F v x + singleV F v y :=
      RestrictedProduct.single_add _ v x y
    rw [this]
    exact Prod.ext (add_zero (0 : Ainf F)).symm rfl
  rw [psiV, h, AddChar.map_add_eq_mul]
  rfl

theorem ann_isCompact {χ : Fv F v → ℂ} (hc : Continuous χ) (h0 : χ 0 = 1) {y : Fv F v} (hy : χ y ≠ 1)
    (L : AddSubgroup (Fv F v)) (hLo : IsOpen (L : Set (Fv F v))) :
    IsCompact {t | ∀ s ∈ L, χ (s * t) = 1} := by
  obtain ⟨m, hm⟩ := exists_ball_subset (L : Set (Fv F v)) (hLo.mem_nhds L.zero_mem)
  have hy0 : y ≠ 0 := fun h => hy (h ▸ h0)
  have hv : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
  have hcl : IsClosed {t | ∀ s ∈ L, χ (s * t) = 1} := by
    simp only [Set.setOf_forall]
    exact isClosed_iInter fun s => isClosed_iInter fun _ =>
      isClosed_eq (hc.comp (continuous_const.mul continuous_id)) continuous_const
  refine (ball_isCompact (v := v) (WithZero.log (Valued.v y) - m)).of_isClosed_subset hcl ?_
  intro t ht
  by_contra hne
  have hlt : WithZero.exp (WithZero.log (Valued.v y) - m) < Valued.v t :=
    not_le.1 fun h => hne h
  have hvt : Valued.v t ≠ 0 := (lt_of_le_of_lt zero_le' hlt).ne'
  have ht0 : t ≠ 0 := (Valuation.ne_zero_iff _).1 hvt
  have hmem : y / t ∈ ball v m := by
    rw [mem_ball, map_div₀, div_le_iff₀ (zero_lt_iff.2 hvt)]
    calc Valued.v y = WithZero.exp m * WithZero.exp (WithZero.log (Valued.v y) - m) := by
          rw [← WithZero.exp_add, add_sub_cancel, WithZero.exp_log hv]
      _ ≤ WithZero.exp m * Valued.v t := mul_le_mul_right hlt.le _
  have := ht _ (hm hmem)
  rw [div_mul_cancel₀ _ ht0] at this
  exact hy this

theorem selfDual_pi_v : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (k : Measure (Fv F v)), SelfDual k (fun s t => psiV F ψ v (s * t)) → ∀ (ι : Type) [Fintype ι], SelfDual (Measure.pi fun _ : ι => k) (fun x y => psiV F ψ v (x ⬝ᵥ y)) := by
  intro F _ _ ψ hψ v k hk ι _
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨hc, y, hy⟩ := (GlobalTheory.CompanionTheory.AdeleCharLocal.char_nontrivial_at_every_place F ψ hψ).1 v
  have ha := psiV_add ψ v
  have hn : ∀ x, ‖psiV F ψ v x‖ = 1 := fun x => hψ.2.1 _
  refine GlobalTheory.CompanionTheory.SW.FourierPi.selfDual_pi (Fv F v) (psiV F ψ v) hc ha hn k hk
    ⟨ball v 0, ball_isCompact 0, ball_isOpen 0⟩
    (fun L _ hLo => ann_isCompact hc (GlobalTheory.CompanionTheory.SW.FourierPi.psi_zero ha hn) hy L hLo)
    (fun K hK => ?_) (fun U hU => ?_) ι
  · obtain ⟨m, hm⟩ := exists_ball_of_isCompact K hK
    exact ⟨ball v m, ball_isCompact m, ball_isOpen m, hm⟩
  · obtain ⟨m, hm⟩ := exists_ball_subset U hU
    exact ⟨ball v m, ball_isCompact m, ball_isOpen m, hm⟩

end GlobalTheory.CompanionTheory.SW.PiV
end
end
