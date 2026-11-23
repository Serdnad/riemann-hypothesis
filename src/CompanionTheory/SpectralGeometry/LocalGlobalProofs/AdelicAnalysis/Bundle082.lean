module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle030
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle043
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle041
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsTraceFormGramMatrixInBasis
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle081
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolume
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle016
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle007
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

theorem _root_.GlobalTheory.T.theta_function_cusp_expansion : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ φ : (ι → A F) → ℂ, SB φ → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → (∀ b : F, eis ψ lf B ρ P (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) = eis ψ lf B ρ P φ τ) ∧ (∀ a : F, a ≠ 0 → eis ψ lf B ρ P (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = eis ψ lf B ρ P φ τ) ∧ (cG B ρ P τ * eis ψ lf B ρ P (fou (chiB ψ (Bf B)) (muF B lf) φ) (fun w => -(τ w)⁻¹) = eis ψ lf B ρ P φ τ) ∧ ∀ c : ℂ, eis ψ lf B ρ P (c • φ) τ = c * eis ψ lf B ρ P φ τ := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.EiInv.ei_inv | exact GlobalTheory.CompanionTheory.SW.Core.EiInv.ei_inv | (intros; apply GlobalTheory.CompanionTheory.SW.Core.EiInv.ei_inv <;> assumption)
end

section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.CntLarge

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def orbitHom (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA (AF F) σ J) :
    (Fin 1 → Fin M → E) →+ (Fin 1 → Fin M → AF F ⊗[F] E) where
  toFun X := actW (AF F) σ J h (ratTup (AF F) X)
  map_zero' := by
    funext a i
    simp [actW, actTup, ratTup, inclR, Matrix.mulVec, dotProduct]
  map_add' X Y := by
    funext a i
    simp [actW, actTup, ratTup, inclR, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib,
      TensorProduct.tmul_add]

theorem count_le (hpack : ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ) (Λ : Type) [AddCommGroup Λ]
      (e : Λ →+ (Fin 1 → Fin M → AF F ⊗[F] E)) (N : ℕ) (r R : ℝ), 0 < r → r ≤ R →
      ∑' l : Λ, (Set.indicator (box b N R) (fun _ => (1 : ℝ≥0∞))) (e l) ≤
        ENNReal.ofReal ((5 * R / r) ^ (2 * Module.finrank ℚ F * M)) *
          ∑' l : Λ, (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e l))
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA (AF F) σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (N : ℕ) {r₀ r : ℝ} (h0 : 0 < r₀) (hr : r₀ ≤ r) :
    ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
        (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞)))
          (actW (AF F) σ J h (ratTup (AF F) (X : Fin 1 → Fin M → E))) ≤
      ENNReal.ofReal ((5 * r / r₀) ^ (2 * Module.finrank ℚ F * M)) *
        (1 + ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
          (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞)))
            (actW (AF F) σ J h (ratTup (AF F) (X : Fin 1 → Fin M → E)))) := by
  classical
  set e := orbitHom σ J h with he
  have key := hpack d b M (Fin 1 → Fin M → E) e N r₀ r h0 hr
  have hsplit : ∑' X : Fin 1 → Fin M → E, (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) (e X) ≤
      1 + ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
        (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) (e X) := by
    rw [ENNReal.tsum_eq_add_tsum_ite (0 : Fin 1 → Fin M → E)]
    refine add_le_add (by rw [Set.indicator_apply]; split_ifs <;> simp) ?_
    rw [tsum_subtype {X : Fin 1 → Fin M → E | X ≠ 0}
      (fun X => (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) (e X))]
    refine le_of_eq (tsum_congr fun X => ?_)
    by_cases hX : X = 0 <;> simp [hX]
  have hle : ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
      (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e X) ≤
      ∑' X : Fin 1 → Fin M → E, (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e X) := by
    rw [tsum_subtype {X : Fin 1 → Fin M → E | X ≠ 0}
      (fun X => (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e X))]
    exact ENNReal.tsum_le_tsum fun X => Set.indicator_le_self _ _ _
  exact hle.trans (key.trans (mul_le_mul_right hsplit _))

theorem cnt_large : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (N : ℕ) (r₀ : ℝ), 0 < N → 0 < r₀ → ∃ C : ℝ, ∀ r : ℝ, r₀ ≤ r → cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) ≤ ENNReal.ofReal (C * r ^ (2 * Module.finrank ℚ F * M)) := by
  intro F E _ _ _ _ _ σ hσ M J hJ hM μ 𝓕 hμ h𝓕 d b N r₀ hN h0
  have hvol : μ 𝓕 < ⊤ := ((finVol_unitaryGroup F E σ hσ M J hJ).2 μ hμ).2 𝓕 h𝓕
  have hcomp : IsCompact (box b N r₀ : Set (Fin 1 → Fin M → AF F ⊗[F] E)) :=
    (GlobalTheory.T.adelic_boxes_compact_exhaust F E σ hσ d b 1 M).1 N r₀ hN
  have hcnt := GlobalTheory.T.theta_count_compact_finite F E σ hσ M J hJ hM μ 𝓕 hμ h𝓕 _ hcomp
  set B : ℝ≥0∞ := μ 𝓕 + cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0}
    (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞))) with hB
  have hBtop : B ≠ ⊤ := (ENNReal.add_lt_top.2 ⟨hvol, hcnt⟩).ne
  set k := 2 * Module.finrank ℚ F * M with hk
  refine ⟨(5 / r₀) ^ k * B.toReal, fun r hr => ?_⟩
  have hpt : ∀ h : HA (AF F) σ J, _ := fun h => count_le (fun d b M Λ _ e N r R => GlobalTheory.T.adelic_box_lattice_count_ratio F E σ hσ d b M Λ e N r R)
    σ J h⁻¹ b N h0 hr
  have hr0 : 0 ≤ r := h0.le.trans hr
  calc cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞)))
      ≤ ∫⁻ h in 𝓕, ENNReal.ofReal ((5 * r / r₀) ^ k) *
          (1 + ∑' X : {X : Fin 1 → Fin M → E | X ≠ 0},
            (Set.indicator (box b N r₀) (fun _ => (1 : ℝ≥0∞)))
              (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin 1 → Fin M → E)))) ∂μ :=
        lintegral_mono fun h => hpt h
    _ = ENNReal.ofReal ((5 * r / r₀) ^ k) * B := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const]
        simp [hB, cntI]
    _ = ENNReal.ofReal ((5 / r₀) ^ k * B.toReal * r ^ k) := by
        have : (5 / r₀) ^ k * B.toReal * r ^ k = (5 * r / r₀) ^ k * B.toReal := by
          rw [show 5 * r / r₀ = 5 / r₀ * r by ring, mul_pow]; ring
        rw [this, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hBtop]

end GlobalTheory.CompanionTheory.SW.CntLarge
end
end

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SdTuples

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
  {d : ℕ} (b : Module.Basis (Fin d) F E)

def cf (y : R ⊗[F] E) (k : Fin d) : R := (Algebra.TensorProduct.basis R b).repr y k

variable {R b}

def tupE (hc : IsHomeomorph (cf (F := F) (E := E) R b)) (n M : ℕ) :
    (Fin n → Fin M → R ⊗[F] E) ≃ₜ+ ((Fin M × Fin d) × Fin n → R) where
  toFun X p := cf R b (X p.2 p.1.1) p.1.2
  invFun Y a i := hc.homeomorph.symm (fun k => Y ((i, k), a))
  left_inv X := by
    funext a i
    exact hc.homeomorph.symm_apply_apply (X a i)
  right_inv Y := by
    funext p
    obtain ⟨⟨i, k⟩, a⟩ := p
    exact congrFun (hc.homeomorph.apply_symm_apply (fun k => Y ((i, k), a))) k
  map_add' X Y := by
    funext p
    simp [cf]
  continuous_toFun := by
    refine continuous_pi fun p => ?_
    exact (continuous_apply p.1.2).comp (hc.continuous.comp
      ((continuous_apply p.1.1).comp (continuous_apply p.2)))
  continuous_invFun := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    exact hc.homeomorph.symm.continuous.comp
      (continuous_pi fun k => continuous_apply ((i, k), a))

end Coord

section Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
  {d : ℕ} {b : Module.Basis (Fin d) F E}


omit [NumberField F] [NumberField E] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] in
theorem coordK_preimage (hc : IsHomeomorph (cf (F := F) (E := E) R b)) (lam : Measure R)
    (T : Set (Fin d → R)) :
    coordK R b lam (cf R b ⁻¹' T) = Measure.pi (fun _ => lam) T := by
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have he : MeasurableEmbedding (cf (F := F) (E := E) R b) := hc.homeomorph.measurableEmbedding
  have := he.comap_apply (Measure.pi fun _ : Fin d => lam) (cf R b ⁻¹' T)
  rw [Set.image_preimage_eq _ hc.surjective] at this
  exact this

theorem map_coordW (hCM : IsCMExt F E σ) (hc : IsHomeomorph (cf (F := F) (E := E) R b))
    (lam : Measure R) (hlam : lam.IsAddHaarMeasure) (n M : ℕ) :
    (coordW R b lam n M).map (tupE hc n M) = Measure.pi fun _ : (Fin M × Fin d) × Fin n => lam := by
  obtain ⟨h1, h2, h3, h4, -, -, -, hB, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := h1; haveI := h2; haveI := h3; haveI := h4
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI := hB n M
  haveI := (GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam hlam).1
  have hm : Measurable (tupE hc n M) := (map_continuous (tupE hc n M)).measurable
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (tupE hc n M) ⁻¹' Set.univ.pi s = Set.univ.pi fun a : Fin n => Set.univ.pi fun i : Fin M =>
      cf R b ⁻¹' (Set.univ.pi fun k : Fin d => s ((i, k), a)) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Prod.forall]
    exact ⟨fun h a i k => h i k a, fun h i k a => h a i k⟩
  rw [hpre]
  unfold coordW
  rw [Measure.pi_pi]
  simp_rw [Measure.pi_pi, coordK_preimage hc, Measure.pi_pi]
  rw [Fintype.prod_prod_type_right]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Fintype.prod_prod_type]


omit [NumberField F] [NumberField E] [IsTopologicalRing R] [LocallyCompactSpace R]
  [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R] in
theorem BR_eq (hc : IsHomeomorph (cf (F := F) (E := E) R b)) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F)
    (hB : ∀ x y : Fin M → R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
      (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ
        (B.map (algebraMap F R) *ᵥ fun p : Fin M × Fin d =>
          (Algebra.TensorProduct.basis R b).repr (y p.1) p.2))
    (X Y : Fin n → Fin M → R ⊗[F] E) :
    BR R σ J X Y = tupE hc n M X ⬝ᵥ
      ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F R) *ᵥ tupE hc n M Y) := by
  rw [Matrix.blockDiagonal_map _ _ (map_zero _)]
  unfold BR
  simp_rw [hB]
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type_right (f := fun p : (Fin M × Fin d) × Fin n => _)]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun p _ => ?_
  have hs : ∑ c : Fin n, ∑ q : Fin M × Fin d,
      Matrix.blockDiagonal (fun _ : Fin n => B.map (algebraMap F R)) (p, a) (q, c) *
        tupE hc n M Y (q, c) =
      ∑ q : Fin M × Fin d, B.map (algebraMap F R) p q *
        (Algebra.TensorProduct.basis R b).repr (Y a q.1) q.2 := by
    rw [Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [Matrix.blockDiagonal_apply_eq]
      rfl
    · intro c _ hca
      refine Finset.sum_eq_zero fun q _ => ?_
      rw [Matrix.blockDiagonal_apply_ne _ _ _ (Ne.symm hca), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ a) h
  rw [hs]
  rfl

theorem sdW_iff (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F)
    (hB : ∀ x y : Fin M → R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
      (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ
        (B.map (algebraMap F R) *ᵥ fun p : Fin M × Fin d =>
          (Algebra.TensorProduct.basis R b).repr (y p.1) p.2))
    (lam : Measure R) (hlam : lam.IsAddHaarMeasure) (ψR : R → ℂ) (n : ℕ) (cc : ℝ≥0)
    (hmain : ∀ μ : Measure ((Fin M × Fin d) × Fin n → R),
      SelfDual μ (fun x y => ψR (x ⬝ᵥ
        ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F R) *ᵥ y))) ↔
        μ = cc • Measure.pi fun _ => lam)
    (μ : Measure (Fin n → Fin M → R ⊗[F] E)) :
    SdW F E σ M J R ψR n μ ↔ μ = cc • coordW R b lam n M := by
  obtain ⟨h1, h2, h3, h4, -, -, hcc, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := h1
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI := hBor n M
  have hc : IsHomeomorph (cf (F := F) (E := E) R b) := hcc d b
  set e := tupE hc n M with he
  have hm : Measurable e := (map_continuous e).measurable
  have hm' : Measurable e.symm := (map_continuous e.symm).measurable
  have inj : ∀ ν : Measure (Fin n → Fin M → R ⊗[F] E), (ν.map e).map e.symm = ν := by
    intro ν
    rw [Measure.map_map hm' hm]
    have : (e.symm ∘ e) = id := by funext X; exact e.symm_apply_apply X
    rw [this, Measure.map_id]
  have key := GlobalTheory.T.selfdual_measure_transport_equiv _ _ e μ (fun x y => ψR (x ⬝ᵥ
        ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F R) *ᵥ y)))
  have hform : SdW F E σ M J R ψR n μ ↔ SelfDual μ (fun X Y => ψR (e X ⬝ᵥ
        ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F R) *ᵥ e Y))) := by
    unfold SdW
    have : (fun X Y => ψR (BR R σ J X Y)) = (fun X Y : Fin n → Fin M → R ⊗[F] E => ψR (e X ⬝ᵥ
        ((Matrix.blockDiagonal fun _ : Fin n => B).map (algebraMap F R) *ᵥ e Y))) := by
      funext X Y
      rw [BR_eq hc J B hB X Y]
    rw [this]
  rw [hform, key, hmain]
  constructor
  · intro h
    rw [← inj μ, h, ← map_coordW hCM hc lam hlam n M, ← Measure.map_smul, inj]
    exact hm.aemeasurable
  · intro h
    rw [h, Measure.map_smul, map_coordW hCM hc lam hlam n M]
    exact hm.aemeasurable

end Meas

theorem sdW_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∀ ψ, IsCharAF F ψ → ∀ n : ℕ, ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ, SdW F E σ M J (Ainf F) (psiInf F ψ) n μ ↔ μ = cinf • coordW (Ainf F) b laminf n M) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ, SdW F E σ M J (Fv F v) (psiV F ψ v) n μ ↔ μ = c v • coordW (Fv F v) b (lam v) n M) := by
  intro F E _ _ _ _ _ σ hCM M J hJ d b laminf lam hinf hv ψ hψ n
  obtain ⟨B, hsym, hdet, -, hR'⟩ := GlobalTheory.CompanionTheory.SW.TraceCoord.exists_trace_coord F E σ hCM M J hJ d b
  have hsym' : (Matrix.blockDiagonal fun _ : Fin n => B).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.blockDiagonal_transpose]
    simp only [hsym.eq]
  have hdet' : (Matrix.blockDiagonal fun _ : Fin n => B).det ≠ 0 := by
    rw [Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => hdet
  obtain ⟨cinf, c, hU, h1, h2⟩ := GlobalTheory.T.exists_unipotentInvariant_compactlySupported_weight F hCM.1 laminf lam hinf hv ψ hψ
    ((Fin M × Fin d) × Fin n) (Matrix.blockDiagonal fun _ : Fin n => B) hsym' hdet'
  refine ⟨cinf, c, hU, ?_, fun v => ?_⟩
  · obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
    haveI := t1; haveI := t2; haveI := t3; haveI := t4
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    exact fun μ => sdW_iff hCM J B (hR' (Ainf F)).1 laminf hinf.1 (psiInf F ψ) n cinf h1 μ
  · obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    haveI := t1; haveI := t2; haveI := t3; haveI := t4
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    exact fun μ => sdW_iff hCM J B (hR' (Fv F v)).1 (lam v) (hv v).1 (psiV F ψ v) n (c v) (h2 v) μ

end GlobalTheory.CompanionTheory.SW.SdTuples
end
end
