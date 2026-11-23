module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle198
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle169
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle121
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle196
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle123
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle144
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle223
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle197
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle199
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle184
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle124
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle225
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle003
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle231
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WhitX

theorem u_formula (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (ω : A.K → ℂ) (μ : Measure A.L) (γ : ℂ)
    (W : SpecialLinearGroup (Fin 2) A.K → (A.L → ℂ) → A.L → ℂ) (hW : A.IsWeil ψ x ω μ γ W)
    (φ : A.L → ℂ) (hφ : IsTest φ) (z : A.K) :
    W (wS A.K * nS z) φ 0 = γ * ∫ y, φ y * A.psiK ψ (z * x * A.NL y) ∂μ := by
  obtain ⟨hrep, hform⟩ := hW
  rw [hrep.2.2.1 _ _ _ hφ, (hform _ (hrep.1 _ _ hφ)).2.2 0]
  congr 1
  unfold fourB
  congr 1
  funext y
  rw [(hform φ hφ).1 z y]
  simp [Et.kerL, Et.psiK, mul_comm]

theorem M_sub (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
    [Unram F E] (A : Et F E) (c : F) (hc : c ≠ 0) :
    ∃ M : AddSubgroup A.K, (M : Set A.K) = {z : A.K | c • z ∈ A.OK} ∧ IsOpen (M : Set A.K) ∧ IsCompact (M : Set A.K) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hOo, hOc, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  refine ⟨(R.toAddSubgroup).comap (DistribSMul.toAddMonoidHom A.K c), ?_, ?_, ?_⟩
  · ext z; simp [← hR]
  · have : ((R.toAddSubgroup).comap (DistribSMul.toAddMonoidHom A.K c) : Set A.K) = (fun z => c • z) ⁻¹' A.OK := by
      ext z; simp [← hR]
    rw [this]; exact hOo.preimage (continuous_const_smul c)
  · have : ((R.toAddSubgroup).comap (DistribSMul.toAddMonoidHom A.K c) : Set A.K) = (fun z => c⁻¹ • z) '' A.OK := by
      ext z; simp only [AddSubgroup.coe_comap, Set.mem_preimage, Set.mem_image, DistribSMul.toAddMonoidHom_apply]
      constructor
      · intro h; exact ⟨c • z, by simpa [← hR] using h, by simp [smul_smul, inv_mul_cancel₀ hc]⟩
      · rintro ⟨w, hw, rfl⟩; simpa [smul_smul, mul_inv_cancel₀ hc, ← hR] using hw
    rw [this]; exact hOc.image (continuous_const_smul c⁻¹)

theorem lam_weil_eventually : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (x : A.Kˣ) (γ : ℂ) W, A.IsWeil ψ x A.etaK (m.μL x) γ W → ∀ φ, IsTest φ → ∀ a : A.K, IsUnit a → (∀ y : A.L, IsUnit y → a = x * A.NL y → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ m.μK ψ a (fun g => W g φ 0) c = γ * A.orbL m.ν φ y) ∧ ((¬ ∃ y : A.L, IsUnit y ∧ a = x * A.NL y) → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ m.μK ψ a (fun g => W g φ 0) c = 0) := by
  intro F E _ _ _ _ _ A ψ hψ m x γ W hW φ hφ a ha
  haveI := m.sdK.1
  haveI := (m.sdL x).1
  obtain ⟨-, -, hnd, -, -, -, -, -, -, hOo, -, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  have key : ∀ c : F, c ≠ 0 → A.abelian₂ m.μK ψ a (fun g => W g φ 0) c =
      γ * ((m.μK {z | c • z ∈ A.OK}).toReal : ℂ) *
        ∫ y, φ y * Set.indicator {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1} (fun _ => (1 : ℂ))
          ((x : A.K) * A.NL y - a) ∂(m.μL x) := by
    intro c hc
    unfold Et.abelian₂
    simp_rw [u_formula F E A ψ x A.etaK (m.μL x) γ W hW φ hφ, mul_assoc γ]
    rw [integral_const_mul, GlobalTheory.T.setIntegral_integral_psiK_swap F E A ψ hψ m.μK inferInstance (m.μL x) inferInstance φ hφ x a c hc]
    simp_rw [GlobalTheory.T.integral_psiK_over_scaled_integers_eq_volume_indicator F E A ψ hψ m.μK inferInstance c hc]
    congr 1
    rw [← integral_const_mul]
    congr 1; funext y
    simp only [Set.indicator]
    split_ifs <;> ring
  obtain ⟨U1, hU1, hinv⟩ := GlobalTheory.T.exists_nhds_one_etaleAlgebra_mul_invariant F E A φ hφ
  have hOK1 : A.OK ∈ 𝓝 (1 : A.K) := hOo.mem_nhds (by rw [← hR]; exact R.one_mem)
  have hsq := GlobalTheory.T.finiteEtale_exists_sq_root_near_one F E A (U1 ∩ A.OK) (inter_mem hU1 hOK1)
  have hcont : Tendsto (fun b : A.K => 1 + Ring.inverse a * b) (𝓝 0) (𝓝 1) := by
    have : Continuous (fun b : A.K => 1 + Ring.inverse a * b) := by fun_prop
    simpa using this.tendsto 0
  have hU : {b : A.K | ∃ s ∈ U1 ∩ A.OK, ∃ s' ∈ U1 ∩ A.OK, s * s' = 1 ∧ s ^ 2 = 1 + Ring.inverse a * b} ∈ 𝓝 (0 : A.K) :=
    hcont hsq
  have hev := GlobalTheory.T.scaledIntegersK_annihilator_small_near_zero F E A ψ hψ _ hU
  have hne : ∀ᶠ c in 𝓝[≠] (0 : F), c ≠ 0 := self_mem_nhdsWithin
  constructor
  · intro y hy hay
    filter_upwards [hev, hne] with c hc hc0
    rw [key c hc0]
    obtain ⟨D, hDset, hDo, hDc⟩ := GlobalTheory.T.exists_openCompact_annihilator_scaled_integersK F E A ψ hψ c hc0
    obtain ⟨M, hMset, hMo, hMc⟩ := M_sub F E A c hc0
    have hMD : m.μK M * m.μK D = 1 := by
      have h := ((GlobalTheory.T.selfDual_iff_lattice_volume_and_plancherel_alt F E ψ hψ A.K (Algebra.traceForm F A.K) (Algebra.traceForm_isSymm F) hnd m.μK
        inferInstance).1 M hMo hMc).1
      have hk : A.kerK ψ = fun x y => ψ (Algebra.traceForm F A.K x y) := by
        funext x y; simp [Et.kerK, Et.psiK, Algebra.traceForm_apply]
      have hsd : SelfDual m.μK (fun x y => ψ (Algebra.traceForm F A.K x y)) := hk ▸ m.sdK
      have hDeq : (D : Set A.K) = {y | ∀ x ∈ M, ψ (Algebra.traceForm F A.K x y) = 1} := by
        rw [hDset]; ext b; simp [← SetLike.mem_coe, hMset, Et.psiK, Algebra.traceForm_apply]
      rw [hDeq]; exact h.1 hsd
    rw [← hDset, ← hMset]
    subst hay
    rw [GlobalTheory.T.truncatedIntegral_eq_vol_mul_orbitalIntegral F E A (GlobalTheory.T.finiteEtaleHermitianPair_norm_properties F E A) (GlobalTheory.T.absK_multiplicative_unitOne_haarScaling F E A) ψ hψ m x y hy D hDo hDc φ hφ ?_]
    · have : (m.μK M).toReal * (m.μK D).toReal = 1 := by rw [← ENNReal.toReal_mul, hMD]; simp
      have : ((m.μK M).toReal : ℂ) * ((m.μK D).toReal : ℂ) = 1 := by exact_mod_cast this
      linear_combination (γ * A.orbL m.ν φ y) * this
    · intro b hb
      have hb' := hc b (by rw [← SetLike.mem_coe, hDset] at hb; exact hb)
      obtain ⟨s, ⟨hsU, hsO⟩, s', ⟨hsU', hsO'⟩, hss, hs2⟩ := hb'
      exact ⟨s, s', hsO, hsO', hss, hs2, hinv s hsU s' hsU' hss⟩
  · intro hno
    filter_upwards [hev, hne] with c hc hc0
    rw [key c hc0]
    have hz := GlobalTheory.T.truncated_set_empty_outside_norm_coset F E A (GlobalTheory.T.finiteEtaleHermitianPair_norm_properties F E A) x a {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1}
      (fun b hb => by
        obtain ⟨s, -, s', -, hss, hs2⟩ := hc b hb
        exact ⟨s, s', hss, hs2⟩) ha hno
    have : (fun y => φ y * Set.indicator {b : A.K | ∀ z : A.K, c • z ∈ A.OK → A.psiK ψ (z * b) = 1}
        (fun _ => (1 : ℂ)) ((x : A.K) * A.NL y - a)) = fun _ => 0 := by
      funext y; rw [Set.indicator_of_notMem (hz y)]; simp
    rw [this]; simp

end GlobalTheory.JR.WhitX
end
end

section

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory

theorem scale_integral : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (f : A.K → ℂ) (t : A.K), IsUnit t → ∫ b, f (t * b) ∂μK = ((A.absK t : ℂ))⁻¹ * ∫ s, f s ∂μK := by
  intro F E _ _ _ _ _ A μK hH f t ht
  have := Unram.lcF (F := F) (E := E); have := Unram.ultraF (F := F) (E := E)
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.K
  have hme : MeasurableEmbedding (fun b : A.K => ht.unit • b) := (Homeomorph.smul ht.unit).measurableEmbedding
  have hmap : Measure.map (fun b : A.K => ht.unit • b) μK =
      ((distribHaarChar A.K ht.unit : ENNReal))⁻¹ • μK := by
    ext S hS
    rw [hme.map_apply, Measure.smul_apply, smul_eq_mul]
    have h1 := distribHaarChar_mul μK ht.unit⁻¹ S
    rw [Set.preimage_smul, ← h1, map_inv, ENNReal.coe_inv (distribHaarChar_pos).ne']
  have hint : ∫ b, f (t * b) ∂μK = ∫ b, f b ∂(Measure.map (fun b : A.K => ht.unit • b) μK) := by
    rw [hme.integral_map]; rfl
  rw [hint, hmap, integral_smul_measure]
  simp [Et.absK, ht, Complex.real_smul]

theorem jHyp_wn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (φ' : A.K × A.K → ℂ) (z : A.K), A.jHyp μK ψ φ' (wS A.K * nS z) = ∫ t, (∫ b, φ' (b, t) * A.psiK ψ (t * z * b) ∂μK) * A.etaK t ∂μK := by
  intro F E _ _ _ _ _ A ψ μK hH φ' z
  have := Unram.lcF (F := F) (E := E); have := Unram.ultraF (F := F) (E := E)
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.JR.EtMeas.top_facts F A.K
  have : μK.IsNegInvariant := Measure.IsAddHaarMeasure.isNegInvariant_of_regular μK
  have h10 : ((wS A.K * nS z : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 0 = -1 := by
    show (!![0, 1; -1, 0] * !![1, z; 0, 1] : Matrix (Fin 2) (Fin 2) A.K) 1 0 = -1
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : ((wS A.K * nS z : SpecialLinearGroup (Fin 2) A.K) : Matrix (Fin 2) (Fin 2) A.K) 1 1 = -z := by
    show (!![0, 1; -1, 0] * !![1, z; 0, 1] : Matrix (Fin 2) (Fin 2) A.K) 1 1 = -z
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have heta : ∀ t : A.K, A.etaK (-t) = A.etaK t := by
    intro t
    unfold Et.etaK
    have hg : ∀ x y : F, ‖x‖ = ‖y‖ → eta x = eta y := by
      intro x y h; unfold eta; rw [h]
    apply hg
    show ‖Algebra.norm F (-t)‖ = ‖Algebra.norm F t‖
    rw [show -t = algebraMap F A.K (-1) * t by simp, map_mul, Algebra.norm_algebraMap, norm_mul, norm_pow,
      norm_neg, norm_one, one_pow, one_mul]
  unfold Et.jHyp
  simp only [h10, h11]
  refine (integral_neg_eq_self _ μK).symm.trans ?_
  congr 1
  funext t
  simp only [neg_mul_neg, mul_one, heta, Et.tilde]

theorem whittaker_jHyp_eq_orbK : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ φ', IsTest φ' → ∀ a : A.K, IsUnit a → ∀ᶠ c in 𝓝[≠] (0 : F), A.abelian₂ μK ψ a (A.jHyp μK ψ φ') c = A.orbK μK φ' a := by
  intro F E _ _ _ _ _ A ψ hψ μK hμ φ' hφ a ha
  have hH : μK.IsAddHaarMeasure := hμ.1
  have hnull : μK {t : A.K | ¬ IsUnit t} = 0 := (GlobalTheory.T.etaleHermitianPair_structure_facts F E A).2.2.2.2.2.2.2.2.1 μK hH
  have hae : ∀ᵐ t ∂μK, IsUnit t := ae_iff.2 (by simpa using hnull)
  have hV : {v : A.K | ∀ t : A.K, IsUnit t → φ' ((a + v) * Ring.inverse t, t) = φ' (a * Ring.inverse t, t)}
      ∈ 𝓝 (0 : A.K) := by
    have h2 := GlobalTheory.T.eventually_testFunction_mul_inverse_unit_eq F E A φ' hφ a ha
    have hc : Tendsto (fun v : A.K => a + v) (𝓝 0) (𝓝 a) := by
      have := (continuous_const_add a).tendsto (0 : A.K)
      rwa [add_zero] at this
    exact hc h2
  filter_upwards [GlobalTheory.T.eventually_dual_scaled_OK_subset_nhds F E A ψ hψ _ hV, self_mem_nhdsWithin] with c hc hc0
  have hc0' : c ≠ 0 := hc0
  set M := {z : A.K | c • z ∈ A.OK} with hM
  set N := {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} with hN
  obtain ⟨hNm, hvol⟩ := GlobalTheory.T.volume_scaledIntegers_mul_volume_dual_eq_one F E A ψ hψ μK hμ c hc0'
  have hLam : A.abelian₂ μK ψ a (A.jHyp μK ψ φ') c = (((μK M).toReal : ℝ) : ℂ) *
      ∫ t, (∫ b, φ' (b, t) * N.indicator (fun _ => (1 : ℂ)) (t * b - a) ∂μK) * A.etaK t ∂μK := by
    rw [← GlobalTheory.T.truncatedWhittakerIntegral_eq_volume_mul_integral_perp F E A ψ hψ μK hH φ' hφ a c hc0']
    unfold Et.abelian₂
    simp only [jHyp_wn F E A ψ μK hH φ']
  have hin : ∀ t : A.K, IsUnit t → (∫ b, φ' (b, t) * N.indicator (fun _ => (1 : ℂ)) (t * b - a) ∂μK) =
      ((A.absK t : ℂ))⁻¹ * (φ' (a * Ring.inverse t, t) * (((μK N).toReal : ℝ) : ℂ)) := by
    intro t ht
    have h4 := scale_integral F E A μK hH (fun s => φ' (Ring.inverse t * s, t) * N.indicator (fun _ => (1 : ℂ)) (s - a)) t ht
    simp only [Ring.inverse_mul_cancel_left t _ ht] at h4
    rw [h4]
    congr 1
    have h5 : (fun s => φ' (Ring.inverse t * s, t) * N.indicator (fun _ => (1 : ℂ)) (s - a)) =
        fun s => φ' (a * Ring.inverse t, t) * N.indicator (fun _ => (1 : ℂ)) (s - a) := by
      funext s
      by_cases hs : s - a ∈ N
      · have := hc hs t ht
        simp only [add_sub_cancel] at this
        rw [mul_comm (Ring.inverse t) s, this]
      · simp [Set.indicator_of_notMem hs]
    rw [h5, integral_const_mul]
    congr 1
    have h6 : ∫ s, N.indicator (fun _ => (1 : ℂ)) (s - a) ∂μK = ∫ s, N.indicator (fun _ => (1 : ℂ)) s ∂μK :=
      integral_sub_right_eq_self (fun s => N.indicator (fun _ => (1 : ℂ)) s) a
    rw [h6, integral_indicator_const _ hNm]
    rw [Complex.real_smul, mul_one]
    rfl
  have horb : A.orbK μK φ' a = ∫ t, φ' (a * Ring.inverse t, t) * A.etaK t * ((A.absK t : ℂ))⁻¹ ∂μK := by
    unfold Et.orbK
    rw [Measure.restrict_eq_self_of_ae_mem (s := {t : A.K | IsUnit t}) hae]
  rw [hLam, horb]
  have h7 : ∫ t, (∫ b, φ' (b, t) * N.indicator (fun _ => (1 : ℂ)) (t * b - a) ∂μK) * A.etaK t ∂μK =
      (((μK N).toReal : ℝ) : ℂ) * ∫ t, φ' (a * Ring.inverse t, t) * A.etaK t * ((A.absK t : ℂ))⁻¹ ∂μK := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with t ht
    rw [hin t ht]
    ring
  rw [h7, ← mul_assoc, hvol, one_mul]

end GlobalTheory
end
end

section

noncomputable section

namespace GlobalTheory.NL.LetterFree

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem letE_mul (i : ZMod n) (a : LetA O n) : (letE i : LetA O n) * a = Pi.single i (a i) := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

theorem single_mul_letE (i : ZMod n) (a : PowerSeries O) :
    (Pi.single i a : LetA O n) * letE i = Pi.single i a := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i :=
  single_mul_letE i 1

theorem letE_mul_ne {i j : ZMod n} (h : i ≠ j) : (letE i : LetA O n) * letE j = 0 := by
  rw [letE_mul]
  simp [letE, h]

theorem sum_letE [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  funext j
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem sum_letE_smul [NeZero n] (x : W.DD T) : ∑ i : ZMod n, (letE i : LetA O n) • x = x := by
  rw [← Finset.sum_smul, sum_letE, one_smul]

theorem mem_Nl_iff (i : ZMod n) (x : W.DD T) :
    x ∈ W.Nl T i ↔ x ∈ W.N T ∧ (letE i : LetA O n) • x = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(W.N T).smul_mem _ hy, ?_⟩
    change (letE i : LetA O n) • (letE i : LetA O n) • y = (letE i : LetA O n) • y
    rw [smul_smul, letE_mul_self]
  · rintro ⟨hx, he⟩
    exact ⟨x, hx, he⟩

theorem lettersDecompose [NeZero n] : GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.LettersDecompose W T := by
  refine ⟨?_, le_antisymm (iSup_le fun i x hx => ((mem_Nl_iff W T i x).1 hx).1) fun x hx => ?_⟩
  · intro i
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hk : (⨆ (j) (_ : j ≠ i), W.Nl T j) ≤
        LinearMap.ker (LinearMap.lsmul (LetA O n) (W.DD T) (letE i)) := by
      refine iSup_le fun j => iSup_le fun hj y hy => ?_
      rw [LinearMap.mem_ker, LinearMap.lsmul_apply, ← ((mem_Nl_iff W T j y).1 hy).2, smul_smul,
        letE_mul_ne hj.symm, zero_smul]
    have h0 := hk hx'
    rw [LinearMap.mem_ker, LinearMap.lsmul_apply, ((mem_Nl_iff W T i x).1 hx).2] at h0
    exact h0
  · rw [← sum_letE_smul W T x]
    exact Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ⟨x, hx, rfl⟩

theorem isLetterBasis {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (i : ZMod n) :
    GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness.IsLetterBasis W T i (fun k => (letE i : LetA O n) • (b k : W.DD T)) := by
  have hli : LinearIndependent (LetA O n) (fun k => (b k : W.DD T)) :=
    b.linearIndependent.map' (W.N T).subtype (W.N T).ker_subtype
  refine ⟨fun k => ⟨b k, (b k).2, rfl⟩, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  have hy' : y = ∑ k, b.repr ⟨y, hy⟩ k • (b k : W.DD T) := by
    have := congrArg Subtype.val (b.sum_repr ⟨y, hy⟩)
    rw [AddSubmonoidClass.coe_finsetSum] at this
    exact this.symm
  generalize b.repr ⟨y, hy⟩ = a at hy'
  subst hy'
  have key : (letE i : LetA O n) • (∑ k, a k • (b k : W.DD T)) =
      ∑ k, (Pi.single i (a k i) : LetA O n) • (b k : W.DD T) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, letE_mul]
  refine ⟨fun k => a k i, ?_, fun c hc => ?_⟩
  · change (letE i : LetA O n) • (∑ k, a k • (b k : W.DD T)) = _
    rw [key]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_smul, single_mul_letE]
  · change (letE i : LetA O n) • (∑ k, a k • (b k : W.DD T)) = _ at hc
    rw [key] at hc
    simp only [smul_smul, single_mul_letE] at hc
    funext k
    have h0 := Fintype.linearIndependent_iff.1 hli
      (fun k => (Pi.single i (c k) : LetA O n) - Pi.single i (a k i))
      (by simp only [sub_smul, Finset.sum_sub_distrib, hc, sub_self]) k
    have h1 := congrFun h0 i
    simpa [sub_eq_zero] using h1

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letterModule

theorem exists_letter_basis {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T)) (i : ZMod n) :
    ∃ c : Module.Basis (Fin r) (PowerSeries O) ↥(W.Nl T i),
      ∀ k, (c k : W.DD T) = (letE i : LetA O n) • (b k : W.DD T) := by
  obtain ⟨hm, hu⟩ := isLetterBasis W T b i
  let f : Fin r → ↥(W.Nl T i) := fun k => ⟨_, hm k⟩
  have hs : ∀ c : Fin r → PowerSeries O, ((∑ k, c k • f k : ↥(W.Nl T i)) : W.DD T) =
      ∑ k, (Pi.single i (c k) : LetA O n) • (letE i : LetA O n) • (b k : W.DD T) := by
    intro c
    rw [AddSubmonoidClass.coe_finsetSum]
    exact Finset.sum_congr rfl fun k _ => GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.letter_smul W T i (c k) (f k)
  have hli : LinearIndependent (PowerSeries O) f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc k
    have h1 := hs c
    rw [hc] at h1
    have h2 := (hu 0 (Submodule.zero_mem _)).unique h1 (y₂ := fun _ => 0) (by simp)
    exact congrFun h2 k
  have hsp : ⊤ ≤ Submodule.span (PowerSeries O) (Set.range f) := by
    intro x _
    obtain ⟨c, hc, -⟩ := hu x.1 x.2
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨c, Subtype.ext ((hs c).trans hc.symm)⟩
  exact ⟨Module.Basis.mk hli hsp, fun k => by rw [Module.Basis.mk_apply]⟩

end Generic

theorem letters_loc {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (hT : IsCrys (P.PD K) T.ρ) :
    GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.LettersDecompose (H.W K s LL h) T ∧ GlobalTheory.IndefiniteRowSideFullHecke.LetterBasisDecomposition.LettersFree (H.W K s LL h) T ∧
      ∀ i, ∃ b : Fin (Module.finrank ↥(OL LL) ↥T.L.T) → (H.W K s LL h).DD T,
        GlobalTheory.IndefiniteRowSideFullHecke.WachLettersFreeness.IsLetterBasis (H.W K s LL h) T i b := by
  haveI := (P.PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨b⟩ := N_basis_loc H K s LL h T hT
  exact ⟨lettersDecompose _ T, fun i => ⟨(exists_letter_basis _ T b i).choose⟩,
    fun i => ⟨_, isLetterBasis _ T b i⟩⟩

end GlobalTheory.NL.LetterFree
end
end

section

noncomputable section

namespace GlobalTheory.NL.XStab

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem φpow_γA (k : ℕ) (g : W.Gam) (a : LetA O n) :
    (W.φA ^ k) (W.γA g a) = W.γA g ((W.φA ^ k) a) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', AlgHom.mul_apply, AlgHom.mul_apply, ih, W.φA_γA]

theorem X_dvd_γX (g : W.Gam) : W.X ∣ W.γA g W.X := by
  obtain ⟨c, hc⟩ : (PowerSeries.X : PowerSeries O) ∣ W.γ₀ g PowerSeries.X :=
    PowerSeries.X_dvd_iff.2 (W.γ₀_X g).1
  have h1 : W.γA g letπ = letπ * (fun _ => c) := by
    funext i
    simp [LocWach.γA, letγ, letπ, hc]
  refine ⟨(W.φA ^ (W.s - 1)) (fun _ => c), ?_⟩
  rw [LocWach.X, ← φpow_γA, h1, map_mul]

theorem γD_mem_aN_X (T : LocLat G Qp LL O) (δ : W.Gam) (x : W.DD T) (hx : x ∈ aN W T W.X) :
    W.γD T δ x ∈ aN W T W.X := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨c, hc⟩ := X_dvd_γX W δ
  refine ⟨c • W.γD T δ y, (W.N T).smul_mem _ (W.N_Γ T δ y hy), ?_⟩
  change W.X • c • W.γD T δ y = W.γD T δ (W.X • y)
  rw [γD_smulA, hc, mul_smul]

end Generic

theorem xstab : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL) (δ : ((HW l).W K s LL h).Gam) (x : ((HW l).W K s LL h).DD T), x ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X → ((HW l).W K s LL h).γD T δ x ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X :=
  fun _ HW l _ K s LL h T δ x hx => γD_mem_aN_X ((HW l).W K s LL h) T δ x hx

end GlobalTheory.NL.XStab
end
end
