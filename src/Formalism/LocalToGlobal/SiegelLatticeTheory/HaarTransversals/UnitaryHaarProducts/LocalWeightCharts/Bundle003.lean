module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.Bundle001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilpotentChartRightInverse
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NShear
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NilpotentChartNormBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.InstLocallyCompactSpace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.Bundle002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.UnitMulStar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

open MeasureTheory Formalism.MainNotions.S
open scoped ENNReal

namespace WlocSk

theorem nilradical_haar_unique : NUniq := by
  intro k r μ μ' hμ hμ'
  obtain ⟨c, hc0, hct, hc⟩ := HM.n_unique μ hμ
  obtain ⟨c', hc0', hct', hc'⟩ := HM.n_unique μ' hμ'
  refine ⟨c / c', ENNReal.div_ne_top hct hc0', ?_⟩
  rw [hc, hc', smul_smul, ENNReal.div_mul_cancel hc0' hct']

end WlocSk
end
end

section

open MeasureTheory Formalism.QuantumDeterminants Formalism.L2.SG.SplitPrimeNormLemmas Matrix

noncomputable section

namespace WlocSk

theorem card_CI_le (k r : ℕ) : Fintype.card (NB.CI k r) ≤ r * r + r * (k + 1) + r * r := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have h : Fintype.card (NB.UP r) ≤ Fintype.card (Fin r × Fin r) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  omega

theorem dim_lt (k r : ℕ) :
    (((2 * (2 * Fintype.card (NB.CI k r) + r)) : ℕ) : ℝ) < N1H k r := by
  have hc := card_CI_le k r
  have h1 : 2 * (2 * Fintype.card (NB.CI k r) + r) < 4 * (2 * r + k + 1) ^ 2 := by
    have : 2 * (2 * Fintype.card (NB.CI k r) + r) ≤ 2 * (2 * (r * r + r * (k + 1) + r * r) + r) := by
      omega
    refine lt_of_le_of_lt this ?_
    nlinarith
  have h2 : (1 : ℝ) ≤ Real.sqrt (2 * ((r + 1 : ℕ) : ℝ)) := by
    rw [Real.one_le_sqrt]
    have : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    push_cast; linarith
  unfold N1H
  have h1' : (((2 * (2 * Fintype.card (NB.CI k r) + r)) : ℕ) : ℝ) < 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast h1
  have hp : (0 : ℝ) ≤ 4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  nlinarith

theorem nilpotent_chart_exists : NChart := by
  intro k r
  let eC := Fintype.equivFin (NB.CI k r)
  let Φ : CSp (Fintype.card (NB.CI k r)) r → Mt k r := fun t => NB.phi0 (t.1 ∘ eC) t.2
  let ψ : Mt k r → CSp (Fintype.card (NB.CI k r)) r := fun x => (NB.psiC x ∘ eC.symm, NB.psiR x)
  have hcomp : Continuous fun t : CSp (Fintype.card (NB.CI k r)) r => (t.1 ∘ eC, t.2) :=
    (continuous_pi fun i => (continuous_apply (eC i)).comp continuous_fst).prodMk continuous_snd
  have hΦc : Continuous Φ := NB.continuous_nilpotent_chart.comp hcomp
  have hψc : Continuous ψ :=
    (continuous_pi fun j => (continuous_apply (eC.symm j)).comp NB.continuous_psiC).prodMk
      NB.continuous_psiR
  have hleft : Function.LeftInverse ψ Φ := by
    intro t
    obtain ⟨h1, h2⟩ := NB.nilpotent_chart_right_inverse (t.1 ∘ eC) t.2
    show (NB.psiC (NB.phi0 (t.1 ∘ eC) t.2) ∘ eC.symm, NB.psiR (NB.phi0 (t.1 ∘ eC) t.2)) = t
    rw [h1, h2]
    ext j <;> simp
  have hright : ∀ x : Mt k r, Matrix.of x ∈ Nset k r → Φ (ψ x) = x := by
    intro x hx
    show NB.phi0 ((NB.psiC x ∘ eC.symm) ∘ eC) (NB.psiR x) = x
    have : (NB.psiC x ∘ eC.symm) ∘ eC = NB.psiC x := by funext i; simp
    rw [this]
    exact NB.nilpotent_chart_left_inverse hx
  have hrange : Set.range Φ = {x | Matrix.of x ∈ Nset k r} := by
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact NB.test_vector_mem_schwartz_bruhat _ _
    · intro hx
      exact ⟨ψ x, hright x hx⟩
  refine ⟨Fintype.card (NB.CI k r), r, 2, Φ, (r : ℝ) + 2, by norm_num, dim_lt k r, by positivity,
    ?_, hrange, ?_, ?_⟩
  ·
    refine MeasurableEmbedding.of_measurable_inverse hΦc.measurable ?_ hψc.measurable hleft
    have : Set.range Φ = {x | Φ (ψ x) = x} := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        show Φ (ψ (Φ t)) = Φ t
        rw [hleft t]
      · intro hx
        exact ⟨ψ x, hx⟩
    rw [this]
    exact (isClosed_eq (hΦc.comp hψc) continuous_id).measurableSet
  ·
    intro m₀ h0
    let G : (Fin (Fintype.card (NB.CI k r)) → ℂ) → Fin (Fintype.card (NB.CI k r)) → ℂ :=
      fun y j => NB.shG m₀ (y ∘ eC) (eC.symm j)
    let H : (Fin (Fintype.card (NB.CI k r)) → ℂ) → Fin r → ℝ := fun y => NB.shH m₀ (y ∘ eC)
    have hyc : Continuous fun y : Fin (Fintype.card (NB.CI k r)) → ℂ => y ∘ eC :=
      continuous_pi fun i => continuous_apply (eC i)
    refine ⟨fun t => (t.1 + G t.1, t.2 + H t.1), ?_, ?_⟩
    · refine NB.shear_mp (fun j => NB.rk (eC.symm j)) G H
        (fun j => ((NB.continuous_shG m₀ (eC.symm j)).comp hyc).measurable) ?_
        ((NB.continuous_shH m₀).comp hyc).measurable
      intro j y y' hyy
      refine NB.shG_dep m₀ (eC.symm j) (y ∘ eC) (y' ∘ eC) fun i hi => ?_
      exact hyy (eC i) (by simpa using hi)
    · intro t
      obtain ⟨h1, h2⟩ := NB.lmul_coord h0 (t.1 ∘ eC) t.2
      have hmem : m₀ * NB.phi0 (t.1 ∘ eC) t.2 ∈ Nset k r := UnitaryGroupBasics.mem_n_mul h0 (NB.test_vector_mem_schwartz_bruhat _ _)
      show m₀ * NB.phi0 (t.1 ∘ eC) t.2 = NB.phi0 ((t.1 + G t.1) ∘ eC) (t.2 + H t.1)
      have e1 : (t.1 + G t.1) ∘ eC = t.1 ∘ eC + NB.shG m₀ (t.1 ∘ eC) := by
        funext i; simp [G]
      rw [e1, ← h1]
      show _ = NB.phi0 (NB.psiC (m₀ * NB.phi0 (t.1 ∘ eC) t.2)) (t.2 + NB.shH m₀ (t.1 ∘ eC))
      rw [← h2]
      exact (NB.nilpotent_chart_left_inverse hmem).symm
  ·
    intro t
    have hg := NB.nilpotent_chart_norm_bound (t.1 ∘ eC) t.2
    have hn : ‖t‖ ≤ ‖(t.1 ∘ eC, t.2)‖ := by
      rw [Prod.norm_def, Prod.norm_def]
      refine max_le_max ?_ le_rfl
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
      have := norm_le_pi_norm (t.1 ∘ eC) (eC.symm j)
      simpa using this
    calc 1 + ‖t‖ ≤ 1 + ‖(t.1 ∘ eC, t.2)‖ := by linarith
      _ ≤ _ := hg

end WlocSk
end
end

section

noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas Matrix
open scoped InnerProductSpace ENNReal

namespace WlocSk.DecayR

lemma opn_conj {n : ℕ} {P g : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Formalism.L2.SG.WuDecay.opn (P⁻¹ * g * P) = Formalism.L2.SG.WuDecay.opn g := by
  unfold Formalism.L2.SG.WuDecay.opn
  have h1 : star P * P = 1 := by
    first
      | exact Unitary.star_mul_self_of_mem hP
      | exact unitary.star_mul_self_of_mem hP
  have h2 : P * star P = 1 := by
    first
      | exact Unitary.mul_star_self_of_mem hP
      | exact unitary.mul_star_self_of_mem hP
  have hPinv : P⁻¹ = star P := Matrix.inv_eq_left_inv h1
  have hU1 : star (Matrix.toEuclideanCLM (𝕜 := ℂ) P) * Matrix.toEuclideanCLM (𝕜 := ℂ) P = 1 := by
    rw [← map_star, ← map_mul, h1, map_one]
  have hU2 : Matrix.toEuclideanCLM (𝕜 := ℂ) P * star (Matrix.toEuclideanCLM (𝕜 := ℂ) P) = 1 := by
    rw [← map_star, ← map_mul, h2, map_one]
  have hU : Matrix.toEuclideanCLM (𝕜 := ℂ) P ∈ unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) :=
    ⟨hU1, hU2⟩
  have hUs : star (Matrix.toEuclideanCLM (𝕜 := ℂ) P) ∈
      unitary (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := by
    refine ⟨?_, ?_⟩
    · rw [star_star]
      exact hU2
    · rw [star_star]
      exact hU1
  rw [hPinv, map_mul, map_mul, map_star, CStarRing.norm_mul_mem_unitary _ hU,
    CStarRing.norm_mem_unitary_mul _ hUs]

variable {k r : ℕ}

lemma transport {ε : Fin (2 * r + k + 1) → Bool} {P' : Mat k r} (hP' : IsCayleyU k r ε P')
    {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hG : IsHaarOn (Gr k r) μG) :
    ∃ cc : ℝ≥0∞, cc ≠ 0 ∧ cc ≠ ⊤ ∧ μG = (cc • PI.UpqRep.muG ε).map (Port.conjPrime₂ ε P') := by
  have : SigmaFinite μG := hG.1
  have hPJ' : P'ᴴ * PI.UpqRep.Jm ε * P' = PI.UpqRep.Hpk k r := hP'.1.2
  have hconc : μG {x | Matrix.of x ∉ PI.UpqRep.UH (P'ᴴ * PI.UpqRep.Jm ε * P')} = 0 := by
    rw [hPJ']; exact hG.2.2.1
  have hinv : ∀ s ∈ PI.UpqRep.UH (P'ᴴ * PI.UpqRep.Jm ε * P'),
      μG.map (fun x => Matrix.of.symm (s * Matrix.of x)) = μG := by
    rw [hPJ']; intro s hs; exact hG.2.2.2 s hs
  exact Port.haar_transport ε P' hP'.1.1 μG hG.2.1 hconc hinv

theorem decay_estimate : WlocSk.Decay := by
  intro hCW k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp
  obtain ⟨hS, hσ, _, hw, hG, _⟩ := hyp
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨P', hP', hLow⟩ := hw
  have hDS' := OneP.isDS_cayley hP hP' hDS
  obtain ⟨_, _, _, _, _, _, hHC, _, _, hGap⟩ := hS
  have hC := hCW k r v b hHC hGap H (fun g => σ (P'⁻¹ * g * P')) hDS' w hLow
  obtain ⟨cc, _, hctop, hμ⟩ := transport hP' hG
  have hE := Port.conjP_measurableEmbedding (eps48 k r) P' hP'.1.1
  rw [hμ, hE.lintegral_map, lintegral_smul_measure]
  refine ENNReal.mul_lt_top hctop.lt_top (lt_of_eq_of_lt (lintegral_congr fun g => ?_) hC)
  show ‖⟪w, σ (P'⁻¹ * uMat g * P') w⟫_ℂ‖ₑ *
      ENNReal.ofReal (Formalism.L2.SG.WuDecay.opn (P'⁻¹ * uMat g * P') ^ N1H k r) =
    ‖⟪w, σ (P'⁻¹ * uMat g * P') w⟫_ℂ‖ₑ *
      ENNReal.ofReal (‖Matrix.toEuclideanCLM (𝕜 := ℂ) (uMat g)‖ ^
        (4 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 * Real.sqrt (2 * ((r + 1 : ℕ) : ℝ))))
  rw [opn_conj hP'.2]
  rfl

theorem reproducing_formula_holds : WlocSk.ReprodG := by
  intro hR k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp
  obtain ⟨_, hσ, _, hw, hG, _⟩ := hyp
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨P', hP', hLow⟩ := hw
  have hDS' := OneP.isDS_cayley hP hP' hDS
  obtain ⟨α', Ω', a', hΩc, hαm, hαs, hαb, hαi, hαe⟩ :=
    hR _ (eps48 k r) (lam48 k r v b) H (fun g => σ (P'⁻¹ * g * P')) hDS' w hLow.2
  obtain ⟨cc, hc0, hctop, hμ⟩ := transport hP' hG
  have hE := Port.conjP_measurableEmbedding (eps48 k r) P' hP'.1.1
  have hct : 0 < cc.toReal := ENNReal.toReal_pos hc0 hctop
  set ψ := Port.conjPrime₂ (eps48 k r) P' with hψ
  set f : Formalism.REAL.UJ (eps48 k r) → ℂ := fun g => (cc.toReal⁻¹ : ℝ) • α' g with hf
  set α : Mat k r → ℂ := fun y => Function.extend ψ f (fun _ => 0) (Matrix.of.symm y) with hα
  have hαψ : ∀ g, α (Matrix.of (ψ g)) = f g := fun g => hE.injective.extend_apply _ _ g
  have hcase : ∀ y : Mat k r, α y ≠ 0 → ∃ g, ψ g = Matrix.of.symm y ∧ α y = f g := by
    intro y hy
    by_cases h : ∃ g, ψ g = Matrix.of.symm y
    · obtain ⟨g, hg⟩ := h
      refine ⟨g, hg, ?_⟩
      show Function.extend ψ f (fun _ => 0) (Matrix.of.symm y) = f g
      rw [← hg]; exact hE.injective.extend_apply _ _ g
    · exact absurd (Function.extend_apply' f (fun _ => (0 : ℂ)) _ h) hy
  have hcont : Continuous fun g : Formalism.REAL.UJ (eps48 k r) => P'⁻¹ * uMat g * P' :=
    (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)).matrix_mul
      continuous_const
  have hinv := OneP.unit_inv hP'.2
  have h1 := OneP.unit_star_mul hP'.2
  have h2 := OneP.unit_mul_star hP'.2
  refine ⟨α, (fun g => P'⁻¹ * uMat g * P') '' Ω', cc.toReal⁻¹ * max a' 0, hΩc.image hcont, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rintro _ ⟨g, _, rfl⟩
    have hg : (uMat g)ᴴ * Formalism.REAL.Jm (eps48 k r) * uMat g = Formalism.REAL.Jm (eps48 k r) := g.2
    show (P'⁻¹ * uMat g * P')ᴴ * Formalism.QuantumDeterminants.Hpk k r * (P'⁻¹ * uMat g * P') = Formalism.QuantumDeterminants.Hpk k r
    rw [← hP'.1.2, hinv]
    calc (P'ᴴ * uMat g * P')ᴴ * (P'ᴴ * Formalism.REAL.Jm (eps48 k r) * P') * (P'ᴴ * uMat g * P')
        = P'ᴴ * (uMat g)ᴴ * (P' * P'ᴴ) * Formalism.REAL.Jm (eps48 k r) * (P' * P'ᴴ) * uMat g * P' := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = P'ᴴ * ((uMat g)ᴴ * Formalism.REAL.Jm (eps48 k r) * uMat g) * P' := by
          rw [h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = P'ᴴ * Formalism.REAL.Jm (eps48 k r) * P' := by rw [hg]
  · have hfm : Measurable f := hαm.const_smul (cc.toReal⁻¹ : ℝ)
    exact hE.measurable_extend hfm measurable_const
  · intro y hy
    obtain ⟨g, hg, hyg⟩ := hcase y hy
    have hg0 : α' g ≠ 0 := by
      intro h0; apply hy; rw [hyg, hf]; simp [h0]
    refine ⟨g, hαs g hg0, ?_⟩
    rw [← Matrix.of.apply_symm_apply y, ← hg]
    rfl
  · intro y
    have hcn : 0 ≤ cc.toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
    by_cases hy : α y = 0
    · rw [hy, norm_zero]; exact mul_nonneg hcn (le_max_right _ _)
    · obtain ⟨g, _, hyg⟩ := hcase y hy
      rw [hyg, hf]
      simp only
      rw [norm_smul, Real.norm_of_nonneg hcn]
      exact mul_le_mul_of_nonneg_left ((hαb g).trans (le_max_left _ _)) hcn
  · have hfun : (fun x : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of x) • σ (Matrix.of x) w) ∘ ψ =
        fun g => (cc.toReal⁻¹ : ℝ) • (α' g • σ (P'⁻¹ * uMat g * P') w) := by
      funext g
      simp only [Function.comp]
      rw [hαψ, hf, smul_assoc]
      rfl
    rw [hμ, hE.integrable_map_iff, hfun]
    exact (hαi.smul_measure hctop).smul _
  · have hfun : (fun x : Formalism.QuantumDeterminants.Mt k r => α (Matrix.of x) • σ (Matrix.of x) w) ∘ ψ =
        fun g => (cc.toReal⁻¹ : ℝ) • (α' g • σ (P'⁻¹ * uMat g * P') w) := by
      funext g
      simp only [Function.comp]
      rw [hαψ, hf, smul_assoc]
      rfl
    rw [hμ, hE.integral_map, integral_smul_measure]
    have hpt : ∀ x, α (Matrix.of (ψ x)) • σ (Matrix.of (ψ x)) w =
        (cc.toReal⁻¹ : ℝ) • (α' x • σ (P'⁻¹ * uMat x * P') w) := fun x => congrFun hfun x
    simp_rw [hpt]
    rw [integral_smul]
    have he : ∫ g, α' g • σ (P'⁻¹ * uMat g * P') w ∂(PI.UpqRep.muG (eps48 k r)) = w := hαe
    rw [he, smul_smul, mul_inv_cancel₀ hct.ne', one_smul]

end WlocSk.DecayR

section Check
end Check
end
end

section

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas
open scoped ENNReal InnerProductSpace

namespace WlocSk.ANz

variable {k r : ℕ}

theorem haarG_pos {μG : Measure (Formalism.QuantumDeterminants.Mt k r)} (hμ : IsHaarOn (Gr k r) μG) {U : Set (Mat k r)}
    (hU : IsOpen U) {x : Mat k r} (hxU : x ∈ U) (hxG : x ∈ Gr k r) :
    0 < μG {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ U ∩ Gr k r} := by
  obtain ⟨c, hc0, -, hμeq⟩ := WlocSk.HM.haar_unique (Gr k r) WlocSk.HM.uh_clsub μG hμ
  have hVm : MeasurableSet {y : Formalism.QuantumDeterminants.Mt k r | Matrix.of y ∈ U ∩ Gr k r} :=
    (hU.preimage WlocSk.Grp.continuous_of).measurableSet.inter
      (WlocSk.Grp.isClosed_Gr.preimage WlocSk.Grp.continuous_of).measurableSet
  have hvt : Continuous (WlocSk.HM.Grp.vt :
      WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub → Formalism.QuantumDeterminants.Mt k r) := WlocSk.HM.Grp.embt.continuous
  have hO : IsOpen ((fun a => Matrix.of (WlocSk.HM.Grp.vt a)) ⁻¹' U :
      Set (WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub)) :=
    hU.preimage (WlocSk.Grp.continuous_of.comp hvt)
  have hne : ((fun a => Matrix.of (WlocSk.HM.Grp.vt a)) ⁻¹' U :
      Set (WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub)).Nonempty :=
    ⟨WlocSk.HM.Grp.mk x hxG, hxU⟩
  have hpos := hO.measure_pos (Measure.haar : Measure (WlocSk.HM.Grp (Gr k r) WlocSk.HM.uh_clsub)) hne
  rw [hμeq, Measure.smul_apply, smul_eq_mul, WlocSk.HM.hmeas, Measure.map_apply hvt.measurable hVm]
  refine ENNReal.mul_pos hc0 (ne_of_gt (lt_of_lt_of_le hpos (measure_mono ?_)))
  intro a ha
  exact ⟨ha, WlocSk.HM.Grp.mem a⟩

theorem aNonzero_of (hSG : SGrp) (hPU : PiUnit) (hSP : SProd) (hAE : AEquiv) (hAC : ACont) :
    ANonzero := by
  intro hNV k r z c u v b H _ _ _ σ Vp _ _ _ π w μG μS ν μW μN hyp hR hCW
  obtain ⟨hset, hDS, hHC, hLU, hG, -, -, hW, hN, -, -⟩ := id hyp
  obtain ⟨hk1, hev, hz, hT, hc, hu, hl, hI, hH2, hGB⟩ := hset
  have hk2 : 2 ≤ k := by obtain ⟨m, hm⟩ := hev; omega
  obtain ⟨x, x₀, hx, hx₀, hne⟩ :=
    hNV k r z c u v b hk2 hev hz hT hc hu hl hI hH2 hGB H σ hDS Vp π hHC w hLU μW μN hW hN
  have hFi : Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ * star (psiGen k r z c (Matrix.of p.2))) •
        π (Matrix.of p.1)⁻¹) (μW.prod μN) := by
    by_contra hni
    exact hne (integral_undef hni)
  obtain ⟨ξ, hξ⟩ : ∃ ξ : Vp, (∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (⟪σ x₀ w, σ (Matrix.of p.1 * Matrix.of p.2) (σ x w)⟫_ℂ * star (psiGen k r z c (Matrix.of p.2))) •
        π (Matrix.of p.1)⁻¹ ∂(μW.prod μN)) ξ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (ContinuousLinearMap.ext hall)
  rw [ContinuousLinearMap.integral_apply hFi] at hξ
  set A := Af z c σ π μW μN w x₀ ξ with hAdef
  have hAx : A x ≠ 0 := hξ
  have hcont : ContinuousOn A (Gr k r) :=
    hAC k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ
  have hequiv : IsSPsiEquiv z (psiGen k r z c) π A :=
    hAE k r z c u v b H σ Vp π w μG μS ν μW μN hyp hR hCW x₀ hx₀ ξ
  obtain ⟨hWG, hNG, -, hNg, -⟩ := hSG k r z c hz hT
  have hπ := (hPU k r z u Vp π hz hT hHC).2

  have hApos : 0 < ‖A x‖ := norm_pos_iff.mpr hAx
  obtain ⟨ε, hε, hεlt⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < ‖A x‖ := ⟨‖A x‖ / 2, half_pos hApos, half_lt_self hApos⟩
  have hevn : ∀ᶠ y in nhdsWithin x (Gr k r), ε < ‖A y‖ :=
    (hcont x hx).norm.eventually (lt_mem_nhds hεlt)
  obtain ⟨U, hUo, hxU, hUsub⟩ := mem_nhdsWithin.mp hevn

  set V : Set (Formalism.QuantumDeterminants.Mt k r) := {y | Matrix.of y ∈ U ∩ Gr k r} with hVdef
  have hVm : MeasurableSet V :=
    (hUo.preimage WlocSk.Grp.continuous_of).measurableSet.inter
      (WlocSk.Grp.isClosed_Gr.preimage WlocSk.Grp.continuous_of).measurableSet
  have hμV : 0 < μG V := haarG_pos hG hUo hxU hx

  obtain ⟨cS, hcS0, -, hunf⟩ := unfold_of hSP hyp
  have hfm : Measurable (V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)) := measurable_one.indicator hVm
  have := hW.1
  have := hN.1
  set g : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun x => ∫⁻ p, V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
      (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) with hgdef
  have hU' : ∫⁻ x, g x ∂ν = cS * μG V := by
    have h := hunf _ hfm
    rw [lintegral_indicator_one hVm] at h
    exact h
  have hjoint : Measurable (fun q : Formalism.QuantumDeterminants.Mt k r × (Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) =>
      V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (fun i j => (Matrix.of (mulP q.2) * Matrix.of q.1) i j)) := by
    refine hfm.comp (Continuous.measurable ?_)
    exact (WlocSk.Grp.continuous_of.comp (continuous_mulP.comp continuous_snd)).matrix_mul
      (WlocSk.Grp.continuous_of.comp continuous_fst)
  have hgm : Measurable g := hjoint.lintegral_prod_right'
  set P : Set (Formalism.QuantumDeterminants.Mt k r) := {x | 0 < g x} with hPdef
  have hPm : MeasurableSet P := measurableSet_lt measurable_const hgm
  have hPpos : ν P ≠ 0 := by
    intro h0
    have hae : ∀ᵐ x ∂ν, g x = 0 := by
      refine ae_iff.mpr (measure_mono_null (fun x hx => ?_) h0)
      exact pos_iff_ne_zero.mpr hx
    have h1 : ∫⁻ x, g x ∂ν = 0 := by rw [lintegral_congr_ae hae, lintegral_zero]
    rw [h1] at hU'
    exact (ENNReal.mul_pos hcS0 hμV.ne').ne' hU'.symm

  have hTae : ∀ᵐ p ∂(μW.prod μN),
      Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
    have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z :=
      Measure.quasiMeasurePreserving_fst.ae (ae_iff.mpr hW.2.2.1)
    have h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r :=
      Measure.quasiMeasurePreserving_snd.ae (ae_iff.mpr hN.2.2.1)
    filter_upwards [h1, h2] with p hp1 hp2
    exact ⟨hp1, hp2⟩

  have key : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ Gr k r → 0 < g x → ε < ‖A (Matrix.of x)‖ := by
    intro x hxG hgx
    by_contra hle
    apply hgx.ne'
    have hae : ∀ᵐ p ∂(μW.prod μN), V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
        (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) = 0 := by
      filter_upwards [hTae] with p hp
      apply Set.indicator_of_notMem
      intro hpV
      have h1 : ε < ‖A (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ := hUsub hpV
      have h2 : ‖A (Matrix.of p.1 * Matrix.of p.2 * Matrix.of x)‖ = ‖A (Matrix.of x)‖ := by
        rw [hequiv _ hp.1 _ hp.2 _ hxG, norm_smul, (hNg _ hp.2 _ hp.2).2.2.2.2, hπ _ hp.1, one_mul]
      exact hle (h2 ▸ h1)
    show ∫⁻ p, V.indicator (1 : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞)
        (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) = 0
    rw [lintegral_congr_ae hae, lintegral_zero]
  have hνG : ∀ᵐ x ∂ν, Matrix.of x ∈ Gr k r := ae_iff.mpr (nu_conc_of hSG hyp)
  have hlow : ∀ᵐ x ∂ν, P.indicator (fun _ => ENNReal.ofReal ε ^ 2) x ≤
      (‖A (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [hνG] with x hxG
    by_cases hxP : x ∈ P
    · rw [Set.indicator_of_mem hxP]
      have hb : ENNReal.ofReal ε ≤ (‖A (Matrix.of x)‖₊ : ℝ≥0∞) := by
        refine ENNReal.ofReal_le_of_le_toReal ?_
        rw [ENNReal.coe_toReal, coe_nnnorm]
        exact (key x hxG hxP).le
      gcongr
    · rw [Set.indicator_of_notMem hxP]
      exact bot_le
  refine ⟨x₀, hx₀, ξ, fun hzero => ?_⟩
  have hmono : ∫⁻ x, P.indicator (fun _ => ENNReal.ofReal ε ^ 2) x ∂ν ≤
      ∫⁻ x, (‖A (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν := lintegral_mono_ae hlow
  have hz' : ∫⁻ x, (‖A (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν = 0 := hzero
  rw [lintegral_indicator_const hPm, hz'] at hmono
  have hne0 : ENNReal.ofReal ε ^ 2 * ν P ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hε).ne') hPpos
  exact hne0 (le_zero_iff.mp hmono)

end WlocSk.ANz
end
end
