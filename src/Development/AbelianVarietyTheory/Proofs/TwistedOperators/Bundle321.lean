module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle350
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.ConjAtFixedIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle303
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunSmStar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1389
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1158
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle306
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle143
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle204
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle308
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle170
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle236
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPointsUnitaryCharacterEqDetPower
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle287
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle310

@[expose] public section

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grow GlobalTheory.Size GlobalTheory.Mem.AutSpace Filter
open scoped ENNReal NNReal Topology

namespace GlobalTheory.Size.NearOne

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem exists_log (V : HSp D) (τ : D.what₂.Tau) :
    ∃ Λ : Matrix (Fin V.rank) (Fin V.rank) ℂ → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ u, Λ u ∈ lieAt V τ) ∧
      Tendsto Λ (𝓝 1) (𝓝 0) ∧
      ∀ᶠ u in 𝓝[Formalism.QuantumDeterminants.UH (gramAt D V τ)] 1, NormedSpace.exp (Λ u) = u := by
  obtain ⟨L, hL, hexp, hlog⟩ := GlobalTheory.ConjMult.hasLogAt (V := V) τ
  have hJ := GlobalTheory.SmoothAutCheck.gramAt_unit V τ
  have h0 : L 1 = 0 := by
    have h := hlog.self_of_nhds
    simpa using h
  refine ⟨fun u => (L u).1, fun u => (L u).2, ?_, ?_⟩
  · have hc : Filter.Tendsto L (𝓝 1) (𝓝 0) := h0 ▸ hL.continuousAt.tendsto
    exact (continuous_subtype_val.tendsto _).comp hc
  · filter_upwards [nhdsWithin_le_nhds hexp, self_mem_nhdsWithin] with u hu hmem
    exact hu ((GlobalTheory.ConjMult.unit_iffM hJ u).2 hmem)

private theorem continuous_matrix_exp' (n : ℕ) : Continuous (fun M : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp M) := by
  let _ : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let _ : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := .restrictScalars ℚ ℂ _
  have _ : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  exact NormedSpace.exp_continuous


attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem exists_height_le (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau) :
    ∀ᶠ X in 𝓝 (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ →
      ∀ t ∈ Set.Icc (0 : ℝ) 1, height V (oneP θ V τ X t) ≤ 2 := by
  have hl := height_laws (V := V)
  have hexp : Continuous (fun M : Matrix (Fin V.rank) (Fin V.rank) ℂ => NormedSpace.exp M) := continuous_matrix_exp' V.rank
  let F : {X : Matrix (Fin V.rank) (Fin V.rank) ℂ // X ∈ lieAt V τ} × ℝ → ℝ :=
    fun p => height V (atTau θ V τ (NormedSpace.exp (p.2 • p.1.1)))
  have hF : Continuous F := by
    have hin : Continuous fun p : {X : Matrix (Fin V.rank) (Fin V.rank) ℂ // X ∈ lieAt V τ} × ℝ =>
        NormedSpace.exp (p.2 • p.1.1) :=
      hexp.comp (continuous_snd.smul (continuous_subtype_val.comp continuous_fst))
    exact hl.2.2.2.2.comp ((GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp_continuous hin
      fun p => GlobalTheory.Mem.Lift.exp_mem p.1.2 p.2)
  have h0mem : (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ lieAt V τ := by
    show (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * gramAt D V τ + gramAt D V τ * 0 = 0
    simp
  have hF0 : ∀ t : ℝ, F (⟨0, h0mem⟩, t) = 1 := by
    intro t
    show height V (atTau θ V τ (NormedSpace.exp (t • (0 : Matrix (Fin V.rank) (Fin V.rank) ℂ)))) = 1
    rw [smul_zero, NormedSpace.exp_zero, (GlobalTheory.PointAtPlaceHom.atTau_laws D θ hθ V τ).2.1, hl.2.1]
  have hev : ∀ᶠ x in 𝓝 (⟨0, h0mem⟩ : {X : Matrix (Fin V.rank) (Fin V.rank) ℂ // X ∈ lieAt V τ}),
      ∀ t ∈ Set.Icc (0 : ℝ) 1, F (x, t) ≤ 2 := by
    refine isCompact_Icc.eventually_forall_of_forall_eventually fun t _ => ?_
    have hlt : F (⟨0, h0mem⟩, t) < 2 := by rw [hF0]; norm_num
    exact (hF.continuousAt.eventually (gt_mem_nhds hlt)).mono fun z hz => hz.le
  rw [nhds_subtype, Filter.eventually_comap] at hev
  filter_upwards [hev] with X hX hXl t ht
  exact hX ⟨X, hXl⟩ rfl t ht

theorem growthSize_sub_le (hθ : IsInfFam θ) {τ : D.what₂.Tau} {N : ℕ} {φ : GA D V → ℂ} (hs : φ ∈ SmFun θ V)
    (hf : growthSob θ V 1 N φ ≠ ⊤) {X : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hX : X ∈ lieAt V τ)
    (hh : ∀ t ∈ Set.Icc (0 : ℝ) 1, height V (oneP θ V τ X t) ≤ 2) :
    growthSize V N (rTr V (oneP θ V τ X 1) φ - φ) ≤
      ENNReal.ofReal ((∑ a : Fin V.rank × Fin V.rank, ‖X a.1 a.2‖) * (growthSob θ V 1 N φ).toReal * 2 ^ N) := by
  set S := (growthSob θ V 1 N φ).toReal with hS
  have hS0 : 0 ≤ S := ENNReal.toReal_nonneg
  set s := ∑ a : Fin V.rank × Fin V.rank, ‖X a.1 a.2‖ with hs_def
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hglob : ∀ a : Fin V.rank × Fin V.rank, ∀ h, ‖glDer θ V (τ, a) φ h‖ ≤ S * height V h ^ N := by
    intro a
    have h1 : growthSize V N (glDer θ V (τ, a) φ) ≤ growthSob θ V 1 N φ := by
      have h0 := le_wordSum (A := glDer θ V) (p := growthSize V N) (d := 1) (l := [(τ, a)]) (by simp) φ
      simpa [wordAct, growthSob] using h0
    have h2 : growthSize V N (glDer θ V (τ, a) φ) ≤ ENNReal.ofReal S := by
      rw [hS, ENNReal.ofReal_toReal hf]
      exact h1
    exact (growthSize_le_iff hS0).1 h2
  have hder : ∀ h, ‖Rder θ V τ X φ h‖ ≤ s * S * height V h ^ N := by
    intro h
    rw [Rder_eq_sum_glDer hθ hs hX, Finset.sum_apply]
    calc ‖∑ a : Fin V.rank × Fin V.rank, (X a.1 a.2 • glDer θ V (τ, a) φ) h‖
        ≤ ∑ a : Fin V.rank × Fin V.rank, ‖(X a.1 a.2 • glDer θ V (τ, a) φ) h‖ := norm_sum_le _ _
      _ ≤ ∑ a : Fin V.rank × Fin V.rank, ‖X a.1 a.2‖ * (S * height V h ^ N) := by
          refine Finset.sum_le_sum fun a _ => ?_
          rw [Pi.smul_apply, norm_smul]
          exact mul_le_mul_of_nonneg_left (hglob a h) (norm_nonneg _)
      _ = s * S * height V h ^ N := by rw [← Finset.sum_mul, mul_assoc]
  have hC : 0 ≤ s * S * 2 ^ N := by positivity
  rw [growthSize_le_iff hC]
  intro g
  have hl := height_laws (V := V)
  have hφd : ∀ t, HasDerivAt (fun r : ℝ => φ (g * oneP θ V τ X r)) (Rder θ V τ X φ (g * oneP θ V τ X t)) t :=
    fun t => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun g' => GlobalTheory.Mem.Lift.hasDerivAt_Rder hs hX g') g t
  have hb : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖Rder θ V τ X φ (g * oneP θ V τ X t)‖ ≤ s * S * 2 ^ N * height V g ^ N := by
    intro t ht
    have hk : height V (oneP θ V τ X t) ≤ 2 := hh t (Set.Ico_subset_Icc_self ht)
    have hgk : height V (g * oneP θ V τ X t) ≤ height V g * 2 :=
      (hl.2.2.2.1 g _).trans (mul_le_mul_of_nonneg_left hk (zero_le_one.trans (hl.1 g)))
    have hpow : height V (g * oneP θ V τ X t) ^ N ≤ (height V g * 2) ^ N :=
      pow_le_pow_left₀ (zero_le_one.trans (hl.1 _)) hgk N
    calc ‖Rder θ V τ X φ (g * oneP θ V τ X t)‖ ≤ s * S * height V (g * oneP θ V τ X t) ^ N := hder _
      _ ≤ s * S * (height V g * 2) ^ N := mul_le_mul_of_nonneg_left hpow (mul_nonneg hs0 hS0)
      _ = s * S * 2 ^ N * height V g ^ N := by rw [mul_pow]; ring
  have key := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun r : ℝ => φ (g * oneP θ V τ X r))
    (a := 0) (b := 1) (fun t _ => (hφd t).hasDerivWithinAt) hb 1 (by simp)
  simp only [sub_zero, mul_one] at key
  rw [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one] at key
  exact key

theorem tendsto_growthSize_translate : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (N : ℕ), ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V 1 N φ ≠ ⊤ → Filter.Tendsto (fun u : Matrix (Fin V.rank) (Fin V.rank) ℂ => GlobalTheory.Size.growthSize V N (rTr V (atTau θ V τ u) φ - φ)) (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (nhds 0) := by
  intro D θ hθ V τ N φ hs hf
  obtain ⟨Λ, hΛmem, hΛ0, hΛexp⟩ := exists_log V τ
  have hH := exists_height_le hθ V τ
  have h1 : Filter.Tendsto Λ (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0) := hΛ0.mono_left nhdsWithin_le_nhds
  have h2 : Filter.Tendsto (fun u => ∑ a : Fin V.rank × Fin V.rank, ‖Λ u a.1 a.2‖)
      (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0) := by
    have h3 : ∀ a : Fin V.rank × Fin V.rank, Filter.Tendsto (fun u => ‖Λ u a.1 a.2‖)
        (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0) := by
      intro a
      have hce : Continuous fun M : Matrix (Fin V.rank) (Fin V.rank) ℂ => M a.1 a.2 := by
        fun_prop
      have h5 : Filter.Tendsto (fun u => Λ u a.1 a.2) (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ)))
          (𝓝 ((0 : Matrix (Fin V.rank) (Fin V.rank) ℂ) a.1 a.2)) :=
        (hce.tendsto _).comp h1
      simpa using h5.norm
    have h4 := tendsto_finsetSum (Finset.univ : Finset (Fin V.rank × Fin V.rank)) fun a _ => h3 a
    simpa using h4
  have hc : Filter.Tendsto (fun u => ENNReal.ofReal ((∑ a : Fin V.rank × Fin V.rank, ‖Λ u a.1 a.2‖) *
      (growthSob θ V 1 N φ).toReal * 2 ^ N)) (nhdsWithin 1 (Formalism.QuantumDeterminants.UH (gramAt D V τ))) (𝓝 0) := by
    have h4 := ENNReal.tendsto_ofReal ((h2.mul_const ((growthSob θ V 1 N φ).toReal)).mul_const ((2 : ℝ) ^ N))
    simpa using h4
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc
    (Filter.Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [hΛexp, h1.eventually hH] with u hu hhu
  have hk : atTau θ V τ u = oneP θ V τ (Λ u) 1 := by
    show atTau θ V τ u = atTau θ V τ (NormedSpace.exp ((1 : ℝ) • Λ u))
    rw [one_smul, hu]
  rw [hk]
  exact growthSize_sub_le hθ hs hf (hΛmem u) (hhu (hΛmem u))

end GlobalTheory.Size.NearOne

end
end

section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.Grow GlobalTheory.Mem.AutSpace GlobalTheory.Mem.RealTranslate GlobalTheory.Size
open scoped ENNReal NNReal

namespace GlobalTheory.Size.Translate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem wordSum_succ {ι X : Type} [Fintype ι] (A : ι → X → X) (p : X → ℝ≥0∞) (d : ℕ) (x : X) :
    wordSum A p (d + 1) x = p x + ∑ i, wordSum A p d (A i x) := by
  classical
  unfold wordSum
  rw [Finset.sum_range_succ', add_comm]
  congr 1
  · simp [wordAct_nil]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Fintype.sum_prod_type']
    symm
    refine Fintype.sum_equiv (Fin.snocEquiv fun _ => ι) _ _ fun q => ?_
    change _ = p (wordAct A (List.ofFn (fun i => (Fin.snoc (α := fun _ => ι) q.2 q.1 i : ι))) x)
    rw [List.ofFn_succ']
    simp [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, wordAct_append, wordAct_cons, wordAct_nil]

variable {D : D7} {θ : InfFam D} {V : HSp D}

theorem growthSob_sum_le {α : Type} (s : Finset α) (f : α → GA D V → ℂ) (hf : ∀ a, f a ∈ SmFun θ V) (d N : ℕ) :
    growthSob θ V d N (∑ a ∈ s, f a) ≤ ∑ a ∈ s, growthSob θ V d N (f a) := by
  classical
  induction s using Finset.induction_on
  · simpa using growthSob_smul (θ := θ) (φ := (0 : GA D V → ℂ)) (0 : ℂ) d N
  · rename_i a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (growthSob_add_le (hf a) (Submodule.sum_mem _ fun b _ => hf b) d N).trans (add_le_add le_rfl ih)

theorem growthSob_RderC_le (hθ : IsInfFam θ) {φ : GA D V → ℂ} (hs : φ ∈ SmFun θ V) (τ : D.what₂.Tau)
    {Z : Matrix (Fin V.rank) (Fin V.rank) ℂ} {B : ℝ≥0∞} (hB : ∀ a b, ‖Z a b‖ₑ ≤ B) (d N : ℕ) :
    growthSob θ V d N (RderC θ V τ Z φ) ≤
      (Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0∞) * (B * growthSob θ V (d + 1) N φ) := by
  rw [RderC_eq_sum_glDer hθ hs τ Z]
  have hmem : ∀ a : Fin V.rank × Fin V.rank, Z a.1 a.2 • glDer θ V (τ, a) φ ∈ SmFun θ V := fun a =>
    (SmFun θ V).smul_mem _ ((linOnSm_RderC (θ := θ) τ (Matrix.single a.1 a.2 1)).mem φ hs)
  refine (growthSob_sum_le Finset.univ _ hmem d N).trans ?_
  calc ∑ a : Fin V.rank × Fin V.rank, growthSob θ V d N (Z a.1 a.2 • glDer θ V (τ, a) φ)
      ≤ ∑ _a : Fin V.rank × Fin V.rank, B * growthSob θ V (d + 1) N φ := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [growthSob_smul]
        exact mul_le_mul' (hB a.1 a.2)
          (wordSum_letter_le (A := glDer θ V) (p := growthSize V N) d (τ, a) φ)
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem growthSize_rTr_le (h : GA D V) (N : ℕ) (φ : GA D V → ℂ) :
    growthSize V N (rTr V h φ) ≤ ENNReal.ofReal (height V h) ^ N * growthSize V N φ := by
  obtain ⟨h1, -, -, hmul, -⟩ := height_laws V
  unfold growthSize
  refine iSup_le fun g => ?_
  have hgpos : 0 < height V g := lt_of_lt_of_le one_pos (h1 g)
  have hhpos : 0 < height V h := lt_of_lt_of_le one_pos (h1 h)
  have hghpos : 0 < height V (g * h) := lt_of_lt_of_le one_pos (h1 (g * h))
  have hq : 0 ≤ ‖φ (g * h)‖ / height V (g * h) ^ N := div_nonneg (norm_nonneg _) (pow_pos hghpos N).le
  have key : ‖rTr V h φ g‖ / height V g ^ N ≤ height V h ^ N * (‖φ (g * h)‖ / height V (g * h) ^ N) := by
    change ‖φ (g * h)‖ / height V g ^ N ≤ _
    rw [div_le_iff₀ (pow_pos hgpos N)]
    have hp : height V (g * h) ^ N ≤ (height V g * height V h) ^ N := pow_le_pow_left₀ hghpos.le (hmul g h) N
    calc ‖φ (g * h)‖ = ‖φ (g * h)‖ / height V (g * h) ^ N * height V (g * h) ^ N :=
          (div_mul_cancel₀ _ (pow_pos hghpos N).ne').symm
      _ ≤ ‖φ (g * h)‖ / height V (g * h) ^ N * (height V g * height V h) ^ N := mul_le_mul_of_nonneg_left hp hq
      _ = height V h ^ N * (‖φ (g * h)‖ / height V (g * h) ^ N) * height V g ^ N := by ring
  calc ENNReal.ofReal (‖rTr V h φ g‖ / height V g ^ N)
      ≤ ENNReal.ofReal (height V h ^ N * (‖φ (g * h)‖ / height V (g * h) ^ N)) := ENNReal.ofReal_le_ofReal key
    _ = ENNReal.ofReal (height V h) ^ N * ENNReal.ofReal (‖φ (g * h)‖ / height V (g * h) ^ N) := by
        rw [ENNReal.ofReal_mul (pow_pos hhpos N).le, ENNReal.ofReal_pow hhpos.le]
    _ ≤ ENNReal.ofReal (height V h) ^ N * ⨆ g', ENNReal.ofReal (‖φ g'‖ / height V g' ^ N) :=
        by gcongr; exact le_iSup (fun g' => ENNReal.ofReal (‖φ g'‖ / height V g' ^ N)) (g * h)

theorem exists_adAt_le (hθ : IsInfFam θ) (V : HSp D) : ∃ C : ℝ≥0, ∀ (h : GA D V) τ a b c d,
    ‖adAt θ h τ (Matrix.single a b 1) c d‖ₑ ≤ C * ENNReal.ofReal (height V h) ^ 2 := by
  obtain ⟨C, hC⟩ := normInf_le_height V hθ
  refine ⟨Real.toNNReal (C ^ 2), fun h τ a b c d => ?_⟩
  have hent : ∀ i j, ‖infMat D.sp.cm.sig V.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j‖ ≤
      C * height V h := by
    intro i j
    refine le_trans ?_ (hC h)
    calc ‖infMat D.sp.cm.sig V.gram (θ τ) h i j‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j‖
        ≤ ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ) h i j'‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j'‖) :=
          Finset.single_le_sum (f := fun j' => ‖infMat D.sp.cm.sig V.gram (θ τ) h i j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i j'‖) (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ) h i' j'‖ + ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i' j'‖) :=
          Finset.single_le_sum (f := fun i' => ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ) h i' j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ i' j'‖)) (fun _ _ => by positivity) (Finset.mem_univ i)
      _ ≤ ∑ τ', ∑ i', ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ') h i' j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ') h⁻¹ i' j'‖) :=
          Finset.single_le_sum (f := fun τ' => ∑ i', ∑ j', (‖infMat D.sp.cm.sig V.gram (θ τ') h i' j'‖ +
            ‖infMat D.sp.cm.sig V.gram (θ τ') h⁻¹ i' j'‖)) (fun _ _ => by positivity) (Finset.mem_univ τ)
      _ = _ := rfl
  have hcomp : adAt θ h τ (Matrix.single a b 1) c d =
      infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a * infMat D.sp.cm.sig V.gram (θ τ) h b d := by
    simp [adAt, Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have hx := hent c a
  have hy := hent b d
  have hx' : ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a‖ ≤ C * height V h := by
    linarith [norm_nonneg (infMat D.sp.cm.sig V.gram (θ τ) h c a)]
  have hy' : ‖infMat D.sp.cm.sig V.gram (θ τ) h b d‖ ≤ C * height V h := by
    linarith [norm_nonneg (infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ b d)]
  have hht : 0 ≤ height V h := le_trans zero_le_one ((height_laws V).1 h)
  have hreal : ‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a‖ * ‖infMat D.sp.cm.sig V.gram (θ τ) h b d‖ ≤
      C ^ 2 * height V h ^ 2 := by
    calc _ ≤ (C * height V h) * (C * height V h) :=
          mul_le_mul hx' hy' (norm_nonneg _) ((norm_nonneg _).trans hx')
      _ = C ^ 2 * height V h ^ 2 := by ring
  rw [hcomp, ← ofReal_norm_eq_enorm, norm_mul]
  calc ENNReal.ofReal (‖infMat D.sp.cm.sig V.gram (θ τ) h⁻¹ c a‖ * ‖infMat D.sp.cm.sig V.gram (θ τ) h b d‖)
      ≤ ENNReal.ofReal (C ^ 2 * height V h ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := by rw [ENNReal.ofReal_mul (sq_nonneg C), ENNReal.ofReal_pow hht]; rfl

private theorem rderC_rTr' (hθ : IsInfFam θ) (h : GA D V) {φ : GA D V → ℂ} (hs : φ ∈ SmFun θ V)
    (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    RderC θ V τ Z (rTr V h φ) = rTr V h (RderC θ V τ (adAt θ h τ Z) φ) := by
  obtain ⟨hX, hY⟩ := GlobalTheory.SmoothAutCheck.parts_mem V τ Z
  have hZ := (GlobalTheory.SmoothAutCheck.parts_sum V τ Z).symm
  set X := (1 / 2 : ℂ) • (Z + conjAt V τ Z) with hXdef
  set Y := (1 / (2 * Complex.I)) • (Z - conjAt V τ Z) with hYdef
  have hsum : adAt θ h τ Z = adAt θ h τ X + Complex.I • adAt θ h τ Y := by
    conv_lhs => rw [hZ]
    simp only [adAt, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [hsum, RderC_add hθ hs, RderC_smul hθ hs,
    GlobalTheory.SmoothAutCheck.RderC_eq θ V τ (adAt_mem_lieAt hθ h hX),
    GlobalTheory.SmoothAutCheck.RderC_eq θ V τ (adAt_mem_lieAt hθ h hY)]
  change Rder θ V τ X (rTr V h φ) + Complex.I • Rder θ V τ Y (rTr V h φ) = _
  rw [Rder_rTr_adelic hθ h hX, Rder_rTr_adelic hθ h hY]
  rfl

theorem exists_growthSob_rTr_le (hθ : IsInfFam θ) (V : HSp D) (N d : ℕ) : ∃ C : ℝ≥0, ∀ h ∈ GinfC V, ∀ φ ∈ SmFun θ V,
    growthSob θ V d N (rTr V h φ) ≤ C * ENNReal.ofReal (height V h) ^ (N + 2 * d) * growthSob θ V d N φ := by
  obtain ⟨C₁, hC₁⟩ := exists_adAt_le hθ V
  induction d with
  | zero =>
    refine ⟨1, fun h _ φ _ => ?_⟩
    simpa [growthSob, wordSum_zero] using growthSize_rTr_le h N φ
  | succ d ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨1 + (Fintype.card (D.what₂.Tau × Fin V.rank × Fin V.rank) : ℝ≥0) * C *
      (Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0) * C₁, fun h hh φ hs => ?_⟩
    have hT : 1 ≤ ENNReal.ofReal (height V h) := by
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal ((height_laws V).1 h)
    have hS0 : growthSize V N φ ≤ growthSob θ V (d + 1) N φ :=
      le_wordSum (A := glDer θ V) (p := growthSize V N) (l := []) (Nat.zero_le _) φ
    have hterm : ∀ a : D.what₂.Tau × Fin V.rank × Fin V.rank,
        growthSob θ V d N (glDer θ V a (rTr V h φ)) ≤
          C * ENNReal.ofReal (height V h) ^ (N + 2 * d) *
            ((Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0∞) *
              ((C₁ * ENNReal.ofReal (height V h) ^ 2) * growthSob θ V (d + 1) N φ)) := by
      intro a
      have e : glDer θ V a (rTr V h φ) =
          rTr V h (RderC θ V a.1 (adAt θ h a.1 (Matrix.single a.2.1 a.2.2 1)) φ) :=
        rderC_rTr' hθ h hs a.1 _
      rw [e]
      refine (hC h hh _ ((linOnSm_RderC (θ := θ) a.1 _).mem φ hs)).trans ?_
      gcongr
      exact growthSob_RderC_le hθ hs a.1 (fun b c => hC₁ h a.1 a.2.1 a.2.2 b c) d N
    have hpow : ENNReal.ofReal (height V h) ^ N ≤ ENNReal.ofReal (height V h) ^ (N + 2 * (d + 1)) :=
      pow_le_pow_right₀ hT (by omega)
    have e0 : growthSob θ V (d + 1) N (rTr V h φ) =
        growthSize V N (rTr V h φ) + ∑ a, growthSob θ V d N (glDer θ V a (rTr V h φ)) :=
      wordSum_succ _ _ _ _
    rw [e0]
    calc growthSize V N (rTr V h φ) + ∑ a, growthSob θ V d N (glDer θ V a (rTr V h φ))
        ≤ ENNReal.ofReal (height V h) ^ (N + 2 * (d + 1)) * growthSob θ V (d + 1) N φ +
          ∑ _a : D.what₂.Tau × Fin V.rank × Fin V.rank, C * ENNReal.ofReal (height V h) ^ (N + 2 * d) *
            ((Fintype.card (Fin V.rank × Fin V.rank) : ℝ≥0∞) *
              ((C₁ * ENNReal.ofReal (height V h) ^ 2) * growthSob θ V (d + 1) N φ)) :=
          add_le_add ((growthSize_rTr_le h N φ).trans (mul_le_mul' hpow hS0))
            (Finset.sum_le_sum fun a _ => hterm a)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          push_cast
          ring

theorem growthSob_rTr_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (d N : ℕ), ∃ (C : NNReal) (m : ℕ),
    ∀ h ∈ GinfC V, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V d N (rTr V h φ) ≤
      (C : ENNReal) * ENNReal.ofReal (GlobalTheory.Grow.height V h ^ m) * GlobalTheory.Size.growthSob θ V d N φ := by
  intro D θ hθ V d N
  obtain ⟨C, hC⟩ := exists_growthSob_rTr_le hθ V N d
  refine ⟨C, N + 2 * d, fun h hh φ hφ => ?_⟩
  rw [ENNReal.ofReal_pow (le_trans zero_le_one ((height_laws V).1 h))]
  exact hC h hh φ hφ

end GlobalTheory.Size.Translate

end
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adjoint_conjugateThetaLift_eq_vectorValuedLift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), (∀ χ ∈ A.X, IsAbsIrrChar χ) → GlobalTheory.LiftRows.SourceLevelLawC R F → GlobalTheory.LiftRows.InnerProductFormulaC R F → GlobalTheory.LiftRows.FockCoefficientC R F → GlobalTheory.LiftRows.FiniteZetaL R F → GlobalTheory.LiftRows.RealLowestKTypeCoeffSquareIntegrable R →
  ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (μ' η' : (AE D)ˣ →* Circle)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (c : CoefA (Vc D i))
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (H : HMod (Bridge.Gf (Vc D i) → c.W)),
  GlobalTheory.LiftRows.IsLiftDataC R F i A.μ0 σ s R.triv μ' η' m ω B f₀ f c io →
  IsMeasDef (Vc D i) (GlobalTheory.AdelicScalar.levV R i A.μ0 R.triv m) (R.νV i A.μ0) (R.fdV i A.μ0) →
  Bridge.IsReps (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y →
  H.Is (Bridge.AdForms (Bridge.ratF (Vc D i)) c.coef.ρ (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.chrOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m))) (Bridge.adInner (Bridge.ratF (Vc D i)) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.grpOf (Vc D i) (R.βV i) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.datV i R.Pg (R.Q A.μ0) R.triv m)) (R.B.L i A.μ0).pres.y) →
  ∀ v : ∀ ρ, lowT (R.MW i σ) ρ, (∀ ρ, ‖((v ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)‖ = 1) →
  ∀ (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))) (th : H.H →ₗ[ℂ] (R.HW i σ).H),
  Lift.IsThetaP (R.νV i A.μ0) (R.fdV i A.μ0) (fun g h φ => thetaKO ω h g φ) (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f) io (LinearMap.range (c.ext ∘ₗ H.e)) thP →
  GlobalTheory.GalLift.IsProjOf R i σ thP th →
  ∀ (y : (R.HW i σ).H) (h : GA D (Vc D i)) (w : c.W),
    inner ℂ (c.ext (H.e (LinearMap.adjoint th y)) h) w =
      (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) * GlobalTheory.AdelicScalar.upLift R i ω (GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.ptAt R i σ B f (io (PiTensorProduct.tprod ℂ v) w)) ((R.HW i σ).e (GlobalTheory.LiftLower.projH R i σ y) fun ρ => v ρ) h := by
  first | exact @GlobalTheory.ConjAdjoint.adjoint_eq_upLift | exact GlobalTheory.ConjAdjoint.adjoint_eq_upLift | (intros; apply GlobalTheory.ConjAdjoint.adjoint_eq_upLift <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realPoint_acts_linearly_on_multiplicity_values_posDef : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → AllPlus M → ∀ k ∈ GinfC V, ∃ φ : Module.End ℂ (MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => M.sm τ) ℂ), ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : GA D V, evAt M (g * k) T = φ (evAt M g T) := by
  first | exact @GlobalTheory.RealAct.real_acts | exact GlobalTheory.RealAct.real_acts | (intros; apply GlobalTheory.RealAct.real_acts <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section

namespace GlobalTheory.RowVacScalar

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

def idemAt (w : Pl D.host.E) : AE D := Classical.epsilon fun e : AE D => Formalism.L2.NTheta.IsIdemAt e w


open Classical in
def detIdl (e : AE D) (V : HSp D) (g : GA D V) : (AE D)ˣ :=
  if he : e * e = e then GlobalTheory.VecInv.detAt e he V g else 1


open Classical in
theorem detIdl_val {e : AE D} (he : e * e = e) (V : HSp D) (g : GA D V) :
    ((detIdl e V g : (AE D)ˣ) : AE D) = e * (Formalism.L2.Theta.mt V g).det + (1 - e) := by
  rw [detIdl, dite_eq_left he]; rfl

def splitScal (G : GridData L sc) (p : Pair T) (w : Pl D.host.E) (g : GA D (G.pS p)) (h : GA D (G.pT p)) : ℂ :=
  ((splitFacO (G.chrS p) (G.chrT p) (detIdl (idemAt w) (G.pS p) g) (detIdl (idemAt w) (G.pT p) h) : Circle) : ℂ)

end GlobalTheory.RowVacScalar
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.realPoints_unitaryCharacter_eq_detPower : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → V.SigOK → ∀ z : GA D V → ℂ, (∀ a ∈ GinfC V, ∀ a' ∈ GinfC V, z (a * a') = z a * z a') → (∀ a ∈ GinfC V, ‖z a‖ = 1) → ContinuousOn z (GinfC V : Set (GA D V)) → ∃ m : D.what₂.Tau → ℤ, ∀ a ∈ GinfC V, z a = detPow θ V m a := by
  first | exact @GlobalTheory.AdSpan.char_eq_detPow | exact GlobalTheory.AdSpan.char_eq_detPow | (intros; apply GlobalTheory.AdSpan.char_eq_detPow <;> assumption)
end
