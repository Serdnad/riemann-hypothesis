module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.AbsoluteL2Bound
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PolynomialNilpotentPath
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.Fub2
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle258
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle041
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle035
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ParabolicSubgroupEquality
import Development.AbelianVarietyTheory.Definitions.Foundations.MeasurePreservingRmulQuotMeas
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle238
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle282
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle139
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle119
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionUnitaryIsotropicFlag
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle288
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle292
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle065
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ObstructionLifting.H1StructureDimLe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle026
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal

@[expose] public section

section

noncomputable section

open Polynomial

namespace GlobalTheory.CompanionTheory.LocFinFilt

open _root_.CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem aeval_mul_of_intertwine (T Y : Module.End ℂ V) (c : ℂ)
    (h : T * Y = Y * (T + algebraMap ℂ _ c)) (f : ℂ[X]) :
    aeval T f * Y = Y * aeval (T + algebraMap ℂ _ c) f := by
  induction f using Polynomial.induction_on with
  | C a =>
    simp only [aeval_C]
    exact (Algebra.commutes a Y)
  | add p q hp hq => simp only [map_add (f := _), add_mul, mul_add, hp, hq]
  | monomial m a ih =>
    have e : ∀ S : Module.End ℂ V, aeval S (C a * X ^ (m + 1)) = aeval S (C a * X ^ m) * S := by
      intro S
      simp only [map_mul, map_pow, aeval_X, pow_succ, mul_assoc]
    rw [e, e, mul_assoc, h, ← mul_assoc, ih, mul_assoc]

theorem actM_intertwine {E : Fin n → Fin n → Module.End ℂ V} (hE : Formalism.REAL.GlRel E)
    {A Y : Matrix (Fin n) (Fin n) ℂ} {c : ℂ} (h : A * Y - Y * A = c • Y) :
    actM E A * actM E Y = actM E Y * (actM E A + algebraMap ℂ _ c) := by
  have hb := GlobalTheory.CompanionTheory.PolyNilGrad.actM_bracket E hE A Y
  have hs : actM E (c • Y) = c • actM E Y :=
    (GlobalTheory.CompanionTheory.PolyNilGrad.actL E).map_smul c Y
  rw [h, hs] at hb
  rw [mul_add, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
  exact sub_eq_iff_eq_add'.mp hb

theorem aeval_shift (T : Module.End ℂ V) (c d : ℂ) (h : c + d = 0) (f : ℂ[X]) :
    aeval (T + algebraMap ℂ _ c) (f.comp (X + C d)) = aeval T f := by
  have e : aeval (T + algebraMap ℂ _ c) (X + C d : ℂ[X]) = T := by
    rw [map_add (f := _), aeval_X, aeval_C, add_assoc, ← map_add (f := _), h, map_zero, add_zero]
  rw [aeval_comp, e]

theorem step_down {M : GMod n} {A : Matrix (Fin n) (Fin n) ℂ} (F : Filt M A) (p q : ℂ[X])
    (hnil : ∀ u : M.V, ∃ (m : ℕ) (Y : Fin m → Matrix (Fin n) (Fin n) ℂ) (v : Fin m → M.V),
      (∀ k, Y k ∈ L.nilpC A) ∧ aeval (actM M.E A) p u = ∑ k, actM M.E (Y k) (v k))
    (s : ℝ) (hq : ∀ u : M.V, aeval (actM M.E A) q u ∈ F.N s) (u : M.V) :
    aeval (actM M.E A) (q.comp (X + C 1) * q.comp (X + C 2) * p) u ∈ F.N (s - 1) := by
  set T := actM M.E A with hT
  set g : ℂ[X] := q.comp (X + C 1) * q.comp (X + C 2) with hg
  obtain ⟨m, Y, v, hY, hu⟩ := hnil u
  have key : aeval T (g * p) u = ∑ k, aeval T g (actM M.E (Y k) (v k)) := by

    rw [map_mul, mul_apply_eq_comp, hu, map_sum]
  rw [key]
  refine Submodule.sum_mem _ fun k _ => ?_
  obtain ⟨Y₁, Y₂, hk, h₁, h₂⟩ := hY k
  have hadd : actM M.E (Y k) = actM M.E Y₁ + actM M.E Y₂ := by
    rw [hk]; exact (GlobalTheory.CompanionTheory.PolyNilGrad.actL M.E).map_add Y₁ Y₂
  rw [hadd, LinearMap.add_apply, map_add (f := _)]
  refine Submodule.add_mem _ ?_ ?_
  · have h₁' : A * Y₁ - Y₁ * A = (-1 : ℂ) • Y₁ := by rw [h₁, neg_smul, one_smul]
    have hc := aeval_mul_of_intertwine T (actM M.E Y₁) (-1) (actM_intertwine M.gl h₁') g
    have e : aeval T g (actM M.E Y₁ (v k)) =
        actM M.E Y₁ (aeval T q (aeval (T + algebraMap ℂ _ (-1)) (q.comp (X + C 2)) (v k))) := by
      have := congrArg (fun f : Module.End ℂ M.V => f (v k)) hc
      simp only [mul_apply_eq_comp] at this
      rw [this, hg, map_mul, aeval_shift T (-1) 1 (by norm_num), mul_apply_eq_comp]
    rw [e]
    have := F.shift Y₁ (-1) (by simpa using h₁') s _ (hq (aeval (T + algebraMap ℂ _ (-1)) (q.comp (X + C 2)) (v k)))
    simpa [sub_eq_add_neg] using this
  · have h₂' : A * Y₂ - Y₂ * A = (-2 : ℂ) • Y₂ := by rw [h₂, neg_smul]
    have hc := aeval_mul_of_intertwine T (actM M.E Y₂) (-2) (actM_intertwine M.gl h₂') g
    have e : aeval T g (actM M.E Y₂ (v k)) =
        actM M.E Y₂ (aeval T q (aeval (T + algebraMap ℂ _ (-2)) (q.comp (X + C 1)) (v k))) := by
      have := congrArg (fun f : Module.End ℂ M.V => f (v k)) hc
      simp only [mul_apply_eq_comp] at this
      rw [this, hg, mul_comm, map_mul, aeval_shift T (-2) 2 (by norm_num), mul_apply_eq_comp]
    rw [e]
    have := F.shift Y₂ (-2) (by simpa using h₂') s _ (hq (aeval (T + algebraMap ℂ _ (-2)) (q.comp (X + C 1)) (v k)))
    refine F.mono _ _ ?_ this
    push_cast
    linarith

theorem exists_monic_descend {M : GMod n} {A : Matrix (Fin n) (Fin n) ℂ} (F : Filt M A) (p : ℂ[X])
    (hp : p.Monic)
    (hnil : ∀ u : M.V, ∃ (m : ℕ) (Y : Fin m → Matrix (Fin n) (Fin n) ℂ) (v : Fin m → M.V),
      (∀ k, Y k ∈ L.nilpC A) ∧ aeval (actM M.E A) p u = ∑ k, actM M.E (Y k) (v k))
    (s : ℝ) (hs : F.N s = ⊤) (K : ℕ) :
    ∃ q : ℂ[X], q.Monic ∧ ∀ u : M.V, aeval (actM M.E A) q u ∈ F.N (s - K) := by
  induction K with
  | zero => exact ⟨1, monic_one, fun u => by simp [hs]⟩
  | succ K ih =>
    obtain ⟨q, hq, hu⟩ := ih
    refine ⟨q.comp (X + C 1) * q.comp (X + C 2) * p,
      (hq.comp_X_add_C 1 |>.mul (hq.comp_X_add_C 2)).mul hp, fun u => ?_⟩
    have := step_down F p q hnil _ hu u
    have e : s - ((K + 1 : ℕ) : ℝ) = s - K - 1 := by push_cast; ring
    rwa [e]

theorem locFin : LocFin := by
  intro n ε M A F χ hA hχ t
  obtain ⟨p, hp, hnil⟩ := GlobalTheory.CompanionTheory.PolyNilGrad.polyNilPath n ε M χ A hχ hA
  obtain ⟨s, hs⟩ := F.top
  obtain ⟨K, hK⟩ := exists_nat_ge (s - t)
  obtain ⟨q, hq, hu⟩ := exists_monic_descend F p hp hnil s hs K
  exact ⟨q, hq, fun u => F.mono _ _ (by linarith) (hu u)⟩

end GlobalTheory.CompanionTheory.LocFinFilt
end
end

section

theorem _root_.GlobalTheory.T.PolynomialNilpotentPath : CompanionTheory.RgExh.Dec.L.PolyNilPath :=
  GlobalTheory.CompanionTheory.PolyNilGrad.polyNilPath
end

section

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.FubNM

open _root_.CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S ReciprocityTheory.ChartRestriction.DS GlobalTheory.FlagMeas Formalism.MainNotions.S

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem lintegral_prodMul_eq (M : Set G) (μM μN : Measure G) [SFinite μM] [SFinite μN] (hM : μM Mᶜ = 0)
    (δ : G → ℝ≥0∞) (hmod : ∀ m ∈ M, μN.map (fun u => m * u * m⁻¹) = δ m • μN)
    (C : Set G) (hCm : MeasurableSet C) (hC0 : μN C ≠ 0) (hC1 : μN C ≠ ⊤)
    (F : G → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂(GlobalTheory.ParabModulus.prodMul μM μN) = ∫⁻ u, ∫⁻ m, δ m * F (u * m) ∂μM ∂μN := by
  have aM : ∀ᵐ m ∂μM, m ∈ M := mem_ae_iff.2 hM
  have cm : ∀ m : G, Measurable fun u : G => m * u * m⁻¹ := fun m => (measurable_const_mul m).mul_const _
  set δ' : G → ℝ≥0∞ := fun m => μN ((fun u => m * u * m⁻¹) ⁻¹' C) / μN C with hδ'
  have hm' : Measurable δ' := by
    refine Measurable.div_const ?_ _
    exact measurable_measure_prodMk_left (s := (fun z : G × G => z.1 * z.2 * z.1⁻¹) ⁻¹' C)
      ((measurable_mul.mul measurable_fst.inv) hCm)
  have he : ∀ m ∈ M, δ' m = δ m := by
    intro m hm
    simp only [hδ']
    rw [← Measure.map_apply (cm m) hCm, hmod m hm, Measure.smul_apply, smul_eq_mul, mul_div_assoc,
      ENNReal.div_self hC0 hC1, mul_one]
  have hFm : Measurable fun z : G × G => δ' z.1 * F (z.2 * z.1) :=
    (hm'.comp measurable_fst).mul (hF.comp (measurable_snd.mul measurable_fst))
  rw [GlobalTheory.ParabModulus.lintegral_prodMul _ _ _ hF]
  have step : ∀ᵐ m ∂μM, ∫⁻ u, F (m * u) ∂μN = ∫⁻ u, δ' m * F (u * m) ∂μN := by
    filter_upwards [aM] with m hm
    have h := lintegral_map (μ := μN) (hF.comp (measurable_mul_const m)) (cm m)
    rw [hmod m hm, lintegral_smul_measure, smul_eq_mul] at h
    have h2 : ∫⁻ u, δ' m * F (u * m) ∂μN = δ' m * ∫⁻ u, F (u * m) ∂μN :=
      lintegral_const_mul _ (hF.comp (measurable_mul_const m))
    rw [h2, he m hm]
    simp only [Function.comp_apply, inv_mul_cancel_right] at h
    exact h.symm
  rw [lintegral_congr_ae step,
    lintegral_lintegral_swap (f := fun m u => δ' m * F (u * m)) hFm.aemeasurable]
  refine lintegral_congr fun u => lintegral_congr_ae ?_
  filter_upwards [aM] with m hm
  rw [he m hm]

end General

variable {n : ℕ} {ε : Fin n → Bool}

theorem muPar_facts (A : Matrix (Fin n) (Fin n) ℂ) (ν : Measure (PSub ε A)) [ν.IsHaarMeasure] :
    SigmaFinite (muPar ε A ν) ∧ muPar ε A ν (PSub ε A : Set (S7.UJ ε))ᶜ = 0 ∧
      (∀ s ∈ PSub ε A, (muPar ε A ν).map (fun g => s * g) = muPar ε A ν) ∧ muPar ε A ν ≠ 0 := by
  have hcl := GlobalTheory.CompanionTheory.ParabolicHaar.isClosed_pSub ε A
  have hv : Measurable (Subtype.val : PSub ε A → S7.UJ ε) := measurable_subtype_coe
  have hσ : SigmaFinite (muPar ε A ν) :=
    (MeasurableEmbedding.subtype_coe hcl.measurableSet).sigmaFinite_map (μ := ν)
  refine ⟨hσ, ?_, ?_, ?_⟩
  · rw [muPar, Measure.map_apply hv hcl.measurableSet.compl]
    have : (Subtype.val : PSub ε A → S7.UJ ε) ⁻¹' (PSub ε A : Set (S7.UJ ε))ᶜ = ∅ := by
      ext x
      simp
    rw [this, measure_empty]
  · intro s hs
    have e : (fun g : S7.UJ ε => s * g) ∘ (Subtype.val : PSub ε A → S7.UJ ε) =
        Subtype.val ∘ (fun g : PSub ε A => (⟨s, hs⟩ : PSub ε A) * g) := rfl
    rw [muPar, Measure.map_map (measurable_const_mul s) hv, e,
      ← Measure.map_map hv (measurable_const_mul _), map_mul_left_eq_self]
  · exact (Measure.map_ne_zero_iff (μ := ν) hv.aemeasurable).2
      (fun h => isOpen_univ.measure_ne_zero ν Set.univ_nonempty (by simp [h]))

theorem fub2 : Fub2 := by
  intro n ε A hA
  have hW : IsIsoFlag ε (fun _ : Fin 1 => rk A) (W A) := GlobalTheory.CompanionTheory.PSubFlag.isoFlag hA
  have hj : ∀ i : Fin 1, 1 ≤ (fun _ : Fin 1 => rk A) i := fun _ => (GlobalTheory.CompanionTheory.GradFlag.flagFacts n ε A hA).1
  obtain ⟨⟨μN, sN, hN⟩, ⟨μM, sM, hM⟩, μK, hK0, hK1, hKi⟩ := GlobalTheory.T.exists_gauge_measures_isotropicFlag_parabolic n ε 1 _ (W A) hj hW
  have hmod := GlobalTheory.T.isotropicFlag_levi_conj_haar_modulus n ε 1 _ (W A) hj hW μN hN
  refine ⟨μN, μM, inferInstance, inferInstance, hM.1, ?_, ?_, ?_⟩
  · intro a ha hc
    have e : μM.map (· * a) = μM.map (a * ·) :=
      Measure.map_congr (Filter.Eventually.mono (mem_ae_iff.2 hM.1 : ∀ᵐ m ∂μM, m ∈ flagM ε (W A)) fun m hm => hc m hm)
    rw [e]
    exact hM.2.1 a ha
  · obtain ⟨κ, k0, k1, hκ⟩ := GlobalTheory.T.iwasawa_integration_formula_up_to_constant n ε _ _ rfl rfl 1 _ hj (W A) hW μN μM μK hN hM hK0 hK1 hKi
    refine ⟨κ, k0, k1, fun F hF hinv => ?_⟩
    rw [hκ F hF]
    congr 1
    refine lintegral_congr fun u => lintegral_congr fun m => ?_
    have aK : ∀ᵐ k ∂μK, k ∈ maxK ε := mem_ae_iff.2 hK0
    have e : ∫⁻ k, F (u * m * k) ∂μK = F (u * m) := by
      rw [lintegral_congr_ae (g := fun _ => F (u * m)) (aK.mono fun k hk => hinv _ k (by
        rw [← SetLike.mem_coe, GlobalTheory.IwasawaShape.coe_KG]; exact hk))]
      simp [lintegral_const, hK1]
    rw [e]
    rfl
  · intro ν hν
    obtain ⟨⟨N, eN⟩, cN, -⟩ := GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps n ε 1 _ (W A) hW
    obtain ⟨⟨M, eM⟩, cM, -, -, hnorm⟩ := GlobalTheory.FlagLeviGroup.levi_compact_subgroups n ε 1 (W A)
    have huniq := (GlobalTheory.RealIwasawa.iwasawa n ε 1 _ (W A) hW).2
    have mN : ∀ v, v ∈ N ↔ v ∈ flagN ε (W A) := fun v => by rw [← SetLike.mem_coe, eN]
    have mM : ∀ v, v ∈ M ↔ v ∈ flagM ε (W A) := fun v => by rw [← SetLike.mem_coe, eM]
    have cN' : IsClosed (N : Set (Formalism.REAL.UJ ε)) := eN ▸ cN
    have cM' : IsClosed (M : Set (Formalism.REAL.UJ ε)) := eM ▸ cM
    have hN' : IsGaugeSub (N : Set (Formalism.REAL.UJ ε)) _ μN := eN ▸ hN
    have hM' : IsGaugeSub (M : Set (Formalism.REAL.UJ ε)) _ μM := eM ▸ hM
    obtain ⟨hN0, iN⟩ := GlobalTheory.IwasawaShape.gauge_ne_zero_finite N _ μN cN' hN'
    obtain ⟨hM0, iM⟩ := GlobalTheory.IwasawaShape.gauge_ne_zero_finite M _ μM cM' hM'
    haveI := iN
    haveI := iM
    let P : Subgroup (Formalism.REAL.UJ ε) := PSub ε A
    have hcl : IsClosed (P : Set (Formalism.REAL.UJ ε)) := GlobalTheory.CompanionTheory.ParabolicHaar.isClosed_pSub ε A
    have hPeq : ∀ g : Formalism.REAL.UJ ε, g ∈ P ↔ ∃ u ∈ flagN ε (W A), ∃ m ∈ flagM ε (W A), g = u * m :=
      GlobalTheory.CompanionTheory.PSubFlag.psubEq n ε A hA
    have hnorm1 : ∀ m ∈ M, ∀ v ∈ N, m * v * m⁻¹ ∈ N := fun m hm v hv =>
      (mN _).2 (hnorm m ((mM m).1 hm) v ((mN v).1 hv))
    have hnorm' : ∀ l ∈ M, ∀ v ∈ N, l⁻¹ * v * l ∈ N := fun l hl v hv => by
      simpa using hnorm1 l⁻¹ (M.inv_mem hl) v hv
    have hMN : ∀ l ∈ M, l ∈ N → l = 1 := fun l hl hlN =>
      huniq l ((mN l).1 hlN) l⁻¹ ((mM _).1 (M.inv_mem hl)) (by
        rw [mul_inv_cancel, ← GlobalTheory.IwasawaShape.coe_KG]; exact (Formalism.REAL.KG ε).one_mem)
    have hMP : ∀ l ∈ M, ∀ v ∈ N, l * v ∈ P := fun l hl v hv =>
      (hPeq _).2 ⟨l * v * l⁻¹, (mN _).1 (hnorm1 l hl v hv), l, (mM l).1 hl, by group⟩
    have hdec : ∀ p ∈ P, ∃ l ∈ M, ∃ v ∈ N, p = l * v := by
      intro p hp
      obtain ⟨u, hu, m, hm, rfl⟩ := (hPeq p).1 hp
      exact ⟨m, (mM m).2 hm, m⁻¹ * u * m, hnorm' m ((mM m).2 hm) u ((mN u).2 hu), by group⟩
    obtain ⟨hP0, sf, T, hTm, hT0, hT1⟩ := GlobalTheory.ParabModulus.prodMul_facts M N P cM' cN' hcl.measurableSet hMN hMP hdec
      μM μN hM0 hN0 hM'.1 hN'.1
    haveI := sf
    have lP : ∀ s ∈ P, (GlobalTheory.ParabModulus.prodMul μM μN).map (fun g => s * g) = GlobalTheory.ParabModulus.prodMul μM μN := by
      intro s hs
      obtain ⟨l, hl, v, hv, rfl⟩ := hdec s hs
      have : (fun g => l * v * g) = (fun g => l * g) ∘ (fun g => v * g) := by
        funext g; simp [mul_assoc]
      rw [this, ← Measure.map_map (measurable_const_mul l) (measurable_const_mul v),
        GlobalTheory.ParabModulus.prodMul_left_snd M N hnorm' μM μN hM'.1 hN'.2.1 v hv,
        GlobalTheory.ParabModulus.prodMul_left_fst M μM μN hM'.2.1 l hl]
    have key : ∀ ρ : Measure (Formalism.REAL.UJ ε), SigmaFinite ρ → ρ (P : Set (Formalism.REAL.UJ ε))ᶜ = 0 →
        (∀ s ∈ P, ρ.map (fun g => s * g) = ρ) → ρ ≠ 0 → ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
          ∀ F : Formalism.REAL.UJ ε → ℝ≥0∞, Measurable F →
            ∫⁻ x, F x ∂ρ = c * ∫⁻ u, ∫⁻ m, modA A m * F (u * m) ∂μM ∂μN := by
      intro ρ sρ hρ0 hρi hρne
      haveI := sρ
      obtain ⟨c, hc⟩ := GlobalTheory.ParabModulus.eq_smul_of_left_inv P hcl.measurableSet (ρ)
        (GlobalTheory.ParabModulus.prodMul μM μN) hρ0 hP0 hρi lP T hTm hT0 hT1
      have c0 : c ≠ 0 := by
        rintro rfl
        exact hρne (by rw [hc, zero_smul])
      have c1 : c ≠ ⊤ := by
        rintro rfl
        have hS := iUnion_spanningSets (ρ)
        have hz : ∀ i, GlobalTheory.ParabModulus.prodMul μM μN (T ∩ spanningSets (ρ) i) = 0 := by
          intro i
          by_contra h
          have h1 : ρ (T ∩ spanningSets (ρ) i) = ⊤ := by
            generalize T ∩ spanningSets ρ i = X at h ⊢
            rw [hc, Measure.smul_apply, smul_eq_mul, ENNReal.top_mul h]
          have h2 : ρ (T ∩ spanningSets ρ i) < ⊤ := lt_of_le_of_lt (measure_mono Set.inter_subset_right)
            (measure_spanningSets_lt_top (ρ) i)
          rw [h1] at h2
          exact lt_irrefl _ h2
        refine hT0 (measure_mono_null (t := ⋃ i, T ∩ spanningSets (ρ) i) ?_ (measure_iUnion_null hz))
        rw [← Set.inter_iUnion, hS, Set.inter_univ]
      obtain ⟨i, hi⟩ : ∃ i, μN (compactCovering (Formalism.REAL.UJ ε) i) ≠ 0 := by
        by_contra h
        push Not at h
        exact hN0 (Measure.measure_univ_eq_zero.1 (by
          rw [← iUnion_compactCovering]; exact measure_iUnion_null h))
      have hC := isCompact_compactCovering (Formalism.REAL.UJ ε) i
      refine ⟨c, c0, c1, fun F hF => ?_⟩
      rw [hc, lintegral_smul_measure, smul_eq_mul,
        lintegral_prodMul_eq (flagM ε (W A)) μM μN hM.1 (modA A) hmod _ hC.measurableSet hi hC.measure_lt_top.ne F hF]
    obtain ⟨sρ, hρ0, hρi, hρne⟩ := muPar_facts (ε := ε) A ν
    exact key (muPar ε A ν) sρ hρ0 hρi hρne

end GlobalTheory.CompanionTheory.FubNM
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual CompanionTheory.ObstructionTrivialLocus
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.PointSurjectivity


theorem _root_.GlobalTheory.T.exists_affine_cover_cechLB_fibre_acyclic : ∀ {k : Type} [Field k] {X T Z : Scheme.{0}} (a : X ⟶ Sp k) (b : T ⟶ Sp k) (p : Z ⟶ X)
    (q : Z ⟶ T) (H : IsPullback p q a b) [IsSeparated a] [Flat a] (G : LB Z) (hG : G.IsLB)
    (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ T) (Y : Scheme.{0})
    (π : Y ⟶ Z) (f : Y ⟶ Spec (CommRingCat.of R)) (Hy : IsPullback π f q t)
    {κ : Type} [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (hD : ∀ i, IsAffineOpen (D i)) (hc : ⨆ i, D i = ⊤)
    (hac : (cechLB f (G.pull π) D).Acyclic)
    (s : Sp k ⟶ Spec (CommRingCat.of R)) (σ : X ⟶ Z) (hs : s ≫ t ≫ b = 𝟙 _) (h₁ : σ ≫ p = 𝟙 X)
    (h₂ : σ ≫ q = a ≫ s ≫ t), ∃ D' : κ → X.Opens, (∀ i, IsAffineOpen (D' i)) ∧ ⨆ i, D' i = ⊤ ∧ (cechLB a (G.pull σ) D').Acyclic := by
  first | exact @GlobalTheory.CompanionTheory.PointSurjFibre.cech_fibre_acyclic | exact GlobalTheory.CompanionTheory.PointSurjFibre.cech_fibre_acyclic | (intros; apply GlobalTheory.CompanionTheory.PointSurjFibre.cech_fibre_acyclic <;> assumption)
end
