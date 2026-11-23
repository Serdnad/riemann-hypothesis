module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle001
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle002
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Etale.Weakly
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

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal

private theorem tri {E : Type} [Field E] [NumberField E] (g h : Matrix.SpecialLinearGroup (Fin 2) E) (t : Eˣ)
    (hrow : g.1 1 = (t : E) • h.1 1) :
    ∃ β : A E, ratS E g = nU β * mD (IdeleGroup.diagonal E t⁻¹) * ratS E h := by
  obtain ⟨k, hk⟩ : ∃ k, k = g * h⁻¹ := ⟨_, rfl⟩
  have hdet : h.1 0 0 * h.1 1 1 - h.1 0 1 * h.1 1 0 = 1 := by
    have hd := h.det_coe
    rwa [Matrix.det_fin_two] at hd
  have hg0 : g.1 1 0 = t * h.1 1 0 := by simpa using congrFun hrow 0
  have hg1 : g.1 1 1 = t * h.1 1 1 := by simpa using congrFun hrow 1
  have e0 : k.1 1 0 = 0 := by
    rw [hk]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp [hg0, hg1]
    ring
  have e1 : k.1 1 1 = t := by
    rw [hk]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp [hg0, hg1]
    linear_combination (t : E) * hdet
  have e2 : k.1 0 0 = ((t⁻¹ : Eˣ) : E) := by
    have hd := k.det_coe
    rw [Matrix.det_fin_two, e0, e1] at hd
    have ht : (t : E) ≠ 0 := t.ne_zero
    simp only [Units.val_inv_eq_inv_val]
    field_simp
    linear_combination hd
  have d2 : (((IdeleGroup.diagonal E t⁻¹)⁻¹ : (A E)ˣ) : A E) = UpperTheory.ConvolutionTheory.R2.rt (t : E) := by
    rw [← map_inv, inv_inv]
    rfl
  have d3 : (((IdeleGroup.diagonal E t)⁻¹ : (A E)ˣ) : A E) = algebraMap E (A E) (t : E)⁻¹ := by
    rw [← map_inv]
    exact congrArg (algebraMap E (A E)) (Units.val_inv_eq_inv_val t)
  refine ⟨UpperTheory.ConvolutionTheory.R2.rt (k.1 0 1 * ((t⁻¹ : Eˣ) : E)), ?_⟩
  have hkm : ratS E k = nU (UpperTheory.ConvolutionTheory.R2.rt (k.1 0 1 * ((t⁻¹ : Eˣ) : E))) * mD (IdeleGroup.diagonal E t⁻¹) := by
    refine Subtype.ext ?_
    rw [M.val_mul, M.val_ratS]
    ext i j
    fin_cases i <;> fin_cases j
    · simp [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, d3, e2]
    · simp only [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, d2]
      simp [← map_mul]
    · simp [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, e0]
    · simp [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, d2, e1]
  have hgk : g = k * h := by rw [hk, inv_mul_cancel_right]
  calc ratS E g = ratS E (k * h) := by rw [← hgk]
    _ = _ := by rw [map_mul, hkm]

theorem UpperTheory.exists_unipotentInvariant_set_unique_row_scaling :
    TorCo → ∀ (E : Type) [Field E] [NumberField E], ∃ T : Set (G1 E), MeasurableSet T ∧ (∀ b x, nU b * x ∈ T ↔ x ∈ T) ∧ ∀ σ : {r : Fin 2 → E // r ≠ 0} → Matrix.SpecialLinearGroup (Fin 2) E, M.RowSec σ → ∀ (x : G1 E) (r : {r : Fin 2 → E // r ≠ 0}), ∃! t : Eˣ, ∃ r' ∈ {r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T}, r'.1 = (t : E) • r.1 := by
  intro hT E _ _
  obtain ⟨α, hm, hu, hd⟩ := hT E
  obtain ⟨Tq, hTq⟩ : ∃ Tq : Subgroup (IdeleGroup E), Tq = (IdeleGroup.diagonal E).range := ⟨_, rfl⟩
  have hmem : ∀ g : Tq, mD g.1 ∈ Gam E := by
    rintro ⟨g, hg⟩
    rw [hTq] at hg
    obtain ⟨t, rfl⟩ := hg
    exact M.mD_diag_mem t
  haveI : DiscreteTopology Tq := by
    refine DiscreteTopology.of_continuous_injective (f := fun g : Tq => (⟨mD g.1, hmem g⟩ : Gam E)) ?_ ?_
    · exact (M.continuous_mD.comp continuous_subtype_val).subtype_mk _
    · intro a b hab
      have h1 : mD a.1 = mD b.1 := congrArg (·.1) hab
      have h2 := congrArg (fun g : G1 E => g.1 0 0) h1
      exact Subtype.ext (Units.ext (by simpa [mD] using h2))
  obtain ⟨F, hF, huniq, -⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup Tq
  have hdiag : Function.Injective (IdeleGroup.diagonal E) := by
    intro a b hab
    have h1 : ((IdeleGroup.diagonal E a : (A E)ˣ) : A E) = ((IdeleGroup.diagonal E b : (A E)ˣ) : A E) := by rw [hab]
    exact Units.ext (AdeleRing.algebraMap_injective (𝓞 E) E h1)
  refine ⟨α ⁻¹' F, hm hF, fun b x => by simp [hu], ?_⟩
  intro σ hσ x r
  have key : ∀ (t : Eˣ) (r' : {r : Fin 2 → E // r ≠ 0}), r'.1 = (t : E) • r.1 →
      α (ratS E (σ r') * x) = IdeleGroup.diagonal E t⁻¹ * α (ratS E (σ r) * x) := by
    intro t r' hr
    obtain ⟨β, hβ⟩ := tri (σ r') (σ r) t (by rw [hσ r', hσ r, hr])
    rw [hβ, mul_assoc, mul_assoc, hu, hd]
  obtain ⟨⟨g, hg⟩, hgF, hgU⟩ := huniq (α (ratS E (σ r) * x))
  have hg' := hg
  rw [hTq] at hg'
  obtain ⟨s, rfl⟩ := hg'
  have hne : ((s⁻¹ : Eˣ) : E) • r.1 ≠ 0 := by
    intro h0
    exact r.2 ((smul_eq_zero.mp h0).resolve_left (Units.ne_zero _))
  refine ⟨s⁻¹, ⟨⟨_, hne⟩, ?_, rfl⟩, ?_⟩
  · show α (ratS E (σ _) * x) ∈ F
    rw [key s⁻¹ _ rfl, inv_inv]
    exact hgF
  · rintro t ⟨r', hr'T, hr'⟩
    have hin : IdeleGroup.diagonal E t⁻¹ * α (ratS E (σ r) * x) ∈ F := by
      rw [← key t r' hr']
      exact hr'T
    have hmemt : IdeleGroup.diagonal E t⁻¹ ∈ Tq := by
      rw [hTq]
      exact ⟨_, rfl⟩
    have := hgU ⟨_, hmemt⟩ hin
    have h2 : IdeleGroup.diagonal E t⁻¹ = IdeleGroup.diagonal E s := congrArg Subtype.val this
    rw [← inv_inv t, hdiag h2]
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private noncomputable def Nq (E : Type) [Field E] [NumberField E] : Subgroup (G1 E) where
  carrier := Set.range fun ξ : E => (nU (rt ξ : A E) : G1 E)
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by simp only [UpperTheory.ConvolutionTheory.R2.rt, map_add (f := _), M.nU_add]⟩
  one_mem' := ⟨0, by simp only [UpperTheory.ConvolutionTheory.R2.rt, map_zero, M.nU_zero]⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, by simp only [UpperTheory.ConvolutionTheory.R2.rt, map_neg, M.nU_neg]⟩

private theorem Nq_le : Nq E ≤ Gam E := by
  rintro _ ⟨ξ, rfl⟩
  exact M.nU_rt_mem ξ

private theorem Nq_disc : DiscreteTopology (Nq E) :=
  DiscreteTopology.of_continuous_injective (f := Subgroup.inclusion Nq_le)
    (continuous_subtype_val.subtype_mk _) (Subgroup.inclusion_injective Nq_le)

private theorem Nq_count : Countable (Nq E) :=
  (Subgroup.inclusion_injective Nq_le).countable

private theorem nU_inj : Function.Injective (fun ξ : E => (nU (rt ξ : A E) : G1 E)) := by
  intro a b h
  have h1 : (nU (rt a : A E) : G1 E) 0 1 = (nU (rt b : A E) : G1 E) 0 1 := by
    rw [show (nU (rt a : A E) : G1 E) = nU (rt b : A E) from h]
  have h2 : (rt a : A E) = rt b := by simpa [nU] using h1
  exact AdeleRing.algebraMap_injective (𝓞 E) E h2

private theorem nU_comm (a b : A E) : nU a * nU b = nU b * nU a := by
  rw [← M.nU_add, ← M.nU_add, add_comm]

private theorem exDN : ∃ S : Set (G1 E), MeasurableSet S ∧ M.NWt (S.indicator 1) ∧
    ∀ μ : Measure (G1 E), IsFundamentalDomain (Nq E) S μ := by
  haveI := Nq_disc (E := E)
  obtain ⟨D, hD, hu, hf⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (Nq E)
  refine ⟨D, hD, ⟨measurable_one.indicator hD, fun g => ?_⟩, hf⟩
  obtain ⟨n, hn, huniq⟩ := hu g
  obtain ⟨ξ₀, hξ₀⟩ := n.2
  have hn' : (nU (rt ξ₀ : A E) : G1 E) * g ∈ D := by
    have : (n : G1 E) * g ∈ D := hn
    rwa [← hξ₀] at this
  rw [tsum_eq_single ξ₀]
  · rw [Set.indicator_of_mem hn']
    rfl
  · intro ξ hξ
    refine Set.indicator_of_notMem (fun hmem => hξ ?_) _
    have h1 : (⟨nU (rt ξ : A E), ⟨ξ, rfl⟩⟩ : Nq E) = n := huniq _ hmem
    have h2 : (nU (rt ξ : A E) : G1 E) = n := congrArg Subtype.val h1
    exact nU_inj (h2.trans hξ₀.symm)

private theorem cosetE (N₀ : MeasE E) (σ) (β u : G1 E → ℝ≥0∞) (hσ : M.RowSec (F := E) σ) (hβ : M.NWt β)
    (hu : Measurable u) (hinv : ∀ (ξ : E) g, u (nU (rt ξ) * g) = u g) :
    ∫⁻ g, u g * β g ∂N₀.μ = ∫⁻ g in N₀.D, ∑' r, u (ratS E (σ r) * g) ∂N₀.μ := by
  have hc := (UpperTheory.ConvolutionTheory.R2.M.rowCosets E).2 σ hσ
  haveI := N₀.haar
  let e : ({r : Fin 2 → E // r ≠ 0} × E) → Gam E := fun p =>
    ⟨nU (rt p.2) * ratS E (σ p.1), (Gam E).mul_mem (M.nU_rt_mem _) ⟨_, rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro p q h
      obtain ⟨p0, _, hp⟩ := hc (e p)
      exact (hp p rfl).trans (hp q (congrArg Subtype.val h)).symm
    · intro γ
      obtain ⟨p, hp, _⟩ := hc γ
      exact ⟨p, Subtype.ext hp.symm⟩
  have key : ∀ g : G1 E, ∑' γ : Gam E, u (γ • g) * β (γ • g) = ∑' r, u (ratS E (σ r) * g) := by
    intro g
    rw [← (Equiv.ofBijective e he).tsum_eq, ENNReal.tsum_prod']
    refine tsum_congr fun r => ?_
    have h1 : ∀ ξ : E, u ((Equiv.ofBijective e he (r, ξ)) • g) * β ((Equiv.ofBijective e he (r, ξ)) • g)
        = u (ratS E (σ r) * g) * β (nU (rt ξ) * (ratS E (σ r) * g)) := by
      intro ξ
      have h2 : (Equiv.ofBijective e he (r, ξ)) • g = nU (rt ξ) * (ratS E (σ r) * g) := by
        change (nU (rt ξ) * ratS E (σ r)) * g = _
        rw [mul_assoc]
      rw [h2, hinv]
    simp_rw [h1]
    rw [ENNReal.tsum_mul_left, hβ.2, mul_one]
  have hmeas : ∀ γ : Gam E, Measurable fun g : G1 E => u (γ • g) * β (γ • g) := fun γ =>
    (hu.mul hβ.1).comp (measurable_const_smul γ)
  rw [N₀.fund.lintegral_eq_tsum'', ← lintegral_tsum fun γ => (hmeas γ).aemeasurable]
  exact lintegral_congr key

private theorem shiftFd (μ : Measure (G1 E)) [μ.IsHaarMeasure] {S : Set (G1 E)}
    (h : IsFundamentalDomain (Nq E) S μ) (b : A E) :
    IsFundamentalDomain (Nq E) ((fun x => nU b * x) '' S) μ := by
  have h1 := h.image_of_equiv (ν := μ) (Equiv.mulLeft (nU b))
    (measurePreserving_mul_left μ (nU b)⁻¹).quasiMeasurePreserving (Equiv.refl _) (by
      rintro ⟨_, ξ, rfl⟩ x
      change nU b * (nU (rt ξ) * x) = nU (rt ξ) * (nU b * x)
      rw [← mul_assoc, ← mul_assoc, nU_comm])
  exact h1

private theorem moveInt (μ : Measure (G1 E)) [μ.IsHaarMeasure] {S : Set (G1 E)}
    (hS : IsFundamentalDomain (Nq E) S μ) (b : A E) (w : G1 E → ℂ)
    (hw : ∀ (ξ : E) g, w (nU (rt ξ) * g) = w g) :
    ∫ x in S, w (nU b * x) ∂μ = ∫ x in S, w x ∂μ := by
  haveI := Nq_count (E := E)
  rw [← (measurePreserving_mul_left μ (nU b)).setIntegral_image_emb
    (MeasurableEquiv.mulLeft (nU b)).measurableEmbedding w S]
  refine (shiftFd μ hS b).setIntegral_eq hS ?_
  rintro ⟨_, ξ, rfl⟩ x
  exact hw ξ x

private theorem moveL (μ : Measure (G1 E)) [μ.IsHaarMeasure] {S : Set (G1 E)}
    (hS : IsFundamentalDomain (Nq E) S μ) (b : A E) (w : G1 E → ℝ≥0∞)
    (hw : ∀ (ξ : E) g, w (nU (rt ξ) * g) = w g) :
    ∫⁻ x in S, w (nU b * x) ∂μ = ∫⁻ x in S, w x ∂μ := by
  haveI := Nq_count (E := E)
  rw [(measurePreserving_mul_left μ (nU b)).setLIntegral_comp_emb
    (MeasurableEquiv.mulLeft (nU b)).measurableEmbedding w S]
  refine (shiftFd μ hS b).setLIntegral_eq hS w ?_
  rintro ⟨_, ξ, rfl⟩ x
  exact hw ξ x

private theorem van (μ : Measure (G1 E)) [μ.IsHaarMeasure] {S : Set (G1 E)}
    (hS : IsFundamentalDomain (Nq E) S μ) (a c : G1 E → ℂ) (ha : Measurable a) (hc : Measurable c)
    (haI : ∀ b x, a (nU b * x) = a x) (hcI : ∀ (ξ : E) x, c (nU (rt ξ) * x) = c x)
    (h0 : ∀ x, ∫ b in fundamentalSet E, c (nU b * x) ∂(adeleMeasure E) = 0)
    (hfin : ∫⁻ x in S, ‖a x * c x‖ₑ ∂μ ≠ ⊤) : ∫ x in S, a x * c x ∂μ = 0 := by
  let f : G1 E → ℂ := fun x => a x * c x
  have hfI : ∀ (ξ : E) g, f (nU (rt ξ) * g) = f g := fun ξ g => by simp only [f, haI, hcI]
  let ρ : Measure (A E) := (adeleMeasure E).restrict (fundamentalSet E)
  haveI : IsProbabilityMeasure ρ := ⟨by simp [ρ, adeleMeasure_fundamentalSet]⟩
  let F : A E → G1 E → ℂ := fun b x => a x * c (nU b * x)
  have hFm : Measurable (Function.uncurry F) := by
    have hg : Measurable fun p : A E × G1 E => nU p.1 * p.2 :=
      ((M.continuous_nU.comp continuous_fst).mul continuous_snd).measurable
    exact (ha.comp measurable_snd).mul (hc.comp hg)
  have hF : ∀ b x, F b x = f (nU b * x) := fun b x => by simp only [F, f, haI]
  have hInt : Integrable (Function.uncurry F) (ρ.prod (μ.restrict S)) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    have h1 : ∫⁻ p, ‖Function.uncurry F p‖ₑ ∂(ρ.prod (μ.restrict S)) = ∫⁻ x in S, ‖f x‖ₑ ∂μ := by
      rw [lintegral_prod _ hFm.enorm.aemeasurable]
      have h2 : ∀ b, ∫⁻ x, ‖Function.uncurry F (b, x)‖ₑ ∂(μ.restrict S) = ∫⁻ x in S, ‖f x‖ₑ ∂μ := fun b => by
        simp only [Function.uncurry, hF]
        exact moveL μ hS b (fun x => ‖f x‖ₑ) (fun ξ g => by simp only [hfI])
      simp only [h2, lintegral_const, measure_univ, mul_one]
    exact lt_top_iff_ne_top.2 (h1 ▸ hfin)
  have hswap := integral_integral_swap hInt
  have hl : ∫ b, ∫ x, F b x ∂(μ.restrict S) ∂ρ = ∫ x in S, f x ∂μ := by
    have h2 : ∀ b, ∫ x, F b x ∂(μ.restrict S) = ∫ x in S, f x ∂μ := fun b => by
      simp only [hF]
      exact moveInt μ hS b f hfI
    simp only [h2, integral_const, probReal_univ, one_smul]
  have hr : ∫ x, ∫ b, F b x ∂ρ ∂(μ.restrict S) = 0 := by
    simp only [F, ρ, integral_const_mul, h0, mul_zero, integral_zero]
  exact hl.symm.trans (hswap.trans hr)

end SlopeTestRemainingChoices

theorem UpperTheory.integral_tsum_rowSection_eq_zero_of_constantTerm_eq_zero :
    ∀ {E : Type} [Field E] [NumberField E] (N : MeasE E) (σ : {r : Fin 2 → E // r ≠ 0} → Matrix.SpecialLinearGroup (Fin 2) E) (A c : G1 E → ℂ), M.RowSec σ → Measurable A → Measurable c → (∀ b x, A (nU b * x) = A x) → (∀ γ x, c (ratS E γ * x) = c x) → (∀ x, ∫ b in fundamentalSet E, c (nU b * x) ∂(adeleMeasure E) = 0) → (∫⁻ x in N.D, ∑' r, ‖A (ratS E (σ r) * x) * c x‖ₑ ∂N.μ) ≠ ⊤ → ∫ x in N.D, ∑' r, A (ratS E (σ r) * x) * c x ∂N.μ = 0 := by
  intro E _ _ N σ A c hσ hA hc hAI hcI hc0 hfin
  haveI : Countable E := Finsupp.Countable.of_moduleFinite (R := ℚ)
  haveI := N.haar
  obtain ⟨S, hSm, hβ, hS⟩ := exDN (E := E)
  have hcN : ∀ (ξ : E) x, c (nU (rt ξ) * x) = c x := fun ξ x => by
    rw [← M.ratS_up ξ]
    exact hcI _ x
  let f : G1 E → ℂ := fun x => A x * c x
  have hf : Measurable f := hA.mul hc
  have hfI : ∀ (ξ : E) g, f (nU (rt ξ) * g) = f g := fun ξ g => by simp only [f, hAI, hcN]
  have hL : ∀ u : G1 E → ℝ≥0∞, Measurable u → (∀ (ξ : E) g, u (nU (rt ξ) * g) = u g) →
      ∫⁻ g in N.D, ∑' r, u (ratS E (σ r) * g) ∂N.μ = ∫⁻ g in S, u g ∂N.μ := by
    intro u hu hi
    rw [← cosetE N σ _ u hσ hβ hu hi, ← lintegral_indicator hSm]
    refine lintegral_congr fun g => ?_
    by_cases hg : g ∈ S <;> simp [hg]
  have hsw : ∀ r x, A (ratS E (σ r) * x) * c x = f (ratS E (σ r) * x) := fun r x => by
    simp only [f, hcI]
  simp only [hsw] at hfin ⊢
  have hfinS : ∫⁻ x in S, ‖f x‖ₑ ∂N.μ ≠ ⊤ := by
    rw [← hL (fun x => ‖f x‖ₑ) hf.enorm (fun ξ g => by simp only [hfI])]
    exact hfin
  let e : {r : Fin 2 → E // r ≠ 0} → G1 E → G1 E := fun r g => ratS E (σ r) * g
  have he : ∀ r, Measurable (e r) := fun r => measurable_const_mul _
  have hSS := M.sumSide (G1 E) {r : Fin 2 → E // r ≠ 0} (N.μ.restrict N.D) e he
  have hT := M.transfer (m := Measure.sum fun i => (N.μ.restrict N.D).map (e i)) (n := N.μ.restrict S) hf hf
    (fun φ hφ => (hSS.1 _ (hφ.comp hf)).trans (hL _ (hφ.comp hf) (fun ξ g => by simp only [Function.comp, hfI])))
  have hI : Integrable f (N.μ.restrict S) := ⟨hf.aestronglyMeasurable, lt_top_iff_ne_top.2 hfinS⟩
  obtain ⟨-, -, h3⟩ := hSS.2 f hf (hT.1.2 hI)
  exact h3.trans (hT.2.trans (van N.μ (hS _) A c hA hc hAI hcN hc0 hfinS))
end
