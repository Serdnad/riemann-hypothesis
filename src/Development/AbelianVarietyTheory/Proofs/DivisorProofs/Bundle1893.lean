module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1838
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1860
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCuspFormTransvectionConstantTermsZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHolomorphicCuspFormOfAdelicConstantTermsZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle038
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1773
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1541
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1626
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle039
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1410
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1839
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SobolevGrowth

theorem lintegral_le_of_count {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G)
    [μ.IsMulLeftInvariant] (Γ : Subgroup G) [Countable Γ] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    {A : Set G} (hA : MeasurableSet A) {h : G → ℝ≥0∞} (hm : Measurable h) (hinv : ∀ γ ∈ Γ, ∀ g, h (γ * g) = h g)
    (M : ℝ) (hM : ∀ y, {γ : G | γ ∈ Γ ∧ γ * y ∈ A}.Finite ∧ (({γ : G | γ ∈ Γ ∧ γ * y ∈ A}.ncard : ℕ) : ℝ) ≤ M) :
    ∫⁻ x in A, h x ∂μ ≤ ENNReal.ofReal M * ∫⁻ x in 𝓕, h x ∂μ := by
  classical
  rw [← lintegral_indicator hA, h𝓕.lintegral_eq_tsum'' (A.indicator h), ← lintegral_tsum, ← lintegral_const_mul _ hm]
  · refine lintegral_mono fun y => ?_
    obtain ⟨hfin, hle⟩ := hM y
    have hfin' : {γ : Γ | (γ : G) * y ∈ A}.Finite := by
      refine Set.Finite.of_finite_image (f := Subtype.val) (hfin.subset ?_) Subtype.val_injective.injOn
      rintro _ ⟨γ, hγ, rfl⟩
      exact ⟨γ.2, hγ⟩
    have hcard : hfin'.toFinset.card = {γ : G | γ ∈ Γ ∧ γ * y ∈ A}.ncard := by
      rw [← Set.ncard_eq_toFinset_card _ hfin', ← Set.ncard_image_of_injective _ Subtype.val_injective]
      congr 1
      ext g
      constructor
      · rintro ⟨γ, hγ, rfl⟩
        exact ⟨γ.2, hγ⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨g, h1⟩, h2, rfl⟩
    rw [tsum_eq_sum (s := hfin'.toFinset)]
    · have : ∀ γ ∈ hfin'.toFinset, A.indicator h (γ • y) = h y := by
        intro γ hγ
        have h1 : (γ : G) * y ∈ A := by simpa using hγ
        change A.indicator h ((γ : G) * y) = h y
        rw [Set.indicator_of_mem h1, hinv _ γ.2]
      rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, hcard]
      gcongr
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hle
    · intro γ hγ
      have h1 : (γ : G) * y ∉ A := by simpa using hγ
      change A.indicator h ((γ : G) * y) = 0
      exact Set.indicator_of_notMem h1 _
  · intro γ
    exact ((hm.indicator hA).comp (measurable_const_mul (γ : G))).aemeasurable

theorem lintegral_enorm_sq {Q : Type} [MeasurableSpace Q] (ν : Measure Q) (F : Lp ℂ 2 ν) :
    ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν = ENNReal.ofReal (‖F‖ ^ 2) := by
  have h := eLpNorm_nnreal_pow_eq_lintegral (f := F) (μ := ν) (p := 2) (by norm_num) (Lp.stronglyMeasurable F).aestronglyMeasurable
  rw [ENNReal.ofReal_pow (norm_nonneg _), Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top F)]
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at h
  exact h.symm

theorem sum_sq_le {α : Type} (S : List α) (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    (S.map fun a => f a ^ 2).sum ≤ (S.map f).sum ^ 2 := by
  induction S with
  | nil => simp
  | cons a S ih =>
    have : 0 ≤ (S.map f).sum := List.sum_nonneg (by simpa using fun a _ => hf a)
    simp only [List.map_cons, List.sum_cons]
    nlinarith [hf a, mul_nonneg (hf a) this]

theorem integral_le_of_count {G Q : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableSpace Q] (μ : Measure G) [μ.IsMulLeftInvariant]
    (Γ : Subgroup G) [Countable Γ] {𝓕 : Set G} (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (π : G → Q) (hmk : Measurable π)
    (hπ : ∀ γ ∈ Γ, ∀ g, π (γ * g) = π g) {Ω : Set G} (hΩ : IsCompact Ω) (z : G) (M : ℝ)
    (hM : ∀ y, {γ : G | γ ∈ Γ ∧ ∃ o ∈ Ω, γ * y = z * o}.Finite ∧
      (({γ : G | γ ∈ Γ ∧ ∃ o ∈ Ω, γ * y = z * o}.ncard : ℕ) : ℝ) ≤ M)
    (F : Lp ℂ 2 ((μ.restrict 𝓕).map π)) (φ : G → ℂ) (hφ : Continuous φ) (hr : ∀ᵐ x ∂μ, F (π x) = φ x) :
    ∫ x in Ω, ‖φ (z * x)‖ ^ 2 ∂μ ≤ M ^ 2 * ‖F‖ ^ 2 := by
  have hFm : Measurable fun x => ‖F x‖ₑ ^ 2 := (Lp.stronglyMeasurable F).measurable.eNorm.pow_const 2
  have hA : IsCompact ((fun o => z * o) '' Ω) := hΩ.image (continuous_const_mul z)
  have key := lintegral_le_of_count μ Γ h𝓕 hA.measurableSet (hFm.comp hmk)
    (fun γ hγ g => by simp only [Function.comp, hπ γ hγ g]) (M ^ 2) (fun y => by
      have e : {γ : G | γ ∈ Γ ∧ γ * y ∈ (fun o => z * o) '' Ω} = {γ : G | γ ∈ Γ ∧ ∃ o ∈ Ω, γ * y = z * o} :=
        Set.ext fun γ => and_congr_right fun _ => exists_congr fun _ => and_congr_right fun _ => eq_comm
      rw [e]
      refine ⟨(hM y).1, ?_⟩
      have h1 := (hM y).2
      generalize Set.ncard _ = n at h1
      have h2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (by norm_num) n
      exact h2.trans (pow_le_pow_left₀ (Nat.cast_nonneg n) h1 2))
  have e1 : ∫⁻ x in 𝓕, ((fun x => ‖F x‖ₑ ^ 2) ∘ π) x ∂μ = ENNReal.ofReal (‖F‖ ^ 2) := by
    rw [← lintegral_enorm_sq]
    exact (lintegral_map hFm hmk).symm
  have e2 : ∫⁻ x in (fun o => z * o) '' Ω, ((fun x => ‖F x‖ₑ ^ 2) ∘ π) x ∂μ =
      ∫⁻ x in Ω, ‖φ (z * x)‖ₑ ^ 2 ∂μ := by
    rw [((measurePreserving_mul_left μ z).setLIntegral_comp_emb (measurableEmbedding_mulLeft z)
      (fun x => ‖φ x‖ₑ ^ 2) Ω)]
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hr] with x hx
    simp only [Function.comp, hx]
  rw [e1, e2, ← ENNReal.ofReal_mul (sq_nonneg _)] at key
  have hc : Continuous fun x => ‖φ (z * x)‖ ^ 2 := (hφ.comp (continuous_const_mul z)).norm.pow 2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _) hc.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) (le_of_eq_of_le ?_ key)
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem le_of_sums {α : Type} (S : List α) (I f : α → ℝ) (a C₁ C₂ n : ℝ) (N : ℕ) (hn : 0 ≤ n)
    (hI : ∀ l, 0 ≤ I l) (hf : ∀ l, 0 ≤ f l) (h1 : a ^ 2 ≤ C₁ * (S.map I).sum)
    (h2 : ∀ l ∈ S, I l ≤ (C₂ * n ^ N) ^ 2 * f l ^ 2) : a ≤ √|C₁| * |C₂| * n ^ N * (S.map f).sum := by
  have h2' : (S.map I).sum ≤ (S.map fun l => (C₂ * n ^ N) ^ 2 * f l ^ 2).sum := List.sum_le_sum h2
  rw [List.sum_map_mul_left] at h2'
  have h3 := sum_sq_le S f hf
  have h0 : 0 ≤ (S.map I).sum := List.sum_nonneg (by simpa using fun a _ => hI a)
  have hT : 0 ≤ (S.map f).sum := List.sum_nonneg (by simpa using fun a _ => hf a)
  refine le_of_sq_le_sq ?_ (by positivity)
  have e : (√|C₁| * |C₂| * n ^ N * (S.map f).sum) ^ 2 = |C₁| * ((C₂ * n ^ N) ^ 2 * (S.map f).sum ^ 2) := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
    ring
  rw [e]
  refine h1.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) h0).trans ?_)
  exact mul_le_mul_of_nonneg_left (h2'.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))) (abs_nonneg _)

variable {D : D7}

theorem integral_le_adelic (V : HSp D) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} (hp : FinPair V μ 𝓕)
    {Ω : Set (GA D V)} (hΩ : IsCompact Ω) (z : GA D V) (M : ℝ)
    (hM : ∀ y, {γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ Ω, γ * y = z * o}.Finite ∧
      (({γ : GA D V | γ ∈ GQ V ∧ ∃ o ∈ Ω, γ * y = z * o}.ncard : ℕ) : ℝ) ≤ M)
    (F : Lp ℂ 2 (nuQ V μ 𝓕)) (φ : GA D V → ℂ) (hφ : Continuous φ) (hr : Repr V μ 𝓕 F φ) :
    ∫ x in Ω, ‖φ (z * x)‖ ^ 2 ∂μ ≤ M ^ 2 * ‖F‖ ^ 2 := by
  obtain ⟨-, -, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have := hp.haar
  exact integral_le_of_count μ (GQ V) hp.fd (autMk V) measurable_quotient_mk''
    (fun γ hγ g => Quotient.sound (QuotientGroup.rightRel_apply.2 (by
      rw [_root_.mul_inv_rev, mul_inv_cancel_left]
      exact (GQ V).inv_mem hγ))) hΩ z M hM F φ hφ hr

theorem level_of_repr (V : HSp D) {μ : Measure (GA D V)} {𝓕 : Set (GA D V)}
    {ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))} (hp : FinPair V μ 𝓕) (hρ : IsReg V μ 𝓕 ρ)
    {F : Lp ℂ 2 (nuQ V μ 𝓕)} {ψ : GA D V → ℂ} (hψ : Continuous ψ) (hr : Repr V μ 𝓕 F ψ) {k : GA D V} (hk : ρ k F = F)
    (g : GA D V) : ψ (g * k) = ψ g := by
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨-, huniq, -, htr, -⟩ := GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ
  have h1 := htr F ψ k hr
  rw [hk] at h1
  exact congrFun (huniq F (rTr V k ψ) ψ (hψ.comp (continuous_mul_const k)) hψ h1 hr) g

theorem normInf_nonneg (θ : InfFam D) (V : HSp D) (g : GA D V) : 0 ≤ normInf θ V g := by
  unfold normInf
  positivity

theorem pointwise_growth : ∀ (D : D7) (θ : InfFam D) (V : HSp D), IsInfFam θ → ∀ (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (ρ : GA D V →* (Lp ℂ 2 (nuQ V μ 𝓕) →L[ℂ] Lp ℂ 2 (nuQ V μ 𝓕))), FinPair V μ 𝓕 → IsReg V μ 𝓕 ρ → ∀ U : Subgroup (GA D V), IsOpen (U : Set (GA D V)) → ∃ (N : ℕ) (S : List (List (D.what₂.Tau × Mt V.rank))), (∀ l ∈ S, ∀ p ∈ l, p.2 ∈ lieAt V p.1) ∧ ∀ x, ∃ C : ℝ, ∀ F ψ, IsSmoothVector' θ V ρ F → (∀ k ∈ U, k ∈ GfC V → ρ k F = F) → Continuous ψ → Repr V μ 𝓕 F ψ → ∀ u ∈ GinfC V, ‖ψ (x * u)‖ ≤ C * normInf θ V u ^ N * (S.map fun l => ‖l.foldr (dL2 θ V ρ) F‖).sum := by
  intro D θ V hθ μ 𝓕 ρ hp hρ U hU
  obtain ⟨S, Ω, C₁, hS, hΩ, hsob⟩ := GlobalTheory.T.local_sobolev_inequality_adelic_unitary D θ V hθ U hU μ hp.haar
  have hcount := GlobalTheory.T.ncard_rationalPoints_translatedCompact_le_pow D θ V hθ Ω hΩ
  refine hcount.elim fun N hN => ?_
  refine ⟨N, S, hS, fun x => ?_⟩
  refine (hN x).elim fun C₂ hC₂ => ?_
  refine ⟨√|C₁| * |C₂|, fun F ψ hF hlev hψ hr u hu => ?_⟩
  obtain ⟨ψ', hr', haut, hsm, hder⟩ := GlobalTheory.T.smooth_vector_automorphic_derivatives D θ V hθ μ 𝓕 ρ hp hρ U hU F hF hlev
  have e : ψ' = ψ := (GlobalTheory.T.bounded_automorphic_has_representative D V μ 𝓕 ρ hp hρ).2.1 F ψ' ψ haut.cont hψ hr' hr
  subst e
  have h1 := hsob ψ' hψ (fun k hk hk' => level_of_repr V hp hρ hψ hr (hlev k hk hk')) (fun l hl => (hder l hl).1) hsm (x * u)
  have h2 := fun l hl => integral_le_adelic V hp hΩ (x * u) _ (hC₂ u hu) _ _ (hder l (hS l hl)).1 (hder l (hS l hl)).2
  have h3 := le_of_sums S
    (fun l => ∫ o in Ω, ‖(l.foldr (fun p f => Rder θ V p.1 p.2 f) ψ') (x * u * o)‖ ^ 2 ∂μ)
    (fun l => ‖l.foldr (dL2 θ V ρ) F‖) ‖ψ' (x * u)‖ C₁ C₂ (normInf θ V u) N (normInf_nonneg θ V u)
    (fun _ => integral_nonneg fun _ => sq_nonneg _) (fun _ => norm_nonneg _) h1 h2
  exact h3

end GlobalTheory.SobolevGrowth
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.adelicCuspForm_transvection_constantTerms_zero : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → ∀ P : FDSec X, IsHolCusp X la P → ZCusp V (adel V dict (muPin V dict mu c) P) := by
  first | exact @GlobalTheory.HolDict.TransvCusp.zCusp_adel | exact GlobalTheory.HolDict.TransvCusp.zCusp_adel | (intros; apply GlobalTheory.HolDict.TransvCusp.zCusp_adel <;> assumption)
end

section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.isHolomorphicCuspForm_of_adelic_constantTerms_zero : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (r : ℕ) (hr : V.rank = r) (Comp : Type) (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data D.host.E r) (la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (dict : GA D V → Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (X k).Ψ r) (mu : GA D V → ℂ) (c : Comp → ℂ) (Kf : Subgroup (GA D V)), HolShape M → GoodDict θ M w hr X la dict mu c Kf → ∀ P : FDSec X, (∀ k, (X k).IsBddSec (la k) (P k)) → ZCusp V (adel V dict (muPin V dict mu c) P) → IsHolCusp X la P := by
  first | exact @GlobalTheory.HolDict.IntoCusp.isHolCusp_of_zCusp | exact GlobalTheory.HolDict.IntoCusp.isHolCusp_of_zCusp | (intros; apply GlobalTheory.HolDict.IntoCusp.isHolCusp_of_zCusp <;> assumption)
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem exists_pair_mem_H_of_rep {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    {a b : ℤ} {M : HermLB p} (h : P.Rep a b M) : ∃ Q : Pair p, Q.L = M ∧ ∀ f ∈ P.H a b, f ∈ Q.H 1 0 := by
  obtain ⟨ρ, hρ, hu, -⟩ := h
  refine ⟨⟨M, P.A, ρ, P.r', hρ, P.hr'⟩, rfl, fun f hf x c j hc hj => ?_⟩
  have hx : x ∈ (⨆ i, P.L.B.U i) := by rw [P.L.isLB.cover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hx
  have h1 := (hu x c i j hc hi hj).regAt.mul (hf x i j hi hj)
  have hi0 : (P.r i : X.functionField) ^ a ≠ 0 := zpow_ne_zero _ (P.r i).ne_zero
  have hj0 : (P.r' j : X.functionField) ^ b ≠ 0 := zpow_ne_zero _ (P.r' j).ne_zero
  convert h1 using 1
  simp only [Pair.loc, zpow_one, zpow_zero]
  field_simp

theorem gdeg_pos_of_ample : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L : HermLB p, IsAmpleLB L.B → L.SemiPos D → 0 < gdeg L D := by
  intro hA hS k _ X _ p D hX L hL hs
  obtain ⟨P, rfl, hPA⟩ := exists_pair L L
  obtain ⟨x, hx⟩ := (GlobalTheory.T.isTranscendenceBasis_functionField_arithmeticVariety k X p D hX).1
  obtain ⟨c, g, hc, hg, -, hm⟩ := GlobalTheory.T.exists_clear_denominators_ampleHermLineBundle k X p D hX P (hPA ▸ hL) 0 (Finset (Fin D)) fun S => ∏ i ∈ S, x i
  have hr := Pair.rep_pow k X p P 0 1 P.A c (Pair.rep_base k X p P).2.1
  rw [mul_zero, mul_one, hPA] at hr
  obtain ⟨Q, hQ, hH⟩ := exists_pair_mem_H_of_rep P hr
  have hQa : IsAmpleLB Q.L.B := by
    rw [hQ]
    exact (isAmpleLB_pow_iff hL.isLB hc).2 hL
  have hQs : Q.L.SemiPos D := by rw [hQ]; exact hs.pow c
  haveI : CharZero X.functionField :=
    have := hX.charZero
    ((fnOf (X := X) ⊤ trivial).charZero_iff (fnOf_injective _ _)).1 this
  have hli : LinearIndependent ℤ (fun _ : Unit => g) := linearIndependent_unique_iff.2 hg
  have h := GlobalTheory.T.factorial_mul_card_le_degree_ample_semiPositive hA hS k X p D hX Q hQa hQs Unit (fun _ => g) x hli hx.1 fun c' => hH _ (hm c'.2)
  rw [hQ, GlobalTheory.T.hermLineBundleGeometricDegree_pow hA k X p D hX] at h
  have h0 : (0 : ℝ) < (c : ℝ) ^ D := by positivity
  have h1 : (0 : ℝ) < (D.factorial : ℝ) * Fintype.card Unit := by
    simp [Nat.factorial_pos]
  exact (mul_pos_iff_of_pos_left h0).1 (h1.trans_le h)

end GlobalTheory.HSNef
end
end

section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma mem_offHyp_iff {n : ℕ} {S : Finset (Fin n)}
    {U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n} :
    v ∈ _root_.GlobalTheory.GoodTop.offHyp S U ↔ v ∈ U ∧ ∀ a ∈ S, v.ofLp a ≠ 0 := by
  unfold _root_.GlobalTheory.GoodTop.offHyp
  exact Iff.rfl

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma mixTop_slot_smul_sub_sub {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] (A B D : _root_.GlobalTheory.GoodTop.EndValuedForm11Coeffs n r) (s : ℂ) (j : Fin n) :
    _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one A (s • (A - B) - D) B j) =
      s * _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one A (A - B) B j) +
        (-1) * _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one A D B j) := by
  rw [← _root_.GlobalTheory.GoodTop.mixTop_position_linear, neg_one_smul, ← sub_eq_add_neg]


open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
theorem _root_.GlobalTheory.GoodTop.integral_cutTop_sub : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (G₀ G₁ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, ∀ a i j, ‖_root_.GlobalTheory.HermFrame.conn G₁ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖ * _root_.GlobalTheory.GoodMetric.poinWt S v a ≤ c) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, ∀ a b i j, ‖_root_.GlobalTheory.HermFrame.curv G₁ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖ * (_root_.GlobalTheory.GoodMetric.poinWt S v a * _root_.GlobalTheory.GoodMetric.poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → (∫ v in _root_.GlobalTheory.GoodTop.offHyp S U, (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) - (∫ v in U, (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) = ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v := by
  intro n r _ _ S U K G₀ G₁ ρ c hU hK hKU hS hG₀ hG₁ hconn hcurv hρ hρK
  have hstokes := _root_.GlobalTheory.GoodTop.integral_mixTop_position_eq_zero S U K G₀ G₁ ρ c hU hK hKU
    hS hG₀ hG₁ hconn hcurv hρ hρK
  have hF₁ := _root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_curvAt S U K G₀ G₁ ρ c hU hK hKU hS
    hG₀ hG₁ hconn hcurv hρ hρK
  have hF₀ := (_root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth U K G₀ ρ hU hK hKU hG₀ hρ
    hρK).mono_set (fun v hv => ((mem_offHyp_iff (S := S)).1 hv).1)
  have hT := _root_.GlobalTheory.GoodTop.integrableOn_corrC S U K G₀ G₁ ρ c hU hK hKU hS
    hG₀ hG₁ hconn hcurv hρ hρK
  have hpt : ∀ v, (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v =
      ∑ j, _root_.GlobalTheory.GoodTop.mixTop (_root_.GlobalTheory.GoodTop.intersection_update_fsHerm_neg_one (_root_.GlobalTheory.GoodTop.curvAt G₁ v)
        ((ρ v : ℂ) • (_root_.GlobalTheory.GoodTop.curvAt G₁ v - _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
          _root_.GlobalTheory.GoodTop.cutForm ρ G₀ G₁ v) (_root_.GlobalTheory.GoodTop.curvAt G₀ v) j) := by
    intro v
    simp_rw [mixTop_slot_smul_sub_sub]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      _root_.GlobalTheory.GoodTop.sum_mixTop_position_sub]
    unfold _root_.GlobalTheory.GoodTop.corrC
    ring
  have hzero : ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
      ((ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v) = 0 := by
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_finsetSum _ fun j _ => (hstokes j).1]
    exact Finset.sum_eq_zero fun j _ => (hstokes j).2
  have hsplit : ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
      ((ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v) =
      (∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
      (∫ v in _root_.GlobalTheory.GoodTop.offHyp S U,
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v) -
      ∫ v in _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.GoodTop.corrC ρ G₀ G₁ v := by
    have hsub : IntegrableOn (fun v =>
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) -
        (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₀ v))
        (_root_.GlobalTheory.GoodTop.offHyp S U) := hF₁.sub hF₀
    exact (integral_sub hsub hT).trans (congrArg (· - _) (integral_sub hF₁ hF₀))
  rw [← setIntegral_congr_set (_root_.GlobalTheory.GoodTop.offHyp_ae_eq S U)]
  linear_combination hzero - hsplit

end GlobalTheory.GoodTop
end

section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem exists_intBasis {K : Type} [Field K] [CharZero K] (Λ : AddSubgroup K) (hΛ : Λ.FG) :
    ∃ f : Fin (Module.finrank ℤ Λ) → K, LinearIndependent ℤ f ∧ AddSubgroup.closure (Set.range f) = Λ ∧
      ∀ i, f i ∈ Λ := by
  haveI : Module.Finite ℤ Λ := Module.Finite.iff_addGroup_fg.2 ((AddGroup.fg_iff_addSubgroup_fg Λ).2 hΛ)
  haveI : Module.Free ℤ Λ := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ Λ
  refine ⟨fun i => (b i : K), ?_, le_antisymm ?_ ?_, fun i => (b i).2⟩
  · exact b.linearIndependent.map' Λ.subtype.toIntLinearMap (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  · exact (AddSubgroup.closure_le _).2 (Set.range_subset_iff.2 fun i => (b i).2)
  · intro x hx
    have h := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
    change _ = x at h
    rw [← h, AddSubmonoidClass.coe_finsetSum]
    refine AddSubgroup.sum_mem _ fun i _ => ?_
    rw [AddSubgroupClass.coe_zsmul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self (f := fun i => (b i : K)) i)) _

theorem tendsto_logCount_sub_up : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p) (a : ℝ), P.L.SemiPos D → P.L.IsSelfInter a → ∀ Λ : ℕ → AddSubgroup X.functionField, GoodFam P D (gdeg P.L D / D.factorial) Λ → ∃ t₀ : ℝ, ∀ (u : SmFn p) (B a' : ℝ), 0 ≤ B → (∀ σ y, |u.u σ y| ≤ B) → (up P.L u).SemiPos D → (up P.L u).IsSelfInter a' → ∀ t : ℝ, t₀ + B ≤ t → Tendsto (fun m : ℕ => (Real.log ((ballIn (upperParabolic P u) (Λ m) m 1 (Real.exp (t * m))).ncard : ℝ) - Real.log ((ballIn P (Λ m) m 1 (Real.exp (t * m))).ncard : ℝ)) / (m : ℝ) ^ (D + 1)) atTop (𝓝 ((a' - a) / (D + 1).factorial)) := by
  intro HA k _ X _ p D hX hS P a hP ha Λ hΛ
  obtain ⟨C, hC1, hCs⟩ := hΛ.small
  refine ⟨Real.log C + 1, ?_⟩
  intro u B a' hB hu hup ha' t ht
  have := hX.charZero
  haveI : CharZero X.functionField :=
    charZero_of_injective_ringHom (germ_injective_of_isIntegral X (U := ⊤) _ trivial)
  choose f hli hcl hmemΛ using fun m => exists_intBasis (Λ m) (hΛ.fg m)
  let ω : ∀ σ, VolDens p σ D := fun σ => Classical.choice (GlobalTheory.T.exists_smoothVolumeDensityChart_projArith k X p D hX hS σ)
  have hmem : ∀ (m : ℕ) i, f m i ∈ P.H m 1 := fun m i => hΛ.le m (hmemΛ m i)
  have hmem' : ∀ (m : ℕ) i, f m i ∈ (upperParabolic P u).H m 1 := fun m i => by
    rw [(GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u m 1).1]; exact hmem m i
  have hC1' : 1 ≤ C * Real.exp B := one_le_mul_of_one_le_of_one_le hC1 (Real.one_le_exp hB)
  have hlog : Real.log (C * Real.exp B) = Real.log C + B := by
    rw [Real.log_mul (by positivity) (Real.exp_pos B).ne', Real.log_exp]
  have hs : ∀ m : ℕ, 1 ≤ m → AddSubgroup.closure (Set.range (f m)) ≤
      AddSubgroup.closure (ballIn P (AddSubgroup.closure (Set.range (f m))) m 1 (C ^ m)) := by
    intro m hm; rw [hcl m]; exact hCs m hm
  have hs' : ∀ m : ℕ, 1 ≤ m → AddSubgroup.closure (Set.range (f m)) ≤
      AddSubgroup.closure (ballIn (upperParabolic P u) (AddSubgroup.closure (Set.range (f m))) m 1 ((C * Real.exp B) ^ m)) := by
    intro m hm
    rw [hcl m]
    refine (hCs m hm).trans (AddSubgroup.closure_mono ?_)
    rintro x ⟨hx, hb⟩
    refine ⟨hx, fun σ y => ?_⟩
    rw [((GlobalTheory.T.raiseFirstWeight_sections_loci_values_norms k X p P u m 1).2.2 σ y x).2]
    have h0 : 0 ≤ P.nu m 1 σ y x := by rw [← norm_val]; exact norm_nonneg _
    rw [mul_pow, ← Real.exp_nat_mul]
    refine mul_le_mul (hb σ y) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le (by positivity)
    have hu' := (abs_le.1 (hu σ y)).1
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left (neg_le.1 hu') hm0, mul_nonneg hm0 hB]
  have h1 := GlobalTheory.T.supNormBall_count_asymptotic_gramDeterminant k X p D hX hS P hP ω _ f hmem hli _ hΛ.rank C hC1 hs t (by linarith)
  have h2 := GlobalTheory.T.supNormBall_count_asymptotic_gramDeterminant k X p D hX hS (upperParabolic P u) hup ω _ f hmem' hli _ hΛ.rank (C * Real.exp B) hC1' hs' t
    (by rw [hlog]; linarith)
  have h3 := GlobalTheory.T.tendsto_logDet_gram_change_semiPositive_metric HA k X p D hX hS P hP ω _ f hmem hli hΛ.rank u a a' hup ha ha'
  simp only [hcl] at h1 h2
  have key := (h2.sub h1).add (h3.div_const 2)
  convert key using 1
  · funext m; ring
  · congr 1; ring

end GlobalTheory.HSAmp
end
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
theorem _root_.GlobalTheory.T.orbital_integral_test_function_first : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), (∀ (y : grp G β) (h : G.GAf), f (h⁻¹ * toAfF G β x t hx y * h) ≠ 0 → (∃ z : Fin G.n → ℂ, 0 < (star z ⬝ᵥ (herm G v β *ᵥ z)).re ∧ FixL G v β y z) → (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).natDegree = G.n ∧ (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)).Separable) → sh G β = β → (∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1) → ∀ P : Polynomial G.F, ∃ Y : Finset (grp G β), ∀ y : grp G β, minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) = P → (∃ a : Dat G v β, FixL G v β y a.2.1 ∧ f (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * f' (a.1.2⁻¹ * toP1 G β y * a.1.2) ≠ 0) → ∃ y₀ ∈ Y, ∃ γ : grp G β, y = γ * y₀ * γ⁻¹ := by
  first | exact @GlobalTheory.LKCx.ClsReg.classes_finite | exact GlobalTheory.LKCx.ClsReg.classes_finite
end

section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

theorem _root_.GlobalTheory.T.finite_kottwitz_classes_per_minpoly_a_eq_one : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → (∀ g, f g ≠ 0 → RegAf G g) → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ P0 : Polynomial G.F, {q : Cls G | (Quot.out q).pol = P0 ∧ (∃ μ, (Quot.out q).Mark μ) ∧ (Quot.out q).term L.K.toSubgroup f 1 K' f' ≠ 0}.Finite := by
  first | (exact @GlobalTheory.LKCx.PeriodicClassFixedPoints.finite_classes_of_pol_a_one) | (exact GlobalTheory.LKCx.PeriodicClassFixedPoints.finite_classes_of_pol_a_one) | (intros; apply GlobalTheory.LKCx.PeriodicClassFixedPoints.finite_classes_of_pol_a_one  <;> assumption)
end
