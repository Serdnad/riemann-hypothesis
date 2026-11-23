module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1464
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle263
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle530
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle097
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle167
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle314
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle559
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle561
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemOfRaisingOperatorsJointHarmonics
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle554
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle456
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulMemOfTwistedInvariantModLattice
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
public import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle022
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle021
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle011
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete

@[expose] public section

section

noncomputable section

namespace GlobalTheory.UnitLemma.Orbit

open GlobalTheory.UnitLemma Polynomial

variable {K : UQ}

theorem IsIso.stSum_eq {B C : InvAlg K} {φ : B.A ≃ₐ[K.E] C.A} (h : IsIso φ) : C.stSum = B.stSum := by
  unfold InvAlg.stSum
  rw [h.finsum_eq C.N fun x u => (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K C x u).1]
  exact finsum_congr fun k => h.N_eq _

theorem IsIso.kapSum_eq {B₁ B₂ C₁ C₂ : InvAlg K} {φ₁ : B₁.A ≃ₐ[K.E] C₁.A} {φ₂ : B₂.A ≃ₐ[K.E] C₂.A}
    (h₁ : IsIso φ₁) (h₂ : IsIso φ₂) : InvAlg.kapSum C₁ C₂ = InvAlg.kapSum B₁ B₂ := by
  unfold InvAlg.kapSum
  refine ((h₁.prod h₂).finsum_eq (fun x => K.eta (C₁.gramDet x.1) * (C₁.prod C₂).N x) fun x u => ?_).trans ?_
  · have e1 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K (C₁.prod C₂) x u).1
    have e2 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K C₁ x.1 (Units.map (MonoidHom.fst C₁.A C₂.A) u)).2
    exact congrArg₂ (· * ·) e2 e1
  · exact finsum_congr fun k => congrArg₂ (· * ·) (h₁.eta_eq _) ((h₁.prod h₂).N_eq _)

theorem IsIso.identity {B₁ B₂ C₁ C₂ : InvAlg K} {φ₁ : B₁.A ≃ₐ[K.E] C₁.A} {φ₂ : B₂.A ≃ₐ[K.E] C₂.A}
    (h₁ : IsIso φ₁) (h₂ : IsIso φ₂) (h : InvAlg.Identity C₁ C₂) : InvAlg.Identity B₁ B₂ := by
  unfold InvAlg.Identity at h ⊢
  rwa [h₁.kapSum_eq h₂, h₁.stSum_eq, h₂.stSum_eq, h₁.charpoly_eq_of_isIso, h₂.charpoly_eq_of_isIso] at h

theorem prod_aeval (B₁ B₂ : InvAlg K) (f : K.O[X]) :
    aeval (B₁.prod B₂).g f = ((aeval B₁.g f, aeval B₂.g f) : B₁.A × B₂.A) :=
  Prod.ext (aeval_algHom_apply (AlgHom.fst K.O B₁.A B₂.A) (B₁.g, B₂.g) f).symm
    (aeval_algHom_apply (AlgHom.snd K.O B₁.A B₂.A) (B₁.g, B₂.g) f).symm

theorem prod_integral (B₁ B₂ : InvAlg K) (h₁ : IsIntegral K.O B₁.g) (h₂ : IsIntegral K.O B₂.g) :
    IsIntegral K.O (B₁.prod B₂).g :=
  IsIntegral.pair (x := (B₁.g, B₂.g)) h₁ h₂

theorem eq_one_of_finrank_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e)
    (h : Module.finrank K.E (cut B e he).A = 0) : e = 1 := by
  have : Subsingleton (B.A ⧸ Ideal.span {e}) := (Module.finrank_zero_iff (R := K.E) (M := (cut B e he).A)).1 h
  have h1 : (1 : B.A) ∈ Ideal.span {e} := Ideal.Quotient.eq_zero_iff_mem.1 (Subsingleton.elim _ _)
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
  linear_combination (e - 1) * -ha + a * hi.eq

theorem finrank_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e) :
    Module.finrank K.E B.A = Module.finrank K.E (cut B e he).A +
      Module.finrank K.E (cut B (1 - e) (one_sub_fixed B he)).A := by
  rw [(AlgEquiv.prodQuotientOfIsIdempotentElem K.E hi hi.one_sub (by simp)
    (by simp [hi])).toLinearEquiv.finrank_eq, Module.finrank_prod]
  rfl

theorem charpoly_eq_mul_charpoly_cut (B : InvAlg K) {e : B.A} (hi : IsIdempotentElem e) (he : B.σ e = e) :
    B.P = (cut B e he).P * (cut B (1 - e) (one_sub_fixed B he)).P := by
  rw [← prod_P, (isIso_cut B hi he).charpoly_eq_of_isIso]

theorem one_orbit (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g)
    (h : ∀ e ∈ Algebra.adjoin K.O ({B.g} : Set B.A), e * e = e → B.σ e = e → e = 0 ∨ e = 1) :
    (∃ e ∈ Algebra.adjoin K.O ({B.g} : Set B.A), e * e = e ∧ e + B.σ e = 1) ∨
      IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A)) := by
  apply GlobalTheory.UnitLemma.OrbitAll.one_orbit <;> assumption

theorem identity_integral (hL : UnitLemmaLie) (hK : K.Odd) (n : ℕ) : ∀ B₁ B₂ : InvAlg K,
    Module.finrank K.E B₁.A + Module.finrank K.E B₂.A = n → B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 →
    (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → InvAlg.Identity B₁ B₂ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B₁ B₂ hn u₁ u₂ hs i₁ i₂
  by_cases h : ∀ e ∈ Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A),
      e * e = e → (B₁.prod B₂).σ e = e → e = 0 ∨ e = 1
  · rcases one_orbit (B₁.prod B₂) (Prod.ext u₁ u₂) (prod_integral _ _ i₁ i₂) h with h | h
    · exact GlobalTheory.T.involutive_algebra_product_identity K B₁ B₂ u₁ u₂ hs i₁ i₂ h
    · exact GlobalTheory.T.unitLemma_local_oddResidue_of_lieAlgebra hL K hK B₁ B₂ u₁ u₂ hs i₁ i₂ h
  push Not at h
  obtain ⟨e, he, hee, hσ, h0, h1⟩ := h
  rw [Algebra.adjoin_singleton_eq_range_aeval] at he
  obtain ⟨f, hf⟩ := he
  have hf : ((aeval B₁.g f, aeval B₂.g f) : B₁.A × B₂.A) = e := (prod_aeval B₁ B₂ f).symm.trans hf
  obtain ⟨e₁, e₂⟩ := e
  obtain ⟨f₁, f₂⟩ := Prod.ext_iff.1 hf
  have j₁ : IsIdempotentElem e₁ := congrArg Prod.fst hee
  have j₂ : IsIdempotentElem e₂ := congrArg Prod.snd hee
  have s₁ : B₁.σ e₁ = e₁ := congrArg Prod.fst hσ
  have s₂ : B₂.σ e₂ = e₂ := congrArg Prod.snd hσ
  dsimp only at f₁ f₂
  have r₁ := finrank_cut B₁ j₁ s₁
  have r₂ := finrank_cut B₂ j₂ s₂
  have p₁ : Module.finrank K.E (cut B₁ e₁ s₁).A + Module.finrank K.E (cut B₂ e₂ s₂).A ≠ 0 := fun hz =>
    h1 (Prod.ext (eq_one_of_finrank_cut B₁ j₁ s₁ (Nat.add_eq_zero_iff.1 hz).1)
      (eq_one_of_finrank_cut B₂ j₂ s₂ (Nat.add_eq_zero_iff.1 hz).2))
  have p₂ : Module.finrank K.E (cut B₁ (1 - e₁) (one_sub_fixed B₁ s₁)).A +
      Module.finrank K.E (cut B₂ (1 - e₂) (one_sub_fixed B₂ s₂)).A ≠ 0 := fun hz =>
    h0 (Prod.ext
      (sub_eq_self.1 (eq_one_of_finrank_cut B₁ j₁.one_sub (one_sub_fixed B₁ s₁) (Nat.add_eq_zero_iff.1 hz).1))
      (sub_eq_self.1 (eq_one_of_finrank_cut B₂ j₂.one_sub (one_sub_fixed B₂ s₂) (Nat.add_eq_zero_iff.1 hz).2)))
  rw [charpoly_eq_mul_charpoly_cut B₁ j₁ s₁, charpoly_eq_mul_charpoly_cut B₂ j₂ s₂, mul_mul_mul_comm] at hs
  refine (isIso_cut B₁ j₁ s₁).identity (isIso_cut B₂ j₂ s₂) ?_
  refine GlobalTheory.T.involutiveAlg_identity_prod_of_unit_resultant K _ _ _ _ hs (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂) (cut_integral _ _ _ i₁)
    (cut_integral _ _ _ i₂) ?_ ?_ ?_
  · rw [← prod_P, ← prod_P] at hs ⊢
    refine val_resultant _ _ hs.of_mul_left hs.of_mul_right
      (prod_integral _ _ (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂))
      (prod_integral _ _ (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂)) f ?_ ?_
    · rw [prod_aeval, cut_aeval, cut_aeval, f₁, f₂]
      exact Prod.ext (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))
        (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _))
    · rw [prod_aeval, cut_aeval, cut_aeval, f₁, f₂]
      exact Prod.ext (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self (1 - e₁))).symm
        (Ideal.Quotient.eq.2 (Ideal.mem_span_singleton_self (1 - e₂))).symm
  · exact ih _ (by omega) _ _ rfl (cut_unitary _ _ _ u₁) (cut_unitary _ _ _ u₂) hs.of_mul_left
      (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂)
  · exact ih _ (by omega) _ _ rfl (cut_unitary _ _ _ u₁) (cut_unitary _ _ _ u₂) hs.of_mul_right
      (cut_integral _ _ _ i₁) (cut_integral _ _ _ i₂)

theorem unitLemmaGroup_of_lie : UnitLemmaLie → UnitLemmaGroup := by
  intro hL K hK B₁ B₂ u₁ u₂ hs
  by_cases hi : IsIntegral K.O B₁.g ∧ IsIntegral K.O B₂.g
  · exact identity_integral hL hK _ B₁ B₂ rfl u₁ u₂ hs hi.1 hi.2
  · obtain ⟨h1, h2⟩ := GlobalTheory.T.kappaSum_zero_and_stableSum_mul_zero_of_not_integral K B₁ B₂ hi
    unfold InvAlg.Identity
    rw [h1, h2, mul_zero]

end GlobalTheory.UnitLemma.Orbit
end
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.DiscExpand

theorem ultra (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) : IsUltrametricDist (Disc l u ρ) := by
  refine IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => ?_
  refine (denseRange_ofPre l u ρ).induction_on₂ (p := fun x y => ‖x + y‖ ≤ max ‖x‖ ‖y‖)
    (isClosed_le (by fun_prop) (by fun_prop)) (fun a b => ?_) x y
  rw [← map_add (f := _), norm_ofPre, norm_ofPre, norm_ofPre]
  exact gauge_add_le_max l u ρ a b

def smallIdeal (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) (r : ℝ≥0) : Ideal A where
  carrier := {x | ‖toDisc l u ρ x‖ ≤ r}
  zero_mem' := by simp
  add_mem' {x y} hx hy := by
    haveI := ultra l u ρ
    change ‖toDisc l u ρ (x + y)‖ ≤ r
    rw [map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
  smul_mem' a x hx := by
    change ‖toDisc l u ρ (a * x)‖ ≤ r
    rw [map_mul]
    exact (norm_mul_le _ _).trans ((mul_le_mul (norm_toDisc_le _) hx (norm_nonneg _) zero_le_one).trans
      (one_mul _).le)

theorem pow_le_smallIdeal (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ θ : ℝ≥0) (I : Ideal A)
    (h : I ≤ smallIdeal l u ρ θ) (n : ℕ) : I ^ n ≤ smallIdeal l u ρ (θ ^ n) := by
  induction n with
  | zero => intro x _; change ‖toDisc l u ρ x‖ ≤ _; simpa using norm_toDisc_le x
  | succ n ih =>
    rw [pow_succ]
    refine Ideal.mul_le.2 fun x hx y hy => ?_
    change ‖toDisc l u ρ (x * y)‖ ≤ _
    rw [map_mul, pow_succ, NNReal.coe_mul]
    exact (norm_mul_le _ _).trans (mul_le_mul (ih hx) (h hy) (norm_nonneg _) (by positivity))

theorem small (l : ℕ) [hl : Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A)
    (ρ : ℝ≥0) (h0 : 0 < ρ) (h1 : ρ < 1) (r : ℝ) (hr : 0 < r) :
    ∃ n : ℕ, ∀ x ∈ (bk.J ^ n).map s, ‖toDisc l (s X) ρ x‖ ≤ r := by
  apply GlobalTheory.BSP.norm_toDisc_J_pow_small <;> assumption

theorem isClosed_expand {D D' ι : Type} [NormedCommRing D] [NormedCommRing D'] [IsUltrametricDist D']
    (j : D →+* D') (hj : ∀ x, ‖j x‖ ≤ ‖x‖) (c : ι → (D' →+ D)) (hc : ∀ i y, ‖c i y‖ ≤ ‖y‖) (b : ι → D')
    (hb : ∀ i, ‖b i‖ ≤ 1) :
    IsClosed {y | Filter.Tendsto (fun i => c i y) Filter.cofinite (nhds 0) ∧ HasSum (fun i => j (c i y) * b i) y} := by
  refine isClosed_of_closure_subset fun y hy => ?_
  rw [Metric.mem_closure_iff] at hy
  refine ⟨Metric.tendsto_nhds.2 fun ε hε => ?_, Metric.tendsto_nhds.2 fun ε hε => ?_⟩
  · obtain ⟨z, hz, hd⟩ := hy (ε / 2) (by positivity)
    filter_upwards [Metric.tendsto_nhds.1 hz.1 (ε / 2) (by positivity)] with i hi
    rw [dist_zero_right] at hi ⊢
    rw [dist_eq_norm] at hd
    have e : c i y = c i z + c i (y - z) := by rw [← map_add (f := _)]; congr 1; ring
    have := norm_add_le (c i z) (c i (y - z))
    have := hc i (y - z)
    rw [e]; linarith
  · obtain ⟨z, hz, hd⟩ := hy (ε / 3) (by positivity)
    filter_upwards [Metric.tendsto_nhds.1 hz.2 (ε / 3) (by positivity)] with F hF
    rw [dist_eq_norm] at hd hF ⊢
    have e : ∑ i ∈ F, j (c i y) * b i - y =
        (∑ i ∈ F, j (c i z) * b i - z) + (∑ i ∈ F, j (c i (y - z)) * b i) - (y - z) := by
      simp only [map_sub, sub_mul, Finset.sum_sub_distrib]; ring
    have h2 : ‖∑ i ∈ F, j (c i (y - z)) * b i‖ ≤ ‖y - z‖ :=
      IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ =>
        (norm_mul_le _ _).trans ((mul_le_mul ((hj _).trans (hc _ _)) (hb i) (norm_nonneg _) (norm_nonneg _)).trans
          (mul_one _).le)
    have h3 := norm_sub_le ((∑ i ∈ F, j (c i z) * b i - z) + (∑ i ∈ F, j (c i (y - z)) * b i)) (y - z)
    have h4 := norm_add_le (∑ i ∈ F, j (c i z) * b i - z) (∑ i ∈ F, j (c i (y - z)) * b i)
    rw [e]; linarith

theorem disc_expand (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A)
    (ι : Type) (TB : TopBasis s bk.J ι) (ρ : ℝ≥0) (h0 : 0 < ρ) (h1 : ρ < 1) (j : bk.DS ρ →+* Disc l (s X) ρ)
    (hj : IsDiscMap (l := _) (u := _) (ρ := _) s j) (cD : ι → (Disc l (s X) ρ →+ bk.DS ρ))
    (hc : (∀ i a, cD i (toDisc l (s X) ρ a) = toDisc l (X : bk.S) ρ (TB.c i a)) ∧
      (∀ i x y, cD i (j x * y) = x * cD i y) ∧ (∀ i y, ‖cD i y‖ ≤ ‖y‖)) (y : Disc l (s X) ρ) :
    Filter.Tendsto (fun i => cD i y) Filter.cofinite (nhds 0) ∧
      HasSum (fun i => j (cD i y) * toDisc l (s X) ρ (TB.b i)) y := by
  haveI := ultra l (s X) ρ
  obtain ⟨hc1, hc2, hc3⟩ := hc
  refine (denseRange_ofPre l (s X) ρ).induction_on y
    (isClosed_expand j hj.norm_le cD hc3 _ fun i => norm_toDisc_le _) fun p => ?_
  have base : ∀ a : A, Filter.Tendsto (fun i => cD i (toDisc l (s X) ρ a)) Filter.cofinite (nhds 0) ∧
      HasSum (fun i => j (cD i (toDisc l (s X) ρ a)) * toDisc l (s X) ρ (TB.b i)) (toDisc l (s X) ρ a) := by
    intro a
    refine ⟨Metric.tendsto_nhds.2 fun ε hε => ?_, Metric.tendsto_nhds.2 fun ε hε => ?_⟩
    · obtain ⟨n, hn⟩ := small l K bk bk.S (RingHom.id _) ρ h0 h1 (ε / 2) (by positivity)
      refine Filter.mem_of_superset (TB.fin a n).compl_mem_cofinite fun i hi => ?_
      have hi' : TB.c i a ∈ bk.J ^ n := by simpa using hi
      have h2 : ‖toDisc l (X : bk.S) ρ (TB.c i a)‖ ≤ ε / 2 := hn _ (by rwa [Ideal.map_id])
      change dist (cD i (toDisc l (s X) ρ a)) 0 < ε
      rw [dist_zero_right, hc1]; linarith
    · obtain ⟨n, hn⟩ := small l K bk A s ρ h0 h1 (ε / 2) (by positivity)
      change ∀ᶠ F in Filter.atTop, _
      filter_upwards [Filter.eventually_ge_atTop (TB.fin a n).toFinset] with F hF
      have h2 := hn _ (TB.approx a n F fun i hi => by
        by_contra h
        exact hi (hF (by simpa using h)))

      rw [map_sub, map_sum] at h2
      rw [dist_comm, dist_eq_norm]
      simp only [hc1, hj.ext, ← map_mul]
      linarith
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (l : A) p
  obtain ⟨w, hw⟩ := (isUnit_l_disc l (X : bk.S) ρ).exists_left_inv
  have hw' : j w * l = 1 := by rw [← map_natCast j, ← map_mul, hw, map_one]
  have e : ofPre l (s X) ρ p = j (w ^ n) * toDisc l (s X) ρ a := by
    have h2 : ofPre l (s X) ρ p * (l : Disc l (s X) ρ) ^ n = toDisc l (s X) ρ a := by
      have := congrArg (ofPre l (s X) ρ) h
      rwa [map_mul, map_pow, map_natCast, map_natCast] at this
    rw [← h2, map_pow, mul_left_comm, ← mul_pow, hw', one_pow, mul_one]
  rw [e]
  simp only [hc2]
  refine ⟨by simpa using (base a).1.const_mul (w ^ n), ?_⟩
  simpa only [map_mul, mul_assoc] using (base a).2.mul_left (j (w ^ n))

end GlobalTheory.BSP.DiscExpand
end
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP.BK

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}

theorem X_pow_natDegree_mem_lE (bk : BK K) : (X : bk.S) ^ bk.Ep.natDegree ∈ bk.J := by
  apply GlobalTheory.BSP.BK.X_pow_natDegree_mem_J <;> assumption

theorem E_mem_span_l_X (bk : BK K) : bk.E ∈ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)} := by
  obtain ⟨w, hw⟩ := bk.coeff_zero
  have hc : constantCoeff bk.E = (l : Wq l bk.a) * w := by
    rw [← coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hw]
  rw [eq_shift_mul_X_add_const bk.E, hc, map_mul, map_natCast]
  exact Ideal.add_mem _ (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
    (Ideal.mem_sup_left (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)))

end GlobalTheory.BSP.BK

theorem GlobalTheory.BSP.BK.mem_J_pow_of_X_pow_mul_mem : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N : ℕ),
    ∃ n : ℕ, ∀ m : ℕ, ∃ n' : ℕ, ∀ s : bk.S,
      (X : bk.S) ^ m * s ∈ bk.J ^ n' ⊔ Ideal.span {(l : bk.S) ^ n} → s ∈ bk.J ^ N := by
  intro l _ K bk N
  refine ⟨N, fun m => ⟨N + (m + bk.Ep.natDegree * N), fun s hs => ?_⟩⟩
  have hJ : bk.J ≤ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)} :=
    sup_le le_sup_left (Ideal.span_singleton_le_iff_mem _ |>.2 (BK.E_mem_span_l_X bk))
  have h1 : bk.J ^ (N + (m + bk.Ep.natDegree * N)) ≤
      Ideal.span {(l : bk.S) ^ N} ⊔ Ideal.span {(X : bk.S) ^ (m + bk.Ep.natDegree * N)} := by
    refine (Ideal.pow_right_mono hJ _).trans ?_
    have := Ideal.sup_pow_add_le_pow_sup_pow (I := Ideal.span {(l : bk.S)}) (J := Ideal.span {(X : bk.S)})
      (n := N) (m := m + bk.Ep.natDegree * N)
    rwa [Ideal.span_singleton_pow, Ideal.span_singleton_pow] at this
  have hs' := (sup_le h1 le_sup_left : _ ≤ Ideal.span {(l : bk.S) ^ N} ⊔
      Ideal.span {(X : bk.S) ^ (m + bk.Ep.natDegree * N)}) hs
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hs'
  obtain ⟨h, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 hz
  set t := s - (X : bk.S) ^ (bk.Ep.natDegree * N) * g with ht
  have htm : (X : bk.S) ^ m * t = C ((l : Wq l bk.a) ^ N) * h := by
    rw [ht, map_pow, map_natCast, mul_sub, ← hyz]; ring
  have ht' : t = C ((l : Wq l bk.a) ^ N) * PowerSeries.mk (fun k => coeff (k + m) h) := by
    ext k
    have := congrArg (coeff (k + m)) htm
    rw [coeff_X_pow_mul', if_pos (Nat.le_add_left m k), Nat.add_sub_cancel, coeff_C_mul] at this
    rw [this, coeff_C_mul, coeff_mk]
  have hs2 : s = ((X : bk.S) ^ bk.Ep.natDegree) ^ N * g + (l : bk.S) ^ N * PowerSeries.mk (fun k => coeff (k + m) h) := by
    have : s = t + (X : bk.S) ^ (bk.Ep.natDegree * N) * g := by rw [ht]; ring
    rw [this, ht', map_pow, map_natCast, ← pow_mul]; ring
  rw [hs2]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (BK.X_pow_natDegree_mem_lE bk) N))
    (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) N))
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

theorem _root_.GlobalTheory.T.mem_of_raisingOperators_jointHarmonics : ∀ (D : D7) (n m : ℕ) (w : GlobalTheory.ExportSeries.Weight D n) (BS : GlobalTheory.ExportSeries.GLR D n) (K : Type) [Group K] (r : K →* GlobalTheory.ExportSeries.GLR D n), (∀ (k : K) (τ : D.what₂.Tau), ((GlobalTheory.ExportSeries.inBasis BS (r k) τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : K →* Module.End ℂ W), ∀ N : Submodule ℂ (W →ₗ[ℂ] PolF D m n), (∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → (∀ w' : W, ∀ (τ' : D.what₂.Tau) (i l : Fin m), w.p τ' ≤ (i : ℕ) → (l : ℕ) < w.p τ' → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ' (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ')) (Matrix.single i l (1 : ℂ)) (φ w') = 0) → φ ∈ N) → (∀ ψ ∈ N, ∀ (τ : D.what₂.Tau) (i l : Fin m), (i : ℕ) < w.p τ → w.p τ ≤ (l : ℕ) → GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin n => true) (fun j : Fin m => decide ((j : ℕ) < w.p τ)) (Matrix.single i l (1 : ℂ)) ∘ₗ ψ ∈ N) → ∀ φ : W →ₗ[ℂ] PolF D m n, (∀ (k : K) (w' : W), φ (ρ k w') = GlobalTheory.ExportSeries.fockGL m w BS (r k) (φ w')) → φ ∈ N := by
  first | exact @GlobalTheory.RaiseGen.mem_of_raise | exact GlobalTheory.RaiseGen.mem_of_raise | (intros; apply GlobalTheory.RaiseGen.mem_of_raise <;> assumption)
end

section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj GlobalTheory.CoverRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RayUp

theorem containsRayField_up {K L L' : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field L'] [NumberField L']
    (φ : K →+* L) (τ : L →+* L') (n : ℕ) (h : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (τ.comp φ) n := by
  intro P hP
  letI : Algebra L L' := τ.toAlgebra
  let Q : HeightOneSpectrum (𝓞 L) := P.under (𝓞 L)
  have hQ : Q.asIdeal = P.asIdeal.comap (RingOfIntegers.mapRingHom τ) := rfl
  haveI hPo : P.asIdeal.LiesOver Q.asIdeal := ⟨rfl⟩
  have hn : ((n : ℕ) : 𝓞 L) ∉ Q.asIdeal := fun h' => hP (by
    rw [hQ, Ideal.mem_comap, map_natCast] at h'
    exact h')
  obtain ⟨f, α, h1, h2, h3⟩ := h Q hn
  have hf := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver P.asIdeal Q.asIdeal Q.isPrime Q.ne_bot
  have hcm : P.asIdeal.comap (RingOfIntegers.mapRingHom (τ.comp φ)) =
      Q.asIdeal.comap (RingOfIntegers.mapRingHom φ) := by
    ext x
    rfl
  rw [hcm]
  refine ⟨f * Q.asIdeal.inertiaDeg' P.asIdeal, α ^ Q.asIdeal.inertiaDeg' P.asIdeal, ?_, ?_, ?_⟩
  · rw [hf, h1, ← pow_mul]
  · rw [pow_mul, h2, Ideal.span_singleton_pow]
  · have := sub_dvd_pow_sub_pow α 1 (Q.asIdeal.inertiaDeg' P.asIdeal)
    rw [one_pow] at this
    exact dvd_trans h3 this

end GlobalTheory.RayUp
end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.CocycStLemma

theorem tmul_one_injective {F V B : Type} [Field F] [AddCommGroup V] [Module F V] [Ring B] [Algebra F B]
    [Nontrivial B] : Function.Injective (fun v : V => v ⊗ₜ[F] (1 : B)) := by
  have hinj : Function.Injective (Algebra.linearMap F B) := (algebraMap F B).injective
  obtain ⟨f, hf⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F B)
    (LinearMap.ker_eq_bot.mpr hinj)
  intro v w h
  have h2 := congrArg (fun x => TensorProduct.rid F V (LinearMap.lTensor V f x)) h
  have h1 : f 1 = 1 := by
    have := LinearMap.congr_fun hf 1
    simpa using this
  simpa [h1] using h2

end GlobalTheory.CocycStLemma

theorem GlobalTheory.cocycle_of_st_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ (z : V ⊗[ℚ_[l]] Bst P) (c : ↥(GK K) → V), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) → c ∈ continuousCocycles ρ := by
  intro l _ P AI T K V _ _ _ _ _ _ _ ρ hρ z c hc
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := GlobalTheory.T.coboundary_deRham_of_coboundary_semistable l P AI T K V ρ c z hc
    refine GlobalTheory.T.continuous_cochain_of_deRham_coboundary l P AI T K V ρ hρ 0 Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) b c ?_
    intro g
    simp [hb g]
  · intro g h
    haveI : Nontrivial P.R.B := nontrivial_B P
    haveI : Nontrivial (Bst P) := inferInstance
    apply GlobalTheory.CocycStLemma.tmul_one_injective (F := ℚ_[l]) (B := Bst P)
    simp only [add_tmul]
    rw [hc, hc g, map_mul, Module.End.mul_apply]
    have e : stRep P ρ g (c h ⊗ₜ[ℚ_[l]] (1 : Bst P)) = ρ g (c h) ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
      rw [stRep_tmul, map_one]
    rw [← e, hc h, map_sub]
    abel
end

section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.Published

theorem _root_.GlobalTheory.T.lie_skew_adjoint_matrix : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (W : Submodule ℂ (Sm E N)) (h : ∀ φ ∈ W, MemL2Quotient (latticeGL E N) μ φ.1) (hW : _root_.GlobalTheory.CuspRep.IsStable W), (∀ φ ∈ W, IsAutForm φ) → ∀ (X : Matrix (Fin N) (Fin N) (Cinf E)) (φ ψ : W), inner ℂ (toL2ₗ μ W h ⟨_, hW (.lie X) φ.1 φ.2⟩) (toL2ₗ μ W h ψ) = - inner ℂ (toL2ₗ μ W h φ) (toL2ₗ μ W h ⟨_, hW (.lie X) ψ.1 ψ.2⟩) := by
  first | exact @GlobalTheory.LieSkew.lie_skew | exact GlobalTheory.LieSkew.lie_skew | (intros; apply GlobalTheory.LieSkew.lie_skew <;> assumption)
end

section

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc

theorem _root_.GlobalTheory.T.prime_pow_smul_mem_of_twistedInvariant_mod_lattice : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → ∀ (i : ℤ), i ∉ J → ∀ M : AddSubgroup (Fin r → PadicComplex l), ball l r ⊆ (M : Set _) → (∀ x ∈ M, (l : PadicComplex l) • x ∈ ball l r) → ∀ y : Fin r → PadicComplex l, (∀ σ ∈ Gj K m, twAct act χ i U σ y - y ∈ M) → (l : PadicComplex l) ^ (2 + max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i)))) • y ∈ M := by
  first | exact @GlobalTheory.FrameInv.pow_smul_mem_of_invariant_mod | exact GlobalTheory.FrameInv.pow_smul_mem_of_invariant_mod | (intros; apply GlobalTheory.FrameInv.pow_smul_mem_of_invariant_mod <;> assumption)
end
