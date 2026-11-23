module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSublatticeIndexRpowLeSolomon
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle001
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Irreducible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle022
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle021
public import Mathlib.RingTheory.PowerSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle039
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TendstoPrimeIdealZetaSumUniv
public import Mathlib.NumberTheory.NumberField.DirichletDensity
public import Mathlib.LinearAlgebra.Eigenspace.Basic

@[expose] public section

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.valuation_sqrt_absNorm_eq_one' : ∀ (K : Type) [Field K] [NumberField K] (A : ValuationSubring ℂ) (p : ℕ), p.Prime → (p : ℂ) ∈ A.nonunits → ∀ (P : HeightOneSpectrum (𝓞 K)), (p : 𝓞 K) ∉ P.asIdeal → A.valuation (((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.valuation_sqrt_absNorm_eq_one | exact GlobalTheory.valuation_sqrt_absNorm_eq_one | (intros; apply GlobalTheory.valuation_sqrt_absNorm_eq_one <;> assumption)
end

section

open Finset MvPolynomial

namespace GlobalTheory.PowerSumDiv

variable {σ : Type} [Fintype σ]

theorem eval_esymm_card (f : σ → ℂ) :
    MvPolynomial.eval f (esymm σ ℂ (Fintype.card σ)) = ∏ i, f i := by
  rw [← Finset.card_univ, esymm, Finset.powersetCard_self]
  simp

theorem eval_psum (f : σ → ℂ) (r : ℕ) : MvPolynomial.eval f (psum σ ℂ r) = ∑ i, f i ^ r := by
  simp [psum]

theorem norm_eval_esymm_le (f : σ → ℂ) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1)
    (hp : ∀ r, 1 ≤ r → r ≤ Fintype.card σ → ‖∑ i, f i ^ r‖ ≤ c) :
    ∀ k, 1 ≤ k → k ≤ Fintype.card σ → ‖MvPolynomial.eval f (esymm σ ℂ k)‖ ≤ c := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1 hkn
    have hN := congrArg (MvPolynomial.eval f) (MvPolynomial.mul_esymm_eq_sum σ ℂ k)

    simp only [map_mul, map_pow, map_neg, map_one, map_sum, map_natCast] at hN
    have hsub : (antidiagonal k).filter (fun a => a.1 < k) ⊆ (range k).image (fun j => (j, k - j)) := by
      intro a ha
      simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
      simp only [mem_image, mem_range]
      exact ⟨a.1, ha.2, by ext <;> simp <;> omega⟩
    have hcard : ((antidiagonal k).filter (fun a => a.1 < k)).card ≤ k :=
      (card_le_card hsub).trans (card_image_le.trans (by simp))
    have hterm : ∀ a ∈ (antidiagonal k).filter (fun a => a.1 < k),
        ‖(-1 : ℂ) ^ a.1 * MvPolynomial.eval f (esymm σ ℂ a.1) * MvPolynomial.eval f (psum σ ℂ a.2)‖ ≤ c := by
      intro a ha
      simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
      have he : ‖MvPolynomial.eval f (esymm σ ℂ a.1)‖ ≤ 1 := by
        rcases Nat.eq_zero_or_pos a.1 with h0 | h0
        · rw [h0, esymm_zero]; simp
        · exact (ih a.1 ha.2 h0 (by omega)).trans hc
      have hq : ‖MvPolynomial.eval f (psum σ ℂ a.2)‖ ≤ c := by
        rw [eval_psum]; exact hp _ (by omega) (by omega)
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      calc _ ≤ 1 * c := mul_le_mul he hq (norm_nonneg _) zero_le_one
        _ = c := one_mul c
    have hk : (0 : ℝ) < k := by exact_mod_cast hk1
    have h1 : (k : ℝ) * ‖MvPolynomial.eval f (esymm σ ℂ k)‖ ≤ k * c := by
      have := congrArg norm hN
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast] at this
      rw [this]
      calc _ ≤ ∑ a ∈ (antidiagonal k).filter (fun a => a.1 < k), c := norm_sum_le_of_le _ hterm
        _ = ((antidiagonal k).filter (fun a => a.1 < k)).card * c := by rw [sum_const, nsmul_eq_mul]
        _ ≤ k * c := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hc0
    exact le_of_mul_le_mul_left h1 hk

theorem exists_one_le_norm_psum (f : σ → ℂ) (hn : 1 ≤ Fintype.card σ) (hf : ‖∏ i, f i‖ = 1) :
    ∃ r, 1 ≤ r ∧ r ≤ Fintype.card σ ∧ 1 ≤ ‖∑ i, f i ^ r‖ := by
  by_contra h
  push_neg at h
  have hne : (Icc 1 (Fintype.card σ)).Nonempty := ⟨1, by simp [hn]⟩
  set c := (Icc 1 (Fintype.card σ)).sup' hne (fun r => ‖∑ i, f i ^ r‖)
  have hc1 : c < 1 := by
    rw [Finset.sup'_lt_iff]
    intro r hr
    rw [mem_Icc] at hr
    exact h r hr.1 hr.2
  have hle : ∀ r, 1 ≤ r → r ≤ Fintype.card σ → ‖∑ i, f i ^ r‖ ≤ c := fun r h1 h2 =>
    Finset.le_sup' (fun r => ‖∑ i, f i ^ r‖) (by rw [mem_Icc]; exact ⟨h1, h2⟩)
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hle 1 le_rfl hn)
  have := norm_eval_esymm_le f hc0 hc1.le hle _ hn le_rfl
  rw [eval_esymm_card, hf] at this
  linarith

end GlobalTheory.PowerSumDiv

namespace GlobalTheory.PowerSumDiv

theorem exists_one_le_norm_psum_multiset (A : Multiset ℂ) (hA : 1 ≤ Multiset.card A) (h : ‖A.prod‖ = 1) :
    ∃ r, 1 ≤ r ∧ r ≤ Multiset.card A ∧ 1 ≤ ‖(A.map (· ^ r)).sum‖ := by
  set f : Fin A.toList.length → ℂ := A.toList.get
  have hA' : A = Finset.univ.val.map f := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have hc : Fintype.card (Fin A.toList.length) = Multiset.card A := by simp
  have hp : A.prod = ∏ i, f i := by rw [Finset.prod_eq_multiset_prod, ← hA']
  have hs : ∀ r, (A.map (· ^ r)).sum = ∑ i, f i ^ r := by
    intro r
    have e := congrArg (fun B : Multiset ℂ => (B.map (· ^ r)).sum) hA'
    rw [e, Finset.sum_eq_multiset_sum, Multiset.map_map]; rfl
  obtain ⟨r, h1, h2, h3⟩ := exists_one_le_norm_psum f (by rw [hc]; exact hA) (by rw [← hp]; exact h)
  exact ⟨r, h1, by rw [← hc]; exact h2, by rw [hs]; exact h3⟩

end GlobalTheory.PowerSumDiv

open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.PowerSumDiv

theorem one_le_absNorm {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    (1 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := by
  have : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr this

theorem not_summable_inv_absNorm {E : Type} [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ¬ Summable (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹) := by
  intro hS
  have hU : Summable (fun w : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm w.asIdeal : ℝ)⁻¹) :=
    (Finset.summable_compl_iff (f := fun w : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm w.asIdeal : ℝ)⁻¹) S).mp hS
  set M := ∑' w : HeightOneSpectrum (𝓞 E), (Ideal.absNorm w.asIdeal : ℝ)⁻¹
  have hb : ∀ s : ℝ, 1 < s → NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 E))) s ≤ M := by
    intro s hs
    have hle : ∀ w : HeightOneSpectrum (𝓞 E), (Ideal.absNorm w.asIdeal : ℝ) ^ (-s) ≤ (Ideal.absNorm w.asIdeal : ℝ)⁻¹ := by
      intro w
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (one_le_absNorm w) (by linarith)
    rw [NumberField.Set.primeIdealZetaSum_def,
      tsum_univ (fun w : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))]
    exact Summable.tsum_le_tsum hle (hU.of_nonneg_of_le (fun _ => by positivity) hle) hU
  obtain ⟨s, hsM, hs1⟩ := (((ReciprocityTheory.Neutral.Bridge.tendsto_primeIdealZetaSum_univ E).eventually_gt_atTop M).and
    self_mem_nhdsWithin).exists
  exact absurd (hb s hs1) (not_le.mpr hsM)

theorem not_summable_psum_sq {E : Type} [Field E] [NumberField E] (N : ℕ) (hN : 1 ≤ N)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (A : HeightOneSpectrum (𝓞 E) → Multiset ℂ)
    (hcard : ∀ w ∉ S, Multiset.card (A w) = N) (hprod : ∀ w ∉ S, ‖(A w).prod‖ = 1) {x : ℝ} (hx : x ≤ 1 / N) :
    ¬ Summable (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} × ℕ =>
      ‖((A p.1.1).map (· ^ (p.2 + 1))).sum‖ ^ 2 * (Ideal.absNorm p.1.1.asIdeal : ℝ) ^ (-(((p.2 : ℝ) + 1) * x)) /
        ((p.2 : ℝ) + 1)) := by
  intro hs
  have hex : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S},
      ∃ r, 1 ≤ r ∧ r ≤ N ∧ 1 ≤ ‖((A w.1).map (· ^ r)).sum‖ := by
    intro w
    have := exists_one_le_norm_psum_multiset (A w.1) (by rw [hcard w.1 w.2]; exact hN) (hprod w.1 w.2)
    rwa [hcard w.1 w.2] at this
  choose r hr1 hrN hr using hex
  set F := fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} × ℕ =>
      ‖((A p.1.1).map (· ^ (p.2 + 1))).sum‖ ^ 2 * (Ideal.absNorm p.1.1.asIdeal : ℝ) ^ (-(((p.2 : ℝ) + 1) * x)) /
        ((p.2 : ℝ) + 1) with hF
  have hinj : Function.Injective (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => (w, r w - 1)) :=
    fun a b h => congrArg Prod.fst h
  have h1 := hs.comp_injective hinj
  apply not_summable_inv_absNorm S
  refine (h1.mul_left (N : ℝ)).of_nonneg_of_le (fun _ => by positivity) (fun w => ?_)
  have hre : (((r w - 1 : ℕ) : ℝ) + 1) = (r w : ℝ) := by
    rw [Nat.cast_sub (hr1 w)]; push_cast; ring
  have hpow : r w - 1 + 1 = r w := Nat.sub_add_cancel (hr1 w)
  simp only [Function.comp_apply, hF, hre, hpow]
  have hq := one_le_absNorm w.1
  have hr0 : (0 : ℝ) < r w := by exact_mod_cast hr1 w
  have hrN' : (r w : ℝ) ≤ N := by exact_mod_cast hrN w
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hrx : (r w : ℝ) * x ≤ 1 := by
    calc (r w : ℝ) * x ≤ r w * (1 / N) := mul_le_mul_of_nonneg_left hx hr0.le
      _ = r w / N := by ring
      _ ≤ 1 := (div_le_one hN0).mpr hrN'
  have hqq : (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹ ≤ (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-((r w : ℝ) * x)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hP : 1 ≤ ‖((A w.1).map (· ^ r w)).sum‖ ^ 2 := one_le_pow₀ (hr w)
  have hQ0 : 0 ≤ (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-((r w : ℝ) * x)) := by positivity
  have hNr : 1 ≤ (N : ℝ) / r w := (one_le_div hr0).mpr hrN'
  calc (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹ ≤ (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-((r w : ℝ) * x)) := hqq
    _ ≤ ((N : ℝ) / r w) * (‖((A w.1).map (· ^ r w)).sum‖ ^ 2 * (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-((r w : ℝ) * x))) := by
        nlinarith [mul_le_mul hNr hP zero_le_one (by positivity : (0:ℝ) ≤ N / r w)]
    _ = _ := by field_simp

end GlobalTheory.PowerSumDiv

namespace GlobalTheory.PowerSumDiv

open NumberField IsDedekindDomain

end GlobalTheory.PowerSumDiv
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.sum_sublattice_index_rpow_le_solomon : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] (r : ℕ) (σ : ℝ), (r : ℝ) - 1 < σ → ∀ C : Finset (Submodule O (Fin r → O)), (∀ M ∈ C, M.toAddSubgroup.index ≠ 0) → ∑ M ∈ C, (M.toAddSubgroup.index : ℝ) ^ (-σ) ≤ ∏ i ∈ Finset.range r, (1 - (Nat.card (IsLocalRing.ResidueField O) : ℝ) ^ ((i : ℝ) - σ))⁻¹ := by
  first | exact @GlobalTheory.SubZeta.sum_index_rpow_le | exact GlobalTheory.SubZeta.sum_index_rpow_le | (intros; apply GlobalTheory.SubZeta.sum_index_rpow_le <;> assumption)
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.congruenceInvariant_const_on_frame_translate : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ (Φ : Matrix (Fin r ⊕ Fin t) (Fin r) K → ℂ), (∀ h : GL (Fin r ⊕ Fin t) O, (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inl a) (Sum.inl b) - (1 : Matrix (Fin r) (Fin r) O) a b ∈ Ideal.span {ϖ}) → (∀ a b, (h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O) (Sum.inr a) (Sum.inl b) ∈ Ideal.span {ϖ}) → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) K, Φ ((h : Matrix (Fin r ⊕ Fin t) (Fin r ⊕ Fin t) O).map (algebraMap O K) * x) = Φ x) → ∀ (x : Matrix (Fin r ⊕ Fin t) (Fin r) K) (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K) → Φ x = Φ ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)).map (algebraMap O K) * ((g⁻¹ : GL (Fin r) K) : Matrix (Fin r) (Fin r) K)) := by
  first | exact @GlobalTheory.invariant_const_on_translate | exact GlobalTheory.invariant_const_on_translate | (intros; apply GlobalTheory.invariant_const_on_translate <;> assumption)
end

section

open scoped ComplexConjugate

namespace GlobalTheory

lemma sesq_rules_of_combination {X : Type} (C : Submodule ℂ (X → ℂ)) (F : (X → ℂ) → (X → ℂ) → ℂ)
    (hl : ∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → F (a • f + f') g = star a * F f g + F f' g)
    (hr : ∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → F f (a • g + g') = a * F f g + F f g') :
    (∀ f f' g, f ∈ C → f' ∈ C → g ∈ C → F (f + f') g = F f g + F f' g) ∧
    (∀ (a : ℂ) f g, f ∈ C → g ∈ C → F (a • f) g = star a * F f g) ∧
    (∀ f g g', f ∈ C → g ∈ C → g' ∈ C → F f (g + g') = F f g + F f g') ∧
    (∀ (a : ℂ) f g, f ∈ C → g ∈ C → F f (a • g) = a * F f g) := by
  have l0 : ∀ g, g ∈ C → F 0 g = 0 := by
    intro g hg
    have := hl 1 0 0 g C.zero_mem C.zero_mem hg
    simp only [one_smul, add_zero, star_one, one_mul] at this
    linear_combination -this
  have r0 : ∀ f, f ∈ C → F f 0 = 0 := by
    intro f hf
    have := hr 1 f 0 0 hf C.zero_mem C.zero_mem
    simp only [one_smul, add_zero, one_mul] at this
    linear_combination -this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f f' g hf hf' hg
    simpa using hl 1 f f' g hf hf' hg
  · intro a f g hf hg
    have := hl a f 0 g hf C.zero_mem hg
    rwa [add_zero, l0 g hg, add_zero] at this
  · intro f g g' hf hg hg'
    simpa using hr 1 f g g' hf hg hg'
  · intro a f g hf hg
    have := hr a f g 0 hf hg C.zero_mem
    rwa [add_zero, r0 f hf, add_zero] at this

theorem riesz_and_eigenvector_of_sesq_on_fun_space : ∀ (X : Type) (C : Submodule ℂ (X → ℂ)), FiniteDimensional ℂ C →
    ∀ (ip Φ : (X → ℂ) → (X → ℂ) → ℂ),
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → ip (a • f + f') g = star a * ip f g + ip f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → ip f (a • g + g') = a * ip f g + ip f g') →
    (∀ f g : X → ℂ, f ∈ C → g ∈ C → ip g f = star (ip f g)) →
    (∀ f : X → ℂ, f ∈ C → f ≠ 0 → 0 < (ip f f).re) →
    (∀ (a : ℂ) (f f' g : X → ℂ), f ∈ C → f' ∈ C → g ∈ C → Φ (a • f + f') g = star a * Φ f g + Φ f' g) →
    (∀ (a : ℂ) (f g g' : X → ℂ), f ∈ C → g ∈ C → g' ∈ C → Φ f (a • g + g') = a * Φ f g + Φ f g') →
    (∀ f : X → ℂ, f ∈ C → ∃ h : X → ℂ, h ∈ C ∧ ∀ g : X → ℂ, g ∈ C → ip h g = Φ f g) ∧
    (C ≠ ⊥ → ∃ c : ℂ, ∃ e : X → ℂ, e ∈ C ∧ e ≠ 0 ∧ ∀ f : X → ℂ, f ∈ C → Φ f e = c * ip f e) := by
  intro X C hfin ip Φ hl hr hs hp Φl Φr
  haveI := hfin
  obtain ⟨ipa, ips, ipa', ips'⟩ := sesq_rules_of_combination C ip hl hr
  obtain ⟨Φa, Φs, Φa', Φs'⟩ := sesq_rules_of_combination C Φ Φl Φr
  let B : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun x y => ip (y : X → ℂ) x)
    (fun m₁ m₂ n => by simp only [Submodule.coe_add]; exact ipa' _ _ _ n.2 m₁.2 m₂.2)
    (fun c m n => by
      simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]; exact ips' c _ _ n.2 m.2)
    (fun m n₁ n₂ => by simp only [Submodule.coe_add]; exact ipa _ _ _ n₁.2 n₂.2 m.2)
    (fun c m n => by
      simp only [Submodule.coe_smul, smul_eq_mul, starRingEnd_apply]; exact ips c _ _ n.2 m.2)
  have Bsym : ∀ x y, B x y = conj (B y x) := by
    intro x y
    simp only [B, LinearMap.mk₂'ₛₗ_apply, starRingEnd_apply]
    exact hs _ _ x.2 y.2
  have Bpos : ∀ x, x ≠ 0 → 0 < (B x x).re := by
    intro x hx
    simp only [B, LinearMap.mk₂'ₛₗ_apply]
    exact hp _ x.2 (by rwa [ne_eq, Submodule.coe_eq_zero])
  let ipA : ℂ →ₗ[ℂ] ℂ →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun a b => conj b * a) (by intros; ring) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring)
  have riesz : ∀ L : C →ₗ[ℂ] ℂ, ∃ x : C, ∀ y : C, ip (x : X → ℂ) y = L y := by
    intro L
    obtain ⟨x, hx, -⟩ := hermitian_adjoint_exists_unique ℂ C ipA B Bsym Bpos L 1
    exact ⟨x, fun y => by have := hx y; simpa [B, ipA] using this⟩
  refine ⟨?_, ?_⟩
  · intro f hf
    let L : C →ₗ[ℂ] ℂ :=
      { toFun := fun g => Φ f g
        map_add' := fun g g' => Φa' _ _ _ hf g.2 g'.2
        map_smul' := fun c g => Φs' c _ _ hf g.2 }
    obtain ⟨x, hx⟩ := riesz L
    exact ⟨x, x.2, fun g hg => hx ⟨g, hg⟩⟩
  · intro hC
    let large₂ : C → (C →ₗ[ℂ] ℂ) := fun g =>
      { toFun := fun f => star (Φ f g)
        map_add' := fun f f' => by
          simp only [Submodule.coe_add]; rw [Φa _ _ _ f.2 f'.2 g.2, star_add]
        map_smul' := fun c f => by
          simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
          rw [Φs c _ _ f.2 g.2, star_mul, star_star, mul_comm] }
    have hex : ∀ g : C, ∃ x : C, ∀ f : C, ip (f : X → ℂ) x = Φ f g := by
      intro g
      obtain ⟨x, hx⟩ := riesz (large₂ g)
      refine ⟨x, fun f => ?_⟩
      rw [hs _ _ x.2 f.2, hx f]
      simp [large₂]
    choose R hR using hex
    have inj : ∀ x y : C, (∀ f : C, ip (f : X → ℂ) x = ip f y) → x = y := by
      intro x y h
      by_contra hne
      have hd : ((x - y : C) : X → ℂ) = (-1 : ℂ) • (y : X → ℂ) + x := by
        rw [Submodule.coe_sub]; ext t; simp; ring
      have h1 := hr (-1) ((x - y : C) : X → ℂ) y x (x - y).2 y.2 x.2
      rw [← hd, h (x - y)] at h1
      have h2 := hp _ (x - y).2 (by rwa [ne_eq, Submodule.coe_eq_zero, sub_eq_zero])
      have h3 : ip ((x - y : C) : X → ℂ) ((x - y : C) : X → ℂ) = 0 := by rw [h1]; ring
      rw [h3] at h2
      simp at h2
    let Rl : Module.End ℂ C :=
      { toFun := R
        map_add' := fun g g' => inj _ _ (fun f => by
          rw [hR, Submodule.coe_add, Submodule.coe_add, ipa' _ _ _ f.2 (R g).2 (R g').2, hR, hR,
            Φa' _ _ _ f.2 g.2 g'.2])
        map_smul' := fun c g => inj _ _ (fun f => by
          rw [hR, Submodule.coe_smul, RingHom.id_apply, Submodule.coe_smul, ips' c _ _ f.2 (R g).2, hR,
            Φs' c _ _ f.2 g.2]) }
    haveI : Nontrivial C := Submodule.nontrivial_iff_ne_bot.mpr hC
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue Rl
    obtain ⟨e, he⟩ := hc.exists_hasEigenvector
    refine ⟨c, e, e.2, by rw [ne_eq, Submodule.coe_eq_zero]; exact he.2, fun f hf => ?_⟩
    rw [← hR e ⟨f, hf⟩]
    show ip f ((Rl e : C) : X → ℂ) = _
    rw [he.apply_eq_smul, Submodule.coe_smul, ips' c _ _ hf e.2]

end GlobalTheory
end

section


theorem _root_.GlobalTheory.T.schur_equivariant_maps_proportional : ∀ (H W X : Type) [Group H] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] [Nontrivial W] [AddCommGroup X] [Module ℂ X] (ρ : H → Module.End ℂ W) (a : H → Module.End ℂ X) (φ ξ : W →ₗ[ℂ] X), (∀ U : Submodule ℂ W, (∀ h, U.map (ρ h) ≤ U) → U = ⊥ ∨ U = ⊤) → Function.Injective ξ → LinearMap.range φ ≤ LinearMap.range ξ → (∀ h w, φ (ρ h w) = a h (φ w)) → (∀ h w, ξ (ρ h w) = a h (ξ w)) → ∃ c : ℂ, φ = c • ξ := by
  first | exact @GlobalTheory.schur_proportional | exact GlobalTheory.schur_proportional | (intros; apply GlobalTheory.schur_proportional <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.valuation_embedding_generator_eq_one' : ∀ (K : Type) [Field K] [NumberField K] (A : ValuationSubring ℂ) (p : ℕ), p.Prime → (p : ℂ) ∈ A.nonunits → ∀ (P : HeightOneSpectrum (𝓞 K)), (p : 𝓞 K) ∉ P.asIdeal → ∀ (α : 𝓞 K) (h : ℕ), Ideal.span {α} = P.asIdeal ^ h → ∀ σ : K →+* ℂ, A.valuation (σ (α : K)) = 1 := by
  first | exact @GlobalTheory.valuation_embedding_generator_eq_one | exact GlobalTheory.valuation_embedding_generator_eq_one | (intros; apply GlobalTheory.valuation_embedding_generator_eq_one <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_intertwiningMap_ne_zero_of_isotypic_irreducible : ∀ (H V W : Type) [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H V) (σ : Representation ℂ H W), σ.IsIrreducible → (⨆ f : σ.IntertwiningMap ρ, LinearMap.range f.toLinearMap) = ⊤ → (∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ H W'), σ'.IsIrreducible → ∀ f' : σ'.IntertwiningMap ρ, f' ≠ 0 → Nonempty (σ.Equiv σ')) → ∀ v : V, v ≠ 0 → ∃ p : ρ.IntertwiningMap σ, p v ≠ 0 := by
  first | exact @GlobalTheory.IsoSep.main | exact GlobalTheory.IsoSep.main | (intros; apply GlobalTheory.IsoSep.main <;> assumption)
end

section


theorem _root_.GlobalTheory.T.mk_sum_hsymm_mul_prod_one_sub_eq_one : ∀ {m n : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (T : ℂ),
    PowerSeries.mk (fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j)) *
      ∏ p : Fin n × Fin m, (1 - PowerSeries.C (α p.1 * β p.2 * T) * PowerSeries.X) = 1 := by
  exact @GlobalTheory.JSW.mk_sum_prod_hsymm_mul_prod_one_sub
end

section


theorem _root_.GlobalTheory.T.exists_compatible_seq_of_finite_nonempty' : ∀ (X : ℕ → Type) (f : ∀ n, X (n + 1) → X n) (Y : ∀ n, Set (X n)), (∀ n, (Y n).Finite) → (∀ n, (Y n).Nonempty) → (∀ n, ∀ x ∈ Y (n + 1), f n x ∈ Y n) → ∃ s : ∀ n, X n, ∀ n, s n ∈ Y n ∧ f n (s (n + 1)) = s n := by
  first | exact @GlobalTheory.exists_compatible_seq_of_finite_nonempty | exact GlobalTheory.exists_compatible_seq_of_finite_nonempty | (intros; apply GlobalTheory.exists_compatible_seq_of_finite_nonempty <;> assumption)
end

section


theorem _root_.GlobalTheory.T.exists_representatives_two_element_orbits_involution : ∀ (ι : Type) [Finite ι] (s : ι → ι), (∀ i, s (s i) = i) → ∃ (r : ℕ) (e : Fin r → ι), (∀ j k, e j = e k → j = k) ∧ (∀ j k, s (e j) ≠ e k) ∧ ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j) := by
  first | exact @GlobalTheory.involution_pair_representatives | exact GlobalTheory.involution_pair_representatives | (intros; apply GlobalTheory.involution_pair_representatives <;> assumption)
end

section

open NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.norm_totallyPositive_of_totallyPositive_ne_zero : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] (a : E'), a ≠ 0 → (∀ φ : E' →+* ℝ, 0 < φ a) → ∀ φ : E →+* ℝ, 0 < φ (Algebra.norm E a) := by
  first | exact @GlobalTheory.norm_pos_of_totallyPositive | exact GlobalTheory.norm_pos_of_totallyPositive | (intros; apply GlobalTheory.norm_pos_of_totallyPositive <;> assumption)
end
