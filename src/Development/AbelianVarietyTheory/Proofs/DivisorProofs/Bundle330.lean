module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle248
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.E2.Defs
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Legendre
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle249
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
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Geometry.Manifold.StructureGroupoid
import Mathlib.Topology.UniformSpace.Uniformizable
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle005
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle007
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle004

@[expose] public section

section

open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
open scoped ContDiff

namespace GlobalTheory.PsCo.Pc1.Homot

noncomputable def scF (G : ℝ → ℝ) (j : ℕ) (s y : ℝ) : ℝ := s ^ j * iteratedDeriv (j + 1) G (s * y)

lemma contDiff_iter {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (k : ℕ) : ContDiff ℝ ∞ (iteratedDeriv k G) := by
  rw [iteratedDeriv_eq_iterate]
  exact hG.iterate_deriv k

lemma scF_contDiff {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) : ContDiff ℝ ∞ (Function.uncurry (scF G j)) := by
  have h := contDiff_iter hG (j + 1)
  exact (contDiff_fst.pow j).mul (h.comp (contDiff_fst.mul contDiff_snd))

lemma deriv_scF {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) (s y : ℝ) : deriv (scF G j s) y = scF G (j + 1) s y := by
  have h := (contDiff_iter hG (j + 1)).differentiable (by simp)
  have h1 : HasDerivAt (fun y => s * y) s y := by simpa using (hasDerivAt_id y).const_mul s
  have h2 := ((h (s * y)).hasDerivAt.comp y h1).const_mul (s ^ j)
  have h3 : deriv (scF G j s) y = _ := h2.deriv
  rw [h3, scF, iteratedDeriv_succ (n := j + 1)]
  ring

lemma iter_scale {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) (s y : ℝ) :
    iteratedDeriv (j + 1) (fun y => G (s * y)) y = s * scF G j s y := by
  rw [iteratedDeriv_comp_const_mul (hG.of_le (by exact_mod_cast le_top)) s, scF]
  ring

lemma iter_zero {G : ℝ → ℝ} (h0 : ∀ x, 1 ≤ x → G x = 0) (k : ℕ) {x : ℝ} (hx : 1 < x) : iteratedDeriv k G x = 0 := by
  have : G =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using h0 y (le_of_lt hy)
  rw [this.iteratedDeriv_eq k]
  simp

lemma scF_cont {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) (y : ℝ) : Continuous fun s => scF G j s y :=
  (scF_contDiff hG j).continuous.comp (continuous_id.prodMk continuous_const)

theorem stHomot : GlobalTheory.PsCo.Pc1.StHomot := by
  intro n ε G p q hP hK t ht
  obtain ⟨hG, h0, -, -⟩ := hP
  have hI : ∀ j, IsCutFn (fun y => ∫ s in (1:ℝ)..t, scF G j s y) ∧
      ∀ y, deriv (fun y => ∫ s in (1:ℝ)..t, scF G j s y) y = ∫ s in (1:ℝ)..t, deriv (scF G j s) y := by
    intro j
    refine GlobalTheory.T.isSmoothEventuallyZeroCutoff_intervalIntegral_deriv (scF G j) 1 t (scF_contDiff hG j) ⟨2, ?_⟩
    intro s hs y hy
    rw [Set.uIcc_of_le ht] at hs
    have : 1 < s * y := by nlinarith [hs.1]
    simp [scF, iter_zero h0 _ this]
  have key : famF ε G p 1 - famF ε G p t = -∑ x : Mode ε, ∑ j ∈ Finset.range (nMode ε + 1),
      adBas ε (Matrix.single x.1.2 x.1.1 1) (fun y => ∫ s in (1:ℝ)..t, scF G j s y) (q x j) := by
    funext g
    set D : ℝ → ℂ := fun s => ∑ x : Mode ε, ∑ j ∈ Finset.range (nMode ε + 1),
      ((scF G (j + 1) s (rM ε g) : ℂ) * ev g (dZ ε (Matrix.single x.1.2 x.1.1 1) (rP ε) * q x j) +
        (scF G j s (rM ε g) : ℂ) * ev g (dZ ε (Matrix.single x.1.2 x.1.1 1) (q x j))) with hD
    have hc : ∀ j, Continuous fun s => (scF G j s (rM ε g) : ℂ) := fun j =>
      Complex.continuous_ofReal.comp (scF_cont hG j _)
    have hder : ∀ s ∈ Set.uIcc (1:ℝ) t, HasDerivAt (fun s : ℝ => famF ε G p s g) (D s) s := by
      intro s hs
      rw [Set.uIcc_of_le ht] at hs
      have hs0 : 0 < s := by linarith [hs.1]
      have h := GlobalTheory.T.scaledKoszulTestFamily_hasDerivAt_scale ε G p q hG hK s hs0 g
      convert h using 1
      rw [hD, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
      simp only [adBas, bas]
      rw [← iteratedDeriv_succ, iter_scale hG, iter_scale hG]
      push_cast
      field_simp
    have hDc : Continuous D := by
      rw [hD]
      refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun j _ => ?_
      exact ((hc _).mul continuous_const).add ((hc _).mul continuous_const)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hDc.intervalIntegrable _ _)
    have hint : ∫ s in (1:ℝ)..t, D s = ∑ x : Mode ε, ∑ j ∈ Finset.range (nMode ε + 1),
        adBas ε (Matrix.single x.1.2 x.1.1 1) (fun y => ∫ s in (1:ℝ)..t, scF G j s y) (q x j) g := by
      rw [hD, intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun x _ => ?_
        rw [intervalIntegral.integral_finsetSum]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [intervalIntegral.integral_add (((hc _).mul_const _).intervalIntegrable _ _)
            (((hc _).mul_const _).intervalIntegrable _ _),
            intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
            intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
          simp only [adBas, bas, (hI j).2, deriv_scF hG]
        · intro j _
          exact (((hc _).mul continuous_const).add ((hc _).mul continuous_const)).intervalIntegrable _ _
      · intro x _
        refine (continuous_finsetSum _ fun j _ => ?_).intervalIntegrable _ _
        exact ((hc _).mul continuous_const).add ((hc _).mul continuous_const)
    simp only [Pi.sub_apply, Pi.neg_apply, Finset.sum_apply]
    rw [← hint, hftc]
    ring
  rw [key]
  exact neg_mem (Submodule.sum_mem _ fun x _ => Submodule.sum_mem _ fun j _ => GlobalTheory.T.conjugationDerivCutoffPolynomial_mem_unitarySpan ε _ _ _ (hI j).1)

end GlobalTheory.PsCo.Pc1.Homot
end

section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

theorem _root_.GlobalTheory.T.hasSum_rows_inv_cube_derivWeierstrassP : ∀ (τ : ℍ) (z : ℂ), HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * (τ : ℂ) + m) ^ 3) (-(1 / 2) * (tauPair τ).derivWeierstrassP z) := by
  first | exact @GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP | exact GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP | (intros; apply GlobalTheory.WpFam.hasSum_rows_derivWeierstrassP <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

theorem _root_.GlobalTheory.T.qExpansionsCoeffwiseConjugate_ring_closure : ∀ (g : ℂ ≃+* ℂ) (N : ℕ), 0 < N → (∀ c : ℂ, QConj g N (fun _ => c) fun _ => g c) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ + h τ) fun τ => f' τ + h' τ) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ - h τ) fun τ => f' τ - h' τ) ∧ (∀ f f' h h', QConj g N f f' → QConj g N h h' → QConj g N (fun τ => f τ * h τ) fun τ => f' τ * h' τ) ∧ (∀ f f' (k : ℕ), QConj g N f f' → QConj g N (fun τ => f τ ^ k) fun τ => f' τ ^ k) ∧ (∀ (κ : Type) (s : Finset κ) (f f' : κ → ℍ → ℂ), (∀ k ∈ s, QConj g N (f k) (f' k)) → (QConj g N (fun τ => ∑ k ∈ s, f k τ) fun τ => ∑ k ∈ s, f' k τ) ∧ QConj g N (fun τ => ∏ k ∈ s, f k τ) fun τ => ∏ k ∈ s, f' k τ) := by
  first | exact @GlobalTheory.QFam.qConj_ring | exact GlobalTheory.QFam.qConj_ring | (intros; apply GlobalTheory.QFam.qConj_ring <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

theorem _root_.GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ : ∀ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < N → HasQ N f a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ UpperHalfPlane.IsBoundedAtImInfty f := by
  first | exact @GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty | exact GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty | (intros; apply GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty <;> assumption)
end

section

noncomputable section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma summable_weierstrassP_terms (L : PeriodPair) (z : ℂ) :
    Summable fun l : L.lattice => 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2 := by
  have h := (L.hasSum_weierstrassPExcept 0 z).summable
  refine (h.add (summable_of_ne_finset_zero (s := {0})
    (f := fun l : L.lattice => if (l : ℂ) = 0 then 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2 else 0)
    ?_)).congr ?_
  · intro l hl
    simp only [Finset.mem_singleton] at hl
    simp [hl]
  · intro l
    by_cases hl : (l : ℂ) = 0 <;> simp [hl]

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
private lemma latticeEquivProd_symm_coe (L : PeriodPair) (p : ℤ × ℤ) :
    (L.latticeEquivProd.symm p : ℂ) = p.1 * L.ω₁ + p.2 * L.ω₂ := by
  simp [PeriodPair.latticeEquivProd, Finsupp.linearCombination_apply, Finsupp.sum_fintype,
    PeriodPair.latticeBasis]


open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate in
lemma _root_.GlobalTheory.WpFam.hasSum_rows_G2_add_weierstrassP (τ : ℍ) (z : ℂ) :
    HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z + n * τ + m) ^ 2)
      (EisensteinSeries.G2 τ + (_root_.GlobalTheory.QFam.tauPair τ).weierstrassP z) := by
  set L := _root_.GlobalTheory.QFam.tauPair τ with hLdef
  have hω₁ : L.ω₁ = τ := rfl
  have hω₂ : L.ω₂ = 1 := rfl
  set f : ℤ × ℤ → ℂ := fun p => 1 / (z - (p.1 * τ + p.2)) ^ 2 - 1 / ((p.1 : ℂ) * τ + p.2) ^ 2
    with hfdef
  have hg : HasSum (fun l : L.lattice => 1 / (z - ↑l) ^ 2 - 1 / (↑l : ℂ) ^ 2) (L.weierstrassP z) :=
    (summable_weierstrassP_terms L z).hasSum
  have hf : HasSum f (L.weierstrassP z) := by
    have := (L.latticeEquivProd.symm.toEquiv.hasSum_iff).mpr hg
    convert this using 1
    funext p
    simp [hfdef, latticeEquivProd_symm_coe, hω₁, hω₂]
  have hrow : HasSum (fun n : ℤ => ∑' m : ℤ, f (n, m)) (L.weierstrassP z) :=
    hf.prod_fiberwise fun n => (hf.summable.prod_factor n).hasSum
  have hG : HasSum (fun n : ℤ => EisensteinSeries.e2Summand n τ) (EisensteinSeries.G2 τ) := by
    rw [← _root_.Formalism.L2.Th1.F.LegendreModelEllipticTorsion.tsum_e2Summand τ]
    exact (_root_.Formalism.L2.Th1.F.LegendreModelEllipticTorsion.summable_e2Summand τ).hasSum
  have hsum := hG.add hrow
  have hF : HasSum (fun n : ℤ => ∑' m : ℤ, 1 / (z - (n * τ + m)) ^ 2)
      (EisensteinSeries.G2 τ + L.weierstrassP z) := by
    convert hsum using 1
    funext n
    have ha : Summable fun m : ℤ => 1 / ((n : ℂ) * τ + m) ^ 2 := by
      have := EisensteinSeries.linear_right_summable (τ : ℂ) n (k := 2) le_rfl
      convert this using 1
      funext m
      simp [zpow_ofNat]
    have hba : Summable fun m : ℤ => f (n, m) := hf.summable.prod_factor n
    have he : EisensteinSeries.e2Summand n τ = ∑' m : ℤ, 1 / ((n : ℂ) * τ + m) ^ 2 := by
      unfold EisensteinSeries.e2Summand
      congr 1
      funext m
      simp [EisensteinSeries.eisSummand]
    rw [he]
    have := (ha.hasSum.add hba.hasSum).tsum_eq
    simp only [hfdef, add_sub_cancel] at this
    exact this
  have hneg := (Equiv.neg ℤ).hasSum_iff.mpr hF
  convert hneg using 1
  funext n
  rw [← (Equiv.neg ℤ).tsum_eq]
  congr 1
  funext m
  simp only [Equiv.neg_apply, Int.cast_neg, Function.comp_apply]
  ring

end GlobalTheory.WpFam
end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

private theorem eis_spread (N : ℕ) (hN : 0 < N) (f : ℍ → ℂ) (a : ℕ → ℂ) (h : HasQ 1 f a) :
    HasQ N f (spread N a) := by
  unfold HasQ at h ⊢
  intro τ
  have hg : Function.Injective (fun n : ℕ => N * n) := fun x y hxy => Nat.eq_of_mul_eq_mul_left hN hxy
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← hg.hasSum_iff]
  · convert h τ using 1
    funext n
    simp only [Function.comp_apply, spread, dvd_mul_right, if_true, Nat.mul_div_cancel_left n hN]
    congr 2
    push_cast
    field_simp
  · intro m hm
    simp only [spread]
    rw [if_neg, zero_mul]
    rintro ⟨k, rfl⟩
    exact hm ⟨k, rfl⟩

private theorem eis_one {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (p : PowerSeries ℤ)
    (hp : p.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 f) :
    HasQ 1 f fun n => ((PowerSeries.coeff n p : ℤ) : ℂ) := by
  unfold HasQ
  intro τ
  have hs := hf.hasSum τ
  rw [← hp] at hs
  convert hs using 1
  funext n
  rw [PowerSeries.coeff_map, eq_intCast, ReciprocityTheory.ChartRestriction.L1.qm, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

theorem eis_hasQ_int (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ) (hF : F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD) :
    ∃ a : ℕ → ℤ, HasQ N F fun n => (a n : ℂ) := by
  obtain ⟨k, hk, p, hp⟩ : ∃ k : ℤ, IsMF k F ∧ ∃ p : PowerSeries ℤ,
      p.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 F := by
    rcases hF with rfl | rfl | rfl
    · exact ⟨4, ⟨E₄, fun _ => rfl⟩, _, ReciprocityTheory.ChartRestriction.L1.map_eisensteinFourInt⟩
    · exact ⟨6, ⟨E₆, fun _ => rfl⟩, _, ReciprocityTheory.ChartRestriction.L1.map_eisensteinSixInt⟩
    · exact ⟨12, ReciprocityTheory.ChartRestriction.L1.isMF_DD, _, ReciprocityTheory.ChartRestriction.L1.dC_eq⟩
  refine ⟨fun n => if N ∣ n then PowerSeries.coeff (n / N) p else 0, ?_⟩
  convert eis_spread N hN F _ (eis_one hk p hp) using 1
  funext n
  simp only [spread]
  split_ifs <;> simp

theorem eis_qAll (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ) (hF : F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD)
    (R : Subring ℂ) : QAll (· ∈ R) N F := by
  obtain ⟨a, ha⟩ := eis_hasQ_int N hN F hF
  exact ⟨_, ha, fun n => intCast_mem R (a n)⟩

theorem eis_qConj (N : ℕ) (hN : 0 < N) (F : ℍ → ℂ) (hF : F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD)
    (g : ℂ ≃+* ℂ) : QConj g N F F := by
  obtain ⟨a, ha⟩ := eis_hasQ_int N hN F hF
  refine ⟨_, ha, ?_⟩
  simpa only [map_intCast] using ha

theorem eis_q : ∀ (N : ℕ), 0 < N → ∀ F : ℍ → ℂ, (F = ⇑E₄ ∨ F = ⇑E₆ ∨ F = DD) →
    (∃ a : ℕ → ℤ, HasQ N F fun n => (a n : ℂ)) ∧ (∀ R : Subring ℂ, QAll (· ∈ R) N F) ∧
      ∀ g : ℂ ≃+* ℂ, QConj g N F F := by
  intro N hN F hF
  exact ⟨eis_hasQ_int N hN F hF, fun R => eis_qAll N hN F hF R, fun g => eis_qConj N hN F hF g⟩

end GlobalTheory.QFam
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
theorem _root_.GlobalTheory.QFam.isMF_of_invariant_of_hasQ : ∀ (N : ℕ) (k : ℤ) (f : ℍ → ℂ)
    (a : ℕ → ℂ), 0 < N →
    (∀ γ : SL(2, ℤ), f ∣[k] γ = f) → _root_.GlobalTheory.QFam.HasQ N f a → _root_.ReciprocityTheory.ChartRestriction.L1.IsMF k f := by
  intro N k f a hN hinv h
  refine ⟨{ toFun := f, slash_action_eq' := ?_, holo' := ?_, bdd_at_cusps' := ?_ },
    fun _ => rfl⟩
  · rintro _ ⟨γ, rfl⟩
    exact (ModularForm.SL_slash f γ).symm.trans (hinv γ)
  · exact h.mdifferentiable hN
  · intro c hc
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [hinv γ]
    exact (_root_.GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty N f a hN h).2

end GlobalTheory.QFam
end
