module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle048
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle045
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle049
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle039
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreBase
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
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver IsMultiHomog)
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (secOver chartRingOver cellMon)

namespace RowSecGlue

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  [Algebra S Ω]

def ratioPt (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) : (Σ k, ι k) → Ω := fun p => y p / y ⟨p.1, c p.1⟩


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_ratioPt_mem (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (R : MRingOver S ι) :
    aeval (ratioPt y c) R ∈ chartRingOver S y c := by
  rw [chartRingOver, Algebra.adjoin_range_eq_range_aeval]
  exact ⟨R, rfl⟩

theorem aeval_eq_ratioPt (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    {F : MRingOver S ι} {d : K → ℕ} (hF : _root_.ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog F d) :
    aeval y F = aeval (ratioPt y c) F * ∏ k, y ⟨k, c k⟩ ^ d k := by
  classical
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]

  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  simp only [aeval_monomial]
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Finsupp.prod_fintype _ _ (fun _ => by simp)]
  have h1 : ∀ p : (Σ k, ι k), y p ^ μ p = ratioPt y c p ^ μ p * y ⟨p.1, c p.1⟩ ^ μ p := by
    intro p
    rw [ratioPt, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ (hc p.1))]
  have h2 : ∏ p : (Σ k, ι k), y ⟨p.1, c p.1⟩ ^ μ p = ∏ k, y ⟨k, c k⟩ ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, y ⟨k, c k⟩ ^ μ ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hF μ hμ k]
  rw [Finset.prod_congr rfl fun p _ => h1 p, Finset.prod_mul_distrib, h2]
  ring

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem exists_mul_eq_pow (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1))
    (J : Finset (Fin (N + 1))) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {t : MRingOver S ι}
    (ht : t ∈ cellMon S (baseCell k₀ e J fun k => {c k})) :
    ∃ (n : ℕ) (w : Ω), w ∈ chartRingOver S y c ∧
      w * aeval (ratioPt y c) t = (∏ j ∈ J, ratioPt y c ⟨k₀, e.symm j⟩) ^ n := by
  have hone : ∀ k, ratioPt y c ⟨k, c k⟩ = 1 := fun k => div_self (hc k)
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    unfold baseCell at hi
    by_cases hk : k = k₀
    · subst hk
      rw [Function.update_self, Finset.mem_union, Finset.mem_singleton, Finset.mem_map] at hi
      rcases hi with rfl | ⟨j, hj, rfl⟩
      · exact ⟨0, 1, one_mem _, by rw [aeval_X, hone, pow_zero, one_mul]⟩
      · refine ⟨1, ∏ j' ∈ J.erase j, ratioPt y c ⟨k, e.symm j'⟩,
          prod_mem fun j' _ => by simpa using aeval_ratioPt_mem (S := S) y c (X ⟨k, e.symm j'⟩), ?_⟩
        rw [aeval_X, pow_one]
        exact Finset.prod_erase_mul J (fun j' => ratioPt y c ⟨k, e.symm j'⟩) hj
    · rw [Function.update_of_ne hk, Finset.mem_singleton] at hi
      subst hi
      exact ⟨0, 1, one_mem _, by rw [aeval_X, hone, pow_zero, one_mul]⟩
  | one => exact ⟨0, 1, one_mem _, by simp⟩
  | mul f g _ _ h₁ h₂ =>
    obtain ⟨n₁, w₁, hw₁, e₁⟩ := h₁
    obtain ⟨n₂, w₂, hw₂, e₂⟩ := h₂
    exact ⟨n₁ + n₂, w₁ * w₂, mul_mem hw₁ hw₂, by rw [map_mul, pow_add, ← e₁, ← e₂]; ring⟩

theorem prod_zpow_neg (Y : K → Ω) (hY : ∀ k, Y k ≠ 0) (k₀ : K) (γ : K → ℤ) (m : ℕ) :
    ∏ k, Y k ^ (-(γ + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) = (∏ k, Y k ^ γ k)⁻¹ * (Y k₀ ^ m)⁻¹ := by
  have h : ∀ k, Y k ^ (-(γ + (m : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
      (Y k ^ γ k)⁻¹ * (Y k ^ ((m : ℤ) * (Pi.single k₀ (1 : ℤ) : K → ℤ) k))⁻¹ := by
    intro k
    rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_add, zpow_add₀ (hY k), zpow_neg, zpow_neg,
      IndefiniteRowSideFullHecke.Kleiman2.baseDeg]
  have h2 : ∏ k, Y k ^ ((m : ℤ) * (Pi.single k₀ (1 : ℤ) : K → ℤ) k) = Y k₀ ^ m := by
    rw [Finset.prod_eq_single k₀ (fun k _ hk => by simp [Pi.single_apply, hk])
      (fun h => absurd (Finset.mem_univ _) h)]
    simp
  rw [Finset.prod_congr rfl fun k _ => h k, Finset.prod_mul_distrib, Finset.prod_inv_distrib,
    Finset.prod_inv_distrib, h2]

theorem exists_pow_of_mem_cellSec (y : (Σ k, ι k) → Ω) (k₀ : K) {N : ℕ} (e : ι k₀ ≃ Fin (N + 1)) (γ : K → ℤ)
    (J : Kleiman.Chart (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀ ∘ e.symm)) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {z : Ω}
    (hz : z ∈ cellSec S y γ (baseCell k₀ e J.1 fun k => {c k})) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, Kleiman.xProd J ^ n * z *
      ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) ∈ chartRingOver S y c := by
  have hJ : ∀ j ∈ J.1, y ⟨k₀, e.symm j⟩ ≠ 0 := fun j hj => (Kleiman.mem_support _).mp (J.2.2 hj)
  have hmeet : CellMeets y (baseCell k₀ e J.1 fun k => {c k}) := by
    intro k i hi
    unfold baseCell at hi
    by_cases hk : k = k₀
    · subst hk
      rw [Function.update_self, Finset.mem_union, Finset.mem_singleton, Finset.mem_map] at hi
      rcases hi with rfl | ⟨j, hj, rfl⟩
      · exact hc k
      · exact hJ j hj
    · rw [Function.update_of_ne hk, Finset.mem_singleton] at hi
      subst hi; exact hc k
  unfold cellSec at hz
  rw [if_pos hmeet] at hz
  set u := ratioPt y c with hu
  set xJ := ∏ j ∈ J.1, u ⟨k₀, e.symm j⟩ with hxJdef
  have hxJ : xJ ∈ chartRingOver S y c :=
    prod_mem fun j _ => by simpa using aeval_ratioPt_mem (S := S) y c (X ⟨k₀, e.symm j⟩)
  have hxJ0 : xJ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j hj => div_ne_zero (hJ j hj) (hc k₀)
  have hX : Kleiman.xProd J = xJ * y ⟨k₀, c k₀⟩ ^ J.1.card := by
    rw [Kleiman.xProd, hxJdef, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [hu, ratioPt, Function.comp, IndefiniteRowSideFullHecke.Kleiman2.blockVec]
    rw [div_mul_cancel₀ _ (hc k₀)]
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, t, a', ht, hta, hγ, hg, rfl⟩ := hz
    obtain ⟨n₀, w, hw, hwt⟩ := exists_mul_eq_pow y k₀ e J.1 c hc ht
    refine ⟨n₀, fun n hn => ?_⟩
    have ht0 : aeval u t ≠ 0 := fun h0 => pow_ne_zero n₀ hxJ0 (by rw [← hwt, h0, mul_zero])
    have hg' := aeval_eq_ratioPt y c hc hg
    have ht' := aeval_eq_ratioPt y c hc hta
    have hexp : ∏ k, y ⟨k, c k⟩ ^ (γ k + a' k).toNat = (∏ k, y ⟨k, c k⟩ ^ γ k) * ∏ k, y ⟨k, c k⟩ ^ a' k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, Int.toNat_of_nonneg (hγ k), zpow_add₀ (hc k), zpow_natCast]
    have hW : (∏ k, y ⟨k, c k⟩ ^ γ k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
    have hA : (∏ k, y ⟨k, c k⟩ ^ a' k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    rw [← hu] at hg' ht'
    have hn' : xJ ^ n = xJ ^ (n - n₀) * (w * aeval u t) := by
      rw [hwt, ← pow_add, Nat.sub_add_cancel hn]
    have key : Kleiman.xProd J ^ n * (aeval y g / aeval y t) *
        ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
        xJ ^ (n - n₀) * w * aeval u g := by
      rw [prod_zpow_neg (fun k => y ⟨k, c k⟩) hc k₀ γ, hX, mul_pow, hn', hg', ht', hexp, pow_mul]
      have hp : y ⟨k₀, c k₀⟩ ^ (J.1.card * n) * (y ⟨k₀, c k₀⟩)⁻¹ ^ (J.1.card * n) = 1 := by
        rw [← mul_pow, mul_inv_cancel₀ (hc k₀), one_pow]
      field_simp
      linear_combination (w * aeval u g) * hp
    rw [key]
    exact mul_mem (mul_mem (pow_mem hxJ _) hw) (aeval_ratioPt_mem y c g)
  | zero => exact ⟨0, fun n _ => by simp⟩
  | add z₁ z₂ _ _ h₁ h₂ =>
    obtain ⟨n₁, h₁⟩ := h₁
    obtain ⟨n₂, h₂⟩ := h₂
    refine ⟨max n₁ n₂, fun n hn => ?_⟩
    have := add_mem (h₁ n (le_of_max_le_left hn)) (h₂ n (le_of_max_le_right hn))
    rwa [← add_mul, ← mul_add] at this
  | smul r z _ h =>
    obtain ⟨n₀, h⟩ := h
    refine ⟨n₀, fun n hn => ?_⟩
    have e1 : Kleiman.xProd J ^ n * (r • z) *
        ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) =
        algebraMap S Ω r * (Kleiman.xProd J ^ n * z *
          ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k)) := by
      rw [Algebra.smul_def]; ring
    rw [e1]
    exact mul_mem (Subalgebra.algebraMap_mem _ r) (h n hn)

end RowSecGlue

theorem RowSecGlue.proof : RowSecGlue.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y k₀ N e γ J a h
  have hc : ∀ c : ∀ k, ι k, ∃ n₀ : ℕ, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ n ≥ n₀, Kleiman.xProd J ^ n * a *
      ∏ k, y ⟨k, c k⟩ ^ (-(γ + ((n * J.1.card : ℕ) : ℤ) • IndefiniteRowSideFullHecke.Kleiman2.baseDeg k₀) k) ∈ chartRingOver S y c := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨n₀, h'⟩ := RowSecGlue.exists_pow_of_mem_cellSec y k₀ e γ J c hc (h c hc)
      exact ⟨n₀, fun _ => h'⟩
    · exact ⟨0, fun h' => absurd h' hc⟩
  choose n₀ hn₀ using hc
  refine ⟨Finset.univ.sup n₀, ?_⟩
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  intro c hc'
  exact hn₀ c hc' _ (Finset.le_sup (Finset.mem_univ c))

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn modelPts)

theorem BlockGenOfModel.proof : BlockGenOfModel.Statement := by
  classical
  intro S _ K ι _ Ω _ _ y k₀ hmod j hj k
  set x := IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀) with hx
  set A := chartRingOver S x (fun _ => j) with hA

  let D : Set A := {d | ∃ b, y ⟨k, b⟩ ≠ 0 ∧ ∀ a, (d : Ω) * (y ⟨k, a⟩ / y ⟨k, b⟩) ∈ A}
  have hI : (Submodule.span A D : Ideal A) = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hIq⟩ := Ideal.exists_le_maximal _ hne
    have hqp : q.IsPrime := hq.isPrime
    have hsame : modelPts S y = modelPts S x := hmod.2
    have hmem : locIn A q ∈ modelPts S x := ⟨fun _ => j, fun _ => hj, q, hqp, rfl⟩
    rw [← hsame] at hmem
    obtain ⟨c, hc, p, hp, hEq⟩ := hmem
    have hr : ∀ a, y ⟨k, a⟩ / y ⟨k, c k⟩ ∈ locIn A q := by
      intro a
      rw [hEq]
      exact (mem_locIn_chart_iff y c p).mpr
        ⟨⟨_, Algebra.subset_adjoin ⟨⟨k, a⟩, rfl⟩⟩, 1, Ideal.one_notMem p, by simp⟩
    choose nn dd hdd hnd using fun a => (mem_locIn_chart_iff x (fun _ => j) q).mp (hr a)
    have hdq : (∏ a, dd a) ∉ q := by
      rw [Ideal.IsPrime.prod_mem_iff]
      rintro ⟨a, -, ha⟩
      exact hdd a ha
    apply hdq
    apply hIq
    apply Submodule.subset_span
    refine ⟨c k, hc k, fun a => ?_⟩
    rw [hnd a]
    have hda : (dd a : Ω) ≠ 0 := coe_ne_zero_of_notMem x (fun _ => j) q (hdd a)
    have e : ((∏ a', dd a' : A) : Ω) * ((nn a : Ω) / dd a) =
        (nn a : Ω) * ∏ a' ∈ Finset.univ.erase a, (dd a' : Ω) := by
      rw [SubmonoidClass.coe_finsetProd, ← Finset.mul_prod_erase Finset.univ (fun a' => (dd a' : Ω))
        (Finset.mem_univ a)]
      field_simp
    rw [e]
    exact Subalgebra.mul_mem _ (nn a).2 (Subalgebra.prod_mem _ fun i _ => (dd i).2)

  have key : ∀ t ∈ (Submodule.span A D : Ideal A), ∃ w : ι k → Ω,
      (∀ a b, y ⟨k, a⟩ * w b ∈ A) ∧ ∑ b, y ⟨k, b⟩ * w b = (t : Ω) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem d hd =>
      obtain ⟨b, hb, hdb⟩ := hd
      refine ⟨Pi.single b ((d : Ω) / y ⟨k, b⟩), fun a b' => ?_, ?_⟩
      · by_cases h : b' = b
        · subst h
          simp only [Pi.single_eq_same]
          have e : y ⟨k, a⟩ * ((d : Ω) / y ⟨k, b'⟩) = (d : Ω) * (y ⟨k, a⟩ / y ⟨k, b'⟩) := by ring
          rw [e]
          exact hdb a
        · simp only [Pi.single_eq_of_ne h, mul_zero]
          exact Subalgebra.zero_mem _
      · simp only [Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
        field_simp
    | zero => exact ⟨0, fun _ _ => by simp, by simp⟩
    | add s t _ _ hs ht =>
      obtain ⟨w, hw, hws⟩ := hs
      obtain ⟨w', hw', hwt⟩ := ht
      refine ⟨w + w', fun a b => ?_, ?_⟩
      · rw [Pi.add_apply, mul_add]
        exact Subalgebra.add_mem _ (hw a b) (hw' a b)
      · simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, hws, hwt]
        push_cast
        ring
    | smul r t _ ht =>
      obtain ⟨w, hw, hwt⟩ := ht
      refine ⟨fun b => (r : Ω) * w b, fun a b => ?_, ?_⟩
      · have e : y ⟨k, a⟩ * ((r : Ω) * w b) = (r : Ω) * (y ⟨k, a⟩ * w b) := by ring
        rw [e]
        exact Subalgebra.mul_mem _ r.2 (hw a b)
      · rw [smul_eq_mul, Subalgebra.coe_mul, ← hwt, Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
  obtain ⟨w, hw, hsum⟩ := key 1 (by rw [hI]; exact Submodule.mem_top)
  exact ⟨w, hw, by rw [hsum]; simp⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver chartRingOver mConeMapOver)

theorem ne_zero_of_mIdealOver_le {S : Type} [CommRing S] {K : Type} {ι : K → Type} {Ω Ω' : Type} [Field Ω]
    [Field Ω'] [Algebra S Ω] [Algebra S Ω'] {y : (Σ k, ι k) → Ω} {y' : (Σ k, ι k) → Ω'}
    (h : mIdealOver S y ≤ mIdealOver S y') (p : Σ k, ι k) (hp : y' p ≠ 0) : y p ≠ 0 := by
  intro h0
  apply hp
  have hmem : (X p : MvPolynomial (Σ k, ι k) S) ∈ mIdealOver S y := by
    simp [mIdealOver, RingHom.mem_ker, mConeMapOver, h0]
  have h' := h hmem
  simpa [mIdealOver, RingHom.mem_ker, mConeMapOver] using h'

theorem mem_chartRing_blockVec_iff {S : Type} [CommRing S] {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]
    [Algebra S Ω] (z : (Σ k, ι k) → Ω) (k₀ : K) (j : ι k₀) (u : Ω) :
    u ∈ chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec z k₀)) (fun _ => j) ↔
      ∃ P : MvPolynomial (Σ _ : Unit, ι k₀) S,
        aeval (fun v : (Σ _ : Unit, ι k₀) => z ⟨k₀, v.2⟩ / z ⟨k₀, j⟩) P = u := by
  unfold chartRingOver
  rw [Algebra.adjoin_range_eq_range_aeval, AlgHom.mem_range]
  rfl

theorem aeval_rename_blockRatio {S : Type} [CommRing S] {K : Type} {ι : K → Type} {L : Type} [Field L]
    [Algebra S L] (z : (Σ k, ι k) → L) (k₀ : K) (c : ∀ k, ι k) (P : MvPolynomial (Σ _ : Unit, ι k₀) S) :
    aeval (fun p => z p / z ⟨p.1, c p.1⟩)
        (rename (fun v : (Σ _ : Unit, ι k₀) => (⟨k₀, v.2⟩ : Σ k, ι k)) P) =
      aeval (fun v : (Σ _ : Unit, ι k₀) => z ⟨k₀, v.2⟩ / z ⟨k₀, c k₀⟩) P := by
  rw [aeval_rename]
  rfl

theorem BlockGenTransfer.proof (hk : ChartKernel.Statement) : BlockGenTransfer.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y k₀ hB Ω' _ _ y' hne hle j hj k
  have hy := ne_zero_of_mIdealOver_le hle
  obtain ⟨c, hck₀, hc⟩ : ∃ c : ∀ k, ι k, c k₀ = j ∧ ∀ k, y' ⟨k, c k⟩ ≠ 0 := by
    choose c₀ hc₀ using hne
    refine ⟨Function.update c₀ k₀ j, Function.update_self _ _ _, fun k' => ?_⟩
    by_cases h : k' = k₀
    · cases h
      rw [Function.update_self]
      exact hj
    · rw [Function.update_of_ne h]
      exact hc₀ k'
  have hb₀ : y ⟨k, c k⟩ ≠ 0 := hy _ (hc k)
  obtain ⟨w, hw, hsum⟩ := hB j (hy _ hj) k
  choose P hP using fun a b => (mem_chartRing_blockVec_iff y k₀ j _).1 (hw a b)
  let φ : (Σ _ : Unit, ι k₀) → (Σ k, ι k) := fun v => ⟨k₀, v.2⟩
  have hR1 : ∀ a b, aeval (fun p => y p / y ⟨p.1, c p.1⟩)
      (X ⟨k, a⟩ * rename φ (P (c k) b) - rename φ (P a b)) = 0 := by
    intro a b
    simp only [map_sub, map_mul, aeval_X, φ, aeval_rename_blockRatio, hck₀, hP]
    field_simp
    ring
  have hR2 : aeval (fun p => y p / y ⟨p.1, c p.1⟩)
      (∑ b, X ⟨k, b⟩ * rename φ (P (c k) b) - 1) = 0 := by

    simp only [map_sub, map_sum, map_mul, map_one, aeval_X, φ, aeval_rename_blockRatio, hck₀, hP]
    rw [sub_eq_zero, ← hsum]
    refine Finset.sum_congr rfl fun b _ => ?_
    field_simp
  refine ⟨fun b => aeval (fun v : (Σ _ : Unit, ι k₀) => y' ⟨k₀, v.2⟩ / y' ⟨k₀, j⟩) (P (c k) b) / y' ⟨k, c k⟩,
    fun a b => ?_, ?_⟩
  · have h1 := hk S K ι Ω y Ω' y' hle c hc _ (hR1 a b)
    simp only [map_sub, map_mul, aeval_X, φ, aeval_rename_blockRatio, hck₀, sub_eq_zero] at h1
    rw [mem_chartRing_blockVec_iff]
    refine ⟨P a b, ?_⟩
    rw [← h1]
    ring
  · have h2 := hk S K ι Ω y Ω' y' hle c hc _ hR2

    simp only [map_sub, map_sum, map_mul, map_one, aeval_X, φ, aeval_rename_blockRatio, hck₀,
    sub_eq_zero] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 (pullDeg baseDeg)
open GroundTheory.Heights₂.Heights.NumbersDVR (segreVec)

section Twist

variable {S : Type} [CommRing S] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)

theorem zpow_mem_subalgebra_of_inv_mem (A : Subalgebra S Ω) {u : Ω} (hu : u ∈ A) (hu' : u⁻¹ ∈ A) (n : ℤ) :
    u ^ n ∈ A := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]
    exact pow_mem hu m
  · rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact pow_mem hu' m

theorem prod_segreChart_twist (d c : ∀ k, ι k) (β : K → ℤ) (n : ℤ) :
    ∏ k, segreJoin y ⟨k, segreChart d c k⟩ ^ (-(pullDeg β + n • baseDeg (Sum.inl ()) : Unit ⊕ K → ℤ) k) =
      segreVec y d ^ (-n) * ∏ k, y ⟨k, c k⟩ ^ (-β k) := by
  rw [Fintype.prod_sum_type]
  simp [pullDeg, baseDeg]
  rfl


omit [DecidableEq K] in
theorem prod_add_const (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (β : K → ℤ) (n : ℤ) :
    ∏ k, y ⟨k, c k⟩ ^ (-(β + fun _ => n : K → ℤ) k) = segreVec y c ^ (-n) * ∏ k, y ⟨k, c k⟩ ^ (-β k) := by
  have e : ∀ k, y ⟨k, c k⟩ ^ (-(β + fun _ => n : K → ℤ) k) = y ⟨k, c k⟩ ^ (-n) * y ⟨k, c k⟩ ^ (-β k) := fun k => by
    rw [Pi.add_apply, neg_add, zpow_add₀ (hc k), mul_comm]
  simp only [e, Finset.prod_mul_distrib, Finset.prod_zpow]
  rfl

theorem secOver_segreJoin_twist (β : K → ℤ) (n : ℤ) :
    secOver S (segreJoin y) (pullDeg β + n • baseDeg (Sum.inl ())) = secOver S y (β + fun _ => n) := by
  ext s
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  constructor
  · intro h c hc
    have := h (segreChart c c) (segreChart_adm y (segreVec_ne_zero y hc) hc)
    rw [prod_segreChart_twist] at this
    rw [prod_add_const y c hc]
    exact segre_diag_le y c this
  · intro h C hC
    obtain ⟨d, c, rfl⟩ := segreChart_eta C
    have hd : segreVec y d ≠ 0 := hC (Sum.inl ())
    have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => hC (Sum.inr k)
    have hc0 : segreVec y c ≠ 0 := segreVec_ne_zero y hc
    have hs := chartRingOver_le_segre y d c (h c hc)
    rw [prod_add_const y c hc] at hs
    set R := chartRingOver S (segreJoin y) (segreChart d c)
    have hu : segreVec y c / segreVec y d ∈ R := Algebra.subset_adjoin ⟨⟨Sum.inl (), c⟩, rfl⟩
    have hu' : (segreVec y c / segreVec y d)⁻¹ ∈ R := by
      rw [inv_div]
      exact chartRingOver_le_segre y d c (segreVec_div_mem y c d)
    have e : s * (segreVec y d ^ (-n) * ∏ k, y ⟨k, c k⟩ ^ (-β k)) =
        s * (segreVec y c ^ (-n) * ∏ k, y ⟨k, c k⟩ ^ (-β k)) * (segreVec y c / segreVec y d) ^ n := by
      rw [div_zpow, zpow_neg, zpow_neg]
      field_simp
    rw [prod_segreChart_twist, e]
    exact mul_mem hs (zpow_mem_subalgebra_of_inv_mem R hu hu' n)

end Twist

theorem SegreTwist.proof : SegreTwist.Statement := by
  intro S _ K _ _ ι _ Ω _ _ y _ β c
  exact secOver_segreJoin_twist y β c

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end
end
