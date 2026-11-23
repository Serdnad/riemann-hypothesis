module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle012
public import Mathlib.NumberTheory.NumberField.CMField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle641
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle246
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle392
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnWirtWordMulExpComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle638
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle332
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle334
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle639
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle014
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle150
import Development.AbelianVarietyTheory.Definitions.Divisors.EntireEqOfHalfPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle589
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle003

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_equiv_cmType_realEmbeddings_maxRealSubfield : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∃ e : I ≃ Emb (maximalRealSubfield E), ∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CMTypeRealEmb.exists_equiv | exact GlobalTheory.CMTypeRealEmb.exists_equiv | (intros; apply GlobalTheory.CMTypeRealEmb.exists_equiv <;> assumption)
end

section

open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.QHolo

variable {F : Type} [Field F] [NumberField F]

theorem isOpen_upperHalf : IsOpen (upperHalf F) := by
  have : upperHalf F = ⋂ τ : Emb F, (fun z : Emb F → ℂ => (z τ).im) ⁻¹' Set.Ioi 0 := by
    ext z; simp [upperHalf]
  rw [this]
  exact isOpen_iInter_of_finite fun τ => isOpen_Ioi.preimage (by fun_prop)

theorem qClass_two (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) : qClass 𝔞 𝔟 2 z c =
    ((|(Algebra.norm ℚ c.out.1.1 : ℝ)| / nrm 𝔞 : ℝ) : ℂ) *
      Complex.exp (2 * (Real.pi : ℂ) * I * ∑ τ, (τ (c.out.1.1 * c.out.1.2) : ℂ) * z τ) := by
  simp [qClass, qTerm, qPow]

theorem differentiable_qClass (𝔞 𝔟 : Frac F) (c : Quotient (qRel 𝔞 𝔟)) :
    Differentiable ℂ (fun z => qClass 𝔞 𝔟 2 z c) := by
  simp only [qClass_two]
  fun_prop

theorem norm_qClass (𝔞 𝔟 : Frac F) (z : Emb F → ℂ) (c : Quotient (qRel 𝔞 𝔟)) : ‖qClass 𝔞 𝔟 2 z c‖ =
    |(Algebra.norm ℚ c.out.1.1 : ℝ)| / nrm 𝔞 *
      Real.exp (-(2 * Real.pi) * ∑ τ, τ (c.out.1.1 * c.out.1.2) * (z τ).im) := by
  rw [qClass_two, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (abs_nonneg _) (by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _))]
  congr 2
  simp [Complex.mul_re, Complex.mul_im, Complex.re_sum, Complex.im_sum, Finset.mul_sum]

theorem summable_of_fiber {α β : Type} (g : α → β) (f : α → ℝ) (B : β → ℝ) (hf : ∀ a, 0 ≤ f a)
    (hB : Summable B) (hfib : ∀ (b : β) (s : Finset α), (∀ a ∈ s, g a = b) → ∑ a ∈ s, f a ≤ B b) :
    Summable f := by
  classical
  have hB0 : ∀ b, 0 ≤ B b := fun b => by simpa using hfib b ∅ (by simp)
  refine summable_of_sum_le hf (c := ∑' b, B b) fun u => ?_
  rw [← Finset.sum_fiberwise_of_maps_to (s := u) (t := u.image g) (g := g)
    (fun x hx => Finset.mem_image_of_mem g hx)]
  calc ∑ b ∈ u.image g, ∑ a ∈ u with g a = b, f a ≤ ∑ b ∈ u.image g, B b :=
        Finset.sum_le_sum fun b _ => hfib b _ fun a ha => (Finset.mem_filter.1 ha).2
    _ ≤ ∑' b, B b := hB.sum_le_tsum _ fun b _ => hB0 b

theorem card_fiber_le [IsTotallyReal F] (𝔞 𝔟 : Frac F) (ξ : F) (s : Finset (Quotient (qRel 𝔞 𝔟)))
    (hs : ∀ c ∈ s, c.out.1.1 * c.out.1.2 = ξ) :
    (s.card : ℝ) ≤ |(Algebra.norm ℚ ξ : ℝ)| / (nrm 𝔞 * nrm 𝔟) := GlobalTheory.T.card_hilbertEisensteinFourierFiber_le_norm F 𝔞 𝔟 ξ s hs

theorem abs_norm_le [IsTotallyReal F] (𝔞 𝔟 : Frac F) (p : QPair 𝔞 𝔟) :
    |(Algebra.norm ℚ p.1.1 : ℝ)| ≤ |(Algebra.norm ℚ (p.1.1 * p.1.2) : ℝ)| / nrm 𝔟 := GlobalTheory.T.abs_norm_le_abs_norm_mul_div_absNorm_of_eisensteinIndexPair F 𝔞 𝔟 p

theorem summable_exp_trace [IsTotallyReal F] (L : FractionalIdeal (𝓞 F)⁰ F) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} => Real.exp (-δ * ∑ τ : Emb F, τ x.1)) :=
  GlobalTheory.T.summable_exp_neg_trace_totallyPositive_fractionalIdeal F L δ hδ

theorem norm_sq_exp_le [IsTotallyReal F] {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, ∀ x : F, (∀ τ : Emb F, 0 < τ x) →
    |(Algebra.norm ℚ x : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x) ≤ C * Real.exp (-(δ / 2) * ∑ τ : Emb F, τ x) :=
  GlobalTheory.T.norm_sq_mul_exp_neg_trace_le' F δ hδ

theorem summable_key [IsTotallyReal F] (𝔞 𝔟 : Frac F) {δ : ℝ} (hδ : 0 < δ) :
    Summable (fun c : Quotient (qRel 𝔞 𝔟) =>
      |(Algebra.norm ℚ c.out.1.1 : ℝ)| * Real.exp (-δ * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2))) := by
  have hna : 0 ≤ nrm 𝔞 := by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _
  have hnb : 0 ≤ nrm 𝔟 := by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _
  let β := {x : F // x ∈ ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟) ∧ ∀ τ : Emb F, 0 < τ x}
  let g : Quotient (qRel 𝔞 𝔟) → β := fun c =>
    ⟨c.out.1.1 * c.out.1.2, FractionalIdeal.mul_mem_mul c.out.2.1 c.out.2.2.1, c.out.2.2.2⟩
  let B : β → ℝ := fun x => |(Algebra.norm ℚ x.1 : ℝ)| / (nrm 𝔞 * nrm 𝔟) *
    (|(Algebra.norm ℚ x.1 : ℝ)| / nrm 𝔟 * Real.exp (-δ * ∑ τ : Emb F, τ x.1))
  obtain ⟨C, hC⟩ := norm_sq_exp_le (F := F) hδ
  have hB : Summable B := by
    refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_)
      ((summable_exp_trace (F := F) ((𝔞 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟) (half_pos hδ)).mul_left
        ((nrm 𝔞 * nrm 𝔟 * nrm 𝔟)⁻¹ * C))
    have h := hC x.1 x.2.2
    have : B x = (nrm 𝔞 * nrm 𝔟 * nrm 𝔟)⁻¹ *
        (|(Algebra.norm ℚ x.1 : ℝ)| ^ 2 * Real.exp (-δ * ∑ τ : Emb F, τ x.1)) := by
      simp only [B]; field_simp
    rw [this]
    have h2 := mul_le_mul_of_nonneg_left h (show 0 ≤ (nrm 𝔞 * nrm 𝔟 * nrm 𝔟)⁻¹ by positivity)
    linarith
  refine summable_of_fiber g _ B (fun c => by positivity) hB fun b s hs => ?_
  have hξ : ∀ c ∈ s, c.out.1.1 * c.out.1.2 = b.1 := fun c hc => by rw [← hs c hc]
  calc ∑ c ∈ s, |(Algebra.norm ℚ c.out.1.1 : ℝ)| * Real.exp (-δ * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2))
      ≤ ∑ c ∈ s, |(Algebra.norm ℚ b.1 : ℝ)| / nrm 𝔟 * Real.exp (-δ * ∑ τ : Emb F, τ b.1) := by
        refine Finset.sum_le_sum fun c hc => ?_
        rw [← hξ c hc]
        exact mul_le_mul_of_nonneg_right (abs_norm_le 𝔞 𝔟 c.out) (Real.exp_pos _).le
    _ = (s.card : ℝ) * (|(Algebra.norm ℚ b.1 : ℝ)| / nrm 𝔟 * Real.exp (-δ * ∑ τ : Emb F, τ b.1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ B b := mul_le_mul_of_nonneg_right (card_fiber_le 𝔞 𝔟 b.1 s hξ) (by positivity)

theorem exists_im_bound {y : Emb F → ℂ} (hy : y ∈ upperHalf F) :
    ∃ ε > 0, ∀ v ∈ Metric.ball y ε, ∀ τ, ε ≤ (v τ).im := by
  obtain ⟨ε, hε, hle⟩ : ∃ ε > 0, ∀ τ, 2 * ε ≤ (y τ).im := by
    rcases isEmpty_or_nonempty (Emb F) with h | h
    · exact ⟨1, one_pos, fun τ => isEmptyElim τ⟩
    · obtain ⟨τ₀, hτ₀⟩ := Finite.exists_min (fun τ => (y τ).im)
      exact ⟨(y τ₀).im / 2, half_pos (hy τ₀), fun τ => by linarith [hτ₀ τ]⟩
  refine ⟨ε, hε, fun v hv τ => ?_⟩
  have h1 : dist (v τ) (y τ) < ε := (dist_le_pi_dist v y τ).trans_lt (Metric.mem_ball.1 hv)
  have h2 : |(v τ).im - (y τ).im| < ε := by
    rw [Complex.dist_eq] at h1
    exact (by simpa using Complex.abs_im_le_norm (v τ - y τ) : |(v τ).im - (y τ).im| ≤ ‖v τ - y τ‖).trans_lt h1
  linarith [hle τ, (abs_lt.1 h2).1]

theorem qholo : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F),
    DifferentiableOn ℂ (fun z => ∑' c, GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.qClass 𝔞 𝔟 2 z c) (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F) := by
  intro F _ _ _ 𝔞 𝔟
  refine ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.differentiableOn_tsum_loc isOpen_upperHalf
    (fun c z => qClass 𝔞 𝔟 2 z c) (fun c => (differentiable_qClass 𝔞 𝔟 c).differentiableOn) ?_
  intro y hy
  obtain ⟨ε, hε, hv⟩ := exists_im_bound hy
  refine ⟨ε, hε, fun c => (nrm 𝔞)⁻¹ * (|(Algebra.norm ℚ c.out.1.1 : ℝ)| *
      Real.exp (-(2 * Real.pi * ε) * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2))),
    (summable_key 𝔞 𝔟 (by positivity)).mul_left _, fun c v hvb => ?_⟩
  rw [norm_qClass, div_eq_inv_mul, mul_assoc]
  have hn : 0 ≤ (nrm 𝔞)⁻¹ := inv_nonneg.2 (by unfold nrm; exact_mod_cast FractionalIdeal.absNorm_nonneg _)
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)) hn
  refine Real.exp_le_exp.2 ?_
  have hpos := c.out.2.2.2
  have : ε * ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2) ≤ ∑ τ : Emb F, τ (c.out.1.1 * c.out.1.2) * (v τ).im := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun τ _ => by nlinarith [hpos τ, hv v hvb τ]
  have hπ := Real.pi_pos
  nlinarith

end GlobalTheory.QHolo
end
end

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.differentiableOn_wirtWord_mul_exp_comp' : ∀ (Φ I : Type) [Fintype Φ] [Fintype I] (U : Set (I → ℂ)) (V : Set (Φ → ℂ)) (D : Set ℂ) (G : ℂ → (Φ → ℂ) → ℂ) (t : (I → ℂ) → Φ → ℂ) (b l : (I → ℂ) → ℂ), IsOpen U → IsOpen V → Set.MapsTo t U V → ContDiffOn ℝ ∞ t U → ContDiffOn ℝ ∞ b U → ContDiffOn ℝ ∞ l U → (∀ σ ∈ D, ContDiffOn ℝ ∞ (G σ) V) → (∀ w : List (Φ × Bool), ∀ y ∈ V, DifferentiableOn ℂ (fun σ => wirtWord w (G σ) y) D) → ∀ w : List (I × Bool), ∀ z ∈ U, DifferentiableOn ℂ (fun σ => wirtWord w (fun z' => b z' * Complex.exp (-σ * l z') * G σ (t z')) z) D := by
  first | exact @GlobalTheory.WirtChain.differentiableOn_wirtWord_mul_exp_comp | exact GlobalTheory.WirtChain.differentiableOn_wirtWord_mul_exp_comp | (intros; apply GlobalTheory.WirtChain.differentiableOn_wirtWord_mul_exp_comp <;> assumption)
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem isAlgebraic_of_isIntegral_algebraicNumbers {x : ℂ}
    (hx : IsIntegral (integralClosure ℚ ℂ).toSubring x) : IsAlgebraic ℚ x := by
  have hx' : IsIntegral (integralClosure ℚ ℂ) x := hx
  exact (isIntegral_trans (R := ℚ) (A := integralClosure ℚ ℂ) x hx').isAlgebraic

theorem fam_value_isAlgebraic : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (τ₀ : ℍ) (Ω : ℂ), 0 < N → ActBij act → IsFam act w f → (∀ i, QAll (IsAlgebraic ℚ) N (f i)) → IsAlgebraic ℚ (jT τ₀) → Ω ^ 12 = DD τ₀ → ∀ i, IsAlgebraic ℚ (f i τ₀ / Ω ^ w) := by
  intro ι _ act w N f τ₀ Ω hN hb hf hq hj hΩ i
  refine isAlgebraic_of_isIntegral_algebraicNumbers
    (GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow ι act w N f (integralClosure ℚ ℂ).toSubring τ₀ Ω hN hb hf (fun k => ?_) ?_ hΩ i)
  · obtain ⟨a, ha, hal⟩ := hq k
    exact ⟨a, ha, fun n => (hal n).isIntegral⟩
  · exact isIntegral_algebraMap (R := (integralClosure ℚ ℂ).toSubring) (A := ℂ)
      (x := ⟨jT τ₀, hj.isIntegral⟩)

end GlobalTheory.QFam
end

section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin.NormSurj

variable {F F' : Type} [Field F] [Field F'] [Algebra F F']

theorem coe_galAct (n : ℕ) (t : F' ≃ₐ[F] F') (x : GL (Fin n) F') :
    ((galAct F F' n t x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      (x : Matrix (Fin n) (Fin n) F').map t := by
  rfl

theorem map_incl (n : ℕ) (t : F' ≃ₐ[F] F') (γ : GL (Fin n) F) :
    ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F').map t =
      ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') := by
  ext i j
  simp [incl, gal]

theorem adjoin_stable (n : ℕ) (t : F' ≃ₐ[F] F') (γ : GL (Fin n) F) :
    ∀ x ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')},
      x.map t ∈ Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.1 hx, map_incl]
    exact Algebra.subset_adjoin rfl
  | algebraMap r =>
    have : (algebraMap F' (Matrix (Fin n) (Fin n) F') r).map t = algebraMap F' _ (t r) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.algebraMap_matrix_apply]
      split_ifs <;> simp
    rw [this]; exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy =>
    rw [Matrix.map_add _ (map_add t)]; exact Subalgebra.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    have := Matrix.map_mul (L := x) (M := y) (f := (t : F' →+* F'))
    erw [this]; exact Subalgebra.mul_mem _ hx hy

theorem adjoin_comm {A : Type} [Ring A] [Algebra F' A] (M : A) :
    ∀ x ∈ Algebra.adjoin F' {M}, ∀ y ∈ Algebra.adjoin F' {M}, x * y = y * x := by
  intro x hx y hy
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx hy
  obtain ⟨p, rfl⟩ := (AlgHom.mem_range _).1 hx
  obtain ⟨q, rfl⟩ := (AlgHom.mem_range _).1 hy
  rw [← map_mul, mul_comm, map_mul]

theorem inv_mem_of_finite {n : ℕ} [Finite F'] (B : Subalgebra F' (Matrix (Fin n) (Fin n) F'))
    (δ : GL (Fin n) F') (h : (δ : Matrix (Fin n) (Fin n) F') ∈ B) :
    ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := by
  haveI : Finite (Matrix (Fin n) (Fin n) F') := inferInstanceAs (Finite (Fin n → Fin n → F'))
  let f : B → B := fun b => ⟨δ, h⟩ * b
  have hf : Function.Injective f := by
    intro a b hab
    have h1 : (δ : Matrix (Fin n) (Fin n) F') * a = δ * b := congrArg Subtype.val hab
    apply Subtype.ext
    have h2 := congrArg (fun m => ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * m) h1
    simpa [← mul_assoc] using h2
  obtain ⟨b, hb⟩ := (Finite.injective_iff_surjective.1 hf) 1
  have hb' : (δ : Matrix (Fin n) (Fin n) F') * b = 1 := congrArg Subtype.val hb
  have : ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') = b := by
    calc ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')
        = ((δ⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') * (δ * b) := by rw [hb', mul_one]
      _ = b := by rw [← mul_assoc]; simp
  rw [this]; exact b.2

def unitsIn {n : ℕ} [Finite F'] (B : Subalgebra F' (Matrix (Fin n) (Fin n) F')) :
    Subgroup (GL (Fin n) F') where
  carrier := {δ | (δ : Matrix (Fin n) (Fin n) F') ∈ B}
  one_mem' := by simpa using B.one_mem
  mul_mem' := fun ha hb => by simpa using B.mul_mem ha hb
  inv_mem' := fun h => inv_mem_of_finite B _ h

theorem nrm_surj_adjoin : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'),
    (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (n : ℕ) (γ : GL (Fin n) F), ∃ δ : GL (Fin n) F',
      (δ : Matrix (Fin n) (Fin n) F') ∈
        Algebra.adjoin F' {((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F')} ∧
      nrm s δ = incl F F' n γ := by
  intro F F' _ _ _ _ s hs n γ
  set M : Matrix (Fin n) (Fin n) F' := ((incl F F' n γ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') with hM
  set B := Algebra.adjoin F' {M} with hB
  obtain ⟨hfix, hinj, -, hcomm4, hmul⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n
  have hcard := GlobalTheory.T.card_twistedNorm_one_mul_card_fixed_units F F' s hs n B (adjoin_stable n s γ)
  have hstab : ∀ (t : F' ≃ₐ[F] F') (δ : GL (Fin n) F'), δ ∈ unitsIn B → galAct F F' n t δ ∈ unitsIn B :=
    fun t δ h => by
      show ((galAct F F' n t δ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B
      rw [coe_galAct]; exact adjoin_stable n t γ _ h
  have hcommB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := adjoin_comm M
  have hcommU : ∀ δ ∈ unitsIn B, ∀ ε ∈ unitsIn B, δ * ε = ε * δ := fun δ hδ ε hε =>
    Units.ext (by simpa using hcommB _ hδ _ hε)
  have hnrm_mem : ∀ δ ∈ unitsIn B, nrm s δ ∈ unitsIn B := by
    intro δ hδ
    unfold nrm nrmG
    apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hx
    exact hstab _ _ hδ
  have hmulU : ∀ δ ∈ unitsIn B, ∀ ε ∈ unitsIn B, nrm s (δ * ε) = nrm s δ * nrm s ε :=
    fun δ hδ ε hε => hmul δ ε (fun t u => hcommU _ (hstab t δ hδ) _ (hstab u ε hε))
  let N : unitsIn B →* unitsIn B := MonoidHom.mk' (fun δ => ⟨nrm s δ, hnrm_mem δ δ.2⟩)
    (fun a b => Subtype.ext (hmulU a a.2 b b.2))
  have hfixN : ∀ δ ∈ unitsIn B, galAct F F' n s (nrm s δ) = nrm s δ := by
    intro δ hδ
    have h4 := hcomm4 δ
    rw [hcommU _ (hnrm_mem δ hδ) _ hδ] at h4
    exact mul_left_cancel h4
  let W : Set (unitsIn B) := {x | galAct F F' n s x = x}
  have hRW : (N.range : Set (unitsIn B)) ⊆ W := by
    rintro _ ⟨δ, rfl⟩
    exact hfixN δ δ.2
  have hVW : Nat.card {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B}
      = Nat.card W := by
    apply Nat.card_congr
    refine Equiv.ofBijective (fun x => ⟨⟨incl F F' n x.1, x.2⟩, (hfix _).2 ⟨x.1, rfl⟩⟩) ⟨?_, ?_⟩
    · intro a b h
      have := congrArg (fun y : W => ((y : unitsIn B) : GL (Fin n) F')) h
      exact Subtype.ext (hinj this)
    · rintro ⟨⟨x, hx⟩, hxW⟩
      obtain ⟨y, rfl⟩ := (hfix x).1 hxW
      exact ⟨⟨y, hx⟩, rfl⟩
  have hUc : Nat.card {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B} = Nat.card (unitsIn B) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
  have hKc : Nat.card {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1}
      = Nat.card N.ker := by
    apply Nat.card_congr
    exact
      { toFun := fun ε => ⟨⟨ε.1, ε.2.1⟩, (MonoidHom.mem_ker).2 (Subtype.ext ε.2.2)⟩
        invFun := fun ε => ⟨ε.1.1, ε.1.2, congrArg Subtype.val ((MonoidHom.mem_ker).1 ε.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hsplit : Nat.card N.ker * Nat.card N.range = Nat.card (unitsIn B) := by
    rw [← Subgroup.index_ker]; exact Subgroup.card_mul_index _
  have hKpos : 0 < Nat.card N.ker := Nat.card_pos
  have hVR : Nat.card W = Nat.card N.range := by
    rw [← hVW]
    rw [hKc, hUc, ← hsplit] at hcard
    exact Nat.eq_of_mul_eq_mul_left hKpos hcard
  have hEq : (N.range : Set (unitsIn B)) = W := by
    apply Set.eq_of_subset_of_ncard_le hRW
    · rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, hVR]; rfl
  have hmem : (⟨incl F F' n γ, Algebra.subset_adjoin rfl⟩ : unitsIn B) ∈ W := by
    show galAct F F' n s (incl F F' n γ) = incl F F' n γ
    exact (hfix _).2 ⟨γ, rfl⟩
  rw [← hEq] at hmem
  obtain ⟨δ, hδ⟩ := hmem
  exact ⟨δ, δ.2, congrArg Subtype.val hδ⟩

end GlobalTheory.Shin.NormSurj
end

section

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

theorem lineFin : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (n : ℕ) (g : Place k F → Matrix (Fin n) (Fin n) F), admitted g → {v : Place k F | ord v (g v).det ≠ 0}.Finite ∧ ∀ w : Fin n → F, w ≠ 0 → {v : Place k F | nrm v ((g v).mulVec w) ≠ 1}.Finite ∧ ∀ v, (g v).mulVec w ≠ 0 := by
  intro k F _ _ _ _ _ hFF n g hg
  obtain ⟨hdet, hfin⟩ := hg
  refine ⟨hfin.subset ?_, fun w hw => ⟨?_, fun v h => hw (Matrix.eq_zero_of_mulVec_eq_zero (hdet v) h)⟩⟩
  · intro v hv hu
    apply hv
    simp [ord, hu.2]
  · let S : Set (Place k F) := {v | ¬ Unimod v (g v)} ∪
      ⋃ i ∈ {i : Fin n | w i ≠ 0}, {v : Place k F | v.1 (w i) ≠ 1}
    have hS : S.Finite := hfin.union (Set.Finite.biUnion (Set.toFinite _)
      fun i hi => ((GlobalTheory.T.functionField_finite_support_sum_order_eq_zero k F hFF (w i) hi).1))
    refine hS.subset fun v hv => ?_
    by_contra hvS
    simp only [S, Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion, not_or, not_not, not_exists] at hvS
    obtain ⟨hu, hw1⟩ := hvS
    apply hv
    rw [(((GlobalTheory.T.functionFieldPlaceOrder_calculus k F v).2.2.2.2.2.2.2.2.1) n (g v) w hu)]
    obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
      by_contra h; push_neg at h; exact hw (funext h)
    have h1 : ∀ i, v.1 (w i) ≤ 1 := by
      intro i
      by_cases hi : w i = 0
      · simp [hi]
      · exact le_of_eq (hw1 i hi)
    apply le_antisymm
    · exact Finset.sup_le fun i _ => h1 i
    · have := Finset.le_sup (f := fun i => v.1 (w i)) (Finset.mem_univ i0)
      have e : v.1 (w i0) = 1 := hw1 i0 hi0
      rw [e] at this; exact this

end GlobalTheory.Nef
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleSpaceCohomology_baseChange_coprod_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (U : Over S) (ι : Type) (V : ι → Over S) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U.left (fun i => (j i).left)) → ∀ n : ℤ, Function.Bijective (fun (x : H R ((bc p).obj U) F n) (i : ι) => pull R ((bc p).map (j i)) F n x) := by
  first | (exact @GlobalTheory.EtC.BcCoprod.main) | (exact GlobalTheory.EtC.BcCoprod.main) | (intros; apply GlobalTheory.EtC.BcCoprod.main  <;> assumption)
end

section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.etale_holomorphic_iff_chart_holomorphic : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ (Ω : Set Y) (u : Y → ℂ), IsOpen Ω → ((∀ e : OpenPartialHomeomorph U (V n), IsChart n (fun y : U => z y) e → DifferentiableOn ℂ ((fun y : U => u y) ∘ e.symm) (e.target ∩ e.symm ⁻¹' (Subtype.val ⁻¹' Ω))) ↔ ∀ i, DifferentiableOn ℂ (u ∘ (A.chart i).symm) ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ Ω))) := by
  first | exact @GlobalTheory.OTY.holo_etale_iff_holo_chart | exact GlobalTheory.OTY.holo_etale_iff_holo_chart | (intros; apply GlobalTheory.OTY.holo_etale_iff_holo_chart <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleCohomologyEquivalence_basic_properties : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E E' : Spc) (f : E ⟶ E'), IsIso f → Eqv R f F) ∧ (∀ (E E' E'' : Spc) (f : E ⟶ E') (g : E' ⟶ E''), (Eqv R f F → Eqv R g F → Eqv R (f ≫ g) F) ∧ (Eqv R f F → Eqv R (f ≫ g) F → Eqv R g F) ∧ (Eqv R g F → Eqv R (f ≫ g) F → Eqv R f F)) ∧ (∀ (E E' : Spc) (f : E ⟶ E'), QuasiIso ((chains R).map f) → Eqv R f F) ∧ ∀ (E E' : Spc) (f : E ⟶ E'), Eqv R f F → (AcycF R E F ↔ AcycF R E' F) := by
  first | (exact @GlobalTheory.EtC.eqv_basic) | (exact GlobalTheory.EtC.eqv_basic) | (intros; apply GlobalTheory.EtC.eqv_basic  <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem _root_.GlobalTheory.T.etaleSheafOfRingFunctor_isFinitary : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)), PreservesFilteredColimitsOfSize.{0, 0} M → Finitary (ofRings R M) := by
  first
  | exact @GlobalTheory.ofRings_finitary
  | exact GlobalTheory.ofRings_finitary
  | (intros; apply GlobalTheory.ofRings_finitary <;> assumption)
end

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem _root_.GlobalTheory.T.exists_strictHenselization_at_maximal : ∀ (B : Type) [CommRing B] (P : Ideal B) [P.IsMaximal], IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime P)) → ∃ (O : Type) (_ : CommRing O) (_ : Algebra B O), SH O ∧ IndEt B O ∧ ∀ Q : Ideal O, Q.IsMaximal → Q.comap (algebraMap B O) = P ∧ ∀ o : O, ∃ b : B, o - algebraMap B O b ∈ Q := by
  first | (exact @GlobalTheory.HensMax.exists_strictHens_of_maximal) | (exact GlobalTheory.HensMax.exists_strictHens_of_maximal) | (intros; apply GlobalTheory.HensMax.exists_strictHens_of_maximal  <;> assumption)
end
