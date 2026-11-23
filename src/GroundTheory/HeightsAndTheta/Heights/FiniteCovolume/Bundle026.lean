module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle009
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle001
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle024
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle022
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.MajorantInvolutionDiagonalForm
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
public import Mathlib.Topology.Algebra.Group.Units
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PScalingLaw
public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Bundle012
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Examples

@[expose] public section

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def LineStabHaar.invUnits (b : InfinitePlace E → ℂ) : InfinitePlace E → ℂˣ :=
  fun w => if hb : b w = 0 then 1 else (Units.mk0 (b w) hb)⁻¹

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem LineStabHaar.invUnits_of_ne {b : InfinitePlace E → ℂ} (hb : ∀ w, b w ≠ 0) :
    invUnits b = fun w => (Units.mk0 (b w) (hb w))⁻¹ := by
  funext w
  simp [invUnits, hb w]

omit [NumberField E] [_root_.NumberField.IsTotallyComplex E] in
theorem LineStabHaar.measurable_invUnits : Measurable (invUnits (E := E)) := by
  have h0 : Measurable fun z : ℂ => if hz : z = 0 then (1 : ℂˣ) else (Units.mk0 z hz)⁻¹ := by
    refine measurable_iff_comap_le.2 ?_
    change MeasurableSpace.comap _ (MeasurableSpace.comap Units.val _) ≤ _
    rw [MeasurableSpace.comap_comp]
    have e : (Units.val ∘ fun z : ℂ => if hz : z = 0 then (1 : ℂˣ) else (Units.mk0 z hz)⁻¹) =
        fun z => if z = 0 then 1 else z⁻¹ := by
      funext z
      by_cases hz : z = 0 <;> simp [hz]
    rw [e]
    exact (Measurable.ite (measurableSet_singleton 0) measurable_const measurable_inv).comap_le
  exact Measurable.of_eval fun w => h0.comp (measurable_pi_apply w)


omit [NumberField F] [NumberField E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] [DecidableEq ι] in
theorem LineStabHaar.two_le_finrank {h : HermitianForm F E W} (v : Basis ι E W) {x₀ w₀ : W}
    (hx₀ : x₀ ≠ 0) (hp : IsHyperbolicPair h x₀ w₀) : 2 ≤ finrank E W := by
  have : Module.Finite E W := Module.Finite.of_basis v
  have hli : LinearIndependent E ![x₀, w₀] := by
    refine LinearIndependent.pair_iff.2 fun s t hst => ?_
    have e := congrArg (h.toSesq x₀) hst
    rw [map_add (f := _), map_smul, map_smul, hp.1, hp.2.2, map_zero, smul_zero, zero_add, smul_eq_mul,
      mul_one] at e
    subst e
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact ⟨hst.resolve_right hx₀, rfl⟩
  simpa using hli.fintype_card_le_finrank


omit [NumberField F] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] in
theorem LineStabHaar.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : WittPartner.Statement h) (h2 : VecAtNeZero.Statement v)
    (h3 : TorusEmbedding.Statement h v) (h4 : LineEigenvalue.Statement h v)
    (h5 : TorusModulus.Statement h v)
    (h6 : SemidirectHaar.Statement (archUnitary h v) (InfinitePlace E → ℂˣ))
    (h7 : UnitsInvHaar.Statement (InfinitePlace E)) : LineStabHaar.Statement h v := by
  classical
  intro x₀ hx₀ hiso μP _
  obtain ⟨w₀, hxw, hww⟩ := h1 x₀ hx₀ hiso
  have hp : IsHyperbolicPair h x₀ w₀ := ⟨hiso, hww, hxw⟩
  obtain ⟨τ₀, hτc, hτ⟩ := h3 x₀ w₀ hp
  obtain ⟨β, hβc, hβ⟩ := h4 x₀ hx₀
  have hN := LineStabHaar.two_le_finrank v hx₀ hp
  have hX := h2 x₀ hx₀
  have act : ∀ (g k : archUnitary h v) w (z : ι → ℂ),
      (((g * k : archUnitary h v) : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z =
        ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ
          (((k : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ z) := by
    intro g k w z
    simp [Matrix.mulVec_mulVec]
  have τinv : ∀ a w, ((((τ₀ a)⁻¹ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
      Matrix ι ι ℂ) *ᵥ vecAt v x₀ w = (((a w)⁻¹ : ℂˣ) : ℂ) • vecAt v x₀ w := by
    intro a w
    rw [← map_inv, (hτ a⁻¹ w).1, Pi.inv_apply]
  have hmemP : ∀ t, τ₀ t ∈ lineStab h v x₀ := fun t w => ⟨t w, (hτ t w).1⟩
  have hnorm : ∀ t, ∀ x ∈ vecFixGroup h v x₀, τ₀ t * x * (τ₀ t)⁻¹ ∈ vecFixGroup h v x₀ := by
    intro t x hx w
    rw [act, act, τinv, Matrix.mulVec_smul, Matrix.mulVec_smul, hx w, (hτ t w).1, smul_smul,
      Units.inv_mul, one_smul]
  have hinj : ∀ t, τ₀ t ∈ vecFixGroup h v x₀ → t = 1 := by
    intro t ht
    funext w
    have e := ht w
    rw [(hτ t w).1] at e
    have e' : ((t w : ℂ) - 1) • vecAt v x₀ w = 0 := by rw [sub_smul, one_smul, e, sub_self]
    exact Units.ext (sub_eq_zero.mp ((smul_eq_zero.mp e').resolve_right (hX w)))
  have hdec : ∀ p : lineStab h v x₀, (p : archUnitary h v) * (τ₀ (β p))⁻¹ ∈ vecFixGroup h v x₀ := by
    intro p w
    rw [act, τinv, Matrix.mulVec_smul, hβ p w, smul_smul, Units.inv_mul, one_smul]
  set N := finrank E W with hNdef
  let δ : (InfinitePlace E → ℂˣ) → ℝ≥0 := fun t => ∏ w, ‖(((t w)⁻¹ : ℂˣ) : ℂ)‖₊ ^ (2 * (N - 1))
  have hδc : Continuous δ := continuous_finsetProd _ fun w _ =>
    ((Units.continuous_coe_inv.comp (continuous_apply w)).nnnorm).pow _
  have hδcoe : ∀ t, (δ t : ℝ≥0∞) = ∏ w, ‖(t w : ℂ)‖ₑ⁻¹ ^ (2 * (N - 2 + 1)) := by
    intro t
    rw [show N - 2 + 1 = N - 1 by omega, ENNReal.ofNNReal_finsetProd]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [ENNReal.coe_pow, Units.val_inv_eq_inv_val, nnnorm_inv,
      ENNReal.coe_inv (nnnorm_ne_zero_iff.mpr (t w).ne_zero), enorm_eq_nnnorm]
  let ν₀ : Measure (vecFixGroup h v x₀) := Measure.haar
  let ρ : Measure (InfinitePlace E → ℂˣ) := Measure.haar
  have hδ : ∀ (t : InfinitePlace E → ℂˣ) (f : archUnitary h v → ℝ≥0∞), Measurable f →
      ∫⁻ x, f (τ₀ t * x * (τ₀ t)⁻¹) ∂ν₀ = δ t * ∫⁻ x, f x ∂ν₀ := by
    intro t f hf
    rw [hδcoe, show N - 2 + 1 = N - 1 by omega]
    exact h5 x₀ w₀ hp (τ₀ t) (fun w => (t w : ℂ)) (fun w => (hτ t w).1) (fun w => (hτ t w).2.1)
      (fun w z hz₁ hz₂ => (hτ t w).2.2 z hz₁ hz₂) ν₀ f hf
  obtain ⟨c, hc0, hc⟩ := h6 (lineStab h v x₀) (vecFixGroup h v x₀) (isClosed_lineStab h v x₀)
    (isClosed_vecFixGroup h v x₀) (vecFixGroup_le_lineStab h v x₀) τ₀ β δ hτc hβc hδc hmemP hnorm
    hinj hdec μP ν₀ ρ hδ
  obtain ⟨c', hc'0, hc'⟩ := h7 ρ
  let τ : (InfinitePlace E → ℂ) → archUnitary h v := fun b =>
    if ∀ w, b w ≠ 0 then τ₀ (LineStabHaar.invUnits b) else 1
  have hτb : ∀ b (hb : ∀ w, b w ≠ 0), τ b = τ₀ fun w => (Units.mk0 (b w) (hb w))⁻¹ := by
    intro b hb
    simp only [τ, if_pos hb, LineStabHaar.invUnits_of_ne hb]
  have hset : MeasurableSet {b : InfinitePlace E → ℂ | ∀ w, b w ≠ 0} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun w => (measurableSet_singleton (0 : ℂ)).compl.preimage
      (measurable_pi_apply w)
  refine ⟨((c * c' : ℝ≥0) : ℝ≥0∞) • ν₀, τ, Measure.IsHaarMeasure.smul _ (by simp [hc0, hc'0]) ENNReal.coe_ne_top,
    Measurable.ite hset (hτc.measurable.comp LineStabHaar.measurable_invUnits) measurable_const,
    fun b => ?_, fun b hb => ?_, fun φ hφ => ?_⟩
  · by_cases hb : ∀ w, b w ≠ 0
    · rw [hτb b hb]
      exact hmemP _
    · simp only [τ, if_neg hb]
      exact one_mem _
  · funext w
    rw [invApply, hτb b hb, ← map_inv, (hτ _ w).1]
    simp
  · have hg : Measurable fun t => ∫⁻ x : vecFixGroup h v x₀, φ (x * τ₀ t) ∂ν₀ :=
      Measurable.lintegral_prod_right' (f := fun q : (InfinitePlace E → ℂˣ) × vecFixGroup h v x₀ =>
        φ (q.2 * τ₀ q.1)) (hφ.comp ((continuous_subtype_val.comp continuous_snd).mul
          (hτc.comp continuous_fst)).measurable)
    have key := hc' (N - 2) (fun t => ∫⁻ x : vecFixGroup h v x₀, φ (x * τ₀ t) ∂ν₀)
      (fun b => ∫⁻ x : vecFixGroup h v x₀, φ (x * τ b) ∂ν₀) hg (fun b hb => by rw [hτb b hb])
    rw [hc φ hφ]
    simp_rw [hδcoe]
    rw [key]
    have e2 : ∀ b : InfinitePlace E → ℂ, (∏ w, ‖b w‖ₑ ^ (2 * (N - 2))) *
        ∫⁻ x : vecFixGroup h v x₀, φ (x * τ b) ∂(((c * c' : ℝ≥0) : ℝ≥0∞) • ν₀) =
        ((c * c' : ℝ≥0) : ℝ≥0∞) * ((∏ w, ‖b w‖ₑ ^ (2 * (N - 2))) *
          ∫⁻ x : vecFixGroup h v x₀, φ (x * τ b) ∂ν₀) := by
      intro b
      rw [lintegral_smul_measure, smul_eq_mul, mul_left_comm]
    simp_rw [e2]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ENNReal.coe_mul, mul_assoc]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def UnipotentCentral.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ w₀ : W), IsDIntegral h D La → x₀ ∈ La →
    IsHyperbolicPair h x₀ w₀ → ∀ K₁ : Set (InfinitePlace E → ι → ℂ), IsCompact K₁ →
    ∃ K : Set (InfinitePlace E → ι → ℂ), IsCompact K ∧ ∀ n : unipRadical h v x₀,
      (∃ t : InfinitePlace E → ℂ, unipCoord h v x₀ w₀ n - (fun w => t w • vecAt v x₀ w) ∈ K₁) →
      ∃ δ : unipRadical h v x₀, (δ : archUnitary h v) ∈ vecStabGroup h v La x₀ ∧
        unipCoord h v x₀ w₀ (δ * n) ∈ K

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

def UnipotentHorizontal.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (D : ℕ) (La : AddSubgroup W) (x₀ w₀ : W), IsDIntegral h D La → x₀ ∈ La →
    IsHyperbolicPair h x₀ w₀ →
    ∃ K : Set (InfinitePlace E → ι → ℂ), IsCompact K ∧ ∀ n : unipRadical h v x₀,
      ∃ δ : unipRadical h v x₀, (δ : archUnitary h v) ∈ vecStabGroup h v La x₀ ∧
        ∃ t : InfinitePlace E → ℂ,
          unipCoord h v x₀ w₀ (δ * n) - (fun w => t w • vecAt v x₀ w) ∈ K

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem UnipRadicalOfRational.proof (h : HermitianForm F E W) (v : Basis ι E W) :
    UnipRadicalOfRational.Statement h v := by
  classical
  intro x₀ γ hx hz
  have hγ : ∀ u : W, γ • u = (γ : W ≃ₗ[E] W) u := fun _ => rfl

  have key : ∃ y : W, ∀ u : W, ∃ a : E,
      γ • u = u + h.toSesq x₀ u • (γ • y - y) + a • x₀ := by
    by_cases hy : ∃ y, h.toSesq x₀ y = 1
    · obtain ⟨y, hy⟩ := hy
      refine ⟨y, fun u => ?_⟩
      obtain ⟨a, ha⟩ := hz (u - h.toSesq x₀ u • y)
        (by rw [map_sub, map_smul, smul_eq_mul, hy, mul_one, sub_self])
      have hs : γ • (u - h.toSesq x₀ u • y) = γ • u - h.toSesq x₀ u • (γ • y) := by
        simp only [hγ, map_sub, map_smul]
      rw [hs] at ha
      refine ⟨a, ?_⟩
      rw [smul_sub, sub_eq_iff_eq_add.mp ha]
      abel
    · refine ⟨0, fun u => ?_⟩
      have h0 : h.toSesq x₀ u = 0 := by
        by_contra hu
        exact hy ⟨(h.toSesq x₀ u)⁻¹ • u, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu]⟩
      obtain ⟨a, ha⟩ := hz u h0
      exact ⟨a, by simp [ha]⟩
  obtain ⟨y, hy⟩ := key
  choose a ha using fun j => hy (v j)
  rw [mem_unipRadical]
  intro w
  set M : Matrix ι ι ℂ := (((archEmbed h v γ : archUnitary h v) : InfinitePlace E → GL ι ℂ) w :
    Matrix ι ι ℂ) with hM
  have hvec : ∀ x : W, M *ᵥ vecAt v x w = vecAt v (γ • x) w := fun x =>
    congrFun (archEmbed_smul_vecAt h v γ x) w

  have hcol : ∀ i j, M i j = w.embedding (v.repr (γ • v j) i) := by
    intro i j
    have := congrFun (hvec (v j)) i
    simpa [vecAt, Basis.repr_self, Finsupp.single_apply, mulVec, dotProduct, apply_ite,
      eq_comm] using this
  refine ⟨by rw [hvec, hx], fun z hz0 => ?_⟩

  have hℓ : ∑ j, w.embedding (h.toSesq x₀ (v j)) * z j = 0 := by
    rw [← hz0]
    have hH : ∀ j, w.embedding (h.toSesq x₀ (v j)) =
        ∑ i, star (vecAt v x₀ w i) * gramAt h v w i j := by
      intro j
      rw [HermAtPlace.proof h v w x₀ (v j)]
      simp [vecAt, Basis.repr_self, Finsupp.single_apply, mulVec, dotProduct, apply_ite]
    simp only [hH, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul, Pi.star_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨∑ j, w.embedding (a j) * z j, ?_⟩
  funext i
  have hrow : (M *ᵥ z) i = ∑ j, (w.embedding (if i = j then 1 else 0) +
      w.embedding (h.toSesq x₀ (v j)) * w.embedding (v.repr (γ • y - y) i) +
      w.embedding (a j) * w.embedding (v.repr x₀ i)) * z j := by
    simp only [mulVec, dotProduct, hcol]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ha j]
    simp [Basis.repr_self, Finsupp.single_apply, eq_comm]
  rw [hrow]
  simp only [add_mul, Finset.sum_add_distrib]
  have e1 : ∑ j, w.embedding (if i = j then 1 else 0) * z j = z i := by
    simp [apply_ite]
  have e2 : ∑ j, w.embedding (h.toSesq x₀ (v j)) * w.embedding (v.repr (γ • y - y) i) * z j =
      w.embedding (v.repr (γ • y - y) i) * ∑ j, w.embedding (h.toSesq x₀ (v j)) * z j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : ∑ j, w.embedding (a j) * w.embedding (v.repr x₀ i) * z j =
      (∑ j, w.embedding (a j) * z j) * w.embedding (v.repr x₀ i) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, e3, hℓ]
  simp [vecAt]

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end

section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [NumberField E]

def LineEigenvalue.coordRatio (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W)
    (i : InfinitePlace E → ι) (g : archUnitary h v) (w : InfinitePlace E) : ℂ :=
  ((((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) (i w)) / vecAt v x₀ w (i w)


omit [NumberField E] in
theorem LineEigenvalue.continuous_coordRatio (h : HermitianForm F E W) (v : Basis ι E W) (x₀ : W)
    (i : InfinitePlace E → ι) (w : InfinitePlace E) :
    Continuous fun g : archUnitary h v => coordRatio h v x₀ i g w := by
  unfold coordRatio
  refine Continuous.div_const ?_ _
  exact (continuous_apply (i w)).comp
    ((Units.continuous_val.comp ((continuous_apply w).comp continuous_subtype_val)).matrix_mulVec
      continuous_const)


omit [NumberField E] in
theorem LineEigenvalue.mulVec_eq_coordRatio {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {i : InfinitePlace E → ι} (hi : ∀ w, vecAt v x₀ w (i w) ≠ 0) {g : archUnitary h v}
    (hg : g ∈ lineStab h v x₀) (w : InfinitePlace E) :
    ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w =
      coordRatio h v x₀ i g w • vecAt v x₀ w := by
  obtain ⟨c, hc⟩ := hg w
  have e : coordRatio h v x₀ i g w = c := by
    rw [coordRatio, hc, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self (hi w), mul_one]
  rw [e, hc]

theorem LineEigenvalue.coordRatio_ne_zero {h : HermitianForm F E W} {v : Basis ι E W} {x₀ : W}
    {i : InfinitePlace E → ι} (hi : ∀ w, vecAt v x₀ w (i w) ≠ 0) {g : archUnitary h v}
    (hg : g ∈ lineStab h v x₀) (w : InfinitePlace E) : coordRatio h v x₀ i g w ≠ 0 := by
  intro h0
  have e := mulVec_eq_coordRatio hi hg w
  rw [h0, zero_smul] at e
  apply hi w
  have hX : vecAt v x₀ w = (((((g : InfinitePlace E → GL ι ℂ) w)⁻¹ : GL ι ℂ) : Matrix ι ι ℂ) *ᵥ
      (((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w)) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  rw [hX, e, Matrix.mulVec_zero, Pi.zero_apply]

theorem LineEigenvalue.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h1 : VecAtNeZero.Statement v) : LineEigenvalue.Statement h v := by
  intro x₀ hx₀
  have hne : ∀ w, ∃ j, vecAt v x₀ w j ≠ 0 := fun w => by
    simpa using Function.ne_iff.mp (h1 x₀ hx₀ w)
  choose i hi using hne
  refine ⟨fun p w => Units.mk0 (coordRatio h v x₀ i (p : archUnitary h v) w)
    (coordRatio_ne_zero hi p.2 w), ?_, fun p w => ?_⟩
  · refine continuous_pi fun w => Units.continuous_iff.2 ⟨?_, ?_⟩
    · exact (continuous_coordRatio h v x₀ i w).comp continuous_subtype_val
    · simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
      exact ((continuous_coordRatio h v x₀ i w).comp continuous_subtype_val).inv₀
        fun p => coordRatio_ne_zero hi p.2 w
  · rw [Units.val_mk0]
    exact mulVec_eq_coordRatio hi p.2 w

theorem LineEigenvalue.closed (h : HermitianForm F E W) (v : Basis ι E W) :
    LineEigenvalue.Statement h v :=
  LineEigenvalue.proof h v (VecAtNeZero.proof v)

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
end
