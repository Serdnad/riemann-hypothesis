module

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle056
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle001
public import Formalism.WeaklyAdmissibleFiltrations.Statement
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.BruhatFunctionExistsClosedSubgroup
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

section

open Matrix

noncomputable section

namespace GlobalTheory.Tw.Model

variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]

omit [StarRing R] in
theorem Phi_apply' (i j : Fin n) : Phi n R i j = if j = i.rev then (-1) ^ (i : ℕ) else 0 := by
  simp only [Phi, Matrix.of_apply]
  congr 1
  apply propext
  rw [Fin.ext_iff, Fin.val_rev]
  have := i.2
  have := j.2
  omega

omit [StarRing R] in
theorem Phi_mul_transpose : Phi n R * (Phi n R)ᵀ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Phi_apply', ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_inj, Matrix.one_apply]
  split_ifs with h
  · subst h
    rw [← pow_add, ← two_mul, pow_mul]; simp
  · simp

omit [StarRing R] in
theorem transpose_mul_Phi : (Phi n R)ᵀ * Phi n R = 1 := mul_eq_one_comm.mp Phi_mul_transpose

theorem Phi_conjTranspose : (Phi n R)ᴴ = (Phi n R)ᵀ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Phi_apply']
  split_ifs <;> simp

omit [StarRing R] in
theorem Phi_transpose : (Phi n R)ᵀ = ((-1 : R) ^ (n - 1)) • Phi n R := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.smul_apply, Phi, Matrix.of_apply, smul_eq_mul]
  by_cases h : (i : ℕ) + (j : ℕ) + 1 = n
  · rw [if_pos h, if_pos (by omega)]
    have : n - 1 = i + j := by omega
    rw [this, ← pow_add, show (i : ℕ) + j + i = 2 * i + j by ring, pow_add, pow_mul]; simp
  · rw [if_neg h, if_neg (by omega)]; simp

theorem theta_one : theta (1 : Matrix (Fin n) (Fin n) R) = 1 := by
  simp [theta, Phi_mul_transpose]

theorem theta_mul (g h : Matrix (Fin n) (Fin n) R) : theta (g * h) = theta g * theta h := by
  simp only [theta, Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Phi n R)ᵀ (Phi n R), transpose_mul_Phi, Matrix.one_mul]

theorem theta_mul_theta_inv {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) :
    theta g * theta g⁻¹ = 1 := by
  rw [← theta_mul, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det g).mp hg), theta_one]

theorem theta_inv_eq {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) :
    (theta g)⁻¹ = Phi n R * gᴴ * (Phi n R)ᵀ := by
  rw [Matrix.inv_eq_right_inv (theta_mul_theta_inv hg), theta,
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det g).mp hg)]

theorem theta_theta {g : Matrix (Fin n) (Fin n) R} (hg : IsUnit g) : theta (theta g) = g := by
  apply GlobalTheory.Tw.PhiConjugateTranspose.theta_theta <;> assumption

theorem adj_eq {δ g : Matrix (Fin n) (Fin n) R} (hδ : IsUnit δ) (hg : IsUnit g) :
    adj δ g = (δ * theta g * δ⁻¹)⁻¹ := by
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, theta_inv_eq hg,
    Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det δ).mp hδ), adj]
  simp only [Matrix.mul_assoc]

end GlobalTheory.Tw.Model
end
end

section

noncomputable section

namespace GlobalTheory.HyodoDef

open Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)
    [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

def geometricCocycles : Submodule LL (G → V) where
  carrier := {c | c ∈ continuousCocycles ρ ∧ ∃ b : V ⊗[Qp] BdR, ∀ g, c g ⊗ₜ[Qp] (1 : BdR) = actVdR PD ρ g b - b}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, 0, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, x, hx⟩ ⟨hb, y, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, x + y, fun g => ?_⟩
    simp only [Pi.add_apply, add_tmul, hx, hy, map_add (f := _)]
    abel
  smul_mem' := by
    rintro c a ⟨ha, x, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, c • x, fun g => ?_⟩
    simp only [Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

def crystallineCocycles : Submodule LL (G → V) where
  carrier := {c | c ∈ continuousCocycles ρ ∧ ∃ x : V ⊗[Qp] B, φVB PD (LL := LL) (V := V) x = x ∧
    ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x}
  zero_mem' := ⟨(continuousCocycles ρ).zero_mem, 0, map_zero _, fun g => by simp⟩
  add_mem' := by
    rintro a b ⟨ha, x, hxφ, hx⟩ ⟨hb, y, hyφ, hy⟩
    refine ⟨(continuousCocycles ρ).add_mem ha hb, x + y, by rw [map_add (f := _), hxφ, hyφ], fun g => ?_⟩
    simp only [Pi.add_apply, add_tmul, hx, hy, map_add (f := _)]
    abel
  smul_mem' := by
    rintro c a ⟨ha, x, hxφ, hx⟩
    refine ⟨(continuousCocycles ρ).smul_mem c ha, c • x, by rw [map_smul, hxφ], fun g => ?_⟩
    simp only [Pi.smul_apply, map_smul, ← smul_sub, ← hx]
    rfl

end GlobalTheory.HyodoDef

end
end

section

open MeasureTheory Topology
open scoped ENNReal

noncomputable section

namespace GlobalTheory.Tw

section Defs
variable {G : Type} [Group G] [MeasurableSpace G]

abbrev RCoset (T : Subgroup G) : Type := Quotient (QuotientGroup.rightRel T)

def IsQuotMeasure (T : Subgroup G) (μ : Measure G) (μT : Measure T) (ν : Measure (RCoset T)) : Prop :=
  ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μ = ∫⁻ c, ∫⁻ t : T, f (t * Quotient.out c) ∂μT ∂ν

def IsCosetCutoff (T : Subgroup G) (μT : Measure T) (β : G → NNReal) : Prop :=
  Measurable β ∧ ∀ x, ∫⁻ t : T, β (t * x) ∂μT = 1

def quotMeas (T : Subgroup G) (μ : Measure G) (μT : Measure T) : Measure (RCoset T) :=
  Classical.epsilon (IsQuotMeasure T μ μT)

def quotInt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : Subgroup G) (μ : Measure G) (μT : Measure T)
    (F : G → E) : E :=
  ∫ c, F (Quotient.out c) ∂quotMeas T μ μT

def QuotIntegrable {E : Type} [NormedAddCommGroup E] (T : Subgroup G) (μ : Measure G) (μT : Measure T)
    (F : G → E) : Prop :=
  Integrable (fun c : RCoset T => F (Quotient.out c)) (quotMeas T μ μT)


omit [MeasurableSpace G] in
theorem apply_out_mk {T : Subgroup G} {α : Type} {F : G → α} (hF : ∀ t ∈ T, ∀ x, F (t * x) = F x) (x : G) :
    F (Quotient.out (Quotient.mk (QuotientGroup.rightRel T) x)) = F x := by
  have h := Quotient.mk_out (s := QuotientGroup.rightRel T) x
  rw [QuotientGroup.rightRel_apply] at h
  have := hF _ h (Quotient.out (Quotient.mk (QuotientGroup.rightRel T) x))
  rw [inv_mul_cancel_right] at this
  exact this.symm

theorem measurable_comp_out {T : Subgroup G} {α : Type} [MeasurableSpace α] {F : G → α} (hm : Measurable F)
    (hF : ∀ t ∈ T, ∀ x, F (t * x) = F x) : Measurable fun c : RCoset T => F (Quotient.out c) := by
  refine measurable_from_quotient.2 ?_
  have : (fun c : RCoset T => F (Quotient.out c)) ∘ Quotient.mk'' = F := funext (apply_out_mk hF)
  rwa [this]

end Defs

section Exist
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {T : Subgroup G} {μ : Measure G} {μT : Measure T}


omit [SecondCountableTopology G] in
theorem exists_isCosetCutoff [LocallyCompactSpace G] [T2Space G] (hT : IsClosed (T : Set G)) [μT.IsHaarMeasure]
    [μT.IsInvInvariant] : ∃ β : G → NNReal, Continuous β ∧ IsCosetCutoff T μT β := by
  obtain ⟨β, hc, h0, -, h1⟩ := GlobalTheory.bruhatFunctionExists_closedSubgroup G T hT μT inferInstance
  have hcont : Continuous fun x => (β x⁻¹).toNNReal := continuous_real_toNNReal.comp (hc.comp continuous_inv)
  refine ⟨fun x => (β x⁻¹).toNNReal, hcont, hcont.measurable, fun x => ?_⟩
  have hi : Integrable (fun h : T => β (x⁻¹ * h)) μT := by
    by_contra hn
    have := h1 x⁻¹
    rw [integral_undef hn] at this
    exact zero_ne_one this
  have h2 := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun h => h0 _)
  rw [h1, ENNReal.ofReal_one, ← lintegral_inv_eq_self] at h2
  rw [h2]
  simp [ENNReal.ofReal]

theorem IsCosetCutoff.isQuotMeasure [SFinite μ] [μ.IsMulLeftInvariant] [SFinite μT] [μT.IsMulLeftInvariant]
    [μT.IsInvInvariant] {β : G → NNReal} (hβ : IsCosetCutoff T μT β) :
    IsQuotMeasure T μ μT ((μ.withDensity fun x => β x).map (Quotient.mk (QuotientGroup.rightRel T))) := by
  intro f hf
  have hb : Measurable fun x => (β x : ℝ≥0∞) := hβ.1.coe_nnreal_ennreal
  have hmul : Measurable fun p : G × T => (p.2 : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
  have hmul' : Measurable fun p : G × T => ((p.2⁻¹ : T) : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd.inv).mul measurable_fst
  have : μT.IsMulRightInvariant := by
    rw [← Measure.inv_eq_self μT]; infer_instance
  have hF : Measurable fun x => ∫⁻ t : T, f (t * x) ∂μT := (hf.comp hmul).lintegral_prod_right'
  have hinv : ∀ s ∈ T, ∀ x, ∫⁻ t : T, f (t * (s * x)) ∂μT = ∫⁻ t : T, f (t * x) ∂μT := fun s hs x => by
    rw [← lintegral_mul_right_eq_self (μ := μT) (fun t : T => f (t * x)) ⟨s, hs⟩]
    simp [mul_assoc]
  have hmk : Measurable (Quotient.mk (QuotientGroup.rightRel T)) := measurable_quotient_mk''
  rw [lintegral_map (measurable_comp_out hF hinv) hmk,
    lintegral_withDensity_eq_lintegral_mul _ hb (g := fun a => ∫⁻ t : T,
      f (t * Quotient.out (Quotient.mk (QuotientGroup.rightRel T) a)) ∂μT) ((measurable_comp_out hF hinv).comp hmk)]
  have e1 : ∀ x, ((fun x => (β x : ℝ≥0∞)) * fun a => ∫⁻ t : T,
      f (t * Quotient.out (Quotient.mk (QuotientGroup.rightRel T) a)) ∂μT) x = ∫⁻ t : T, β x * f (t * x) ∂μT := fun x => by
    rw [Pi.mul_apply, apply_out_mk (F := fun x => ∫⁻ t : T, f (t * x) ∂μT) hinv, lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  rw [lintegral_congr e1, lintegral_lintegral_swap ((hb.comp measurable_fst).mul (hf.comp hmul)).aemeasurable]
  have e2 : ∀ t : T, ∫⁻ x, β x * f (t * x) ∂μ = ∫⁻ x, β ((t⁻¹ : T) * x) * f x ∂μ := fun t => by
    rw [← lintegral_mul_left_eq_self (μ := μ) (fun x => β ((t⁻¹ : T) * x) * f x) t]
    simp
  rw [lintegral_congr e2,
    ← lintegral_lintegral_swap (f := fun x (t : T) => β ((t⁻¹ : T) * x) * f x)
      ((hb.comp hmul').mul (hf.comp measurable_fst)).aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [lintegral_mul_const _ (f := fun t : T => (β ((t⁻¹ : T) * x) : ℝ≥0∞)) (hb.comp (hmul'.comp (measurable_prodMk_left))),
    lintegral_inv_eq_self (μ := μT) (fun t : T => (β (t * x) : ℝ≥0∞)), hβ.2, one_mul]


omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [BorelSpace G] in
theorem IsQuotMeasure.eq_map {ν : Measure (RCoset T)} (hν : IsQuotMeasure T μ μT ν) {β : G → NNReal}
    (hβ : IsCosetCutoff T μT β) :
    ν = (μ.withDensity fun x => β x).map (Quotient.mk (QuotientGroup.rightRel T)) := by
  have hb : Measurable fun x => (β x : ℝ≥0∞) := hβ.1.coe_nnreal_ennreal
  ext S hS
  have hS' : MeasurableSet (Quotient.mk (QuotientGroup.rightRel T) ⁻¹' S) := measurable_quotient_mk'' hS
  rw [Measure.map_apply measurable_quotient_mk'' hS, withDensity_apply _ hS', ← lintegral_indicator hS',
    hν _ (hb.indicator hS'), ← lintegral_indicator_one hS]
  refine lintegral_congr fun c => ?_
  have hq : ∀ t : T, Quotient.mk (QuotientGroup.rightRel T) (t * c.out) = c := fun t => by
    conv_rhs => rw [← c.out_eq]
    refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
    simp
  by_cases hc : c ∈ S
  · simp [Set.indicator, hq, hc, hβ.2]
  · simp [Set.indicator, hq, hc]

variable [LocallyCompactSpace G] [T2Space G] [SFinite μ] [μ.IsMulLeftInvariant] [μT.IsHaarMeasure] [μT.IsInvInvariant]

theorem isQuotMeasure_quotMeas (hT : IsClosed (T : Set G)) : IsQuotMeasure T μ μT (quotMeas T μ μT) := by
  obtain ⟨β, -, hβ⟩ := exists_isCosetCutoff (μT := μT) hT
  have : LocallyCompactSpace T := hT.locallyCompactSpace
  have : SecondCountableTopology T := TopologicalSpace.Subtype.secondCountableTopology (T : Set G)
  exact Classical.epsilon_spec ⟨_, hβ.isQuotMeasure⟩

theorem quotInt_eq_cutoff (hT : IsClosed (T : Set G)) {β : G → NNReal} (hβ : IsCosetCutoff T μT β) {F : G → ℂ}
    (hm : Measurable F) (hF : ∀ t ∈ T, ∀ x, F (t * x) = F x) : quotInt T μ μT F = ∫ x, (β x : ℝ) • F x ∂μ := by
  rw [quotInt, (isQuotMeasure_quotMeas hT).eq_map hβ,
    integral_map measurable_quotient_mk''.aemeasurable (measurable_comp_out hm hF).aestronglyMeasurable,
    integral_withDensity_eq_integral_smul hβ.1]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [apply_out_mk hF]; rfl)

theorem quotIntegrable_iff_cutoff (hT : IsClosed (T : Set G)) {β : G → NNReal} (hβ : IsCosetCutoff T μT β) {F : G → ℂ}
    (hm : Measurable F) (hF : ∀ t ∈ T, ∀ x, F (t * x) = F x) :
    QuotIntegrable T μ μT F ↔ Integrable (fun x => (β x : ℝ) • F x) μ := by
  rw [QuotIntegrable, (isQuotMeasure_quotMeas hT).eq_map hβ,
    integrable_map_measure (measurable_comp_out hm hF).aestronglyMeasurable measurable_quotient_mk''.aemeasurable,
    integrable_withDensity_iff_integrable_smul hβ.1]
  exact integrable_congr (Filter.Eventually.of_forall fun x => by simp only [Function.comp, apply_out_mk hF]; rfl)

end Exist

end GlobalTheory.Tw
end
end
