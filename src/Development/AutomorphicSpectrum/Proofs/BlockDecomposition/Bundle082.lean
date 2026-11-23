module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Formalism.UnipotentAdelicQuotients.SWXSDefs
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle008
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import GroundTheory.LocalFields.UnitsBasic
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle015
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle014
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.SetTheory.Cardinal.Finite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle041
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
import Mathlib.Topology.Sheaves.Init
import Formalism.ConjugateSelfDual.Bundle001
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section

section

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix TensorProduct

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def hermE (σ : E →ₐ[F] E) (n : ℕ) : Submodule F (Matrix (Fin n) (Fin n) E) where
  carrier := {c | ∀ a b, σ (c b a) = c a b}
  add_mem' := by
    intro c d hc hd a b
    simp [map_add (f := _), hc a b, hd a b]
  zero_mem' := by
    intro a b
    simp
  smul_mem' := by
    intro t c hc a b
    simp [hc a b]

def hermIn (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (n : ℕ) :
    hermE σ n →+ HermR R σ n where
  toFun c := hermOf R σ c.1 c.2
  map_zero' := by
    apply Subtype.ext
    ext a b
    simp [hermOf]
  map_add' := by
    intro c d
    apply Subtype.ext
    ext a b
    simp [hermOf]

variable [NumberField E]

def hermO (σ : E →ₐ[F] E) (n : ℕ) : AddSubgroup (hermE σ n) where
  carrier := {c | ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = c.1 a b}
  add_mem' := by
    intro c d hc hd a b
    obtain ⟨o, ho⟩ := hc a b
    obtain ⟨p, hp⟩ := hd a b
    exact ⟨o + p, by simp [ho, hp]⟩
  zero_mem' := fun a b => ⟨0, by simp⟩
  neg_mem' := by
    intro c hc a b
    obtain ⟨o, ho⟩ := hc a b
    exact ⟨-o, by simp [ho]⟩

def Kc {n : ℕ} (c : Matrix (Fin n) (Fin n) E) : AddSubgroup (Fin n → 𝓞 E) where
  carrier := {y | ∀ i, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (c *ᵥ fun j => algebraMap (𝓞 E) E (y j)) i}
  add_mem' := by
    intro y z hy hz i
    obtain ⟨o, ho⟩ := hy i
    obtain ⟨p, hp⟩ := hz i
    refine ⟨o + p, ?_⟩
    have : (fun j => algebraMap (𝓞 E) E ((y + z) j)) =
        (fun j => algebraMap (𝓞 E) E (y j)) + fun j => algebraMap (𝓞 E) E (z j) := by
      funext j
      simp
    rw [this, Matrix.mulVec_add, Pi.add_apply, ← ho, ← hp, map_add (f := _)]
  zero_mem' := fun i => ⟨0, by
    have h0 : (fun _ : Fin n => (0 : E)) = 0 := rfl
    simp [h0, Matrix.mulVec_zero]⟩
  neg_mem' := by
    intro y hy i
    obtain ⟨o, ho⟩ := hy i
    refine ⟨-o, ?_⟩
    have : (fun j => algebraMap (𝓞 E) E ((-y) j)) = -fun j => algebraMap (𝓞 E) E (y j) := by
      funext j
      simp
    rw [this, Matrix.mulVec_neg, Pi.neg_apply, ← ho, map_neg]

def delta {n : ℕ} (c : Matrix (Fin n) (Fin n) E) : ℕ := (Kc c).index

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
end
end

section

open HeckeCharacterZeroLocus.SiegelWeilU
open scoped Matrix

namespace GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry

open GlobalTheory.CompanionTheory.SW.QuasiRefl

section Form

variable {A : Type} [CommRing A] {N : ℕ} {τ : A →+* A} {H : Matrix (Fin N) (Fin N) A}

theorem hform_add_fst (x x' y : Fin N → A) :
    hform τ H (x + x') y = hform τ H x y + hform τ H x' y := by
  have h : (τ ∘ (x + x')) = τ ∘ x + τ ∘ x' := by
    funext i
    simp
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, h, add_dotProduct]

theorem hform_add_snd (x y y' : Fin N → A) :
    hform τ H x (y + y') = hform τ H x y + hform τ H x y' := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, Matrix.mulVec_add, dotProduct_add]

theorem hform_sub_fst (x x' y : Fin N → A) :
    hform τ H (x - x') y = hform τ H x y - hform τ H x' y := by
  have h : (τ ∘ (x - x')) = τ ∘ x - τ ∘ x' := by
    funext i
    simp
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, h, sub_dotProduct]

theorem hform_sub_snd (x y y' : Fin N → A) :
    hform τ H x (y - y') = hform τ H x y - hform τ H x y' := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot, Matrix.mulVec_sub, dotProduct_sub]

theorem hform_unitary {g : GL (Fin N) A} (hg : g ∈ UJ τ H) (x y : Fin N → A) :
    hform τ H ((g : Matrix (Fin N) (Fin N) A) *ᵥ x) ((g : Matrix (Fin N) (Fin N) A) *ᵥ y) =
      hform τ H x y := by
  rw [hform_mulVec']
  have hg' : cT τ (g : Matrix (Fin N) (Fin N) A) * H * (g : Matrix (Fin N) (Fin N) A) = H := hg
  rw [hg']

theorem carry (hτ : ∀ y, τ (τ y) = y)
    (hcar : ∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1)
    (hH : ∀ i j, τ (H j i) = H i j) (x y : Fin N → A)
    (hxy : hform τ H x x = hform τ H y y) (hβ : IsUnit (hform τ H x x)) :
    ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ x = y ∧
      ∀ z, hform τ H x z = 0 → hform τ H y z = 0 → (g : Matrix (Fin N) (Fin N) A) *ᵥ z = z := by
  have hfix : τ (hform τ H x x) = hform τ H x x := hform_conj_symm hτ hH x x
  obtain ⟨ε, z, hε, hz⟩ := hcar (hform τ H y x) (hform τ H x x) hβ hfix
  exact exists_unitary_carry A τ hτ N H hH x y ε hxy hβ hε ⟨⟨_, z, hz, (mul_comm z _).trans hz⟩, rfl⟩

theorem exists_hyperbolic_partner (hτ : ∀ y, τ (τ y) = y) (h2 : IsUnit (2 : A))
    {Hi : Matrix (Fin N) (Fin N) A} (hHi : H * Hi = 1) (hH : ∀ i j, τ (H j i) = H i j)
    (y a : Fin N → A) (hyy : hform τ H y y = 0) (hay : ∑ k, a k * y k = 1) :
    ∃ y₁ : Fin N → A, hform τ H y₁ y₁ = 0 ∧ hform τ H y y₁ = 1 := by
  have hyw : hform τ H y (Hi *ᵥ (τ ∘ a)) = 1 := by
    rw [hform_eq_dot, Matrix.mulVec_mulVec, hHi, Matrix.one_mulVec]
    have h : (τ ∘ y) ⬝ᵥ (τ ∘ a) = τ (∑ k, a k * y k) := by

      simp only [dotProduct, Function.comp_apply, map_sum, map_mul]
      exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    rw [h, hay, map_one]
  have hwy : hform τ H (Hi *ᵥ (τ ∘ a)) y = 1 := by
    rw [← hform_conj_symm hτ hH y (Hi *ᵥ (τ ∘ a)), hyw, map_one]
  have hww : τ (hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a))) =
      hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a)) := hform_conj_symm hτ hH _ _
  have ht2 : 2 * (↑h2.unit⁻¹ : A) = 1 := h2.mul_val_inv
  have hτt : τ (↑h2.unit⁻¹ : A) = ↑h2.unit⁻¹ := by
    have h1 : τ (↑h2.unit⁻¹ : A) * 2 = 1 := by
      have h := congrArg τ ht2
      rw [map_mul, map_one, map_ofNat] at h
      rw [mul_comm]
      exact h
    calc τ (↑h2.unit⁻¹ : A) = τ (↑h2.unit⁻¹ : A) * (2 * ↑h2.unit⁻¹) := by rw [ht2, mul_one]
      _ = (τ (↑h2.unit⁻¹ : A) * 2) * ↑h2.unit⁻¹ := by ring
      _ = ↑h2.unit⁻¹ := by rw [h1, one_mul]
  have hτc : τ ((↑h2.unit⁻¹ : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a))) =
      (↑h2.unit⁻¹ : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a)) := by
    rw [map_mul, hτt, hww]
  refine ⟨Hi *ᵥ (τ ∘ a) - ((↑h2.unit⁻¹ : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a))) • y, ?_, ?_⟩
  · rw [hform_sub_left, hform_sub_right, hform_sub_right, hyy, hwy, hyw, hτc]
    linear_combination (-1 : A) * hform τ H (Hi *ᵥ (τ ∘ a)) (Hi *ᵥ (τ ∘ a)) * ht2
  · rw [hform_sub_right, hyw, hyy, mul_zero, sub_zero]

end Form

theorem exists_unitary_carry_primitive :
    ∀ (A : Type) [CommRing A] (τ : A →+* A), (∀ y, τ (τ y) = y) → IsUnit (2 : A) →
    (∀ p β : A, IsUnit β → τ β = β → ∃ ε z : A, ε * τ ε = 1 ∧ (β - τ ε * p) * z = 1) →
    ∀ (N : ℕ) (H Hi : Matrix (Fin N) (Fin N) A), H * Hi = 1 → (∀ i j, τ (H j i) = H i j) →
    ∀ e f y a : Fin N → A, hform τ H e e = 0 → hform τ H f f = 0 → hform τ H e f = 1 →
    hform τ H y y = 0 → ∑ k, a k * y k = 1 →
    ∃ g ∈ UJ τ H, (g : Matrix (Fin N) (Fin N) A) *ᵥ e = y := by
  intro A _ τ hτ h2 hcar N H Hi hHi hH e f y a hee hff hef hyy hay
  obtain ⟨y₁, hy₁, hyy₁⟩ := exists_hyperbolic_partner hτ h2 hHi hH y a hyy hay
  have hfe : hform τ H f e = 1 := by rw [← hform_conj_symm hτ hH e f, hef, map_one]
  have hy₁y : hform τ H y₁ y = 1 := by rw [← hform_conj_symm hτ hH y y₁, hyy₁, map_one]
  have hx1 : hform τ H (e + f) (e + f) = 2 := by
    rw [hform_add_fst, hform_add_snd, hform_add_snd, hee, hef, hfe, hff]
    norm_num
  have hy1 : hform τ H (y + y₁) (y + y₁) = 2 := by
    rw [hform_add_fst, hform_add_snd, hform_add_snd, hyy, hyy₁, hy₁y, hy₁]
    norm_num
  obtain ⟨g₁, hg₁, hg₁x, -⟩ := carry hτ hcar hH (e + f) (y + y₁) (by rw [hx1, hy1]) (by rw [hx1]; exact h2)
  have hvv : hform τ H ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) = -2 := by
    rw [hform_unitary hg₁, hform_sub_fst, hform_sub_snd, hform_sub_snd, hee, hef, hfe, hff]
    ring
  have hyy' : hform τ H (y - y₁) (y - y₁) = -2 := by
    rw [hform_sub_fst, hform_sub_snd, hform_sub_snd, hyy, hyy₁, hy₁y, hy₁]
    ring
  have h2' : IsUnit (-2 : A) := h2.neg
  obtain ⟨g₂, hg₂, hg₂v, hfix⟩ := carry hτ hcar hH ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) (y - y₁)
    (by rw [hvv, hyy']) (by rw [hvv]; exact h2')
  have hperp1 : hform τ H ((g₁ : Matrix (Fin N) (Fin N) A) *ᵥ (e - f)) (y + y₁) = 0 := by
    rw [← hg₁x, hform_unitary hg₁, hform_sub_fst, hform_add_snd, hform_add_snd, hee, hef, hfe, hff]
    ring
  have hperp2 : hform τ H (y - y₁) (y + y₁) = 0 := by
    rw [hform_sub_fst, hform_add_snd, hform_add_snd, hyy, hyy₁, hy₁y, hy₁]
    ring
  have hfix' := hfix (y + y₁) hperp1 hperp2
  refine ⟨g₂ * g₁, mul_mem hg₂ hg₁, ?_⟩
  have hsum : ((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ (e + f) = y + y₁ := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg₁x, hfix']
  have hdiff : ((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ (e - f) = y - y₁ := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hg₂v]
  have key : (2 : A) • (((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ e) = (2 : A) • y := by
    have h : ((g₂ * g₁ : GL (Fin N) A) : Matrix (Fin N) (Fin N) A) *ᵥ ((e + f) + (e - f)) = (y + y₁) + (y - y₁) := by
      rw [Matrix.mulVec_add, hsum, hdiff]
    have he : (e + f) + (e - f) = (2 : A) • e := by
      rw [two_smul]
      abel
    have hy : (y + y₁) + (y - y₁) = (2 : A) • y := by
      rw [two_smul]
      abel
    rw [he, Matrix.mulVec_smul, hy] at h
    exact h
  have h3 := congrArg (fun z => (↑h2.unit⁻¹ : A) • z) key
  simp only [smul_smul, h2.val_inv_mul, one_smul] at h3
  exact h3

end GlobalTheory.CompanionTheory.WeilSiegel.PrimCarry
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ValuativeRel

namespace GlobalTheory.CompanionTheory.Uniformiser

theorem valued_eq_exp_neg_one {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (a : 𝓞 F) (h1 : a ∈ v.asIdeal) (h2 : a ∉ v.asIdeal ^ 2) :
    Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = WithZero.exp (-1 : ℤ) := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact h2 (Submodule.zero_mem _)
  rw [show algebraMap F (v.adicCompletion F) (a : F) = ((a : F) : v.adicCompletion F) from rfl,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  have hle1 : v.intValuation a ≤ WithZero.exp (-(1 : ℕ) : ℤ) :=
    (HeightOneSpectrum.intValuation_le_pow_iff_mem v a 1).2 (by simpa using h1)
  have hnle2 : ¬ v.intValuation a ≤ WithZero.exp (-(2 : ℕ) : ℤ) := fun h =>
    h2 ((HeightOneSpectrum.intValuation_le_pow_iff_mem v a 2).1 h)
  have hne : v.intValuation a ≠ 0 := HeightOneSpectrum.intValuation_ne_zero v a ha0
  rw [← WithZero.exp_log hne] at hle1 hnle2 ⊢
  rw [WithZero.exp_le_exp] at hle1 hnle2
  congr 1
  omega

theorem ord_eq_zero_of_valued_eq_one {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {x : v.adicCompletion F} (hx : Valued.v x = 1) :
    GroundTheory.LocalField.ord x = 0 := by
  have heq : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).IsEquiv
      (ValuativeRel.valuation (v.adicCompletion F)) := ValuativeRel.isEquiv _ _
  have h1 : ValuativeRel.valuation (v.adicCompletion F) x = 1 := heq.eq_one_iff_eq_one.1 hx
  unfold GroundTheory.LocalField.ord
  rw [GroundTheory.LocalField.normalizedValuation_apply, h1, map_one, WithZero.log_one, neg_zero]

theorem ord_ratio_eq_zero : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (ϖ ϖ' : 𝓞 F), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → ϖ' ∈ v.asIdeal → ϖ' ∉ v.asIdeal ^ 2 →
    ∀ U : (v.adicCompletion F)ˣ, (U : v.adicCompletion F) *
      algebraMap F (v.adicCompletion F) (ϖ : F) = algebraMap F (v.adicCompletion F) (ϖ' : F) →
    GroundTheory.LocalField.ord (U : v.adicCompletion F) = 0 := by
  intro F _ _ v ϖ ϖ' h1 h2 h1' h2' U hU
  apply ord_eq_zero_of_valued_eq_one v
  have e1 := valued_eq_exp_neg_one v ϖ h1 h2
  have e2 := valued_eq_exp_neg_one v ϖ' h1' h2'
  have h := congrArg Valued.v hU
  rw [map_mul, e1, e2] at h
  exact mul_right_cancel₀ WithZero.exp_ne_zero (h.trans (one_mul _).symm)

end GlobalTheory.CompanionTheory.Uniformiser
end

section

namespace GlobalTheory.CompanionTheory.ComplexSets

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter

theorem exists_hypersurface_of_monic_relation {σ : Type} [Fintype σ] {Y : Set (σ → ℂ)} {w : σ → ℂ} {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (hirr : GermIrreducibleAt Y w) {φ : (σ → ℂ) → ℂ}
    (hφ : AnalyticAt ℂ φ w) (hnv : ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → φ z = 0) :
    ∀ (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ), (∀ j, AnalyticAt ℂ (a j) (A w)) →
      (∀ᶠ z in 𝓝 w, z ∈ Y → φ z ^ N + ∑ j, a j (A z) * φ z ^ (j : ℕ) = 0) →
      ∃ e : (Fin d → ℂ) → ℂ, AnalyticAt ℂ e (A w) ∧ (¬ ∀ᶠ y in 𝓝 (A w), e y = 0) ∧
        ∀ᶠ z in 𝓝 w, z ∈ Y → φ z = 0 → e (A z) = 0 := by
  intro N
  induction N with
  | zero =>
    intro a _ hrel
    exfalso
    have := hrel.self_of_nhds hirr.1
    simp at this
  | succ n ih =>
    intro a ha hrel
    by_cases h0 : ∀ᶠ y in 𝓝 (A w), a 0 y = 0
    · have h0' : ∀ᶠ z in 𝓝 w, a 0 (A z) = 0 := (A.continuous.tendsto w).eventually h0
      have hQ : AnalyticAt ℂ (fun z => φ z ^ n + ∑ j : Fin n, a j.succ (A z) * φ z ^ (j : ℕ)) w := by
        refine (hφ.pow n).add ?_
        refine Finset.analyticAt_fun_sum _ fun j _ => ?_
        have hc : AnalyticAt ℂ (fun z => a j.succ (A z)) w :=
          AnalyticAt.fun_comp (ha j.succ) (A.analyticAt w)
        exact hc.mul (hφ.pow _)
      have hprod : ∀ᶠ z in 𝓝 w, z ∈ Y →
          φ z * (φ z ^ n + ∑ j : Fin n, a j.succ (A z) * φ z ^ (j : ℕ)) = 0 := by
        filter_upwards [hrel, h0'] with z hz hz0 hzY
        have h := hz hzY
        rw [Fin.sum_univ_succ] at h
        simp only [Fin.val_zero, pow_zero, mul_one, hz0, zero_add, Fin.val_succ] at h
        rw [← h, mul_add, Finset.mul_sum, pow_succ']
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rcases hirr.2 φ _ hφ hQ hprod with h | h
      · exact absurd h hnv
      · exact ih (fun j => a j.succ) (fun j => ha j.succ) h
    · refine ⟨a 0, ha 0, h0, ?_⟩
      filter_upwards [hrel] with z hz hzY hφ0
      have h := hz hzY
      rw [Fin.sum_univ_succ] at h
      simpa [hφ0] using h

theorem irreducibleGermMeetOverHypersurface_of_finiteFibreGermIntegral
    (H : FiniteFibreGermIntegral.Statement) : IrreducibleGermMeetOverHypersurface.Statement := by
  intro σ _ Y Z w d A hY hirr hfib hZ hnot
  obtain ⟨N₀, k, f, hN₀, hwN₀, hf, hZN⟩ := hZ
  have hex : ∃ m, ¬ ∀ᶠ z in 𝓝 w, z ∈ Y → f m z = 0 := by
    by_contra hcon
    push_neg at hcon
    apply hnot
    filter_upwards [eventually_all.2 hcon, hN₀.mem_nhds hwN₀] with z hz hzN hzY
    have hmem : z ∈ {z | z ∈ N₀ ∧ ∀ i, f i z = 0} := ⟨hzN, fun i => hz i hzY⟩
    rw [← hZN] at hmem
    exact hmem.1
  obtain ⟨m, hm⟩ := hex
  have hφ : AnalyticAt ℂ (f m) w := hf m w hwN₀
  obtain ⟨N, a, ha, hrel⟩ := H σ Y w d A hY hfib (f m) hφ
  obtain ⟨e, he, hne, hz⟩ := exists_hypersurface_of_monic_relation A hirr hφ hm N a ha hrel
  refine ⟨e, he, hne, ?_⟩
  filter_upwards [hz, hN₀.mem_nhds hwN₀] with z hz' hzN hzY hzZ
  have hmem : z ∈ Z ∩ N₀ := ⟨hzZ, hzN⟩
  rw [hZN] at hmem
  exact hz' hzY (hmem.2 m)

end GlobalTheory.CompanionTheory.ComplexSets
end

section

namespace GlobalTheory.CompanionTheory.PairCount

theorem card_comap_subtype {R X : Type} [Ring R] [AddCommGroup X] [Module R X]
    (p q : Submodule R X) :
    Nat.card ↥(q.comap p.subtype) = Nat.card ↥(p ⊓ q) :=
  Nat.card_congr
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_sup_mul_card_inf {R X : Type} [Ring R] [AddCommGroup X] [Module R X] [Finite X]
    (I L : Submodule R X) :
    Nat.card ↥(I ⊔ L) * Nat.card ↥(I ⊓ L) = Nat.card ↥I * Nat.card ↥L := by
  have e := Nat.card_congr (LinearMap.quotientInfEquivSupQuotient I L).toEquiv
  have hq : I.comap I.subtype ⊓ L.comap I.subtype = L.comap I.subtype := by
    rw [Submodule.comap_subtype_self, top_inf_eq]
  rw [hq] at e
  have h1 := Submodule.card_eq_card_quotient_mul_card (L.comap I.subtype)
  have h2 := Submodule.card_eq_card_quotient_mul_card (L.comap (I ⊔ L).subtype)
  rw [card_comap_subtype] at h1 h2
  rw [inf_eq_right.2 (le_sup_right : L ≤ I ⊔ L)] at h2
  rw [h1, h2, e]
  ring

theorem bijective_of_injective (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X]
    [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y]
    (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n) (hB : Function.Injective B)
    (hB' : Function.Injective B.flip) : Function.Bijective B := by
  have : Finite (X →ₗ[ZMod n] ZMod n) := Finite.of_injective _ DFunLike.coe_injective
  have hd : Nat.card (X →ₗ[ZMod n] ZMod n) = Nat.card X := GlobalTheory.ZModDual.card_dual_eq n X
  have hd' : Nat.card (Y →ₗ[ZMod n] ZMod n) = Nat.card Y := GlobalTheory.ZModDual.card_dual_eq n Y
  have : Finite (Y →ₗ[ZMod n] ZMod n) := Finite.of_injective _ DFunLike.coe_injective
  have h1 : Nat.card X ≤ Nat.card Y := hd' ▸ Nat.card_le_card_of_injective _ hB'
  exact hB.bijective_of_nat_card_le (hd ▸ h1)

theorem card_annihilator_mul_card (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X]
    [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y]
    (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n) (hB : Function.Injective B)
    (hB' : Function.Injective B.flip) (U : Submodule (ZMod n) X) :
    Nat.card ↥(⨅ x ∈ U, LinearMap.ker (B.flip x)) * Nat.card ↥U = Nat.card X := by
  let e : Y ≃ (X →ₗ[ZMod n] ZMod n) :=
    Equiv.ofBijective B (bijective_of_injective n X Y B hB hB')
  have h1 : Nat.card ↥(⨅ x ∈ U, LinearMap.ker (B.flip x)) = Nat.card ↥U.dualAnnihilator := by
    refine Nat.card_congr (Equiv.subtypeEquiv e fun y => ?_)
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply,
      Submodule.mem_dualAnnihilator]
    rfl
  have : Finite (X ⧸ U) := Finite.of_surjective _ (Submodule.mkQ_surjective U)
  have h2 : Nat.card ↥U.dualAnnihilator = Nat.card (X ⧸ U) := by
    rw [← Nat.card_congr (Submodule.dualQuotEquivDualAnnihilator U).toEquiv]
    exact GlobalTheory.ZModDual.card_dual_eq n (X ⧸ U)
  rw [h1, h2]
  rw [mul_comm]
  exact (Submodule.card_eq_card_quotient_mul_card U).symm

theorem annihilator_inf (n : ℕ) (X Y : Type) [AddCommGroup X] [Module (ZMod n) X]
    [AddCommGroup Y] [Module (ZMod n) Y] (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n)
    (I L : Submodule (ZMod n) X) :
    (⨅ x ∈ I, LinearMap.ker (B.flip x)) ⊓ (⨅ x ∈ L, LinearMap.ker (B.flip x)) =
      ⨅ x ∈ I ⊔ L, LinearMap.ker (B.flip x) := by
  ext y
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.flip_apply]
  refine ⟨fun h x hx => ?_, fun h => ⟨fun x hx => h x (Submodule.mem_sup_left hx),
    fun x hx => h x (Submodule.mem_sup_right hx)⟩⟩
  obtain ⟨i, hi, l, hl, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add (f := _), h.1 i hi, h.2 l hl, add_zero]

theorem card_annihilator_inf (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X]
    [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y]
    (B : Y →ₗ[ZMod n] X →ₗ[ZMod n] ZMod n) (hB : Function.Injective B)
    (hB' : Function.Injective B.flip) (I L : Submodule (ZMod n) X) :
    Nat.card ↥((⨅ x ∈ I, LinearMap.ker (B.flip x)) ⊓ (⨅ x ∈ L, LinearMap.ker (B.flip x))) *
        Nat.card ↥I * Nat.card ↥L = Nat.card X * Nat.card ↥(I ⊓ L) := by
  rw [annihilator_inf, mul_assoc, ← card_sup_mul_card_inf, ← mul_assoc,
    card_annihilator_mul_card n X Y B hB hB']

end GlobalTheory.CompanionTheory.PairCount
end
