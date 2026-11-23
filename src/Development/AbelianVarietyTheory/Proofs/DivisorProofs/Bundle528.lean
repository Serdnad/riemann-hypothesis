module

public import Formalism.RealPlaceAnalysis.Bundle005
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle001
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle002
public import Formalism.SatakeDualWeyl.Bundle001
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Span
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGUIffAdjJ
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle005
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.RingTheory.MvPowerSeries.Basic
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle011

@[expose] public section

section

open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)

namespace GlobalTheory.UJOffDiag

open Formalism.REAL

def sgn (e : Bool) : ℝ := if e then 1 else -1

def ind (e : Bool) : ℝ := if e then 1 else 0

lemma term_left (z : ℂ) (e : Bool) :
    star z * (if e then (1 : ℂ) else -1) * z = ((sgn e * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  have h : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']; push_cast; ring
  cases e
  · rw [show star z * (if false = true then (1 : ℂ) else -1) * z = -(star z * z) by simp, h]
    simp [sgn]
  · rw [show star z * (if true = true then (1 : ℂ) else -1) * z = star z * z by simp, h]
    simp [sgn]

lemma term_right (z : ℂ) (e : Bool) :
    z * (if e then (1 : ℂ) else -1) * star z = ((sgn e * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [show z * (if e then (1 : ℂ) else -1) * star z = star z * (if e then (1 : ℂ) else -1) * z by ring]
  exact term_left z e

lemma col_id {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) (b : Fin n) :
    ∑ a, sgn (ε a) * ‖g a b‖ ^ 2 = sgn (ε b) := by
  unfold inUJ at hg
  have h := congrFun (congrFun hg b) b
  rw [Matrix.mul_apply] at h
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply] at h
  simp only [term_left] at h
  have h2 : ((∑ a, sgn (ε a) * ‖g a b‖ ^ 2 : ℝ) : ℂ) = ((sgn (ε b) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, h, Matrix.diagonal_apply_eq]; cases ε b <;> simp [sgn]
  exact_mod_cast h2

lemma row_id {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) (a : Fin n) :
    ∑ b, sgn (ε b) * ‖g a b‖ ^ 2 = sgn (ε a) := by
  have h1 := (indefinite_unitary_inv_closed n ε g hg).1
  have hJ : g * Jm ε * gᴴ = Jm ε := by
    calc g * Jm ε * gᴴ = g * (Jm ε * gᴴ * Jm ε) * Jm ε := by
          simp only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
      _ = Jm ε := by rw [h1, Matrix.one_mul]
  have h := congrFun (congrFun hJ a) a
  rw [Matrix.mul_apply] at h
  simp only [Jm, Matrix.mul_diagonal, Matrix.conjTranspose_apply] at h
  simp only [term_right] at h
  have h2 : ((∑ b, sgn (ε b) * ‖g a b‖ ^ 2 : ℝ) : ℂ) = ((sgn (ε a) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, h, Matrix.diagonal_apply_eq]; cases ε a <;> simp [sgn]
  exact_mod_cast h2

end GlobalTheory.UJOffDiag

namespace GlobalTheory.UJOffDiag

open Formalism.REAL

lemma off_sum_eq {n : ℕ} (ε : Fin n → Bool) (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2 =
      ∑ a, ∑ b, ind (ε a) * ind (!ε b) * ‖M a b‖ ^ 2 := by
  rw [← Finset.sum_subtype (Finset.univ.filter fun z : Fin n × Fin n => ε z.1 = true ∧ ε z.2 = false)
    (fun x => by simp) (fun z => ‖M z.1 z.2‖ ^ 2), Finset.sum_filter, ← Finset.univ_product_univ,
    Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  cases ε a <;> cases ε b <;> simp [ind]

lemma hs_eq {n : ℕ} (ε : Fin n → Bool) (g : Matrix (Fin n) (Fin n) ℂ) (hg : inUJ ε g) :
    hs g = n + 4 * ∑ a, ∑ b, ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2 := by
  have key : ∀ a b, ‖g a b‖ ^ 2 = 4 * (ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2) +
      (-(sgn (ε a) * ‖g a b‖ ^ 2) + 2 * (ind (ε a) * (sgn (ε b) * ‖g a b‖ ^ 2))) := by
    intro a b; cases ε a <;> cases ε b <;> simp [ind, sgn] <;> ring
  have hcol : ∑ a, ∑ b, sgn (ε a) * ‖g a b‖ ^ 2 = ∑ b, sgn (ε b) := by
    rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun b _ => col_id ε g hg b
  have hrow : ∑ a, ind (ε a) * ∑ b, sgn (ε b) * ‖g a b‖ ^ 2 = ∑ a, ind (ε a) * sgn (ε a) :=
    Finset.sum_congr rfl fun a _ => by rw [row_id ε g hg a]
  have hn : ∑ a : Fin n, (-(sgn (ε a)) + 2 * (ind (ε a) * sgn (ε a))) = n := by
    rw [show (n : ℝ) = ∑ _a : Fin n, (1 : ℝ) by simp]
    exact Finset.sum_congr rfl fun a _ => by cases ε a <;> simp [ind, sgn] <;> norm_num
  calc hs g = ∑ a, ∑ b, (4 * (ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2) +
      (-(sgn (ε a) * ‖g a b‖ ^ 2) + 2 * (ind (ε a) * (sgn (ε b) * ‖g a b‖ ^ 2)))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => key a b
    _ = 4 * (∑ a, ∑ b, ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2) +
        (-(∑ a, ∑ b, sgn (ε a) * ‖g a b‖ ^ 2) +
          2 * ∑ a, ind (ε a) * ∑ b, sgn (ε b) * ‖g a b‖ ^ 2) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_neg_distrib]
    _ = n + 4 * ∑ a, ∑ b, ind (ε a) * ind (!ε b) * ‖g a b‖ ^ 2 := by
        rw [hcol, hrow, ← hn, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
        ring

end GlobalTheory.UJOffDiag

namespace GlobalTheory

open Formalism.REAL

theorem isCompact_offDiag_sublevel : ∀ (n : ℕ) (ε : Fin n → Bool) (C : ℝ),
    IsCompact {g : UJ ε | ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false},
      ‖(toM g) z.1.1 z.1.2‖ ^ 2 ≤ C} := by
  intro n ε C
  set F : Matrix (Fin n) (Fin n) ℂ → ℝ := fun M =>
    ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2 with hF
  have hFc : Continuous F :=
    continuous_finsetSum _ fun z _ => (continuous_norm.comp (continuous_id.matrix_elem z.1.1 z.1.2)).pow 2
  have hK : IsCompact {M : Matrix (Fin n) (Fin n) ℂ | inUJ ε M ∧ F M ≤ C} := by
    refine IsCompact.of_isClosed_subset ((hermitian_small_ball n ε).1 (n + 4 * C)) ?_ ?_
    · exact (indefinite_unitary_closed n ε).inter (isClosed_le hFc continuous_const)
    · rintro M ⟨hM, hFM⟩
      refine ⟨hM, ?_⟩
      rw [UJOffDiag.hs_eq ε M hM, ← UJOffDiag.off_sum_eq]
      have : F M = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2 := rfl
      linarith
  have h := (isClosedEmbeddingMatrix n ε).1.isCompact_preimage hK
  convert h using 1
  ext g
  exact ⟨fun hg => ⟨g.2, hg⟩, fun hg => hg.2⟩

end GlobalTheory
end

section

open GlobalTheory.LGrp GlobalTheory.BorelUMod Formalism.UG

namespace GlobalTheory.BorelUMod

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem ball_eq_image {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    {x : L | Valued.v x ≤ WithZero.exp (-k)} = (fun x => ϖ ^ k * x) '' {x : L | Valued.v x ≤ 1} := by
  have h0 : ϖ ≠ 0 := fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  have hk : Valued.v (ϖ ^ k) = WithZero.exp (-k) := by
    rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; simp
  ext x
  constructor
  · intro hx
    refine ⟨(ϖ ^ k)⁻¹ * x, ?_, by field_simp⟩
    show Valued.v ((ϖ ^ k)⁻¹ * x) ≤ 1
    rw [map_mul, map_inv₀, hk]
    exact (inv_mul_le_one₀ (zero_lt_iff.2 WithZero.exp_ne_zero)).2 hx
  · rintro ⟨y, hy, rfl⟩
    show Valued.v (ϖ ^ k * y) ≤ WithZero.exp (-k)
    rw [map_mul, hk]
    exact (mul_le_mul' le_rfl hy).trans (by rw [mul_one])

theorem isOpen_vball {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    IsOpen {x : L | Valued.v x ≤ WithZero.exp (-k)} := by
  have h0 : ϖ ≠ 0 := fun e => by simp [e] at hϖ; exact WithZero.exp_ne_zero hϖ.symm
  rw [ball_eq_image hϖ]
  exact (Homeomorph.mulLeft₀ (ϖ ^ k) (zpow_ne_zero k h0)).isOpenMap _ (Valued.isOpen_integer L)

theorem isCompact_vball [CompleteSpace L] {ϖ : L} {σ : L →+* L} {q : ℕ} (h : IsUnramInv ϖ σ q) (k : ℤ) :
    IsCompact {x : L | Valued.v x ≤ WithZero.exp (-k)} := by
  obtain ⟨-, hv, -, hϖ, -, hq, hcard⟩ := h
  haveI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).IsNontrivial :=
    ⟨ϖ, by rw [hϖ]; exact WithZero.coe_ne_zero, by rw [hϖ, ← WithZero.coe_one, ne_eq, WithZero.coe_inj]; decide⟩
  letI : (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (e := 2) (by norm_num)
  have hp := (Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    (K := L)).2 ⟨(Valued.isClosed_integer L).completeSpace_coe,
      (Valued.v : Valuation L _).valuationSubring_isDiscreteValuationRing,
      Nat.finite_of_card_ne_zero (by
        refine ne_of_eq_of_ne hcard (pow_ne_zero _ (by omega)))⟩
  rw [ball_eq_image hϖ]
  exact (isCompact_iff_compactSpace.2 hp).image (continuous_const.mul continuous_id)

end GlobalTheory.BorelUMod
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem dual_eq_smul_of_forall_dvd :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O), (∀ x : O, a * x = 0 → x = 0) →
      ∀ l : Module.Dual O M, (∀ w, a ∣ l w) → ∃ l' : Module.Dual O M, l = a • l' := by
  intro O M _ _ _ a ha l hl
  have cancel : ∀ x y : O, a * x = a * y → x = y := by
    intro x y hxy
    have := ha (x - y) (by rw [mul_sub, hxy, sub_self])
    exact sub_eq_zero.mp this
  let c : M → O := fun w => Classical.choose (hl w)
  have hc : ∀ w, l w = a * c w := fun w => Classical.choose_spec (hl w)
  refine ⟨{ toFun := c, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    apply cancel
    rw [mul_add, ← hc, ← hc, ← hc, map_add (f := _)]
  · intro r x
    apply cancel
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← hc, map_smul, hc, smul_eq_mul]
    ring
  · ext w
    simp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, smul_eq_mul]
    exact hc w

end GlobalTheory
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv

theorem one_tmul_quot_reduction :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (I : Ideal O),
      (∀ y : (O ⧸ I) ⊗[O] M, ∃ b : M, y = 1 ⊗ₜ b) ∧
      (∀ b : M, (1 : O ⧸ I) ⊗ₜ[O] b = 0 ↔ b ∈ I • (⊤ : Submodule O M)) ∧
      ∀ (a : O) (b : M), b ∈ Ideal.span {a} • (⊤ : Submodule O M) ↔ ∃ z, b = a • z := by
  intro O M _ _ _ I
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective (I • (⊤ : Submodule O M))
      (TensorProduct.quotTensorEquivQuotSMul M I y)
    refine ⟨b, ?_⟩
    rw [← TensorProduct.quotTensorEquivQuotSMul_symm_mk I b, hb, LinearEquiv.symm_apply_apply]
  · intro b
    rw [← (TensorProduct.quotTensorEquivQuotSMul M I).map_eq_zero_iff,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul, Submodule.Quotient.mk_eq_zero]
  · intro a b
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, -, hz⟩
      exact ⟨z, hz.symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, Submodule.mem_top, rfl⟩

end GlobalTheory.PDiv
end

section

open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory

theorem groupChunk_extend {G H : Type} [Group G] [Group H] (C : G → Prop) (f : G → H)
    (hmul : ∀ x y, C x → C y → C (x * y) → f (x * y) = f x * f y)
    (hgen : ∀ s : Finset G, ∃ u : G, ∀ g ∈ s, C (g * u)) :
    ∃ Φ : G →* H, ∀ g u, C u → C (g * u) → Φ g = f (g * u) * (f u)⁻¹ := by
  classical

  have key : ∀ g u w, C u → C (g * u) → C w → C (g * w) → C (u⁻¹ * w) →
      f (g * u) * (f u)⁻¹ = f (g * w) * (f w)⁻¹ := by
    intro g u w hu hgu hw hgw huw
    have h1 : f w = f u * f (u⁻¹ * w) := by
      have h := hmul u (u⁻¹ * w) hu huw (by rwa [mul_inv_cancel_left])
      rwa [mul_inv_cancel_left] at h
    have h2 : f (g * w) = f (g * u) * f (u⁻¹ * w) := by
      have h := hmul (g * u) (u⁻¹ * w) hgu huw (by rwa [mul_assoc, mul_inv_cancel_left])
      rwa [mul_assoc, mul_inv_cancel_left] at h
    rw [h1, h2]
    group
  choose u₀ hu₀ using fun g : G => hgen {1, g}
  have hu₀1 : ∀ g, C (u₀ g) := fun g => by simpa using hu₀ g 1 (by simp)
  have hu₀g : ∀ g, C (g * u₀ g) := fun g => hu₀ g g (by simp)
  let φ : G → H := fun g => f (g * u₀ g) * (f (u₀ g))⁻¹
  have hφ : ∀ g u, C u → C (g * u) → φ g = f (g * u) * (f u)⁻¹ := by
    intro g u hu hgu
    obtain ⟨w, hw⟩ := hgen {1, g, u⁻¹, (u₀ g)⁻¹}
    have hw1 : C w := by simpa using hw 1 (by simp)
    have hwg : C (g * w) := hw g (by simp)
    have hwu : C (u⁻¹ * w) := hw u⁻¹ (by simp)
    have hwu₀ : C ((u₀ g)⁻¹ * w) := hw (u₀ g)⁻¹ (by simp)
    rw [key g u w hu hgu hw1 hwg hwu]
    exact key g (u₀ g) w (hu₀1 g) (hu₀g g) hw1 hwg hwu₀
  refine ⟨MonoidHom.mk' φ ?_, fun g u hu hgu => hφ g u hu hgu⟩
  intro g h
  obtain ⟨w, hw⟩ := hgen {1, h, g * h}
  have hw1 : C w := by simpa using hw 1 (by simp)
  have hwh : C (h * w) := hw h (by simp)
  have hwgh : C (g * h * w) := hw (g * h) (by simp)
  rw [hφ (g * h) w hw1 hwgh, hφ h w hw1 hwh, hφ g (h * w) hwh (by rwa [← mul_assoc]),
    ← mul_assoc g h w]
  group

theorem bigCell_hom : ∀ (G H : Type) [Group G] [Group H] (P : Subgroup G) (w : G) (ρ : P →* H) (W : H), (∀ p q : P, w * p = q * w → W * ρ p = ρ q * W) → (∀ p : P, (∃ p₁ p₂ : P, w * p * w = p₁ * w * p₂) → ∃ p₁ p₂ : P, w * p * w = p₁ * w * p₂ ∧ W * ρ p * W = ρ p₁ * W * ρ p₂) → (∀ s : Finset G, ∃ u : G, ∀ g ∈ s, ∃ p₁ p₂ : P, g * u = p₁ * w * p₂) → ∃ Φ : G →* H, (∀ p : P, Φ p = ρ p) ∧ Φ w = W := by
  classical
  intro G H _ _ P w ρ W ha hb hc
  let C : G → Prop := fun g => ∃ p₁ p₂ : P, g = p₁ * w * p₂

  have hwd : ∀ p₁ p₂ q₁ q₂ : P, (p₁ : G) * w * p₂ = q₁ * w * q₂ →
      ρ p₁ * W * ρ p₂ = ρ q₁ * W * ρ q₂ := by
    intro p₁ p₂ q₁ q₂ h
    have h' : w * ((p₂ * q₂⁻¹ : P) : G) = ((p₁⁻¹ * q₁ : P) : G) * w := by
      push_cast
      calc w * ((p₂ : G) * (q₂ : G)⁻¹)
          = (p₁ : G)⁻¹ * ((p₁ : G) * w * p₂) * (q₂ : G)⁻¹ := by group
        _ = (p₁ : G)⁻¹ * ((q₁ : G) * w * q₂) * (q₂ : G)⁻¹ := by rw [h]
        _ = (p₁ : G)⁻¹ * q₁ * w := by group
    have h'' := ha _ _ h'
    rw [map_mul, map_mul, map_inv, map_inv] at h''
    calc ρ p₁ * W * ρ p₂ = ρ p₁ * (W * (ρ p₂ * (ρ q₂)⁻¹)) * ρ q₂ := by group
      _ = ρ p₁ * ((ρ p₁)⁻¹ * ρ q₁ * W) * ρ q₂ := by rw [h'']
      _ = ρ q₁ * W * ρ q₂ := by group
  let f : G → H := fun g => if h : C g then ρ h.choose * W * ρ h.choose_spec.choose else 1
  have hf : ∀ p₁ p₂ : P, f (p₁ * w * p₂) = ρ p₁ * W * ρ p₂ := by
    intro p₁ p₂
    have hC : C (p₁ * w * p₂) := ⟨p₁, p₂, rfl⟩
    dsimp only [f]
    rw [dite_eq_left hC]
    exact hwd _ _ _ _ hC.choose_spec.choose_spec.symm
  have hmul : ∀ x y, C x → C y → C (x * y) → f (x * y) = f x * f y := by
    rintro x y ⟨p₁, p₂, rfl⟩ ⟨q₁, q₂, rfl⟩ ⟨r₁, r₂, hr⟩
    have hin : ∃ a b : P, w * ((p₂ * q₁ : P) : G) * w = a * w * b :=
      ⟨p₁⁻¹ * r₁, r₂ * q₂⁻¹, by
        push_cast
        calc w * ((p₂ : G) * q₁) * w
            = (p₁ : G)⁻¹ * ((p₁ : G) * w * p₂ * ((q₁ : G) * w * q₂)) * (q₂ : G)⁻¹ := by group
          _ = (p₁ : G)⁻¹ * ((r₁ : G) * w * r₂) * (q₂ : G)⁻¹ := by rw [hr]
          _ = (p₁ : G)⁻¹ * r₁ * w * ((r₂ : G) * (q₂ : G)⁻¹) := by group⟩
    obtain ⟨a, b, hab, hW⟩ := hb _ hin
    rw [map_mul] at hW
    have hxy : (p₁ : G) * w * p₂ * ((q₁ : G) * w * q₂) = ((p₁ * a : P) : G) * w * ((b * q₂ : P) : G) := by
      calc (p₁ : G) * w * p₂ * ((q₁ : G) * w * q₂)
          = (p₁ : G) * (w * ((p₂ * q₁ : P) : G) * w) * q₂ := by push_cast; group
        _ = (p₁ : G) * ((a : G) * w * b) * q₂ := by rw [hab]
        _ = ((p₁ * a : P) : G) * w * ((b * q₂ : P) : G) := by push_cast; group
    rw [hxy, hf, hf, hf, map_mul, map_mul]
    calc ρ p₁ * ρ a * W * (ρ b * ρ q₂) = ρ p₁ * (ρ a * W * ρ b) * ρ q₂ := by group
      _ = ρ p₁ * (W * (ρ p₂ * ρ q₁) * W) * ρ q₂ := by rw [hW]
      _ = ρ p₁ * W * ρ p₂ * (ρ q₁ * W * ρ q₂) := by group
  obtain ⟨Φ, hΦ⟩ := groupChunk_extend C f hmul hc
  refine ⟨Φ, fun p => ?_, ?_⟩
  · obtain ⟨u, hu⟩ := hc {1}
    obtain ⟨a, b, hab⟩ := hu 1 (by simp)
    rw [one_mul] at hab
    have e1 : (p : G) * u = ((p * a : P) : G) * w * b := by
      rw [hab]
      push_cast
      group
    rw [hΦ p u ⟨a, b, hab⟩ ⟨p * a, b, e1⟩, e1, hab, hf, hf, map_mul]
    group
  · obtain ⟨u, hu⟩ := hc {1, w}
    obtain ⟨a, b, hab⟩ := hu 1 (by simp)
    rw [one_mul] at hab
    obtain ⟨c, d, hcd⟩ := hu w (by simp)
    have hin : ∃ p₁ p₂ : P, w * (a : G) * w = p₁ * w * p₂ :=
      ⟨c, d * b⁻¹, by
        calc w * (a : G) * w = w * u * (b : G)⁻¹ := by rw [hab]; group
          _ = (c : G) * w * d * (b : G)⁻¹ := by rw [hcd]
          _ = (c : G) * w * ((d * b⁻¹ : P) : G) := by push_cast; group⟩
    obtain ⟨r₁, r₂, hr, hW⟩ := hb a hin
    have e1 : w * u = (r₁ : G) * w * ((r₂ * b : P) : G) := by
      rw [hab]
      push_cast
      calc w * ((a : G) * w * b) = w * a * w * b := by group
        _ = (r₁ : G) * w * ((r₂ : G) * b) := by rw [hr]; group
    rw [hΦ w u ⟨a, b, hab⟩ ⟨c, d, hcd⟩, e1, hab, hf, hf, map_mul]
    calc ρ r₁ * W * (ρ r₂ * ρ b) * (ρ a * W * ρ b)⁻¹ = (ρ r₁ * W * ρ r₂) * (ρ a * W)⁻¹ := by group
      _ = (W * ρ a * W) * (ρ a * W)⁻¹ := by rw [hW]
      _ = W := by group

end GlobalTheory
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem projective_dvd_of_forall_dual_dvd :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Projective O M] (a : O) (b : M),
      (∀ φ : Module.Dual O M, a ∣ φ b) → ∃ z, b = a • z := by
  intro O M _ _ _ _ a b h
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective O M)
  have hc : ∀ i : M, a ∣ s b i := fun i => h ((Finsupp.lapply i).comp s)
  choose c hc using hc
  refine ⟨∑ i ∈ (s b).support, c i • i, ?_⟩
  have hb : Finsupp.linearCombination O id (s b) = b := by
    simpa using LinearMap.congr_fun hs b
  rw [Finset.smul_sum]
  conv_lhs => rw [← hb]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, ← hc i]
  rfl

end GlobalTheory
end

section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem dual_quotient_form_eq_eval :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Finite O M]
      [Module.Projective O M] (I : Ideal O) (u : Module.Dual O M →ₗ[O] O ⧸ I),
      ∃ b : M, ∀ φ, u φ = Ideal.Quotient.mk I (φ b) := by
  intro O M _ _ _ _ _ I u
  obtain ⟨v, hv⟩ := Module.projective_lifting_property (Submodule.mkQ I) u
    (Submodule.mkQ_surjective I)
  refine ⟨(Module.evalEquiv O M).symm v, fun φ => ?_⟩
  have h1 : φ ((Module.evalEquiv O M).symm v) = v φ := by
    have := congrArg (fun w : Module.Dual O (Module.Dual O M) => w φ)
      ((Module.evalEquiv O M).apply_symm_apply v)
    simpa using this
  rw [h1, ← hv]
  rfl

end GlobalTheory
end
