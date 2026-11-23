module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle010
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle007
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle012
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle014
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1

@[expose] public section

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.matrixKroneckerPower_tensorAction_algebra : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R : Type) [CommRing R], (∀ n : ℕ, tpow n (1 : Matrix ι ι R) = 1 ∧ (∀ y z : Matrix ι ι R, tpow n (y * z) = tpow n y * tpow n z) ∧ ∀ y : Matrix ι ι R, (tpow n y)ᵀ = tpow n yᵀ) ∧ ∀ (m : ℕ) (d : Fin m → ℕ) (t : TIdx ι d → R), act d t 1 = t ∧ (∀ y z : Matrix ι ι R, act d t (y * z) = act d (act d t y) z) ∧ (∀ (a : ι → R) (k : TIdx ι d), act d t (diagonal a) k = t k * ∏ j, a (k.2 j)) ∧ (∀ (S : Subring R) (y : Matrix ι ι R), (∀ k, t k ∈ S) → (∀ i j, y i j ∈ S) → ∀ k, act d t y k ∈ S) ∧ (∀ (c : R) (y : Matrix ι ι R), act d (c • t) y = c • act d t y) ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R') (y : Matrix ι ι R), act d (fun k => φ (t k)) (y.map φ) = fun k => φ (act d t y k) := by
  first | exact @GlobalTheory.ClassFin.tpow_act_algebra | exact GlobalTheory.ClassFin.tpow_act_algebra | (intros; apply GlobalTheory.ClassFin.tpow_act_algebra <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S' : Set (MvPolynomial (ι × ι) ℚ)) (R : Type) [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R), (y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R → ∀ f ∈ S', ev f y = 0) ∧ (IsReduced R → (∀ f ∈ S', ev f y = 0) → y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R) := by
  first | exact @GlobalTheory.ClassFin.mem_pts_zeroSet_of_isReduced | exact GlobalTheory.ClassFin.mem_pts_zeroSet_of_isReduced | (intros; apply GlobalTheory.ClassFin.mem_pts_zeroSet_of_isReduced <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.relIndex_squares_le_two_mul_of_subgroup : ∀ (G : Type) [CommGroup G] (U H : Subgroup G) (ε : G), H ≤ U → H.relIndex U ≠ 0 → (∀ a : G, a ^ 2 = 1 → a = 1 ∨ a = ε) → (sqs H).relIndex H ≠ 0 → (sqs U).relIndex U ≠ 0 ∧ (sqs U).relIndex U ≤ 2 * (sqs H).relIndex H := by
  first | exact @GlobalTheory.QNorm.relIndex_sqs_le_two_mul | exact GlobalTheory.QNorm.relIndex_sqs_le_two_mul | (intros; apply GlobalTheory.QNorm.relIndex_sqs_le_two_mul <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma eq_one_of_sq_eq_one_withZero_int {r : WithZero (Multiplicative ℤ)} (h : r ^ 2 = 1) :
    r = 1 := by
  rcases lt_trichotomy r 1 with hr | hr | hr
  · exact absurd h (ne_of_lt (pow_lt_one₀ zero_le' hr two_ne_zero))
  · exact hr
  · exact absurd h (ne_of_gt (one_lt_pow₀ hr two_ne_zero))

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma valuation_algebraMap_eq_of_unit_at_under {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E}
    (hq : _root_.GlobalTheory.QNorm.IsQuad δ θ σ) (w : HeightOneSpectrum (𝓞 E))
    (h2 : (w.under (𝓞 F)).valuation F 2 = 1) (hδ : (w.under (𝓞 F)).valuation F δ = 1) (c : F) :
    w.valuation E (algebraMap F E c) = (w.under (𝓞 F)).valuation F c := by
  obtain ⟨-, -, hram⟩ := _root_.GlobalTheory.QNorm.places_over F E
  obtain ⟨e, he0, hw⟩ := hram w
  set v := w.under (𝓞 F)
  set V := w.valuation E
  suffices he : e = 1 by rw [hw, he, pow_one]
  have hV2 : V 2 = 1 := by
    have := hw 2
    rw [map_ofNat] at this
    rw [this, h2, one_pow]
  have hθ : V θ = 1 := by
    apply eq_one_of_sq_eq_one_withZero_int
    rw [← map_pow, hq.sq, hw, hδ, one_pow]
  have hσθ := hq.conj
  have hθ0 := hq.root_ne_zero
  obtain ⟨x, hx⟩ := HeightOneSpectrum.valuation_exists_uniformizer E w
  obtain ⟨a, b, hab⟩ := hq.span x
  have hσx : σ x = algebraMap F E a - algebraMap F E b * θ := by
    rw [hab, map_add (f := _), map_mul, AlgEquiv.commutes, AlgEquiv.commutes, hσθ]; ring
  obtain ⟨-, -, -, hnorm, -⟩ := _root_.GlobalTheory.QNorm.isQuad_basic F E δ θ σ hq
  obtain ⟨a', b', hN⟩ := hnorm x
  have hbθ : V (algebraMap F E b * θ) = V (algebraMap F E b) := by rw [map_mul, hθ, mul_one]
  have hA : V x ≤ max (V (algebraMap F E a)) (V (algebraMap F E b)) := by
    rw [hab, ← hbθ]; exact Valuation.map_add _ _ _
  have hB : V (σ x) ≤ max (V (algebraMap F E a)) (V (algebraMap F E b)) := by
    rw [hσx, ← hbθ]; exact Valuation.map_sub _ _ _
  have ha : V (algebraMap F E a) ≤ max (V x) (V (σ x)) := by
    have h' : algebraMap F E a = (x + σ x) * (2 : E)⁻¹ := by
      rw [hσx, hab]; field_simp; ring
    rw [h', map_mul, map_inv₀, hV2, inv_one, mul_one]
    exact Valuation.map_add _ _ _
  have hb : V (algebraMap F E b) ≤ max (V x) (V (σ x)) := by
    have h' : algebraMap F E b = (x - σ x) * (2 * θ)⁻¹ := by
      rw [hσx, hab]; field_simp; ring
    rw [h', map_mul, map_inv₀, map_mul, hV2, hθ, one_mul, inv_one, mul_one]
    exact Valuation.map_sub _ _ _
  have hmax : max (V x) (V (σ x)) = max (V (algebraMap F E a)) (V (algebraMap F E b)) :=
    le_antisymm (max_le hA hB) (max_le ha hb)
  have hx0 : V x ≠ 0 := by rw [hx]; exact WithZero.exp_ne_zero
  have key : ∃ d : F, V x = v.valuation F d ^ e := by
    have hmem : max (V x) (V (σ x)) = V (algebraMap F E a) ∨
        max (V x) (V (σ x)) = V (algebraMap F E b) := by
      rw [hmax]; exact max_choice _ _
    rcases le_total (V (σ x)) (V x) with hle | hle
    · rw [max_eq_left hle] at hmem
      rcases hmem with h | h
      · exact ⟨a, h.trans (hw a)⟩
      · exact ⟨b, h.trans (hw b)⟩
    · rw [max_eq_right hle] at hmem
      have hc : ∃ c : F, V (σ x) = V (algebraMap F E c) := by
        rcases hmem with h | h
        · exact ⟨a, h⟩
        · exact ⟨b, h⟩
      obtain ⟨c, hc⟩ := hc
      have hσ0 : V (σ x) ≠ 0 := ne_of_gt (lt_of_lt_of_le (zero_lt_iff.mpr hx0) hle)
      refine ⟨(a' ^ 2 - δ * b' ^ 2) / c, ?_⟩
      rw [← hw, map_div₀, map_div₀, ← hN, ← hc, map_mul, mul_div_cancel_right₀ _ hσ0]
  obtain ⟨d, hd⟩ := key
  rw [hx] at hd
  have hl := congrArg WithZero.log hd
  rw [WithZero.log_exp, WithZero.log_pow, nsmul_eq_mul] at hl
  rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one hl.symm with h1 | h1 <;> omega


open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.hilbert90_sUnits_quadratic_extension_qnorm : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), _root_.GlobalTheory.QNorm.IsQuad δ θ σ →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (SE : Finset (HeightOneSpectrum (𝓞 E))),
    (∀ w : HeightOneSpectrum (𝓞 E), w ∈ SE ↔ w.under (𝓞 F) ∈ S) → _root_.GlobalTheory.QNorm.admitted F S →
    (∀ v, v ∉ S → v.valuation F δ = 1) → ∀ u : Eˣ, u ∈ _root_.GlobalTheory.QNorm.sUnits E SE →
    (u : E) * σ u = 1 → ∃ y : Eˣ, y ∈ _root_.GlobalTheory.QNorm.sUnits E SE ∧ (u : E) = y / σ y := by
  intro F E _ _ _ _ _ δ θ σ hq S SE hSE hS hδ u hu hnu
  classical
  obtain ⟨-, -, -, -, h90, -⟩ := _root_.GlobalTheory.QNorm.isQuad_basic F E δ θ σ hq
  obtain ⟨y, hy0, hy⟩ := h90 u hnu
  obtain ⟨-, hover, -⟩ := _root_.GlobalTheory.QNorm.places_over F E
  obtain ⟨-, hdich⟩ := _root_.GlobalTheory.QNorm.conj_places_transitive F E δ θ σ hq
  choose ch hch using hover
  rw [_root_.GlobalTheory.QNorm.mem_sUnits] at hu
  have hadm := hS
  unfold _root_.GlobalTheory.QNorm.admitted at hadm
  have hinv : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ SE →
      w.valuation E (σ y) = w.valuation E y := by
    intro w hw
    have h1 := hu w hw
    rw [hy, map_div₀] at h1
    have hσy0 : w.valuation E (σ y) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr ((map_ne_zero σ).mpr hy0)
    exact ((div_eq_one_iff_eq hσy0).mp h1).symm
  have hfib : ∀ w : HeightOneSpectrum (𝓞 E), w ∉ SE →
      w.valuation E y = (ch (w.under (𝓞 F))).valuation E y := by
    intro w hw
    have hv : (ch (w.under (𝓞 F))).under (𝓞 F) = w.under (𝓞 F) := hch _
    have hw0 : ch (w.under (𝓞 F)) ∉ SE := by
      rw [hSE, hv]; rwa [hSE] at hw
    rcases hdich (ch (w.under (𝓞 F))) w hv.symm with h | h
    · rw [← h]
    · rw [h y, hinv _ hw0]
  let n : HeightOneSpectrum (𝓞 F) → ℤ := fun v =>
    if v ∈ S then 0 else -((ch v).valuation E y).log
  have hfin := _root_.GlobalTheory.QNorm.finite_valuation_ne_one E (Units.mk0 y hy0)
  let T : Finset (HeightOneSpectrum (𝓞 F)) :=
    hfin.toFinset.image (fun w => w.under (𝓞 F))
  have hnT : ∀ v ∉ T, n v = 0 := by
    intro v hv
    by_cases hvS : v ∈ S
    · simp [n, hvS]
    · have h1 : (ch v).valuation E y = 1 := by
        by_contra hne
        apply hv
        refine Finset.mem_image.mpr ⟨ch v, ?_, hch v⟩
        rw [Set.Finite.mem_toFinset]
        exact hne
      simp [n, hvS, h1]
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.QNorm.exists_unit_valuation_eq_of_adm F S T n hS hnT
  have ha0 : algebraMap F E a ≠ 0 := by simp
  refine ⟨Units.mk0 (y * algebraMap F E a) (mul_ne_zero hy0 ha0), ?_, ?_⟩
  · rw [_root_.GlobalTheory.QNorm.mem_sUnits]
    intro w hw
    have hvS : w.under (𝓞 F) ∉ S := by rwa [hSE] at hw
    show w.valuation E (y * algebraMap F E a) = 1
    rw [map_mul, valuation_algebraMap_eq_of_unit_at_under hq w (hadm _ hvS).1 (hδ _ hvS), ha _ hvS,
      hfib w hw]
    have h0 : (ch (w.under (𝓞 F))).valuation E y ≠ 0 := (Valuation.ne_zero_iff _).mpr hy0
    simp only [n, if_neg hvS]
    nth_rewrite 1 [← WithZero.exp_log h0]
    rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
  · show (u : E) = y * algebraMap F E a / σ (y * algebraMap F E a)
    rw [hy, map_mul, AlgEquiv.commutes, mul_div_mul_right _ _ ha0]

end GlobalTheory.QNorm
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.index_sqs_of_fg : ∀ (G : Type) [CommGroup G] [Group.FG G], (sqs (⊤ : Subgroup G)).index = 2 ^ Module.finrank ℤ (Additive G) * Nat.card {a : G // a ^ 2 = 1} := by
  first | exact @GlobalTheory.QNorm.index_sqs_top_of_fg | exact GlobalTheory.QNorm.index_sqs_top_of_fg | (intros; apply GlobalTheory.QNorm.index_sqs_top_of_fg <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.sUnitsNumberField_fg : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), Group.FG (sUnits F S) := by
  first | exact @GlobalTheory.QNorm.sUnits_fg | exact GlobalTheory.QNorm.sUnits_fg | (intros; apply GlobalTheory.QNorm.sUnits_fg <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.leftTranslateMatrixPoly_tensorForm_properties : ∀ (ι : Type) [Fintype ι] [DecidableEq ι], (∀ (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ), evC (ltr g f) y = evC f (g * y)) ∧ (∀ (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ), IsInv Γ f ↔ ∀ g ∈ Γ, ltr g f = f) ∧ (∀ (g : Matrix ι ι ℂ) (n : ℕ) (f : MvPolynomial (ι × ι) ℂ), f.IsHomogeneous n → (ltr g f).IsHomogeneous n) ∧ ∀ n : ℕ, ∃ p : (Fin n → ι) → ((Fin n → ι) → ℂ) →ₗ[ℂ] MvPolynomial (ι × ι) ℂ, (∀ b l (y : Matrix ι ι ℂ), evC (p b l) y = (l ᵥ* tpow n y) b) ∧ (∀ b l (g : Matrix ι ι ℂ), ltr g (p b l) = p b (l ᵥ* tpow n g)) ∧ ∀ f : MvPolynomial (ι × ι) ℂ, f.IsHomogeneous n → ∃ l : (Fin n → ι) → (Fin n → ι) → ℂ, f = ∑ b, p b (l b) := by
  first | exact @GlobalTheory.ClassFin.ltr_tensorForms | exact GlobalTheory.ClassFin.ltr_tensorForms | (intros; apply GlobalTheory.ClassFin.ltr_tensorForms <;> assumption)
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

theorem _root_.GlobalTheory.T.exists_isotropic_basis_nonorthogonal_two_vectors : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → (∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) → ∀ x y : Fin n → E, x ≠ 0 → y ≠ 0 → ∃ z : Fin n → Fin n → E, LinearIndependent E z ∧ ∀ i, hf σ G (z i) (z i) = 0 ∧ hf σ G x (z i) ≠ 0 ∧ hf σ G y (z i) ≠ 0 := by
  first | exact @GlobalTheory.UTrans.IsoBasis.exists_isotropic_basis | exact GlobalTheory.UTrans.IsoBasis.exists_isotropic_basis | (intros; apply GlobalTheory.UTrans.IsoBasis.exists_isotropic_basis <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_isometry_matrix_range {ι : Type} [Fintype ι] [DecidableEq ι] (W : Submodule ℂ (ι → ℂ)) :
    ∃ (n : ℕ) (Q : Matrix ι (Fin n) ℂ), Qᴴ * Q = 1 ∧ ∀ v, v ∈ W ↔ ∃ x, v = Q *ᵥ x := by
  let W' : Submodule ℂ (EuclideanSpace ℂ ι) := W.comap (WithLp.linearEquiv 2 ℂ (ι → ℂ)).toLinearMap
  let b := stdOrthonormalBasis ℂ W'
  refine ⟨_, Matrix.of fun i j => (b j : EuclideanSpace ℂ ι) i, ?_, ?_⟩
  · ext j k
    have h := orthonormal_iff_ite.mp b.orthonormal j k
    rw [Submodule.coe_inner, PiLp.inner_apply] at h
    rw [Matrix.mul_apply, Matrix.one_apply, ← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_comm]
  · intro v
    constructor
    · intro hv
      let w : W' := ⟨WithLp.toLp 2 v, hv⟩
      refine ⟨fun j => b.repr w j, ?_⟩
      ext i
      have h := congrArg (fun z : W' => (z : EuclideanSpace ℂ ι) i) (b.sum_repr w)
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
      have h2 : v i = (w : EuclideanSpace ℂ ι) i := rfl
      rw [h2, ← h]
      simp [Matrix.mulVec, dotProduct, mul_comm]
    · rintro ⟨x, rfl⟩
      have h : (Matrix.of fun i j => (b j : EuclideanSpace ℂ ι) i) *ᵥ x
          = ∑ j, x j • (b j : EuclideanSpace ℂ ι).ofLp := by
        ext i
        simp [Matrix.mulVec, dotProduct, mul_comm]
      rw [h]
      exact W.sum_mem fun j _ => W.smul_mem _ (b j).2

theorem ss_of_harm : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (τ : σ ≃ σ)
    (g : σ → Matrix ι ι ℂ), (∀ s, g (τ s) * g s = 1) → Harm g → SS (Set.range g) := by
  intro ι _ _ σ _ τ g hτ hH W hW
  obtain ⟨H, hlog, hsum⟩ := hH
  obtain ⟨n, Q, hQ, hmem⟩ := exists_isometry_matrix_range W
  have hN : ∀ s, ∃ N : Matrix (Fin n) (Fin n) ℂ, g s * Q = Q * N := by
    intro s
    have : ∀ j : Fin n, ∃ x, g s *ᵥ (Q *ᵥ Pi.single j 1) = Q *ᵥ x := fun j =>
      (hmem _).1 (hW _ ⟨s, rfl⟩ _ ((hmem _).2 ⟨_, rfl⟩))
    choose x hx using this
    refine ⟨Matrix.of fun i j => x j i, ?_⟩
    ext i j
    have h := congrFun (hx j) i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
    exact h
  choose N hN using hN
  have hNinv : ∀ s, N (τ s) * N s = 1 := by
    intro s
    have h : Q * (N (τ s) * N s) = Q := by
      rw [← Matrix.mul_assoc, ← hN, Matrix.mul_assoc, ← hN, ← Matrix.mul_assoc, hτ, Matrix.one_mul]
    have h2 := congrArg (fun X => Qᴴ * X) h
    simpa only [← Matrix.mul_assoc, hQ, Matrix.one_mul] using h2
  have hdet : ∀ s, (Qᴴ * ((g s)ᴴ * g s) * Q).det.re = Complex.normSq (N s).det := by
    intro s
    have h : Qᴴ * ((g s)ᴴ * g s) * Q = (N s)ᴴ * N s := by
      calc Qᴴ * ((g s)ᴴ * g s) * Q = (g s * Q)ᴴ * (g s * Q) := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = (N s)ᴴ * (Qᴴ * Q) * N s := by
            rw [hN]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hQ, Matrix.mul_one]
    rw [h, Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  set a : σ → ℝ := fun s => Real.log (Complex.normSq (N s).det) with ha
  have hpair : ∀ s, a (τ s) + a s = 0 := by
    intro s
    have h : Complex.normSq (N (τ s)).det * Complex.normSq (N s).det = 1 := by
      rw [← map_mul, ← Matrix.det_mul, hNinv, Matrix.det_one, map_one]
    simp only [ha]
    rw [← Real.log_mul (left_ne_zero_of_mul_eq_one h) (right_ne_zero_of_mul_eq_one h), h, Real.log_one]
  have hasum : ∑ s, a s = 0 := by
    have h : ∑ s, (a (τ s) + a s) = 0 := Finset.sum_eq_zero fun s _ => hpair s
    rw [Finset.sum_add_distrib, Equiv.sum_comp τ a] at h
    linarith
  have htsum : ∑ s, (Matrix.trace (Qᴴ * H s * Q)).re = 0 := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.sum_mul, ← Matrix.mul_sum, hsum]
    simp
  have hJ := fun s => GlobalTheory.LogCompress.trace_log_le_log_det ι (Fin n) (H s) ((g s)ᴴ * g s) Q (hlog s) hQ
  have heq : ∀ s, (Matrix.trace (Qᴴ * H s * Q)).re = a s := by
    have h := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
      (f := fun s => (Matrix.trace (Qᴴ * H s * Q)).re) (g := a)
      (fun s _ => by have := (hJ s).1; rwa [hdet] at this)).1 (by rw [htsum, hasum])
    exact fun s => h s (Finset.mem_univ s)
  have hadj : ∀ s, ∃ M : Matrix (Fin n) (Fin n) ℂ, Qᴴ * g s = M * Qᴴ := by
    intro s
    obtain ⟨M, hM⟩ := (hJ s).2 (by rw [hdet]; exact heq s)
    have h1 : N s * N (τ s) = 1 := mul_eq_one_comm.1 (hNinv s)
    have h2 : (g s)ᴴ * Q = Q * (M * N (τ s)) := by
      rw [← Matrix.mul_assoc, ← hM, Matrix.mul_assoc (g s)ᴴ, hN, Matrix.mul_assoc, Matrix.mul_assoc, h1,
        Matrix.mul_one]
    refine ⟨(M * N (τ s))ᴴ, ?_⟩
    have h3 := congrArg Matrix.conjTranspose h2
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul Q] at h3
  refine ⟨LinearMap.ker (Matrix.mulVecLin Qᴴ), ?_, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩ v hv
    obtain ⟨M, hM⟩ := hadj s
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    rw [Matrix.mulVec_mulVec, hM, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  · rw [Submodule.disjoint_def]
    intro v hv hv'
    obtain ⟨x, rfl⟩ := (hmem v).1 hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hQ, Matrix.one_mulVec] at hv'
    rw [hv', Matrix.mulVec_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    refine Submodule.mem_sup.2 ⟨Q *ᵥ (Qᴴ *ᵥ v), (hmem _).2 ⟨_, rfl⟩, v - Q *ᵥ (Qᴴ *ᵥ v), ?_, by abel⟩
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_sub, Matrix.mulVec_mulVec (Qᴴ *ᵥ v), hQ,
      Matrix.one_mulVec, sub_self]

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.glFreeAlgebraToSpecialLinearEmb_injective_hom : ∀ (R A β κ : Type) [CommRing R] [CommRing A] [Algebra R A] [Fintype β] [DecidableEq β] [Fintype κ] [DecidableEq κ] (b : Module.Basis β R A), emb b (1 : GL κ A) = 1 ∧ (∀ g h : GL κ A, emb b (g * h) = emb b g * emb b h) ∧ (∀ g : GL κ A, (emb b g).det = 1 ∧ (emb b g).adjugate = emb b g⁻¹) ∧ Function.Injective (fun g : GL κ A => emb b g) := by
  first | exact @GlobalTheory.ClassFin.EmbHom.emb_hom | exact GlobalTheory.ClassFin.EmbHom.emb_hom | (intros; apply GlobalTheory.ClassFin.EmbHom.emb_hom <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.isCompletelyReducibleMatrixSet_transpose_image : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), SS Γ → SS (Matrix.transpose '' Γ) := by
  first | exact @GlobalTheory.ClassFin.ss_transpose | exact GlobalTheory.ClassFin.ss_transpose | (intros; apply GlobalTheory.ClassFin.ss_transpose <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem IsQuad.exists_base_value {F E : Type} [Field F] [Field E] [Algebra F E] {δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsQuad δ θ σ) (w : Valuation E ℤᵐ⁰) (h2 : w 2 = 1)
    (hδ : w (algebraMap F E δ) = 1) (x : E) : ∃ u : F, w x = w (algebraMap F E u) := by
  obtain ⟨a, b, hx⟩ := h.span x
  have hθ : w θ = 1 := by
    rw [← h.sq, map_pow] at hδ
    exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 hδ
  set y : E := algebraMap F E a - algebraMap F E b * θ with hy
  have ha : w (x + y) = w (algebraMap F E a) := by
    have : x + y = 2 * algebraMap F E a := by rw [hx, hy]; ring
    rw [this, map_mul, h2, one_mul]
  have hb : w (x - y) = w (algebraMap F E b) := by
    have : x - y = 2 * algebraMap F E b * θ := by rw [hx, hy]; ring
    rw [this, map_mul, map_mul, h2, hθ, one_mul, mul_one]
  have hn : x * y = algebraMap F E (a ^ 2 - δ * b ^ 2) := by
    rw [hx, hy, map_sub, map_mul, map_pow, map_pow, ← h.sq]; ring
  rcases lt_trichotomy (w x) (w y) with hlt | heq | hgt
  · have h1 : w y = w (algebraMap F E a) := by rw [← ha, w.map_add_eq_of_lt_right hlt]
    have hy0 : w y ≠ 0 := (lt_of_le_of_lt zero_le hlt).ne'
    refine ⟨(a ^ 2 - δ * b ^ 2) / a, ?_⟩
    rw [map_div₀, map_div₀, ← hn, ← h1, map_mul, mul_div_assoc, div_self hy0, mul_one]
  · have h1 : w (algebraMap F E a) ≤ w x := by
      rw [← ha]; exact (w.map_add x y).trans (max_le le_rfl heq.ge)
    have h3 : w (algebraMap F E b) ≤ w x := by
      rw [← hb]; exact (w.map_sub x y).trans (max_le le_rfl heq.ge)
    have h4 : w x ≤ max (w (algebraMap F E a)) (w (algebraMap F E b)) := by
      have := w.map_add (algebraMap F E a) (algebraMap F E b * θ)
      rwa [← hx, map_mul, hθ, mul_one] at this
    rcases le_max_iff.1 h4 with h5 | h5
    · exact ⟨a, le_antisymm h5 h1⟩
    · exact ⟨b, le_antisymm h5 h3⟩
  · exact ⟨a, by rw [← ha, w.map_add_eq_of_lt_left hgt]⟩

theorem valuation_unramified_of_unit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ → ∀ w : HeightOneSpectrum (𝓞 E), (w.under (𝓞 F)).valuation F 2 = 1 → (w.under (𝓞 F)).valuation F δ = 1 → ∀ x : F, w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x := by
  intro F E _ _ _ _ _ δ θ σ hq w h2 hδ
  obtain ⟨e, he, hw⟩ := (places_over F E).2.2 w
  obtain ⟨π, hπ⟩ := w.valuation_exists_uniformizer E
  have h2' : w.valuation E 2 = 1 := by
    have := hw 2
    rwa [map_ofNat, h2, one_pow] at this
  obtain ⟨u, hu⟩ := hq.exists_base_value (w.valuation E) h2' (by rw [hw, hδ, one_pow]) π
  rw [hπ, hw] at hu
  have hu0 : (w.under (𝓞 F)).valuation F u ≠ 0 := by
    intro h0
    rw [h0, zero_pow he.ne'] at hu
    exact WithZero.exp_ne_zero hu
  rw [← WithZero.exp_log hu0, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at hu
  have h1 : (e : ℤ) ∣ 1 := ⟨-WithZero.log ((w.under (𝓞 F)).valuation F u), by linear_combination -hu⟩
  have h3 : e = 1 := by
    have : e ∣ 1 := by exact_mod_cast h1
    exact Nat.dvd_one.1 this
  intro x
  rw [hw, h3, pow_one]

end GlobalTheory.QNorm
end
