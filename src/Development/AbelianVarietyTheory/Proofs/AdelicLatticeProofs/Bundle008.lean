module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Algebra.MvPolynomial.Funext

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_isQuad : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ →
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (θ : E) (σ : E ≃ₐ[F] E),
      IsQuad δ θ σ := by
  intro F _ _ δ hδ
  have hroot : ∀ b : F, b ^ 2 ≠ δ := fun b hb => hδ ⟨b, by rw [← hb, sq]⟩
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C δ) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two hroot
  have hmon : (Polynomial.X ^ 2 - Polynomial.C δ).Monic := Polynomial.monic_X_pow_sub_C δ two_ne_zero
  have hdeg : (Polynomial.X ^ 2 - Polynomial.C δ).natDegree = 2 := Polynomial.natDegree_X_pow_sub_C _
  have : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C δ)) := ⟨hirr⟩
  set p : Polynomial F := Polynomial.X ^ 2 - Polynomial.C δ with hp
  have hsq : AdjoinRoot.root p ^ 2 = AdjoinRoot.of p δ := by
    have h := AdjoinRoot.eval₂_root p
    rw [hp, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
    exact sub_eq_zero.mp h
  have hneg : Polynomial.eval₂ (↑(Algebra.ofId F (AdjoinRoot p)) : F →+* AdjoinRoot p)
      (-AdjoinRoot.root p) (Polynomial.X ^ 2 - Polynomial.C δ) = 0 := by
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, neg_sq, hsq, sub_eq_zero]
    rfl
  let τ : AdjoinRoot p →ₐ[F] AdjoinRoot p :=
    AdjoinRoot.liftAlgHom p (Algebra.ofId F (AdjoinRoot p)) (-AdjoinRoot.root p) hneg
  have hτ : τ (AdjoinRoot.root p) = -AdjoinRoot.root p := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hττ : τ.comp τ = AlgHom.id F (AdjoinRoot p) := by
    apply AdjoinRoot.algHom_ext
    simp only [AlgHom.comp_apply, AlgHom.id_apply, hτ, map_neg, neg_neg]
  have hp0 : p ≠ 0 := hmon.ne_zero
  have : Module.Finite F (AdjoinRoot p) := (AdjoinRoot.powerBasis hp0).finite
  have : CharZero (AdjoinRoot p) :=
    charZero_of_injective_algebraMap (algebraMap F (AdjoinRoot p)).injective
  have : FiniteDimensional ℚ (AdjoinRoot p) := Module.Finite.trans F (AdjoinRoot p)
  refine ⟨AdjoinRoot p, inferInstance, { }, inferInstance, AdjoinRoot.root p,
    AlgEquiv.ofAlgHom τ τ hττ hττ, ⟨hδ, ?_, hτ, ?_⟩⟩
  · rw [AdjoinRoot.algebraMap_eq]; exact hsq
  · intro x
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
    have hp1 : p ≠ 1 := fun h => by
      rw [h, Polynomial.natDegree_one] at hdeg; exact absurd hdeg (by norm_num)
    have hlt := Polynomial.natDegree_modByMonic_lt g hmon hp1
    rw [hdeg] at hlt
    have hr := Polynomial.eq_X_add_C_of_natDegree_le_one (Nat.lt_succ_iff.mp hlt)
    refine ⟨(g %ₘ p).coeff 0, (g %ₘ p).coeff 1, ?_⟩
    have hmk : AdjoinRoot.mk p g = AdjoinRoot.mk p (g %ₘ p) := by
      conv_lhs => rw [← Polynomial.modByMonic_add_div g p]
      rw [map_add (f := _), map_mul, AdjoinRoot.mk_self, zero_mul, add_zero]
    rw [hmk]
    conv_lhs => rw [hr]
    rw [map_add (f := _), map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X,
      AdjoinRoot.algebraMap_eq, add_comm]

end GlobalTheory.QNorm
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.intValuation_of_eq_comap {R : Type} [CommRing R] [IsDedekindDomain R]
    (e : R ≃+* R) (w w' : HeightOneSpectrum R) (h : w'.asIdeal = w.asIdeal.comap e) (x : R) :
    w'.intValuation x = w.intValuation (e x) := by
  have hmem : ∀ n : ℕ, x ∈ w'.asIdeal ^ n ↔ e x ∈ w.asIdeal ^ n := by
    intro n
    rw [h, ← Ideal.map_symm, ← Ideal.map_pow, Ideal.map_symm, Ideal.mem_comap]
  have hle : ∀ n : ℕ, w'.intValuation x ≤ WithZero.exp (-(n : ℤ)) ↔
      w.intValuation (e x) ≤ WithZero.exp (-(n : ℤ)) := fun n => by
    rw [HeightOneSpectrum.intValuation_le_pow_iff_mem,
      HeightOneSpectrum.intValuation_le_pow_iff_mem, hmem]
  by_cases hx : x = 0
  · subst hx
    simp
  · have hex : e x ≠ 0 := fun h0 => hx (e.injective (h0.trans (map_zero e).symm))
    rw [HeightOneSpectrum.intValuation_if_neg _ hx, HeightOneSpectrum.intValuation_if_neg _ hex]
      at hle ⊢
    set a := (Associates.mk w'.asIdeal).count (Associates.mk (Ideal.span {x})).factors
    set b := (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {e x})).factors
    have h1 := (hle a).1 le_rfl
    have h2 := (hle b).2 le_rfl
    simp only [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le] at h1 h2
    rw [le_antisymm h1 h2]

open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.valuation_of_eq_comap {E : Type} [Field E] [NumberField E] (σ : E ≃+* E)
    (w w' : HeightOneSpectrum (𝓞 E))
    (h : w'.asIdeal = w.asIdeal.comap (RingOfIntegers.mapRingEquiv σ)) (y : E) :
    w'.valuation E y = w.valuation E (σ y) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) y
  have hσ : ∀ r : 𝓞 E, σ (algebraMap (𝓞 E) E r) =
      algebraMap (𝓞 E) E (RingOfIntegers.mapRingEquiv σ r) := fun r => rfl
  rw [map_div₀ σ, hσ, hσ, map_div₀, map_div₀]
  simp only [HeightOneSpectrum.valuation_of_algebraMap]
  rw [_root_.GlobalTheory.QNorm.intValuation_of_eq_comap _ w w' h a,
    _root_.GlobalTheory.QNorm.intValuation_of_eq_comap _ w w' h b]

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma ringOfIntegers_mapRingEquiv_algebraMap {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : 𝓞 F) :
    RingOfIntegers.mapRingEquiv (σ : E ≃+* E) (algebraMap (𝓞 F) (𝓞 E) n) =
      algebraMap (𝓞 F) (𝓞 E) n := by
  ext
  rw [show ((algebraMap (𝓞 F) (𝓞 E) n : 𝓞 E) : E) = algebraMap F E (n : F) from rfl]
  exact σ.commutes _

open NumberField IsDedekindDomain in
open scoped WithZero in
private lemma exists_algebraMap_eq_mul_conj_of_isQuad {F E : Type} [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] {δ : F} {θ : E} {σ : E ≃ₐ[F] E}
    (hq : _root_.GlobalTheory.QNorm.IsQuad δ θ σ) (x : 𝓞 E) :
    ∃ n : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) n = x * RingOfIntegers.mapRingEquiv (σ : E ≃+* E) x := by
  obtain ⟨a, b, hab⟩ := hq.span (x : E)
  have hprod : (x : E) * σ (x : E) = algebraMap F E (a ^ 2 - b ^ 2 * δ) := by
    rw [hab]
    simp only [map_add (f := _), map_mul, AlgEquiv.commutes, hq.conj]
    rw [map_sub, map_mul, map_pow, map_pow, ← hq.sq]
    ring
  have hint : IsIntegral ℤ (algebraMap F E (a ^ 2 - b ^ 2 * δ)) := by
    rw [← hprod]
    exact (RingOfIntegers.isIntegral_coe x).mul
      (RingOfIntegers.isIntegral_coe (RingOfIntegers.mapRingEquiv (σ : E ≃+* E) x))
  refine ⟨⟨a ^ 2 - b ^ 2 * δ,
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ F E) (algebraMap F E).injective).mp hint⟩, ?_⟩
  ext
  exact hprod.symm

open NumberField IsDedekindDomain in
open scoped WithZero in
theorem _root_.GlobalTheory.QNorm.conj_places_transitive : ∀ (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (δ : F) (θ : E) (σ : E ≃ₐ[F] E), _root_.GlobalTheory.QNorm.IsQuad δ θ σ →
    (∀ w : HeightOneSpectrum (𝓞 E), ∃ w' : HeightOneSpectrum (𝓞 E),
      w'.under (𝓞 F) = w.under (𝓞 F) ∧ ∀ y : E, w'.valuation E y = w.valuation E (σ y)) ∧
    ∀ w w' : HeightOneSpectrum (𝓞 E), w'.under (𝓞 F) = w.under (𝓞 F) →
      w' = w ∨ ∀ y : E, w'.valuation E y = w.valuation E (σ y) := by
  intro F E _ _ _ _ _ δ θ σ hq
  set e := RingOfIntegers.mapRingEquiv (σ : E ≃+* E) with he
  refine ⟨fun w => ?_, fun w w' hunder => ?_⟩
  · refine ⟨HeightOneSpectrum.comap (e : 𝓞 E →+* 𝓞 E) e.surjective w, ?_, fun y =>
      _root_.GlobalTheory.QNorm.valuation_of_eq_comap (σ : E ≃+* E) w _ rfl y⟩
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal]
    ext n
    change e (algebraMap (𝓞 F) (𝓞 E) n) ∈ w.asIdeal ↔ algebraMap (𝓞 F) (𝓞 E) n ∈ w.asIdeal
    rw [he, ringOfIntegers_mapRingEquiv_algebraMap]
  · by_cases hw : w' = w
    · exact Or.inl hw
    right
    refine _root_.GlobalTheory.QNorm.valuation_of_eq_comap (σ : E ≃+* E) w w' ?_
    by_contra hne
    have h1 : ¬ w'.asIdeal ≤ w.asIdeal := fun hle =>
      hw (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top hle))
    have h2 : ¬ w'.asIdeal ≤ w.asIdeal.comap e := fun hle =>
      hne (w'.isMaximal.eq_of_le (Ideal.comap_ne_top _ w.isPrime.ne_top) hle)
    have hns : ¬ ((w'.asIdeal : Set (𝓞 E)) ⊆ (w.asIdeal : Set (𝓞 E)) ∪ (w.asIdeal.comap e)) :=
      fun hs => (Ideal.subset_union.mp hs).elim h1 h2
    rw [Set.not_subset] at hns
    obtain ⟨x, hx, hxn⟩ := hns
    simp only [Set.mem_union, SetLike.mem_coe, Ideal.mem_comap, not_or] at hxn
    obtain ⟨n, hn⟩ := exists_algebraMap_eq_mul_conj_of_isQuad hq x
    have hnw' : n ∈ (w'.under (𝓞 F)).asIdeal := by
      rw [HeightOneSpectrum.under_asIdeal]
      change algebraMap (𝓞 F) (𝓞 E) n ∈ w'.asIdeal
      rw [hn]
      exact Ideal.mul_mem_right _ _ hx
    rw [hunder, HeightOneSpectrum.under_asIdeal] at hnw'
    change algebraMap (𝓞 F) (𝓞 E) n ∈ w.asIdeal at hnw'
    rw [hn] at hnw'
    rcases w.isPrime.mem_or_mem hnw' with h | h
    · exact hxn.1 h
    · exact hxn.2 h

end GlobalTheory.QNorm
end

section

open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.Calc

variable {R : Type} [CommRing R] {n : ℕ} (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R)

theorem hf_add_left (x x' y : Fin n → R) : hf σ G (x + x') y = hf σ G x y + hf σ G x' y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_add_right (x y y' : Fin n → R) : hf σ G x (y + y') = hf σ G x y + hf σ G x y' := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_left (c : R) (x y : Fin n → R) : hf σ G (c • x) y = c * hf σ G x y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_smul_right (c : R) (x y : Fin n → R) : hf σ G x (c • y) = σ c * hf σ G x y := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hf_conj (hσ : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a) (x y : Fin n → R) :
    σ (hf σ G x y) = hf σ G y x := by

  simp only [hf, map_sum, map_mul, hσ, hG]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem tv_mulVec (x : Fin n → R) (t : R) (v : Fin n → R) :
    tv σ G x t *ᵥ v = v + (t * hf σ G v x) • x := by
  rw [tv, Matrix.add_mulVec, Matrix.one_mulVec]
  ext a
  simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  simp only [hf]
  simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem ext_mulVec {A B : Matrix (Fin n) (Fin n) R} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa using this

theorem tv_mul (x : Fin n → R) (t t' : R) :
    tv σ G x t * tv σ G x t' = tv σ G x (t + t' + t * t' * hf σ G x x) := by
  refine ext_mulVec fun v => ?_
  rw [← Matrix.mulVec_mulVec, tv_mulVec, tv_mulVec, tv_mulVec, hf_add_left, hf_smul_left,
    add_assoc, ← add_smul]
  congr 2
  ring

theorem tv_det (x : Fin n → R) (t : R) : (tv σ G x t).det = 1 + t * hf σ G x x := by
  have h : tv σ G x t = 1 + Matrix.replicateCol Unit (t • x) *
      Matrix.replicateRow Unit (fun b => ∑ e, G b e * σ (x e)) := by
    rw [tv]
    congr 1
    ext a b
    simp [Matrix.mul_apply]
  rw [h, Matrix.det_one_add_replicateCol_mul_replicateRow]
  congr 1
  simp only [dotProduct, hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => ?_
  ring

theorem isU_tv (hσ : ∀ a, σ (σ a) = a) (hG : ∀ a b, σ (G a b) = G b a) (x : Fin n → R) (t : R)
    (h : t + σ t + t * σ t * hf σ G x x = 0) : IsU σ G (tv σ G x t) := by
  intro v w
  rw [tv_mulVec, tv_mulVec]
  simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, map_mul, hf_conj σ G hσ hG]
  linear_combination (hf σ G v x * hf σ G x w) * h

theorem conj_tv (γ : Matrix (Fin n) (Fin n) R) (x : Fin n → R) (t : R) (h : IsU σ G γ) :
    γ * tv σ G x t = tv σ G (γ *ᵥ x) t * γ := by
  refine ext_mulVec fun v => ?_
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, tv_mulVec, tv_mulVec, h, Matrix.mulVec_add,
    Matrix.mulVec_smul]

theorem tv_smul (a : R) (x : Fin n → R) (t : R) :
    tv σ G (a • x) t = tv σ G x (t * a * σ a) := by
  refine ext_mulVec fun v => ?_
  rw [tv_mulVec, tv_mulVec, hf_smul_right, smul_smul]
  congr 2
  ring

theorem isU_mul (γ γ' : Matrix (Fin n) (Fin n) R) (h : IsU σ G γ) (h' : IsU σ G γ') :
    IsU σ G (γ * γ') := by
  intro v w
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h, h']

theorem calculus : ∀ (R : Type) [CommRing R] (n : ℕ) (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R), (∀ a, σ (σ a) = a) → (∀ a b, σ (G a b) = G b a) → (∀ x y, σ (hf σ G x y) = hf σ G y x) ∧ (∀ x t v, tv σ G x t *ᵥ v = v + (t * hf σ G v x) • x) ∧ (∀ x t t', tv σ G x t * tv σ G x t' = tv σ G x (t + t' + t * t' * hf σ G x x)) ∧ (∀ x t, (tv σ G x t).det = 1 + t * hf σ G x x) ∧ (∀ x t, t + σ t + t * σ t * hf σ G x x = 0 → IsU σ G (tv σ G x t)) ∧ (∀ γ x t, IsU σ G γ → γ * tv σ G x t = tv σ G (γ *ᵥ x) t * γ) ∧ (∀ (a : R) x t, tv σ G (a • x) t = tv σ G x (t * a * σ a)) ∧ (∀ γ γ', IsU σ G γ → IsU σ G γ' → IsU σ G (γ * γ')) :=
  fun _ _ _ σ G hσ hG => ⟨hf_conj σ G hσ hG, tv_mulVec σ G, tv_mul σ G, tv_det σ G, isU_tv σ G hσ hG,
    conj_tv σ G, tv_smul σ G, isU_mul σ G⟩

end GlobalTheory.UTrans.Calc
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.HilbertFin

open MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    evC (ltr g f) y = evC f (g * y) := by
  unfold evC ltr
  induction f using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp]
    simp [Matrix.mul_apply]

omit [DecidableEq ι] in
theorem isInv_iff (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ) :
    IsInv Γ f ↔ ∀ g ∈ Γ, ltr g f = f := by
  constructor
  · intro h g hg
    apply MvPolynomial.funext
    intro x
    have := h g hg (Matrix.of fun i j => x (i, j))
    rw [← evC_ltr] at this
    exact this
  · intro h g hg y
    rw [← evC_ltr, h g hg]

omit [DecidableEq ι] in
theorem ltr_homog (g : Matrix ι ι ℂ) {f : MvPolynomial (ι × ι) ℂ} {n : ℕ}
    (hf : f.IsHomogeneous n) : (ltr g f).IsHomogeneous n := by
  have := hf.aeval (fun ij : ι × ι => ∑ k, MvPolynomial.C (g ij.1 k) * (MvPolynomial.X (k, ij.2) : MvPolynomial (ι × ι) ℂ))
    (n := 1) (fun ij => IsHomogeneous.sum _ _ _ fun k _ => by
      simpa using (isHomogeneous_C (ι × ι) (g ij.1 k)).mul (isHomogeneous_X ℂ (k, ij.2)))
  rw [one_mul] at this
  exact this

omit [DecidableEq ι] in
theorem ltr_comp (g : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) (n : ℕ) :
    ltr g (homogeneousComponent n f) = homogeneousComponent n (ltr g f) := by
  conv_lhs => rw [← sum_homogeneousComponent f]
  conv_rhs => rw [← sum_homogeneousComponent f]

  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := homogeneousComponent_isHomogeneous i f
  rw [homogeneousComponent_of_mem h1, homogeneousComponent_of_mem (ltr_homog g h1)]
  split_ifs <;> simp

omit [DecidableEq ι] in
theorem isInv_comp {Γ : Set (Matrix ι ι ℂ)} {f : MvPolynomial (ι × ι) ℂ} (hf : IsInv Γ f) (n : ℕ) :
    IsInv Γ (homogeneousComponent n f) := by
  rw [isInv_iff] at hf ⊢
  intro g hg
  rw [ltr_comp, hf g hg]

theorem hilbert_finiteness : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (Rey : MvPolynomial (ι × ι) ℂ →ₗ[ℂ] MvPolynomial (ι × ι) ℂ), IsReynolds Γ Rey → ∃ s : Finset (MvPolynomial (ι × ι) ℂ), (∀ F ∈ s, IsInv Γ F ∧ ∃ n, F.IsHomogeneous n) ∧ ∀ f, IsInv Γ f → f ∈ Algebra.adjoin ℂ (s : Set (MvPolynomial (ι × ι) ℂ)) := by
  intro ι _ _ Γ Rey hR
  classical
  set S : Set (MvPolynomial (ι × ι) ℂ) := {F | IsInv Γ F ∧ ∃ n, 0 < n ∧ F.IsHomogeneous n} with hS
  have hfg : (Submodule.span (MvPolynomial (ι × ι) ℂ) S).FG := IsNoetherian.noetherian _
  obtain ⟨s, hsS, hs⟩ := (Submodule.fg_span_iff_fg_span_finset_subset S).1 hfg
  refine ⟨s, fun F hF => ⟨(hsS hF).1, (hsS hF).2.imp fun n h => h.2⟩, ?_⟩
  have key : ∀ n : ℕ, ∀ f, IsInv Γ f → f.IsHomogeneous n →
      f ∈ Algebra.adjoin ℂ (s : Set (MvPolynomial (ι × ι) ℂ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro f hf hn
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · have : f = C (AddMonoidAlgebra.coeff f 0) := by
          rw [← homogeneousComponent_zero, homogeneousComponent_of_mem hn, if_pos rfl]
        rw [this]
        exact Subalgebra.algebraMap_mem _ _
      · have hmem : f ∈ Submodule.span (MvPolynomial (ι × ι) ℂ) (s : Set (MvPolynomial (ι × ι) ℂ)) := by
          rw [← hs]
          exact Submodule.subset_span ⟨hf, n, hpos, hn⟩
        obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 hmem
        have h1 : f = ∑ F ∈ s, F * Rey (c F) := by

          conv_lhs => rw [← hR.fix f hf, ← hc, map_sum]
          refine Finset.sum_congr rfl fun F hF => ?_
          rw [smul_eq_mul, mul_comm, hR.mul _ _ (hsS hF).1]
        have h2 : f = homogeneousComponent n f := by
          rw [homogeneousComponent_of_mem hn, if_pos rfl]

        rw [h2, h1, map_sum]
        refine Subalgebra.sum_mem _ fun F hF => ?_
        obtain ⟨-, d, hd, hFd⟩ := hsS hF

        rw [← sum_homogeneousComponent (Rey (c F)), Finset.mul_sum, map_sum]
        refine Subalgebra.sum_mem _ fun i _ => ?_
        have h3 := homogeneousComponent_isHomogeneous i (Rey (c F))
        rw [homogeneousComponent_of_mem (hFd.mul h3)]
        split_ifs with h
        · exact Subalgebra.mul_mem _ (Algebra.subset_adjoin hF)
            (ih i (by omega) _ (isInv_comp (hR.inv _) i) h3)
        · exact Subalgebra.zero_mem _
  intro f hf
  rw [← sum_homogeneousComponent f]
  exact Subalgebra.sum_mem _ fun i _ =>
    key i _ (isInv_comp hf i) (homogeneousComponent_isHomogeneous i f)

end GlobalTheory.ClassFin.HilbertFin
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_unit_valuation_eq_of_adm :
    ∀ (F : Type) [Field F] [NumberField F] (S T : Finset (HeightOneSpectrum (𝓞 F)))
      (n : HeightOneSpectrum (𝓞 F) → ℤ), admitted F S → (∀ v, v ∉ T → n v = 0) →
      ∃ a : Fˣ, ∀ v, v ∉ S → v.valuation F (a : F) = WithZero.exp (n v) := by
  intro F _ _ S T n hS hT
  classical
  have key : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∃ π : Fˣ,
      v.valuation F (π : F) = WithZero.exp (-1) ∧
        ∀ w : HeightOneSpectrum (𝓞 F), w ∉ S → w ≠ v → w.valuation F (π : F) = 1 := by
    intro v hv
    obtain ⟨-, π, h1, h2⟩ := hS v hv
    have hπ0 : π ≠ 0 := by
      rintro rfl
      rw [map_zero] at h1
      exact WithZero.exp_ne_zero h1.symm
    exact ⟨Units.mk0 π hπ0, h1, h2⟩
  choose! π hπ1 hπ2 using key
  refine ⟨∏ w ∈ T.filter (· ∉ S), (π w) ^ (-n w), ?_⟩
  intro v hv
  simp only [Units.coe_prod, Units.val_zpow_eq_zpow_val, map_prod, map_zpow₀]
  by_cases hvT : v ∈ T
  · rw [Finset.prod_eq_single v]
    · rw [hπ1 v hv, ← WithZero.exp_zsmul]
      congr 1
      simp
    · intro w hw hwv
      rw [hπ2 w (Finset.mem_filter.1 hw).2 v hv (Ne.symm hwv), one_zpow]
    · intro h
      exact absurd (Finset.mem_filter.2 ⟨hvT, hv⟩) h
  · rw [hT v hvT, WithZero.exp_zero]
    refine Finset.prod_eq_one fun w hw => ?_
    have hne : v ≠ w := fun h => hvT (h ▸ (Finset.mem_filter.1 hw).1)
    rw [hπ2 w (Finset.mem_filter.1 hw).2 v hv hne, one_zpow]

end GlobalTheory.QNorm
end
