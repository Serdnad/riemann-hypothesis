module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
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
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
public import Mathlib.RingTheory.Nakayama

@[expose] public section

section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem det_mul_map_det_eq_one_of_sesq {E : Type*} [Field E] {V : Type*} [AddCommGroup V]
    [Module E V] [FiniteDimensional E V] (σ : E →+* E) (H : V →ₗ[E] V →ₛₗ[σ] E)
    (hH : ∀ x, (∀ y, H x y = 0) → x = 0) (g : V →ₗ[E] V)
    (hg : ∀ x y, H (g x) (g y) = H x y) :
    LinearMap.det g * σ (LinearMap.det g) = 1 := by
  classical
  let b := Module.finBasis E V
  let S : Matrix _ _ E := Matrix.of fun i j => H (b i) (b j)
  let G := LinearMap.toMatrix b b g
  have hgb : ∀ j, g (b j) = ∑ i, G i j • b i := by
    intro j
    simp only [G, LinearMap.toMatrix_apply]
    exact (b.sum_repr (g (b j))).symm
  have hS : G.transpose * S * σ.mapMatrix G = S := by
    ext i j
    have h1 : S i j = H (g (b i)) (g (b j)) := (hg _ _).symm
    rw [h1, hgb, hgb]

    simp only [Matrix.mul_apply, Matrix.transpose_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    LinearMap.map_smulₛₗ, smul_eq_mul, S, Matrix.of_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_comm]
  have hdet : S.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hvS⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
    apply hv
    have hx : ∑ i, v i • b i = 0 := by
      apply hH
      have : H (∑ i, v i • b i) = 0 := by
        apply b.ext
        intro j
        have := congrFun hvS j

        simpa [Matrix.vecMul, dotProduct, S, map_sum, LinearMap.sum_apply] using this
      intro y
      rw [this]; rfl
    funext i
    exact Fintype.linearIndependent_iff.mp b.linearIndependent v hx i
  have hd := congrArg Matrix.det hS
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det] at hd
  have hG : G.det = LinearMap.det g := LinearMap.det_toMatrix b g
  rw [hG] at hd
  apply mul_left_cancel₀ hdet
  linear_combination hd

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open NumberField TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem det_one_add_comp_comm_field {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K V] [Module.Finite K W]
    (A : V →ₗ[K] W) (B : W →ₗ[K] V) :
    LinearMap.det (1 + A ∘ₗ B) = LinearMap.det (1 + B ∘ₗ A) := by
  classical
  let bV := Module.finBasis K V
  let bW := Module.finBasis K W
  rw [← LinearMap.det_toMatrix bW, ← LinearMap.det_toMatrix bV, map_add (f := _), map_add (f := _),
    LinearMap.toMatrix_comp bW bV bW, LinearMap.toMatrix_comp bV bW bV,
    LinearMap.toMatrix_one, LinearMap.toMatrix_one, Matrix.det_one_add_mul_comm]

theorem exists_det_congr_one : ∀ (E : Type) [Field E] [NumberField E] (La : Type) [AddCommGroup La] [Module (𝓞 E) La] [Module.Finite (𝓞 E) La] [Module.Projective (𝓞 E) La] (I : Ideal (𝓞 E)) (g : La →ₗ[𝓞 E] La), (∀ a, g a - a ∈ I • (⊤ : Submodule (𝓞 E) La)) → ∃ u : 𝓞 E, u - 1 ∈ I ∧ (u : E) = LinearMap.det (g.baseChange E) := by
  intro E _ _ La _ _ _ _ I g hg
  classical
  obtain ⟨n, p, i, -, -, hpi⟩ := Module.Finite.exists_comp_eq_id_of_projective (𝓞 E) La
  set N : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → 𝓞 E) := i ∘ₗ ((g - 1) ∘ₗ p) with hN
  have key : ∀ (x : La), x ∈ I • (⊤ : Submodule (𝓞 E) La) → ∀ k, i x k ∈ I := by
    intro x hx k
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y _
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
      exact I.mul_mem_right _ hr
    · intro x y hx hy
      rw [map_add (f := _), Pi.add_apply]
      exact I.add_mem hx hy
  refine ⟨LinearMap.det (1 + N), ?_, ?_⟩
  · rw [← Ideal.Quotient.eq, ← LinearMap.det_toMatrix', RingHom.map_det, map_one]
    have : (Ideal.Quotient.mk I).mapMatrix (LinearMap.toMatrix' (1 + N)) = 1 := by
      rw [map_add (f := _), map_add (f := _), LinearMap.toMatrix'_one, map_one, add_eq_left]
      ext a b
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.zero_apply,
        LinearMap.toMatrix'_apply]
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact key _ (hg _) _
    rw [this, Matrix.det_one]
  · have h1 : ((LinearMap.det (1 + N) : 𝓞 E) : E) = LinearMap.det ((1 + N).baseChange E) :=
      (LinearMap.det_baseChange (A := E) (1 + N)).symm
    rw [h1, LinearMap.baseChange_add, LinearMap.baseChange_one, hN, LinearMap.baseChange_comp,
      det_one_add_comp_comm_field, ← LinearMap.baseChange_comp, LinearMap.comp_assoc, hpi,
      LinearMap.comp_id, LinearMap.baseChange_sub, LinearMap.baseChange_one, add_sub_cancel]

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem root_of_unity_eq_one_of_dvd_sub_one :
    ∀ (E : Type) [Field E] [NumberField E] (u : 𝓞 E) (n M : ℕ),
      0 < n → u ^ n = 1 → 3 ≤ M → (M : 𝓞 E) ∣ u - 1 → u = 1 := by
  intro E _ _ u n M hn hu hM ⟨x, hx⟩
  have hlt : ∀ φ : E →+* ℂ, ‖φ (x : E)‖ < 1 := by
    intro φ
    have h1 : (φ (u : E)) ^ n = 1 := by
      have := congrArg (fun y : 𝓞 E => φ (y : E)) hu
      simpa using this
    have h2 : ‖φ (u : E)‖ = 1 := by
      have := congrArg norm h1
      rw [norm_pow, norm_one] at this
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this
    have h3 : φ (u : E) - 1 = (M : ℂ) * φ (x : E) := by
      have := congrArg (fun y : 𝓞 E => φ (y : E)) hx
      simpa using this
    have h4 : (M : ℝ) * ‖φ (x : E)‖ ≤ 2 := by
      have h5 := norm_sub_le (φ (u : E)) 1
      rw [h3, norm_mul, h2, norm_one, Complex.norm_natCast] at h5
      linarith
    have h6 : (3 : ℝ) ≤ M := by exact_mod_cast hM
    nlinarith [norm_nonneg (φ (x : E))]
  by_contra hne
  have hx0 : (x : E) ≠ 0 := by
    intro h0
    have : x = 0 := by exact_mod_cast h0
    rw [this, mul_zero, sub_eq_zero] at hx
    exact hne hx
  obtain ⟨k, hk, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_le_one E ℂ hx0
    (RingOfIntegers.isIntegral_coe x) (fun φ => (hlt φ).le)
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have h7 := congrArg (fun y : E => ‖φ y‖) hpow
  simp only [map_pow, norm_pow, map_one, norm_one] at h7
  have h8 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk.ne').1 h7
  exact (hlt φ).ne h8

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem rootOfUnity_eq_one_of_sub_one_mem_span : ∀ (E : Type) [Field E] [NumberField E] (z : 𝓞 E) (n M : ℕ), 0 < n → 3 ≤ M → z ^ n = 1 → z - 1 ∈ Ideal.span {(M : 𝓞 E)} → z = 1 := by
  intro E _ _ z n M hn hM hz hmem
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hmem
  suffices hw0 : w = 0 by
    rw [hw0, zero_mul] at hw
    exact sub_eq_zero.mp hw.symm
  have hMpos : (0 : ℝ) < M := by
    have : 0 < M := by omega
    exact_mod_cast this
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hzE : (z : E) ^ n = 1 := by
    have h := congrArg (algebraMap (𝓞 E) E) hz
    rw [map_pow, map_one] at h
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap]
    exact h
  have hwE : (w : E) * (M : E) = (z : E) - 1 := by
    have h := congrArg (algebraMap (𝓞 E) E) hw
    rw [map_mul, RingHom.map_sub, map_natCast, map_one] at h
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap w, NumberField.RingOfIntegers.coe_eq_algebraMap z]
    exact h
  have hbound : ∀ σ : E →ₐ[ℚ] ℂ, ‖σ (w : E)‖ ≤ 2 / M := by
    intro σ
    have hz1 : ‖σ (z : E)‖ = 1 := by
      have h1 : ‖σ (z : E)‖ ^ n = 1 := by
        rw [← norm_pow, ← map_pow, hzE, map_one, norm_one]
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h1
    have h2 : σ (w : E) * (M : ℂ) = σ (z : E) - 1 := by
      have h := congrArg σ hwE
      rw [map_mul, map_sub, map_natCast, map_one] at h
      exact h
    have h3 : ‖σ (w : E)‖ * (M : ℝ) ≤ 2 := by
      have h4 : ‖σ (w : E) * (M : ℂ)‖ = ‖σ (w : E)‖ * (M : ℝ) := by
        rw [norm_mul, Complex.norm_natCast]
      rw [← h4, h2]
      calc ‖σ (z : E) - 1‖ ≤ ‖σ (z : E)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [hz1, norm_one]; norm_num
    exact (le_div_iff₀ hMpos).mpr h3
  have hcard : Fintype.card (E →ₐ[ℚ] ℂ) ≠ 0 := by
    rw [AlgHom.card ℚ E ℂ]
    exact (Module.finrank_pos).ne'
  have hprod : ‖((Algebra.norm ℤ w : ℤ) : ℂ)‖ < 1 := by
    have h1 : ((Algebra.norm ℤ w : ℤ) : ℂ) = algebraMap ℚ ℂ (Algebra.norm ℚ (w : E)) := by
      rw [← Algebra.coe_norm_int, map_intCast]
    rw [h1, Algebra.norm_eq_prod_embeddings ℚ ℂ (w : E), norm_prod]
    calc ∏ σ : E →ₐ[ℚ] ℂ, ‖σ (w : E)‖ ≤ ∏ _σ : E →ₐ[ℚ] ℂ, (2 / M : ℝ) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun σ _ => hbound σ)
      _ = (2 / M : ℝ) ^ Fintype.card (E →ₐ[ℚ] ℂ) := by rw [Finset.prod_const, Finset.card_univ]
      _ < 1 := pow_lt_one₀ (by positivity) ((div_lt_one hMpos).mpr (by linarith)) hcard
  have hN : Algebra.norm ℤ w = 0 := by
    rw [Complex.norm_intCast] at hprod
    have habs : ((|Algebra.norm ℤ w| : ℤ) : ℝ) < 1 := by
      push_cast
      exact hprod
    have habs' : |Algebra.norm ℤ w| < 1 := by exact_mod_cast habs
    exact Int.abs_lt_one_iff.mp habs'
  exact Algebra.norm_eq_zero_iff.mp hN

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem prod_norm_embeddings_eq_abs_norm (F : Type) [Field F] [NumberField F] (α : F) :
    ∏ σ : F →+* ℂ, ‖σ α‖ = ((|Algebra.norm ℚ α| : ℚ) : ℝ) := by
  have h2 : ∏ σ : F →+* ℂ, σ α = ∏ σ : F →ₐ[ℚ] ℂ, σ α :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun σ => rfl)
  rw [← norm_prod, h2, ← Algebra.norm_eq_prod_embeddings ℚ ℂ α, eq_ratCast (algebraMap ℚ ℂ),
    Complex.norm_ratCast, Rat.cast_abs]

theorem norm_finite_embedding_eq_zpow (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (α : F) (k : ℤ)
    (h : v.valuation F α = WithZero.exp (-k)) :
    ‖FinitePlace.embedding v α‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) := by
  rw [FinitePlace.norm_embedding', h,
    WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero (a := -k)),
    WithZero.log_exp, NNReal.coe_zpow, NNReal.coe_natCast]

theorem sum_log_embeddings_eq (F : Type) [Field F] [NumberField F]
    (n : HeightOneSpectrum (𝓞 F) →₀ ℤ) (α : F) (hα : α ≠ 0)
    (hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F α = WithZero.exp (-(n v))) :
    ∑ σ : F →+* ℂ, Real.log ‖σ α‖ =
      n.sum fun v k => (k : ℝ) * Real.log (Ideal.absNorm v.asIdeal) := by
  have hσ : ∀ σ ∈ (Finset.univ : Finset (F →+* ℂ)), ‖σ α‖ ≠ 0 := fun σ _ =>
    norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hα)
  rw [← Real.log_prod hσ, prod_norm_embeddings_eq_abs_norm]
  have hv2 : ∀ v : HeightOneSpectrum (𝓞 F),
      ‖FinitePlace.embedding v α‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n v)) :=
    fun v => norm_finite_embedding_eq_zpow F v α (n v) (hv v)
  have key : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v α‖
      = ∏ᶠ w : FinitePlace F, w α := by
    rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F)).symm]
    simp only [FinitePlace.equivHeightOneSpectrum_symm_apply]
  have hprod : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v α‖
      = ∏ v ∈ n.support, (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n v)) := by
    simp only [hv2]
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hvs
    rw [Function.mem_mulSupport] at hvs
    by_contra hn
    simp only [Finset.mem_coe, Finsupp.mem_support_iff, not_not] at hn
    apply hvs
    simp [hn]
  have E0 := FinitePlace.prod_eq_inv_abs_norm hα
  rw [← key, hprod] at E0
  have hfac : ∀ v ∈ n.support, (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n v)) ≠ 0 := by
    intro v _
    apply zpow_ne_zero
    exact_mod_cast (mt Ideal.absNorm_eq_zero_iff.mp v.ne_bot)
  have L := congrArg Real.log E0
  push_cast at L ⊢
  rw [Real.log_prod hfac, Real.log_inv] at L
  simp only [Real.log_zpow] at L
  rw [Finsupp.sum]
  have hneg : ∑ v ∈ n.support, ((-(n v) : ℤ) : ℝ) * Real.log (Ideal.absNorm v.asIdeal)
      = -∑ v ∈ n.support, (n v : ℝ) * Real.log (Ideal.absNorm v.asIdeal) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    push_cast
    ring
  linarith

end GlobalTheory.CompanionTheory.Ar.Flat
end

section

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

theorem mem_ideal_smul_top_iff_forall_dual {O : Type*} [CommRing O] {L : Type*} [AddCommGroup L]
    [Module O L] [Module.Finite O L] [Module.Projective O L] (𝔟 : Ideal O) (x : L) :
    x ∈ 𝔟 • (⊤ : Submodule O L) ↔ ∀ φ : L →ₗ[O] O, φ x ∈ 𝔟 := by
  constructor
  · intro hx φ
    have hle : 𝔟 • (⊤ : Submodule O L) ≤ Submodule.comap φ 𝔟 := by
      rw [Submodule.smul_le]
      intro r hr n _
      rw [Submodule.mem_comap, map_smul, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ hr
    exact hle hx
  · intro h
    obtain ⟨s, hs⟩ := Module.Projective.out (R := O) (P := L)
    rw [← hs x, Finsupp.linearCombination_apply, Finsupp.sum]
    refine sum_mem fun y _ => ?_
    have hy : (s x) y ∈ 𝔟 := by
      simpa using h ((Finsupp.lapply y).comp s)
    exact Submodule.smul_mem_smul hy Submodule.mem_top

theorem mem_of_forall_mul_mem_ideal_mul {O : Type*} [CommRing O] [IsDedekindDomain O]
    {𝔪 𝔞 : Ideal O} (h𝔪 : 𝔪 ≠ ⊥) {c : O} (h : ∀ m ∈ 𝔪, m * c ∈ 𝔪 * 𝔞) : c ∈ 𝔞 := by
  have h0 : 𝔪 ≠ 0 := by rwa [Ne, Ideal.zero_eq_bot]
  have hle : 𝔪 * Ideal.span {c} ≤ 𝔪 * 𝔞 := by
    rw [Ideal.mul_le]
    intro r hr s hs
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton.mp hs
    rw [← mul_assoc]
    exact Ideal.mul_mem_right _ _ (h r hr)
  have hd : 𝔪 * 𝔞 ∣ 𝔪 * Ideal.span {c} := Ideal.dvd_iff_le.mpr hle
  rw [mul_dvd_mul_iff_left h0] at hd
  exact (Ideal.dvd_iff_le.mp hd) (Ideal.mem_span_singleton_self c)

theorem map_ideal_smul_top_iff_cancel : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] (L : Type) [AddCommGroup L] [Module O L] [Module.Finite O L] [Module.Projective O L] (𝔪 𝔞 : Ideal O) (T : L →ₗ[O] L), 𝔪 ≠ ⊥ → ((∀ x ∈ 𝔪 • (⊤ : Submodule O L), T x ∈ (𝔪 * 𝔞) • (⊤ : Submodule O L)) ↔ ∀ x, T x ∈ 𝔞 • (⊤ : Submodule O L)) := by
  intro O _ _ L _ _ _ _ 𝔪 𝔞 T h𝔪
  constructor
  · intro hT x
    rw [mem_ideal_smul_top_iff_forall_dual]
    intro φ
    refine mem_of_forall_mul_mem_ideal_mul h𝔪 fun m hm => ?_
    have hmx : m • x ∈ 𝔪 • (⊤ : Submodule O L) := Submodule.smul_mem_smul hm Submodule.mem_top
    have key := (mem_ideal_smul_top_iff_forall_dual (𝔪 * 𝔞) (T (m • x))).mp (hT _ hmx) φ
    rwa [map_smul, map_smul, smul_eq_mul] at key
  · intro hT x hx
    have hle : 𝔪 • (⊤ : Submodule O L) ≤ Submodule.comap T ((𝔪 * 𝔞) • (⊤ : Submodule O L)) := by
      rw [Submodule.smul_le]
      intro r hr n _
      rw [Submodule.mem_comap, map_smul, mem_ideal_smul_top_iff_forall_dual]
      intro φ
      rw [map_smul, smul_eq_mul]
      exact Ideal.mul_mem_mul hr ((mem_ideal_smul_top_iff_forall_dual 𝔞 (T n)).mp (hT n) φ)
    exact hle hx

end GlobalTheory.CompanionTheory.Ar.Cmp
end

section

open Matrix Filter Topology
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.CommAlg.SatOfInj

theorem mem_max_smul_top_iff {R M : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup M] [Module R M] {π : R} (hπ : Irreducible π) (x : M) :
    x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) ↔ ∃ z : M, x = π • z := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer π |>.mp hπ,
    Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, trivial, rfl⟩

theorem eq_zero_of_smul {R M : Type} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]
    [Module.IsTorsionFree R M] {a : R} (ha : a ≠ 0) {z : M} (h : a • z = 0) : z = 0 :=
  (smul_eq_zero.mp h).resolve_left ha

theorem pow_step {R P E : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup E] [Module R E] [Module.IsTorsionFree R E]
    (f : P →ₗ[R] E) {π : R} (hπ : Irreducible π)
    (hf : ∀ x : P, f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) →
      x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P))
    (n : ℕ) : ∀ (y : E), π ^ n • y ∈ LinearMap.range f → y ∈ LinearMap.range f := by
  induction n with
  | zero => intro y hy; simpa using hy
  | succ n ih =>
    intro y hy
    obtain ⟨x, hx⟩ := hy
    have hmem : f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) := by
      rw [mem_max_smul_top_iff hπ]
      exact ⟨π ^ n • y, by rw [hx, pow_succ', mul_smul]⟩
    obtain ⟨x', rfl⟩ := (mem_max_smul_top_iff hπ x).mp (hf x hmem)
    refine ih y ⟨x', ?_⟩
    have h0 : π • (f x' - π ^ n • y) = 0 := by
      rw [smul_sub, ← map_smul, hx, pow_succ', mul_smul, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_smul hπ.ne_zero h0)

theorem sat_of_inj_mod : ∀ (R P E : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [AddCommGroup P] [Module R P] [Module.Finite R P] [AddCommGroup E] [Module R E]
    [Module.IsTorsionFree R E] [Module.IsTorsionFree R P] (f : P →ₗ[R] E),
    (∀ x : P, f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) →
      x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R P)) →
    Function.Injective f ∧ ∀ (a : R) (y : E), a ≠ 0 → a • y ∈ LinearMap.range f →
      y ∈ LinearMap.range f := by
  intro R P E _ _ _ _ _ _ _ _ _ _ f hf
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    refine Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (IsLocalRing.maximalIdeal R) _
      (IsNoetherian.noetherian _) ?_ (IsLocalRing.maximalIdeal_le_jacobson _)
    intro x hx
    have hx0 : f x = 0 := hx
    have hmem : f x ∈ IsLocalRing.maximalIdeal R • (⊤ : Submodule R E) := by
      rw [hx0]; exact Submodule.zero_mem _
    obtain ⟨x', rfl⟩ := (mem_max_smul_top_iff hπ x).mp (hf x hmem)
    have hx' : f x' = 0 := by
      rw [map_smul] at hx0
      exact eq_zero_of_smul hπ.ne_zero hx0
    exact Submodule.smul_mem_smul
      ((IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ ▸ Ideal.mem_span_singleton_self π)
      (LinearMap.mem_ker.mpr hx')
  · intro a y ha hy
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hπ
    have h1 : π ^ n • ((u : R) • y) ∈ LinearMap.range f := by
      rw [smul_smul, mul_comm]
      exact hy
    have h2 := pow_step f hπ hf n _ h1
    have h3 := Submodule.smul_mem _ ((u⁻¹ : Rˣ) : R) h2
    rwa [smul_smul, Units.inv_mul, one_smul] at h3

end GlobalTheory.CompanionTheory.CommAlg.SatOfInj
end
