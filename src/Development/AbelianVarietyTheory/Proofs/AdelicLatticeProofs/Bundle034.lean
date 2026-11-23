module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle025
public import Formalism.UnipotentAdelicQuotients.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle027
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Basic.Complex.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle028
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle031
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle030
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle018
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle026
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.RingTheory.Adjoin.PowerBasis
public import Mathlib.RingTheory.Norm.Basic
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.exists_admissiblePlacesContainingPrime_superset_mono : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F], 0 < p → (∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∃ S, S₀ ⊆ S ∧ AdmP p F S) ∧ ∀ S T : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ T → AdmP p F S → AdmP p F T := by
  first | exact @GlobalTheory.CNorm.exists_admissiblePlaces_superset_and_mono | exact GlobalTheory.CNorm.exists_admissiblePlaces_superset_and_mono | (intros; apply GlobalTheory.CNorm.exists_admissiblePlaces_superset_and_mono <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem isUnit_of_norm_ne_zero {L A : Type} [Field L] [CommRing A] [Algebra L A]
    [Module.Finite L A] (y : A) (h : Algebra.norm L y ≠ 0) : IsUnit y := by
  have h1 : IsUnit (Algebra.lmul L A y) := by
    rw [LinearMap.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr (by rwa [Algebra.norm_apply] at h)
  obtain ⟨z, hz⟩ := ((Module.End.isUnit_iff _).mp h1).surjective 1
  exact IsUnit.of_mul_eq_one z (by simpa using hz)

theorem IsKum.nonempty_tensor_equiv {p : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E]
    {ζ δ : F} {θ : E} {σ : E ≃ₐ[F] E} (h : IsKum p ζ δ θ σ) (L : Type) [Field L] [Algebra F L] :
    Nonempty ((L ⊗[F] E) ≃ₐ[L] AdjoinRoot (X ^ p - C (algebraMap F L δ) : L[X])) := by
  have hp := h.prime
  have hmin := h.minpoly_eq
  have hint : IsIntegral F θ :=
    ⟨X ^ p - C δ, monic_X_pow_sub_C δ hp.ne_zero, by simp [h.pow]⟩
  let pb : PowerBasis F E := PowerBasis.ofAdjoinEqTop hint h.gen
  have hgen : pb.gen = θ := PowerBasis.ofAdjoinEqTop_gen hint h.gen
  set g : L[X] := X ^ p - C (algebraMap F L δ) with hg
  have hroot : AdjoinRoot.root g ^ p = algebraMap F (AdjoinRoot g) δ := by
    have := AdjoinRoot.eval₂_root g
    rw [hg, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at this
    rw [IsScalarTower.algebraMap_apply F L (AdjoinRoot g)]
    exact this
  let ψ : E →ₐ[F] AdjoinRoot g := pb.lift (AdjoinRoot.root g) (by
    rw [hgen, hmin]; simp [hroot])
  have hψ : ψ θ = AdjoinRoot.root g := (congrArg _ hgen.symm).trans (pb.lift_gen _ _)
  let a : (L ⊗[F] E) →ₐ[L] AdjoinRoot g :=
    Algebra.TensorProduct.lift (Algebra.ofId L _) ψ (fun _ _ => Commute.all _ _)
  let b : AdjoinRoot g →ₐ[L] (L ⊗[F] E) :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId L _) ((1 : L) ⊗ₜ[F] θ) (by
      rw [hg, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero, Algebra.TensorProduct.tmul_pow,
        one_pow, h.pow]
      change _ = algebraMap L (L ⊗[F] E) (algebraMap F L δ)
      rw [← IsScalarTower.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply',])
  have hb : b (AdjoinRoot.root g) = (1 : L) ⊗ₜ[F] θ := AdjoinRoot.liftAlgHom_root ..
  have ha : a ((1 : L) ⊗ₜ[F] θ) = AdjoinRoot.root g := by
    simp [a, hψ]
  refine ⟨AlgEquiv.ofAlgHom a b ?_ ?_⟩
  · apply AdjoinRoot.algHom_ext
    simp [ha, hb]
  · apply Algebra.TensorProduct.ext
    · exact Subsingleton.elim _ _
    · apply pb.algHom_ext
      rw [hgen]
      simp [ha, hb]

theorem mem_kNorm_of_tNorm : ∀ (p : ℕ) (F E L : Type) [Field F] [CharZero F] [Field E] [Algebra F E] [Field L] [Algebra F L] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ x : Fˣ, TNorm F E L (x : F) → x ∈ kNorm p (algebraMap F L) δ := by
  intro p F E L _ _ _ _ _ _ ζ δ θ σ h x ⟨y, hy⟩
  obtain ⟨e⟩ := h.nonempty_tensor_equiv L
  have : Module.Finite L (AdjoinRoot (X ^ p - C (algebraMap F L δ) : L[X])) :=
    (AdjoinRoot.powerBasis' (monic_X_pow_sub_C _ h.prime.ne_zero)).finite
  have hn : Algebra.norm L (e y) = algebraMap F L x := by
    rw [Algebra.norm_eq_of_algEquiv, hy]
  have hu : IsUnit (e y) := isUnit_of_norm_ne_zero _ (by
    rw [hn]; exact (_root_.map_ne_zero _).mpr x.ne_zero)
  rw [mem_kNorm]
  exact ⟨hu.unit, hn⟩

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

theorem _root_.GlobalTheory.T.exists_anisotropic_orthogonal_basis_hermitian : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∃ x : Fin n → Fin n → E, (∀ i, hermE c G (x i) (x i) ≠ 0) ∧ (∀ i j, i ≠ j → hermE c G (x i) (x j) = 0) ∧ Submodule.span E (Set.range x) = ⊤ := by
  first | exact @GlobalTheory.UnRep.exists_anisotropic_orthogonal_basis | exact GlobalTheory.UnRep.exists_anisotropic_orthogonal_basis | (intros; apply GlobalTheory.UnRep.exists_anisotropic_orthogonal_basis <;> assumption)
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem IsKum.sum_conj_eq {p : ℕ} {F E : Type} [Field F] [Field E] [Algebra F E] {ζ δ : F} {θ : E}
    {σ : E ≃ₐ[F] E} (h : IsKum p ζ δ θ σ) (a : ℕ → F) (k : ℕ) (hk : k < p) :
    ∑ j ∈ Finset.range p, algebraMap F E (((ζ ^ k)⁻¹) ^ j) *
        (σ ^ j) (∑ i ∈ Finset.range p, a i • θ ^ i) = (p : E) * (a k • θ ^ k) := by
  have hζ : ζ ≠ 0 := h.root.ne_zero h.prime.ne_zero
  have h1 : ∀ j, algebraMap F E (((ζ ^ k)⁻¹) ^ j) * (σ ^ j) (∑ i ∈ Finset.range p, a i • θ ^ i)
      = ∑ i ∈ Finset.range p, ((ζ ^ i / ζ ^ k) ^ j) • (a i • θ ^ i) := by
    intro j

    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_pow, map_pow (σ ^ j), h.pow_apply, div_eq_mul_inv]
    simp only [Algebra.smul_def, mul_pow, map_mul, map_pow]
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul]
  rw [Finset.sum_eq_single k]
  · rw [div_self (pow_ne_zero _ hζ)]
    simp [Algebra.smul_def]
  · intro i hi hik
    have hne : ζ ^ i / ζ ^ k ≠ 1 := by
      intro h0
      rw [div_eq_one_iff_eq (pow_ne_zero _ hζ)] at h0
      exact hik (h.root.pow_inj (Finset.mem_range.1 hi) hk h0)
    have hp : (ζ ^ i / ζ ^ k) ^ p = 1 := by
      rw [div_pow, ← pow_mul, ← pow_mul, mul_comm i, mul_comm k, pow_mul, pow_mul,
        h.root.pow_eq_one, one_pow, one_pow, div_one]
    rw [geom_sum_eq hne, hp, sub_self, zero_div, zero_smul]
  · intro h0
    exact absurd (Finset.mem_range.2 hk) h0

theorem exists_uniformizer_lt_one (E : Type) [Field E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (T : Finset (HeightOneSpectrum (𝓞 E))) (hw : w ∈ T) :
    ∃ y : E, w.valuation E y = WithZero.exp (-1) ∧ ∀ w' ∈ T, w'.valuation E y < 1 := by
  classical
  obtain ⟨π, hπ⟩ := w.intValuation_exists_uniformizer
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun v : HeightOneSpectrum (𝓞 E) => v.asIdeal) (fun _ => 2) (fun v _ => v.prime)
    (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun v => if v.1 = w then π else 0)
  have h1 : w.intValuation y = WithZero.exp (-1) := by
    have h2 := hy w hw
    simp only [if_true] at h2
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem] at h2
    have h3 : w.intValuation (y - π) < w.intValuation π := by
      rw [hπ]
      exact h2.trans_lt (WithZero.exp_lt_exp.2 (by norm_num))
    have := w.intValuation.map_add_eq_of_lt_right h3
    rwa [sub_add_cancel, hπ] at this
  refine ⟨(y : E), by rw [HeightOneSpectrum.valuation_of_algebraMap, h1], fun w' hw' => ?_⟩
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  by_cases hww : w' = w
  · rw [hww, h1, ← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.2 (by norm_num)
  · have h2 := hy w' hw'
    simp only [if_neg hww, sub_zero] at h2
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem] at h2
    rw [← WithZero.exp_zero]
    exact h2.trans_lt (WithZero.exp_lt_exp.2 (by norm_num))

theorem kummer_valuation_unramified : ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (ζ δ : F) (θ : E) (σ : E ≃ₐ[F] E), IsKum p ζ δ θ σ → ∀ w : HeightOneSpectrum (𝓞 E), (w.under (𝓞 F)).valuation F (p : F) = 1 → (w.under (𝓞 F)).valuation F δ = 1 → ∀ x : F, w.valuation E (algebraMap F E x) = (w.under (𝓞 F)).valuation F x := by
  intro p F E _ _ _ _ _ ζ δ θ σ h w hp hδ
  obtain ⟨e, he, hw⟩ := (places_over F E).2.2 w
  obtain ⟨-, -, hgal, -⟩ := kummer_galois p F E ζ δ θ σ h
  have hp0 := h.prime.ne_zero
  obtain ⟨y, hy1, hy2⟩ := exists_uniformizer_lt_one E w
    (finite_places_over F E (w.under (𝓞 F))).toFinset (by simp)
  have hconj : ∀ τ : E ≃ₐ[F] E, w.valuation E (τ y) < 1 := by
    intro τ
    obtain ⟨w', h1, h2⟩ := (galois_places_transitive F E).1 τ w
    rw [← h2]
    exact hy2 w' (by simpa using h1)
  have hint : IsIntegral F θ :=
    ⟨X ^ p - C δ, monic_X_pow_sub_C δ hp0, by simp [h.pow]⟩
  let pb : PowerBasis F E := PowerBasis.ofAdjoinEqTop hint h.gen
  have hgen : pb.gen = θ := PowerBasis.ofAdjoinEqTop_gen hint h.gen
  have hdim : pb.dim = p := by
    rw [← pb.natDegree_minpoly, hgen, h.minpoly_eq, natDegree_X_pow_sub_C _]
  obtain ⟨f, hf, hyf⟩ := pb.exists_eq_aeval y
  rw [hdim] at hf
  rw [hgen, Polynomial.aeval_eq_sum_range' hf] at hyf
  have hpE : w.valuation E (p : E) = 1 := by
    have := hw (p : F)
    rwa [map_natCast, hp, one_pow] at this
  have hθ : w.valuation E θ = 1 := by
    have := hw δ
    rw [hδ, one_pow, ← h.pow, map_pow] at this
    exact (pow_eq_one_iff_of_nonneg zero_le hp0).1 this
  have hζ : w.valuation E (algebraMap F E ζ) = 1 := by
    have : w.valuation E (algebraMap F E ζ) ^ p = 1 := by
      rw [← map_pow, ← map_pow, h.root.pow_eq_one, map_one, map_one]
    exact (pow_eq_one_iff_of_nonneg zero_le hp0).1 this
  have hco : ∀ k ∈ Finset.range p,
      w.valuation E (f.coeff k • θ ^ k) ≤ WithZero.exp (-1 : ℤ) ^ e := by
    intro k hk
    have h1 := h.sum_conj_eq f.coeff k (Finset.mem_range.1 hk)
    rw [← hyf] at h1
    have h2 : w.valuation E ((p : E) * (f.coeff k • θ ^ k)) < 1 := by
      rw [← h1]
      refine (w.valuation E).map_sum_lt one_ne_zero fun j _ => ?_
      rw [map_mul, map_pow, map_inv₀, map_pow, map_pow, map_inv₀, map_pow, hζ]
      simpa using hconj (σ ^ j)
    rw [map_mul, hpE, one_mul] at h2
    rw [Algebra.smul_def, map_mul, map_pow, hθ, one_pow, mul_one, hw] at h2 ⊢
    have h3 : (w.under (𝓞 F)).valuation F (f.coeff k) < 1 := by
      by_contra h4
      exact absurd h2 (not_lt.2 (one_le_pow₀ (not_lt.1 h4)))
    have h5 : (w.under (𝓞 F)).valuation F (f.coeff k) ≤ WithZero.exp (-1 : ℤ) := by
      rw [← WithZero.lt_mul_exp_iff_le WithZero.exp_ne_zero, ← WithZero.exp_add]
      simpa using h3
    exact pow_le_pow_left₀ zero_le h5 e
  have h6 : w.valuation E y ≤ WithZero.exp (-1 : ℤ) ^ e := by
    rw [hyf]
    exact (w.valuation E).map_sum_le hco
  rw [hy1, ← WithZero.exp_nsmul, WithZero.exp_le_exp, nsmul_eq_mul] at h6
  have h7 : e = 1 := by omega
  intro x
  rw [hw, h7, pow_one]

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem kNorm_eq_top_of_pow : ∀ (p : ℕ) (F L : Type) [Field F] [Field L] [CharZero L] (φ : F →+* L) (δ : F) (r : L), 0 < p → δ ≠ 0 → r ^ p = φ δ → kNorm p φ δ = ⊤ := by
  intro p F L _ _ _ φ δ r hp hδ hr
  have hφ : φ δ ≠ 0 := (map_ne_zero φ).2 hδ
  have hsep : (X ^ p - C (φ δ) : L[X]).Separable :=
    separable_X_pow_sub_C (φ δ) (Nat.cast_ne_zero.2 hp.ne') hφ
  have hm : (X ^ p - C (φ δ) : L[X]).Monic := monic_X_pow_sub_C _ hp.ne'
  have : IsReduced (AdjoinRoot (X ^ p - C (φ δ) : L[X])) :=
    (Ideal.isRadical_iff_quotient_reduced _).1
      (isRadical_iff_span_singleton.1 hsep.squarefree.isRadical)
  have : Module.Finite L (AdjoinRoot (X ^ p - C (φ δ) : L[X])) :=
    (AdjoinRoot.powerBasis' hm).finite
  let ψ : AdjoinRoot (X ^ p - C (φ δ) : L[X]) →ₐ[L] L :=
    AdjoinRoot.liftAlgHom _ (AlgHom.id L L) r (by simp [hr])
  rw [eq_top_iff]
  intro x _
  rw [mem_kNorm]
  exact GlobalTheory.CNorm.exists_unit_norm_eq_of_algHom L _ ψ (φ (x : F)) ((map_ne_zero φ).2 x.ne_zero)

end GlobalTheory.CNorm
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical HeckeCharacterZeroLocus.ThmBIn
open scoped TensorProduct ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.primeIdempotent_eq_indicator_prime : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ Φ : AE F E ≃+* (mixedSpace E × FiniteAdeleRing (𝓞 E) E), (∀ x : E, Φ (incA F E x) = (mixedEmbedding E x, algebraMap E _ x)) → (∀ y, finPart F E y ∈ intAE F E ↔ ∀ P, Valued.v ((Φ y).2 P) ≤ 1) → (∀ v ε, IsPlaceIdem F v ε → (Φ (algebraMap (AF F) (AE F E) ε)).1 = 0 ∧ ∀ P : HeightOneSpectrum (𝓞 E), (Φ (algebraMap (AF F) (AE F E) ε)).2 P = if P.under (𝓞 F) = v then 1 else 0) → ∀ P e f, IsPrimeIdem σ P e f → ((Φ e).1 = 0 ∧ (Φ e).2 P = 1 ∧ ∀ Q, Q ≠ P → (Φ e).2 Q = 0) := by
  first | exact @GlobalTheory.isPrimeIdem_eq_indicator | exact GlobalTheory.isPrimeIdem_eq_indicator | (intros; apply GlobalTheory.isPrimeIdem_eq_indicator <;> assumption)
end

section

open scoped ContDiff

theorem _root_.GlobalTheory.T.exists_normalise_meanSquare_of_cocompact' : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x : G, ∃ g ∈ Γ, g + x ∈ K) → ∀ f : G → ℂ, Continuous f → f ≠ 0 → (∀ g ∈ Γ, ∀ w, ‖f (g + w)‖ = ‖f w‖) → (∃ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure ∧ MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1) ∧ ∃ c : ℂ, ∀ (μ : MeasureTheory.Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → MeasureTheory.IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∫ w in 𝓕, ‖c * f w‖ ^ 2 ∂μ = 1 := by
  first | exact @GlobalTheory.exists_normalise_meanSquare_of_cocompact | exact GlobalTheory.exists_normalise_meanSquare_of_cocompact | (intros; apply GlobalTheory.exists_normalise_meanSquare_of_cocompact <;> assumption)
end

section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

theorem _root_.GlobalTheory.T.exists_infiniteAdele_tensor_equiv_mixedSpace :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 →
      (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) →
      ∃ θ : InfiniteAdeleRing F ⊗[F] E ≃+* mixedSpace E,
        (∀ x : E, θ (1 ⊗ₜ[F] x) = mixedEmbedding E x) ∧
        @Continuous _ _ inferInstance
          (moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)) θ.symm ∧
        ∀ u : (mixedSpace E)ˣ, (∀ w, ((u : mixedSpace E).2 w).im = 0) →
          ∃ a : (InfiniteAdeleRing F)ˣ, θ ((a : InfiniteAdeleRing F) ⊗ₜ[F] 1) = u := by
  exact GlobalTheory.InfAdeleMixed.exists_equiv_mixedSpace
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_rat_of_forall_complex_ringEquiv_fixed : ∀ z : ℂ, (∀ σ : ℂ ≃+* ℂ, σ z = z) → ∃ q : ℚ, z = q := by
  first | exact @GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed | exact GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed | (intros; apply GlobalTheory.ClassFin.exists_rat_of_forall_ringEquiv_fixed <;> assumption)
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.exists_global_uniformizer_residue_representatives : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), (∃ π : F, v.valuation F π = WithZero.exp (-1) ∧ Valued.v (algebraMap F (v.adicCompletion F) π) = WithZero.exp (-1)) ∧ (∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x) ∧ (∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (a : F)) < 1) ∧ ∃ R : Finset (v.adicCompletion F), R.card ≤ Ideal.absNorm v.asIdeal ∧ (∀ r ∈ R, Valued.v r ≤ 1) ∧ ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ r ∈ R, Valued.v (x - r) < 1 := by
  first | exact @GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives | exact GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives | (intros; apply GlobalTheory.QNorm.exists_uniformizer_and_residue_representatives <;> assumption)
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

theorem _root_.GlobalTheory.T.exists_common_denominator_nilpotent_coboundary : ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra ℚ B] [Algebra B A] [Algebra.FiniteType B A] [IsReduced A] [Nontrivial B], Function.Injective (algebraMap B A) → ∀ s : Finset A, (∀ f ∈ s, IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f)) → ∃ b : B, b ≠ 0 ∧ ∀ f ∈ s, ∃ b' : B, algebraMap B A b * f = algebraMap B A b' := by
  first | exact @GlobalTheory.exists_common_denominator_of_isNilpotent | exact GlobalTheory.exists_common_denominator_of_isNilpotent | (intros; apply GlobalTheory.exists_common_denominator_of_isNilpotent <;> assumption)
end
