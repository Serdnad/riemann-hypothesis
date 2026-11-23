module

public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.Algebra.Module.ZLattice.Covolume
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Algebra.Order.Archimedean.Real.Hom
public import Mathlib.Analysis.Complex.Exponential
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Order
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
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.ExpDecay

@[expose] public section

section

open NumberField Module
open scoped nonZeroDivisors

namespace GlobalTheory

theorem card_mul_rpow_prod_le_sum {ι : Type*} [Fintype ι] [Nonempty ι] (z : ι → ℝ)
    (hz : ∀ i, 0 ≤ z i) :
    (Fintype.card ι : ℝ) * (∏ i, z i) ^ ((Fintype.card ι : ℝ)⁻¹) ≤ ∑ i, z i := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ : ι => (Fintype.card ι : ℝ)⁻¹) z (fun _ _ => by positivity)
    (by simp [hc.ne']) (fun i _ => hz i)
  rw [Real.finsetProd_rpow _ _ (fun i _ => hz i), ← Finset.mul_sum] at h
  calc _ ≤ (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ)⁻¹ * ∑ i, z i) := by gcongr
    _ = _ := by field_simp

section General

variable {K : Type*} [Field K] [NumberField K]

theorem norm_eq_prod_complexEmbeddings (x : K) :
    ((Algebra.norm ℚ x : ℚ) : ℂ) = ∏ σ : K →+* ℂ, σ x := by
  rw [Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => rfl), ← Algebra.norm_eq_prod_embeddings ℚ ℂ x]
  simp

theorem trace_eq_sum_complexEmbeddings (x : K) :
    ((Algebra.trace ℚ K x : ℚ) : ℂ) = ∑ σ : K →+* ℂ, σ x := by
  rw [Fintype.sum_equiv (RingHom.equivRatAlgHom K ℂ) (fun f => f x) (fun φ => φ x)
    (fun _ => rfl), ← trace_eq_sum_embeddings ℂ (K := ℚ) (x := x)]
  simp

theorem abs_norm_eq_prod_complexEmbeddings (x : K) :
    |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∏ σ : K →+* ℂ, ‖σ x‖ := by
  rw [← norm_prod, ← norm_eq_prod_complexEmbeddings, Complex.norm_ratCast]

theorem finrank_mul_abs_norm_rpow_le_sum (x : K) :
    (finrank ℚ K : ℝ) * |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ ((finrank ℚ K : ℝ)⁻¹)
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ := by
  rw [abs_norm_eq_prod_complexEmbeddings, ← Embeddings.card K ℂ]
  exact card_mul_rpow_prod_le_sum _ fun _ => norm_nonneg _

theorem finrank_mul_abs_norm_rpow_le_sum_sq (x : K) :
    (finrank ℚ K : ℝ) * |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ (2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  have h := finrank_mul_abs_norm_rpow_le_sum (x ^ 2)
  simp only [map_pow, norm_pow, Rat.cast_pow, abs_pow] at h
  rwa [div_eq_mul_inv, Real.rpow_mul (abs_nonneg _), Real.rpow_two]

theorem one_le_abs_norm_of_isIntegral {x : K} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) :
    1 ≤ |Algebra.norm ℚ x| := by
  have hn : IsIntegral ℤ (Algebra.norm ℚ x) := Algebra.isIntegral_norm ℚ hx
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hn
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, Algebra.norm_eq_zero_iff] at hm
    exact h0 hm
  rw [← hm, eq_intCast]
  exact_mod_cast Int.one_le_abs hm0

theorem absNorm_le_abs_norm_of_mem {J : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ J)
    (h0 : x ≠ 0) : FractionalIdeal.absNorm J ≤ |Algebra.norm ℚ x| := by
  have hJ : J ≠ 0 := by
    rintro rfl
    exact h0 ((FractionalIdeal.mem_zero_iff _).mp hx)
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ x * J⁻¹ ≤ 1 := by
    calc _ ≤ J * J⁻¹ := by
          gcongr
          exact FractionalIdeal.spanSingleton_le_iff_mem.mpr hx
      _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hI' : FractionalIdeal.spanSingleton (𝓞 K)⁰ x = I * J := by
    rw [hI, inv_mul_cancel_right₀ hJ]
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    exact h0 (by simpa using hI')
  have h1 : (1 : ℚ) ≤ Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
  rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), hI', map_mul,
    FractionalIdeal.coeIdeal_absNorm]
  exact le_mul_of_one_le_left (FractionalIdeal.absNorm_nonneg _) h1

theorem finrank_mul_absNorm_rpow_le_sum_sq {J : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ J)
    (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) * ((FractionalIdeal.absNorm J : ℚ) : ℝ) ^ (2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  refine le_trans ?_ (finrank_mul_abs_norm_rpow_le_sum_sq x)
  have h1 : ((FractionalIdeal.absNorm J : ℚ) : ℝ) ≤ |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    exact_mod_cast absNorm_le_abs_norm_of_mem hx h0
  have h2 : (0 : ℝ) ≤ ((FractionalIdeal.absNorm J : ℚ) : ℝ) := by
    exact_mod_cast FractionalIdeal.absNorm_nonneg J
  gcongr


variable (K) in
theorem dual_one_eq_inv_differentIdeal :
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)
      = (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
  rw [coeIdeal_differentIdeal ℤ ℚ K (𝓞 K), inv_inv]


variable (K) in
theorem absNorm_inv_differentIdeal :
    FractionalIdeal.absNorm (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹
      = |(discr K : ℚ)|⁻¹ := by
  rw [map_inv₀, FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal K]
  simp

theorem finrank_mul_discr_rpow_le_sum_sq {x : K}
    (hx : x ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) * |(discr K : ℝ)| ^ (-2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  have h := finrank_mul_absNorm_rpow_le_sum_sq hx h0
  rw [absNorm_inv_differentIdeal] at h
  rw [neg_div, Real.rpow_neg (abs_nonneg _), ← Real.inv_rpow (abs_nonneg _)]
  simpa using h

theorem finrank_div_rootDiscr_sq_le_sum_sq {x : K}
    (hx : x ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) / rootDiscr K ^ 2 ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  have h := finrank_mul_discr_rpow_le_sum_sq hx h0
  rw [neg_div, Real.rpow_neg (abs_nonneg _), div_eq_inv_mul, Real.rpow_mul (abs_nonneg _),
    Real.rpow_two] at h
  rw [rootDiscr_def, div_eq_mul_inv]
  simpa using h

theorem finrank_mul_discr_rpow_le_sum_sq_of_mem_traceDual {x : K}
    (hx : x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 K) K)) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) * |(discr K : ℝ)| ^ (-2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  refine finrank_mul_discr_rpow_le_sum_sq ?_ h0
  rw [← dual_one_eq_inv_differentIdeal, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_dual_one]
  exact hx

end General

section TotallyReal

variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]


omit [NumberField F] in
variable (F) in
theorem bijective_ofRealHom_comp :
    Function.Bijective (fun σ : F →+* ℝ => Complex.ofRealHom.comp σ) := by
  refine ⟨fun σ τ h => RingHom.ext fun x => ?_, fun φ => ?_⟩
  · simpa using RingHom.congr_fun h x
  · exact ⟨(IsTotallyReal.complexEmbedding_isReal φ).embedding, RingHom.ext fun x => by simp⟩


variable (F) in
theorem card_realEmbeddings : Fintype.card (F →+* ℝ) = finrank ℚ F := by
  rw [← Embeddings.card F ℂ]
  exact Fintype.card_of_bijective (bijective_ofRealHom_comp F)

theorem trace_eq_sum_realEmbeddings (x : F) :
    ((Algebra.trace ℚ F x : ℚ) : ℝ) = ∑ σ : F →+* ℝ, σ x := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_ratCast, trace_eq_sum_complexEmbeddings, Complex.ofReal_sum]
  exact ((bijective_ofRealHom_comp F).sum_comp (fun φ => φ x)).symm

end TotallyReal

end GlobalTheory
end

section

open NumberField Module MeasureTheory Metric Set
open scoped Real ENNReal

namespace GlobalTheory

section Lattice

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

variable [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]


set_option backward.isDefEq.respectTransparency.types false in
theorem covolume_eq_relIndex_mul_of_haar (L' L : Submodule ℤ V) [DiscreteTopology L']
    [IsZLattice ℝ L'] [DiscreteTopology L] [IsZLattice ℝ L] (h : L' ≤ L) :
    ZLattice.covolume L' μ =
      (L'.toAddSubgroup.relIndex L.toAddSubgroup : ℝ) * ZLattice.covolume L μ := by
  classical
  let b : Basis (Fin (finrank ℝ V)) ℤ L := finBasisOfFinrankEq ℤ L (ZLattice.rank ℝ L)
  let b' : Basis (Fin (finrank ℝ V)) ℤ L' := finBasisOfFinrankEq ℤ L' (ZLattice.rank ℝ L')
  rw [AddSubgroup.relIndex_eq_natAbs_det L'.toAddSubgroup L.toAddSubgroup h b' b,
    Nat.cast_natAbs, Int.cast_abs,
    ZLattice.covolume_eq_det_mul_measureReal L' μ b' (b.ofZLatticeBasis ℝ),
    ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain b μ)]
  congr 2
  rw [Basis.det_apply, Basis.det_apply, Int.cast_det]
  congr; ext i j
  rw [Matrix.map_apply, Basis.toMatrix_apply, Basis.toMatrix_apply]
  exact (b.ofZLatticeBasis_repr_apply ℝ L ⟨b' j, h (SetLike.coe_mem _)⟩ i)

end Lattice

section Strip

end Strip

section TotallyComplex

open InfinitePlace

end TotallyComplex

section CM

open InfinitePlace IsCMField
open scoped nonZeroDivisors

variable {E : Type*} [Field E] [NumberField E] [IsCMField E]

end CM

section Constant

end Constant

section Balls

variable {ι : Type*} [Fintype ι] {W : ι → Type*} [∀ i, NormedAddCommGroup (W i)]
  [∀ i, InnerProductSpace ℝ (W i)] [∀ i, FiniteDimensional ℝ (W i)]
  [∀ i, MeasurableSpace (W i)] [∀ i, BorelSpace (W i)]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

end Balls

end GlobalTheory
end

section

open scoped ComplexOrder InnerProductSpace MatrixOrder
open Module Submodule MeasureTheory Matrix

namespace GlobalTheory

section Gram

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_gram_eq_normSq_det {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    (b : OrthonormalBasis ι 𝕜 V) (v : ι → V) :
    (gram 𝕜 v).det = ((‖b.toBasis.det v‖ ^ 2 : ℝ) : 𝕜) := by
  have h : b.toBasis.det v = (Matrix.of fun i j ↦ b.repr (v j) i).det := by
    rw [Basis.det_apply]; congr 1
  rw [gram_eq_conjTranspose_mul b v, det_mul, det_conjTranspose, h, RCLike.star_def,
    RCLike.conj_mul]
  push_cast; rfl

theorem det_gram_le_of_finrank_eq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
    [FiniteDimensional 𝕜 V] (h : finrank 𝕜 V = Fintype.card ι) (v : ι → V) :
    (gram 𝕜 v).det ≤ ((∏ i, ‖v i‖ ^ 2 : ℝ) : 𝕜) := by
  let e := (Fintype.equivFin ι).symm
  have h' : finrank 𝕜 V = Fintype.card (Fin (Fintype.card ι)) := by simpa using h
  have h1 : (gram 𝕜 v).det = (gram 𝕜 (v ∘ e)).det := by
    rw [← det_submatrix_equiv_self e]; rfl
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis h' (v ∘ e)
  have hb : b.toBasis.det (v ∘ e) = ∏ i, ⟪b i, (v ∘ e) i⟫_𝕜 :=
    InnerProductSpace.gramSchmidtOrthonormalBasis_det h' _
  rw [h1, det_gram_eq_normSq_det b, hb, RCLike.ofReal_le_ofReal, norm_prod, ← Finset.prod_pow,
    ← e.prod_comp (fun i ↦ ‖v i‖ ^ 2)]
  refine Finset.prod_le_prod₀ (fun i _ ↦ by positivity) fun i _ ↦ ?_
  gcongr
  simpa using norm_inner_le_norm (𝕜 := 𝕜) (b i) (v (e i))

theorem norm_det_sq_le_prod_col (A : Matrix ι ι 𝕜) :
    ‖A.det‖ ^ 2 ≤ ∏ j, ∑ i, ‖A i j‖ ^ 2 := by
  let v : ι → EuclideanSpace 𝕜 ι := fun j ↦ WithLp.toLp 2 fun i ↦ A i j
  have h := det_gram_le_of_finrank_eq (𝕜 := 𝕜) (by simp) v
  rw [det_gram_eq_normSq_det (EuclideanSpace.basisFun ι 𝕜), RCLike.ofReal_le_ofReal] at h
  have h2 : (EuclideanSpace.basisFun ι 𝕜).toBasis.det v = A.det := by
    rw [Basis.det_apply]; congr 1
  rw [h2] at h
  refine h.trans_eq (Finset.prod_congr rfl fun j _ ↦ ?_)
  rw [EuclideanSpace.norm_sq_eq]

theorem posSemidef_det_le_prod_diag {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    A.det ≤ ∏ i, A i i := by
  obtain ⟨B, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hA.nonneg
  have h := norm_det_sq_le_prod_col B
  rw [← RCLike.ofReal_le_ofReal (K := 𝕜)] at h
  convert h using 1
  · rw [det_mul, star_eq_conjTranspose, det_conjTranspose, RCLike.star_def, RCLike.conj_mul]
    push_cast; rfl
  · push_cast
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    simp [Matrix.mul_apply, RCLike.conj_mul]

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace 𝕜 V]

end Gram

section Covolume

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} [Fintype ι]

theorem linearIndependent_real_of_int_of_discrete {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] (L : Submodule ℤ F) [DiscreteTopology L]
    {v : ι → F} (hv : ∀ i, v i ∈ L) (hli : LinearIndependent ℤ v) : LinearIndependent ℝ v := by
  have hle : span ℤ (Set.range v) ≤ L := span_le.2 (Set.range_subset_iff.2 hv)
  have hd : DiscreteTopology (span ℤ (Set.range v)) :=
    DiscreteTopology.of_continuous_injective (β := L) (f := Set.inclusion hle)
      (continuous_inclusion hle) (Set.inclusion_injective hle)
  rw [linearIndependent_iff_card_eq_finrank_span] at hli ⊢
  rw [Real.finrank_eq_int_finrank_of_discrete hd, hli]

variable [MeasurableSpace E] [BorelSpace E]

theorem covolume_span_basis_eq_sqrt_det_gram [DecidableEq ι] (b : Basis ι ℝ E) :
    ZLattice.covolume (span ℤ (Set.range b)) = √(gram ℝ b).det := by
  let o : OrthonormalBasis ι ℝ E := (stdOrthonormalBasis ℝ E).reindex
    (Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm).symm
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
      (ZSpan.isAddFundamentalDomain b volume),
    ZSpan.measureReal_fundamentalDomain b volume o.toBasis,
    measureReal_congr (ZSpan.fundamentalDomain_ae_parallelepiped o.toBasis volume),
    det_gram_eq_normSq_det o, measureReal_def, o.coe_toBasis, o.volume_parallelepiped]
  simp [Real.sqrt_sq_eq_abs]

theorem covolume_eq_sqrt_det_gram [DecidableEq ι] (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (b : Basis ι ℤ L) :
    ZLattice.covolume L = √(gram ℝ fun i ↦ (b i : E)).det := by
  have h := covolume_span_basis_eq_sqrt_det_gram (b.ofZLatticeBasis ℝ L)
  rw [b.ofZLatticeBasis_span ℝ] at h
  rw [h]
  congr 3
  ext i
  simp

end Covolume

end GlobalTheory
end

section

open Metric MeasureTheory Module Set Real

namespace GlobalTheory

theorem finset_sum_exp_neg_le_of_card_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) {t C : ℝ}
    (hf : ∀ i ∈ s, t ≤ f i)
    (hc : ∀ u, t ≤ u → ((s.filter fun i => f i ≤ u).card : ℝ) ≤ C * exp ((u - t) / 2)) :
    ∑ i ∈ s, exp (-f i) ≤ 2 * C * exp (-t) := by
  have hint : IntegrableOn (fun u : ℝ => exp (-u)) (Ici t) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 (integrableOn_exp_neg_Ioi t)
  have h1 : ∀ i ∈ s, exp (-f i) =
      ∫ u in Ici t, (Ici (f i)).indicator (fun u : ℝ => exp (-u)) u := by
    intro i hi
    rw [setIntegral_indicator measurableSet_Ici, Ici_inter_Ici, sup_eq_right.2 (hf i hi),
      integral_Ici_eq_integral_Ioi, integral_exp_neg_Ioi]
  have hint2 : IntegrableOn (fun u : ℝ => exp (-(1 / 2) * u)) (Ici t) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).2 (exp_neg_integrableOn_Ioi t (by norm_num))
  rw [Finset.sum_congr rfl h1, ← MeasureTheory.integral_finsetSum _
    (fun i _ => hint.indicator measurableSet_Ici)]
  calc ∫ u in Ici t, ∑ i ∈ s, (Ici (f i)).indicator (fun u : ℝ => exp (-u)) u
      ≤ ∫ u in Ici t, (C * exp (-t / 2)) * exp (-(1 / 2) * u) := by
        refine setIntegral_mono_on
          (MeasureTheory.integrable_finsetSum _ fun i _ => hint.indicator measurableSet_Ici)
          (hint2.const_mul _) measurableSet_Ici fun u hu => ?_
        have e : ∑ i ∈ s, (Ici (f i)).indicator (fun u : ℝ => exp (-u)) u =
            ((s.filter fun i => f i ≤ u).card : ℝ) * exp (-u) := by
          simp only [indicator, mem_Ici]
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        rw [e]
        calc _ ≤ C * exp ((u - t) / 2) * exp (-u) :=
              mul_le_mul_of_nonneg_right (hc u hu) (exp_pos _).le
          _ = _ := by
              rw [mul_assoc, mul_assoc, ← exp_add, ← exp_add]; congr 2; ring
    _ = 2 * C * exp (-t) := by
        rw [integral_const_mul, integral_Ici_eq_integral_Ioi,
          integral_exp_mul_Ioi (by norm_num)]
        have : exp (-t) = exp (-t / 2) * exp (-(1 / 2) * t) := by
          rw [← exp_add]; congr 1; ring
        rw [this]; ring

theorem summable_exp_neg_of_card_le {ι : Type*} (f : ι → ℝ) {t C : ℝ} (hf : ∀ i, t ≤ f i)
    (hc : ∀ (s : Finset ι) u, t ≤ u → (∀ i ∈ s, f i ≤ u) → (s.card : ℝ) ≤ C * exp ((u - t) / 2)) :
    Summable (fun i => exp (-f i)) ∧ ∑' i, exp (-f i) ≤ 2 * C * exp (-t) := by
  have key : ∀ s : Finset ι, ∑ i ∈ s, exp (-f i) ≤ 2 * C * exp (-t) := fun s =>
    finset_sum_exp_neg_le_of_card_le s f (fun i _ => hf i) fun u hu =>
      hc _ u hu fun i hi => (Finset.mem_filter.1 hi).2
  have hs := summable_of_sum_le (fun i => (exp_pos (-f i)).le) key
  exact ⟨hs, hs.tsum_le_of_sum_le key⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

end GlobalTheory
end
