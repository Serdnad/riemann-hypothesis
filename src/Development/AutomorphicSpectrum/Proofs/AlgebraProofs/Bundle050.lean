module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle009
public import Mathlib.Algebra.AffineMonoid.Basic
public import Development.WeilBound.CoreStatements.SesquilinearFractions.TraceIntegralOfCodifferent
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle011
public import GroundTheory.GlobalFields.TateThesis.Bundle003
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle001
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle038
public import GroundTheory.GlobalFields.TateThesis.Bundle005
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle031
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle015
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle046
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle040
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle047
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedAFStatement
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle044
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle029
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle032
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle013
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlgebraActionBundleFiltrationStep
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle045
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis
import GroundTheory.GlobalFields.HerbrandQuotients.RationalForm
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnipotentModulusMatrix
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle004
public import ReciprocityTheory.DualLattices.Bundle022
public import ReciprocityTheory.DualLattices.Bundle014
public import ReciprocityTheory.DualLattices.PowMemCarrier
import ReciprocityTheory.DualLattices.ProdDvdOfIso

@[expose] public section

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

theorem _root_.GlobalTheory.T.sesq_sesquilinear_skew_hermitian : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∀ (a : 𝓞 E) x y, Algebra.trace ℚ E ((a : E) * sesq D x y) = (D.EF (a • x) y : ℚ)) ∧ (∀ x x' y, sesq D (x + x') y = sesq D x y + sesq D x' y) ∧ (∀ x y y', sesq D x (y + y') = sesq D x y + sesq D x y') ∧ (∀ (a : 𝓞 E) x y, sesq D (a • x) y = a * sesq D x y) ∧ (∀ (a : 𝓞 E) x y, sesq D x (a • y) = IsCMField.complexConj E (a : E) * sesq D x y) ∧ (∀ x y, sesq D y x = -IsCMField.complexConj E (sesq D x y)) ∧ ∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ x y, ∃ b : 𝓞 E, (δ : E) * sesq D x y = b := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.Sesq.form_of_datum | exact GlobalTheory.CompanionTheory.Ar.Fl.Sesq.form_of_datum | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.Sesq.form_of_datum <;> assumption)
end

section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem unimodularity_sesq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), (∀ y, (∀ x, sesq D x y = 0) → y = 0) ∧ ∀ f : D.La →ₗ[𝓞 E] E, (∀ δ ∈ differentIdeal ℤ (𝓞 E), ∀ x, ∃ b : 𝓞 E, (δ : E) * f x = b) → ∃ y, ∀ x, f x = sesq D x y :=
  PositivityTheory.Xgf.sesq_unimodular_dual

end GlobalTheory.CompanionTheory.Ar.Fl
end

section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.Ar.Cusp

section ShortIntegers

open NumberField.InfinitePlace NumberField.mixedEmbedding Module GroundTheory.Global
open scoped ComplexConjugate nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K]

theorem sum_norm_sq_embeddings (x : K) :
    ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 = ∑ w, (mixedEmbedding K x).1 w ^ 2 +
      ∑ w, 2 * ‖(mixedEmbedding K x).2 w‖ ^ 2 := by
  have h3 : ∀ w : InfinitePlace K,
      ∑ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w), ‖φ x‖ ^ 2 =
        mult w * (w x) ^ 2 := by
    intro w
    have h : ∀ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w),
        ‖φ x‖ ^ 2 = (w x) ^ 2 := by
      intro φ hφ
      rw [← (Finset.mem_filter.mp hφ).2, InfinitePlace.apply]
    rw [Finset.sum_congr rfl h, Finset.sum_const, card_filter_mk_eq, nsmul_eq_mul]
  rw [← Finset.sum_fiberwise Finset.univ (fun φ : K →+* ℂ => InfinitePlace.mk φ)
    (fun φ => ‖φ x‖ ^ 2)]
  simp_rw [h3]
  rw [sum_eq_sum_add_sum]
  congr 1
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isReal, Nat.cast_one, one_mul, mixedEmbedding_apply_isReal,
      ← InfinitePlace.norm_embedding_of_isReal w.2 x, Real.norm_eq_abs, sq_abs]
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [mult_isComplex, mixedEmbedding_apply_isComplex, InfinitePlace.norm_embedding_eq]
    norm_num

omit [Field K] [NumberField K] in
theorem re_conj_sqrtTwo_smul_mul (z : ℂ) :
    (conj ((√2 : ℝ) • z) * ((√2 : ℝ) • z)).re = 2 * ‖z‖ ^ 2 := by
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re, _root_.norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]

theorem norm_sq_mixedToEuclidean (x : mixedSpace K) :
    ‖mixedToEuclidean K x‖ ^ 2 = ∑ w, x.1 w ^ 2 + ∑ w, 2 * ‖x.2 w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, mixedToEuclidean, ContinuousLinearEquiv.trans_apply,
    inner_toMixed_symm]
  simp only [mapComplexCoord_apply, sqrtTwoSMulComplex_apply]
  congr 1
  · exact Finset.sum_congr rfl fun w _ => by ring
  · exact Finset.sum_congr rfl fun w _ => re_conj_sqrtTwo_smul_mul _

theorem norm_sq_mixedToEuclideanConj (x : mixedSpace K) :
    ‖mixedToEuclideanConj K x‖ ^ 2 = ∑ w, x.1 w ^ 2 + ∑ w, 2 * ‖x.2 w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, mixedToEuclideanConj, ContinuousLinearEquiv.trans_apply,
    inner_toMixed_symm]
  simp only [mapComplexCoord_apply, sqrtTwoSMulConj_apply]
  congr 1
  · exact Finset.sum_congr rfl fun w _ => by ring
  · refine Finset.sum_congr rfl fun w _ => ?_
    rw [re_conj_sqrtTwo_smul_mul, Complex.norm_conj]

noncomputable def integersEuclid : Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (idealLattice K 1) (mixedToEuclidean K).symm.toLinearMap

instance : DiscreteTopology (integersEuclid K) := by
  rw [integersEuclid]
  infer_instance

instance : IsZLattice ℝ (integersEuclid K) := by
  simp_rw [integersEuclid]
  infer_instance

theorem mem_integersEuclid {z : euclidean.mixedSpace K} :
    z ∈ integersEuclid K ↔ ∃ a : 𝓞 K, mixedToEuclidean K (mixedEmbedding K (a : K)) = z := by
  change (mixedToEuclidean K).symm z ∈ idealLattice K 1 ↔ _
  rw [mem_idealLattice]
  constructor
  · rintro ⟨y, hy, h⟩
    have hy1 : y ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by simpa using hy
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy1
    refine ⟨a, ?_⟩
    change mixedToEuclidean K (mixedEmbedding K (algebraMap (𝓞 K) K a)) = z
    rw [h, ContinuousLinearEquiv.apply_symm_apply]
  · rintro ⟨a, rfl⟩
    refine ⟨(a : K), ?_, by simp⟩
    have : (a : K) ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) :=
      (FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩
    simpa using this

theorem norm_sq_mixedToEuclidean_embedding (x : K) :
    ‖mixedToEuclidean K (mixedEmbedding K x)‖ ^ 2 = ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  rw [norm_sq_mixedToEuclidean, sum_norm_sq_embeddings]

theorem finrank_div_rootDiscr_sq_le_norm_sq {y : euclidean.mixedSpace K} (hy : y ≠ 0)
    (h : ∀ x ∈ integersEuclid K, ∃ m : ℤ, ⟪x, y⟫_ℝ = m) :
    (finrank ℚ K : ℝ) / rootDiscr K ^ 2 ≤ ‖y‖ ^ 2 := by
  set y0 := (mixedToEuclideanConj K).symm y with hy0
  have hmem : y0 ∈ idealLattice K (traceDualIdeal K 1) := by
    rw [mem_idealLattice_traceDualIdeal_iff]
    intro x hx
    obtain ⟨m, hm⟩ := h (mixedToEuclidean K x) (by
      change (mixedToEuclidean K).symm (mixedToEuclidean K x) ∈ idealLattice K 1
      simpa using hx)
    refine ⟨m, ?_⟩
    rw [mixedTraceForm_comm, mixedTraceForm_eq_inner, hy0,
      ContinuousLinearEquiv.apply_symm_apply, hm]
  obtain ⟨t, ht, hty⟩ := (mem_idealLattice K _).1 hmem
  have hyy : y = mixedToEuclideanConj K (mixedEmbedding K t) := by
    rw [hty, hy0, ContinuousLinearEquiv.apply_symm_apply]
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hy (by simpa using hyy)
  have ht' : t ∈ (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K)⁻¹ := by
    rw [← GlobalTheory.dual_one_eq_inv_differentIdeal]
    simpa [coe_traceDualIdeal] using ht
  have hb := GlobalTheory.finrank_div_rootDiscr_sq_le_sum_sq ht' ht0
  rw [hyy, norm_sq_mixedToEuclideanConj, ← sum_norm_sq_embeddings]
  exact hb

theorem exists_short_integers :
    ∃ a : Fin (finrank ℚ K) → 𝓞 K, LinearIndependent ℚ (fun i => (a i : K)) ∧
      ∀ i (σ : K →+* ℂ), ‖σ (a i)‖ ≤ finrank ℚ K * rootDiscr K := by
  have hfr : finrank ℝ (euclidean.mixedSpace K) = finrank ℚ K := euclidean.finrank K
  have hn : (0 : ℝ) < finrank ℚ K := by exact_mod_cast finrank_pos
  have hrd : 0 < rootDiscr K := by
    rw [rootDiscr_def]
    exact Real.rpow_pos_of_pos (by exact_mod_cast abs_pos.2 (discr_ne_zero K)) _
  have hμ : 0 < √(finrank ℚ K : ℝ) / rootDiscr K := by positivity
  have hdual : ∀ y : euclidean.mixedSpace K, y ≠ 0 →
      (∀ x ∈ integersEuclid K, ∃ m : ℤ, ⟪x, y⟫_ℝ = m) →
      √(finrank ℚ K : ℝ) / rootDiscr K ≤ ‖y‖ := by
    intro y hy h
    refine (sq_le_sq₀ hμ.le (norm_nonneg y)).1 ?_
    rw [div_pow, Real.sq_sqrt hn.le]
    exact finrank_div_rootDiscr_sq_le_norm_sq K hy h
  obtain ⟨b, hbL, hbi, hbn⟩ := exists_independent_le_of_dual_min (euclidean.mixedSpace K) (integersEuclid K) _ hμ hdual
  have hbound : (finrank ℚ K : ℝ) ^ (3 / 2 : ℝ) / (√(finrank ℚ K : ℝ) / rootDiscr K) =
      finrank ℚ K * rootDiscr K := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hn, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
    have : √(finrank ℚ K : ℝ) ≠ 0 := (Real.sqrt_pos.2 hn).ne'
    field_simp
  have hb' : ∀ i : Fin (finrank ℚ K), ∃ a : 𝓞 K,
      mixedToEuclidean K (mixedEmbedding K (a : K)) = b (Fin.cast hfr.symm i) :=
    fun i => (mem_integersEuclid K).1 (hbL _)
  choose a ha using hb'
  refine ⟨a, ?_, fun i σ => ?_⟩
  · have h1 : LinearIndependent ℤ (fun i : Fin (finrank ℚ K) => b (Fin.cast hfr.symm i)) :=
      (hbi.comp _ (Fin.cast_injective _)).restrict_scalars (R := ℤ)
        (fun x y h => by simpa using h)
    rw [← LinearIndependent.iff_fractionRing (R := ℤ) (K := ℚ)]
    let g : K →ₗ[ℤ] euclidean.mixedSpace K := AddMonoidHom.toIntLinearMap
      { toFun := fun x => mixedToEuclidean K (mixedEmbedding K x)
        map_zero' := by simp
        map_add' := fun x y => by simp }
    have hg : (⇑g ∘ fun i => ((a i : 𝓞 K) : K)) = fun i => b (Fin.cast hfr.symm i) := funext ha
    refine LinearIndependent.of_comp g ?_
    rw [hg]
    exact h1
  · have h2 : ‖σ (a i)‖ ^ 2 ≤ ∑ τ : K →+* ℂ, ‖τ (a i)‖ ^ 2 :=
      Finset.single_le_sum (f := fun τ : K →+* ℂ => ‖τ (a i)‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ σ)
    rw [← norm_sq_mixedToEuclidean_embedding, ha i] at h2
    have h3 := hbn (Fin.cast hfr.symm i)
    rw [show ((finrank ℝ (euclidean.mixedSpace K) : ℕ) : ℝ) = finrank ℚ K by rw [hfr], hbound] at h3
    exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
      (h2.trans (pow_le_pow_left₀ (norm_nonneg _) h3 2))

end ShortIntegers

theorem exists_full_family_conjugates_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    ∃ a : Fin (Module.finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (a i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (a i)‖ ≤ Module.finrank ℚ E * hostRd E := by
  intro E _ _ _
  have h : hostRd E = rootDiscr E := by simp [hostRd, rootDiscr_def]
  rw [h]
  exact exists_short_integers E

end GlobalTheory.CompanionTheory.Ar.Cusp
end

section

open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve

theorem _root_.GlobalTheory.T.algebra_action_bundle_filtration_step : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (k A : Type) [Field k] [Algebra k K] [CommRing A] [Algebra k A] (τ : A →+* Module.End K V) (r : ℕ) (χ : A →ₐ[k] k) (J₁ J : Ideal A) (t : A) (l : A →ₗ[k] k), IsBun C L → (∀ a, IsHom C L L (τ a)) → (∀ (c : k) (x : V), τ (algebraMap k A c) x = algebraMap k K c • x) → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → (∀ i, FreeAt C k τ L r i) → J₁ ≤ J → t ∈ J → (∀ a ∈ J, ∃ c : k, a - algebraMap k A c * t ∈ J₁) → (∀ a ∈ RingHom.ker χ, a * t ∈ J₁) → (∀ a ∈ J₁, l a = 0) → l t = 1 → subDeg C L (idealV τ J) = subDeg C L (idealV τ J₁) + deg C (quot C L (idealV τ (RingHom.ker χ))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.FiltStep.subDeg_step | exact GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.FiltStep.subDeg_step | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.FiltStep.subDeg_step <;> assumption)
end

section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.sphere_mean_normalized_groups : ∀ (n e : ℕ) (h : HermNorm n) (G : (Fin e × Fin n → ℂ) → ℝ),
  IntegrableOn (fun u => G (nrmGroups h e u)) (ballProd h e) →
    Integrable (fun π : Fin (e + 1) → Fin n → ℂ => G (nrmGroups h e (coefRows h π))) (gaussM (e + 1) n) ∧
      ∫ π, G (nrmGroups h e (coefRows h π)) ∂(gaussM (e + 1) n) =
        (gaussM (e + 1) n Set.univ).toReal * sphereMean h e G := by
  first | exact @GlobalTheory.CompanionTheory.Relay.sphere_mean_normalized_groups | exact GlobalTheory.CompanionTheory.Relay.sphere_mean_normalized_groups | (intros; apply GlobalTheory.CompanionTheory.Relay.sphere_mean_normalized_groups <;> assumption)
end

section

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

theorem _root_.GlobalTheory.T.cm_type_polynomial_vanishing_criterion : ∀ (E : Type) [Field E] [NumberField E] (C : Type) [Field C] [CharZero C] (w : Valuation C ℝ≥0) [Fintype (E →+* C)] (emb : (E →+* C) → (𝓞 E →+* w.valuationSubring)), (∀ s (a : 𝓞 E), ((emb s a : w.valuationSubring) : C) = s (a : E)) → Fintype.card (E →+* C) = Module.finrank ℚ E → ∀ (D : (E →+* C) → Prop) (π : 𝓞 E), (∀ f : (E →+* C) → w.valuationSubring, (∀ s, ¬ D s → f s = 0) → ((∃ g : Polynomial w.valuationSubring, ∀ s, D s → f s = g.eval (emb s π)) ↔ f ∈ Submodule.span w.valuationSubring (Set.range fun a : 𝓞 E => fun s => emb s a))) → ∀ (M : Type) [AddCommGroup M] [Module C M] [Module w.valuationSubring M] [IsScalarTower w.valuationSubring C M] (ρ : 𝓞 E →+* Module.End C M) (X : Submodule w.valuationSubring M) (N : ℕ) (t : Fin N → M), HT.IsFreeOn ρ X t → ∀ [Fintype {s // D s}], (∀ f : {s // D s} → Fin N → C, (∑ s, eigCoord ρ t s.1 (f s)) ∈ X ↔ f ∈ freeLattice (fun s : {s // D s} => emb s.1 π) N) ∧ (∀ y ∈ X, ∃ f ∈ freeLattice (fun s : {s // D s} => emb s.1 π) N, ∀ s, HT.eigProj ρ s.1 y = eigCoord ρ t s.1 (f s)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExG.Block.block_freeLattice | exact GlobalTheory.CompanionTheory.Ar.Flat.ExG.Block.block_freeLattice | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExG.Block.block_freeLattice <;> assumption)
end

section

open scoped NNReal
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Flat.ExG

theorem _root_.GlobalTheory.T.conjugate_embeddings_valuation_rank_bound : TargetO → ∀ (E : Type) [Field E] [NumberField E] (V C : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field C] [CharZero C] [Algebra V C] [IsFractionRing V C] (bar : 𝓞 E ≃+* 𝓞 E) (σ σ' : E →+* C) (rk : (E →+* C) → ℕ) (p q : ℕ) (ν : Valuation C NNReal), ν.Integers V → (∃ ℓ : C, 0 < ν ℓ ∧ ν ℓ < 1) → (∀ (s : E →+* C) (a : 𝓞 E), s (a : E) ∈ (algebraMap V C).range) → Nat.card (E →+* C) = Module.finrank ℚ E → (∀ a : 𝓞 E, σ' (a : E) = σ (bar a : 𝓞 E)) → (∀ a, bar (bar a) = a) → ∃ γ : C, γ ≠ 0 ∧ ∀ (W : Type) [AddCommGroup W] [Module C W] [Module V W] [IsScalarTower V C W] [FiniteDimensional C W] (ρ : 𝓞 E →+* Module.End C W) (ρH : 𝓞 E →+* Module.End C (W × Module.Dual C W)) (HV : Submodule V (W × Module.Dual C W)) (Lie : Submodule V W) (x : Fin (p + q) → W × Module.Dual C W) (v : Fin p → W) (w : Fin q → W) (u : Fin (p + q) → W × Module.Dual C W) (A : Matrix (Fin (p + q)) (Fin (p + q)) C), (∀ a y, (ρH a y).1 = ρ a y.1) → (∀ a φ, ρH a (0, φ) = (0, φ ∘ₗ ρ (bar a))) → HV.map ((LinearMap.fst C W (Module.Dual C W)).restrictScalars V) = Lie → (∀ φ : Module.Dual C W, (0, φ) ∈ HV ↔ ∀ e ∈ Lie, φ e ∈ (algebraMap V C).range) → HT.IsFreeOn ρH HV x → (∀ s, Module.finrank C (HT.eigSp ρ s) = rk s) → LinearIndependent C v → Submodule.span V (Set.range v) = HT.eigSub ρ σ Lie → LinearIndependent C w → Submodule.span V (Set.range w) = HT.eigSub ρ σ' Lie → IsAdapted ρH σ v w u → LinearIndependent C (fun i => ∑ j, A i j • u j) → Submodule.span V (Set.range fun i => ∑ j, A i j • u j) = HT.eigQuot ρH σ HV → ∃ ε : Vˣ, A.det = algebraMap V C ε * γ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ExG.Red.targetV | exact GlobalTheory.CompanionTheory.Ar.Flat.ExG.Red.targetV | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ExG.Red.targetV <;> assumption)
end

section

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR.PolAF

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

theorem hasLen_omAA_htd {p : ℕ} [Fact p.Prime] {g : ℕ} {v : Valuation C NNReal} [Algebra ℤ_[p] R]
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
    (H : HodgeTateDatum p g v R O σ cp) :
    HasLen v R (OmAA H.AA.carrier) (v (algebraMap R C (p : R)) ^ g) := by
  refine ⟨g, fun _ => (p : R), ⟨?_⟩, by simp⟩
  exact (Submodule.quotEquivOfEq _ _ H.cotangent_ker_eq.symm).trans
    ((LinearMap.quotKerEquivOfSurjective H.φ H.cotangent_surjective).trans (PullbackHopfOrder.qPi p g))

theorem mem_afLat_of_cong {p : ℕ} [Fact p.Prime] {g : ℕ} [Algebra ℤ_[p] R]
    (M : Submodule R (Nb p g → C)) (l : Ix g → R) (f : Nb p g → C) (hf : f ∈ M)
    (h : ∀ t : TT p g, ∃ r : R, algebraMap R C (∑ i, l i * algebraMap ℤ_[p] R (t i)) -
      f (red p g t) = algebraMap R C (p * r)) : l ∈ afLat p M := by
  refine ⟨f, hf, fun x => ?_⟩
  obtain ⟨r, hr⟩ := h (fun i => ((x i).val : ℤ_[p]))
  have hred : red p g (fun i => ((x i).val : ℤ_[p])) = x := by
    funext i; simp [red]
  have hsum : (∑ i, l i * algebraMap ℤ_[p] R (((x i).val : ℕ) : ℤ_[p])) =
      ∑ i, l i * ((x i).val : R) := by
    exact Finset.sum_congr rfl fun i _ => by rw [map_natCast]
  rw [hred, hsum] at hr
  have hx : f x - algebraMap R C (∑ i, l i * ((x i).val : R)) = -(algebraMap R C (p * r)) := by
    rw [← hr]; ring
  show _ ∈ Submodule.span R {(p : C)}
  rw [hx, Submodule.mem_span_singleton]
  refine ⟨-r, ?_⟩
  rw [Algebra.smul_def, map_mul, map_neg, map_natCast]
  ring

theorem rows_mem_afLat {p : ℕ} [Fact p.Prime] {g : ℕ} {v : Valuation C NNReal} [Algebra ℤ_[p] R]
    {O : Type} [CommRing O] [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}
    (H : HodgeTateDatum p g v R O σ cp) (k : Ix g) :
    Matrix.fromRows H.Ht H.Bt k ∈ afLat p H.AA.carrier := by
  rcases k with k | k
  · obtain ⟨f, hf, h⟩ := (H.h4 k).1
    exact mem_afLat_of_cong H.AA.carrier (H.Ht k) f hf h
  · obtain ⟨f, hf, h⟩ := (H.h4 k).2
    exact mem_afLat_of_cong H.AA.carrier (H.Bt k) f hf h

theorem span_rows_integral {g : ℕ} (v : Valuation C NNReal) (hv : v.Integers R)
    (Ht Bt : Matrix (Fin g) (Ix g) R) (x : Ix g → C) :
    (∀ l ∈ Submodule.span R (Set.range fun k => Matrix.fromRows Ht Bt k),
      v (∑ i, algebraMap R C (l i) * x i) ≤ 1) ↔
    (∀ k, v ((Ht.map (algebraMap R C) *ᵥ x) k) ≤ 1) ∧
      ∀ k, v ((Bt.map (algebraMap R C) *ᵥ x) k) ≤ 1 := by
  constructor
  · intro h
    refine ⟨fun k => ?_, fun k => ?_⟩
    · simpa [Matrix.mulVec, dotProduct] using h _ (Submodule.subset_span ⟨Sum.inl k, rfl⟩)
    · simpa [Matrix.mulVec, dotProduct] using h _ (Submodule.subset_span ⟨Sum.inr k, rfl⟩)
  · rintro ⟨h1, h2⟩ l hl
    induction hl using Submodule.span_induction with
    | mem l hl =>
      obtain ⟨k, rfl⟩ := hl
      rcases k with k | k
      · simpa [Matrix.mulVec, dotProduct] using h1 k
      · simpa [Matrix.mulVec, dotProduct] using h2 k
    | zero => simp
    | add a b _ _ ha hb =>
      simp only [Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
      exact (v.map_add _ _).trans (max_le ha hb)
    | smul r a _ ha =>
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc, ← Finset.mul_sum]
      exact mul_le_one' (hv.map_le_one r) ha

end GlobalTheory.CompanionTheory.Ar.GR.PolAF

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem polarisedAF : PolarisedAFStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H
  intro φ AF H' hb
  classical
  have hv : v.Integers R := hS.integers
  have hp1 : v (p : C) < 1 := by simpa [map_natCast] using hS.p_lt
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hvcp : v (algebraMap R C cp) ≠ 0 := by
    intro h0
    have h := hS.cp_val
    rw [h0, zero_pow (by omega)] at h
    exact hS.p_ne h.symm
  have hcp : cp ≠ 0 := by rintro rfl; exact hvcp (by simp)
  have hEalt : (H.E.map (algebraMap ℤ_[p] R))ᵀ = -(H.E.map (algebraMap ℤ_[p] R)) := by
    ext i j
    have h := congrFun (congrFun H.E_alternating.1 j) i
    simp only [Matrix.transpose_apply, Matrix.neg_apply] at h
    simp [Matrix.transpose_apply, Matrix.map_apply, h]
  have hEu : IsUnit (H.E.map (algebraMap ℤ_[p] R)).det := by
    have : (H.E.map (algebraMap ℤ_[p] R)).det = algebraMap ℤ_[p] R H.E.det :=
      (RingHom.map_det _ _).symm
    rw [this]; exact H.isUnit_det_E.map _
  obtain ⟨hdet, hker, himg, hcpmem⟩ :=
    GlobalTheory.T.symplectic_period_matrix_integrality C v R hv g H.Ht H.Bt _ cp hcp hEalt hEu H.form_eq_alt

  set L := Submodule.span R (Set.range fun k => Matrix.fromRows H.Ht H.Bt k) with hL
  have hLle : L ≤ AF :=
    Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact PolAF.rows_mem_afLat H k)
  have hLlen : HasLen v R ((Ix g → R) ⧸ L) (v (algebraMap R C cp) ^ g) := by
    have h := hasLen_coker_det' v R hv (Ix g) (Matrix.fromRows H.Ht H.Bt)ᵀ
    rw [Matrix.det_transpose, hdet, Matrix.range_mulVecLin] at h
    exact h

  have hkill : ∀ x : Nb p g, p • x = 0 := by intro x; ext i; simp
  obtain ⟨cA, cN, cO, -, -, -, hA, hN, hO⟩ := GlobalTheory.T.augmentation_lengths_exist p C v R hv hp1 (Nb p g) hkill H.AA
  have hcO : cO = v (algebraMap R C (p : R)) ^ g := hasLen_unique hv hO (PolAF.hasLen_omAA_htd H)
  have hdeg := u4 p C v R hv hp1 (Nb p g) hkill H.AA cN cO hN hO
  obtain ⟨hcnt, hgen⟩ := GlobalTheory.T.augmentation_length_colength_bound p C v R hv hp1 (Nb p g) hkill H.AA cA cN hA hN
  obtain ⟨eq⟩ := GlobalTheory.T.augmentation_quotient_equiv_lattice p C v R hv hp1 (Ix g) H.AA
  have hAF : HasLen v R ((Ix g → R) ⧸ AF) cA := hasLen_of_equiv eq.symm hA
  obtain ⟨hle, hLeq⟩ :=
    GlobalTheory.T.lattice_length_mono_strict C v R hv (Ix g) L AF hLle _ _ (pow_ne_zero _ hvcp) hLlen hAF
  have hn : Fintype.card (Nb p g) * (p - 1) ≠ 0 :=
    Nat.mul_ne_zero Fintype.card_ne_zero (by omega)
  have hOeq : cO ^ Fintype.card (Nb p g) =
      (v (algebraMap R C cp) ^ g) ^ (Fintype.card (Nb p g) * (p - 1)) := by
    rw [hcO, ← hS.cp_val, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1; ring
  have h1 : (v (algebraMap R C cp) ^ g) ^ (Fintype.card (Nb p g) * (p - 1)) ≤
      cA ^ (Fintype.card (Nb p g) * (p - 1)) := pow_le_pow_left₀ zero_le hle _
  have hAn : cA ^ (Fintype.card (Nb p g) * (p - 1)) = cN ^ 2 :=
    le_antisymm hcnt (hdeg.trans (hOeq ▸ h1))
  have hOn : cO ^ Fintype.card (Nb p g) = cN ^ 2 :=
    le_antisymm (hOeq ▸ h1.trans hAn.le) hdeg
  have hcA : cA = v (algebraMap R C cp) ^ g :=
    ((pow_left_inj₀ zero_le zero_le hn).1 (hAn.trans (hOn.symm.trans hOeq)))
  have hLAF : L = AF := hLeq hcA.symm

  have hmem : ∀ x, x ∈ H' ↔ (∀ k, v ((H.Ht.map φ *ᵥ x) k) ≤ 1) ∧
      ∀ k, v ((H.Bt.map φ *ᵥ x) k) ≤ 1 := by
    intro x
    show (∀ l ∈ AF, _) ↔ _
    rw [← hLAF]
    exact PolAF.span_rows_integral v hv H.Ht H.Bt x
  refine ⟨hLAF.symm, fun l => hLAF ▸ hcpmem l, hLAF ▸ hLlen, hcA ▸ hA, hmem, ?_, ?_,
    hgen hAn, ⟨cA, cN, cO, hA, hN, hO, hAn, hOn⟩⟩
  · intro x
    rw [← hker x, hmem]
    constructor
    · rintro ⟨⟨-, h2⟩, h0⟩; exact ⟨h0, h2⟩
    · rintro ⟨h0, h2⟩; exact ⟨⟨fun k => by rw [show H.Ht.map φ *ᵥ x = 0 from h0]; simp, h2⟩, h0⟩
  · intro w hw
    obtain ⟨x, hx1, hx2⟩ := himg w hw
    refine ⟨x, (hmem x).2 ⟨fun k => by rw [hx1]; exact hw k, fun k => by rw [show H.Bt.map φ *ᵥ x = 0 from hx2]; simp⟩, hx1⟩

end GlobalTheory.CompanionTheory.Ar.GR
end
end

section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem _root_.GlobalTheory.T.polarised_lattice_tower_exists : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (N : ℕ) (u : Fin N → La), IsPolLattice c p EF u → ∃ (ρ : 𝓞 E →+* Module.End C (C ⊗[ℤ] La)) (T : Submodule O (C ⊗[ℤ] La)) (e : C ⊗[ℤ] La →ₗ[C] C ⊗[ℤ] La →ₗ[C] C), (∀ (a : 𝓞 E) (x : La), ρ a (1 ⊗ₜ x) = 1 ⊗ₜ (a • x)) ∧ T = Submodule.span O (Set.range fun x : La => (1 : C) ⊗ₜ[ℤ] x) ∧ IsFreeOn ρ T (fun i => 1 ⊗ₜ u i) ∧ (∀ x y : La, e (1 ⊗ₜ x) (1 ⊗ₜ y) = (EF x y : C)) ∧ (∀ x, e x x = 0) ∧ (∀ y, (∀ x, e x y = 0) → y = 0) ∧ dualLat e T = T ∧ ∀ (a : 𝓞 E) x y, e (ρ a x) y = e x (ρ (RingOfIntegers.mapRingEquiv c a) y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.free_on_lift | exact GlobalTheory.CompanionTheory.Ar.HT.free_on_lift | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.free_on_lift <;> assumption)
end
