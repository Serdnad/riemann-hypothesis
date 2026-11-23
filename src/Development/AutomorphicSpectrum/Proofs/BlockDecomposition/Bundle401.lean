module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Mathlib.Algebra.FiniteSupport.Basic
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle132
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import GroundTheory.AutomorphicForms.QuotientMeasure
public import GroundTheory.AutomorphicForms.ReductionMahler
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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
public import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle391
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsCompactOperatorOfIsHilbertSchmidt
import Development.AutomorphicArithmetic.IntegralCasts.Bundle001
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting

@[expose] public section

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH.MinInf

theorem opNorm_le_one_of_unitary {ι : Type} [Fintype ι] [DecidableEq ι] (U : Matrix ι ι ℂ) (hU : U * Uᴴ = 1) :
    opNorm U ≤ 1 := by
  have h1 : Uᴴ * U = 1 := mul_eq_one_comm.1 hU
  set T := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) U with hT
  have h2 : star T * T = 1 := by
    rw [hT, ← map_star, ← map_mul, Matrix.star_eq_conjTranspose, h1, map_one]
  have h3 : ‖T‖ * ‖T‖ ≤ 1 := by
    rw [← CStarRing.norm_star_mul_self, h2]
    exact ContinuousLinearMap.norm_id_le
  have h4 : ‖T‖ ≤ 1 := by
    by_contra h
    have h' : 1 < ‖T‖ := not_le.1 h
    nlinarith
  exact_mod_cast h4

theorem nnnorm_entry_le {ι : Type} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (i j : ι) :
    ‖A i j‖₊ ≤ opNorm A := by
  unfold opNorm
  have h1 : (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A (EuclideanSpace.single j 1)) i = A i j := by
    change ∑ d, A i d * (EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ ι) d = A i j
    simp
  have h2 := ContinuousLinearMap.le_opNNNorm (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A) (EuclideanSpace.single j 1)
  rw [PiLp.nnnorm_single, nnnorm_one, mul_one] at h2
  rw [← h1]
  exact (PiLp.nnnorm_apply_le _ i).trans h2

theorem nnnorm_det_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : ℝ≥0) (h : ∀ i j, ‖M i j‖₊ ≤ c) :
    ‖M.det‖₊ ≤ (n.factorial : ℝ≥0) * c ^ n := by
  have h1 := Matrix.det_le (A := M) (abv := NormedField.toAbsoluteValue ℂ) (x := (c : ℝ))
    (fun i j => NNReal.coe_le_coe.2 (h i j))
  simp only [Fintype.card_fin, nsmul_eq_mul] at h1
  exact_mod_cast h1

theorem minor_le {R : Type} [CommRing R] (φ : R →+* ℂ) {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (A κ : Matrix ι ι R) (c : ℝ≥0) (hA : opNorm (A.map φ) ≤ c) (hκ : κ.map φ * (κ.map φ)ᴴ = 1) (f e : Fin n → ι) :
    ‖φ ((A * κ).submatrix f e).det‖₊ ≤ (n.factorial : ℝ≥0) * c ^ n := by
  have hAU : opNorm (A.map φ * κ.map φ) ≤ c :=
    (opNorm_mul_le _ _).trans ((mul_le_of_le_one_right' (opNorm_le_one_of_unitary _ hκ)).trans hA)
  have hdet : φ ((A * κ).submatrix f e).det = ((A.map φ * κ.map φ).submatrix f e).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← Matrix.submatrix_map, Matrix.map_mul]
  rw [hdet]
  exact nnnorm_det_le _ c fun i j => (nnnorm_entry_le (A.map φ * κ.map φ) (f i) (e j)).trans hAU

theorem opNorm_le_htInf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ι : Type) [Fintype ι] [DecidableEq ι] (w : InfinitePlace F) (τ : EmbOver E w) (X : GL ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) :
    opNorm (X.1.map (piInf τ)) ≤ htInf F w (Formalism.UG.bc (compInf F E w) X) := by
  have e : X.1.map (piInf τ) = ((Formalism.UG.bc (compInf F E w) X).1).map (infEmb τ) := by
    ext i j
    rfl
  rw [e]
  exact ((normInf_le_iff F w).1 le_rfl τ).trans (le_htOf (normInf F w) (Formalism.UG.bc (compInf F E w) X))

theorem minor_le_htInf (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (w : InfinitePlace F) (τ : EmbOver E w) (X : GL ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (κ : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (hκ : κ.map (piInf τ) * (κ.map (piInf τ))ᴴ = 1) (f e : Fin n → ι) :
    ‖piInf τ ((X.1 * κ).submatrix f e).det‖₊ ≤
      (n.factorial : ℝ≥0) * htInf F w (Formalism.UG.bc (compInf F E w) X) ^ n :=
  minor_le (piInf τ) X.1 κ _ (opNorm_le_htInf F E ι w τ X) hκ f e

end GlobalTheory.CompanionTheory.GodementH.MinInf
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

theorem trace_norm_local_sizes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ x : E, ∃ y₁ y₂ : F,
    x ^ 2 - algebraMap F E y₁ * x + algebraMap F E y₂ = 0 ∧ ∀ (v : Pl (F := F)) (τ : E →ₐ[F] FvBar F v),
      ‖algebraMap F (Fv F v) y₁‖₊ ≤ max (absBar F v (τ x)) (absBar F v (τ (σ x))) ∧
      ‖algebraMap F (Fv F v) y₂‖₊ = absBar F v (τ x) * absBar F v (τ (σ x)) := by
  intro F E _ _ _ _ _ σ hCM x
  obtain ⟨_, hEc, hfin2, hconj⟩ := hCM
  obtain ⟨τ0⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hσσ : ∀ z, σ (σ z) = z := fun z => τ0.injective (by rw [hconj, hconj, star_star])
  have hσne : ∃ w, σ w ≠ w := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have hreal : NumberField.ComplexEmbedding.IsReal τ0 := by
      rw [NumberField.ComplexEmbedding.isReal_iff]
      refine RingHom.ext fun w => ?_
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      have h1 := hconj τ0 w
      rw [hcon w] at h1
      exact h1.symm
    exact InfinitePlace.not_isReal_iff_isComplex.2 (hEc.isComplex (InfinitePlace.mk τ0)) ⟨τ0, hreal, rfl⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  have hfix : ∀ z : E, σ z = z → ∃ y : F, algebraMap F E y = z := by
    intro z hz
    have hSle : Submodule.span F {(1 : E)} ≤ LinearMap.ker (σ.toLinearMap - LinearMap.id) := by
      rw [Submodule.span_le, Set.singleton_subset_iff]
      simp
    have hker : LinearMap.ker (σ.toLinearMap - LinearMap.id) ≠ ⊤ := by
      intro htop
      obtain ⟨w, hw⟩ := hσne
      have hw' : w ∈ LinearMap.ker (σ.toLinearMap - LinearMap.id) := htop ▸ Submodule.mem_top
      rw [LinearMap.mem_ker] at hw'
      exact hw (sub_eq_zero.1 hw')
    have h1 : Module.finrank F (Submodule.span F {(1 : E)}) = 1 := finrank_span_singleton one_ne_zero
    have hlt := Submodule.finrank_lt hker
    have hge := Submodule.finrank_mono hSle
    have heq := Submodule.eq_of_le_of_finrank_eq hSle (by omega)
    have hzk : z ∈ LinearMap.ker (σ.toLinearMap - LinearMap.id) := by
      rw [LinearMap.mem_ker]
      simp [hz]
    rw [← heq] at hzk
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hzk
    exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩
  obtain ⟨y₁, hy₁⟩ := hfix (x + σ x) (by rw [map_add (f := _), hσσ, add_comm])
  obtain ⟨y₂, hy₂⟩ := hfix (x * σ x) (by rw [map_mul, hσσ, mul_comm])
  refine ⟨y₁, y₂, by rw [hy₁, hy₂]; ring, fun v τ => ?_⟩
  have key : ∀ y : F, τ (algebraMap F E y) =
      algebraMap (Fv F v) (FvBar F v) (algebraMap F (Fv F v) y) := fun y => by
    rw [τ.commutes]
    exact IsScalarTower.algebraMap_apply F (Fv F v) (FvBar F v) y
  constructor
  · rw [← absBar_algebraMap F v, ← key, hy₁, map_add (f := _)]
    exact absBar_add_le F v _ _
  · rw [← absBar_algebraMap F v, ← key, hy₂, map_mul]
    exact absBar_mul F v _ _

end GlobalTheory.CompanionTheory.GodementH
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

namespace GlobalTheory.CompanionTheory.GodementH

theorem absFin_minor_mul_le (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (v : Pl (F := F)) (X : GL ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (κ : Matrix ι ι (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hκ : ∀ i j, absFin F v (compFin F E v (κ i j)) ≤ 1) (f e : Fin n → ι) :
    absFin F v (compFin F E v ((X.1 * κ).submatrix f e).det) ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n := by
  have hent : ∀ i j, absFin F v (compFin F E v ((X.1 * κ) i j)) ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) := by
    intro i j
    have h1 : compFin F E v ((X.1 * κ) i j) = ((X.1.map (compFin F E v)) * (κ.map (compFin F E v))) i j := by
      rw [← Matrix.map_mul]; rfl
    rw [h1]
    refine (absFin_le_normFin F v _ i j).trans ((normFin_mul_le F v _ _).trans ?_)
    have h2 : normFin F v (κ.map (compFin F E v)) ≤ 1 := (normFin_le_iff F v).2 fun a b => hκ a b
    exact (mul_le_of_le_one_right' h2).trans (le_htOf (normFin F v) (Formalism.UG.bc (compFin F E v) X))
  rw [RingHom.map_det, Matrix.det_apply]
  refine absFin_sum_le F v _ _ fun σ _ => ?_
  have hprod : absFin F v (∏ i : Fin n, ((compFin F E v).mapMatrix ((X.1 * κ).submatrix f e)) (σ i) i)
      ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n := by
    calc _ ≤ ∏ i : Fin n, absFin F v (((compFin F E v).mapMatrix ((X.1 * κ).submatrix f e)) (σ i) i) :=
          Finset.le_prod_of_submultiplicative _ (absFin_one F v).le (absFin_mul_le F v) _ _
      _ ≤ ∏ _i : Fin n, htFin F v (Formalism.UG.bc (compFin F E v) X) :=
          Finset.prod_le_prod' fun i _ => hent _ _
      _ = _ := by simp
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h, one_smul]; exact hprod
  · rw [h, Units.neg_smul, one_smul, absFin_neg]; exact hprod

end GlobalTheory.CompanionTheory.GodementH
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH.Den

theorem local_exponent {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) {y : F} (hy : y ≠ 0) :
    ∃ e : ℕ, v.valuation F y ≤ WithZero.exp (e : ℤ) ∧
      max 1 ‖algebraMap F (Fv F v) y‖₊ = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ e := by
  have ha : v.valuation F y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  have hq : (1 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) := HeightOneSpectrum.one_lt_absNorm_nnreal v
  have hnorm : ‖algebraMap F (Fv F v) y‖₊ =
      WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (v.valuation F y) :=
    NNReal.eq (FinitePlace.norm_embedding' v y)
  obtain ⟨n, hn⟩ : ∃ n : ℤ, v.valuation F y = WithZero.exp n := ⟨_, (WithZero.exp_log ha).symm⟩
  have hval : WithZeroMulInt.toNNReal (HeightOneSpectrum.absNorm_ne_zero v) (WithZero.exp n) =
      (Ideal.absNorm v.asIdeal : ℝ≥0) ^ n := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    rw [WithZero.log_exp]
  refine ⟨n.toNat, ?_, ?_⟩
  · rw [hn]
    exact WithZero.exp_le_exp.2 (Int.self_le_toNat n)
  · rw [hnorm, hn, hval]
    rcases le_total n 0 with h | h
    · rw [Int.toNat_of_nonpos h, pow_zero]
      exact max_eq_left (zpow_le_one_of_nonpos₀ hq.le h)
    · have h1 : (Ideal.absNorm v.asIdeal : ℝ≥0) ^ n = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ n.toNat := by
        rw [← zpow_natCast, Int.toNat_of_nonneg h]
      rw [h1]
      exact max_eq_right (one_le_pow₀ hq.le)

theorem finite_mulSupport {F : Type} [Field F] [NumberField F] {y : F} (hy : y ≠ 0) :
    (Function.mulSupport fun v : Pl F => max 1 ‖algebraMap F (Fv F v) y‖₊).Finite := by
  have h := (FinitePlace.hasFiniteMulSupport hy).comp_of_injective
    (FinitePlace.equivHeightOneSpectrum (K := F)).symm.injective
  refine Set.Finite.subset h ?_
  intro v hv
  simp only [Function.mem_mulSupport] at hv ⊢
  intro h1
  apply hv
  have h2 : ‖algebraMap F (Fv F v) y‖₊ = 1 := by
    apply NNReal.eq
    have h3 : ‖FinitePlace.embedding v y‖ = 1 := by
      simpa [FinitePlace.equivHeightOneSpectrum_symm_apply] using h1
    exact h3
  rw [h2, max_self]

theorem denominator_le (F : Type) [Field F] [NumberField F] (y : F) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ≥0) ≤ ∏ᶠ v : Pl (F := F), max 1 ‖algebraMap F (Fv F v) y‖₊ ∧
      IsIntegral ℤ ((m : F) * y) := by
  classical
  by_cases hy : y = 0
  · subst hy
    exact ⟨1, one_pos, by simp, by simpa using isIntegral_zero⟩
  choose e he1 he2 using fun v : Pl F => local_exponent v hy
  have hfin := finite_mulSupport hy
  set S : Finset (Pl (F := F)) := hfin.toFinset with hS
  set b : Ideal (𝓞 F) := ∏ v ∈ S, v.asIdeal ^ e v with hb
  have hb0 : b ≠ ⊥ := by
    rw [hb, ← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    intro v _
    exact pow_ne_zero _ v.ne_bot
  have hm : 0 < Ideal.absNorm b :=
    Nat.pos_of_ne_zero fun h => hb0 (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨Ideal.absNorm b, hm, le_of_eq ?_, ?_⟩
  · rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) (by simp [hS])]
    simp only [he2]
    simp [hb, map_prod, map_pow]
  · have key : ∀ v : Pl (F := F), v.valuation F ((Ideal.absNorm b : F) * y) ≤ 1 := by
      intro v
      have hmem : ((Ideal.absNorm b : ℕ) : 𝓞 F) ∈ v.asIdeal ^ e v := by
        by_cases hv : v ∈ S
        · exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv) (Ideal.absNorm_mem b)
        · have h1 : max 1 ‖algebraMap F (Fv F v) y‖₊ = 1 := by
            simpa [hS] using hv
          have h0 : e v = 0 := by
            by_contra hne
            have hq : (1 : ℝ≥0) < (Ideal.absNorm v.asIdeal : ℝ≥0) :=
              HeightOneSpectrum.one_lt_absNorm_nnreal v
            have := one_lt_pow₀ hq hne
            rw [← he2 v, h1] at this
            exact lt_irrefl _ this
          simp [h0]
      have h2 := (v.intValuation_le_pow_iff_mem _ (e v)).2 hmem
      have h3 : v.valuation F (Ideal.absNorm b : F) ≤ WithZero.exp (-(e v : ℤ)) := by
        have : (Ideal.absNorm b : F) = algebraMap (𝓞 F) F ((Ideal.absNorm b : ℕ) : 𝓞 F) := by simp
        rw [this, HeightOneSpectrum.valuation_of_algebraMap]
        exact h2
      rw [map_mul]
      calc _ ≤ WithZero.exp (-(e v : ℤ)) * WithZero.exp (e v : ℤ) := mul_le_mul' h3 (he1 v)
        _ = 1 := by rw [← WithZero.exp_add]; simp
    obtain ⟨c, hc⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ key
    rw [← hc]
    exact c.isIntegral_coe

end GlobalTheory.CompanionTheory.GodementH.Den

end
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.ClozelLie

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem Eop_add_conjugate (τ : E →+* ℂ) (i : Fin a) :
    Eop τ i i + Eop (ComplexEmbedding.conjugate τ) i i = lieS E a i i (atEmb τ 1) := by
  have e1 : atEmb (ComplexEmbedding.conjugate τ) 1 = atEmb τ 1 := by rw [atEmb_conj, map_one]
  have e2 : atEmb (ComplexEmbedding.conjugate τ) Complex.I = -atEmb τ Complex.I := by
    rw [atEmb_conj, Complex.conj_I, atEmb_eq, atEmb_eq τ Complex.I]
    simp
  simp only [Eop, e1, e2, map_neg]
  module

theorem sum_atEmb_one : ∑ τ : E →+* ℂ, atEmb τ 1 = (1 + 1 : Cinf E) := by
  classical
  have e : ∀ τ : E →+* ℂ, atEmb τ 1 = Pi.single (InfinitePlace.mk τ) (1 : ℂ) := fun τ => by
    unfold atEmb
    split_ifs <;> simp
  funext w
  simp only [e, Finset.sum_apply, Pi.single_apply, Pi.add_apply, Pi.one_apply]
  simp only [eq_comm (a := w)]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, InfinitePlace.card_filter_mk_eq,
    IsTotallyComplex.mult_eq]
  norm_num

theorem sum_Eop_diag (i : Fin a) : ∑ τ : E →+* ℂ, Eop τ i i = lieS E a i i 1 := by
  have hs : ∑ τ : E →+* ℂ, Eop (ComplexEmbedding.conjugate τ) i i = ∑ τ : E →+* ℂ, Eop τ i i :=
    Equiv.sum_comp (Function.Involutive.toPerm _ (fun τ : E →+* ℂ => star_star τ))
      (fun τ => Eop τ i i)
  have h : (∑ τ : E →+* ℂ, Eop τ i i) + ∑ τ : E →+* ℂ, Eop τ i i = lieS E a i i 1 + lieS E a i i 1 := by
    nth_rw 2 [← hs]

    rw [← Finset.sum_add_distrib, Finset.sum_congr rfl fun τ _ => Eop_add_conjugate τ i, ← map_sum,
    sum_atEmb_one, map_add]
  have h2 : (2 : ℂ) • (∑ τ : E →+* ℂ, Eop τ i i) = (2 : ℂ) • lieS E a i i 1 := by
    rw [two_smul, two_smul, h]
  exact smul_right_injective _ (two_ne_zero (α := ℂ)) h2

theorem lie_oneL_eq_sum_Eop (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) :
    lie E a (oneL E a) = ∑ τ : E →+* ℂ, ∑ i : Fin a, Eop τ i i := by
  rw [Finset.sum_comm, Finset.sum_congr rfl fun i _ => sum_Eop_diag i]
  simp only [lieS_apply]

  rw [← map_sum]
  have hm : ∑ i : Fin a, Matrix.single i i (1 : Cinf E) = 1 := by
    refine Matrix.ext fun p q => ?_
    rw [Matrix.sum_apply, Matrix.one_apply]
    by_cases h : p = q
    · subst h
      simp [Matrix.single_apply]
    · rw [if_neg h]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [Matrix.single_apply, if_neg]
      rintro ⟨rfl, rfl⟩
      exact h rfl
  congr 1
  exact (congrArg Matrix.of.symm hm).symm

end GlobalTheory.CompanionTheory.ClozelLie
end
end

section

noncomputable section

open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.ZalgCentral

theorem Zalg_mul_lie : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (z : Module.End ℂ (Sm E a)),
    z ∈ Zalg E a → ∀ X, z * lie E a X = lie E a X * z := by
  intro E _ _ _ a z hz X
  unfold Zalg at hz
  have hle : Algebra.adjoin ℂ {z : Module.End ℂ (Sm E a) | ∃ τ u, z = cap τ u} ≤
      Subalgebra.centralizer ℂ {lie E a X} := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨τ, u, rfl⟩
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact (commute_cap_lie τ u X).symm.eq
  have hc := (Subalgebra.mem_centralizer_iff ℂ).mp (hle hz) (lie E a X) (Set.mem_singleton _)
  exact hc.symm

end GlobalTheory.CompanionTheory.ZalgCentral
end
end

section

open NumberField MeasureTheory Topology GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.CuspidalSpectrum

noncomputable section
namespace GlobalTheory.CompanionTheory.CuspTransfer

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

def resQ (φ : GA E a → ℂ) : RightCosetSpace (rationalGLOne (K := E) (n := a)) → ℂ :=
  fun q => φ ((Quotient.out q : normOneGL (K := E) (n := a)) : GA E a)

theorem resQ_mk {φ : GA E a → ℂ} (h : ∀ γ g, φ (ratGL E a γ * g) = φ g) (x : normOneGL (K := E) (n := a)) :
    resQ φ (RightCosetSpace.mk _ x) = φ x := by
  have e : RightCosetSpace.mk (rationalGLOne (K := E) (n := a))
      (Quotient.out (RightCosetSpace.mk (rationalGLOne (K := E) (n := a)) x)) = RightCosetSpace.mk _ x :=
    Quotient.out_eq _
  obtain ⟨γ, hγ⟩ := RightCosetSpace.mk_eq_mk_iff.1 e
  obtain ⟨δ, hδ⟩ : ((γ : normOneGL (K := E) (n := a)) : GA E a) ∈ AdelicGLn.rationalGL E a := γ.2
  unfold resQ
  rw [← hγ]
  change φ (((γ : normOneGL (K := E) (n := a)) : GA E a) * (x : GA E a)) = _
  rw [← hδ]
  exact h δ x.1

theorem continuous_resQ {φ : GA E a → ℂ} (hc : Continuous φ) (h : ∀ γ g, φ (ratGL E a γ * g) = φ g) :
    Continuous (resQ φ) := by
  refine (RightCosetSpace.isOpenQuotientMap_mk (rationalGLOne (K := E) (n := a))).isQuotientMap.continuous_iff.2 ?_
  have : resQ φ ∘ RightCosetSpace.mk (rationalGLOne (K := E) (n := a)) = fun x : normOneGL (K := E) (n := a) => φ x :=
    funext fun x => resQ_mk h x
  rw [this]
  exact hc.comp continuous_subtype_val

end GlobalTheory.CompanionTheory.CuspTransfer
end
end
