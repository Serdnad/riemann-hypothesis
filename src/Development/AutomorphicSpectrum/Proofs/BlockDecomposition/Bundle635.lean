module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle081
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle009
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle061
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle296
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
import Mathlib.Algebra.Module.StablyFree.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle459
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.Bundle002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle025
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle454
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle063
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle107
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle456
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle154
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle053
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle058
import Formalism.LocalRingCardinality.DataHost
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle628
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle627
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.Finsupp.Pointwise
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle012
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle082
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle431
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.Interleave
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyInterleaving.LInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle430
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle001
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.ThetaOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem core_integrable {W : Type} [Fintype W] {n M : ℕ} (hnM : 2 * n < M) (J : W → Matrix (Fin M) (Fin M) ℂ)
    (hJ : ∀ w, (J w).IsHermitian) (hJd : ∀ w, (J w).det ≠ 0) {N : ℕ}
    (e : (W → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ)) (he : Continuous e) (hes : Continuous e.symm)
    (f : SchwartzMap (Fin N → ℝ) ℂ) (μ : Measure (W → Fin n → Fin M → ℂ)) (hμ : μ.IsAddHaarMeasure)
    (ν : Measure (W → hermC n)) (hν : ν.IsAddHaarMeasure) :
    Integrable (coreC J μ (fun X => f (e X))) ν := by
  obtain ⟨C, hC⟩ := GlobalTheory.T.archimedean_orbital_integral_hua_bound W n M J hJ hJd N e he hes f μ hμ
  have hcont := GlobalTheory.T.archimedean_orbital_integral_continuous W n M J N e he hes f μ hμ
  have hs : (n : ℝ) - 1 / 2 < (M : ℝ) / 2 := by
    have : (2 * n + 1 : ℝ) ≤ M := by exact_mod_cast hnM
    linarith
  have hint := (GlobalTheory.T.product_hua_determinant_integrable W n ((M : ℝ) / 2) hs ν hν).const_mul C
  refine hint.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun b => ?_)
  have := hC b
  simpa [neg_div] using this

theorem integrable_starLoc_inf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
  ∀ n : ℕ, 2 * n < M → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
  ∀ ν : Measure (HermR (Ainf F) σ n), ν.IsAddHaarMeasure →
  ∀ P : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, GlobalTheory.Published.SiegelOneVector.IsSchwartzArch P →
    Integrable (starLoc (Ainf F) σ J (psiInf F ψ) μ P) ν := by
  intro F E _ _ _ _ _ σ hcm M J hJ n hn ψ hψ μ hμ ν hν P hP
  obtain ⟨ρ, e, hρ, he, heρ, -, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hcm.1
  obtain ⟨a, ha, hinf, -, -, -⟩ := GlobalTheory.T.adelic_character_archimedean_form F hcm.1 ρ e hρ he heρ ψ hψ
  obtain ⟨τ, Θ, hΘ⟩ := GlobalTheory.T.complex_coordinates_exist_at_infinity F E σ hcm ρ e hρ he heρ
  obtain ⟨Ψ, hΨ, hΨν⟩ := GlobalTheory.T.hermitian_archimedean_complex_coordinates F E σ hcm e τ Θ hΘ n
  obtain ⟨Φ, hΦ, hΦc, hΦs, hΦμ⟩ := GlobalTheory.T.tuple_archimedean_complex_coordinates F E σ hcm e τ Θ hΘ n M
  obtain ⟨N, e₀, he₀, he₀s, f, hP⟩ := hP
  obtain ⟨hνH, hνI⟩ := hΨν ν hν
  obtain ⟨hμH, hμI⟩ := hΦμ μ hμ
  let Jc : InfinitePlace F → Matrix (Fin M) (Fin M) ℂ := fun w => ((ρ w a : ℝ) : ℂ) • J.map (τ w)
  have hρa : ∀ w, ((ρ w a : ℝ) : ℂ) ≠ 0 := fun w => by
    simpa using (map_ne_zero (ρ w)).2 ha
  have hJc : ∀ w, (Jc w).IsHermitian := fun w => by
    ext i j
    have h1 := hJ.1 i j
    have h2 := hcm.2.2.2 (τ w) (J j i)
    simp only [Jc, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul',
      Complex.star_def, Complex.conj_ofReal]
    rw [h1] at h2
    rw [h2]
    rfl
  have hJd : ∀ w, (Jc w).det ≠ 0 := fun w => by
    simp only [Jc, Matrix.det_smul]
    refine mul_ne_zero (pow_ne_zero _ (hρa w)) ?_
    have : (J.map (τ w)).det = τ w J.det := by
      simpa using (RingHom.map_det (τ w) J).symm
    rw [this]
    exact (map_ne_zero (τ w)).2 hJ.2
  let e₂ : (InfinitePlace F → Fin n → Fin M → ℂ) ≃+ (Fin N → ℝ) := Φ.symm.trans e₀
  have he₂ : Continuous e₂ := he₀.comp hΦs
  have he₂s : Continuous e₂.symm := hΦc.comp he₀s
  have hcore := core_integrable hn Jc hJc hJd e₂ he₂ he₂s f (μ.map Φ) hμH (ν.map Ψ) hνH
  have := hνI _ hcore
  refine this.congr (Filter.Eventually.of_forall fun b => ?_)
  show coreC Jc (μ.map Φ) (fun X => f (e₂ X)) (Ψ b) = starLoc (Ainf F) σ J (psiInf F ψ) μ P b
  rw [coreC, ← hμI]
  unfold starLoc
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  show f (e₂ (Φ X)) * _ = P X * _
  have hph := GlobalTheory.T.archimedean_character_in_coordinates F E σ ρ e τ Θ hΘ heρ a ψ hinf M n J (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) X
  rw [hph, hP X]
  have h1 : e₂ (Φ X) = e₀ X := by simp [e₂]
  have h2 : (fun w => ((Ψ b w : hermC n) : Matrix (Fin n) (Fin n) ℂ)) = fun w => matC Θ (b : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) w := funext (hΨ b)
  rw [h1, h2, hΦ X]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatTest

theorem trace_tmul_eq {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] (r : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] e) = r * algebraMap F R (Algebra.trace F E e) := by
  have h1 : (r ⊗ₜ[F] e : R ⊗[F] E) = r • ((1 : R) ⊗ₜ[F] e) := by
    simp [TensorProduct.smul_tmul']
  have h2 : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e)
      = LinearMap.baseChange R (Algebra.lmul F E e) := by
    refine LinearMap.ext fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s y => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [h1, map_smul, Algebra.trace_apply, h2, LinearMap.trace_baseChange, Algebra.trace_apply]
  simp

theorem inNOh_tmul {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
    (b : Module.Basis (Fin d) F E) (N : ℕ) {α : Af F} (hα : α ∈ Oh F) (k : Fin d) :
    InNOh b N (((N : Af F) * α) ⊗ₜ[F] b k) := by
  intro j
  by_cases h : j = k
  · subst h
    exact ⟨α, hα, by simp [Algebra.TensorProduct.basis_repr_tmul]⟩
  · refine ⟨0, fun v => zero_mem _, ?_⟩
    simp [Algebra.TensorProduct.basis_repr_tmul, Finsupp.single_apply, Ne.symm h]

theorem exists_common_denom {E : Type} [Field E] [NumberField E] {d : ℕ} (ε : Fin d → E) :
    ∃ y : ℤ, y ≠ 0 ∧ ∀ k, IsIntegral ℤ ((y : E) * ε k) := by
  have hex : ∀ k, ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ ((y : E) * ε k) := by
    intro k
    obtain ⟨y, hy, h⟩ := IsAlgebraic.exists_integral_multiple (R := ℤ) ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic (ε k)))
    exact ⟨y, hy, by simpa [zsmul_eq_mul] using h⟩
  choose y hy hint using hex
  refine ⟨∏ k, y k, Finset.prod_ne_zero_iff.mpr fun k _ => hy k, fun k => ?_⟩
  have h1 : (((∏ j, y j : ℤ)) : E) * ε k
      = ((∏ j ∈ Finset.univ.erase k, y j : ℤ) : E) * ((y k : E) * ε k) := by
    rw [← mul_assoc, ← Int.cast_mul, mul_comm (∏ j ∈ Finset.univ.erase k, y j) (y k),
      Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  rw [h1]
  have h2 : IsIntegral ℤ (((∏ j ∈ Finset.univ.erase k, y j : ℤ)) : E) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := E) (x := (∏ j ∈ Finset.univ.erase k, y j : ℤ))
  exact h2.mul (hint k)

theorem rat_test : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ),
    IsCharAF F ψ → ∀ N : ℕ, 0 < N → ∀ D : ℕ, 0 < D → (∀ f : F,
      (∀ r : 𝓞 F, ∃ m : ℤ, Algebra.trace ℚ F (f * (r : F)) = m) → ∃ o : 𝓞 F, (o : F) = (D : F) * f) →
    ∃ t : F, t ≠ 0 ∧ ∀ w : E, (∀ x : Af F ⊗[F] E, InNOh b N x →
        psiFin F ψ (Algebra.trace (Af F) (Af F ⊗[F] E) (sigR (Af F) σ x * inclR (Af F) w)) = 1) →
      ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = t • w := by
  intro F E _ _ _ _ _ σ hCM d b ψ hψ N hN D hD hDint
  have hF : IsTotallyReal F := hCM.1
  obtain ⟨ρ, e, h1, h2, h3, -, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hF
  obtain ⟨a, ha, -, ψf, hstd, hpsi⟩ := GlobalTheory.T.adelic_character_archimedean_form F hF ρ e h1 h2 h3 ψ hψ
  have hbeta := ((GlobalTheory.T.standard_adelic_character F).2 ψf hstd).2.2
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  let τ : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  let b' : Module.Basis (Fin d) F E := b.map τ.toLinearEquiv
  have hb' : ∀ k, b' k = σ (b k) := fun k => by simp [b', τ]
  let ε := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b'
  obtain ⟨y, hy, hyint⟩ := exists_common_denom (fun k => ε k)
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hDF : (D : F) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
  have hyF : (y : F) ≠ 0 := Int.cast_ne_zero.mpr hy
  refine ⟨(y : F) * ((D : F) * (a * (N : F))), mul_ne_zero hyF (mul_ne_zero hDF (mul_ne_zero ha hNF)), ?_⟩
  intro w hw

  have hcoord : ∀ k, ∃ o : 𝓞 F, (o : F) = (D : F) * (a * (N : F) * ε.repr w k) := by
    intro k
    have hrepr : ε.repr w k = Algebra.trace F E (σ (b k) * w) := by
      rw [LinearMap.BilinForm.dualBasis_repr_apply, hb', Algebra.traceForm_apply, mul_comm]
    refine hDint _ ((hbeta _).mp fun α hα => ?_)
    have hx := hw (((N : Af F) * α) ⊗ₜ[F] b k) (inNOh_tmul b N hα k)
    have e1 : sigR (Af F) σ (((N : Af F) * α) ⊗ₜ[F] b k) * inclR (Af F) w
        = ((N : Af F) * α) ⊗ₜ[F] (σ (b k) * w) := by
      change (((N : Af F) * α) ⊗ₜ[F] σ (b k)) * ((1 : Af F) ⊗ₜ[F] w) = _
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [e1, trace_tmul_eq] at hx
    change ψ (pairA F 0 _) = 1 at hx
    rw [hpsi] at hx
    rw [hrepr, ← hx]
    congr 1
    simp only [map_mul, map_natCast]
    ring
  choose o ho using hcoord
  rw [← IsIntegralClosure.isIntegral_iff (A := 𝓞 E) (R := ℤ), ← ε.sum_repr w, Finset.smul_sum]
  refine IsIntegral.sum _ fun k _ => ?_
  have e2 : ((y : F) * ((D : F) * (a * (N : F)))) • (ε.repr w k • ε k)
      = algebraMap F E (o k : F) * ((y : E) * ε k) := by
    have e3 : (y : F) * ((D : F) * (a * (N : F))) * ε.repr w k
        = (y : F) * ((D : F) * (a * (N : F) * ε.repr w k)) := by ring
    rw [smul_smul, Algebra.smul_def, e3, ho k, map_mul, map_intCast]
    ring
  rw [e2]
  exact (IsIntegral.algebraMap (RingOfIntegers.isIntegral_coe (o k))).mul (hyint k)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl.RatTest
end

section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M GlobalTheory.CompanionTheory.WordProd
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.WordProd.OneBlockProd

theorem exists_equiv_tensor {α : Type} [Fintype α] [DecidableEq α] (X : α → Type) [∀ i, AddCommGroup (X i)]
    [∀ i, Module ℂ (X i)] (i₀ : α) (hx : ∀ i, i ≠ i₀ → ∃ v : X i, v ≠ 0 ∧ ∀ w, ∃ a : ℂ, a • v = w) :
    ∃ (x : ∀ i, X i) (ι : X i₀ ≃ₗ[ℂ] ⨂[ℂ] i, X i),
      ∀ v, ι v = PiTensorProduct.tprod ℂ (Function.update x i₀ v) := by
  have hx' : ∀ i, ∃ (x : X i) (c : Module.Dual ℂ (X i)), i ≠ i₀ → c x = 1 ∧ ∀ w, c w • x = w := by
    intro i
    by_cases hi : i = i₀
    · exact ⟨0, 0, fun h => absurd hi h⟩
    · obtain ⟨v, hv, hs⟩ := hx i hi
      obtain ⟨f, hf⟩ : ∃ f : Module.Dual ℂ (X i), f v ≠ 0 := by
        by_contra h
        push Not at h
        exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
      refine ⟨v, (f v)⁻¹ • f, fun _ => ⟨by simp [hf], fun w => ?_⟩⟩
      obtain ⟨a, rfl⟩ := hs w
      simp [hf, mul_comm]
  choose x c hc using hx'
  let T : X i₀ →ₗ[ℂ] ⨂[ℂ] i, X i := (PiTensorProduct.tprod ℂ).toLinearMap x i₀
  have hT : ∀ v, T v = PiTensorProduct.tprod ℂ (Function.update x i₀ v) := fun v => rfl
  have hinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).2 fun v hv => ?_
    refine (Module.forall_dual_apply_eq_zero_iff ℂ v).1 fun l => ?_
    have h1 := congrArg (PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ α ℂ).compLinearMap
      (Function.update c i₀ l))) hv
    rw [hT, PiTensorProduct.lift.tprod, map_zero] at h1
    simp only [MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply] at h1
    rw [Finset.prod_eq_single_of_mem i₀ (Finset.mem_univ _) (fun i _ hi => by
      rw [Function.update_of_ne hi, Function.update_of_ne hi]
      exact (hc i hi).1)] at h1
    simpa using h1
  have hsurj : Function.Surjective T := by
    intro y
    refine PiTensorProduct.induction_on y (fun r f => ?_) (fun y z hy hz => ?_)
    · let d : α → ℂ := fun i => if h : i = i₀ then 1 else c i (f i)
      have e1 : f = fun i => d i • Function.update x i₀ (f i₀) i := by
        funext i
        by_cases h : i₀ = i
        · subst h
          simp [d]
        · have h' : i ≠ i₀ := fun e => h e.symm
          simp only [d, dif_neg h', Function.update_of_ne h']
          exact ((hc i h').2 (f i)).symm
      have e2 : PiTensorProduct.tprod ℂ f =
          (∏ i, d i) • PiTensorProduct.tprod ℂ (Function.update x i₀ (f i₀)) := by
        calc
          _ = PiTensorProduct.tprod ℂ (fun i => d i • Function.update x i₀ (f i₀) i) := congrArg _ e1
          _ = _ := by simpa using (PiTensorProduct.tprod ℂ).map_smul_univ d (Function.update x i₀ (f i₀))
      exact ⟨r • (∏ i, d i) • f i₀, by rw [map_smul, map_smul, hT, e2]⟩
    · obtain ⟨u, rfl⟩ := hy
      obtain ⟨v, rfl⟩ := hz
      exact ⟨u + v, map_add _ _ _⟩
  exact ⟨x, LinearEquiv.ofBijective T ⟨hinj, hsurj⟩, hT⟩

theorem exists_line {G V : Type} [Group G] [Subsingleton G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (hirr : π.IsIrreducible) : ∃ v : V, v ≠ 0 ∧ ∀ w, ∃ a : ℂ, a • v = w := by
  have hg : ∀ g : G, g = 1 := fun g => Subsingleton.elim _ _
  have hnt : ∃ v : V, v ≠ 0 := by
    by_contra h
    push Not at h
    have : (⊥ : Subrepresentation π) = ⊤ := by
      ext v; rw [h v]; exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
    exact bot_ne_top this
  obtain ⟨v, hv⟩ := hnt
  let S : Subrepresentation π := ⟨Submodule.span ℂ {v}, fun g w hw => by simpa [hg g] using hw⟩
  have hS : S = ⊤ := (eq_bot_or_eq_top S).resolve_left fun h => hv (by
    have : v ∈ S := Submodule.mem_span_singleton_self v
    rw [h] at this; exact this)
  refine ⟨v, hv, fun w => ?_⟩
  have : w ∈ S := by rw [hS]; trivial
  exact Submodule.mem_span_singleton.1 this

theorem exists_conj_perm {n R : Type} [Fintype n] [DecidableEq n] [CommRing R] (e : n ≃ n) :
    ∃ w : GL n R, ∀ y : GL n R,
      ((w * y * w⁻¹ : GL n R) : Matrix n n R) = (y : Matrix n n R).submatrix e e := by
  let P : Matrix n n R := (1 : Matrix n n R).submatrix e (Equiv.refl n)
  let Q : Matrix n n R := (1 : Matrix n n R).submatrix (Equiv.refl n) e
  have hP : ∀ y : Matrix n n R, P * y = y.submatrix e (Equiv.refl n) := fun y => by
    ext s t
    simp [P, Matrix.mul_apply, Matrix.one_apply]
  have hQ : ∀ y : Matrix n n R, y * Q = y.submatrix (Equiv.refl n) e := fun y => by
    ext s t
    simp [Q, Matrix.mul_apply, Matrix.one_apply]
  have h1 : P * Q = 1 := by
    rw [hQ]
    ext s t
    simp [P, Matrix.one_apply]
  have h2 : Q * P = 1 := mul_eq_one_comm.1 h1
  refine ⟨⟨P, Q, h1, h2⟩, fun y => ?_⟩
  show P * (y : Matrix n n R) * Q = _
  rw [hQ, hP]
  rfl

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nonempty_equiv_parInd {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] {V W : Type} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) W}
    {π : Representation ℂ (GL n k) V} (hπ : IsSmooth π) (hP : ∀ g : GL n k, g ∈ parab k e)
    (hd : ∀ z, deltaHalf k m z = 1) (L : V ≃ₗ[ℂ] W)
    (law0 : ∀ (p : parab k e) v, ρ (leviProj k e p) (L v) = L (π p v)) :
    Nonempty (π.Equiv (parInd e ρ)) := by
  have law : ∀ (p : parab k e) v, _root_.GlobalTheory.SmGL.twist ρ (deltaHalf k m) (leviProj k e p) (L v) = L (π p v) := fun p v => by
    simp only [twist_apply, hd, Units.val_one, one_smul, law0]
  let f : π.IntertwiningMap (parInd e ρ) :=
    { toFun := fun v => ⟨⟨fun x => L (π x v), fun p x => by
          refine Eq.trans ?_ (law p _).symm
          simp⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ v).mem_nhds (by simp)) fun g hg => by
          have hg' : π g v = v := hg
          refine Subtype.ext (funext fun x => ?_)
          show L (π (x * g) v) = L (π x v)
          simp [hg'])⟩
      map_add' := fun v w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c v => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun g => LinearMap.ext fun v => Subtype.ext (Subtype.ext (funext fun x => by
        show L (π x (π g v)) = L (π (x * g) v)
        simp)) }
  refine ⟨equivOfBijective f ⟨fun v w h => ?_, fun φ => ⟨L.symm (φ.1.1 1), Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩⟩
  · have h1 : L (π 1 v) = L (π 1 w) := congrArg (fun φ => φ.1.1 1) h
    simpa using h1
  · have h1 := φ.1.2 ⟨x, hP x⟩ 1
    rw [mul_one] at h1
    refine (law ⟨x, hP x⟩ _).symm.trans ?_
    rw [L.apply_symm_apply]
    exact h1.symm

theorem multiProd_single {α : Type} [Fintype α] [LinearOrder α] (b : α → ℕ) (i₀ : α)
    (h0 : ∀ i, i ≠ i₀ → b i = 0) (σ : ∀ i, IrrRep (GL (Fin (b i)) k))
    (g : (Σ i, Fin (b i)) ≃ Fin (b i₀)) :
    Nonempty ((multiProd g fun i => (σ i).ρ).Equiv (σ i₀).ρ) := by
  have hP : ∀ x : GL (Fin (b i₀)) k, x ∈ parab k g := fun x =>
    OneBlockCell.mem_parab_of_single g i₀ h0 x
  have hsub : ∀ i, i ≠ i₀ → Subsingleton (GL (Fin (b i)) k) := by
    intro i hi
    haveI : IsEmpty (Fin (b i)) := by rw [h0 i hi]; infer_instance
    exact ⟨fun x y => Units.ext (Subsingleton.elim _ _)⟩
  obtain ⟨x, ι, hι⟩ := exists_equiv_tensor (fun i => (σ i).V) i₀ (fun i hi =>
    haveI := hsub i hi
    exists_line (σ i).ρ (σ i).irr)
  let E : Fin (b i₀) ≃ Fin (b i₀) := (OneBlockCell.valEquiv i₀ rfl h0).symm.trans g
  obtain ⟨w, hw⟩ := exists_conj_perm (R := k) E
  have hwp : ∀ p : parab k g, leviProj k g p i₀ = w * (p : GL (Fin (b i₀)) k) * w⁻¹ := fun p =>
    Units.ext (Matrix.ext fun s t => by
      rw [hw]
      rfl)
  let A : (σ i₀).V ≃ₗ[ℂ] (σ i₀).V := LinearEquiv.ofLinear ((σ i₀).ρ w) ((σ i₀).ρ w⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
  obtain ⟨φ⟩ := nonempty_equiv_parInd (ρ := piTensor fun i => (σ i).ρ) (π := (σ i₀).ρ) g (σ i₀).smooth hP
    (OneBlockCell.deltaHalf_eq_one_of_single i₀ h0) (A.trans ι) (fun p v => by
      show (piTensor fun i => (σ i).ρ) (leviProj k g p) (ι ((σ i₀).ρ w v)) = ι ((σ i₀).ρ w ((σ i₀).ρ p v))
      rw [hι, hι, piTensor_tprod]
      refine congrArg _ (funext fun i => ?_)
      rw [Function.apply_update (fun i u => (σ i).ρ (leviProj k g p i) u)]
      by_cases h : i₀ = i
      · subst h
        rw [Function.update_self, Function.update_self, hwp, ← Module.End.mul_apply, ← map_mul,
          inv_mul_cancel_right, map_mul, Module.End.mul_apply]
      · have h' : i ≠ i₀ := fun e => h e.symm
        haveI := hsub i h'
        rw [Function.update_of_ne h', Function.update_of_ne h',
          Subsingleton.elim (leviProj k g p i) 1, map_one]
        rfl)
  exact ⟨φ.symm⟩

theorem multiProd_clOf_single : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a : IrrGL (k := k)) {α : Type} [Fintype α] [LinearOrder α] (b : α → ℕ) (i₀ : α), b i₀ = a.1 → (∀ i, i ≠ i₀ → b i = 0) → ∀ (g : (Σ i, Fin (b i)) ≃ Fin a.1), Nonempty ((multiProd g fun i => (clOf a (b i)).rep.ρ).Equiv a.rep) := by
  intro k _ _ _ _ a α _ _ b i₀ hb h0 g
  obtain ⟨N, c⟩ := a
  dsimp only at hb g ⊢
  subst hb
  obtain ⟨φ⟩ := multiProd_single b i₀ h0 (fun i => (clOf ⟨b i₀, c⟩ (b i)).rep) g
  have key : ∀ d : IrrCl (GL (Fin (b i₀)) k), d = c → Nonempty (d.rep.ρ.Equiv c.rep.ρ) := by
    rintro _ rfl
    exact ⟨.refl _⟩
  obtain ⟨ψ⟩ := key _ (clOf_self ⟨b i₀, c⟩)
  exact ⟨φ.trans ψ⟩

end GlobalTheory.CompanionTheory.WordProd.OneBlockProd

end
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.factorizable_siegel_weil_finite_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))) (φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (A : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ → (∀ v, IsCompact (A v) ∧ IsOpen (A v)) → (∀ v, v ∉ S → A v = latV b v) → GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (pureN φ A) := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.pureN_isSchwartzBruhat | exact GlobalTheory.CompanionTheory.WhitFree.pureN_isSchwartzBruhat | (intros; apply GlobalTheory.CompanionTheory.WhitFree.pureN_isSchwartzBruhat <;> assumption)
end

section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.euler_product_almost_all_standard : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (M n d : ℕ) (b : Module.Basis (Fin d) F E) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : NNReal) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), GlobalTheory.CompanionTheory.SW.IsEulerProd b I c minf m → ∃ S₀ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∀ S, S₀ ⊆ S → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Measurable φ → Integrable φ minf → ∀ A : (∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), (∀ v, MeasurableSet (A v)) → (∀ v, m v (A v) ≠ ⊤) → (∀ v, v ∉ S → A v = latV b v) → Integrable (pureN φ A) I ∧ ∫ X, pureN φ A X ∂I = (c : ℂ) * (∫ X, φ X ∂minf) * (∏ v ∈ S, ((m v (A v)).toReal : ℂ)) * ((∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal : ℝ) : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.WhitFree.Euler.integrable_integral_pureN | exact GlobalTheory.CompanionTheory.WhitFree.Euler.integrable_integral_pureN | (intros; apply GlobalTheory.CompanionTheory.WhitFree.Euler.integrable_integral_pureN <;> assumption)
end
