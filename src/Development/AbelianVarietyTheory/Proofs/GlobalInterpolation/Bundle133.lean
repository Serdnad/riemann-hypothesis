module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle002
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle004
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle009
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle011
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowPrincipal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle084
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle086
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StarDetMulDetMem
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle001
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesImagQuadShortIntervalLowerBound
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle003
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle060
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle004
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle051
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle334
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle337
public import Formalism.SharpRestriction.Divisibility.StatementFT.PeriodPointConditions
public import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdmissiblePeriodZeroOfClassPeriodDecompositionAl
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle130
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle102
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle037
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle038
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdChar
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle001
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Th0CharMulOpUTh0HalfPeriodEq
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
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle082

@[expose] public section

section


theorem _root_.GlobalTheory.T.adelicUnitaryGroupHaarProperties_proof : GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure.AdelicUnitaryHaar := by
  first | exact @GlobalTheory.adelicUnitaryHaar_holds | exact GlobalTheory.adelicUnitaryHaar_holds | (intros; apply GlobalTheory.adelicUnitaryHaar_holds <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.LocalDualIndex

theorem _root_.GlobalTheory.T.existsUnique_isStandardAdeleChar_unramifiedCM_base : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (σ : E →ₐ[F] E), IsCMExt F E σ → (∀ x : E, star x = σ x) → Formalism.HermitianLatticesTheory.IsCMUnram E → ∃! ψ₀ : AddChar (AF F) ℂ, IsStdChar F ψ₀ := by
  first | exact @GlobalTheory.StdCharUnique.existsUnique_isStdChar_cm | exact GlobalTheory.StdCharUnique.existsUnique_isStdChar_cm | (intros; apply GlobalTheory.StdCharUnique.existsUnique_isStdChar_cm <;> assumption)
end

section


theorem _root_.GlobalTheory.T.stabiliser_self_dual_lattice_level_index_formula : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeIndex.StabiliserLevelIndexFormula := by
  first | exact @GlobalTheory.LevelIndex.selfDualLatticeIndex_stabiliserLevelIndexFormula | exact GlobalTheory.LevelIndex.selfDualLatticeIndex_stabiliserLevelIndexFormula | (intros; apply GlobalTheory.LevelIndex.selfDualLatticeIndex_stabiliserLevelIndexFormula <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.ChiUnit

open GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

theorem norm_integer_le {E K : Type} [Field E] [NumberField E] [NormedField K] [IsUltrametricDist K] (ψ : E →+* K) (r : 𝓞 E) :
    ‖ψ r‖ ≤ 1 := by
  have h : IsIntegral ℤ (ψ r) := (r.isIntegral_coe).map ψ.toIntAlgHom
  by_contra H
  push Not at H
  obtain ⟨f, hf, e⟩ := h
  rw [hf.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at e
  have e2 := congrArg norm (eq_neg_of_add_eq_zero_left e)
  rw [norm_neg, norm_pow] at e2
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | h0
  · simp [h0] at e2
  · have := IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (s := Finset.range f.natDegree)
      (f := fun i => Polynomial.eval₂ (algebraMap ℤ K) (ψ r) (Polynomial.C (f.coeff i) * Polynomial.X ^ i))
      (C := ‖ψ r‖ ^ (f.natDegree - 1)) (by positivity) (fun i hi => by
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow]
        have h1 : ‖algebraMap ℤ K (f.coeff i)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ _
        have h2 : ‖ψ r‖ ^ i ≤ ‖ψ r‖ ^ (f.natDegree - 1) :=
          pow_le_pow_right₀ H.le (by have := Finset.mem_range.1 hi; omega)
        calc _ ≤ 1 * _ := mul_le_mul h1 h2 (by positivity) zero_le_one
          _ = _ := one_mul _)
    rw [← e2] at this
    exact absurd this (not_le.2 (pow_lt_pow_right₀ H (by omega)))

theorem exists_prime_under {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] (ψ : E →+* ℂ_[p]) :
    ∃ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal ∧ ∀ r : 𝓞 E, r ∉ P.asIdeal → ‖ψ r‖ = 1 := by
  let I : Ideal (𝓞 E) :=
    { carrier := {r | ‖ψ r‖ < 1}
      add_mem' := fun {a b} ha hb => by
        show ‖ψ ((a + b : 𝓞 E) : E)‖ < 1
        rw [RingOfIntegers.coe_eq_algebraMap, map_add (f := _), map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by
        show ‖ψ ((0 : 𝓞 E) : E)‖ < 1
        simp
      smul_mem' := fun c a ha => by
        show ‖ψ ((c * a : 𝓞 E) : E)‖ < 1
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (norm_integer_le ψ c)).trans_lt ha }
  have hI : ∀ r, r ∈ I ↔ ‖ψ r‖ < 1 := fun _ => Iff.rfl
  have h1 : ∀ r, r ∉ I → ‖ψ r‖ = 1 := fun r hr =>
    le_antisymm (norm_integer_le ψ r) (not_lt.1 hr)
  have hp : (p : 𝓞 E) ∈ I := by
    rw [hI, RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast, ← map_natCast (algebraMap ℚ_[p] ℂ_[p]),
      norm_algebraMap']
    exact Padic.norm_p_lt_one
  refine ⟨⟨I, ⟨?_, fun {a b} hab => ?_⟩, ?_⟩, hp, h1⟩
  · rw [Ideal.ne_top_iff_one, hI]
    simp
  · by_contra H
    push Not at H
    rw [hI, RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, norm_mul] at hab
    have ha := h1 a H.1
    have hb := h1 b H.2
    rw [RingOfIntegers.coe_eq_algebraMap] at ha hb
    rw [ha, hb] at hab
    simp at hab
  · intro h
    rw [h, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)

theorem norm_eq_one_of_val {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] (ψ : E →+* ℂ_[p]) {y : E}
    (hy : ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → P.valuation E y = 1) : ‖ψ y‖ = 1 := by
  obtain ⟨P, hP, h1⟩ := exists_prime_under ψ
  have key : ∀ x : E, IntAt P x → ‖ψ x‖ ≤ 1 := by
    rintro x ⟨r, s, hs, e⟩
    have := congrArg (fun z => ‖ψ z‖) e
    have h2 := h1 s hs
    rw [RingOfIntegers.coe_eq_algebraMap] at h2
    simp only [map_mul, norm_mul, h2, one_mul] at this
    rw [this]
    exact norm_integer_le ψ r
  have hv := hy P hP
  have h0 : y ≠ 0 := by rintro rfl; simp at hv
  obtain ⟨a, b⟩ := (GlobalTheory.CharValCompare.val_eq_one_iff h0).1 hv
  have hb := key _ b
  rw [map_inv₀, norm_inv, inv_le_one₀ (norm_pos_iff.2 (by simpa using h0))] at hb
  exact le_antisymm (key _ a) hb

variable {D : D7} {X : Fields} {s : Seam D X} {χ : TaylorLogMetric.IdE D → ℂ}

theorem symm_conj (hs : s.Ok) (x : D.host.E) : s.iE.symm (D.host.conj x) = star (s.iE.symm x) := by
  apply s.iE.injective
  rw [hs.2, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

theorem normOne_idTo (hs : s.Ok) {I J : Submodule (𝓞 X.E) X.E} (h1 : ∀ x, x ∈ J ↔ star x ∈ I) (h2 : I * J = 1) :
    TaylorLogMetric.N1 D (idTo s I) := by
  obtain ⟨t1, t2, t3, -⟩ := GlobalTheory.IdealTransport.transport D X s
  exact ⟨idTo s J, fun x => by rw [t1, t1, h1, symm_conj hs], by rw [← t2, h2, t3]⟩

theorem chi_span (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) {y : X.E} (hy : star y * y = 1) :
    χ (idTo s (Submodule.span (𝓞 X.E) {y})) = ∏ τ, (s.σ₀ (X.emb τ y))⁻¹ := by
  obtain ⟨-, -, -, t4, -⟩ := GlobalTheory.IdealTransport.transport D X s
  letI := D.host.cmStar
  have hst : star (s.iE y) = s.iE (star y) := by
    apply D.host.φ₀.injective
    rw [hs.2]
    change D.host.φ₀ (@NumberField.IsCMField.complexConj D.host.E _ _
      (D.host.isCMField_hostE) _ (s.iE y)) = _
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  have hu : s.iE y ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, mul_comm (s.iE y), and_self, hst, ← map_mul, hy, map_one]
  have := hχ.2 ⟨_, hu⟩
  rw [t4, this, ← s.iT.prod_comp]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hs.1]

theorem chi_pow (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) {I J : Submodule (𝓞 X.E) X.E}
    (h1 : ∀ x, x ∈ J ↔ star x ∈ I) (h2 : I * J = 1) :
    ∃ (h : ℕ) (y : X.E), 0 < h ∧ star y * y = 1 ∧ Submodule.span (𝓞 X.E) {y} = I ^ h ∧
      χ (idTo s I) ^ h = ∏ τ, (s.σ₀ (X.emb τ y))⁻¹ := by
  obtain ⟨c1, h, y, hh, hy, hyI⟩ := GlobalTheory.NormOneIdeal.pow_eq_span_norm_one X.E I J h1 h2
  obtain ⟨-, t2, -⟩ := GlobalTheory.IdealTransport.transport D X s
  have hn : ∀ n : ℕ, TaylorLogMetric.N1 D (idTo s (I ^ n)) := fun n => normOne_idTo hs (c1 n) (by rw [← mul_pow, h2, one_pow])
  have hp : ∀ n : ℕ, χ (idTo s (I ^ n)) = χ (idTo s I) ^ n := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero, Submodule.one_eq_span, chi_span hs hχ (by simp)]
      simp
    | succ n ih => rw [pow_succ, pow_succ, t2, hχ.1 _ _ (hn n) (normOne_idTo hs h1 h2), ih]
  exact ⟨h, y, hh, hy, hyI, by rw [← chi_span hs hχ hy, hyI, hp]⟩

theorem map_mem_Qbar {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ) (x : E) : φ x ∈ TaylorLogMetric.Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom)

theorem chi_det_unit : ∀ (D : D7) (X : Fields) (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ϖ : 𝓞 X.E) (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), X.Ok → s.Ok → TaylorLogMetric.IsChi D χ → ϖ * X.conjO ϖ = (p : 𝓞 X.E) → IsSdLat N → (∀ P : HeightOneSpectrum (𝓞 X.E), ϖ ∈ P.asIdeal → localization₂ P.asIdeal N = stdAt X.E n P) → χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) ∈ TaylorLogMetric.Qbar ∧ ‖TaylorLogMetric.lamC lam (χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)))‖ = 1 := by
  intro D X s χ p _ lam ϖ n N _ hs hχ hϖ hN hS
  obtain ⟨-, -, -, -, -, t6⟩ := GlobalTheory.IdealTransport.transport D X s
  rw [t6]
  obtain ⟨J, h1, h2⟩ := GlobalTheory.DetSelfDual.detLat_mul_conj X.E n N hN
  obtain ⟨h, y, hh, hy, hyI, e⟩ := chi_pow hs hχ h1 h2
  have hv1 : ∀ P : HeightOneSpectrum (𝓞 X.E), ϖ ∈ P.asIdeal → P.valuation X.E y = 1 := by
    intro P hP
    have h3 : MaxV P (detLat N) 1 := by
      have := GlobalTheory.CharVal.DetFrame.maxV_detLat X.E n N P 1 (fun x => by rw [hS P hP]; rfl)
      simpa using this
    have := h3.pow h
    rw [← hyI, one_pow] at this
    exact (maxV_span_singleton y).unique this
  have hv : ∀ P : HeightOneSpectrum (𝓞 X.E), (p : 𝓞 X.E) ∈ P.asIdeal → P.valuation X.E y = 1 := by
    intro P hP
    rw [← hϖ] at hP
    rcases P.isPrime.mem_or_mem hP with hP | hP
    · exact hv1 P hP
    · have := GlobalTheory.CharValCompare.val_star_eq_one (hv1 (conjPrime₂ P) ((mem_conjP P ϖ).2 hP))
      rw [GlobalTheory.CharValCompare.conjP_conjP] at this
      have h4 := congrArg (P.valuation X.E) hy
      rwa [map_mul, this, one_mul, map_one] at h4
  let φ : X.Tau → X.E →+* TaylorLogMetric.Qbar := fun τ =>
    (s.σ₀.comp (X.emb τ)).codRestrict TaylorLogMetric.Qbar (map_mem_Qbar (s.σ₀.comp (X.emb τ)))
  have e' : χ (idTo s (detLat N)) ^ h = ((∏ τ, (φ τ y)⁻¹ : TaylorLogMetric.Qbar) : ℂ) := by
    rw [e]
    simp [φ]
  have hmem : χ (idTo s (detLat N)) ∈ TaylorLogMetric.Qbar := by
    refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow hh ?_)
    rw [e']
    exact mem_algebraicClosure_iff.1 (Subtype.prop _)
  refine ⟨hmem, ?_⟩
  rw [TaylorLogMetric.lamC, dite_eq_left hmem]
  have e2 : (⟨_, hmem⟩ : TaylorLogMetric.Qbar) ^ h = ∏ τ, (φ τ y)⁻¹ := Subtype.ext (by rw [← e']; simp)
  have e3 := congrArg (fun z => ‖lam z‖) e2
  simp only [map_pow, norm_pow, map_prod, norm_prod, map_inv₀, norm_inv] at e3
  rw [Finset.prod_eq_one (fun τ _ => by
    have := norm_eq_one_of_val (lam.comp (φ τ)) hv
    rw [RingHom.comp_apply] at this
    rw [this, inv_one])] at e3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hh.ne').1 e3

end GlobalTheory.MomT.ChiUnit
end
end

section

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.normPrimesImagQuad_short_interval_lower_bound : ∃ A c c' : ℝ, 0 < A ∧ 0 < c ∧ 0 < c' ∧ ∀ (d M : ℕ) (X h : ℝ), d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → 1 ≤ X → Real.log (4 * (d : ℝ) * (M : ℝ) ^ 2) ≤ c * Real.sqrt (Real.log X) → Real.exp (-c * Real.sqrt (Real.log X)) ≤ h → h ≤ 1 → c' * h * X / ((4 * (d : ℝ) * (M : ℝ) ^ 2) ^ A * Real.log X) ≤ ((GlobalTheory.Mem.An.normPrimes d M X (X * (1 + h))).card : ℝ) := by
  first | exact @GlobalTheory.Hk.normPrimes_short_interval_lower | exact GlobalTheory.Hk.normPrimes_short_interval_lower | (intros; apply GlobalTheory.Hk.normPrimes_short_interval_lower <;> assumption)
end

section

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

noncomputable section

namespace GlobalTheory.MomN

open GlobalTheory.MomOne
open scoped ComplexConjugate

theorem latInt_th0_of_split_prime : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 → Nat.Coprime (Ideal.absNorm cc) q → ∀ (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]), Per D.host.d ι δ₀ θ Ω → LatInt ι (Ω / ι δ₀) (lamOf D cc δ) B.th0 := by
  intro D cc δ B hcc _ q _ hq2 hjac hcop ι δ₀ θ Ω hPer
  obtain ⟨hdp, hd16, hOK, -, hlat⟩ := GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts D
  obtain ⟨hTh, -, -, -, -, -, M, hMι, hMOK, hMch⟩ := hPer
  have hcc0 : cc ≠ ⊥ := hcc.1
  obtain ⟨hA, hmem⟩ := hlat cc δ hcc0
  have hmem1 := (hlat ⊤ 1 top_ne_bot).2
  have hqp : q.Prime := Fact.out
  have hN0 : Ideal.absNorm cc ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hcc0
  have hNc : ((Ideal.absNorm cc : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hsd : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (by exact_mod_cast hdp.pos)
  have hAF : Formalism.L2.Th1.F.area B.L = Complex.normSq δ * (Ideal.absNorm cc : ℝ) * Real.sqrt D.host.d / 2 := by
    rw [← hA]; exact B.areaOK.symm
  have hApos : 0 < Formalism.L2.Th1.F.area B.L := Formalism.L2.Th1.F.PeriodAreaSignLemmas.area_pos B.L
  have hδ0 : δ ≠ 0 := by
    rintro rfl
    rw [hAF] at hApos
    simp at hApos
  have hmemL : ∀ x, x ∈ B.L.lattice ↔ x ∈ lamOf D cc δ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.mem_iff B
  obtain ⟨hGd0, hG00, -, hzero, hlaw⟩ :=
    Formalism.L2.Th1.F.th0Basic B.L B.ω₀ B.omega_mem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.half B)
  set N : ℕ := Ideal.absNorm cc with hN
  set G : ℂ → ℂ := fun z => B.th0 (δ * N * z) with hG
  have hGd : Differentiable ℂ G := by
    have : Differentiable ℂ fun z : ℂ => δ * N * z := by fun_prop
    exact hGd0.comp this
  have hG0 : G 0 = 1 := by simp only [hG, mul_zero]; exact hG00
  have hsplit : Split D.host.d q := Or.inr ⟨hq2, hjac⟩

  have hzer : ∀ z, G z = 0 → PrimeTo D.host.d q z := by
    intro z hz
    have h1 : δ * N * z + B.ω₀ / 2 ∈ B.L.lattice := (hzero _).1 hz
    have h2 : δ * ((2 * N : ℕ) * z) ∈ B.L.lattice := by
      have e : δ * ((2 * N : ℕ) * z) = (δ * N * z + B.ω₀ / 2) + (δ * N * z + B.ω₀ / 2) - B.ω₀ := by
        push_cast; ring
      rw [e]
      exact B.L.lattice.sub_mem (B.L.lattice.add_mem h1 h1) B.omega_mem
    obtain ⟨y, -, hy⟩ := (hmem _).1 ((hmemL _).1 h2)
    refine ⟨2 * N, Nat.mul_pos two_pos (Nat.pos_of_ne_zero hN0), Nat.Coprime.mul_left ?_ hcop, ?_⟩
    · exact (Nat.coprime_primes Nat.prime_two hqp).2 (Ne.symm hq2)
    · exact (hOK _).2 ⟨y, mul_left_cancel₀ hδ0 hy⟩

  have hkey : ∀ z w : ℂ, Formalism.L2.Th1.F.herm B.L (δ * N * z) (δ * N * w) = N * h1 D.host.d z w := by
    intro z w
    have hc : δ * conj δ = (Complex.normSq δ : ℂ) := Complex.mul_conj δ
    have hδn : (Complex.normSq δ : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.2 hδ0).ne'
    have hsc : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsd.ne'
    have hA0 : ((Complex.normSq δ * (N : ℝ) * Real.sqrt D.host.d / 2 : ℝ) : ℂ) ≠ 0 := by
      have : 0 < Complex.normSq δ * (N : ℝ) * Real.sqrt D.host.d / 2 := by
        have := Complex.normSq_pos.2 hδ0
        have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
        positivity
      exact_mod_cast this.ne'
    have hs2 : (2 / ((Real.sqrt D.host.d : ℝ) : ℂ)) * ((Real.sqrt D.host.d : ℝ) : ℂ) = 2 := by
      field_simp
    rw [Formalism.L2.Th1.F.herm, hAF, h1, div_eq_iff hA0]
    simp only [map_mul, Complex.conj_natCast]
    push_cast
    linear_combination ((N : ℂ) ^ 2 * z * conj w) * hc - ((N : ℂ) ^ 2 * z * conj w * (Complex.normSq δ : ℂ) / 2) * hs2
  have hlaw' : ∀ x, InOK D.host.d x → ∀ z, G (z + x) * (Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) * Complex.exp (-(Real.pi : ℂ) * h1 D.host.d z x - (Real.pi : ℂ) / 2 * h1 D.host.d x x)) ^ N = G z := by
    intro x hx z
    obtain ⟨o, ho⟩ := (hOK x).1 hx
    have hω : δ * N * x ∈ B.L.lattice := by
      refine (hmemL _).2 ((hmem _).2 ⟨(N : 𝓞 D.host.K) * o, cc.mul_mem_right _ (Ideal.absNorm_mem cc), ?_⟩)
      rw [ho]; push_cast; rw [map_mul, map_natCast]; ring
    have hl := hlaw _ hω (δ * N * z)
    rw [← Formalism.L2.Th1.F.thetaZeroCharacter] at hl
    rw [← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.char_eq (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B) B.omega_mem (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hθ B)
      (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hθ' B) (by omega) _ hω, hkey, hkey] at hl
    have ha : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa B.L D.host.d (δ * N * x) = 1 ∨
        Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa B.L D.host.d (δ * N * x) = -1 := by
      rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.char_eq
        (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B) B.omega_mem
        (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hθ B)
        (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hθ' B) (by omega) _ hω]
      exact Formalism.L2.Th1.H.th0Char_pm B.L B.ω₀ _ B.omega_mem hω
    have hq1 : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.q1 B.L D.host.d (δ * N * x) = N * Complex.normSq x := by
      rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.q1, hkey, h1, Complex.mul_conj]
      have : ((N : ℂ) * (((2 / Real.sqrt D.host.d : ℝ) : ℂ) * ((Complex.normSq x : ℝ) : ℂ))).re
          = N * (2 / Real.sqrt D.host.d) * Complex.normSq x := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.ofReal_re]; ring
      rw [this]; field_simp
    have hapow : Complex.exp ((Real.pi : ℂ) * Complex.I * ((Complex.normSq x : ℝ) : ℂ)) ^ N
        = Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa B.L D.host.d (δ * N * x) := by
      rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa, hq1, ← Complex.exp_nat_mul]
      congr 1; push_cast; ring
    have e1 : G (z + x) = B.th0 (δ * N * z + δ * N * x) := by
      simp only [hG]; congr 1; ring
    have e2 : G z = B.th0 (δ * N * z) := rfl
    rw [e1, e2, Base.th0, hl, mul_pow, hapow, ← Complex.exp_nat_mul]
    set a := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SC.aa B.L D.host.d (δ * N * x)
    have haa : a * a = 1 := by rcases ha with h | h <;> rw [h] <;> norm_num
    have hE : Complex.exp ((Real.pi : ℂ) * (N * h1 D.host.d z x) + (Real.pi : ℂ) * (N * h1 D.host.d x x) / 2)
        * Complex.exp (N * (-(Real.pi : ℂ) * h1 D.host.d z x - (Real.pi : ℂ) / 2 * h1 D.host.d x x)) = 1 := by
      rw [← Complex.exp_add, ← Complex.exp_zero]; congr 1; ring
    linear_combination (Complex.exp ((Real.pi : ℂ) * (N * h1 D.host.d z x) + (Real.pi : ℂ) * (N * h1 D.host.d x x) / 2)
        * Complex.exp (N * (-(Real.pi : ℂ) * h1 D.host.d z x - (Real.pi : ℂ) / 2 * h1 D.host.d x x))
        * Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2) (δ * N * z)) * haa
      + (Formalism.L2.Th1.F.th0 B.L (B.ω₀ / 2) (δ * N * z)) * hE

  have hbd : Bd 1 (hat ι (PowerSeries.C (Ω / ι δ₀) * logS) G) := by
    have := GlobalTheory.T.cpSeries_bounded_theta_level_value_one D.host.d q M (Ω / ι δ₀) θ G N hdp hd16 hsplit hq2 hMOK hMch hTh hGd hG0 hlaw' hzer
    rwa [hMι] at this
  have hmom := GlobalTheory.T.jetsAreBoundedMeasureMoments_of_chart_coeff_bound q ι (Ω / ι δ₀) G hGd hbd
  have hspan : LatInt ι (Ω / ι δ₀) (lamOf D ⊤ 1) G := by
    refine GlobalTheory.T.latticeJetsAreBoundedMoments_of_span_imagQuadratic q ι ℂ D.host.d (Ω / ι δ₀) (lamOf D ⊤ 1) Unit (fun _ => (1 : ℂ)) G hdp hd16 hsplit ?_ ?_
    · intro x hx
      obtain ⟨y, -, hy⟩ := (hmem1 x).1 hx
      refine ⟨1, Nat.coprime_one_left _, fun _ => x, fun _ => (hOK x).2 ⟨y, by rw [hy, one_mul]⟩, ?_⟩
      simp
    · convert hmom using 2
      simp
  have hδN : δ * (N : ℂ) ≠ 0 := mul_ne_zero hδ0 hNc
  have hpull := GlobalTheory.T.latticeJetsAreBoundedMoments_pullback q ι ℂ ℂ (Ω / ι δ₀) (lamOf D ⊤ 1) (lamOf D cc δ)
    ((δ * N)⁻¹ • ContinuousLinearMap.id ℂ ℂ) G hGd.contDiff ?_ hspan
  · convert hpull using 1
    funext z
    simp only [hG, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    congr 1
    field_simp
  · intro x hx
    obtain ⟨y, -, hy⟩ := (hmem x).1 hx
    refine ⟨N, hcop, (hmem1 _).2 ⟨y, trivial, ?_⟩⟩
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, nsmul_eq_mul, hy]
    field_simp

end GlobalTheory.MomN
end
end

section

namespace GlobalTheory.TraceConj

open Formalism.MainNotions.N UpperTheory.V.Af

theorem main : ∀ (Γ k : Type) [Group Γ] [Field k] [CharZero k] (n : ℕ)
    (r r' : Γ →* GL (Fin n) k), IsSSRep r → IsSSRep r' →
    (∀ s, ((r s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace =
      ((r' s : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace) → RepIso r r' := by
  intro Γ k _ _ _ n r r' hr hr' htr
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix r r' hr hr' (fun g => by
    refine GlobalTheory.QuadKernelConj.charpoly_eq_of_trace_pow _ _ fun m => ?_
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
    exact htr (g ^ m))
  exact ⟨P⁻¹, fun s => by rw [hP s, inv_inv]⟩

end GlobalTheory.TraceConj
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClassRestObj

theorem defClassRest : ∀ D : D7, DefClassRest D := by
  intro D W hW hsig
  obtain ⟨⟨θ, hθ⟩, A, hA⟩ := GlobalTheory.DecompCompare.exists_data D W hW hsig
  have hK : KSub D W W.rank 0 θ A = StabFin.SFin D.sp.cm.sig W.gram (L0c D W) :=
    SetLike.coe_injective (StabFin.KSub_eq D W hW hsig θ hθ A hA)
  obtain ⟨-, n, g, hcov, hdisj, -, hsum⟩ := GlobalTheory.DefiniteDecompObj.doubleCosets_mass D W hW hsig θ hθ A hA
  rw [hK] at hcov hdisj hsum
  exact ⟨n, g, hcov, hdisj, hsum⟩

end GlobalTheory.ClassRestObj
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Forms

theorem _root_.GlobalTheory.T.admissiblePeriodZero_of_classPeriodDecomposition_all : ∀ D : D7, (∀ u, Formalism.MainNotions.RT.PeriodPointConditions.PerDec0 D u) → Formalism.MainNotions.WeightDegreeSizes.PeriodClassSumWeyl D := by
  first | exact @GlobalTheory.PerRed.periodClassSumWeyl_of_forall_perDec0 | exact GlobalTheory.PerRed.periodClassSumWeyl_of_forall_perDec0 | (intros; apply GlobalTheory.PerRed.periodClassSumWeyl_of_forall_perDec0 <;> assumption)
end

section

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.volume_ratio_up_positive_line : ∀ D : D7, VolTie D → Conclusion2 D → ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 2 ≤ P + Q → ∀ U : HSpace D.host.E, U.SigOK → (∀ τ, U.sig τ = (P + 1, Q)) → D.vol U / D.vol W = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E (P + Q + 1) := by
  first | exact @GlobalTheory.VolRatioUp.volRatio_up | exact GlobalTheory.VolRatioUp.volRatio_up | (intros; apply GlobalTheory.VolRatioUp.volRatio_up <;> assumption)
end
