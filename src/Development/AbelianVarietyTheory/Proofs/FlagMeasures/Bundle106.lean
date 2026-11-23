module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle002
public import Formalism.RealPlaceAnalysis.Bundle001
public import Mathlib.Analysis.Calculus.FDeriv.Defs
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.KoszulLowersPower
public import Formalism.HermitianLattices.Bundle003
public import Formalism.LocalRingCardinality.Bundle001
public import Formalism.LocalRingCardinality.Bundle003
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop
public import Formalism.CyclotomicNorms.NonsquarefreeBounds.NonsquarefreeMonicBoundHolds
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.CoreDefs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle098
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle097
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousMap
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.MeasureTheory.Integral.PeakFunction
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
import Formalism.FormalDegreeBessel.StatementWR
public import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

section

open Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec
open scoped InnerProductSpace
open MeasureTheory Filter Topology
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.HolExt

theorem differentiable_det (n : ℕ) :
    Differentiable ℂ fun y : Fin n → Fin n → ℂ => (Matrix.of y).det := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  fun_prop

theorem differentiable_adjugate (n : ℕ) (i j : Fin n) :
    Differentiable ℂ fun y : Fin n → Fin n → ℂ => (Matrix.of y).adjugate i j := by
  simp only [Matrix.adjugate_apply]
  have : (fun y : Fin n → Fin n → ℂ => ((Matrix.of y).updateRow j (Pi.single i 1)).det) =
      (fun y : Fin n → Fin n → ℂ => (Matrix.of y).det) ∘ fun y => Function.update y j (Pi.single i 1) := rfl
  rw [this]
  refine (differentiable_det n).comp (differentiable_pi.2 fun a => ?_)
  by_cases h : a = j
  · subst h
    simp
  · simp only [Function.update_of_ne h]
    fun_prop

theorem differentiableOn_inv (n : ℕ) (i j : Fin n) :
    DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => (Matrix.of y)⁻¹ i j) {y | IsUnit (Matrix.of y)} := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  refine ((differentiable_det n).differentiableOn.inv fun y hy => ?_).mul
    (differentiable_adjugate n i j).differentiableOn
  exact ((Matrix.isUnit_iff_isUnit_det _).1 hy).ne_zero

def peak {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : ℝ := 1 + 2 * n + 2 * g.trace.re

theorem peak_coe {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) :
    ((peak g : ℝ) : ℂ) = 1 + 2 * n + g.trace + gᴴ.trace := by
  rw [Matrix.trace_conjTranspose, add_assoc, Complex.star_def, Complex.add_conj, peak]
  push_cast
  ring

theorem peak_pos {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * g = 1) : 0 < peak g := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self (g + 1)).trace_nonneg
  have h2 := (Complex.le_def.1 h).1
  simp only [conjTranspose_add, conjTranspose_one, Matrix.add_mul, Matrix.mul_add, hg, Matrix.mul_one,
    Matrix.one_mul, trace_add, trace_one, trace_conjTranspose, Fintype.card_fin, Complex.add_re,
    Complex.natCast_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at h2
  unfold peak
  linarith

theorem peak_lt {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} (hg : gᴴ * g = 1) (h1 : g ≠ 1) :
    peak g < peak (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have h := (Matrix.posSemidef_conjTranspose_mul_self (g - 1)).trace_nonneg
  have hne : ((g - 1)ᴴ * (g - 1)).trace ≠ 0 := by
    rw [Ne, Matrix.trace_conjTranspose_mul_self_eq_zero_iff, sub_eq_zero]
    exact h1
  have h2 := (Complex.lt_def.1 (lt_of_le_of_ne h hne.symm)).1
  simp only [conjTranspose_sub, conjTranspose_one, Matrix.sub_mul, Matrix.mul_sub, hg, Matrix.mul_one,
    Matrix.one_mul, trace_sub, trace_one, trace_conjTranspose, Fintype.card_fin, Complex.sub_re,
    Complex.natCast_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at h2
  simp only [peak, trace_one, Fintype.card_fin, Complex.natCast_re]
  linarith

def intCLM {K : Type} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K]
    (μ : Measure K) [IsFiniteMeasure μ] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (p : K → B) (hp : Continuous p) : C(K, ℂ) →L[ℂ] B := GlobalTheory.IntegralAgainstMeasure.integralAgainst μ ⟨p, hp⟩

theorem exists_holomorphic_extension : ∀ (n : ℕ) (ε : Fin n → Bool) (B : Type) [NormedRing B] [NormedAlgebra ℂ B] [CompleteSpace B] (π : Matrix (Fin n) (Fin n) ℂ → B), π 1 = 1 → (∀ a ∈ Formalism.REAL.Kset ε, ∀ b ∈ Formalism.REAL.Kset ε, π (a * b) = π a * π b) → ContinuousOn π (Formalism.REAL.Kset ε) → ∃ τ : Matrix (Fin n) (Fin n) ℂ → B, DifferentiableOn ℂ (fun y : Fin n → Fin n → ℂ => τ (Matrix.of y)) {y | IsUnit (Matrix.of y)} ∧ ∀ k ∈ Formalism.REAL.Kset ε, τ k = π k := by
  intro n ε B _ _ _ π h1 hmul hcont
  have hemb : Topology.IsEmbedding (fun k : KG ε => toMK k) :=
    (isClosedEmbeddingMatrix n ε).1.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  haveI : TopologicalSpace.MetrizableSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (TopologicalSpace.MetrizableSpace (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : TopologicalSpace.MetrizableSpace (KG ε) := hemb.metrizableSpace
  haveI : SecondCountableTopology (KG ε) := hemb.secondCountableTopology
  set μ := muK ε
  have hmem : ∀ g : KG ε, toMK g ∈ Kset ε := fun g => g.2
  have hun : ∀ x ∈ Kset ε, xᴴ * x = 1 := fun x hx => Unitary.star_mul_self_of_mem hx.1
  have hu : Continuous fun g : KG ε => toMK g := hemb.continuous
  have hb : Continuous fun g : KG ε => π (toMK g) := hcont.comp_continuous hu hmem
  have hc : Continuous fun g : KG ε => peak (toMK g) := by
    unfold peak
    fun_prop
  have hone : toMK (1 : KG ε) = 1 := rfl
  have hlim := tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn
    (μ := μ) (s := Set.univ) (x₀ := (1 : KG ε)) (c := fun g : KG ε => peak (toMK g))
    (g := fun g : KG ε => π (toMK g)) isCompact_univ hc.continuousOn
    (fun y _ hy => peak_lt (hun _ (hmem y)) fun h => hy (hemb.injective h))
    (fun y _ => (peak_pos (hun _ (hmem y))).le) (peak_pos (hun _ (hmem 1))) (by simp) hb.continuousOn
  simp only [Measure.restrict_univ, hone, h1] at hlim
  obtain ⟨N, hN⟩ := (hlim.eventually (Metric.ball_mem_nhds _ one_pos)).exists
  set c := ∫ g : KG ε, peak (toMK g) ^ N ∂μ
  set A := ∫ g : KG ε, peak (toMK g) ^ N • π (toMK g) ∂μ with hA
  have hint : Integrable (fun g : KG ε => peak (toMK g) ^ N • π (toMK g)) μ :=
    ((hc.pow N).smul hb).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hAu : ∃ A' : B, A * A' = 1 := by
    have e3 : ‖(1 : B) - c⁻¹ • A‖ < 1 := by
      rw [← dist_eq_norm, dist_comm]
      exact hN
    obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one e3
    rw [sub_sub_cancel] at hu
    refine ⟨c⁻¹ • (↑u⁻¹ : B), ?_⟩
    rw [mul_smul_comm, ← smul_mul_assoc, ← hu, Units.mul_inv]
  obtain ⟨A', hA'⟩ := hAu
  have hform : ∀ x ∈ Kset ε, π x * A = ∫ g : KG ε, peak (xᴴ * toMK g) ^ N • π (toMK g) ∂μ := by
    intro x hx
    obtain ⟨z, hz⟩ : x ∈ Set.range (fun g : KG ε => toMK g) := by
      rw [range_toMK]; exact hx
    have hz' : toMK z = x := hz
    have := (ContinuousLinearMap.mul ℂ B (π x)).integral_comp_comm hint
    rw [ContinuousLinearMap.mul_apply'] at this
    rw [hA, ← this,
      ← integral_mul_left_eq_self (fun g : KG ε => peak (xᴴ * toMK g) ^ N • π (toMK g)) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : toMK (z * g) = x * toMK g := by rw [← hz']; rfl
    simp only [e]
    rw [← Matrix.mul_assoc, hun x hx, Matrix.one_mul, hmul _ hx _ (hmem g), ContinuousLinearMap.mul_apply',
      mul_smul_comm]
  let e : Fin n → Fin n → C(KG ε, ℂ) := fun i j => ⟨fun g => toMK g i j, hu.matrix_elem i j⟩
  let F : Matrix (Fin n) (Fin n) ℂ → C(KG ε, ℂ) := fun y =>
    ((1 + 2 * n : ℂ) • (1 : C(KG ε, ℂ)) + ∑ i, ∑ j, y⁻¹ i j • e j i + ∑ i, ∑ j, y j i • star (e j i)) ^ N
  refine ⟨fun y => intCLM μ _ hb (F y) * A', ?_, fun k hk => ?_⟩
  · refine DifferentiableOn.mul_const ((intCLM μ _ hb).differentiable.comp_differentiableOn ?_) _
    refine DifferentiableOn.pow (DifferentiableOn.add (DifferentiableOn.add (differentiableOn_const _) ?_) ?_) N
    · exact DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
        (differentiableOn_inv n i j).smul_const _
    · refine DifferentiableOn.fun_sum fun i _ => DifferentiableOn.fun_sum fun j _ =>
        DifferentiableOn.smul_const ?_ _
      simp only [Matrix.of_apply]
      fun_prop
  · have hinv : k⁻¹ = kᴴ := Matrix.inv_eq_left_inv (hun k hk)
    have hI : intCLM μ _ hb (F k) = π k * A := by
      rw [hform k hk]
      show ∫ g, F k g • π (toMK g) ∂μ = _
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      have : F k g = ((peak (kᴴ * toMK g) ^ N : ℝ) : ℂ) := by
        rw [Complex.ofReal_pow, peak_coe, conjTranspose_mul, conjTranspose_conjTranspose]
        simp [F, e, hinv, Matrix.trace, Matrix.mul_apply, mul_comm]
      simp only [this, Complex.coe_smul]
    show intCLM μ _ hb (F k) * A' = π k
    rw [hI, mul_assoc, hA', mul_one]

end GlobalTheory.HolExt
end
end

section

set_option autoImplicit false

namespace GlobalTheory.InertSquareNorm

open NumberField Module IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S.Lat
open scoped Classical

theorem isSquare_card_of_involution {k : Type} [Field k] [Finite k] (s : k ≃+* k)
    (hs : ∀ x, s (s x) = x) (h1 : ∃ x, s x ≠ x) : IsSquare (Nat.card k) := by
  classical
  have hs2 : s ^ 2 = 1 := by
    ext x
    simp [pow_two, hs]
  have hs1 : s ≠ 1 := by
    obtain ⟨x, hx⟩ := h1
    intro h
    exact hx (by rw [h]; rfl)
  have hord : orderOf s = 2 := orderOf_eq_prime hs2 hs1

  haveI : Finite (k ≃+* k) := Finite.of_injective (fun f : k ≃+* k => (f : k → k))
    (fun a b h => RingEquiv.ext (congrFun h))
  haveI : Fintype (Subgroup.zpowers s) := Fintype.ofFinite _
  haveI : FaithfulSMul (Subgroup.zpowers s) k :=
    ⟨fun {g₁ g₂} h => Subtype.ext (RingEquiv.ext h)⟩
  have hcardG : Fintype.card (Subgroup.zpowers s) = 2 := by
    rw [Fintype.card_eq_nat_card]
    exact (Nat.card_zpowers s).trans hord
  have hfin : Module.finrank (FixedPoints.subfield (Subgroup.zpowers s) k) k = 2 :=
    (FixedPoints.finrank_eq_card (Subgroup.zpowers s) k).trans hcardG
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Fintype (FixedPoints.subfield (Subgroup.zpowers s) k) := Fintype.ofFinite _
  have hk : Fintype.card k = Fintype.card (FixedPoints.subfield (Subgroup.zpowers s) k) ^
      Module.finrank (FixedPoints.subfield (Subgroup.zpowers s) k) k :=
    Module.card_eq_pow_finrank
  refine ⟨Fintype.card (FixedPoints.subfield (Subgroup.zpowers s) k), ?_⟩
  rw [Nat.card_eq_fintype_card, hk, hfin, pow_two]

theorem isSquare_absNorm : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ P : HeightOneSpectrum (𝓞 E), Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal = P.asIdeal → IsSquare (Ideal.absNorm P.asIdeal) := by
  intro E _ _ _ hE P hP
  classical

  let c : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)
  have hc : ∀ x : 𝓞 E, algebraMap (𝓞 E) E (c x) = star (algebraMap (𝓞 E) E x) := fun x => rfl
  have hcc : ∀ x : 𝓞 E, c (c x) = x := fun x => RingOfIntegers.ext (by simp [c])

  have hle : P.asIdeal ≤ P.asIdeal.comap c := by
    intro x hx
    rw [Ideal.mem_comap, ← hP]
    exact Ideal.subset_span ⟨x, hx, hc x⟩
  haveI hmax : P.asIdeal.IsMaximal := P.isMaximal
  letI : Field (𝓞 E ⧸ P.asIdeal) := Ideal.Quotient.field P.asIdeal
  let sb : (𝓞 E ⧸ P.asIdeal) →+* (𝓞 E ⧸ P.asIdeal) := Ideal.quotientMap P.asIdeal c hle
  have hsb_mk : ∀ x : 𝓞 E, sb (Ideal.Quotient.mk P.asIdeal x) = Ideal.Quotient.mk P.asIdeal (c x) :=
    fun x => Ideal.quotientMap_mk
  have hsb : ∀ y, sb (sb y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hsb_mk, hsb_mk, hcc]
  let s : (𝓞 E ⧸ P.asIdeal) ≃+* (𝓞 E ⧸ P.asIdeal) :=
    { sb with invFun := sb, left_inv := hsb, right_inv := hsb }
  have hN : Ideal.absNorm P.asIdeal = Nat.card (𝓞 E ⧸ P.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := by
    apply Nat.finite_of_card_ne_zero
    rw [← hN]
    exact fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)

  obtain ⟨θ, t, ht, hθ⟩ := hE.2.2 P.asIdeal P.isMaximal
  have htc : t = c θ := FaithfulSMul.algebraMap_injective (𝓞 E) E (ht.trans (hc θ).symm)
  rw [hN]
  refine isSquare_card_of_involution s hsb ⟨Ideal.Quotient.mk P.asIdeal θ, fun h => hθ ?_⟩
  have h2 : Ideal.Quotient.mk P.asIdeal θ = Ideal.Quotient.mk P.asIdeal t := by
    rw [htc, ← hsb_mk]
    exact h.symm
  exact Ideal.Quotient.eq.mp h2

end GlobalTheory.InertSquareNorm
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions

theorem _root_.GlobalTheory.T.exists_primitive_vector_norm_neg_hyperbolicPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E], CMData F E → ∀ (S : HSpace E) (Λ : Submodule (𝓞 E) S.V), Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ → (∃ x : 𝓞 E, (x : E) + star (x : E) = 1) → ∀ (e f : S.V) (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 → S.hT e e = 0 → S.hT f f = 0 → S.hT e f = 1 → (∀ x ∈ c, x • e ∈ Λ) → (∀ y ∈ Λ, S.hT f y ∈ c) → ∀ T : ℕ, T ≠ 0 → ∃ z : S.V, z ∈ Submodule.span E {e, f} ∧ z ∈ Λ ∧ S.hT z z = -((T : ℕ) : E) ∧ ∀ γ : E, γ • z ∈ Λ → ∃ o : 𝓞 E, (o : E) = γ := by
  first | exact @GlobalTheory.HypPrimVec.exists_primitive_norm_neg | exact GlobalTheory.HypPrimVec.exists_primitive_norm_neg | (intros; apply GlobalTheory.HypPrimVec.exists_primitive_norm_neg <;> assumption)
end

section

open Formalism.BasicNotions Formalism.MainNotions

theorem GlobalTheory.rowSide_iota_maps_fixedColumns_onto_of_matrices : ∀ (D : D7) (μ : D.what₂.Tup) (n nV dQ d : ℕ) (jA : (Fin n → D.what₂.LL) →ₛₗ[D.what₂.embLL] (RowSide.sharp D).Amb μ) (E : Matrix (Fin n) (Fin n) D.what₂.LL) (V : Matrix (Fin n) (Fin nV) D.what₂.LL) (Pq : Matrix (Fin dQ) (Fin nV) D.what₂.LL) (ι : Matrix (Fin d) (Fin dQ) D.what₂.LL) (eRR : (Fin d → D.what₂.LL) ≃ₗ[D.what₂.LL] (RowSide.sharp D).RR.V), (∀ x, (RowSide.sharp D).eOp μ (jA x) = jA (E.mulVec x)) → (∀ F, E.mulVec (V.mulVec F) = V.mulVec F) → Function.Surjective Pq.mulVec → Function.Surjective ι.mulVec → (∀ F, (RowSide.sharp D).iota μ (jA (V.mulVec F)) = (RowSide.sharp D).jEE (eRR (ι.mulVec (Pq.mulVec F)))) → (D.what₂.V0 μ).map (D.what₂.iota μ) = ⊤ := by
  intro D μ n nV dQ d jA E V Pq ι eRR hE hV hP hι hio
  have hi : (RowSide.sharp D).iota μ = D.what₂.iota μ := by
    unfold RowSide.iota Rows.Data.iota
    rw [PrimeDegreeVariant.sharp_downTo]
    rfl
  have hV0 : (RowSide.sharp D).V0 μ = D.what₂.V0 μ := rfl
  rw [eq_top_iff, ← (RowSide.sharp D).jEE_basis.2, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  obtain ⟨y, hy⟩ := hι (eRR.symm ((RowSide.sharp D).RR.b i))
  obtain ⟨F, hF⟩ := hP y
  have h1 := hio F
  rw [hF, hy, LinearEquiv.apply_symm_apply, hi] at h1
  refine ⟨jA (V.mulVec F), ?_, h1⟩
  rw [← hV0]
  exact ⟨jA (V.mulVec F), by rw [hE, hV]⟩
end

section

open Formalism.BasicNotions Formalism.MainNotions.N Polynomial

namespace GlobalTheory.GoodIdemReal

open GlobalTheory.SeriesSupportTest

theorem star_coeff_of_reverse : ∀ D : D7, (∀ (k : Fin 2) (f : (ZMod (D.host.g k))[X]), f.Monic → f.coeff 0 ≠ 0 →
      ∀ x, star ((D.ntypes.eSer k f).coeff x) = (D.ntypes.eSer k (C (f.coeff 0)⁻¹ * f.reverse)).coeff x) →
    (∀ γ : G0g D.nd, star (D.ntypes.e0.coeff γ) = D.ntypes.e0.coeff γ) := by
  intro D hS γ
  classical
  have : ∀ k, Fact (D.host.g k).Prime := fun k => ⟨D.host.g_prime k⟩
  have : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩

  let ψ : ∀ k : Fin 2, (Fin D.R.r → ZMod (D.host.g k)) → (Fin D.R.r → ZMod (D.host.g k)) :=
    fun k a => if (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 then fun i => (dl (Formalism.CyclotomicNorms.monicOf a)).coeff i else a
  have hlab : ∀ k (a : Fin D.R.r → ZMod (D.host.g k)), (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 →
      (Formalism.CyclotomicNorms.monicOf a).Monic ∧ (Formalism.CyclotomicNorms.monicOf a).natDegree = D.R.r ∧ (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 :=
    fun k a ha => ⟨Formalism.CyclotomicNorms.Sqf.monic_monicOf a, Formalism.CyclotomicNorms.Sqf.natDegree_monicOf a, ha⟩
  have hψm : ∀ k a, (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 → Formalism.CyclotomicNorms.monicOf (ψ k a) = dl (Formalism.CyclotomicNorms.monicOf a) := by
    intro k a ha
    have hd := dl_lab (hlab k a ha)
    simp only [ψ, if_pos ha]
    exact Formalism.CyclotomicNorms.Sqf.monicOf_coeffs _ hd.1 hd.2.1
  have hψ0 : ∀ k a, (Formalism.CyclotomicNorms.monicOf a).coeff 0 = 0 → ψ k a = a := by
    intro k a ha
    simp only [ψ, ha, ne_eq, not_true_eq_false, if_false]
  have hψc : ∀ k a, (Formalism.CyclotomicNorms.monicOf a).coeff 0 ≠ 0 → (Formalism.CyclotomicNorms.monicOf (ψ k a)).coeff 0 ≠ 0 := by
    intro k a ha
    rw [hψm k a ha, (dl_lab (hlab k a ha)).2.2]
    exact inv_ne_zero ha
  have hψinv : ∀ k, Function.Involutive (ψ k) := by
    intro k a
    by_cases ha : (Formalism.CyclotomicNorms.monicOf a).coeff 0 = 0
    · rw [hψ0 k a ha, hψ0 k a ha]
    · funext i
      rw [← Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt (ψ k (ψ k a)) i, hψm k _ (hψc k a ha), hψm k a ha,
        dl_dl (hlab k a ha), Formalism.CyclotomicNorms.Sqf.coeff_monicOf_lt]

  let Φ : Equiv.Perm (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) :=
    Function.Involutive.toPerm (fun a kv => ψ kv.1 (a kv)) (fun a => funext fun kv => hψinv kv.1 (a kv))
  have hΦ : ∀ a kv, Φ a kv = ψ kv.1 (a kv) := fun _ _ => rfl
  let good : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) → Prop :=
    fun a => D.ntypes.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩))
  let T : (∀ kv : (Σ k : Fin 2, D.nd.PlG k), Fin D.R.r → ZMod (D.host.g kv.1)) → ℂ := fun a =>
    if good a then ∏ kv : (Σ k : Fin 2, D.nd.PlG k), (D.ntypes.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (γ kv)
    else 0
  have he : D.ntypes.e0.coeff γ = ∑ᶠ a, T a := rfl

  have hgood : ∀ a, (∀ kv, (Formalism.CyclotomicNorms.monicOf (a kv)).coeff 0 ≠ 0) → good a → good (Φ a) := by
    intro a ha h
    simp only [good] at h ⊢
    unfold NTypes.goodTuple at h ⊢
    intro k
    have hf : (fun v => Formalism.CyclotomicNorms.monicOf (Φ a ⟨k, v⟩)) = fun v => dl (Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) :=
      funext fun v => hψm k _ (ha ⟨k, v⟩)
    have h1 := good_dl _ _ (h k).1
    have h2 := good_dl _ _ (h k).2
    simp only [inv_inv] at h1 h2
    simp only [hf]
    exact ⟨h2, h1⟩

  have hzero : ∀ a, ∀ kv, (Formalism.CyclotomicNorms.monicOf (a kv)).coeff 0 = 0 → T a = 0 := by
    intro a kv h0
    simp only [T]
    split_ifs
    · refine Finset.prod_eq_zero (Finset.mem_univ kv) ?_
      rw [D.ntypes.eSer_zero _ _ (fun h => h.2.2 h0)]
      first
        | rfl
        | simp
    · rfl
  have key : ∀ a, star (T a) = T (Φ a) := by
    intro a
    by_cases hz : ∀ kv, (Formalism.CyclotomicNorms.monicOf (a kv)).coeff 0 ≠ 0
    · have hz' : ∀ kv, (Formalism.CyclotomicNorms.monicOf (Φ a kv)).coeff 0 ≠ 0 := fun kv => hψc _ _ (hz kv)
      have hiff : good (Φ a) ↔ good a := by
        refine ⟨fun h => ?_, hgood a hz⟩
        have := hgood (Φ a) hz' h
        have e : Φ (Φ a) = a := funext fun kv => hψinv kv.1 (a kv)
        rwa [e] at this
      simp only [T, hiff]
      split_ifs
      · rw [star_prod]
        refine Finset.prod_congr rfl fun kv _ => ?_
        rw [hS kv.1 (Formalism.CyclotomicNorms.monicOf (a kv)) (Formalism.CyclotomicNorms.Sqf.monic_monicOf _) (hz kv), hΦ, hψm _ _ (hz kv)]
        rfl
      · exact star_zero _
    · push_neg at hz
      obtain ⟨kv, h0⟩ := hz
      rw [hzero a kv h0, hzero (Φ a) kv (by rw [hΦ, hψ0 _ _ h0]; exact h0), star_zero]
  have hfin : (Function.support T).Finite := Set.toFinite _
  have hstar : star (∑ᶠ a, T a) = ∑ᶠ a, star (T a) := by
    have := map_finsum (starAddEquiv (R := ℂ)) hfin
    simpa only [starAddEquiv_apply] using this
  rw [he, hstar]
  simp_rw [key]
  exact finsum_comp_equiv Φ

end GlobalTheory.GoodIdemReal
end

section


theorem _root_.GlobalTheory.T.capelli_transport_unitary_conj : PI.UnitaryGroupMassFormula.CapelliEig.CapTransport := by
  first | exact @GlobalTheory.capelli_transport_conj | exact GlobalTheory.capelli_transport_conj | (intros; apply GlobalTheory.capelli_transport_conj <;> assumption)
end

section

open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.adelicUnitaryHaar_bi_invariant : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf], (∀ g : I.GA, Measure.map (fun x => g * x) (I.muA μf) = I.muA μf) ∧ (∀ g : I.GA, Measure.map (fun x => x * g) (I.muA μf) = I.muA μf) ∧ Measure.map (fun x : I.GA => x⁻¹) (I.muA μf) = I.muA μf ∧ (∀ g : I.Gf, Measure.map (fun x => x * g) μf = μf) ∧ ∀ U : Set I.GA, IsOpen U → U.Nonempty → 0 < I.muA μf U := by
  first | exact @GlobalTheory.AdelicUnimod.adelic_unimodular | exact GlobalTheory.AdelicUnimod.adelic_unimodular | (intros; apply GlobalTheory.AdelicUnimod.adelic_unimodular <;> assumption)
end

section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.adelicLatticeStabiliser_isCompact_isOpen : ∀ (I : AutInst), IsCompact I.Kset ∧ IsOpen I.Kset ∧ LocallyCompactSpace I.Gf ∧ T2Space I.Gf := by
  first | exact @GlobalTheory.adelicStab_isCompact_isOpen | exact GlobalTheory.adelicStab_isCompact_isOpen | (intros; apply GlobalTheory.adelicStab_isCompact_isOpen <;> assumption)
end

section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.exists_sigmaFinite_haar_finiteAdelicUnitary : ∀ (I : AutInst), ∃ μf : Measure I.Gf, μf.IsHaarMeasure ∧ SigmaFinite μf := by
  first | exact @GlobalTheory.CongTop.exists_haar_sigmaFinite | exact GlobalTheory.CongTop.exists_haar_sigmaFinite | (intros; apply GlobalTheory.CongTop.exists_haar_sigmaFinite <;> assumption)
end

section

open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace

theorem _root_.GlobalTheory.T.secondCountable_finiteAdelicUnitaryPoints : ∀ (I : AutInst), SecondCountableTopology I.Gf := by
  first | exact @GlobalTheory.CongTop.secondCountable_finiteAdelicPoints | exact GlobalTheory.CongTop.secondCountable_finiteAdelicPoints | (intros; apply GlobalTheory.CongTop.secondCountable_finiteAdelicPoints <;> assumption)
end
