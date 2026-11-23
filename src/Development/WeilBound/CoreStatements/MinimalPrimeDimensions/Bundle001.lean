module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1161
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.ContinuousAeval
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.MemOfForallValuationSubring
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.Polynomial.Basic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle027
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle064
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle026
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.BesselHermitianTheta.NoncompactGapAtLeastRange
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle001
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle001

@[expose] public section

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace ChowFormHeightComparison₂.SmallGenerators

private lemma isPair_and_isPair_of_isTriple {K : Type} [Field K] (S : Subring K) (M : Ideal S)
    [M.IsMaximal] : ∃ B : ValuationSubring K, (∀ s ∈ S, s ∈ B) ∧ ∀ s : S, s ∈ M → B.valuation (s : K) < 1 := by
  obtain ⟨B, hB⟩ := (LocalSubring.ofPrime S M).exists_le_valuationSubring
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hB
  refine ⟨B, fun s hs => hle (LocalSubring.le_ofPrime S M hs), fun s hs => ?_⟩
  have ht : algebraMap S (LocalSubring.ofPrime S M).toSubring s ∈
      IsLocalRing.maximalIdeal (LocalSubring.ofPrime S M).toSubring :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ M s).mpr hs
  have hB' : Subring.inclusion hle (algebraMap S (LocalSubring.ofPrime S M).toSubring s) ∈
      IsLocalRing.maximalIdeal B := fun hu => ht (isUnit_of_map_unit (Subring.inclusion hle) _ hu)
  exact (B.valuation_lt_one_iff _).mp hB'

private lemma exists_trace_zero_generator_of_isCMExt {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K] (y : K) (hy : y ≠ 0)
    (hint : ¬ IsIntegral A y⁻¹) :
    Ideal.map (algebraMap A (Algebra.adjoin A {y})) (IsLocalRing.maximalIdeal A) ⊔
      Ideal.span {(⟨y, Algebra.self_mem_adjoin_singleton A y⟩ : Algebra.adjoin A {y})} ≠ ⊤ := by
  intro htop
  let φ : Polynomial A →ₐ[A] Algebra.adjoin A {y} := Polynomial.aeval ⟨y, Algebra.self_mem_adjoin_singleton A y⟩
  have hφy : ∀ q : Polynomial A, ((φ q : Algebra.adjoin A {y}) : K) = Polynomial.aeval y q := fun q =>
    (Polynomial.aeval_algHom_apply (Algebra.adjoin A {y}).val _ q).symm
  have hφ : Function.Surjective φ := by
    rintro ⟨s, hs⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hs
    obtain ⟨q, rfl⟩ := hs
    exact ⟨q, Subtype.ext (hφy q)⟩
  let T : Ideal (Polynomial A) := Ideal.comap Polynomial.constantCoeff (IsLocalRing.maximalIdeal A)
  have hJT : Ideal.map (algebraMap A (Algebra.adjoin A {y})) (IsLocalRing.maximalIdeal A) ⊔
      Ideal.span {(⟨y, Algebra.self_mem_adjoin_singleton A y⟩ : Algebra.adjoin A {y})} ≤ Ideal.map φ T := by
    refine sup_le (Ideal.map_le_iff_le_comap.mpr fun a ha => ?_) (Ideal.span_le.mpr ?_)
    · rw [Ideal.mem_comap, ← Polynomial.aeval_C]
      exact Ideal.mem_map_of_mem φ (by simpa [T] using ha)
    · rw [Set.singleton_subset_iff, SetLike.mem_coe]
      have hX : φ Polynomial.X = ⟨y, Algebra.self_mem_adjoin_singleton A y⟩ := Polynomial.aeval_X _
      rw [← hX]
      exact Ideal.mem_map_of_mem φ (by simp [T])
  have hT : Ideal.map φ T = ⊤ := top_le_iff.mp (htop ▸ hJT)
  have hc := Ideal.comap_map_of_surjective φ hφ T
  rw [hT, Ideal.comap_top] at hc
  have h1 : (1 : Polynomial A) ∈ T ⊔ Ideal.comap φ ⊥ := hc ▸ Submodule.mem_top
  obtain ⟨t, ht, k, hk, htk⟩ := Submodule.mem_sup.mp h1
  have hk0 : Polynomial.aeval y k = 0 := by
    rw [← hφy, (Ideal.mem_bot.mp (Ideal.mem_comap.mp hk)), ZeroMemClass.coe_zero]
  have hu : IsUnit (k.coeff 0) := by
    have hkt : k = 1 - t := eq_sub_of_add_eq' htk
    have ht' : t.coeff 0 ∈ IsLocalRing.maximalIdeal A := by
      rw [← Polynomial.constantCoeff_apply]
      exact ht
    rw [hkt, Polynomial.coeff_sub, Polynomial.coeff_one_zero]
    exact IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ ht'
  apply hint
  have : Invertible y := invertibleOfNonzero hy
  have hrev : Polynomial.eval₂ (algebraMap A K) (⅟y) k.reverse = 0 := by
    have := Polynomial.eval₂_reverse_mul_pow (algebraMap A K) y k
    rw [show Polynomial.eval₂ (algebraMap A K) y k = Polynomial.aeval y k from rfl, hk0] at this
    exact (mul_eq_zero.mp this).resolve_right (pow_ne_zero _ hy)
  have hlc : k.reverse.leadingCoeff = k.coeff 0 := by
    rw [Polynomial.reverse_leadingCoeff, Polynomial.trailingCoeff,
      Polynomial.natTrailingDegree_eq_zero.mpr (Or.inr hu.ne_zero)]
  refine ⟨Polynomial.C (↑hu.unit⁻¹ : A) * k.reverse, ?_, ?_⟩
  · refine Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one ?_
    rw [hlc]
    exact hu.unit.inv_mul
  · rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, ← invOf_eq_inv, hrev, mul_zero]

theorem exists_val {X : Scheme.{0}} [IsIntegral X] {x : X} (hn : IsIntegrallyClosed (X.presheaf.stalk x))
    {h : X.functionField} (hh : ¬ RegAt x h) :
    ∃ O : ValuationSubring X.functionField, (∀ g, RegAt x g → O.valuation g ≤ 1) ∧
      (∀ g, ZeroAt x g → O.valuation g < 1) ∧ ¬ O.valuation h ≤ 1 := by
  have h0 : h ≠ 0 := by
    rintro rfl
    exact hh ⟨0, map_zero _⟩
  have hint : ¬ IsIntegral (X.presheaf.stalk x) (h⁻¹)⁻¹ := by
    rw [inv_inv]
    intro hi
    exact hh (IsIntegrallyClosed.isIntegral_iff.mp hi)
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ (exists_trace_zero_generator_of_isCMExt h⁻¹ (inv_ne_zero h0) hint)
  let M' : Ideal (Algebra.adjoin (X.presheaf.stalk x) {h⁻¹}).toSubring := M
  have : M'.IsMaximal := hM
  obtain ⟨B, hSB, hMB⟩ := isPair_and_isPair_of_isTriple (Algebra.adjoin (X.presheaf.stalk x) {h⁻¹}).toSubring M'
  refine ⟨B, ?_, ?_, ?_⟩
  · rintro g ⟨a, rfl⟩
    exact (B.valuation_le_one_iff _).mpr (hSB _ (Subalgebra.algebraMap_mem _ a))
  · rintro g ⟨a, ha, rfl⟩
    exact hMB (algebraMap (X.presheaf.stalk x) (Algebra.adjoin (X.presheaf.stalk x) {h⁻¹}) a) (hJM (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)))
  · intro hle
    have hy := hMB ⟨h⁻¹, Algebra.self_mem_adjoin_singleton _ _⟩
      (hJM (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    have hne : B.valuation h ≠ 0 := (Valuation.ne_zero_iff _).mpr h0
    have h1 : (1 : B.ValueGroup) ≤ (B.valuation h)⁻¹ :=
      calc (1 : B.ValueGroup) = B.valuation h * (B.valuation h)⁻¹ := (mul_inv_cancel₀ hne).symm
        _ ≤ 1 * (B.valuation h)⁻¹ := by gcongr
        _ = (B.valuation h)⁻¹ := one_mul _
    rw [map_inv₀] at hy
    exact absurd hy (not_lt.mpr h1)

private lemma isHecke_div_and_resEtaPow_div {X : Scheme.{0}} [IsIntegral X] (U : X.Opens) (h : genericPoint X ∈ U)
    (s : X.presheaf.obj (Opposite.op U)) (x : X) (hx : x ∈ U) :
    algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx s) = fnOf U h s := by
  show (X.presheaf.stalkSpecializes _).hom (X.presheaf.germ U x hx s) = _
  rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  rfl

theorem zeroAt_const {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) (x : X) {a : k}
    (ha : a ∈ (p x).asIdeal) :
    ZeroAt x (fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤ a)) := by
  refine ⟨X.presheaf.germ ⊤ x (TopologicalSpace.Opens.mem_top x) (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤ a), ?_,
    isHecke_div_and_resEtaPow_div ⊤ _ _ x _⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  have hx : x ∈ X.basicOpen (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤ a) := (Scheme.mem_basicOpen ..).mpr hu
  unfold ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX at hx
  rw [RingHom.comp_apply] at hx
  have e := Scheme.basicOpen_appLE p ⊤ ⊤ (by simp) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv a)
  rw [basicOpen_eq_of_affine] at e
  have hx' := Eq.mp (congrArg (x ∈ ·) e) hx
  exact (PrimeSpectrum.mem_basicOpen _ _).mp hx'.2 ha

theorem reg_of_val {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] {Nm : (K →+* ℂ) → V → ℝ} {W : Submodule (𝓞 K) V}
    {ev : V →ₗ[K] Ω} {d : ℕ} {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp (𝓞 K)} {L : GlobalTheory.HermLB p}
    {ψ : Ω →+* X.functionField} {s : W → L.B.Sec} (hM : GlobalTheory.ImageModel.IsModelOf Nm W ev d p L ψ s) (b : Ω) (τ : ℕ)
    (hb : ∀ (la : HeightOneSpectrum (𝓞 K)) (O : ValuationSubring X.functionField),
      (∀ a : 𝓞 K, O.valuation (ψ (algebraMap K Ω (a : K))) ≤ 1) →
      (∀ a ∈ la.asIdeal, O.valuation (ψ (algebraMap K Ω (a : K))) < 1) →
      ∃ l ∈ W, O.valuation (ψ b) ≤ O.valuation (ψ (ev l)) ^ τ)
    (w : W) (hw : ev w ≠ 0) (k : L.B.ι) (x : X) (hx : x ∈ L.B.U k) (hp : (p x).asIdeal ≠ ⊥) :
    RegAt x (ψ b * (ψ (ev w))⁻¹ ^ τ * fnOf (L.B.U k) (gen_mem hx) ((s w).f k) ^ τ) := by
  by_contra hreg
  obtain ⟨O, hO1, hO2, hO3⟩ := exists_val (hM.normal x).2 hreg
  have hbase : ∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) =
      fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤ a) := hM.base
  have h1 : ∀ a : 𝓞 K, O.valuation (ψ (algebraMap K Ω (a : K))) ≤ 1 := fun a => by
    rw [hbase a]
    exact hO1 _ ⟨_, isHecke_div_and_resEtaPow_div ⊤ _ _ x trivial⟩
  obtain ⟨l, hlW, hl⟩ := hb ⟨(p x).asIdeal, (p x).isPrime, hp⟩ O h1 (fun a ha => by
    rw [hbase a]
    exact hO2 _ (zeroAt_const p x ha))
  apply hO3
  have hc : O.valuation (ψ (ev w)) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact (map_ne_zero ψ).mpr hw
  have hFl : O.valuation (fnOf (L.B.U k) (gen_mem hx) ((s ⟨l, hlW⟩).f k)) ≤ 1 :=
    hO1 _ ⟨_, isHecke_div_and_resEtaPow_div _ _ _ x hx⟩
  have hv := congrArg O.valuation (hM.ratio w ⟨l, hlW⟩ k (gen_mem hx))
  rw [map_mul, map_mul] at hv
  rw [map_mul, map_mul, map_pow, map_pow, map_inv₀]
  calc O.valuation (ψ b) * (O.valuation (ψ (ev w)))⁻¹ ^ τ *
        O.valuation (fnOf (L.B.U k) (gen_mem hx) ((s w).f k)) ^ τ
      ≤ O.valuation (ψ (ev l)) ^ τ * (O.valuation (ψ (ev w)))⁻¹ ^ τ *
        O.valuation (fnOf (L.B.U k) (gen_mem hx) ((s w).f k)) ^ τ := by
        gcongr
    _ = (O.valuation (ψ (ev l)) * O.valuation (fnOf (L.B.U k) (gen_mem hx) ((s w).f k)) *
        (O.valuation (ψ (ev w)))⁻¹) ^ τ := by
        rw [mul_pow, mul_pow, mul_right_comm]
    _ = O.valuation (fnOf (L.B.U k) (gen_mem hx) ((s ⟨l, hlW⟩).f k)) ^ τ := by
        rw [← hv, mul_comm (O.valuation (ψ (ev w))), mul_inv_cancel_right₀ hc]
    _ ≤ 1 := pow_le_one' hFl τ

end ChowFormHeightComparison₂.SmallGenerators

end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace ChowFormHeightComparison₂.GenericDenseBound

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

theorem finiteType_sections {K : Type} [Field K] [NumberField K] {X : Scheme.{0}} {p : X ⟶ Sp (𝓞 K)}
    (hp : IsProjOver p) {W : X.Opens} (hW : IsAffineOpen W) : Algebra.FiniteType ℤ Γ(X, W) := by
  have : IsProper p := by
    obtain ⟨N, j, _, e⟩ := hp
    have := isProper_str (𝓞 K) N
    rw [← e]
    infer_instance
  have hft : (algX p W).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩
      (show W ≤ p ⁻¹ᵁ ⊤ from le_top)).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of (𝓞 K))).symm.commRingCatIsoToRingEquiv.surjective)
  have h0 : (algebraMap ℤ (𝓞 K)).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  have h1 := hft.comp h0
  rw [Subsingleton.elim ((algX p W).comp (algebraMap ℤ (𝓞 K))) (algebraMap ℤ Γ(X, W))] at h1
  exact RingHom.finiteType_algebraMap.1 h1

theorem final_ineq {a Q t : ℝ} {τ : ℕ} (hQ : 0 ≤ Q) (h : a ≤ Real.exp (2 * (τ : ℝ) * t) * Q ^ τ) :
    a * Real.exp (-((τ : ℝ) * Real.log Q)) ≤ Real.exp (2 * (τ : ℝ) * t) := by
  rcases hQ.eq_or_lt with h0 | h0
  · subst h0
    rw [Real.log_zero, mul_zero, neg_zero, Real.exp_zero, mul_one]
    exact h.trans (mul_le_of_le_one_right (Real.exp_pos _).le (pow_le_one₀ le_rfl zero_le_one))
  · rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log h0, mul_inv_le_iff₀ (pow_pos h0 τ)]
    exact h

theorem norm_le_of_emb {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] {Nm : (K →+* ℂ) → V → ℝ} {W : Submodule (𝓞 K) V}
    {ev : V →ₗ[K] Ω} {d : ℕ} {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp (𝓞 K)} {L : GlobalTheory.HermLB p}
    {ψ : Ω →+* X.functionField} {s : W → L.B.Sec} (hM : GlobalTheory.ImageModel.IsModelOf Nm W ev d p L ψ s) (β : Ω) (τ : ℕ)
    (t : ℝ)
    (hb : ∀ (N m : ℕ) (b : Module.Basis (Fin N) K V) (g : Matrix (Fin N) (Fin m) K)
      (A : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ), IsFrame Nm W b g A → ∀ (σ : K →+* ℂ) (ρ : Ω →+* ℂ),
      ρ.comp (algebraMap K Ω) = σ → ‖ρ β‖ ≤ Real.exp (τ * t) * GlobalTheory.Adelic.archSize (A σ) (fun i => ρ (ev (b i))) ^ τ)
    (w : W) (hw : ev w ≠ 0) (σ : 𝓞 K →+* ℂ) (y : GlobalTheory.CxPts p σ) (k : L.B.ι) (hy : y ∈ ptsIn p σ (L.B.U k))
    (hr : RegAt (under y) (ψ β * (ψ (ev w))⁻¹ ^ τ * fnOf (L.B.U k) (gen_mem (mem_ptsIn.1 hy)) ((s w).f k) ^ τ)) :
    ‖ratVal (ψ β * (ψ (ev w))⁻¹ ^ τ * fnOf (L.B.U k) (gen_mem (mem_ptsIn.1 hy)) ((s w).f k) ^ τ) y‖ ^ 2 *
      Real.exp (-((τ : ℝ) * (L.φ σ).φ k y)) ≤ Real.exp (2 * (τ : ℝ) * t) := by
  obtain ⟨N, n, b, g, A, c, gw, hF, -, hbc, hφ⟩ := hM.fs
  obtain ⟨U', hU', a, ha⟩ := hr.exists_fnOf
  have hyk : under y ∈ L.B.U k := mem_ptsIn.1 hy
  obtain ⟨O, hO, hyO, hle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens (memInf hU' hyk)
  have hO' : IsAffineOpen O := hO
  have hle1 : O ≤ U' := hle.trans inf_le_left
  have hle2 : O ≤ L.B.U k := hle.trans inf_le_right
  have hyO' : y ∈ ptsIn p σ O := mem_ptsIn.2 hyO
  have hg : genericPoint X ∈ O := gen_mem hyO
  have : Nonempty O := ⟨⟨_, hyO⟩⟩
  have := finiteType_sections hM.arith.isProjOver hO'
  have := functionField_isFractionRing_of_isAffineOpen X O hO'
  have halg : ∀ z : Γ(X, O), algebraMap Γ(X, O) X.functionField z = fnOf O hg z := fun _ => rfl
  let r : Option (Fin n) → Γ(X, O) := fun j => j.elim (resG X hle1 a) fun j => resG X hle2 ((s (gw j)).f k)
  have hψw : ψ (ev w) ≠ 0 := (map_ne_zero ψ).2 hw
  set u := fnOf (L.B.U k) (gen_mem (mem_ptsIn.1 hy)) ((s w).f k) with hu
  obtain ⟨σ', hσ', hineq⟩ := bound_of_emb (Ω := X.functionField) (ψ.comp (algebraMap K Ω)) (algX p O)
    (fun z => by
      rw [halg, RingHom.comp_apply, hM.base]
      exact (RingHom.congr_fun (fnOf_comp_algX p O hg) z).trans rfl)
    (evHom hyO') r (fun _ v => ‖v none‖ ^ 2)
    (fun σ' v => Real.exp (2 * (τ : ℝ) * t) * (∑ a, ‖∑ j, (∑ m, σ' (c j m) * A σ' m a) * v (some j)‖ ^ 2) ^ τ)
    (fun _ => by fun_prop) (fun _ => by fun_prop)
    (fun ρ => by
      have h1 := hb N n b g A hF _ (ρ.comp ψ) rfl
      have e0 : (ρ.comp ψ).comp (algebraMap K Ω) = ρ.comp (ψ.comp (algebraMap K Ω)) := rfl
      rw [e0] at h1
      generalize hσ' : ρ.comp (ψ.comp (algebraMap K Ω)) = σ' at h1 ⊢
      have hσa : ∀ z, σ' z = ρ (ψ (algebraMap K Ω z)) := fun z => by rw [← hσ']; rfl
      set lam := ρ ((ψ (ev w))⁻¹ * u) with hlam
      have e1 : ρ (algebraMap Γ(X, O) X.functionField (r none)) = ρ (ψ β) * lam ^ τ := by
        rw [halg]
        show ρ (fnOf O hg (resG X hle1 a)) = _
        rw [fnOf_resG, ha, hlam, ← map_pow ρ, ← map_mul ρ, mul_pow, mul_assoc]
      have e2 : ∀ j, ρ (algebraMap Γ(X, O) X.functionField (r (some j))) = ρ (ψ (ev (gw j))) * lam := fun j => by
        rw [halg]
        show ρ (fnOf O hg (resG X hle2 ((s (gw j)).f k))) = _
        rw [fnOf_resG, hlam, ← map_mul ρ]
        congr 1
        have := hM.ratio w (gw j) k (hle2 hg)
        rw [← mul_assoc, mul_comm (ψ (ev (gw j))), mul_assoc, eq_inv_mul_iff_mul_eq₀ hψw]
        exact this
      have e3 : ∀ m, ρ (ψ (ev (b m))) = ∑ j, σ' (c j m) * ρ (ψ (ev (gw j))) := fun m => by
        rw [hbc m]

        simp only [map_sum, map_smul, Algebra.smul_def, map_mul, hσa]
      have e4 : ∀ a, ∑ j, (∑ m, σ' (c j m) * A σ' m a) * (ρ (ψ (ev (gw j))) * lam) =
          lam * ∑ m, A σ' m a * ρ (ψ (ev (b m))) := fun a => by
        simp only [e3, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      simp only [e1, e2, e4, norm_mul, mul_pow, norm_pow, ← Finset.mul_sum]
      have hS : 0 ≤ ∑ a, ‖∑ m, A σ' m a * ρ (ψ (ev (b m)))‖ ^ 2 := by positivity
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have e5 : (Real.exp (τ * t) * GlobalTheory.Adelic.archSize (A σ') (fun i => (ρ.comp ψ) (ev (b i))) ^ τ) ^ 2 =
          Real.exp (2 * (τ : ℝ) * t) * (∑ a, ‖∑ m, A σ' m a * ρ (ψ (ev (b m)))‖ ^ 2) ^ τ := by
        rw [mul_pow, ← Real.exp_nat_mul, ← pow_mul, mul_comm τ 2, pow_mul]
        unfold GlobalTheory.Adelic.archSize
        simp only [RingHom.comp_apply]
        rw [Real.sq_sqrt hS]
        congr 2
        push_cast
        ring
      rw [e5] at h2
      have h3 := mul_le_mul_of_nonneg_right h2 (show 0 ≤ (‖lam‖ ^ τ) ^ 2 by positivity)
      refine h3.trans_eq ?_
      ring)
  have hσ : σ'.comp (algebraMap (𝓞 K) K) = σ := hσ'.trans (RingHom.ext fun z =>
    (ev_eq hyO' _).symm.trans (ev_algX hyO' z))
  subst hσ
  rw [hφ σ' k y, ← ha, ratVal_fnOf (mem_ptsIn.2 hU')]
  refine final_ineq (by positivity) ?_
  have f1 : evHom hyO' (r none) = GlobalTheory.CxPts.ev p _ U' a y := (ev_eq hyO' _).symm.trans (ev_res hle1 hyO' a)
  have f2 : ∀ j, evHom hyO' (r (some j)) = valR y.1 (L.B.U k) ((s (gw j)).f k) := fun j =>
    (ev_eq hyO' _).symm.trans (ev_res hle2 hyO' _)
  simp only [f1, f2] at hineq
  exact hineq

end ChowFormHeightComparison₂.GenericDenseBound
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace ChowFormHeightComparison₂.RegularPointExistence

theorem reg_of_val {K V Ω : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] {Nm : (K →+* ℂ) → V → ℝ} {W : Submodule (𝓞 K) V}
    {ev : V →ₗ[K] Ω} {d : ℕ} {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp (𝓞 K)} {L : GlobalTheory.HermLB p}
    {ψ : Ω →+* X.functionField} {s : W → L.B.Sec} (hM : GlobalTheory.ImageModel.IsModelOf Nm W ev d p L ψ s) (τ : ℕ) (b : Ω)
    (hb : ∀ (la : HeightOneSpectrum (𝓞 K)) (O : ValuationSubring Ω),
      (∀ a : 𝓞 K, O.valuation (algebraMap K Ω (a : K)) ≤ 1) →
      (∀ a ∈ la.asIdeal, O.valuation (algebraMap K Ω (a : K)) < 1) →
      ∃ l ∈ W, O.valuation b ≤ O.valuation (ev l) ^ τ)
    (w : W) (hw : ev w ≠ 0) (k : L.B.ι) (x : X) (hx : x ∈ L.B.U k) :
    GlobalTheory.Cartier.RegAt x (ψ b * (ψ (ev w))⁻¹ ^ τ * fnOf (L.B.U k) (gen_mem hx) ((s w).f k) ^ τ) := by
  haveI := (hM.normal x).2
  refine mem_of_forall_valuationSubring fun O hO => ?_
  have hreg : ∀ g, GlobalTheory.Cartier.RegAt x g → g ∈ O := fun g ⟨a, ha⟩ => ha ▸ hO a
  obtain ⟨la, O', hle, h1, h2⟩ := exists_refine (K := K) (O.comap ψ) fun a => by
    rw [ValuationSubring.mem_comap, hM.base a]
    exact hreg _ (regAt_fnOf (TopologicalSpace.Opens.mem_top x) _ _)
  obtain ⟨l, hl, hbl⟩ := hb la O' h1 h2
  rw [← map_pow, ValuationSubring.valuation_le_iff] at hbl
  obtain ⟨c, hc⟩ := hbl
  have hcO : ψ (c : Ω) ∈ O := (ValuationSubring.mem_comap).1 (hle c.2)
  have hr := hM.ratio ⟨l, hl⟩ w k (gen_mem hx)
  have hψw : ψ (ev w) ≠ 0 := (map_ne_zero ψ).2 hw
  have e1 : ψ (ev l) * (ψ (ev w))⁻¹ * fnOf (L.B.U k) (gen_mem hx) ((s w).f k) =
      fnOf (L.B.U k) (gen_mem hx) ((s ⟨l, hl⟩).f k) := by
    rw [mul_right_comm]
    erw [hr]
    rw [mul_right_comm, mul_inv_cancel₀ hψw, one_mul]
  have e2 : ψ b * (ψ (ev w))⁻¹ ^ τ * fnOf (L.B.U k) (gen_mem hx) ((s w).f k) ^ τ =
      ψ (c : Ω) * fnOf (L.B.U k) (gen_mem hx) ((s ⟨l, hl⟩).f k) ^ τ := by
    rw [← e1, ← hc, map_mul, map_pow]
    ring
  rw [e2]
  exact O.mul_mem _ _ hcO (O.pow_mem (hreg _ (regAt_fnOf hx _ _)) τ)

end ChowFormHeightComparison₂.RegularPointExistence
end
