module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFixedIff
public import Formalism.LocalRingCardinality.AdicCompletionLocal.InstIsAdicCompleteOCSpanSingletonSetCast
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle404
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle289
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActQdRPeriodTEqCyclotomicBottom
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle003
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle002
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle016
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle158
import Mathlib.Algebra.Module.StablyFree.Basic
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle413
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily

@[expose] public section

section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.TraceCompl

theorem le_one_iff_of_mul_eq_one {Γ : Type} [LinearOrderedCommGroupWithZero Γ] {a b : Γ} (hab : a * b = 1)
    (hb : b ≤ 1) : a ≤ 1 ↔ b = 1 := by
  constructor
  · intro ha
    by_contra hb1
    have hlt : b < 1 := lt_of_le_of_ne hb hb1
    have : (1 : Γ) < 1 := calc
      (1 : Γ) = a * b := hab.symm
      _ ≤ 1 * b := by gcongr
      _ = b := one_mul b
      _ < 1 := hlt
    exact lt_irrefl _ this
  · rintro rfl
    rw [mul_one] at hab
    exact hab.le

variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]

theorem algebraMap_int_mem (A : ValuationSubring Ω) (x : 𝓞 K) : algebraMap K Ω x ∈ A := by
  have h1 : IsIntegral ℤ (algebraMap K Ω x) := x.2.map (algebraMap K Ω).toIntAlgHom
  have h2 : IsIntegral A (algebraMap K Ω x) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact hy ▸ y.2

theorem algebraMap_mem_iff {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v)
    (x : K) : algebraMap K Ω x ∈ A ↔ v.valuation K x ≤ 1 := by
  have key : ∀ n : 𝓞 K, A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) ≤ 1 ∧
      v.valuation K (algebraMap (𝓞 K) K n) ≤ 1 ∧
      (A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) = 1 ↔
        v.valuation K (algebraMap (𝓞 K) K n) = 1) := by
    intro n
    have h1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) ≤ 1 :=
      (A.valuation_le_one_iff _).2 (algebraMap_int_mem A n)
    have h2 : v.valuation K (algebraMap (𝓞 K) K n) ≤ 1 := v.valuation_le_one n
    have h3 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) < 1 ↔ n ∈ v.asIdeal := h n
    have h4 : v.valuation K (algebraMap (𝓞 K) K n) < 1 ↔ n ∈ v.asIdeal := v.valuation_lt_one_iff_mem n
    refine ⟨h1, h2, ?_⟩
    have e1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K n)) = 1 ↔ n ∉ v.asIdeal := by
      rw [← h3, not_lt]; exact ⟨fun e => e.ge, fun e => le_antisymm h1 e⟩
    have e2 : v.valuation K (algebraMap (𝓞 K) K n) = 1 ↔ n ∉ v.asIdeal := by
      rw [← h4, not_lt]; exact ⟨fun e => e.ge, fun e => le_antisymm h2 e⟩
    exact e1.trans e2.symm
  obtain ⟨n, d, hd | hd⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := K) x
  · have hd1 : v.valuation K (algebraMap (𝓞 K) K d) = 1 := by
      have := (v.valuation_lt_one_iff_mem (K := K) (d : 𝓞 K)).not.2 d.2
      exact le_antisymm (v.valuation_le_one _) (not_lt.1 this)
    have hA1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K d)) = 1 := ((key d).2.2).2 hd1
    have e1 := congrArg (fun y => A.valuation (algebraMap K Ω y)) hd
    have e2 := congrArg (v.valuation K) hd
    simp only [map_mul, hA1, hd1, mul_one] at e1 e2
    rw [← A.valuation_le_one_iff, e1, e2]
    exact iff_of_true (key n).1 (key n).2.1
  · have hd1 : v.valuation K (algebraMap (𝓞 K) K d) = 1 := by
      have := (v.valuation_lt_one_iff_mem (K := K) (d : 𝓞 K)).not.2 d.2
      exact le_antisymm (v.valuation_le_one _) (not_lt.1 this)
    have hA1 : A.valuation (algebraMap K Ω (algebraMap (𝓞 K) K d)) = 1 := ((key d).2.2).2 hd1
    have e1 := congrArg (fun y => A.valuation (algebraMap K Ω y)) hd
    have e2 := congrArg (v.valuation K) hd
    simp only [map_mul, hA1, hd1] at e1 e2
    rw [← A.valuation_le_one_iff, le_one_iff_of_mul_eq_one e1 (key n).1,
      le_one_iff_of_mul_eq_one e2 (key n).2.1]
    exact (key n).2.2

end GlobalTheory.LocLanglands.TraceCompl

namespace GlobalTheory.LocLanglands.TraceCompl

variable {K L Ω : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]

theorem trace_mem {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} (h : IsPlaceOver A v)
    (hL : IsLocalExt L h) (z : L) (hz : algebraMap L Ω z ∈ A) :
    algebraMap K Ω (Algebra.trace K L z) ∈ A := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  rw [trace_eq_sum_embeddings Ω]
  refine sum_mem fun s _ => ?_
  obtain ⟨τ, hτ⟩ := hL (AlgEquiv.ofBijective (s.liftNormal Ω) (AlgHom.normal_bijective K Ω Ω _))
  have e : s z = (τ : G K Ω) (algebraMap L Ω z) := ((hτ z).trans (s.liftNormal_commutes Ω z)).symm
  rw [e]
  exact (apply_mem_iff_of_mem_Dec (Weil_le_Dec h τ.2) _).2 hz

theorem valuation_trace_le {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (hL : IsLocalExt L h)
    {c : K} (hc : c ≠ 0) {z : L} (hz : v'.valuation L z ≤ v'.valuation L (algebraMap K L c)) :
    v.valuation K (Algebra.trace K L z) ≤ v.valuation K c := by
  have hc' : algebraMap K L c ≠ 0 := (_root_.map_ne_zero _).2 hc
  have h1 : v'.valuation L (z * (algebraMap K L c)⁻¹) ≤ 1 := by
    rw [map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ hz zero_le'
  have h2 := trace_mem h hL _ ((algebraMap_mem_iff h' _).2 h1)
  rw [algebraMap_mem_iff h, ← map_inv₀, mul_comm, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul,
    map_mul, map_inv₀] at h2
  have hv : v.valuation K c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  calc v.valuation K (Algebra.trace K L z)
      = (v.valuation K c)⁻¹ * v.valuation K (Algebra.trace K L z) * v.valuation K c := by
        rw [mul_comm _ (v.valuation K c), ← mul_assoc, mul_inv_cancel₀ hv, one_mul]
    _ ≤ 1 * v.valuation K c := by gcongr
    _ = v.valuation K c := one_mul _

end GlobalTheory.LocLanglands.TraceCompl

namespace GlobalTheory.LocLanglands.TraceCompl

open WithZero

variable (K : Type) {L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

def traceMap (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) :
    WithVal (v'.valuation L) →+ v.adicCompletion K :=
  ((algebraMap K (v.adicCompletion K)).toAddMonoidHom.comp (Algebra.trace K L).toAddMonoidHom).comp
    (WithVal.equiv (v'.valuation L)).toAddMonoidHom

variable {K} {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  [IsScalarTower K L Ω]

theorem continuous_traceMap {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)}
    {v' : HeightOneSpectrum (𝓞 L)} (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (hL : IsLocalExt L h) :
    Continuous (traceMap K v v') := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero]
  intro s hs
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  have hc0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := (_root_.map_ne_zero _).2 γ.ne_zero
  obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt hc0
  obtain ⟨π, hπ, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hp0 : algebraMap (𝓞 K) K (π ^ n) ≠ 0 :=
    (_root_.map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (pow_ne_zero n hπ0)
  have hpv : v.valuation K (algebraMap (𝓞 K) K (π ^ n)) ≤ exp (-(n : ℤ)) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
    exact Ideal.pow_mem_pow hπ n
  have hd : v'.valuation L (algebraMap K L (algebraMap (𝓞 K) K (π ^ n))) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((_root_.map_ne_zero _).2 hp0)
  rw [Filter.mem_map, Valued.mem_nhds_zero]
  refine ⟨Units.mk0 ((Valued.v : Valuation (WithVal (v'.valuation L)) ℤᵐ⁰).restrict
    (WithVal.toVal _ (algebraMap K L (algebraMap (𝓞 K) K (π ^ n))))) ?_, fun z hz => hγ ?_⟩
  · simpa using hd
  · rw [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hz
    rw [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    have e : traceMap K v v' z = algebraMap K _ (Algebra.trace K L (WithVal.ofVal z)) := rfl
    rw [e, GlobalTheory.Idele.valued_algebraMap]
    exact (valuation_trace_le h h' hL hp0 hz.le).trans_lt (hpv.trans_lt hn)

end GlobalTheory.LocLanglands.TraceCompl

namespace GlobalTheory.LocLanglands.TraceCompl

theorem exists_trace_extension : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v'), IsLocalExt L h → ∃ T : v'.adicCompletion L →+ v.adicCompletion K, Continuous T ∧ ∀ z : L, T (algebraMap L _ z) = algebraMap K _ (Algebra.trace K L z) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' hL
  refine ⟨(AddMonoidHom.extension (traceMap K v v') (continuous_traceMap h h' hL)).comp
    (HeightOneSpectrum.adicCompletion.equiv L v').toAddMonoidHom, ?_, fun z => ?_⟩
  · exact (AddMonoidHom.continuous_extension _ (continuous_traceMap h h' hL)).comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion L v')
  · exact AddMonoidHom.extension_coe _ (continuous_traceMap h h' hL) (WithVal.toVal _ z)

end GlobalTheory.LocLanglands.TraceCompl
end
end

section

open NumberField IsDedekindDomain Polynomial Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq GlobalTheory.SmGL Formalism.L2.NT

noncomputable section

namespace GlobalTheory.ArtinInertia

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem isUnitAt_artin_ine : ∀ {E' Ω : Type} [Field E'] [NumberField E'] [Field Ω] [Algebra E' Ω] [IsAlgClosure E' Ω]
    {A : ValuationSubring Ω} {w' : HeightOneSpectrum (𝓞 E')} (h' : _root_.Formalism.ConjugateSelfDual.IsPlaceOver A w')
    (a' : Weil h' →* (w'.adicCompletion E')ˣ) (ha : IsLocalArtin h' a') (t : Ine (F := E') A),
    IsUnitAt w' (a' (ineIncl h' t)) := by
  intro E' Ω _ _ _ _ _ A w' h' a' ha t
  have h1 := ha.ord_eq (ineIncl h' t)
  rw [deg_ineIncl, neg_zero, SphCompletion.ord_completion, neg_eq_zero] at h1
  have h0 : Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') ≠ 0 := by simp
  show Valued.v ((a' (ineIncl h' t) : (w'.adicCompletion E')ˣ) : w'.adicCompletion E') = 1
  rw [← WithZero.exp_log h0, h1, WithZero.exp_zero]

end GlobalTheory.ArtinInertia
end
end

section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem acris_mul_eq_zero : ∀ (l : ℕ) [Fact l.Prime] (x y : Formalism.Per.Acris l), x * y = 0 → x = 0 ∨ y = 0 := by
  intro l _ x y hxy
  have hl : (1 : ℝ) < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) := by linarith
  have hρ1 : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  have hρ0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.mpr hl0
  have hG := isGauss_gC_target l (l : ℝ)⁻¹ le_rfl hρ1
  have hc : gC l (l : ℝ)⁻¹ (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (l : Formalism.Per.Ainf l)) = (l : ℝ)⁻¹ := by
    rw [hG.2.2.2.2]
    exact GlobalTheory.GaussSlope.gauss_l l hρ0.le
  have h0 : gC l (l : ℝ)⁻¹ (0 : Formalism.Per.Acris l) = 0 := by
    have h := hG.2.2.2.1 0 (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris l) (l : Formalism.Per.Ainf l))
    rw [zero_mul, hc] at h
    have : gC l (l : ℝ)⁻¹ (0 : Formalism.Per.Acris l) * (1 - (l : ℝ)⁻¹) = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · linarith
  by_contra h
  push_neg at h
  have hx := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l x h.1 (l : ℝ)⁻¹ le_rfl hρ1
  have hy := GlobalTheory.T.gaussNormAcrisRadius_pos_definite l y h.2 (l : ℝ)⁻¹ le_rfl hρ1
  have hm := hG.2.2.2.1 x y
  rw [hxy, h0] at hm
  have := mul_pos hx hy
  linarith

end GlobalTheory.PMon.Gauss
end

section

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.Per.DeRhamSpan

open GlobalTheory.DeRhamCompare
open GlobalTheory.IndefiniteRowSideFullHecke.JumpMultiplicityDual (mulPeriod)

theorem span_of_invariant {G E M : Type} [CommRing E] (hE : IsField E) [AddCommGroup M]
    [Module E M] [Module.Finite E M] {n : ℕ} (hn : n = finrank E M)
    (σ : G → (E →+* E)) (ρ : G → (M →+ M))
    (hρ : ∀ g (e : E) (m : M), ρ g (e • m) = σ g e • ρ g m) (v : Fin n → M)
    (hv : ∀ g i, ρ g (v i) = v i)
    (hind : ∀ c : Fin n → E, (∀ g i, σ g (c i) = c i) → ∑ i, c i • v i = 0 → ∀ i, c i = 0)
    (y : M) : ∃ c : Fin n → E, ∑ i, c i • v i = y := by
  letI := hE.toField
  have h := GlobalTheory.Per.linearIndependent_of_invariant G E M (Fin n) σ ρ hρ v hv hind
  have h2 := h.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin]; exact hn)
  exact (Submodule.mem_span_range_iff_exists_fun E).1 (h2 ▸ Submodule.mem_top)

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem finrank_DdRK [FiniteDimensional Qp LL] [FiniteDimensional LL V] (h : IsDR PD ρ) :
    FiniteDimensional K (DdRK PD ρ) ∧ finrank K (DdRK PD ρ) = finrank Qp V := by
  have := PD.finK
  have := finite_DdR PD ρ h
  have : FiniteDimensional Qp V := Module.Finite.trans LL V
  have : FiniteDimensional Qp (DdR PD ρ) := Module.Finite.trans LL _
  let ε : DdR PD ρ ≃ₗ[Qp] DdRK PD ρ :=
    { toFun := fun x => GlobalTheory.DeRhamCompare.toK PD ρ x x.2
      invFun := fun y => ⟨(TensorProduct.comm Qp V BdR).symm y, y.2⟩
      map_add' := fun x y => Subtype.ext (by simp [GlobalTheory.DeRhamCompare.toK])
      map_smul' := fun a x => Subtype.ext (by simp [GlobalTheory.DeRhamCompare.toK])
      left_inv := fun x => Subtype.ext (by simp [GlobalTheory.DeRhamCompare.toK])
      right_inv := fun x => Subtype.ext (by simp [GlobalTheory.DeRhamCompare.toK]) }
  have : FiniteDimensional Qp (DdRK PD ρ) := ε.finiteDimensional
  refine ⟨Module.Finite.of_restrictScalars_finite Qp K _, ?_⟩
  have h1 := Module.finrank_mul_finrank Qp K (DdRK PD ρ)
  have h2 := Module.finrank_mul_finrank Qp LL (DdR PD ρ)
  have h3 := Module.finrank_mul_finrank Qp LL V
  rw [← ε.finrank_eq, ← h2, h, mul_left_comm, h3] at h1
  exact Nat.eq_of_mul_eq_mul_left finrank_pos h1

theorem span_of_isField [FiniteDimensional Qp LL] [FiniteDimensional LL V] (hF : IsField BdR)
    (h : IsDR PD ρ) (y : V ⊗[Qp] BdR) :
    ∃ (m : ℕ) (b : Fin m → BdR) (d : Fin m → V ⊗[Qp] BdR), (∀ i, d i ∈ DdR PD ρ) ∧
      y = ∑ i, mulPeriod (Qp := Qp) (LL := LL) (V := V) (b i) (d i) := by
  have : FiniteDimensional Qp V := Module.Finite.trans LL V
  have := hF.nontrivial
  obtain ⟨_, hr⟩ := finrank_DdRK PD ρ h
  let e := Module.finBasisOfFinrankEq K _ hr
  let σ : G → BdR ⊗[Qp] V →ₗ[Qp] BdR ⊗[Qp] V := fun g =>
    TensorProduct.map (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) ((ρ g).restrictScalars Qp)
  have hσ : ∀ g (b : BdR) w, σ g (b • w) = PD.actdR g b • σ g w := by
    intro g b w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  have hc : ∀ g x, σ g (TensorProduct.comm Qp V BdR x) =
      TensorProduct.comm Qp V BdR (actVdR PD ρ g x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, actVdR]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  obtain ⟨b, hb⟩ := span_of_invariant (M := BdR ⊗[Qp] V) hF (n := finrank Qp V)
    Module.finrank_baseChange.symm
    (fun g => (PD.actdR g : BdR →+* BdR)) (fun g => (σ g).toAddMonoidHom) hσ
    (fun k => (e k : BdR ⊗[Qp] V))
    (fun g k => by
      have h1 := hc g ((TensorProduct.comm Qp V BdR).symm (e k))
      rw [(mem_DdR PD ρ _).1 (e k).2 g, LinearEquiv.apply_symm_apply] at h1
      exact h1)
    (fun c hcg hsum k => by
      choose a ha using fun p => PD.invdR (c p) fun g => hcg g p
      have h1 : ∑ i, a i • e i = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_zero, ← hsum]
        simp only [Submodule.coe_sum, Submodule.coe_smul, ← ha, algebraMap_smul]
      rw [← ha, Fintype.linearIndependent_iff.1 e.linearIndependent a h1 k, map_zero])
    (TensorProduct.comm Qp V BdR y)
  refine ⟨_, b, fun k => (TensorProduct.comm Qp V BdR).symm (e k), fun k => (e k).2, ?_⟩
  apply (TensorProduct.comm Qp V BdR).injective

  simp only [map_sum, comm_mp, LinearEquiv.apply_symm_apply, hb]

end General

theorem tied_deRham_span : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K) ρ → ∀ y : V ⊗[ℚ_[l]] P.R.BdR, ∃ (m : ℕ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR), (∀ i, d i ∈ DdR (P.PD K) ρ) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[↥LL.1] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ h y
  haveI := LL.2
  exact span_of_isField (P.PD K) ρ (GlobalTheory.Per.TiedField.tied_field l P AI T).1 h y

end GlobalTheory.Per.DeRhamSpan
end
end

section

open NumberField

theorem _root_.GlobalTheory.T.host_imagQuadratic_isGalois_units_pm_one : ∀ D : Formalism.BasicNotions.D7, IsGalois ℚ D.host.K ∧ ∀ u : (𝓞 D.host.K)ˣ, u = 1 ∨ u = -1 := by
  first | exact @GlobalTheory.HostQuadUnits.main | exact GlobalTheory.HostQuadUnits.main | (intros; apply GlobalTheory.HostQuadUnits.main <;> assumption)
end

section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

noncomputable section

namespace GlobalTheory.HostImage

theorem host_image_mem : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.host.E), (D.nbr i w hw).j (algebraMap D.host.E D.nd.Om x) ∈ MaximalUnramifiedExtension (D.nd.l i) ⊔ IntermediateField.adjoin ℚ_[D.nd.l i] {y : Om (D.nd.l i) | y ^ (D.nd.l i ^ D.nd.s0 i) = 1} := by
  intro D i w hw x
  have h := UpperTheory.Small.factorization_condN_le D.host (D.nd.lPrime i).out
  refine UpperTheory.Small.image_mem_Kur_sup D.host ((D.nbr i w hw).j.comp (algebraMap D.host.E D.nd.Om)) ?_ x
  by_cases h2 : D.nd.l i = 2
  · rw [D.nd.restNLevelExponent_of_two i h2, ← h2]
    exact h.2 h2
  · rw [D.nd.restNLevelExponent_of_odd i h2]
    exact h.1

end GlobalTheory.HostImage
end
end

section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

noncomputable section
namespace GlobalTheory.NLink.AmbSub

variable {D : D7}

theorem WpO_cont (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hρ : Continuous fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :
    Continuous fun g => WpO D.nd i ρ π g := by
  have h1 : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
    have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      rw [map_inv]
      rfl
    rw [e]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  exact h1.smul hρ

end GlobalTheory.NLink.AmbSub
end
end

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.QForm (QVal IsQ bOf)

theorem _root_.GlobalTheory.T.psiUnitOn_rescale_uniformizer_of_qVal : ∀ (T : Formalism.L2.Pj.CDVR) (D : DegPre T.V) (ϖ : T.V), Irreducible ϖ → ∀ (y : D.X) (n : ℤ), QVal D ϖ y n → ∀ q : D.X → (FractionRing T.V)ˣ, (q y : FractionRing T.V) = algebraMap T.V (FractionRing T.V) ϖ ^ (-n) → PsiUnitOn (GlobalTheory.TauTwist.rescale D q) y Set.univ := by
  first | exact @GlobalTheory.TauTwist.psiUnitOn_rescale_of_qVal | exact GlobalTheory.TauTwist.psiUnitOn_rescale_of_qVal | (intros; apply GlobalTheory.TauTwist.psiUnitOn_rescale_of_qVal <;> assumption)
end

section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem _root_.GlobalTheory.T.structure_unramified_adjoin_sqrt_neg_prime : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K : FinExt l) (M : IntermediateField ℚ_[l] (Om l)) (y : Om l), M ≤ MaximalUnramifiedExtension l → y ^ 2 = -(l : Om l) → y ∉ MaximalUnramifiedExtension l → y ∈ IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} → K.1 = M ⊔ IntermediateField.adjoin ℚ_[l] {y} → K.1 = K0 K ⊔ IntermediateField.adjoin ℚ_[l] {y} ∧ K.1 ≤ Ks K 1 ∧ Module.finrank ↥(K0 K) ↥K.1 = 2 ∧ Module.finrank ℚ_[l] ↥(Ks K 1) = (l - 1) / 2 * Module.finrank ℚ_[l] ↥K.1 := by
  first | exact @GlobalTheory.SqrtNegL.structure_sqrt_neg | exact GlobalTheory.SqrtNegL.structure_sqrt_neg | (intros; apply GlobalTheory.SqrtNegL.structure_sqrt_neg <;> assumption)
end
