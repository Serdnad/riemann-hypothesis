module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle007
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle222
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1901
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1949
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle042
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1115
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1993
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1866
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1697
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1940
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion

@[expose] public section

section

open NumberField MeasureTheory IsDedekindDomain
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.BotClassDict (finQ)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ZeroAtPlaces

section Generic

variable {K : Type} [Field K] [NumberField K]

theorem ev_mul (a b : FiniteAdeleRing (𝓞 K) K) (Q : HeightOneSpectrum (𝓞 K)) : (a * b) Q = a Q * b Q := rfl

theorem val_nat (Q : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Valued.v ((n : FiniteAdeleRing (𝓞 K) K) Q) = Q.valuation K ((n : 𝓞 K) : K) := by
  rw [← Formalism.UG.P.levelaf_valued_algebraMap, ← map_natCast (algebraMap K (FiniteAdeleRing (𝓞 K) K)) n]
  rfl

theorem val_nat_eq_one (Q : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : (n : 𝓞 K) ∉ Q.asIdeal) :
    Valued.v ((n : FiniteAdeleRing (𝓞 K) K) Q) = 1 := by
  rw [val_nat]
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K), not_lt] at hn
  exact le_antisymm (Q.valuation_le_one (K := K) _) hn

theorem val_nat_lt_one (Q : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : (n : 𝓞 K) ∈ Q.asIdeal) :
    Valued.v ((n : FiniteAdeleRing (𝓞 K) K) Q) < 1 := by
  rw [val_nat]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) Q _).2 hn

theorem divisible_iff {q : ℕ} (hq : q.Prime) (y : FiniteAdeleRing (𝓞 K) K)
    (hy : ∃ n : ℕ, 0 < n ∧ ∀ Q, ((n : FiniteAdeleRing (𝓞 K) K) * y) Q ∈ Q.adicCompletionIntegers K) :
    (∀ k : ℕ, ∃ m : ℕ, 0 < m ∧ Nat.Coprime m q ∧ ∃ s : FiniteAdeleRing (𝓞 K) K,
      (∀ Q, s Q ∈ Q.adicCompletionIntegers K) ∧
        (m : FiniteAdeleRing (𝓞 K) K) * y = (q : FiniteAdeleRing (𝓞 K) K) ^ k * s) ↔
    ∀ Q : HeightOneSpectrum (𝓞 K), (q : 𝓞 K) ∈ Q.asIdeal → y Q = 0 := by
  constructor
  · intro h Q hQ
    by_contra h0
    have h1 : Valued.v (y Q) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    obtain ⟨k, hk⟩ := exists_pow_lt₀ (val_nat_lt_one Q hQ) (Units.mk0 _ h1)
    obtain ⟨m, -, hm, s, hs, e⟩ := h k
    have hm' : (m : 𝓞 K) ∉ Q.asIdeal := by
      intro hmem
      obtain ⟨a, b, hab⟩ := (Nat.isCoprime_iff_coprime.2 hm).map (Int.castRingHom (𝓞 K))
      simp only [eq_intCast, Int.cast_natCast] at hab
      refine Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
      rw [← hab]
      exact add_mem (Ideal.mul_mem_left _ _ hmem) (Ideal.mul_mem_left _ _ hQ)
    have e1 : (m : FiniteAdeleRing (𝓞 K) K) Q * y Q = ((q : FiniteAdeleRing (𝓞 K) K) Q) ^ k * s Q :=
      congrArg (fun z : FiniteAdeleRing (𝓞 K) K => z Q) e
    have e2 := congrArg Valued.v e1
    rw [map_mul, map_mul, map_pow, val_nat_eq_one Q hm', one_mul] at e2
    have hs1 : Valued.v (s Q) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hs Q)
    rw [Units.val_mk0, e2] at hk
    exact absurd hk (not_lt.2 (mul_le_of_le_one_right' hs1))
  · intro h k
    obtain ⟨n, hn, hint⟩ := hy
    obtain ⟨j, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero _))
    have hq0 : (q : K) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
    have hu : (q : FiniteAdeleRing (𝓞 K) K) ^ k * algebraMap K _ ((q : K) ^ k)⁻¹ = 1 := by
      rw [← map_natCast (algebraMap K (FiniteAdeleRing (𝓞 K) K)) q, ← map_pow, ← map_mul,
        mul_inv_cancel₀ (pow_ne_zero k hq0), map_one]
    refine ⟨m, hm0, ((Nat.Prime.coprime_iff_not_dvd hq).2 hm).symm,
      algebraMap K _ ((q : K) ^ k)⁻¹ * ((m : FiniteAdeleRing (𝓞 K) K) * y), fun Q => ?_,
      by rw [← mul_assoc, hu, one_mul]⟩
    by_cases hQ : (q : 𝓞 K) ∈ Q.asIdeal
    · rw [ev_mul, ev_mul, h Q hQ, mul_zero, mul_zero]
      exact zero_mem _
    · have h1 := val_nat_eq_one Q hQ
      have h2 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hint Q)
      have e1 : ((q : FiniteAdeleRing (𝓞 K) K) Q) ^ k *
          (algebraMap K (FiniteAdeleRing (𝓞 K) K) ((q : K) ^ k)⁻¹) Q = 1 :=
        congrArg (fun z : FiniteAdeleRing (𝓞 K) K => z Q) hu
      have e2 := congrArg Valued.v e1
      rw [map_mul, map_pow, h1, one_pow, one_mul, map_one] at e2
      have e3 : (((q ^ j * m : ℕ) : FiniteAdeleRing (𝓞 K) K) * y) Q =
          ((q : FiniteAdeleRing (𝓞 K) K) Q) ^ j * ((m : FiniteAdeleRing (𝓞 K) K) * y) Q := by
        rw [Nat.cast_mul, Nat.cast_pow, mul_assoc]
        rfl
      rw [e3, map_mul, map_pow, h1, one_pow, one_mul] at h2
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, ev_mul, map_mul, e2, one_mul]
      exact h2

end Generic

open GlobalTheory.BotFormula GlobalTheory.BotClassDict

theorem mem_OhE_iff {D : D7} (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    y ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D ↔ ∀ Q, toFinE D y Q ∈ Q.adicCompletionIntegers D.host.E :=
  ⟨fun hy => GlobalTheory.AdeleBaseChange.map_mem_int (ι := (toFinE D).toRingHom) toFinE_tmul hy,
    fun hy => GlobalTheory.AdeleBaseChange.mem_int_of_map (ι := (toFinE D).toRingHom) toFinE_tmul hy⟩

theorem zeroAt_iff_comp {D : D7} {q : ℕ} (hq : q.Prime) (y : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    Formalism.MainNotions.StandardLatticesGL3.ZeroAt D q y ↔
      ∀ Q : HeightOneSpectrum (𝓞 D.host.E), (q : 𝓞 D.host.E) ∈ Q.asIdeal → toFinE D y Q = 0 := by
  obtain ⟨n, hn, hint⟩ := (GlobalTheory.AdelicApprox.approx_mod_ideal D ⊤ top_ne_bot).2.1 y
  rw [mem_OhE_iff, map_mul, map_natCast] at hint
  rw [← divisible_iff hq (toFinE D y) ⟨n, hn, hint⟩]
  refine forall_congr' fun k => exists_congr fun m => and_congr_right' (and_congr_right' ⟨?_, ?_⟩)
  · rintro ⟨s, hs, e⟩
    refine ⟨toFinE D s, (mem_OhE_iff s).1 hs, ?_⟩
    have := congrArg (toFinE D) e
    rwa [map_mul, map_mul, map_pow, map_natCast, map_natCast] at this
  · rintro ⟨s, hs, e⟩
    obtain ⟨s, rfl⟩ := (toFinE D).surjective s
    refine ⟨s, (mem_OhE_iff s).2 hs, (toFinE D).injective ?_⟩
    rw [map_mul, map_mul, map_pow, map_natCast, map_natCast]
    exact e

theorem toFinE_finQ {D : D7} (a : AE D) :
    toFinE D (finQ D a) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D a) := by
  rw [← finAdEquiv_toAfE, toAfE_finQ]
  rfl

theorem comp_base {D : D7} (η : AF D.host.F) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    toFinE D (finQ D (algebraMap (AF D.host.F) (AE D) η)) Q =
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q (η.2 (Q.under (𝓞 D.host.F))) := by
  have h : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (algebraMap (AF D.host.F) (AE D) η)) =
      GlobalTheory.AdeleBaseChange.adMap D.host.F D.host.E η.2 * algebraMap D.host.E _ 1 := GlobalTheory.LFun.toFinAd_tmul η.2 1
  rw [toFinE_finQ, h, map_one, mul_one]
  rfl

theorem idem_mul_eq_zero_iff {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {η : AF D.host.F} (h : IsPlaceIdem D v η)
    (a : AE D) : algebraMap (AF D.host.F) (AE D) η * a = 0 ↔
      ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) = v → toFinE D (finQ D a) Q = 0 := by
  have hev : ∀ Q, toFinE D (finQ D (algebraMap (AF D.host.F) (AE D) η * a)) Q =
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q (η.2 (Q.under (𝓞 D.host.F))) * toFinE D (finQ D a) Q := by
    intro Q
    rw [RingHom.map_mul, map_mul, ev_mul, comp_base]
  obtain ⟨α, rfl, h1, h0⟩ := h
  have hinf : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := TensorProduct.zero_tmul _ _
  have k1 : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) = v →
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q ((pairA D.host.F 0 α).2 (Q.under (𝓞 D.host.F))) = 1 := by
    intro Q hQ
    subst hQ
    exact (congrArg _ h1).trans (map_one _)
  have k0 : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Q.under (𝓞 D.host.F) ≠ v →
      GlobalTheory.AdeleBaseChange.locMap D.host.F Q ((pairA D.host.F 0 α).2 (Q.under (𝓞 D.host.F))) = 0 :=
    fun Q hQ => (congrArg _ (h0 _ hQ)).trans (map_zero _)
  constructor
  · intro e Q hQ
    have := hev Q
    rw [e, k1 Q hQ, one_mul, RingHom.map_zero, map_zero] at this
    exact this.symm
  · intro e
    refine GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, hinf, zero_mul, RingHom.map_zero]) ?_
    apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
    rw [← toFinE_finQ, RingHom.map_zero, map_zero]
    refine FiniteAdeleRing.ext _ fun Q => (hev Q).trans ?_
    by_cases hQ : Q.under (𝓞 D.host.F) = v
    · rw [e Q hQ, mul_zero]
      rfl
    · rw [k0 Q hQ, zero_mul]
      rfl

theorem zeroAt_finQ_iff : ∀ (D : D7) (q : ℕ), q.Prime → ∀ a : AE D, (Formalism.MainNotions.StandardLatticesGL3.ZeroAt D q (finQ D a) ↔
  ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (η : AF D.host.F), IsPlaceIdem D v η → (q : 𝓞 D.host.F) ∈ v.asIdeal →
    algebraMap (AF D.host.F) (AE D) η * a = 0) := by
  intro D q hq a
  have hmem : ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
      (q : 𝓞 D.host.F) ∈ (Q.under (𝓞 D.host.F)).asIdeal ↔ (q : 𝓞 D.host.E) ∈ Q.asIdeal := by
    intro Q
    change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ Q.asIdeal ↔ _
    rw [map_natCast]
  rw [zeroAt_iff_comp hq]
  constructor
  · intro h v η hη hv
    refine (idem_mul_eq_zero_iff hη a).2 fun Q hQ => h Q ((hmem Q).1 ?_)
    rw [hQ]
    exact hv
  · intro h Q hQ
    obtain ⟨η, hη⟩ := GlobalTheory.IdemSupport.exists_placeIdem (D := D) (Q.under (𝓞 D.host.F))
    exact (idem_mul_eq_zero_iff hη a).1 (h _ η hη ((hmem Q).2 hQ)) Q rfl

end GlobalTheory.ZeroAtPlaces
end

section

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeckeUChar

open IsDedekindDomain

variable {D : D7}

def finIdl (D : D7) : (AE D)ˣ →* (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
  Units.map ((GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp (finPart D)).toMonoidHom

def finY (D : D7) : (AE D)ˣ →* (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ :=
  (Units.map (GlobalTheory.BotFormula.toFinE D).symm.toRingHom.toMonoidHom).comp (finIdl D)

theorem coe_finIdl (x : (AE D)ˣ) : ((finIdl D x : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
    FiniteAdeleRing (𝓞 D.host.E) D.host.E) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) := rfl

theorem coe_finY (x : (AE D)ˣ) : ((finY D x : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) =
    (GlobalTheory.BotFormula.toFinE D).symm (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D))) := rfl

def finChar {N : ℕ} (c : HeckeU D N) : (AE D)ˣ →* Circle where
  toFun x := ⟨((c.f (finY D x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (c.unitary _)⟩
  map_one' := Circle.ext (by
    change ((c.f (finY D 1) : ℂˣ) : ℂ) = 1
    rw [map_one, map_one, Units.val_one])
  map_mul' x y := Circle.ext (by
    change ((c.f (finY D (x * y)) : ℂˣ) : ℂ) = ((c.f (finY D x) : ℂˣ) : ℂ) * ((c.f (finY D y) : ℂˣ) : ℂ)
    rw [map_mul, map_mul, Units.val_mul])

theorem coe_finChar {N : ℕ} (c : HeckeU D N) (x : (AE D)ˣ) :
    ((finChar c x : Circle) : ℂ) = ((c.f (finY D x) : ℂˣ) : ℂ) := rfl

def phaseAt (θ : InfFam D) (τ : D.what₂.Tau) : (AE D)ˣ →* Circle :=
  GlobalTheory.ChrEqUnique.phase.comp (Units.map ((θ τ).comp (infPart D)).toMonoidHom)

def infChar (θ : InfFam D) (n : D.what₂.Tau → ℤ) : (AE D)ˣ →* Circle := ∏ τ, phaseAt θ τ ^ n τ

theorem coe_infChar (θ : InfFam D) (n : D.what₂.Tau → ℤ) (x : (AE D)ˣ) :
    ((infChar θ n x : Circle) : ℂ) =
      ∏ τ, (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ n τ := by
  have h : ∀ s : Finset D.what₂.Tau, (((∏ τ ∈ s, phaseAt θ τ ^ n τ : (AE D)ˣ →* Circle) x : Circle) : ℂ) =
      ∏ τ ∈ s, ((phaseAt θ τ x : Circle) : ℂ) ^ n τ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha, MonoidHom.mul_apply, Circle.coe_mul, ih,
        MonoidHom.zpow_apply, Circle.coe_zpow]
  exact h Finset.univ

def chi {N : ℕ} (c : HeckeU D N) (θ : InfFam D) (e : ℤ) : (AE D)ˣ →* Circle := (finChar c * infChar θ c.n) ^ e

theorem continuous_phaseAt {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) : Continuous (phaseAt θ τ) :=
  GlobalTheory.ChrEqUnique.continuous_phase.comp (Continuous.units_map _ (GlobalTheory.FockCompare.continuous_comp hθ τ))

theorem continuous_infChar {θ : InfFam D} (hθ : IsInfFam θ) (n : D.what₂.Tau → ℤ) : Continuous (infChar θ n) := by
  have h : ∀ s : Finset D.what₂.Tau,
      Continuous (((∏ τ ∈ s, phaseAt θ τ ^ n τ : (AE D)ˣ →* Circle)) : (AE D)ˣ → Circle) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      change Continuous (fun _ : (AE D)ˣ => (1 : Circle))
      exact continuous_const
    | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact ((continuous_phaseAt hθ a).zpow (n a)).mul ih
  exact h Finset.univ

theorem finY_incA (a : D.host.Eˣ) :
    finY D (Units.map (incA D).toMonoidHom a) = Units.map (Formalism.MainNotions.StandardLatticesGL3.inc D).toMonoidHom a := by
  refine Units.ext ?_
  rw [coe_finY, RingEquiv.symm_apply_eq]
  change GlobalTheory.LFun.toFinAd D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ (a : D.host.E)) =
    GlobalTheory.LFun.toFinAd ℚ D.host.E ((1 : IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ) ⊗ₜ (a : D.host.E))
  rw [GlobalTheory.LFun.toFinAd_tmul, GlobalTheory.LFun.toFinAd_tmul, map_one, map_one]

theorem finY_mul_conj (x y : (AE D)ˣ) (h : (y : AE D) = x * cA D x) :
    finY D y = finY D x * Formalism.MainNotions.StandardLatticesGL3.sgU D (finY D x) := by
  refine Units.ext ?_
  apply (GlobalTheory.BotFormula.toFinE D).injective
  rw [Units.val_mul, map_mul]
  change GlobalTheory.BotFormula.toFinE D ((GlobalTheory.BotFormula.toFinE D).symm _) = GlobalTheory.BotFormula.toFinE D ((GlobalTheory.BotFormula.toFinE D).symm _) *
    GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.sgA D ((GlobalTheory.BotFormula.toFinE D).symm _))
  rw [GlobalTheory.BotFormula.toFinE_sgA, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, coe_finIdl, coe_finIdl, h,
    RingHom.map_mul, map_mul]
  apply congrArg (fun z => GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) * z)
  have e1 : finPart D (cA D (x : AE D)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) :=
    GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig (x : AE D)
  rw [e1, GlobalTheory.DefU.ClassFin.finAdEquiv_sigR D.sp.cm.sig (D.host.conj : D.host.E ≃+* D.host.E)
    (fun z => Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D z)]

end GlobalTheory.HeckeUChar
end
end

section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pull_two_nsmul_eq_zero_of_triples : ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : S.Opens) (V W : A.left.Opens) (hV : V ≤ W), (U : Set S).Nonempty → (∀ s : S, ∃ x ∈ V, A.hom x = s) → A.hom ⁻¹ᵁ U ≤ W → W ≤ A.hom ⁻¹ᵁ U ⊔ V → ∀ c : Pic W.toScheme, GlobalTheory.CechPic.pull (A.left.homOfLE hV) c = 0 → ∀ (Y : Over S) (x a v : Y ⟶ A) (p : Y.left ⟶ V.toScheme) (e : V.toScheme ⟶ (x.left ⁻¹ᵁ V).toScheme), p ≫ V.ι = v.left → (∀ y, (x * a).left y ∈ V ∧ (x * a⁻¹).left y ∈ V ∧ (v * a).left y ∈ V ∧ (v * a⁻¹).left y ∈ V) → Smooth ((x.left ⁻¹ᵁ V).ι ≫ p) → GeometricallyIntegral ((x.left ⁻¹ᵁ V).ι ≫ p) → e ≫ (x.left ⁻¹ᵁ V).ι ≫ p = 𝟙 _ → GlobalTheory.CechPic.pull (x.left ∣_ W) (2 • c) = 0 := by
  intro S _ _ hS A _ hA U V W hV hU hsurj hUW hWUV c hc Y x a v p e hpv hmem hsm hgi he
  have := hA.smooth
  have : GeometricallyIntegral A.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hA.smooth
      hA.geomConnected
  have : GlobalTheory.IsNormalScheme S := (GlobalTheory.isNormalScheme_iff S).mpr hS
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian A.hom
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  obtain ⟨s0, hs0⟩ := hU
  obtain ⟨a0, ha0V, ha0⟩ := hsurj s0
  have : Nonempty V := ⟨⟨a0, ha0V⟩⟩
  have : IsIntegral V.toScheme := inferInstance
  have hVn : GlobalTheory.IsNormalScheme V.toScheme := GlobalTheory.isNormalScheme_of_smooth (V.ι ≫ A.hom)
  let i0 := (x.left ⁻¹ᵁ W).ι
  let O : (x.left ⁻¹ᵁ W).toScheme.Opens := i0 ⁻¹ᵁ (x.left ⁻¹ᵁ V)
  have hrange : Set.range (x.left ⁻¹ᵁ V).ι = Set.range (O.ι ≫ i0) := by
    have hO : (O : Set _) = i0 ⁻¹' (x.left ⁻¹ᵁ V : Set Y.left) := rfl
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι, hO, Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι]
    ext z
    simp only [Set.mem_inter_iff, SetLike.mem_coe, Scheme.Hom.mem_preimage]
    exact ⟨fun h => ⟨h, hV h⟩, fun h => h.1⟩
  let φ := IsOpenImmersion.isoOfRangeEq (x.left ⁻¹ᵁ V).ι (O.ι ≫ i0) hrange
  have hφ : φ.hom ≫ O.ι ≫ i0 = (x.left ⁻¹ᵁ V).ι := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  let UT : V.toScheme.Opens := (V.ι ≫ A.hom) ⁻¹ᵁ U
  have hUT : (UT : Set V.toScheme).Nonempty := ⟨⟨a0, ha0V⟩, by
    show A.hom (V.ι ⟨a0, ha0V⟩) ∈ U
    simpa [ha0] using hs0⟩
  let p' := i0 ≫ p
  have hOp : O.ι ≫ p' = φ.inv ≫ (x.left ⁻¹ᵁ V).ι ≫ p := by
    rw [← hφ]; simp [p']
  have hsm' : Smooth (O.ι ≫ p') := by rw [hOp]; infer_instance
  have hgi' : GeometricallyIntegral (O.ι ≫ p') := by
    have : MorphismProperty.RespectsIso @GeometricallyIntegral :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    rw [hOp]; exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral φ.inv _).mpr hgi
  have he' : (e ≫ φ.hom) ≫ O.ι ≫ p' = 𝟙 _ := by
    simp only [p', Category.assoc]; rw [reassoc_of% hφ]; exact he
  have hpY : p' ≫ V.ι ≫ A.hom = i0 ≫ Y.hom := by
    simp only [p', Category.assoc]; rw [reassoc_of% hpv, Over.w v]
  have hcover : O ⊔ p' ⁻¹ᵁ UT = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    have hz : x.left (i0 z) ∈ W := z.2
    have h' : x.left (i0 z) ∈ ((A.hom ⁻¹ᵁ U ⊔ V : A.left.Opens) : Set A.left) := hWUV hz
    rw [TopologicalSpace.Opens.coe_sup] at h'
    rcases h' with h | h
    · right
      show (V.ι ≫ A.hom) (p' z) ∈ U
      rw [← Scheme.Hom.comp_apply, hpY, ← Over.w x, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact h
    · left
      exact h
  have key : ∀ c' : Pic (x.left ⁻¹ᵁ W).toScheme, pull O.ι c' = 0 → pull (p' ⁻¹ᵁ UT).ι c' = 0 →
      c' = 0 := fun c' h1 h2 =>
    GlobalTheory.T.picardClass_eq_zero_of_zero_dense_open_and_section_open V.toScheme (x.left ⁻¹ᵁ W).toScheme ((GlobalTheory.isNormalScheme_iff _).mp hVn) UT hUT p'
      O (e ≫ φ.hom) hsm' hgi' he' hcover c' h1 h2
  apply key
  · rw [← pull_comp]
    have hfac : O.ι ≫ (x.left ∣_ W) = φ.inv ≫ (x.left ∣_ V) ≫ A.left.homOfLE hV := by
      rw [← cancel_mono W.ι]
      simp only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι]
      rw [← reassoc_of% hφ]
      simp [i0]
    rw [hfac, pull_comp, pull_comp, map_nsmul, hc, smul_zero, map_zero, map_zero]
  · rw [← pull_comp]
    let j := (p' ⁻¹ᵁ UT).ι
    let Y' : Over S := Over.mk (j ≫ i0 ≫ Y.hom)
    let q : Y' ⟶ Y := Over.homMk (j ≫ i0) (by simp [Y'])
    refine GlobalTheory.T.twice_picardClass_eq_zero_of_translates_mem_open S A hA U V W hV hUW c hc Y' (q ≫ x) (q ≫ a) (q ≫ v) ?_ ?_ ?_
      (j ≫ (x.left ∣_ W)) ?_
    · intro y
      show (j ≫ i0 ≫ Y.hom) y ∈ U
      rw [← hpY]
      exact y.2
    · intro y
      have : (q ≫ v).left = (j ≫ i0 ≫ p) ≫ V.ι := by simp [q, hpv]
      rw [this, Scheme.Hom.comp_apply]
      exact ((j ≫ i0 ≫ p) y).2
    · intro y
      simp only [← GrpObj.comp_inv, ← MonObj.comp_mul, Over.comp_left, Scheme.Hom.comp_apply]
      exact hmem _
    · simp [q, j, i0, morphismRestrict_ι]

end GlobalTheory
end

section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem cuspRapidDecaySiegelGL_of_finite (hfin : GlobalTheory.Published.AutomorphicFormsFiniteGL) :
    GlobalTheory.Published.CuspRapidDecaySiegelGL := by
  intro E _ _ _ a φ hφ ω hω hωB _ t ht lam
  obtain ⟨Ω, Kf, hΩ, hKf, hgeom⟩ := GlobalTheory.T.siegelSet_adelicGL_exists_compact_decomposition E a ω hω hωB t ht
  obtain ⟨S, hS⟩ := GlobalTheory.T.finite_translates_smoothFunction_of_compact E a φ hφ.1.level Kf hKf
  have hcore := fun f' : GL (Fin a) (Af E) =>
    GlobalTheory.T.cuspForm_rapidDecay_siegelCone_realPoints hfin E a (finRep E a f' φ) (GlobalTheory.T.isCuspForm_operator_act hfin E a (.fin f') φ hφ) Ω hΩ t ht lam
  choose C hC0 hC using hcore
  refine ⟨∑ f' ∈ S, C f', fun b hb r hr hchain hprod k hk => ?_⟩
  obtain ⟨d, hd, hdiag⟩ := GlobalTheory.T.exists_realDiagonal_infGL_eq_positiveIdeleDiagonal E a r hr
  rw [hdiag]
  obtain ⟨c, hc, f, hf, heq⟩ := hgeom r d hr hchain hd b hb k hk
  rw [heq]
  obtain ⟨f', hf', hff'⟩ := hS f hf
  have e : φ.1 (infGL E a (d * c) * finGL E a f) = (finRep E a f' φ).1 (infGL E a (d * c)) := by
    rw [← hff']; rfl
  rw [e]
  refine (hC f' r d hr hchain hd hprod c hc).trans ?_
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hC0 i) hf')
    (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hr i).le _)

end GlobalTheory
end
