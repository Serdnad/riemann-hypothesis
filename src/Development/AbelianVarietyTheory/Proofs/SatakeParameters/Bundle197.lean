module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle016
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1084
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle191
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1242
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle160
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle144
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.SecondStepGluing
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfCharConjEmbeddingNegOfInvariantPairing
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle194
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.LocalLevelIsKOneAtT
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle149
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SphConj

variable {D : D7}

theorem cA_cA' (z : Formalism.L2.Theta.AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [(cA D).map_zero, (cA D).map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a x => exact congrArg (fun t => a ⊗ₜ[D.host.F] t) (star_star x)

theorem cO_eq (x : 𝓞 D.host.E) : Formalism.DivisionValues.cO D.host.E x = GlobalTheory.IdemSupport.cO D x := RingOfIntegers.ext rfl

theorem conjPl_eq_cP (P : HeightOneSpectrum (𝓞 D.host.E)) : _root_.Formalism.DivisionValues.conjPl P = GlobalTheory.IdemSupport.cP P := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  rw [GlobalTheory.IdemSupport.mem_cP]
  change x ∈ P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) ↔ _
  rw [Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [cO_eq, GlobalTheory.IdemSupport.cO_cO]; exact hy
  · intro h
    exact ⟨GlobalTheory.IdemSupport.cO D x, h, by rw [cO_eq, GlobalTheory.IdemSupport.cO_cO]⟩

theorem mem_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) (x : 𝓞 D.host.E) :
    x ∈ (_root_.Formalism.DivisionValues.conjPl P).asIdeal ↔ GlobalTheory.IdemSupport.cO D x ∈ P.asIdeal := by
  rw [conjPl_eq_cP]; exact GlobalTheory.IdemSupport.mem_cP P x

theorem conjPl_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) : _root_.Formalism.DivisionValues.conjPl (_root_.Formalism.DivisionValues.conjPl P) = P := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  rw [mem_conjPl, mem_conjPl, GlobalTheory.IdemSupport.cO_cO]

theorem isConjPl_conjPl (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.IndefR.Lev.IsConjPl P (_root_.Formalism.DivisionValues.conjPl P) :=
  (GlobalTheory.IdemSupport.isConjPl_iff P _).2 (conjPl_eq_cP P)

theorem not_mem_sq (P : HeightOneSpectrum (𝓞 D.host.E)) (ϖ : 𝓞 D.host.E) (h : ϖ ∉ (_root_.Formalism.DivisionValues.conjPl P).asIdeal ^ 2) :
    GlobalTheory.IdemSupport.cO D ϖ ∉ P.asIdeal ^ 2 := by
  intro h'
  apply h
  have e1 : (_root_.Formalism.DivisionValues.conjPl P).asIdeal = P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) := rfl
  rw [e1, ← Ideal.map_pow]
  have := Ideal.mem_map_of_mem (Formalism.DivisionValues.cO D.host.E) h'
  convert this using 1
  rw [cO_eq, GlobalTheory.IdemSupport.cO_cO]

theorem conj_cases (V : HSp D) {Q : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D} (h : IsPrimeIdem Q e f) :
    (Formalism.L2.NTheta.IsIdemAt e Q ∧ IsPrimeIdem (_root_.Formalism.DivisionValues.conjPl Q) (cA D e) f) ∨ (_root_.Formalism.DivisionValues.conjPl Q = Q ∧ f = e) := by
  rcases h with ⟨hi, rfl⟩ | ⟨rfl, h2, h3⟩
  · have hc := (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.2 Q (_root_.Formalism.DivisionValues.conjPl Q) e hi
      (isConjPl_conjPl Q)
    exact Or.inl ⟨hi, Or.inl ⟨hc, by rw [cA_cA', add_comm]⟩⟩
  · have h' : IsPrimeIdem Q f f := Or.inr ⟨rfl, h2, h3⟩
    have hc := ((GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 Q f f h').2.1
    have ht : GlobalTheory.IdemSupport.Comparison₂ (GlobalTheory.IdemSupport.cP Q) f := by
      have := GlobalTheory.IdemSupport.Comparison₂.conj (P := Q) (e := f) h3
      rwa [hc] at this
    refine Or.inr ⟨?_, rfl⟩
    rw [conjPl_eq_cP]
    refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
    by_cases hx : x = 0
    · subst hx; simp only [Submodule.zero_mem]
    · exact (ht x hx).trans (h3 x hx).symm

theorem hyp_conj (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) : hyp V (_root_.Formalism.DivisionValues.conjPl P) = hyp V P := by
  obtain ⟨e, f, h⟩ := (GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.1 P
  rcases conj_cases V h with ⟨-, h'⟩ | ⟨hc, -⟩
  · rw [GlobalTheory.SphLabelOps.hyp_eq h', GlobalTheory.SphLabelOps.hyp_eq h]
  · rw [hc]

theorem divAt_conj (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E)
    (d : List ℤ) (α : GA D V) (he : Formalism.L2.NTheta.IsIdemAt e P) (h1 : ϖ ∈ P.asIdeal) (h2 : ϖ ∉ P.asIdeal ^ 2)
    (hd : DivAt V e (ϖ : D.host.E) d α) : DivAt V (cA D e) (star (ϖ : D.host.E)) (dualLab d) α :=
  GlobalTheory.T.elementaryDivisors_conjPrime_eq_dualLabel V P e ϖ d α he h1 h2 hd

theorem sphOp_conj (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (R : Finset (GA D V))
    (hR : SphOp V (_root_.Formalism.DivisionValues.conjPl P) d R) : SphOp V P (dualLab d) R := by
  obtain ⟨e, f, ϖ, α, -, hef, hϖ, hϖ2, hd, hJ, hχ, hα, hdiv, hR, hrep⟩ := hR
  have hS : OffS D ∅ P := fun v hv => absurd hv (Finset.notMem_empty v)
  rcases conj_cases V hef with ⟨hi, h'⟩ | ⟨hc, rfl⟩
  · rw [conjPl_conjPl] at h'
    have hD := divAt_conj V (_root_.Formalism.DivisionValues.conjPl P) e ϖ d α hi hϖ hϖ2 hdiv
    rw [← GlobalTheory.IdemSupport.cO_coe] at hD
    exact ⟨cA D e, f, GlobalTheory.IdemSupport.cO D ϖ, α, hS, h', (mem_conjPl P ϖ).1 hϖ, not_mem_sq P ϖ hϖ2,
      GlobalTheory.SphLabelOps.dualLab_pairwise hd, hJ, hχ, hα, hD, hR, hrep⟩
  · have hc' : _root_.Formalism.DivisionValues.conjPl P = P := hc.symm.trans (conjPl_conjPl P)
    rw [hc'] at hef hϖ hϖ2
    have he := (GlobalTheory.HeckeDual.idem_of_isPrimeIdem hef).1
    obtain ⟨a, b, ha, -, hb, -, hab⟩ :=
      (GlobalTheory.InertDoubleCoset.inert_double_cosets V P f hef (GlobalTheory.SphLabelOps.exists_real_unif D P) α hα).1
    have h0 := GlobalTheory.SphLabelOps.unif_ne_zero hϖ2
    have hinv := (GlobalTheory.DivDual.divAt_inv_and_mul V f _ d α he h0 hdiv).1
    have ha' : a⁻¹ ∈ KsphC V ∅ := (GlobalTheory.SphLabelOps.mem_stabG _).1 (inv_mem ((GlobalTheory.SphLabelOps.mem_stabG _).2 ha))
    have hb' : b⁻¹ ∈ KsphC V ∅ := (GlobalTheory.SphLabelOps.mem_stabG _).1 (inv_mem ((GlobalTheory.SphLabelOps.mem_stabG _).2 hb))
    have hD := (GlobalTheory.DivDual.divAt_inv_and_mul V f _ _ α⁻¹ he h0 hinv).2 _ ha' _ hb'
    have e1 : a⁻¹ * α⁻¹ * b⁻¹ = α := by rw [hab]; group
    rw [e1] at hD
    exact ⟨f, f, ϖ, α, hS, hef, hϖ, hϖ2, GlobalTheory.SphLabelOps.dualLab_pairwise hd, hJ, hχ, hα, hD, hR, hrep⟩

theorem isLab_conj (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) :
    IsLab V (_root_.Formalism.DivisionValues.conjPl P) d ↔ IsLab V P (dualLab d) := by
  constructor
  · rintro ⟨R, hR⟩; exact ⟨R, sphOp_conj V P d R hR⟩
  · rintro ⟨R, hR⟩
    rw [← conjPl_conjPl P] at hR
    have := sphOp_conj V (_root_.Formalism.DivisionValues.conjPl P) (dualLab d) R hR
    rw [GlobalTheory.SphLabelOps.dualLab_dualLab] at this
    exact ⟨R, this⟩

theorem sum_rep_conj (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) {M : Type} [AddCommGroup M] [Module ℂ M]
    (π : GA D V →* Module.End ℂ M) (u : M) (hu : ∀ k ∈ hyp V P, π k u = u) (d : List ℤ) :
    ∑ γ ∈ rep V (_root_.Formalism.DivisionValues.conjPl P) d, π γ u = ∑ γ ∈ rep V P (dualLab d), π γ u := by
  by_cases hd : IsLab V (_root_.Formalism.DivisionValues.conjPl P) d
  · have h1 := sphOp_conj V P d _ (GlobalTheory.SphLabelOps.sphOp_rep hd)
    rw [((GlobalTheory.SphLabelOps.label_operators V P).1 _ _ h1).2 M π u hu, GlobalTheory.SphLabelOps.opOf_single]
  · have hd' : ¬ IsLab V P (dualLab d) := fun h => hd ((isLab_conj V P d).2 h)
    rw [Hk3.rep, dite_eq_right hd, Hk3.rep, dite_eq_right hd']

theorem sph_conj : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), hyp V (_root_.Formalism.DivisionValues.conjPl P) = hyp V P ∧ (∀ d, IsLab V (_root_.Formalism.DivisionValues.conjPl P) d ↔ IsLab V P (dualLab d)) ∧ ∀ c, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → opOf π (_root_.Formalism.DivisionValues.conjPl P) c u = opOf π P (dualC c) u := by
  intro D V P
  refine ⟨hyp_conj V P, isLab_conj V P, fun c M _ _ π u hu => ?_⟩
  rw [opOf, opOf, dualC, Finsupp.sum_mapDomain_index (h := fun d (z : ℂ) => z • ∑ γ ∈ rep V P d, π γ) (fun _ => zero_smul ℂ _) (fun _ _ _ => add_smul _ _ _)]
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Finset.sum_congr rfl fun d _ => by rw [sum_rep_conj V P π u hu d]

end GlobalTheory.SphConj

end
end

section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoreThree

open Formalism.IndefR.Bridge in
theorem conj_ne_of_two {D : D7} (P : HeightOneSpectrum (𝓞 D.host.E)) (h2 : ((2 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    Formalism.DivisionValues.conjPl P ≠ P := by
  intro hP
  have hP' : P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) = P.asIdeal := congrArg HeightOneSpectrum.asIdeal hP
  have hfix : ∀ x : 𝓞 D.host.E, Formalism.DivisionValues.cO D.host.E x ∈ P.asIdeal ↔ x ∈ P.asIdeal := fun x => by
    conv_lhs => rw [← hP']
    exact Ideal.apply_mem_of_equiv_iff
  refine Formalism.MainNotions.KudlaSiegelWeil.InertConditionsOfHost.not_fixed_ram D P 2 (Or.inl rfl) h2 (Ideal.ext fun x => ?_)
  rw [Ideal.mem_comap, ← hfix x]
  refine Eq.to_iff (congrArg (· ∈ P.asIdeal) (RingOfIntegers.ext ?_))
  exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host _).symm

theorem exists_two (D : D7) : ∃ P : HeightOneSpectrum (𝓞 D.host.E), ((2 : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
  haveI : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp Nat.prime_two).irreducible
  obtain ⟨Q, hQ, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) (Ideal.span {(2 : ℤ)}) (by
    intro x hx
    rw [RingHom.mem_ker] at hx
    have : x = 0 := by
      have := congrArg (fun y : 𝓞 D.host.E => ((y : D.host.E))) hx
      simpa using this
    rw [this]; exact zero_mem _)
  have h2 : ((2 : ℕ) : 𝓞 D.host.E) ∈ Q := by
    have : (2 : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 D.host.E)) := by
      change (2 : ℤ) ∈ Ideal.under ℤ Q
      rw [hc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ.isPrime, fun hb => ?_⟩, h2⟩
  rw [hb, Ideal.mem_bot] at h2
  have := congrArg (fun y : 𝓞 D.host.E => ((y : D.host.E))) h2
  norm_num at this

end GlobalTheory.CoreThree

namespace GlobalTheory.CoreThree

theorem heckeCharacterisation_places_parts_of_weak : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → (R.toRealDat.ExAt → Core R.toRealDat F.lv2) ∧ IsSF R.toRealDat R.SF ∧ (∀ t, ∀ Q ∈ A3.okI t, Good R.toRealDat t (R.plI Q) ∧ _root_.Formalism.DivisionValues.conjPl (R.plI Q) = R.plI Q) ∧ (∀ P, Good R.toRealDat A3.A.μ0 P → (_root_.Formalism.DivisionValues.conjPl P = P → ∃ Q ∈ A3.okI A3.A.μ0, R.plI Q = P) ∧ (_root_.Formalism.DivisionValues.conjPl P ≠ P → ∃ P0 ∈ A3.A.ok A3.A.μ0, R.pl P0 = P)) ∧ (∀ c, R.EEc c = EEc R.toRealDat R.SF c) ∧ (∀ i c, R.Wc' i c = Wcc R.toRealDat R.SF i c) ∧ (A3.A.ok A3.A.μ0).Nonempty := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h
  have hL : R.toLevCh.Is A3.A.μ0 := h.base.lev
  obtain ⟨hQ0, -, -, -⟩ := GlobalTheory.GoodPrimes.good_primes R.toRealDat F.lv2 hL
  obtain ⟨_, _, _, ht⟩ := h.base.fam.tie
  have hSb : (R.Sb : Set (Pl D.host.E)) = R.Pg := by rw [h.allPl]
  have hon : ∀ P, Good R.toRealDat A3.A.μ0 P → (Formalism.DivisionValues.conjPl P = P → ∃ Q ∈ A3.okI A3.A.μ0, R.plI Q = P) ∧
      (Formalism.DivisionValues.conjPl P ≠ P → ∃ P0 ∈ A3.A.ok A3.A.μ0, R.pl P0 = P) := by
    intro P hP
    have hnS : P ∉ (R.Sb : Set (Pl D.host.E)) := by
      rw [hSb]; intro hm; exact (hP P (Or.inl hm)).1 rfl
    refine ⟨fun hf => ?_, fun hf => ?_⟩
    · have hio : Formalism.IndefR.Bridge.InertOff P (R.Sb : Set (Pl D.host.E)) := by
        refine ⟨?_, hnS⟩
        rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, hf]
      obtain ⟨Q, hQ⟩ := h.inert.onto P hio
      refine ⟨Q, (h.inert.tie.okI A3.A.μ0 Q).2 ?_, hQ⟩
      rw [hQ0, Finset.coe_empty, Set.union_empty, hQ]
      exact hio
    · have hso : Formalism.IndefR.Bridge.SplitOff P (R.Sb : Set (Pl D.host.E)) := by
        refine ⟨?_, hnS, fun Q hQ he => ?_⟩
        · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]
          exact fun he => hf (HeightOneSpectrum.ext he)
        · rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at he
          have hQP : Q = Formalism.DivisionValues.conjPl P := HeightOneSpectrum.ext he
          rw [hSb] at hQ
          apply (hP Q (Or.inl hQ)).2
          have := GlobalTheory.SplitHeckeAdj.isConjPl_conj (Formalism.DivisionValues.conjPl P)
          rw [Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl] at this
          rw [hQP]; exact this
      obtain ⟨P0, hP0⟩ := h.base.fam.pl_onto P hso
      refine ⟨P0, (ht.ok A3.A.μ0 P0).2 ?_, hP0⟩
      rw [hQ0, Finset.coe_empty, Set.union_empty, hP0]
      exact hso
  refine ⟨fun e => (GlobalTheory.CoreOfWeak.core_of_weak R F h e).1, ?_, ?_, hon, fun c => rfl, fun i c => rfl, ?_⟩
  · intro v
    rw [h.inert.SF v, h.allPl]
  · intro t Q hQ
    obtain ⟨hfix, hoff⟩ := (h.inert.tie.okI t Q).1 hQ
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at hfix
    have hf : Formalism.DivisionValues.conjPl (R.plI Q) = R.plI Q := HeightOneSpectrum.ext hfix
    refine ⟨fun PP hPP => ⟨fun he => hoff ?_, fun hc => hoff ?_⟩, hf⟩
    · rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← he]; exact hm)
      · exact Or.inr (by rw [← he]; exact hm)
    · have e1 := GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc
      have e2 : PP = R.plI Q := by
        rw [← Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl PP, ← e1, hf]
      rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← e2]; exact hm)
      · exact Or.inr (by rw [← e2]; exact hm)
  · obtain ⟨P, h2⟩ := exists_two D
    have hg : Good R.toRealDat A3.A.μ0 P := by
      intro PP hPP
      rw [hQ0] at hPP
      have hm : PP ∈ R.Pg := hPP.resolve_right (by simp)
      obtain ⟨k, hk⟩ := (hL.Pg PP).1 hm
      have hgk := GlobalTheory.LevelPlaces.mem_of_div _ k PP hk
      have hn : ((2 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal :=
        GlobalTheory.LevelPlaces.not_mem_of_prime PP.isPrime.ne_top Nat.prime_two (D.host.g_prime k) (Formalism.L2.Pj.g_ne_two D k) hgk
      refine ⟨fun he => hn (he ▸ h2), fun hc => ?_⟩
      have hgP := GlobalTheory.LevelPlaces.natCast_mem_of_isConjPl hc hgk
      exact GlobalTheory.LevelPlaces.not_mem_of_prime P.isPrime.ne_top Nat.prime_two (D.host.g_prime k)
        (Formalism.L2.Pj.g_ne_two D k) hgP h2
    obtain ⟨P0, hP0, -⟩ := (hon P hg).2 (conj_ne_of_two P h2)
    exact ⟨P0, hP0⟩

end GlobalTheory.CoreThree
end

section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.infChar_conjEmbedding_neg_of_invariant_pairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a : ℕ) (π π' : CuspSub E a), Paired π π' conjOp → ∀ (τ : E →+* ℂ) (m m' : Multiset ℂ), π.HasInfChar τ m → π'.HasInfChar (NumberField.ComplexEmbedding.conjugate τ) m' → m' = m.map Neg.neg := by
  first | exact @GlobalTheory.CapPair.infChar_conj_of_paired | exact GlobalTheory.CapPair.infChar_conj_of_paired | (intros; apply GlobalTheory.CapPair.infChar_conj_of_paired <;> assumption)
end

section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a) (ψ : HChar L), Paired (π.twist ψ⁻¹) (π.twist ψ⁻¹) invTOp → GlobalTheory.GalOfCusp.IsConjDualBy π ψ → DualIsConjBy π ψ := by
  first | exact @GlobalTheory.ConjDualPair.dualIsConjBy_of_paired_invT | exact GlobalTheory.ConjDualPair.dualIsConjBy_of_paired_invT | (intros; apply GlobalTheory.ConjDualPair.dualIsConjBy_of_paired_invT <;> assumption)
end

section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

theorem _root_.GlobalTheory.T.isConjSelfDual_of_invTranspose_iso_cmConj : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : CuspSub L a) (S : π.V ≃ₗ[ℂ] π.V), (∀ o φ, S (π.op (invTOp o) φ) = π.op (conjOp o) (S φ)) → π.IsCsd := by
  first | exact @GlobalTheory.CsdFromConj.isCsd_of_invT_conj | exact GlobalTheory.CsdFromConj.isCsd_of_invT_conj | (intros; apply GlobalTheory.CsdFromConj.isCsd_of_invT_conj <;> assumption)
end

section

noncomputable section

namespace GlobalTheory.TwU

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits Classical Formalism.L2.KerInert.Loc

theorem resV_subst_two {ι κ σ τ R : Type} [CommRing R] [Finite ι] [Finite σ]
    {f : κ → ι} (hf : Function.Injective f) {g : τ → σ} (hg : Function.Injective g)
    {a : σ → MvPowerSeries ι R} (ha : MvPowerSeries.HasSubst a)
    {a' : τ → MvPowerSeries κ R} (ha' : MvPowerSeries.HasSubst a')
    (h1 : ∀ k, resV f (a (g k)) = a' k) (h0 : ∀ i, (∀ k, g k ≠ i) → resV f (a i) = 0)
    (T : MvPowerSeries σ R) :
    resV f (MvPowerSeries.subst a T) = MvPowerSeries.subst a' (resV g T) := by
  rw [resV_subst hf ha, resV_eq_subst hg T, MvPowerSeries.subst_comp_subst_apply (hasSubst_resFam g) ha']
  congr 1
  funext i
  by_cases h : ∃ k, g k = i
  · obtain ⟨k, rfl⟩ := h
    rw [h1, resFam_apply hg, MvPowerSeries.subst_X ha']
  · push_neg at h
    rw [h0 i h, resFam_off g i h, ← MvPowerSeries.coe_substAlgHom ha', map_zero]

theorem resV_CX {ι κ R : Type} [CommRing R] [Finite ι] {f : κ → ι} (hf : Function.Injective f) (c : R) (k : κ) :
    resV f (MvPowerSeries.C c * MvPowerSeries.X (f k) : MvPowerSeries ι R) = MvPowerSeries.C c * MvPowerSeries.X k := by
  rw [resV_mul hf, resV_X hf]
  congr 1
  ext n
  rw [resV_coeff, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn, if_neg]
    intro h0
    apply hn
    have := congrArg Finsupp.degree h0
    rw [degree_mapDomain] at this
    exact (Finsupp.degree_eq_zero_iff n).1 (by simpa using this)

theorem resV_CX_off {ι κ R : Type} [CommRing R] [Finite ι] {f : κ → ι} (hf : Function.Injective f) (c : R) (i : ι)
    (hi : ∀ k, f k ≠ i) :
    resV f (MvPowerSeries.C c * MvPowerSeries.X i : MvPowerSeries ι R) = 0 := by
  rw [resV_mul hf, resV_X_off hf i hi, mul_zero]

theorem inj_at {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl) :
    Function.Injective (fun z : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, z⟩ : X.ZA j)) :=
  fun a b h => eq_of_heq (Sigma.mk.inj_iff.1 h).2

theorem inE_inj {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl) : Function.Injective (inE X j v) := by
  have hg : Function.Injective (fun e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, e⟩ : X.EA j)) :=
    fun a b h => eq_of_heq (Sigma.mk.inj_iff.1 h).2
  exact hg.sumMap hg

end GlobalTheory.TwU

namespace GlobalTheory.TwU

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits Classical Formalism.L2.KerInert.Loc

theorem hasSubst_coordZA {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) :
    MvPowerSeries.HasSubst (X.coordZA (K0 p) j) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by
    rintro (⟨w, r, a, b⟩ | ⟨w, r, a, b⟩) <;> simp [Sys.coordZA])

theorem hasSubst_coordZ {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (B : OmBasis p n') :
    MvPowerSeries.HasSubst (coordZ (r0 := r0) (r1 := r1) B (K0 p) 1) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by
    rintro (⟨r, a, b⟩ | ⟨r, a, b⟩) <;> simp [coordZ])

theorem resV_ThZA {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl) (T : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)) :
    resV (fun z : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, z⟩ : X.ZA j)) (X.ThZA (K0 p) j T) =
      ThZ (X.om v) (K0 p) 1 (resV (inE X j v) T) := by
  have hE := inE_inj X j v
  have hZ := inj_at X j v
  unfold Sys.ThZA ThZ
  refine resV_subst_two hZ hE (hasSubst_coordZA X j) (hasSubst_coordZ _) ?_ ?_ T
  · rintro (⟨r, a, b⟩ | ⟨r, a, b⟩)
    · show resV _ (X.coordZA (K0 p) j (Sum.inl ⟨v, (r, a, b)⟩)) = _
      simp only [Sys.coordZA, coordZ]
      rw [resV_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [one_mul, Algebra.algebraMap_self, RingHom.id_apply]
      exact resV_CX hZ _ (s, a, b)
    · show resV _ (X.coordZA (K0 p) j (Sum.inr ⟨v, (r, a, b)⟩)) = _
      simp only [Sys.coordZA, coordZ]
      rw [resV_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [one_mul, Algebra.algebraMap_self, RingHom.id_apply]
      exact resV_CX hZ _ (s, a, b)
  · rintro (⟨w, r, a, b⟩ | ⟨w, r, a, b⟩) hi
    · have hw : w ≠ v := by
        rintro rfl
        exact hi (Sum.inl (r, a, b)) rfl
      simp only [Sys.coordZA]
      rw [resV_sum]
      refine Finset.sum_eq_zero fun s _ => ?_
      exact resV_CX_off hZ _ _ (fun z h => hw (congrArg Sigma.fst h).symm)
    · have hw : w ≠ v := by
        rintro rfl
        exact hi (Sum.inr (r, a, b)) rfl
      simp only [Sys.coordZA]
      rw [resV_sum]
      refine Finset.sum_eq_zero fun s _ => ?_
      exact resV_CX_off hZ _ _ (fun z h => hw (congrArg Sigma.fst h).symm)

theorem resV_phAt {p : ℕ} [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p)) (j : ℕ) (v : X.Pl) :
    resV (inE X j v) (phAt X be j v) =
      ∑ e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)),
        sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)) := by
  have hE := inE_inj X j v
  unfold phAt
  rw [resV_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [restrict_formalSum hE be (by simp) (by simp)]
  exact congrArg₂ (sub2 p be) (resV_X hE (Sum.inl e)) (resV_X hE (Sum.inr e))

theorem restr_onePlace : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p)) (j : ℕ) (v : X.Pl)
    (U : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)), MvPowerSeries.constantCoeff be = 0 → IntS p (inParam p U) →
    IntS p (inParam p (resV (inE X j v) U)) ∧
      resV (fun z : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, z⟩ : X.ZA j))
        (X.ThZA (K0 p) j (expS p (-phAt X be j v) * U)) = thOne (X.om v) be (resV (inE X j v) U) := by
  intro p _ X be j v U _ hU
  have hE := inE_inj X j v
  refine ⟨?_, ?_⟩
  · obtain ⟨g, hg⟩ := hU
    exact ⟨resV (inE X j v) g, by rw [← resV_inParam hE, hg, resV_map]⟩
  · rw [resV_ThZA, resV_mul hE, resV_expS hE, resV_neg, resV_phAt]
    rfl

end GlobalTheory.TwU

end
end
