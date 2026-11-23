module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import GroundTheory.GlobalFields.TateThesis.AdelicCharLocal
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalAdditiveCharacterEqAdelic
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle040
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle001
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle045
public import ReciprocityTheory.Hypotheses.GalCoh
public import Formalism.GaloisCohomology.StatementLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle716
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle001
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle003
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle004
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.EulerCharGaloisOfCardEq
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Bundle003
import GroundTheory.ProfiniteCohomology.LocalTateDuality.TensorHomDualRepRootsOfUnityIsoCartierPairing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle041
import GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA

@[expose] public section

section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)


theorem _root_.GlobalTheory.T.local_additive_character_eq_adelic : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (x : w.adicCompletion E), psiAt w x = (localAdelicChar E w x : ℂ) := by
  first | exact @GlobalTheory.CompanionTheory.PsiStd.psiAt_eq_localAdelicChar | exact GlobalTheory.CompanionTheory.PsiStd.psiAt_eq_localAdelicChar | (intros; apply GlobalTheory.CompanionTheory.PsiStd.psiAt_eq_localAdelicChar <;> assumption)
end

section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem deriv_nonneg_of_nonneg_right {e : ℝ → ℝ} {e' : ℝ} (h : HasDerivAt e e' 0) (h0 : e 0 = 0)
    (hpos : ∀ t, 0 < t → 0 ≤ e t) : 0 ≤ e' := by
  refine ge_of_tendsto h.tendsto_slope_zero_right ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [zero_add, h0, sub_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr (le_of_lt ht)) (hpos t ht)

theorem isBoundedBilinearMap_re_form {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Q : H → H → ℂ) (Mb : ℝ) (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z)
    (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) (hconj : ∀ x y, Q y x = star (Q x y))
    (hbd : ∀ x y, ‖Q x y‖ ≤ Mb * ‖x‖ * ‖y‖) :
    IsBoundedBilinearMap ℝ (fun p : H × H => (Q p.1 p.2).re) := by
  have hsmulR : ∀ (c : ℝ) (x y : H), Q x (c • y) = (c : ℂ) * Q x y := fun c x y => by
    rw [← hsmul, Complex.coe_smul]
  have haddL : ∀ x₁ x₂ y, Q (x₁ + x₂) y = Q x₁ y + Q x₂ y := fun x₁ x₂ y => by
    rw [hconj, hadd, star_add, ← hconj, ← hconj]
  have hsmulL : ∀ (c : ℝ) (x y : H), Q (c • x) y = (c : ℂ) * Q x y := fun c x y => by
    rw [hconj, hsmulR, star_mul', ← hconj, show star (c : ℂ) = c from Complex.conj_ofReal c]
  refine ⟨fun x₁ x₂ y => ?_, fun c x y => ?_, fun x y₁ y₂ => ?_, fun c x y => ?_, ?_⟩
  · simp only [haddL, Complex.add_re]
  · simp only [hsmulL, Complex.re_ofReal_mul, smul_eq_mul]
  · simp only [hadd, Complex.add_re]
  · simp only [hsmulR, Complex.re_ofReal_mul, smul_eq_mul]
  · refine ⟨max Mb 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun x y => ?_⟩
    rw [Real.norm_eq_abs]
    calc |(Q x y).re| ≤ ‖Q x y‖ := Complex.abs_re_le_norm _
      _ ≤ Mb * ‖x‖ * ‖y‖ := hbd x y
      _ ≤ max Mb 1 * ‖x‖ * ‖y‖ := by gcongr; exact le_max_left _ _

theorem abs_two_re_form_dRep_le : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) (Q : H → H → ℂ) (Mb a : ℝ) (hadd : ∀ x y z, Q x (y + z) = Q x y + Q x z) (hsmul : ∀ (c : ℂ) x y, Q x (c • y) = c * Q x y) (hconj : ∀ x y, Q y x = star (Q x y)) (hbd : ∀ x y, ‖Q x y‖ ≤ Mb * ‖x‖ * ‖y‖) (hgrow : ∀ X ∈ HCSS.lieOf G, ∀ (t : ℝ) (x : H), (Q (π (NormedSpace.exp (t • X)) x) (π (NormedSpace.exp (t • X)) x)).re ≤ Real.exp (a * |t| * mnorm X) * (Q x x).re) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) {x : H} (hx : IsSmoothVec G π x), |2 * (Q (dRep π X x) x).re| ≤ a * mnorm X * (Q x x).re := by
  intro n G H _ _ π hG hrep Q Mb a hadd hsmul hconj hbd hgrow X hX x hx
  have hB := isBoundedBilinearMap_re_form Q Mb hadd hsmul hconj hbd
  have hv : HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) x) (dRep π X x) 0 :=
    (GlobalTheory.T.derived_action_of_smooth_vector hG hrep hx hX).1
  have hv0 : π (NormedSpace.exp ((0 : ℝ) • X)) x = x := by
    rw [zero_smul, NormedSpace.exp_zero, hrep.1]
    rfl
  set d := dRep π X x with hd
  set f : ℝ → ℝ := fun t => (Q (π (NormedSpace.exp (t • X)) x) (π (NormedSpace.exp (t • X)) x)).re with hf_def
  have hf : HasDerivAt f (2 * (Q d x).re) 0 := by
    have h1 := (hB.hasFDerivAt (π (NormedSpace.exp ((0 : ℝ) • X)) x, π (NormedSpace.exp ((0 : ℝ) • X)) x)).comp_hasDerivAt
      (0 : ℝ) (hv.prodMk hv)
    rw [hB.deriv_apply] at h1
    simp only [hv0] at h1
    have e : (Q x d).re + (Q d x).re = 2 * (Q d x).re := by
      rw [hconj d x, Complex.star_def, Complex.conj_re]
      ring
    rw [e] at h1
    exact h1
  have hf0 : f 0 = (Q x x).re := by
    simp only [hf_def, hv0]
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (a * t * mnorm X) * (Q x x).re) (a * mnorm X * (Q x x).re) 0 := by
    have h2 : HasDerivAt (fun t : ℝ => a * t * mnorm X) (a * 1 * mnorm X) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_mul a).mul_const (mnorm X)
    have h3 := (h2.exp).mul_const (Q x x).re
    simpa using h3
  have up : 2 * (Q d x).re ≤ a * mnorm X * (Q x x).re := by
    have := deriv_nonneg_of_nonneg_right (hexp.sub hf) (by simp [hf0]) (fun t ht => by
      have := hgrow X hX t x
      rw [abs_of_pos ht] at this
      simp only [hf_def, Pi.sub_apply]
      linarith)
    linarith
  have hfn : HasDerivAt (fun t : ℝ => f (-t)) (2 * (Q d x).re * -1) 0 := by
    have hf' : HasDerivAt f (2 * (Q d x).re) (-(0 : ℝ)) := by rwa [neg_zero]
    exact hf'.comp (0 : ℝ) (hasDerivAt_neg (0 : ℝ))
  have low : -(a * mnorm X * (Q x x).re) ≤ 2 * (Q d x).re := by
    have := deriv_nonneg_of_nonneg_right (hexp.sub hfn) (by simp [hf0]) (fun t ht => by
      have := hgrow X hX (-t) x
      rw [abs_neg, abs_of_pos ht] at this
      simp only [hf_def, Pi.sub_apply]
      linarith)
    linarith
  rw [abs_le]
  exact ⟨low, up⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA
end

section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel Formalism.ConjugateSelfDual

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler


open PositivityTheory.LocalTateOrthogonality.Gcoh in
theorem card_H1_eq_card_H0_mul_card_H2 (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (hK : FiniteDimensional ℚ_[p] K) (l : ℕ) [hl : Fact l.Prime] (hlp : l ≠ p) (r : ℕ) (M : Type)
    [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK p K) M) (hrho : ContAction rho) :
    Nat.card (H1 rho) = Nat.card (H0 rho) * Nat.card (H2 rho) := by
  obtain ⟨hsep, v, t, hloc, hcard⟩ := gcField p K hK
  obtain ⟨A, hA, e, he⟩ := gcRep _ _ M rho hrho
  obtain ⟨e0, -⟩ := gc0 _ _ M rho A e he
  obtain ⟨e1, -⟩ := gc1 _ _ M rho A e he
  obtain ⟨e2, -⟩ := gc2 _ _ M rho A e he
  obtain ⟨k, hk⟩ := exists_card_eq_pow l r M
  have hfA : Finite A := Finite.of_equiv M e.toEquiv
  have hA' : Nat.card A = l ^ k := (Nat.card_congr e.toEquiv).symm.trans hk
  have : CharZero K := algebraRat.charZero K
  have hne : ((Nat.card A : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hE := @card_cohomology_mul_div_eq K (PadicAlgCl p) _ v t hloc _ _ hsep A hA hfA hne
  have hfin := @finite_cohomology_localField K (PadicAlgCl p) _ v t hloc _ _ hsep A hA hfA hne 1
  have hcop : Nat.Coprime (Nat.card A) p := by
    rw [hA']
    exact Nat.Coprime.pow_left k ((Nat.coprime_primes hl.out Fact.out).2 hlp)
  have hu : IsUnit ((Nat.card A : ℕ) : 𝒪[K]) := by
    obtain ⟨a, b, hab⟩ := hcop.cast (R := 𝒪[K])
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one hab with h | h
    · exact isUnit_of_mul_isUnit_right h
    · exfalso
      have h3 := hcard 1
      rw [pow_one, card_quotient_span_eq_one_of_isUnit (isUnit_of_mul_isUnit_right h)] at h3
      have h4 : 1 < p ^ Module.finrank ℚ_[p] K :=
        Nat.one_lt_pow Module.finrank_pos.ne' (Fact.out : p.Prime).one_lt
      omega
  rw [card_quotient_span_eq_one_of_isUnit hu, Nat.cast_one, inv_one] at hE
  rw [Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv]
  have hp1 : (Nat.card (cohomology A 1) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  apply Nat.cast_injective (R := ℚ)
  rw [Nat.cast_mul]
  exact ((div_eq_one_iff_eq hp1).1 hE).symm

theorem exists_prime_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hmax := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 F ⧸ v.asIdeal)
  refine ⟨p, CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) p, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem localEulerChar_holds : ReciprocityTheory.Gal.LocalEulerChar := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ A rho v hr hA hc
  have hval : ∀ (p : ℕ), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → A.valuation (p : Ω) < 1 := fun p hp => by
    simpa using (hA (p : 𝓞 F)).2 hp
  refine ⟨fun hl => ?_, fun hl => ?_⟩
  · obtain ⟨K, hK, i0, -, -, hdeg⟩ := GlobalTheory.DecLocal.decEquiv (p := l) (F := F) A (hval l hl)
    let i : ↥(Dec (F := F) A) ≃ₜ* Formalism.GaloisCohomology.GK l K := i0
    let rhoK : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK l K) M := rho.comp i.symm.toMulEquiv.toMonoidHom
    have hcomp : ∀ h m, rhoK (i h) m = rho h m := fun h m =>
      congrArg (fun g => rho g m) (i.symm_apply_apply h)
    have hcK : ContAction rhoK := hc.comp' i.symm.continuous
    have h := PositivityTheory.LocalTateOrthogonality.Gcoh.top_euler l K hK r M rhoK hr hcK
    rw [hdeg v hA] at h
    rw [← Nat.card_congr (ReciprocityTheory.Neutral.Bridge.equivH0OfIso i rhoK rho hcomp).toEquiv,
      ← Nat.card_congr (ReciprocityTheory.Neutral.Bridge.equivH1OfIso i rhoK rho hcomp).toEquiv,
      ← Nat.card_congr (ReciprocityTheory.Neutral.Bridge.equivH2OfIso i rhoK rho hcomp).toEquiv]
    exact h
  · obtain ⟨p, hp, hpv⟩ := exists_prime_mem v
    haveI : Fact p.Prime := ⟨hp⟩
    have hlp : l ≠ p := fun h => hl (h ▸ hpv)
    obtain ⟨K, hK, i0, -, -, -⟩ := GlobalTheory.DecLocal.decEquiv (p := p) (F := F) A (hval p hpv)
    let i : ↥(Dec (F := F) A) ≃ₜ* Formalism.GaloisCohomology.GK p K := i0
    let rhoK : Representation (ZMod (l ^ r)) (Formalism.GaloisCohomology.GK p K) M := rho.comp i.symm.toMulEquiv.toMonoidHom
    have hcomp : ∀ h m, rhoK (i h) m = rho h m := fun h m =>
      congrArg (fun g => rho g m) (i.symm_apply_apply h)
    have hcK : ContAction rhoK := hc.comp' i.symm.continuous
    have h := card_H1_eq_card_H0_mul_card_H2 p K hK l hlp r M rhoK hcK
    rw [← Nat.card_congr (ReciprocityTheory.Neutral.Bridge.equivH0OfIso i rhoK rho hcomp).toEquiv,
      ← Nat.card_congr (ReciprocityTheory.Neutral.Bridge.equivH1OfIso i rhoK rho hcomp).toEquiv,
      ← Nat.card_congr (ReciprocityTheory.Neutral.Bridge.equivH2OfIso i rhoK rho hcomp).toEquiv]
    exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler
end
end
