module

public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorExponentAtPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteGaloisInertiaLiftsAbsoluteInertiaRat
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalEmbeddingOverPlace
public import Mathlib.Algebra.Polynomial.SpecificDegree
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.IntegralCasts.IsOpenStabOfMemNhds
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal

namespace GlobalTheory.SqrtNegRam

open Polynomial

theorem valuation_natCast_eq {F : Type} [Field F] [NumberField F] {p : ℕ} (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ discr F) (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    v.valuation F (p : F) = WithZero.exp (-1 : ℤ) := by
  have h2 := GlobalTheory.LamTie.ExpCond.not_mem_sq_of_not_dvd_discr hp hd v hv
  have e : (p : F) = algebraMap (𝓞 F) F (p : 𝓞 F) := by simp
  rw [e, v.valuation_of_algebraMap]
  have h0 : ((p : ℕ) : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hne := v.intValuation_ne_zero _ h0
  have h1 := (v.intValuation_le_pow_iff_mem _ 1).2 (by simpa using hv)
  have h2' := mt (v.intValuation_le_pow_iff_mem _ 2).1 h2
  rw [← WithZero.exp_log hne] at h1 h2' ⊢
  rw [WithZero.exp_le_exp] at h1 h2'
  rw [WithZero.exp_inj]
  push_cast at h1 h2'
  omega

theorem valuation_mul_ne_one {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {p : ℕ} (hp : p.Prime) (hd : ¬ (p : ℤ) ∣ discr F) {δ : Ω}
    (hδ : δ ^ 2 = -(p : Ω)) {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}
    (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) (hA : IsPlaceOver A v) (y : F) (hy : y ≠ 0) :
    A.valuation (algebraMap F Ω y * δ) ≠ 1 := by
  intro h
  obtain ⟨ι, hι⟩ := GlobalTheory.LocDict.exists_isLocEmb F Ω A v hA
  have hmem : ∀ e : F, algebraMap F Ω e ∈ A ↔ v.valuation F e ≤ 1 := fun e => by
    rw [hι, ι.commutes]; exact GlobalTheory.LocEmbExist.isIntegral_algebraMap_iff v e
  have he : algebraMap F Ω (y ^ 2 * p) = -(algebraMap F Ω y * δ) ^ 2 := by
    rw [mul_pow, hδ, map_mul, map_pow, map_natCast]; ring
  have hw : A.valuation (algebraMap F Ω (y ^ 2 * p)) = 1 := by
    rw [he, Valuation.map_neg, map_pow, h, one_pow]
  have h1 : v.valuation F (y ^ 2 * p) ≤ 1 := (hmem _).1 ((A.valuation_le_one_iff _).1 hw.le)
  have h2 : v.valuation F (y ^ 2 * p)⁻¹ ≤ 1 :=
    (hmem _).1 ((A.valuation_le_one_iff _).1 (by rw [map_inv₀, map_inv₀, hw, inv_one]))
  have hy0 : v.valuation F y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [map_inv₀] at h2
  rw [map_mul, map_pow, valuation_natCast_eq hp hd v hv, ← WithZero.exp_log hy0,
    ← WithZero.exp_nsmul, ← WithZero.exp_add] at h1 h2
  rw [← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at h2
  rw [← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  rw [nsmul_eq_mul] at h1 h2
  push_cast at h1 h2
  omega

end GlobalTheory.SqrtNegRam

namespace GlobalTheory.SqrtNegRam

open Polynomial

theorem sqrt_neg_moved_by_inertia : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (p : ℕ), p.Prime → p ≠ 2 → ¬ (p : ℤ) ∣ discr F → ∀ (δ : Ω), δ ^ 2 = -(p : Ω) → ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), ((p : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∃ s ∈ Ine (F := F) A, s δ ≠ δ := by
  intro F Ω _ _ _ _ _ p hp _ hd δ hδ v A hv hA
  have hp2 := GlobalTheory.LamTie.ExpCond.not_mem_sq_of_not_dvd_discr hp hd v hv
  refine GlobalTheory.InertiaMovesRoot.exists_mem_Ine_apply_ne F Ω A v hA 2 Nat.prime_two
    (-(p : 𝓞 F)) (neg_mem hv) (fun h => hp2 (by simpa only [neg_neg] using neg_mem h)) δ ?_
  simpa using hδ

end GlobalTheory.SqrtNegRam
