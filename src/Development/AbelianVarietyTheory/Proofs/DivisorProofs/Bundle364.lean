module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle310
public import Mathlib.RingTheory.Idempotents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle102
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle319
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle294
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle003
import Mathlib.Topology.Sheaves.Presheaf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle004

@[expose] public section

section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.GalSec.Tens

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]


open Classical in
def conj (θ : Ω) : Finset Ω := by
  classical
  exact ((minpoly K θ).aroots Ω).toFinset

def DependsOn (k : ℕ) (θ : Ω) (φ : LCRing K Ω k) : Prop :=
  ∀ g g' : Fin k → (Ω ≃ₐ[K] Ω), (∀ i, g i θ = g' i θ) → φ g = φ g'


open Classical in
def pick (k : ℕ) (θ : Ω) (t : Fin k → Ω) : Fin k → (Ω ≃ₐ[K] Ω) := by
  classical
  exact if h : ∃ g : Fin k → (Ω ≃ₐ[K] Ω), ∀ i, g i θ = t i then h.choose else 1

variable {K Ω}
variable {B : Type} [CommRing B]


open Classical in
def idem (g₀ : Ω →+* B) (θ : Ω) (b : B) (s : conj K Ω θ) : B := by
  classical
  exact g₀ (∏ j ∈ (Finset.univ : Finset (conj K Ω θ)).erase s, ((s : Ω) - (j : Ω)))⁻¹ *
    ∏ j ∈ (Finset.univ : Finset (conj K Ω θ)).erase s, (b - g₀ (j : Ω))

def lev (g₀ : Ω →+* B) {k : ℕ} (gs : Fin k → (Ω →+* B)) (θ : Ω) (φ : LCRing K Ω k) : B :=
  ∑ t : Fin k → conj K Ω θ, g₀ (φ (pick K Ω k θ (fun i => (t i : Ω)))) * ∏ i, idem g₀ θ (gs i θ) (t i)

end GlobalTheory.EtC.GalSec.Tens

namespace GlobalTheory.EtC.GalSec.Tens

open Polynomial

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

theorem mem_conj_iff [Algebra.IsAlgebraic K Ω] [Normal K Ω] (θ s : Ω) :
    s ∈ conj K Ω θ ↔ ∃ σ : Ω ≃ₐ[K] Ω, σ θ = s := by
  classical
  have hne : minpoly K θ ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral θ)
  simp only [conj, Multiset.mem_toFinset, mem_aroots, ne_eq, hne, not_false_eq_true, true_and]
  constructor
  · intro h
    have hm : minpoly K s = minpoly K θ :=
      (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible (Algebra.IsIntegral.isIntegral θ)) h
        (minpoly.monic (Algebra.IsIntegral.isIntegral θ))).symm
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit Ω).1 hm
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, rfl⟩
    rw [aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval, map_zero]

theorem self_mem_conj [Algebra.IsAlgebraic K Ω] [Normal K Ω] (θ : Ω) : θ ∈ conj K Ω θ :=
  (mem_conj_iff θ θ).2 ⟨1, rfl⟩

theorem prod_conj [Algebra.IsAlgebraic K Ω] [Normal K Ω] [Algebra.IsSeparable K Ω] (θ : Ω) :
    ∏ s ∈ conj K Ω θ, (X - C s) = (minpoly K θ).map (algebraMap K Ω) := by
  classical
  have hint := Algebra.IsIntegral.isIntegral (R := K) θ
  have hsp : Splits ((minpoly K θ).map (algebraMap K Ω)) := Normal.splits inferInstance θ
  have hmo : ((minpoly K θ).map (algebraMap K Ω)).Monic := (minpoly.monic hint).map _
  have hnd : ((minpoly K θ).map (algebraMap K Ω)).roots.Nodup :=
    nodup_roots (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable K θ))
  conv_rhs => rw [hsp.eq_prod_roots_of_monic hmo]
  rw [conj, aroots, Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnd.dedup]

end GlobalTheory.EtC.GalSec.Tens

namespace GlobalTheory.EtC.GalSec.Tens

open Polynomial

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

theorem apply_mem_conj [Algebra.IsAlgebraic K Ω] [Normal K Ω] (θ : Ω) (σ : Ω ≃ₐ[K] Ω) :
    σ θ ∈ conj K Ω θ :=
  (mem_conj_iff θ (σ θ)).2 ⟨σ, rfl⟩

theorem prod_sub_conj_eq_zero [Algebra.IsAlgebraic K Ω] [Normal K Ω] [Algebra.IsSeparable K Ω]
    {B : Type} [CommRing B] (g₀ σ' : Ω →+* B)
    (h : σ'.comp (algebraMap K Ω) = g₀.comp (algebraMap K Ω)) (θ : Ω) :
    ∏ s ∈ conj K Ω θ, (σ' θ - g₀ s) = 0 := by
  have h1 : (∏ s ∈ conj K Ω θ, (X - C s)).eval₂ g₀ (σ' θ) = ∏ s ∈ conj K Ω θ, (σ' θ - g₀ s) := by
    rw [eval₂_finsetProd]
    simp
  rw [← h1, prod_conj, eval₂_map, ← h, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]

theorem idem_spec [Algebra.IsAlgebraic K Ω] [Normal K Ω] {B : Type} [CommRing B] (g₀ : Ω →+* B)
    (θ : Ω) (b : B) (hb : ∏ s ∈ conj K Ω θ, (b - g₀ s) = 0) :
    CompleteOrthogonalIdempotents (idem (K := K) g₀ θ b) ∧ (∀ s : conj K Ω θ, b * idem (K := K) g₀ θ b s = g₀ s * idem (K := K) g₀ θ b s) ∧
      b = ∑ s : conj K Ω θ, g₀ s * idem (K := K) g₀ θ b s := by
  classical
  letI : Algebra Ω B := g₀.toAlgebra
  haveI : Nonempty (conj K Ω θ) := ⟨⟨θ, self_mem_conj θ⟩⟩
  have hid : idem (K := K) g₀ θ b = GlobalTheory.Pat.lagIdem b (fun j : conj K Ω θ => (j : Ω)) := by
    funext s
    rw [idem, GlobalTheory.Pat.lagIdem, Ring.inverse_eq_inv', Algebra.smul_def, map_prod]
    simp only [map_sub, aeval_X, aeval_C, RingHom.algebraMap_toAlgebra]
  have hu : ∀ i j : conj K Ω θ, i ≠ j → IsUnit ((i : Ω) - j) := fun i j h =>
    (sub_ne_zero.2 (Subtype.coe_injective.ne h)).isUnit
  have hP : aeval b (∏ j : conj K Ω θ, (X - C (j : Ω))) = 0 := by
    rw [map_prod]
    simp only [map_sub, aeval_X, aeval_C, RingHom.algebraMap_toAlgebra]
    rw [Finset.prod_coe_sort (conj K Ω θ) (fun s => b - g₀ s)]
    exact hb
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.lagIdem_spec Ω B (conj K Ω θ) b _ hu hP
  rw [hid]
  refine ⟨h1, fun s => ?_, ?_⟩
  · rw [h2 s, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  · conv_lhs => rw [h3]
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra]

theorem pick_spec [Algebra.IsAlgebraic K Ω] [Normal K Ω] (k : ℕ) (θ : Ω) (t : Fin k → Ω)
    (ht : ∀ i, t i ∈ conj K Ω θ) (i : Fin k) : pick K Ω k θ t i θ = t i := by
  have hex : ∃ g : Fin k → (Ω ≃ₐ[K] Ω), ∀ i, g i θ = t i := by
    choose g hg using fun i => (mem_conj_iff θ (t i)).1 (ht i)
    exact ⟨g, hg⟩
  classical
  rw [pick, dite_eq_left hex]
  exact hex.choose_spec i

end GlobalTheory.EtC.GalSec.Tens

end
end

section

open GlobalTheory.Nef

namespace GlobalTheory.Nef.PathJet

open PowerSeries

section Coeff

variable {R : Type} [CommRing R]

private lemma coeff_eq_of_X_pow_dvd_sub {n i : ℕ} {a b : PowerSeries R}
    (h : (X : PowerSeries R) ^ n ∣ a - b) (hi : i < n) : coeff i a = coeff i b := by
  rw [X_pow_dvd_iff] at h
  have := h i hi
  rwa [map_sub, sub_eq_zero] at this

private lemma coeff_mul_of_X_pow_dvd' {n : ℕ} {u : PowerSeries R} (hu : (X : PowerSeries R) ^ n ∣ u)
    (h : PowerSeries R) : coeff n (u * h) = coeff n u * coeff 0 h := by
  obtain ⟨k, rfl⟩ := hu
  rw [mul_assoc, coeff_X_pow_mul', coeff_X_pow_mul', if_pos le_rfl, if_pos le_rfl, Nat.sub_self]
  simp only [coeff_zero_eq_constantCoeff_apply, map_mul]

private lemma X_pow_dvd_rescale' {k : ℕ} {p : PowerSeries R} (a : R)
    (h : (X : PowerSeries R) ^ k ∣ p) : (X : PowerSeries R) ^ k ∣ rescale a p := by
  rw [X_pow_dvd_iff] at h ⊢
  intro i hi
  rw [coeff_rescale, h i hi, mul_zero]

end Coeff

theorem exists_jet_succ_of_lift (A B R : Type) [CommRing A] [CommRing B] [CommRing R] [Algebra ℚ R]
    (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R)
    (hεπ : ε.comp π = RingHom.id B) (hmπ : m.comp π = π) (hεm : ε.comp m = ε)
    (hm2 : ∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2)
    (_hδ : ∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) (_hδπ : ∀ a, δ (π a) = 0)
    (n : ℕ) (hn : 2 ≤ n) (φ ψ : A → PowerSeries R) (hφ : IsJet π ε m β δ n φ)
    (hψ : IsRingHomMod π β (n + 1) ψ) (hψφ : ∀ f, (X : PowerSeries R) ^ n ∣ ψ f - φ f) :
    ∃ ψ' : A → PowerSeries R, IsJet π ε m β δ (n + 1) ψ' ∧
      ∀ f, (X : PowerSeries R) ^ n ∣ ψ' f - φ f := by
  obtain ⟨-, hφm, hφ0, hφ1⟩ := hφ
  obtain ⟨hψmul, hψadd, hψone, hψπ⟩ := hψ
  have hεmf : ∀ f, ε (m f) = ε f := fun f => by rw [← RingHom.comp_apply, hεm]
  have hmπf : ∀ b, m (π b) = π b := fun b => by rw [← RingHom.comp_apply, hmπ]
  have hψ0 : ∀ f, coeff 0 (ψ f) = β (ε f) := fun f => by
    rw [coeff_eq_of_X_pow_dvd_sub (hψφ f) (by omega), coeff_zero_eq_constantCoeff_apply, hφ0]

  obtain ⟨u, hu_def⟩ : ∃ u : A → PowerSeries R, ∀ f, u f = ψ (m f) - rescale 2 (ψ f) :=
    ⟨_, fun _ => rfl⟩
  have hu : ∀ f, (X : PowerSeries R) ^ n ∣ u f := fun f => by
    have e : u f = (ψ (m f) - φ (m f)) + (φ (m f) - rescale 2 (φ f)) - rescale 2 (ψ f - φ f) := by
      rw [hu_def, map_sub]; ring
    rw [e]
    exact dvd_sub (dvd_add (hψφ _) (hφm f)) (X_pow_dvd_rescale' _ (hψφ f))
  obtain ⟨D, hD_def⟩ : ∃ D : A → R, ∀ f, D f = coeff n (u f) := ⟨_, fun _ => rfl⟩
  have hDadd : ∀ f g, D (f + g) = D f + D g := fun f g => by
    simp only [hD_def]
    rw [← map_add (f := _)]
    apply coeff_eq_of_X_pow_dvd_sub _ (Nat.lt_succ_self n)
    have e : u (f + g) - (u f + u g) =
        (ψ (m f + m g) - (ψ (m f) + ψ (m g))) - rescale 2 (ψ (f + g) - (ψ f + ψ g)) := by
      simp only [hu_def, map_add (f := _), map_sub]; ring
    rw [e]
    exact dvd_sub (hψadd _ _) (X_pow_dvd_rescale' _ (hψadd _ _))
  have hDmul : ∀ f g, D (f * g) = β (ε f) * D g + β (ε g) * D f := fun f g => by
    have e1 : (X : PowerSeries R) ^ (n + 1) ∣
        u (f * g) - (u f * ψ (m g) + rescale 2 (ψ f) * u g) := by
      have e : u (f * g) - (u f * ψ (m g) + rescale 2 (ψ f) * u g) =
          (ψ (m f * m g) - ψ (m f) * ψ (m g)) - rescale 2 (ψ (f * g) - ψ f * ψ g) := by
        simp only [hu_def, map_mul, map_sub]; ring
      rw [e]
      exact dvd_sub (hψmul _ _) (X_pow_dvd_rescale' _ (hψmul _ _))
    simp only [hD_def]
    rw [coeff_eq_of_X_pow_dvd_sub e1 (Nat.lt_succ_self n), map_add (f := _),
      coeff_mul_of_X_pow_dvd' (hu f), mul_comm (rescale 2 (ψ f)), coeff_mul_of_X_pow_dvd' (hu g)]
    rw [coeff_rescale, pow_zero, one_mul, hψ0, hψ0, hεmf]
    ring
  have hDπ : ∀ b, D (π b) = 0 := fun b => by
    rw [hD_def, hu_def, hmπf, map_sub, coeff_rescale,
      coeff_eq_of_X_pow_dvd_sub (hψπ b) (Nat.lt_succ_self n), coeff_C, if_neg (by omega)]
    ring
  obtain ⟨c, hc⟩ : ∃ c : R, c * ((2 : R) ^ n - 2) = 1 := by
    have h4 : (4 : ℚ) ≤ 2 ^ n := by
      calc (4 : ℚ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hn
    have hne : (2 : ℚ) ^ n - 2 ≠ 0 := by intro h; linarith
    refine ⟨algebraMap ℚ R ((2 : ℚ) ^ n - 2)⁻¹, ?_⟩
    have e : ((2 : R) ^ n - 2) = algebraMap ℚ R ((2 : ℚ) ^ n - 2) := by
      rw [map_sub, map_pow, map_ofNat]
    rw [e, ← map_mul, inv_mul_cancel₀ hne, map_one]
  obtain ⟨E, hE⟩ : ∃ E : A →+ R, ∀ f, E f = c * D f :=
    ⟨AddMonoidHom.mk' (fun f => c * D f) (fun f g => by rw [hDadd]; ring), fun _ => rfl⟩
  have hEmul : ∀ f g, E (f * g) = β (ε f) * E g + β (ε g) * E f := fun f g => by
    rw [hE, hE, hE, hDmul]; ring
  have hEπ : ∀ b, E (π b) = 0 := fun b => by rw [hE, hDπ, mul_zero]
  have hEm : ∀ f, E (m f) = 2 * E f := deriv_comp_m π ε m β E hεπ hmπ hm2 hEmul hEπ
  refine ⟨fun f => ψ f + C (E f) * X ^ n, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
  · intro f g
    have e : ψ (f * g) + C (E (f * g)) * X ^ n - (ψ f + C (E f) * X ^ n) * (ψ g + C (E g) * X ^ n) =
        (ψ (f * g) - ψ f * ψ g) + X ^ n * (C (E (f * g)) - C (E f) * ψ g - C (E g) * ψ f) -
          C (E f) * C (E g) * (X ^ n * X ^ n) := by ring
    rw [e]
    refine dvd_sub (dvd_add (hψmul f g) ?_) ?_
    · rw [pow_succ]
      apply mul_dvd_mul_left
      rw [X_dvd_iff, ← coeff_zero_eq_constantCoeff_apply]
      simp only [map_sub, coeff_zero_C, coeff_C_mul, hψ0, hEmul]
      ring
    · apply dvd_mul_of_dvd_right
      rw [← pow_add]
      exact pow_dvd_pow _ (by omega)
  · intro f g
    convert hψadd f g using 1
    simp only [map_add (f := _)]
    ring
  · convert hψone using 1
    dsimp only
    rw [show E 1 = 0 by rw [← map_one π, hEπ]]
    simp
  · intro b
    convert hψπ b using 1
    dsimp only
    rw [hEπ]
    simp
  · intro f
    rw [X_pow_dvd_iff]
    intro i hi
    simp only [map_sub, map_add (f := _), coeff_rescale, coeff_C_mul_X_pow]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · rw [if_neg h.ne, if_neg h.ne]
      have := (X_pow_dvd_iff.mp (hu f)) i h
      rw [hu_def, map_sub, coeff_rescale] at this
      linear_combination this
    · rw [h, if_pos rfl, if_pos rfl, hEm, hE, hD_def, hu_def, map_sub, coeff_rescale]
      linear_combination (-(coeff n (ψ (m f)) - 2 ^ n * coeff n (ψ f))) * hc
  · intro f
    rw [← coeff_zero_eq_constantCoeff_apply, map_add (f := _), coeff_C_mul_X_pow, if_neg (by omega),
      add_zero, hψ0]
  · intro f
    rw [map_add (f := _), coeff_C_mul_X_pow, if_neg (by omega), add_zero,
      coeff_eq_of_X_pow_dvd_sub (hψφ f) (by omega), hφ1]
  · intro f
    have e : ψ f + C (E f) * X ^ n - φ f = (ψ f - φ f) + C (E f) * X ^ n := by ring
    rw [e]
    exact dvd_add (hψφ f) (dvd_mul_left _ _)

end GlobalTheory.Nef.PathJet
end

section

open GlobalTheory.Nef

namespace GlobalTheory.Nef.PathJet

open PowerSeries

theorem firstOrder_isJet : ∀ (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A) (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R), ε.comp π = RingHom.id B → m.comp π = π → ε.comp m = ε → (∀ f ∈ RingHom.ker ε, m f - 2 * f ∈ RingHom.ker ε ^ 2) → (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) → (∀ a, δ (π a) = 0) → GlobalTheory.Nef.PathJet.IsJet π ε m β δ 2 (fun f => PowerSeries.C (β (ε f)) + PowerSeries.C (δ f) * PowerSeries.X) := by
  intro A B R _ _ _ π ε m β δ hεπ hmπ hεm hm2 hδ hδπ
  have hεπ' : ∀ b, ε (π b) = b := fun b => by rw [← RingHom.comp_apply, hεπ, RingHom.id_apply]
  have hεm' : ∀ f, ε (m f) = ε f := fun f => by rw [← RingHom.comp_apply, hεm]
  have hδ1 : δ 1 = 0 := by
    have h := hδ 1 1
    simp only [mul_one, map_one, one_mul] at h
    have : δ 1 + δ 1 = δ 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  have hdm : ∀ f, δ (m f) = 2 * δ f :=
    deriv_comp_m π ε m β δ hεπ hmπ hm2 hδ hδπ
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro f g
    refine ⟨C (-(δ f * δ g)), ?_⟩
    beta_reduce
    rw [hδ, map_mul, map_mul]
    simp only [map_add (f := _), map_mul, map_neg]
    ring
  · intro f g
    simp [map_add (f := _)]
    exact ⟨0, by ring⟩
  · simp [hδ1]
  · intro b
    simp [hεπ', hδπ]
  · intro f
    refine ⟨0, ?_⟩
    beta_reduce
    rw [hεm', hdm]
    have hrC : ∀ x : R, rescale (2 : R) (C x) = C x := by
      intro x; ext n; rw [coeff_rescale, coeff_C]; split_ifs with h <;> simp [h]
    simp only [map_add (f := _), map_mul, rescale_X, hrC]
    ring
  · intro f
    simp
  · intro f
    simp [coeff_C, coeff_C_mul, coeff_X]

end GlobalTheory.Nef.PathJet
end

section

open GlobalTheory.Nef

namespace GlobalTheory.Nef.PathJet

open PowerSeries

theorem limit_of_jets (A B R : Type) [CommRing A] [CommRing B] [CommRing R] (π : B →+* A)
    (ε : A →+* B) (m : A →+* A) (β : B →+* R) (δ : A →+ R) (φ : ℕ → A → PowerSeries R)
    (hφ : ∀ n, IsJet π ε m β δ (n + 2) (φ n))
    (hc : ∀ n f, (X : PowerSeries R) ^ (n + 2) ∣ φ (n + 1) f - φ n f) :
    ∃ γ : A →+* PowerSeries R, γ.comp π = PowerSeries.C.comp β ∧
      PowerSeries.constantCoeff.comp γ = β.comp ε ∧ (∀ f, PowerSeries.coeff 1 (γ f) = δ f) ∧
      (PowerSeries.rescale 2).comp γ = γ.comp m := by

  have hdv : ∀ (n : ℕ) (p q : PowerSeries R), (X : PowerSeries R) ^ n ∣ p - q →
      ∀ k, k < n → coeff k p = coeff k q := by
    intro n p q h k hk
    have := (PowerSeries.X_pow_dvd_iff.mp h) k hk
    rwa [map_sub, sub_eq_zero] at this

  have hstab : ∀ f k j, k ≤ j + 1 → coeff k (φ j f) = coeff k (φ k f) := by
    intro f k j hkj
    rcases Nat.lt_or_ge j k with h | h
    · have hk : k = j + 1 := by omega
      subst hk
      exact (hdv _ _ _ (hc j f) (j + 1) (by omega)).symm
    · induction j, h using Nat.le_induction with
      | base => rfl
      | succ j hj ih =>
        rw [hdv _ _ _ (hc j f) k (by omega)]
        exact ih (by omega)
  let g : A → PowerSeries R := fun f => PowerSeries.mk fun k => coeff k (φ k f)
  have hg : ∀ f k j, k ≤ j + 1 → coeff k (g f) = coeff k (φ j f) := by
    intro f k j hkj
    simp only [g, PowerSeries.coeff_mk]
    exact (hstab f k j hkj).symm
  have gmul : ∀ f h, g (f * h) = g f * g h := by
    intro f h; ext k
    rw [hg _ k k (by omega), hdv _ _ _ ((hφ k).1.1 f h) k (by omega), coeff_mul, coeff_mul]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [hg f x.1 k (by omega), hg h x.2 k (by omega)]
  have gadd : ∀ f h, g (f + h) = g f + g h := by
    intro f h; ext k
    rw [hg _ k k (by omega), hdv _ _ _ ((hφ k).1.2.1 f h) k (by omega), map_add (f := _), map_add (f := _),
      hg f k k (by omega), hg h k k (by omega)]
  have gone : g 1 = 1 := by
    ext k
    rw [hg _ k k (by omega), hdv _ _ _ (hφ k).1.2.2.1 k (by omega)]
  have gzero : g 0 = 0 := by
    have := gadd 0 0
    rw [add_zero] at this
    linear_combination -this
  let γ : A →+* PowerSeries R :=
    { toFun := g, map_one' := gone, map_mul' := gmul, map_zero' := gzero, map_add' := gadd }
  refine ⟨γ, ?_, ?_, ?_, ?_⟩
  · ext b k
    show coeff k (g (π b)) = coeff k (C (β b))
    rw [hg _ k k (by omega), hdv _ _ _ ((hφ k).1.2.2.2 b) k (by omega)]
  · ext f
    show constantCoeff (g f) = β (ε f)
    rw [← coeff_zero_eq_constantCoeff_apply, hg f 0 0 (by omega), coeff_zero_eq_constantCoeff_apply,
      (hφ 0).2.2.1 f]
  · intro f
    show coeff 1 (g f) = δ f
    rw [hg f 1 0 (by omega), (hφ 0).2.2.2 f]
  · ext f k
    show coeff k (rescale 2 (g f)) = coeff k (g (m f))
    rw [coeff_rescale, hg f k k (by omega), hg (m f) k k (by omega),
      hdv _ _ _ ((hφ k).2.1 f) k (by omega), coeff_rescale]

end GlobalTheory.Nef.PathJet
end

section

noncomputable section
namespace GlobalTheory.SUVol
open NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

instance instMeasurableSpaceRealSU (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) :
    MeasurableSpace (realSU Ψ G) := borel _
instance instBorelSpaceRealSU (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) :
    BorelSpace (realSU Ψ G) := ⟨rfl⟩
end GlobalTheory.SUVol
end
end

section

open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate

theorem _root_.GlobalTheory.T.continuous_metaplectic_schwartz_action_prod : ∀ (l : Type) [Fintype l] [DecidableEq l] (G : Type) [Group G] [TopologicalSpace G] (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l)), Continuous pr → (∀ f : L2 l, Continuous fun g => om g f) → (∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l), om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f)) → (∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) → Continuous fun x : G × Sch l => omS x.1 x.2 := by
  first | exact @GlobalTheory.RealWeil.continuous_omS_prod | exact GlobalTheory.RealWeil.continuous_omS_prod | (intros; apply GlobalTheory.RealWeil.continuous_omS_prod <;> assumption)
end
