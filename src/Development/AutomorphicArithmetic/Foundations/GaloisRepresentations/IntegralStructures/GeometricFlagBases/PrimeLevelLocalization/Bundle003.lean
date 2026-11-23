module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.Bundle001
import Formalism.LocalToGlobal.Columns.StdLatUnimodular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
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

@[expose] public section

section

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL satEig)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc GLw AfQ sim mat comp rat loc lev SameK IsCen Shape IsForm IsKap mOf)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.Int.Geo.Pl

private theorem prime_under {E : Type} [Field E] [NumberField E] (u : Plc E) : ∃ l : ℕ, l.Prime ∧ (l : 𝓞 E) ∈ u.asIdeal := by
  haveI := u.isPrime
  haveI : Finite (𝓞 E ⧸ u.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ u.ne_bot
  refine ⟨ringChar (𝓞 E ⧸ u.asIdeal), CharP.char_is_prime (𝓞 E ⧸ u.asIdeal) _, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
  rw [map_natCast]
  exact (ringChar.spec _ _).2 dvd_rfl

private theorem span_le_pow {R : Type} [CommRing R] {I : Ideal R} {l m e : ℕ} (hl : (l : R) ∈ I) (h : l ^ e ∣ m) :
    Ideal.span {(m : R)} ≤ I ^ e := by
  obtain ⟨c, rfl⟩ := h
  rw [Ideal.span_singleton_le_iff_mem, Nat.cast_mul, Nat.cast_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hl e)

private theorem pow_le_prod {R ι : Type} [CommRing R] (T : Finset ι) (f : ι → Ideal R) (I : Ideal R) (e : ℕ) (h : ∀ u ∈ T, I ≤ f u) :
    I ^ (e * T.card) ≤ ∏ u ∈ T, f u ^ e := by
  rw [pow_mul, ← Finset.prod_const]
  exact Finset.prod_le_prod' fun u hu => Ideal.pow_right_mono (h u hu) e

private theorem prod_le_one {R ι : Type} [CommRing R] (T : Finset ι) (f : ι → Ideal R) (u : ι) (hu : u ∈ T) : ∏ u ∈ T, f u ≤ f u :=
  Ideal.le_of_dvd (Finset.dvd_prod_of_mem f hu)

theorem siteEx_of (hS : Sides) (hD : Dict) (hL : LevBasic) (hSt : StabOf) : SiteEx := by
  intro E _ _ _ A n p hp S F x U w₀ Up V hx hoff Q q hQ c hc hcp
  obtain ⟨T, e, hT, hst⟩ := hSt E A n p S F x U w₀ Up V hoff
  have key : ∀ (𝔟 : Ideal (𝓞 E)) (K : Subgroup S.G.GAf), 𝔟 ≠ ⊥ → (∀ u ∈ T, 𝔟 ≤ u.asIdeal ^ e) → IsLev S.L 𝔟 K →
      ∀ k ∈ K, Stab F V k := fun 𝔟 K h0 hle hK k hk => by
    obtain ⟨k', rfl⟩ := F.surj k
    obtain ⟨h1, h2⟩ := (hK _).1 hk
    refine hst k' h1 fun u hu i j => ?_
    obtain ⟨z, hz, hz'⟩ := ((hD E A n p S F k').2.2.1 𝔟 h0).1 h2 u (hT u hu).1 i j
    exact ⟨z, Ideal.map_mono (hle u hu) hz, hz'⟩
  choose l hl hlu using fun u : Plc E => prime_under u
  obtain ⟨t, ht, htp⟩ := Nat.exists_infinite_primes (Q.sup q + p + 3)
  have hr : ∀ q₀ : ℕ, ∃ r : ℤ, ∀ w ∈ Q, q w = q₀ → (q₀ : ℤ) ∣ r ^ 2 - A.tr * r + A.nm ∧ A.ω - (r : 𝓞 E) ∈ w.asIdeal := fun q₀ => by
    by_cases h : ∃ w ∈ Q, q w = q₀
    · obtain ⟨w', hw', rfl⟩ := h
      obtain ⟨a1, -, a3, a4, -, -⟩ := hQ w' hw'
      obtain ⟨-, -, -, -, -, ⟨r, hr, hω⟩, h7⟩ := hS E A x hx _ a1 a3.1 w' a4
      exact ⟨r, fun w hw h => ⟨hr, ((h7 r hω w).1 ((hQ w hw).2.2.2.2.2 w' hw' h)).2⟩⟩
    · exact ⟨0, fun w hw h' => (h ⟨w, hw, h'⟩).elim⟩
  choose r hr using hr
  obtain ⟨P, hP⟩ : ∃ P : ℕ, P = (∏ u ∈ T, l u) * ∏ w ∈ Q, q w := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = c * t * P ^ (e * T.card + e + 1) := ⟨_, rfl⟩
  have hP0 : 0 < P := hP ▸ Nat.mul_pos (Finset.prod_pos fun u _ => (hl u).pos) (Finset.prod_pos fun w hw => (hQ w hw).1.pos)
  have hPp : P.Coprime p := hP ▸ Nat.Coprime.mul_left
    (Nat.Coprime.prod_left fun u hu => (Nat.coprime_primes (hl u) hp.out).2 fun h => (hT u hu).1 (h ▸ hlu u))
    (Nat.Coprime.prod_left fun w hw => (Nat.coprime_primes (hQ w hw).1 hp.out).2 (hQ w hw).2.1)
  have hM0 : 0 < M := hM ▸ Nat.mul_pos (Nat.mul_pos hc htp.pos) (pow_pos hP0 _)
  have htM : t ∣ M := hM ▸ (dvd_mul_left t c).mul_right _
  have hMp : M.Coprime p := hM ▸ (hcp.mul_left ((Nat.coprime_primes htp hp.out).2 (by omega))).mul_left (hPp.pow_left _)
  have hpow : ∀ d k : ℕ, d ∣ P → k ≤ e * T.card + e + 1 → d ^ k ∣ M := fun d k hd hk =>
    hM ▸ ((pow_dvd_pow_of_dvd hd k).trans (pow_dvd_pow P hk)).mul_left _
  have hlP : ∀ u ∈ T, l u ∣ P := fun u hu => hP ▸ (Finset.dvd_prod_of_mem l hu).mul_right _
  have hqP : ∀ w ∈ Q, q w ∣ P := fun w hw => hP ▸ (Finset.dvd_prod_of_mem q hw).mul_left _
  have hM3 : 3 ≤ M := le_trans (by omega) (Nat.le_of_dvd hM0 htM)
  obtain ⟨L1, -, L3, -⟩ := hL p S.D S.G S.L
  let 𝔞 : ℕ → Ideal (𝓞 E) := fun q₀ => ∏ u ∈ T.filter (fun u => (q₀ : 𝓞 E) ∈ u.asIdeal), u.asIdeal ^ e
  have main : ∀ w ∈ Q, ∃ σ : Site S ⟨M, hM3, hMp⟩ w, σ.q = q w ∧ σ.r = r (q w) ∧ σ.𝔞 = 𝔞 (q w) ∧ ∀ k ∈ σ.K₀, Stab F V k := by
    intro w hw
    obtain ⟨a1, a2, a3, a4, a5, -⟩ := hQ w hw
    obtain ⟨r1, r2⟩ := hr _ w hw rfl
    obtain ⟨-, -, s3, -, -, -, s7⟩ := hS E A x hx _ a1 a3.1 w a4
    have hS' : ∀ u ∈ T.filter (fun u => (q w : 𝓞 E) ∈ u.asIdeal), u ∈ V.S := fun u hu =>
      (hT u (Finset.mem_filter.1 hu).1).2.elim id fun h => (h (F.a_int u _ a1 a3 (Finset.mem_filter.1 hu).2)).elim
    obtain ⟨K, hK⟩ := L1 (Ideal.span {((ordCompl[q w] M : ℕ) : 𝓞 E)} * 𝔞 (q w))
    have hmem : ((M : ℕ) : 𝓞 E) ∈ Ideal.span {((ordCompl[q w] M : ℕ) : 𝓞 E)} * 𝔞 (q w) := by
      have h1 : e * (T.filter (fun u => (q w : 𝓞 E) ∈ u.asIdeal)).card ≤ M.factorization (q w) :=
        (a1.pow_dvd_iff_le_factorization hM0.ne').1 (hpow _ _ (hqP w hw)
          ((Nat.mul_le_mul_left e (Finset.card_filter_le _ _)).trans (by omega)))
      have h2 : ((ordProj[q w] M : ℕ) : 𝓞 E) ∈ 𝔞 (q w) := by
        refine pow_le_prod _ (fun u : Plc E => u.asIdeal) (Ideal.span {(q w : 𝓞 E)}) e
          (fun u hu => (Ideal.span_singleton_le_iff_mem _).2 (Finset.mem_filter.1 hu).2) ?_
        refine Ideal.pow_le_pow_right h1 ?_
        rw [Nat.cast_pow]
        exact Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _
      have h3 := Ideal.mul_mem_mul (Ideal.mem_span_singleton_self ((ordCompl[q w] M : ℕ) : 𝓞 E)) h2
      rwa [← Nat.cast_mul, Nat.mul_comm, Nat.ordProj_mul_ordCompl_eq_self] at h3
    have htq : ¬ q w ∣ t := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq a1 htp).1 h
      have := Finset.le_sup (f := q) hw
      omega
    refine ⟨⟨q w, r (q w), 𝔞 (q w), K, a3, atPrime_of S a1 a2 a3 r1 a4 r2, ⟨?_, (Nat.coprime_ordCompl a1 hM0.ne').symm,
      hMp.coprime_dvd_left (Nat.ordCompl_dvd _ _), ?_, ?_⟩, hK, hmem⟩, rfl, rfl, rfl, key _ K (fun h => ?_) (fun u hu => ?_) hK⟩
    · exact le_trans (by omega) (Nat.le_of_dvd (Nat.ordCompl_pos _ hM0.ne') (Nat.dvd_ordCompl_of_dvd_not_dvd htM htq))
    · refine Ideal.isCoprime_iff_sup_eq.1 (IsCoprime.prod_left fun u hu => IsCoprime.pow_left ?_)
      exact HeightOneSpectrum.isCoprime_of_ne u w fun h => a5.2.1 (h ▸ hS' u hu)
    · refine ⟨_, pow_le_prod _ (fun u : Plc E => u.asIdeal) _ e fun u hu => Ideal.span_le.2 ?_⟩
      have hq := (Finset.mem_filter.1 hu).2
      have := ((s7 _ r2 u).1 ((s3 u hq).resolve_right (a5.2.2.2.1 u (hS' u hu)))).2
      rintro y (rfl | rfl)
      exacts [hq, this]
    · rw [h, Ideal.mem_bot] at hmem
      exact hM0.ne' (Nat.cast_eq_zero.1 hmem)
    · by_cases hq : (q w : 𝓞 E) ∈ u.asIdeal
      · exact Ideal.mul_le_right.trans (prod_le_one _ (fun u : Plc E => u.asIdeal ^ e) u (Finset.mem_filter.2 ⟨hu, hq⟩))
      · refine Ideal.mul_le_left.trans (span_le_pow (hlu u) (Nat.dvd_ordCompl_of_dvd_not_dvd (hpow _ e (hlP u hu) (by omega)) fun h => hq ?_))
        rw [(Nat.prime_dvd_prime_iff_eq a1 (hl u)).1 (a1.dvd_of_dvd_pow h)]
        exact hlu u
  choose σ h1 h2 h3 h4 using main
  refine ⟨⟨M, hM3, hMp⟩, σ, hM ▸ (dvd_mul_right c t).mul_right _, key (Ideal.span {(M : 𝓞 E)}) _ ?_ (fun u hu => ?_) (L3 M),
    fun w hw => ⟨?_, h1 w hw, h4 w hw⟩, fun w hw w' hw' h => ?_⟩
  · rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact hM0.ne'
  · exact span_le_pow (hlu u) (hpow _ _ (hlP u hu) (by omega))
  · simpa using hpow _ 1 (hqP w hw) (by omega)
  · rw [h1, h1] at h
    rw [h2, h2, h3, h3, h]
    exact ⟨rfl, rfl⟩

end UpperTheory.Gal.Int.Geo.Pl
end
end

section

open NumberField IsDedekindDomain GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl

private theorem inId_zero {E : Type} [Field E] [NumberField E] (w : Plc E) (𝔟 : Ideal (𝓞 E)) : InId w 𝔟 0 :=
  ⟨0, zero_mem _, rfl⟩

private theorem nat_not_mem {E : Type} [Field E] [NumberField E] (w : Plc E) {q q' : ℕ} (hq : q.Prime) (hq' : q'.Prime)
    (hne : q' ≠ q) (h : (q' : 𝓞 E) ∈ w.asIdeal) : (q : 𝓞 E) ∉ w.asIdeal := by
  intro h2
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hq').2 hne.symm)
  have h1 : (a : 𝓞 E) * (q : 𝓞 E) + (b : 𝓞 E) * (q' : 𝓞 E) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hab
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (h1 ▸ add_mem (Ideal.mul_mem_left _ _ h2) (Ideal.mul_mem_left _ _ h)))

private theorem pow_not_mem {E : Type} [Field E] [NumberField E] (w : Plc E) {q : ℕ} (h : (q : 𝓞 E) ∉ w.asIdeal) (e : ℕ) :
    ((q ^ e : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  push_cast
  exact fun h2 => h (w.isPrime.mem_of_pow_mem _ h2)

theorem UpperTheory.Gal.Int.Geo.Pl.projLev_of :
    Dict → PrimeProj → LevBasic → InIdUnit → ProjLev := by
  intro hD hP hL hU E _ _ _ A n p _ S F N v σ q' k hq' hne K₁ hK₁ u hu
  obtain ⟨π, hπ⟩ := hP E n q' hq'
  obtain ⟨g, rfl⟩ := F.surj u
  have hq := σ.atp.prime
  have hNpos : N.1 ≠ 0 := by have := N.2.1; omega
  have hN0 : (N.1 : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hNpos
  obtain ⟨hu1, hu2⟩ := (σ.isLev (F.j g)).1 hu
  have hb : Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞 ≠ ⊥ := fun h => hN0 (by
    have := σ.mem
    rw [h] at this
    simpa using this)
  have hg3 := ((hD E A n p S F g).2.2.1 _ hb).1 hu2
  have hg2 := (hD E A n p S F g).2.1.1 hu1
  obtain ⟨-, -, -, -, e, he⟩ := σ.lv
  have hqe : ((σ.q ^ e : ℕ) : 𝓞 E) ∈ σ.𝔞 := by
    have h1 : (σ.q : 𝓞 E) ∈ uId S.D σ.q σ.r := Ideal.subset_span (Set.mem_insert _ _)
    have h2 := Ideal.pow_mem_pow h1 e
    push_cast
    exact he h2
  have hxK1 : F.j (π g) ∈ S.L.KN 1 := (hD E A n p S F (π g)).2.1.2 (fun w hw => by
    by_cases h : (q' : 𝓞 E) ∈ w.asIdeal
    · rw [(hπ g w).1 h]; exact hg2 w hw
    · rw [(hπ g w).2 h, mul_one, mul_inv_cancel]; exact one_mem _)
  have hNb : Ideal.span {(N.1 : 𝓞 E)} ≠ ⊥ := by simpa using hN0
  have hxN : F.j (π g) ∈ S.L.KN N.1 := by
    have lev := (hL p S.D S.G S.L).2.2.1 N.1
    refine (lev _).2 ⟨hxK1, ?_⟩
    refine ((hD E A n p S F (π g)).2.2.1 _ hNb).2 fun w hw i l => ?_
    by_cases h : (q' : 𝓞 E) ∈ w.asIdeal
    · have hc : F.cmp w (π g) = F.cmp w g := by simp only [Frame.cmp, (hπ g w).1 h]
      rw [hc]
      have hqw := nat_not_mem w hq hq' hne h
      have h1 := hg3 w hw i l
      rw [hU E w _ _ ⟨_, hqe, pow_not_mem w hqw e⟩] at h1
      have hspan : Ideal.span {(N.1 : 𝓞 E)} = Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} *
          Ideal.span {((σ.q ^ N.1.factorization σ.q : ℕ) : 𝓞 E)} := by
        rw [Ideal.span_singleton_mul_span_singleton, ← Nat.cast_mul, Nat.mul_comm,
          Nat.ordProj_mul_ordCompl_eq_self]
      rw [hspan, hU E w _ _ ⟨_, Ideal.mem_span_singleton_self _, pow_not_mem w hqw _⟩]
      exact h1
    · have hc : F.cmp w (π g) = 1 := by
        simp only [Frame.cmp, (hπ g w).2 h, mul_one, mul_inv_cancel, Units.val_one]
      rw [hc, sub_self]
      exact inId_zero w _
  refine ⟨F.j (π g), hxN, ?_⟩
  rw [← map_inv, ← map_mul]
  have hmul : ∀ w : Plc E, UpperTheory.Gal.CertificateRingHomMap.comp w ((π g)⁻¹ * g) = (UpperTheory.Gal.CertificateRingHomMap.comp w (π g))⁻¹ * UpperTheory.Gal.CertificateRingHomMap.comp w g := fun w => by
    rw [map_mul, map_inv]
  have hspan2 : Ideal.span {((ordCompl[σ.q] N.1 * q' ^ k : ℕ) : 𝓞 E)} * σ.𝔞 =
      (Ideal.span {((ordCompl[σ.q] N.1 : ℕ) : 𝓞 E)} * σ.𝔞) * Ideal.span {((q' ^ k : ℕ) : 𝓞 E)} := by
    rw [Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton]
    ring
  have hq'0 : ((q' ^ k : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ hq'.ne_zero)
  have hBot : Ideal.span {((ordCompl[σ.q] N.1 * q' ^ k : ℕ) : 𝓞 E)} * σ.𝔞 ≠ ⊥ := by
    rw [hspan2]
    exact mul_ne_zero hb (by simpa using hq'0)
  refine (hK₁ _).2 ⟨?_, ?_⟩
  · rw [map_mul, map_inv]
    exact mul_mem (inv_mem hxK1) hu1
  · refine ((hD E A n p S F _).2.2.1 _ hBot).2 fun w hw i l => ?_
    by_cases h : (q' : 𝓞 E) ∈ w.asIdeal
    · have hc : F.cmp w ((π g)⁻¹ * g) = 1 := by
        simp only [Frame.cmp, hmul, (hπ g w).1 h, inv_mul_cancel, mul_one, mul_inv_cancel, Units.val_one]
      rw [hc, sub_self]
      exact inId_zero w _
    · have hc : F.cmp w ((π g)⁻¹ * g) = F.cmp w g := by
        simp only [Frame.cmp, hmul, (hπ g w).2 h, inv_one, one_mul]
      rw [hc, hspan2, hU E w _ _ ⟨_, Ideal.mem_span_singleton_self _, pow_not_mem w h k⟩]
      exact hg3 w hw i l
end

section

set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl

namespace UpperTheory.Gal.Int.Geo.Pl.GoodPlacesAlt

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {N : Lv p}

private def Row (q : ℕ) (r : ℤ) (N₀ : ℕ) (𝔞 : Ideal (𝓞 D.F)) (K₀ : Subgroup G.GAf) (𝔴 : Ideal (𝓞 D.F)) (g : Mem L N) : Prop :=
  ∃ (c : ℕ) (𝔞' : Ideal (𝓞 D.F)) (K₁ : Subgroup G.GAf) (h₁ h₂ : G.GAf) (N₁ : Lv p), LevAt D q r 𝔴 (N₀ * c) 𝔞' ∧
      IsLev L (Ideal.span {((N₀ * c : ℕ) : 𝓞 D.F)} * 𝔞') K₁ ∧ 𝔞' ≤ 𝔞 ∧ L.KN g.M.1 ≤ K₁ ∧
      ((g.M.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {((N₀ * c : ℕ) : 𝓞 D.F)} * 𝔞' ∧
      (∀ u ∈ K₀, ∃ x ∈ g.K, x ∈ K₀ ∧ x⁻¹ * u ∈ K₁) ∧ g.h = h₁ * h₂ ∧ Integ L h₁ ∧ Integ L h₂ ∧
      (∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG h₂ v' = c • v) ∧ ((N₁.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞' ∧
      (∀ k ∈ g.K, ∀ u ∈ L.KN g.M.1, h₂ * k * u * (h₂ * k)⁻¹ ∈ L.KN N₁.1) ∧
      (∀ u ∈ L.KN N₁.1, h₁ * u * h₁⁻¹ ∈ L.KN N.1) ∧
      (h₁ = 1 ∨ ∃ (𝔴' : Ideal (𝓞 D.F)) (i : ℕ), 𝔴'.IsMaximal ∧ uId D q r ≤ 𝔴' ∧ 𝔞' ≤ 𝔞 * 𝔴' ∧ i ≤ D.n ∧
        Ideal.absNorm 𝔴' ^ i ∣ N₁.1 ∧ IsTjElt L q r 𝔴' i h₁)

private theorem kn_le
    (hle : ∀ 𝔟 𝔟' K K', IsLev L 𝔟 K → IsLev L 𝔟' K' → 𝔟 ≤ 𝔟' → K ≤ K')
    (hKN : ∀ N : ℕ, IsLev L (Ideal.span {(N : 𝓞 D.F)}) (L.KN N))
    {𝔟 : Ideal (𝓞 D.F)} {K : Subgroup G.GAf} {M : ℕ} (hK : IsLev L 𝔟 K) (hM : (M : 𝓞 D.F) ∈ 𝔟) : L.KN M ≤ K :=
  hle _ _ _ _ (hKN M) hK ((Ideal.span_singleton_le_iff_mem _).2 hM)

private theorem row_trans
    (hle : ∀ 𝔟 𝔟' K K', IsLev L 𝔟 K → IsLev L 𝔟' K' → 𝔟 ≤ 𝔟' → K ≤ K')
    (hKN : ∀ N : ℕ, IsLev L (Ideal.span {(N : 𝓞 D.F)}) (L.KN N))
    {q : ℕ} {r : ℤ} {N₀ : ℕ} {𝔞 𝔴 : Ideal (𝓞 D.F)} {K₀ K₁ : Subgroup G.GAf} {c : ℕ}
    (hlv : LevAt D q r 𝔴 N₀ 𝔞) (hN : ((N.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞)
    (hc : 0 < c) (hcq : c.Coprime q) (hcp : c.Coprime p)
    (hK₁ : IsLev L (Ideal.span {((N₀ * c : ℕ) : 𝓞 D.F)} * 𝔞) K₁)
    (g : Mem L N) (hM : g.M.1 = N.1 * c)
    (hback : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG g.h v' = c • v)
    (hx : ∀ u ∈ K₀, ∃ x ∈ g.K, x ∈ K₀ ∧ x⁻¹ * u ∈ K₁) : Row q r N₀ 𝔞 K₀ 𝔴 g := by
  obtain ⟨h3, hq, hp, hv, e, he⟩ := hlv
  have hmem : ((g.M.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {((N₀ * c : ℕ) : 𝓞 D.F)} * 𝔞 := by
    obtain ⟨a, ha, ea⟩ := Ideal.mem_span_singleton_mul.1 hN
    refine Ideal.mem_span_singleton_mul.2 ⟨a, ha, ?_⟩
    rw [hM]; push_cast; rw [← ea]; ring
  refine ⟨c, 𝔞, K₁, 1, g.h, N, ⟨le_trans h3 (Nat.le_mul_of_pos_right _ hc), Nat.coprime_mul_iff_left.2 ⟨hq, hcq⟩,
    Nat.coprime_mul_iff_left.2 ⟨hp, hcp⟩, hv, e, he⟩, hK₁, le_rfl, kn_le hle hKN hK₁ hmem, hmem, hx,
    (one_mul _).symm, integ_of_mem (one_mem _), g.int, hback, hN, fun k hk u hu => g.adm k hk u hu, ?_, Or.inl rfl⟩
  intro u hu
  simpa using hu

private theorem row_near
    (hex : ∀ 𝔟, ∃ K, IsLev L 𝔟 K)
    (hle : ∀ 𝔟 𝔟' K K', IsLev L 𝔟 K → IsLev L 𝔟' K' → 𝔟 ≤ 𝔟' → K ≤ K')
    (hKN : ∀ N : ℕ, IsLev L (Ideal.span {(N : 𝓞 D.F)}) (L.KN N))
    (hnorm : ∀ 𝔟 K, IsLev L 𝔟 K → ∀ k ∈ L.KN 1, ∀ u ∈ K, k * u * k⁻¹ ∈ K)
    {q : ℕ} {r : ℤ} {N₀ : ℕ} {𝔞 𝔴 𝔴' : Ideal (𝓞 D.F)} {K₀ : Subgroup G.GAf} {i : ℕ}
    (hlv : LevAt D q r 𝔴 N₀ 𝔞) (hN : ((N.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} * 𝔞)
    (hmax : 𝔴.IsMaximal) (hmax' : 𝔴'.IsMaximal) (hne : 𝔴' ≠ 𝔴) (hu : uId D q r ≤ 𝔴')
    (hi : 0 < i) (hin : i ≤ D.n) (g : Mem L N) (hK : g.K = K₀) (hM : g.M.1 = N.1 * Ideal.absNorm 𝔴' ^ i)
    (hT : IsTjElt L q r 𝔴' i g.h) : Row q r N₀ 𝔞 K₀ 𝔴 g := by
  obtain ⟨h3, hq, hp, hv, e, he⟩ := hlv
  obtain ⟨K₁, hK₁⟩ := hex (Ideal.span {((N₀ * 1 : ℕ) : 𝓞 D.F)} * (𝔞 * 𝔴'))
  have hmem : ((g.M.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {(N₀ : 𝓞 D.F)} * (𝔞 * 𝔴') := by
    rw [← mul_assoc, hM]
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hn : ((Ideal.absNorm 𝔴' : ℕ) : 𝓞 D.F) ∈ 𝔴' := Ideal.absNorm_mem 𝔴'
    have : ((N.1 * Ideal.absNorm 𝔴' ^ (i + 1) : ℕ) : 𝓞 D.F)
        = (((N.1 : ℕ) : 𝓞 D.F) * ((Ideal.absNorm 𝔴' : ℕ) : 𝓞 D.F) ^ i) * ((Ideal.absNorm 𝔴' : ℕ) : 𝓞 D.F) := by
      push_cast; ring
    rw [this]
    exact Ideal.mul_mem_mul (Ideal.mul_mem_right _ _ hN) hn
  have hmem1 : ((g.M.1 : ℕ) : 𝓞 D.F) ∈ Ideal.span {((N₀ * 1 : ℕ) : 𝓞 D.F)} * (𝔞 * 𝔴') := by
    simpa using hmem
  refine ⟨1, 𝔞 * 𝔴', K₁, g.h, 1, g.M, ⟨by simpa using h3, by simpa using hq, by simpa using hp, ?_, e + 1, ?_⟩, hK₁,
    Ideal.mul_le_left, kn_le hle hKN hK₁ hmem1, hmem1, ?_, (mul_one _).symm, g.int, integ_of_mem (one_mem _), ?_,
    hmem, ?_, ?_, Or.inr ⟨𝔴', i, hmax', hu, le_rfl, hin, by rw [hM]; exact Dvd.intro_left _ rfl, hT⟩⟩
  · exact Ideal.isCoprime_iff_sup_eq.1 (IsCoprime.mul_left (Ideal.isCoprime_iff_sup_eq.2 hv)
      (Ideal.isCoprime_iff_sup_eq.2 (Ideal.IsMaximal.coprime_of_ne hmax' hmax hne)))
  · rw [pow_succ]; exact Ideal.mul_mono he hu
  · intro u hu'
    exact ⟨u, hK ▸ hu', hu', by simpa using one_mem K₁⟩
  · intro v hv'
    exact ⟨v, hv', by simp⟩
  · intro k hk u hu'
    have := hnorm _ _ (hKN g.M.1) k (g.le_one hk) u hu'
    simpa using this
  · intro u hu'
    have := g.adm 1 (one_mem _) u hu'
    simpa using this

private theorem absNorm_nat {E : Type} [Field E] [NumberField E] (q : ℕ) :
    Ideal.absNorm (Ideal.span {((q : ℕ) : 𝓞 E)}) = q ^ Module.finrank ℤ (𝓞 E) := by
  rw [Ideal.absNorm_span_singleton, show ((q : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (q : ℤ) by simp,
    Algebra.norm_algebraMap]
  simp [Int.natAbs_pow]

end UpperTheory.Gal.Int.Geo.Pl.GoodPlacesAlt

open UpperTheory.Gal.Int.Geo.Pl.GoodPlacesAlt in
theorem UpperTheory.Gal.Int.Geo.Pl.goodOf_of :
    LevBasic → TjOK → ProjLev → GoodOf := by
  intro hL hT hP E _ _ _ A n p _ S F x hx N v σ J L' _ g θ hD hj
  obtain ⟨hex, hle, hKN, -, hnorm, -⟩ := hL p S.D S.G S.L
  refine ⟨σ.q, σ.r, ordCompl[σ.q] N.1, σ.𝔞, σ.K₀, σ.atp, σ.lv, σ.isLev, kn_le hle hKN σ.isLev σ.mem, σ.mem, hD,
    fun j => ?_⟩
  have hK₀ : IsLev S.L (Ideal.span {((ordCompl[σ.q] N.1 * 1 : ℕ) : 𝓞 E)} * σ.𝔞) σ.K₀ := by
    simpa using σ.isLev
  change Row σ.q σ.r (ordCompl[σ.q] N.1) σ.𝔞 σ.K₀ v.asIdeal (g j)
  rcases hj j with ⟨hK, hM, hh⟩ | ⟨w, σ', i, hne, hc, hi, hK, hH, hM⟩
  · refine row_trans hle hKN σ.lv σ.mem one_pos (Nat.coprime_one_left _) (Nat.coprime_one_left _) hK₀ (g j) (by simp [hM]) ?_ ?_
    · intro v' hv'
      refine ⟨S.L.actG (g j).h⁻¹ v', integ_of_mem (inv_mem hh) v' hv', ?_⟩
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      simp
    · intro u hu
      exact ⟨1, one_mem _, one_mem _, by simpa using hu⟩
  · obtain ⟨hI, hTj⟩ := hT E A n p S F x hx N w σ' i hi _ hH
    by_cases hq : σ.q = σ'.q
    · obtain ⟨hr, ha⟩ := hc hq
      have hKe : σ'.K₀ = σ.K₀ := by
        have h' := σ'.isLev
        rw [← hq, ← ha] at h'
        exact Subgroup.ext fun y => (h' y).trans (σ.isLev y).symm
      rw [hKe] at hK
      have hat := σ'.atp
      rw [← hq, ← hr] at hTj hat
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · refine row_trans hle hKN σ.lv σ.mem one_pos (Nat.coprime_one_left _) (Nat.coprime_one_left _) hK₀ (g j) (by simpa using hM) ?_ ?_
        · intro v' hv'
          obtain ⟨y, hy, e⟩ := hTj.back v' hv'
          exact ⟨y, hy, by simpa using e⟩
        · intro u hu
          exact ⟨1, one_mem _, one_mem _, by simpa using hu⟩
      · exact row_near hex hle hKN hnorm σ.lv σ.mem σ.atp.max hat.max
          (fun e => hne (HeightOneSpectrum.ext e)) hat.le hpos hi (g j) hK hM hTj
    · have hat := σ'.atp
      have hqw : ((σ'.q : ℕ) : 𝓞 E) ∈ w.asIdeal := hat.le (Ideal.subset_span (Set.mem_insert _ _))
      have hdvd : Ideal.absNorm w.asIdeal ∣ σ'.q ^ Module.finrank ℤ (𝓞 E) := by
        have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hqw)
        rwa [absNorm_nat] at this
      obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hat.prime).1 hdvd
      have hcpow : Ideal.absNorm w.asIdeal ^ i = σ'.q ^ (f * i) := by rw [hf, pow_mul]
      obtain ⟨K₁, hK₁⟩ := hex (Ideal.span {((ordCompl[σ.q] N.1 * σ'.q ^ (f * i) : ℕ) : 𝓞 E)} * σ.𝔞)
      have hcq : (σ'.q ^ (f * i)).Coprime σ.q :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes hat.prime σ.atp.prime).2 (Ne.symm hq))
      have hcp : (σ'.q ^ (f * i)).Coprime p :=
        Nat.Coprime.pow_left _ ((Nat.coprime_primes hat.prime (Fact.out)).2 hat.ne)
      refine row_trans hle hKN σ.lv σ.mem (pow_pos hat.prime.pos _) hcq hcp hK₁ (g j) (by rw [hM, hcpow]) ?_ ?_
      · rw [← hcpow]; exact hTj.back
      · intro u hu
        obtain ⟨y, hy, e⟩ := hP E A n p S F N v σ σ'.q (f * i) hat.prime (Ne.symm hq) K₁ hK₁ u hu
        exact ⟨y, hK ▸ kn_le hle hKN σ'.isLev σ'.mem hy, kn_le hle hKN σ.isLev σ.mem hy, e⟩
end
