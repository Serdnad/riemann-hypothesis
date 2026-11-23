module

public import Formalism.LocalToGlobal.Divisibility.CoefMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle211
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle204
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardWeylLatticesFockDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TransportedLatticeLocalizationFreeLeCoefficientS
public import Formalism.LocalToGlobal.IndefiniteReal.Bridge
public import Formalism.LocalToGlobal.KernelLattices.XiIndCClass
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle096
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle050
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

section

noncomputable section

namespace GlobalTheory.ColPeriod.WeylLoc

open NumberField IsDedekindDomain MvPolynomial Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
theorem localized_le_of_le_localized {V : Type} [AddCommGroup V] [Module (𝓞 K) V] (w : HeightOneSpectrum (𝓞 K))
    {N N' : Submodule (𝓞 K) V} (h : N ≤ localization₂ w.asIdeal N') : localization₂ w.asIdeal N ≤ localization₂ w.asIdeal N' := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨t, ht, h'⟩ := h hx
  exact ⟨t * s, mul_mem ht hs, by rw [mul_smul]; exact h'⟩

omit [NumberField K] in
theorem intCast_notMem {p : ℕ} (hp : p.Prime) (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) {c : ℤ}
    (hc : ¬ (p : ℤ) ∣ c) : (c : 𝓞 K) ∉ w.asIdeal := by
  intro ha
  have hco : IsCoprime (p : ℤ) c := (Nat.prime_iff_prime_int.1 hp).irreducible.coprime_iff_not_dvd.2 hc
  obtain ⟨x, y, e⟩ := hco.map (Int.castRingHom (𝓞 K))
  simp only [eq_intCast, Int.cast_natCast] at e
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (e ▸ w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ hw) (w.asIdeal.mul_mem_left _ ha)))

theorem nablaSq_le_locP (h : NablaMemDeltaLocallyAtLargePrime) {n : ℕ} (lam : DomWeight n) {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) (hs : lam.spread < p) :
    (nablaSq (𝓞 K) n lam).map (toK K _) ≤ localization₂ w.asIdeal ((delSq (𝓞 K) n lam).map (toK K _)) := by
  unfold nablaSq
  rw [GlobalTheory.StdDual.dualWeyl_eq, Submodule.map_span, Submodule.span_le,
    ← GlobalTheory.StdDual.image_bidSet (Int.castRingHom (𝓞 K))]
  rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
  have hf' : f ∈ nablaSq ℤ n lam := by
    unfold nablaSq
    rw [GlobalTheory.StdDual.dualWeyl_eq]
    exact Submodule.subset_span hf
  obtain ⟨c, hc, hcf⟩ := h n lam p hp hs f hf'
  refine ⟨(c : 𝓞 K), intCast_notMem hp w hw hc, map (Int.castRingHom (𝓞 K)) (c • f),
    GlobalTheory.TestLat.WeylLocal.map_mem_weyl _ _ hcf, ?_⟩
  rw [map_zsmul, ← Int.cast_smul_eq_zsmul (𝓞 K), map_smul]
  rfl

theorem nabStd_le_locP (h : NablaMemDeltaLocallyAtLargePrime) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {p : ℕ} (hp : p.Prime)
    (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) (hs : ∀ τ, (lam τ).spread < p) :
    nabStd K lam ≤ localization₂ w.asIdeal (delStd K lam) := by
  unfold nabStd Formalism.GradedWeylDivisibility.tensorLat
  rw [Submodule.span_le]
  rintro _ ⟨f, hf, rfl⟩
  exact GlobalTheory.TestLat.WeylLocal.ten_mem_locP w _ f fun τ => nablaSq_le_locP h (lam τ) hp w hw (hs τ) (hf τ)

theorem nabLeDel_of_local (h : NablaMemDeltaLocallyAtLargePrime)
    (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsFullLattice K (M τ))
    (p : ℕ) (w : HeightOneSpectrum (𝓞 K)) (hp : p.Prime) (hw : (p : 𝓞 K) ∈ w.asIdeal)
    (hs : ∀ τ, (lam τ).spread < p) :
    localization₂ w.asIdeal (nabK lam M) ≤ localization₂ w.asIdeal (delK lam M) := by
  intro x hx
  choose B hB using fun τ => GlobalTheory.LatBasisAt.basisAtEx K n (M τ) (hM τ) w
  have h1 := GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι n lam M hM w B hB
  have hx' : x.1 ∈ localization₂ w.asIdeal (nabP lam M) := hx
  change x.1 ∈ localization₂ w.asIdeal (delP lam M)
  rw [h1.1] at hx'
  rw [h1.2]
  exact Submodule.map_mono (localized_le_of_le_localized w (nabStd_le_locP h lam hp w hw hs)) hx'

end GlobalTheory.ColPeriod.WeylLoc
end
end

section

open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory.DoubleCosetComm

variable {G : Type} [Group G]

def InDC (J : Subgroup G) (x g : G) : Prop := ∃ k₁ k₂ : J, g = (k₁ : G) * x * k₂

theorem InDC.mul {J : Subgroup G} {x g a b : G} (h : InDC J x g) (ha : a ∈ J) (hb : b ∈ J) :
    InDC J x (a * g * b) := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨⟨a, ha⟩ * u, v * ⟨b, hb⟩, by simp [mul_assoc]⟩

theorem InDC.inv {J : Subgroup G} {x g : G} (h : InDC J x g) : InDC J x⁻¹ g⁻¹ := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨v⁻¹, u⁻¹, by simp [mul_assoc]⟩


open Classical in
theorem card_filter_le {J : Subgroup G} {x y : G} {A B : Finset G} (hA : IsDC J x A) (hB : IsDC J y B)
    (P Q : G → Prop) (ψ : G → G) (h1 : ∀ a ∈ A, P a → InDC J y (ψ a))
    (h2 : ∀ a ∈ A, P a → ∀ k ∈ J, Q (ψ a * k))
    (h3 : ∀ a ∈ A, ∀ a' ∈ A, (ψ a)⁻¹ * ψ a' ∈ J → a⁻¹ * a' ∈ J) :
    (A.filter P).card ≤ (B.filter Q).card := by
  have hex : ∀ a : G, ∃ b : G, a ∈ A → P a → b ∈ B ∧ b⁻¹ * ψ a ∈ J := by
    intro a
    by_cases h : a ∈ A ∧ P a
    · obtain ⟨b, hb, -⟩ := hB.2 _ (h1 a h.1 h.2)
      exact ⟨b, fun _ _ => hb⟩
    · exact ⟨1, fun h₁ h₂ => absurd ⟨h₁, h₂⟩ h⟩
  choose r hr using hex
  refine Finset.card_le_card_of_injOn r ?_ ?_
  · intro a ha
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ⊢
    obtain ⟨hb, hj⟩ := hr a ha.1 ha.2
    refine ⟨hb, ?_⟩
    have := h2 a ha.1 ha.2 _ (J.inv_mem hj)
    simpa [mul_assoc] using this
  · intro a ha a' ha' e
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ha ha'
    have hj := (hr a ha.1 ha.2).2
    have hj' := (hr a' ha'.1 ha'.2).2
    rw [← e] at hj'
    have h4 : (ψ a)⁻¹ * ψ a' ∈ J := by simpa [mul_assoc] using J.mul_mem (J.inv_mem hj) hj'
    exact (hA.2 a' (hA.1 a' ha'.1)).unique ⟨ha.1, h3 a ha.1 a' ha'.1 h4⟩ ⟨ha'.1, by simp⟩

section Theta

variable {J L : Subgroup G} {θ : G → G}
  (hm : ∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) (hi : ∀ x ∈ L, θ (θ x) = x)
  (hK : ∀ k ∈ J ⊓ L, θ k ∈ J) (hL : ∀ g ∈ L, θ g ∈ L)
  (hdc : ∀ g ∈ L, ∃ a ∈ J ⊓ L, ∃ b ∈ J ⊓ L, θ g = a * g * b)

include hm in
theorem theta_inv {g : G} (hg : g ∈ L) : θ g⁻¹ = (θ g)⁻¹ := by
  have h1 : θ 1 = 1 := by
    have h := hm 1 L.one_mem 1 L.one_mem
    rw [mul_one] at h
    have h' : θ 1 * θ 1 = θ 1 * 1 := by rw [mul_one, ← h]
    exact mul_left_cancel h'
  apply eq_inv_of_mul_eq_one_left
  rw [← hm _ hg _ (L.inv_mem hg), mul_inv_cancel, h1]

include hm hi hK hL in
theorem theta_coset {a a' : G} (ha : a ∈ L) (ha' : a' ∈ L) (h : θ a * (θ a')⁻¹ ∈ J) : a⁻¹ * a' ∈ J := by
  have hl : a'⁻¹ * a ∈ L := L.mul_mem (L.inv_mem ha') ha
  have e : θ (a'⁻¹ * a) = θ a * (θ a')⁻¹ := by
    rw [hm _ (L.inv_mem ha') _ ha, theta_inv hm ha']
  have := hK (θ (a'⁻¹ * a)) ⟨e ▸ h, hL _ hl⟩
  rw [hi _ hl] at this
  simpa using J.inv_mem this

include hdc in
theorem InDC.theta {x g : G} (h : InDC J x g) (hg : g ∈ L) : InDC J x (θ g) := by
  obtain ⟨a, ha, b, hb, e⟩ := hdc g hg
  rw [e]
  exact h.mul ha.1 hb.1

include hm hi hK hL hdc in
theorem card_le_inv {x : G} {A A' : Finset G} (hA : IsDC J x A) (hA' : IsDC J x⁻¹ A') (hAL : ∀ a ∈ A, a ∈ L) :
    A.card ≤ A'.card := by
  classical
  have := card_filter_le hA hA' (fun _ => True) (fun _ => True) (fun a => (θ a)⁻¹)
    (fun a ha _ => (InDC.theta hdc (hA.1 a ha) (hAL a ha)).inv) (fun _ _ _ _ _ => trivial)
    (fun a ha a' ha' h => theta_coset hm hi hK hL (hAL a ha) (hAL a' ha') (by simpa using h))
  simpa using this

open Classical in
include hm hi hK hL hdc in
theorem card_conv_le {x y : G} {A B : Finset G} (hA : IsDC J x A) (hB : IsDC J y B) (hAL : ∀ a ∈ A, a ∈ L)
    {z : G} (hz : z ∈ L) :
    (A.filter fun a => InDC J y (a⁻¹ * z)).card ≤ (B.filter fun b => InDC J x (b⁻¹ * z)).card := by
  obtain ⟨k, hk, k', hk', e⟩ := hdc z hz
  refine card_filter_le hA hB _ _ (fun a => z * k' * (θ a)⁻¹) ?_ ?_ ?_
  · intro a ha hP
    have hl := L.inv_mem (hAL a ha)
    have h1 := InDC.theta hdc hP (L.mul_mem hl hz)
    rw [hm _ hl _ hz, theta_inv hm (hAL a ha), e] at h1
    simpa [mul_assoc] using h1.mul (J.inv_mem hk.1) J.one_mem
  · intro a ha _ c hc
    have h1 := InDC.theta hdc (hA.1 a ha) (hAL a ha)
    simpa [mul_assoc] using h1.mul (J.inv_mem hc) (J.inv_mem hk'.1)
  · intro a ha a' ha' h
    exact theta_coset hm hi hK hL (hAL a ha) (hAL a' ha') (by simpa [mul_assoc] using h)

end Theta


open Classical in
theorem card_pairs {J L : Subgroup G} {y : G} {A B : Finset G} (hB : IsDC J y B) (hAL : ∀ a ∈ A, a ∈ L)
    (hBL : ∀ b ∈ B, b ∈ L) {z : G} (hz : z ∈ L) :
    ((A ×ˢ B).filter fun p => (z : G ⧸ (J ⊓ L)) = ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))).card =
      (A.filter fun a => InDC J y (a⁻¹ * z)).card := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq] at hp ⊢
    refine ⟨hp.1.1, ?_⟩
    have h1 : InDC J y b := hB.1 b hp.1.2
    simpa [mul_assoc] using h1.mul J.one_mem (J.inv_mem hp.2.1)
  · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' e
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq] at hp hp' e
    subst e
    have h4 : b⁻¹ * b' ∈ J := by simpa [mul_assoc] using J.mul_mem (J.inv_mem hp.2.1) hp'.2.1
    have := (hB.2 b' (hB.1 b' hp'.1.2)).unique ⟨hp.1.2, h4⟩ ⟨hp'.1.2, by simp⟩
    rw [this]
  · intro a ha
    simp only [Finset.mem_filter] at ha
    obtain ⟨b, ⟨hb, hj⟩, -⟩ := hB.2 _ ha.2
    refine ⟨(a, b), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_product, QuotientGroup.eq]
    refine ⟨⟨ha.1, hb⟩, ?_, L.mul_mem (L.inv_mem hz) (L.mul_mem (hAL a ha.1) (hBL b hb))⟩
    simpa [mul_assoc] using J.inv_mem hj

theorem dcOp_comm_and_card : ∀ {G W : Type} [Group G] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (J L : Subgroup G) (χ : J →* ℂˣ) (x y : G) (A B A' : Finset G) (F : G → W), (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l) → (∀ k : J, (k : G) ∈ L → χ k = 1) → (∃ θ : G → G, (∀ g ∈ L, θ g ∈ L) ∧ (∀ x ∈ L, ∀ y ∈ L, θ (x * y) = θ y * θ x) ∧ (∀ x ∈ L, θ (θ x) = x) ∧ (∀ k ∈ J ⊓ L, θ k ∈ J) ∧ ∀ g ∈ L, ∃ a ∈ J ⊓ L, ∃ b ∈ J ⊓ L, θ g = a * g * b) → (∀ a ∈ A, a ∈ L) → (∀ a ∈ B, a ∈ L) → (∀ a ∈ A', a ∈ L) → IsDC J x A → IsDC J y B → IsDC J x⁻¹ A' → (∀ (k : J) (h : G), F (h * k) = (χ k : ℂ) • F h) → dcOp A (dcOp B F) = dcOp B (dcOp A F) ∧ A.card = A'.card := by
  classical
  intro G W _ _ _ J L χ x y A B A' F _ hχ ⟨θ, hL, hm, hi, hK, hdc⟩ hAL hBL hAL' hA hB hA' hF
  refine ⟨?_, le_antisymm (card_le_inv hm hi hK hL hdc hA hA' hAL)
    (card_le_inv hm hi hK hL hdc hA' (by rwa [inv_inv]) hAL')⟩
  have hFK : ∀ g g' : G, (g : G ⧸ (J ⊓ L)) = g' → ∀ h, F (h * g) = F (h * g') := by
    intro g g' e h
    rw [QuotientGroup.eq] at e
    have := hF ⟨_, e.1⟩ (h * g)
    rw [hχ ⟨_, e.1⟩ e.2] at this
    simpa [mul_assoc] using this.symm
  have hms : (A ×ˢ B).val.map (fun p => ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) =
      (B ×ˢ A).val.map (fun p => ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) := by
    ext q
    induction q using QuotientGroup.induction_on with
    | H z =>
      rw [Multiset.count_map, Multiset.count_map]
      by_cases hz : z ∈ L
      · have e1 := card_pairs (A := A) hB hAL hBL hz
        have e2 := card_pairs (A := B) hA hBL hAL hz
        have e3 := le_antisymm (card_conv_le hm hi hK hL hdc hA hB hAL hz)
          (card_conv_le hm hi hK hL hdc hB hA hBL hz)
        have := e1.trans (e3.trans e2.symm)
        rw [Finset.card_def, Finset.card_def, Finset.filter_val, Finset.filter_val] at this
        convert this
      · have hz' : ∀ C D : Finset G, (∀ a ∈ C, a ∈ L) → (∀ a ∈ D, a ∈ L) →
            Multiset.filter (fun p : G × G => (z : G ⧸ (J ⊓ L)) = ((p.1 * p.2 : G) : G ⧸ (J ⊓ L))) (C ×ˢ D).val = 0 := by
          intro C D hC hD
          rw [Multiset.filter_eq_nil]
          intro p hp e
          rw [Finset.mem_val, Finset.mem_product] at hp
          rw [QuotientGroup.eq] at e
          apply hz
          simpa [mul_assoc] using L.mul_mem (L.mul_mem (hC _ hp.1) (hD _ hp.2)) (L.inv_mem e.2)
        rw [hz' A B hAL hBL, hz' B A hBL hAL]
  funext h
  have key : ∀ C D : Finset G, dcOp C (dcOp D F) h =
      (((C ×ˢ D).val.map (fun p => ((p.1 * p.2 : G) : G ⧸ (J ⊓ L)))).map fun q => F (h * q.out)).sum := by
    intro C D
    rw [Multiset.map_map]
    change _ = ∑ p ∈ C ×ˢ D, _
    rw [Finset.sum_product]
    simp only [dcOp, Function.comp]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mul_assoc]
    exact hFK _ _ (QuotientGroup.out_eq' _).symm h
  rw [key, key, hms]

end GlobalTheory.DoubleCosetComm
end

section

open Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.ThetaInter

noncomputable section

namespace GlobalTheory.KerLaw

variable {V : Type} [AddCommGroup V] [Module ℂ V]

omit [Module ℂ V] in
theorem sum_reps {Λ₁ Λ₂ : AddSubgroup V} {S S' : Finset V} (h : IsReps Λ₁ Λ₂ S) (h' : IsReps Λ₁ Λ₂ S') (f : V → ℂ)
    (hf : ∀ x ∈ Λ₂, ∀ l ∈ Λ₂, l ∈ Λ₁ → f (x + l) = f x) : ∑ x ∈ S, f x = ∑ x ∈ S', f x := by
  choose! r hr hr' using h'.2.2
  refine Finset.sum_bij (fun x _ => r x) (fun x hx => hr x (h.1 x hx)) (fun x hx y hy e => ?_) (fun y hy => ?_) fun x hx => ?_
  · refine h.2.1 x hx y hy ?_
    have := Λ₁.sub_mem (hr' x (h.1 x hx)) (hr' y (h.1 y hy))
    rwa [e, sub_sub_sub_cancel_right] at this
  · obtain ⟨x, hx, e⟩ := h.2.2 y (h'.1 y hy)
    refine ⟨x, hx, h'.2.1 _ (hr x (h.1 x hx)) _ hy ?_⟩
    have := Λ₁.neg_mem (Λ₁.add_mem e (hr' x (h.1 x hx)))
    rwa [sub_add_sub_cancel, neg_sub] at this
  · have h2 := h'.1 _ (hr x (h.1 x hx))
    rw [← hf _ h2 _ (Λ₂.sub_mem (h.1 x hx) h2) (hr' x (h.1 x hx)), add_sub_cancel]

omit [Module ℂ V] in
theorem sum_reps_equiv {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (h : IsReps Λ₁ Λ₂ S) (φ : V ≃ V)
    (h2 : ∀ x, φ x ∈ Λ₂ ↔ x ∈ Λ₂) (h1 : ∀ x y, φ x - φ y ∈ Λ₁ ↔ x - y ∈ Λ₁) (f : V → ℂ)
    (hf : ∀ x ∈ Λ₂, ∀ l ∈ Λ₂, l ∈ Λ₁ → f (x + l) = f x) : ∑ x ∈ S, f (φ x) = ∑ x ∈ S, f x := by
  rw [← sum_reps (S := S.map φ.toEmbedding) ?_ h f hf, Finset.sum_map]
  · rfl
  refine ⟨fun x hx => ?_, fun x hx y hy e => ?_, fun y hy => ?_⟩
  · obtain ⟨x, hx', rfl⟩ := Finset.mem_map.1 hx
    exact (h2 x).2 (h.1 x hx')
  · obtain ⟨x, hx', rfl⟩ := Finset.mem_map.1 hx
    obtain ⟨y, hy', rfl⟩ := Finset.mem_map.1 hy
    rw [h.2.1 x hx' y hy' ((h1 x y).1 e)]
  · obtain ⟨y, rfl⟩ := φ.surjective y
    obtain ⟨x, hx, e⟩ := h.2.2 y ((h2 y).1 hy)
    exact ⟨φ x, Finset.mem_map_of_mem _ hx, (h1 y x).2 e⟩

variable {H : Sesq V} {α : V → ℂ}

theorem brk_eq (y t : V) : brk H y t = chi H t y := by
  unfold brk chi
  congr 1
  ring

theorem int_of_semi {A : AddSubgroup V} (hs : IsSemiChar H A α) {x y : V} (hx : x ∈ A) (hy : y ∈ A) : chi H x y = 1 := by
  have h1 := alpha_sq hs (A.add_mem hx hy)
  have h2 := alpha_sq hs hx
  have h3 := alpha_sq hs hy
  rw [hs.2 x hx y hy] at h1
  have h4 : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) *
      Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) = 1 := by
    linear_combination h1 - (α y * α y * h2 + h3) * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) ^ 2
  rw [← Complex.exp_add] at h4
  rw [chi, Complex.exp_neg, ← inv_one, ← h4]
  congr 2
  ring

theorem w_add (hH : IsHerm H) {A : AddSubgroup V} (hs : IsSemiChar H A α) {x y : V} (hx : x ∈ A) (hy : y ∈ A)
    (F : V → ℂ) (z : V) : α (x + y) * opU H (x + y) F z = α x * opU H x (fun w => α y * opU H y F w) z := by
  have h := int_of_semi hs hx hy
  have e : Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H x y : ℂ)) =
      Complex.exp (-(Real.pi * Complex.I * (altE H x y : ℂ))) := by
    rw [← mul_one (Complex.exp ((Real.pi : ℂ) * _ * _)), ← h, chi, ← Complex.exp_add]
    congr 1
    ring
  rw [opU_mul, opU_opU hH, hs.2 x hx y hy, e]
  ring

theorem chi_ne (x y : V) : chi H x y ≠ 0 := Complex.exp_ne_zero _

theorem xiL_stab (hH : IsHerm H) {A B Λ : AddSubgroup V} (hA : IsSemiChar H A α) (hB : IsSemiChar H B α)
    (hΛ : IsSemiChar H Λ α) {SX SA SB : Finset V} (hX : IsReps Λ A SX) (hSA : IsReps B (Λ ⊓ A) SA) (hSB : IsReps Λ B SB)
    (vol : ℝ) {θ : V → ℂ} (hθ : θ ∈ fixedBy H α Λ) {Φ : V → ℂ} (hΦ : InvOn A B Φ) (T : V ≃+ V)
    (tH : ∀ x y, H (T x) (T y) = H x y) (tα : ∀ x, α (T x) = α x) (tA : ∀ x, T x ∈ A ↔ x ∈ A) (tB : ∀ x, T x ∈ B ↔ x ∈ B)
    (tΛ : ∀ x, T x ∈ Λ ↔ x ∈ Λ) (tθ : ∀ z, θ (T z) = θ z) (k : ℂ) (tΦ : ∀ x, Φ (T x) = k * Φ x) (z : V) :
    xiL H α vol SX SA SB Φ θ (T z) = k * xiL H α vol SX SA SB Φ θ z := by
  have tU : ∀ x F w, opU H (T x) F (T w) = opU H x (fun v => F (T v)) w := fun x F w => by
    simp only [opU, tH, map_add (f := _)]
  have tc : ∀ x y, chi H (T x) (T y) = chi H x y := fun x y => by simp only [chi, altE, tH]
  have invA : ∀ x ∈ A, ∀ y ∈ B, ∀ t ∈ Λ ⊓ A, ∀ l ∈ Λ ⊓ A, l ∈ B →
      Φ (t + l - x) * (brk H y (t + l))⁻¹ = Φ (t - x) * (brk H y t)⁻¹ := fun x hx y hy t ht l hl hl' => by
    rw [add_sub_right_comm, hΦ _ (A.sub_mem ht.2 hx) l hl.2 hl', brk_eq, brk_eq, chi_add_left, int_of_semi hB hl' hy, mul_one]
  have hatT : ∀ x ∈ A, ∀ y ∈ B, hatS H vol SA (fun s => Φ (s - T x)) (T y) = k * hatS H vol SA (fun s => Φ (s - x)) y := by
    intro x hx y hy
    unfold hatS
    rw [← sum_reps_equiv hSA T.toEquiv (fun t => and_congr (tΛ t) (tA t)) (fun t u => by
      change T t - T u ∈ B ↔ _
      rw [← map_sub, tB]) (fun t => Φ (t - T x) * (brk H (T y) t)⁻¹) (invA _ ((tA x).2 hx) _ ((tB y).2 hy))]
    have : ∀ t, Φ (T.toEquiv t - T x) * (brk H (T y) (T.toEquiv t))⁻¹ = k * (Φ (t - x) * (brk H y t)⁻¹) := fun t => by
      change Φ (T t - T x) * (brk H (T y) (T t))⁻¹ = _
      rw [← map_sub, tΦ, brk_eq, brk_eq, tc, mul_assoc]
    simp only [this, ← Finset.mul_sum]
    ring
  have hatL : ∀ x ∈ A, ∀ y ∈ B, ∀ l ∈ A, l ∈ Λ →
      hatS H vol SA (fun s => Φ (s - (x + l))) y = (chi H l y)⁻¹ * hatS H vol SA (fun s => Φ (s - x)) y := by
    intro x hx y hy l hl hl'
    unfold hatS
    rw [← sum_reps_equiv hSA (Equiv.addRight l) (fun t => (Λ ⊓ A).add_mem_cancel_right ⟨hl', hl⟩) (fun t u => by simp)
      (fun t => Φ (t - (x + l)) * (brk H y t)⁻¹) (invA _ (A.add_mem hx hl) _ hy)]
    have : ∀ t, Φ (Equiv.addRight l t - (x + l)) * (brk H y (Equiv.addRight l t))⁻¹ =
        (chi H l y)⁻¹ * (Φ (t - x) * (brk H y t)⁻¹) := fun t => by
      rw [Equiv.coe_addRight, add_sub_add_right_eq_sub, brk_eq, brk_eq, chi_add_left, mul_inv]
      ring
    simp only [this, ← Finset.mul_sum]
    ring
  have invB : ∀ (Ψ : V → ℂ) w, ∀ y ∈ B, ∀ l ∈ B, l ∈ Λ →
      hatS H vol SA Ψ (y + l) * α (y + l) * opU H (y + l) θ w = hatS H vol SA Ψ y * α y * opU H y θ w := by
    intro Ψ w y hy l hl hl'
    have e1 : hatS H vol SA Ψ (y + l) = hatS H vol SA Ψ y := by
      unfold hatS
      congr 2
      refine Finset.sum_congr rfl fun t ht => ?_
      rw [brk_eq, brk_eq, chi_add_right, int_of_semi hΛ (hSA.1 t ht).1 hl', mul_one]
    rw [e1, mul_assoc, w_add hH hB hy hl, funext (hθ l hl'), mul_assoc]
  have xiT : ∀ x ∈ A, ∀ w, xiS H α vol SA SB (fun s => Φ (s - T x)) θ (T w) = k * xiS H α vol SA SB (fun s => Φ (s - x)) θ w := by
    intro x hx w
    unfold xiS sumU
    rw [← sum_reps_equiv hSB T.toEquiv tB (fun t u => by
      change T t - T u ∈ Λ ↔ _
      rw [← map_sub, tΛ]) _ (invB _ _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    change hatS H vol SA _ (T y) * α (T y) * opU H (T y) θ (T w) = _
    rw [hatT x hx y (hSB.1 y hy), tα, tU, funext tθ]
    ring
  have invX : ∀ w, ∀ x ∈ A, ∀ l ∈ A, l ∈ Λ →
      α (x + l) * opU H (x + l) (xiS H α vol SA SB (fun s => Φ (s - (x + l))) θ) w =
        α x * opU H x (xiS H α vol SA SB (fun s => Φ (s - x)) θ) w := by
    intro w x hx l hl hl'
    rw [w_add hH hA hx hl]
    congr 2
    funext v
    unfold xiS sumU
    rw [opU_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    beta_reduce
    rw [opU_mul, opU_comm hH, hatL x hx y (hSB.1 y hy) l hl hl', opU_of_fixed hΛ hθ hl', opU_mul]
    have h1 := alpha_sq hΛ hl'
    have h2 := chi_ne (H := H) l y
    field_simp
    linear_combination (hatS H vol SA (fun s => Φ (s - x)) y * α y * opU H y θ v) * h1
  unfold xiL
  rw [← sum_reps_equiv hX T.toEquiv tA (fun t u => by
      change T t - T u ∈ Λ ↔ _
      rw [← map_sub, tΛ]) _ (invX _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  change α (T x) * opU H (T x) (xiS H α vol SA SB (fun s => Φ (s - T x)) θ) (T z) = _
  rw [tα, tU, funext (xiT x (hX.1 x hx)), opU_mul]
  ring

end GlobalTheory.KerLaw
end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.N
open scoped Pointwise

namespace GlobalTheory

theorem bridge_field_le_unramified : ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    {N : NData R H what₂} (nbr : Br.NBr N) (i : N.Loc) (w : HeightOneSpectrum (𝓞 H.E))
    (hw : w ∈ placesOver H.E (N.l i)),
    N.l i ∉ H.small → N.l i ≠ H.q → N.l i ≠ H.d → (nbr i w hw).Kw.1 ≤ Loc.MaximalUnramifiedExtension (N.l i) := by
  intro R H what₂ N nbr i w hw h2 hq hd
  have hK := GlobalTheory.T.padicAlgCl_finite_dense_eq_adjoin' (N.l i) H.E ((nbr i w hw).j.comp (algebraMap H.E N.Om)) (nbr i w hw).Kw.1
    (nbr i w hw).j_E (nbr i w hw).Kw.2 (nbr i w hw).j_dense
  rw [hK, IntermediateField.adjoin_le_iff]
  rintro _ ⟨x, rfl⟩
  exact GlobalTheory.T.hostField_padicEmbedding_mem_maxUnramified H (N.l i) h2 hq hd _ x

end GlobalTheory
end
