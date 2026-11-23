module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle136
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle130
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle132
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle146
public import Mathlib.Analysis.Analytic.Order
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle144
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle133
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle108
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralBinomLePowCardPrimesBetween
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle145
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem intCast_zmod_of_dvd {K K₁ : ℕ} (h : K₁ ∣ K) {x y : ℤ} (hx : (x : ZMod K) = y) :
    (x : ZMod K₁) = y := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hx ⊢
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h) hx

theorem mem_Gamma_of_dvd {K K₁ : ℕ} (h : K₁ ∣ K) {δ : SL(2, ℤ)}
    (hδ : δ ∈ CongruenceSubgroup.Gamma K) : δ ∈ CongruenceSubgroup.Gamma K₁ := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast intCast_zmod_of_dvd h (y := 1) (by exact_mod_cast h1)
  · exact_mod_cast intCast_zmod_of_dvd h (y := 0) (by exact_mod_cast h2)
  · exact_mod_cast intCast_zmod_of_dvd h (y := 0) (by exact_mod_cast h3)
  · exact_mod_cast intCast_zmod_of_dvd h (y := 1) (by exact_mod_cast h4)

theorem mem_Gam_of_Gamma {N l K : ℕ} (hN : N ∣ K) (hl : l ∣ K) {δ : SL(2, ℤ)}
    (hδ : δ ∈ CongruenceSubgroup.Gamma K) : δ ∈ Gam N l := by
  have h1 := CongruenceSubgroup.Gamma_mem.1 (mem_Gamma_of_dvd hN hδ)
  have h2 := CongruenceSubgroup.Gamma_mem.1 (mem_Gamma_of_dvd hl hδ)
  show δ ∈ CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l
  exact Subgroup.mem_inf.mpr ⟨(CongruenceSubgroup.Gamma1_mem N δ).mpr ⟨h1.1, h1.2.2.2, h1.2.2.1⟩,
    CongruenceSubgroup.Gamma0_mem.mpr h2.2.2.1⟩

theorem entries_eq_one_of_mem_Gamma {K : ℕ} {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma K)
    (i j : Fin 2) :
    (((δ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) = (((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) := by
  obtain ⟨h1, h2, h3, h4⟩ := CongruenceSubgroup.Gamma_mem.1 hδ
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, h1, h2, h3, h4]

theorem exists_coc_near : ∀ (N l w : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ Φ,
    IsFam l w (Gam N l) Φ → ∀ n : ℕ, ∃ z : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)),
      IsCoc w (Gam N l) z ∧ Near z (Φ n) := by
  intro N l w hN hl hl2 hlN hw Φ hΦ n
  obtain ⟨hhom, hadd, hinv, -⟩ := hΦ
  obtain ⟨M₁, hM₁, hadd₁⟩ := hadd n
  obtain ⟨M₂, hM₂, hinv₂⟩ :=
    GlobalTheory.T.uniform_congruence_level_gamma1CapGamma0 N l (ZMod (l ^ n)) (Φ n) hN hl.pos ⟨M₁, hM₁, hadd₁⟩ (hinv n)
  obtain ⟨b, M', hlM', hMeq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (n := M₁ * M₂) (Nat.mul_pos hM₁ hM₂).ne' l hl.one_lt.ne'
  have hM'pos : 0 < M' := by
    rcases Nat.eq_zero_or_pos M' with h | h
    · exact absurd (h ▸ dvd_zero l) hlM'
    · exact h
  obtain ⟨c, hcΓ, hcomm, hcneg⟩ := GlobalTheory.T.exists_scalar_gamma1CapGamma0_mod_level N l (max b n) M' hN hl hl2 hlN hM'pos hlM'
  have hMK : M₁ * M₂ ∣ M' * N * l ^ (max b n) := by
    rw [hMeq]
    exact dvd_trans (mul_dvd_mul (pow_dvd_pow l (le_max_left b n)) (dvd_refl M')) ⟨N, by ring⟩
  have hM₁K : M₁ ∣ M' * N * l ^ (max b n) := dvd_trans (dvd_mul_right _ _) hMK
  have hM₂K : M₂ ∣ M' * N * l ^ (max b n) := dvd_trans (dvd_mul_left _ _) hMK
  have hnA : l ^ n ∣ l ^ (max b n) := pow_dvd_pow l (le_max_right b n)
  have hnK : l ^ n ∣ M' * N * l ^ (max b n) := dvd_trans hnA (dvd_mul_left _ _)
  obtain ⟨L1, L2, L3, -, -, L6, L7⟩ := GlobalTheory.T.twoVarPolySubstMatrix_basic_laws (ZMod (l ^ n))
  have hΔ : ((CongruenceSubgroup.Gamma (M' * N * l ^ (max b n))).subgroupOf (Gam N l)).Normal := by
    haveI := CongruenceSubgroup.Gamma_normal (M' * N * l ^ (max b n))
    exact Subgroup.normal_subgroupOf
  have h2 : IsUnit (2 : ZMod (l ^ n)) := by
    have hc : Nat.Coprime 2 (l ^ n) :=
      Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm hl2))
    simpa using (ZMod.isUnit_iff_coprime 2 (l ^ n)).mpr hc
  obtain ⟨z, hzS, hzc, hzΔ⟩ := GlobalTheory.T.exists_cocycle_extension_of_neg_central_element (Gam N l) (ZMod (l ^ n)) (MvPolynomial (Fin 2) (ZMod (l ^ n)))
    (fun g => (slP ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).toLinearMap)
    (fun g h v => by simp [L1]) (fun v => by simp [L2]) h2
    (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod (l ^ n)) w)
    (fun g v hv => by
      rw [MvPolynomial.mem_homogeneousSubmodule] at hv ⊢
      exact L3 _ _ _ hv)
    _ hΔ
    (fun δ hδ v => by
      have hδ' : (δ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma (l ^ n) :=
        mem_Gamma_of_dvd hnK (Subgroup.mem_subgroupOf.mp hδ)
      show slP _ v = v
      rw [L6 _ 1 v (entries_eq_one_of_mem_Gamma hδ'), L2])
    ⟨c, hcΓ⟩
    (fun v hv => by
      show slP _ v = -v
      rw [MvPolynomial.mem_homogeneousSubmodule] at hv
      rw [L6 _ (-1) v ?_, L7 w v hv, hw.neg_one_pow, neg_one_smul]
      intro i j
      have h := hcneg i j
      fin_cases i <;> fin_cases j <;> simp at h ⊢
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := -1) (by exact_mod_cast h)
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := 0) (by exact_mod_cast h)
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := 0) (by exact_mod_cast h)
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := -1) (by exact_mod_cast h))
    (fun g => by
      rw [Subgroup.mem_subgroupOf]
      simpa using hcomm g)
    (fun g => Φ n g)
    (fun δ _ => (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hhom n _))
    (fun δ hδ δ' hδ' => by
      have := hadd₁ _ (mem_Gamma_of_dvd hM₁K (Subgroup.mem_subgroupOf.mp hδ)) _
        (mem_Gamma_of_dvd hM₁K (Subgroup.mem_subgroupOf.mp hδ'))
      simpa using this)
    (fun g δ hδ => by
      have := hinv₂ g g.2 δ (mem_Gamma_of_dvd hM₂K (Subgroup.mem_subgroupOf.mp hδ))
      simpa using this)
  classical
  refine ⟨fun γ => if h : γ ∈ Gam N l then z ⟨γ, h⟩ else 0, ⟨?_, ?_⟩, ?_⟩
  · intro γ hγ
    simp only [dif_pos hγ]
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).mp (hzS _)
  · intro γ hγ δ hδ
    simp only [dif_pos hγ, dif_pos hδ, dif_pos (mul_mem hγ hδ)]
    simpa using hzc ⟨γ, hγ⟩ ⟨δ, hδ⟩
  · refine ⟨M' * N * l ^ (max b n) * l,
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hM'pos hN) (pow_pos hl.pos _)) hl.pos, fun δ hδ => ?_⟩
    have hδG : δ ∈ Gam N l :=
      mem_Gam_of_Gamma (dvd_mul_of_dvd_left ⟨M' * l ^ (max b n), by ring⟩ _) (dvd_mul_left _ _) hδ
    have hδK : δ ∈ CongruenceSubgroup.Gamma (M' * N * l ^ (max b n)) :=
      mem_Gamma_of_dvd (dvd_mul_right _ _) hδ
    simp only [dif_pos hδG]
    exact hzΔ ⟨δ, hδG⟩ (Subgroup.mem_subgroupOf.mpr hδK)

end GlobalTheory.KZ.H3
end

section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
open Filter Topology

noncomputable section

namespace GlobalTheory.KZ.H3.UnRoot

lemma isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

lemma isPreconnected_Hs : IsPreconnected Hs :=
  (convex_halfSpace_gt Complex.imLm.isLinear (0:ℝ)).isPreconnected

lemma eventually_of_germ_eq {φ ψ : ℂ → ℂ} (h : (φ : Mero) = (ψ : Mero)) {τ : ℂ} (hτ : τ ∈ Hs) :
    ∀ᶠ z in 𝓝[≠] τ, φ z = ψ z := by
  have h' : ∀ᶠ z in codiscreteWithin Hs, φ z = ψ z := Filter.Germ.coe_eq.mp h
  rw [Filter.eventually_iff, mem_codiscreteWithin] at h'
  have hd := Filter.disjoint_principal_right.mp (h' τ hτ)
  have hH : Hs ∈ 𝓝[≠] τ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hτ)
  filter_upwards [hH, hd] with z hz1 hz2
  by_contra hne
  exact hz2 ⟨hz1, hne⟩

lemma eq_nhds_of_punctured {F G : ℂ → ℂ} {τ : ℂ} (hF : ContinuousAt F τ) (hG : ContinuousAt G τ)
    (h : ∀ᶠ z in 𝓝[≠] τ, F z = G z) : F =ᶠ[𝓝 τ] G := by
  have hτ : F τ = G τ :=
    tendsto_nhds_unique (hF.tendsto.mono_left nhdsWithin_le_nhds)
      ((hG.tendsto.mono_left nhdsWithin_le_nhds).congr' (h.mono fun z hz => hz.symm))
  have h2 := eventually_nhdsWithin_iff.mp h
  filter_upwards [h2] with z hz
  by_cases hz' : z = τ
  · subst hz'; exact hτ
  · exact hz hz'

lemma order_ne_top {a : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (h0 : (a : Mero) ≠ 0) {τ : ℂ} (hτ : τ ∈ Hs) :
    analyticOrderAt a τ ≠ ⊤ := by
  intro htop
  apply h0
  have hA : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs
  have hz := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Hs hτ
    (analyticOrderAt_eq_top.mp htop)
  have : ∀ᶠ z in codiscreteWithin Hs, a z = (0 : ℂ → ℂ) z :=
    Filter.mem_of_superset (self_mem_codiscreteWithin Hs) fun z hz' => hz hz'
  rw [← Filter.Germ.coe_zero]
  exact Filter.Germ.coe_eq.mpr this

lemma germ_eq_of_eqOn {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) :=
  Filter.Germ.coe_eq.mpr (Filter.mem_of_superset (self_mem_codiscreteWithin Hs) fun z hz => h z hz)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

lemma num_ne_zero (X : Tower Ω ε) (f : X.Kˣ) {a b : ℂ → ℂ} (hb : (b : Mero) ≠ 0)
    (hf : X.an (f : X.K) * (b : Mero) = (a : Mero)) : (a : Mero) ≠ 0 := by
  intro h
  apply hb
  have e : X.an ((f⁻¹ : X.Kˣ) : X.K) * X.an (f : X.K) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  calc (b : Mero) = X.an ((f⁻¹ : X.Kˣ) : X.K) * (X.an (f : X.K) * b) := by rw [← mul_assoc, e, one_mul]
    _ = 0 := by rw [hf, h, mul_zero]

end GlobalTheory.KZ.H3.UnRoot

namespace GlobalTheory.KZ.H3.UnRoot

theorem exists_isRoot_of_mem_Un : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), JHol X →
    ∀ (m : ℕ), 0 < m → ∀ f ∈ X.Un m, ∃ a b : ℂ → ℂ, IsRoot X m f a b := by
  intro Ω _ _ ε X hj m hm f hf
  obtain ⟨a0, b0, ha0, hb0, hb0ne, hf0⟩ := X.an_mero (f : X.K)
  have ha0ne : (a0 : Mero) ≠ 0 := num_ne_zero X f hb0ne hf0
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hA : ∀ {c : ℂ → ℂ}, DifferentiableOn ℂ c Hs → ∀ τ ∈ Hs, AnalyticAt ℂ c τ :=
    fun hc τ hτ => hc.analyticOnNhd isOpen_Hs τ hτ
  have hord : ∀ τ ∈ Hs, ∃ k : ℕ, analyticOrderAt (a0 * b0 ^ m') τ = (((m' + 1) * k : ℕ) : ℕ∞) := by
    intro τ hτ
    obtain ⟨W, hW, hWmem⟩ := GlobalTheory.T.exists_tower_place_at_upperHalfPlane_point Ω ε X hj τ hτ
    obtain ⟨g, hg⟩ := hf W hW
    set u : X.K := (f : X.K) / (g : X.K) ^ (m' + 1) with hu
    have hgm : (g : X.K) ^ (m' + 1) ≠ 0 := pow_ne_zero _ g.ne_zero
    have hune : u ≠ 0 := div_ne_zero f.ne_zero hgm
    have huW : u ∈ W := (W.valuation_le_one_iff u).mp hg.le
    have huW' : u⁻¹ ∈ W := (W.valuation_le_one_iff u⁻¹).mp (by rw [map_inv₀, hg, inv_one])
    obtain ⟨φ, hφ, hφa⟩ := (hWmem u).mp huW
    obtain ⟨ψ, hψ, hψa⟩ := (hWmem u⁻¹).mp huW'

    have hφψ : ((φ * ψ : ℂ → ℂ) : Mero) = ((1 : ℂ → ℂ) : Mero) := by
      rw [Filter.Germ.coe_mul, Filter.Germ.coe_one, ← hφ, ← hψ, ← map_mul, mul_inv_cancel₀ hune, map_one]
    have hφτ : φ τ ≠ 0 := by
      have e : φ τ * ψ τ = 1 := (eq_nhds_of_punctured (hφa.continuousAt.mul hψa.continuousAt) continuousAt_const
        (eventually_of_germ_eq hφψ hτ)).self_of_nhds
      intro h0
      rw [h0, zero_mul] at e
      exact zero_ne_one e

    obtain ⟨a1, b1, ha1, hb1, hb1ne, hg1⟩ := X.an_mero (g : X.K)
    have ha1ne : (a1 : Mero) ≠ 0 := num_ne_zero X g hb1ne hg1
    have hfu : X.an (f : X.K) = X.an u * X.an (g : X.K) ^ (m' + 1) := by
      rw [← map_pow, ← map_mul, hu, div_mul_cancel₀ _ hgm]
    have hgerm : ((a0 * b1 ^ (m' + 1) : ℂ → ℂ) : Mero) = ((φ * a1 ^ (m' + 1) * b0 : ℂ → ℂ) : Mero) := by
      simp only [Filter.Germ.coe_mul, Filter.Germ.coe_pow]
      rw [← hf0, ← hg1, hfu, hφ]
      ring
    have hev := eq_nhds_of_punctured
      ((hA ha0 τ hτ).continuousAt.mul ((hA hb1 τ hτ).continuousAt.pow _))
      ((hφa.continuousAt.mul ((hA ha1 τ hτ).continuousAt.pow _)).mul (hA hb0 τ hτ).continuousAt)
      (eventually_of_germ_eq hgerm hτ)
    have hcong := analyticOrderAt_congr hev
    rw [analyticOrderAt_mul (hA ha0 τ hτ) ((hA hb1 τ hτ).pow _), analyticOrderAt_pow (hA hb1 τ hτ),
      analyticOrderAt_mul (hφa.mul ((hA ha1 τ hτ).pow _)) (hA hb0 τ hτ),
      analyticOrderAt_mul hφa ((hA ha1 τ hτ).pow _), analyticOrderAt_pow (hA ha1 τ hτ),
      hφa.analyticOrderAt_eq_zero.mpr hφτ] at hcong
    obtain ⟨oA0, orbitMap_conj_smul_zero⟩ := ENat.ne_top_iff_exists.mp (order_ne_top ha0 ha0ne hτ)
    obtain ⟨oB0, eB0⟩ := ENat.ne_top_iff_exists.mp (order_ne_top hb0 hb0ne hτ)
    obtain ⟨oA1, orbitMap_conj_smul_one⟩ := ENat.ne_top_iff_exists.mp (order_ne_top ha1 ha1ne hτ)
    obtain ⟨oB1, eB1⟩ := ENat.ne_top_iff_exists.mp (order_ne_top hb1 hb1ne hτ)
    rw [← orbitMap_conj_smul_zero, ← eB0, ← orbitMap_conj_smul_one, ← eB1] at hcong
    have heq : oA0 + (m' + 1) * oB1 = (m' + 1) * oA1 + oB0 := by
      simp only [nsmul_eq_mul, zero_add] at hcong
      exact_mod_cast hcong
    have hdvd : (m' + 1) ∣ oA0 + m' * oB0 :=
      Int.natCast_dvd_natCast.mp ⟨(oA1 : ℤ) + oB0 - oB1, by
        have := congrArg (fun n : ℕ => (n : ℤ)) heq
        push_cast at this ⊢
        linear_combination this⟩
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k, ?_⟩
    rw [analyticOrderAt_mul (hA ha0 τ hτ) ((hA hb0 τ hτ).pow _), analyticOrderAt_pow (hA hb0 τ hτ),
      ← orbitMap_conj_smul_zero, ← eB0, ← hk]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  obtain ⟨r, hr, hrm⟩ := GlobalTheory.T.exists_holomorphic_root_upperHalfPlane (a0 * b0 ^ m') (m' + 1) hm (ha0.mul (hb0.pow _)) hord
  refine ⟨r, b0, hr, hb0, hb0ne, ?_⟩
  have e1 : ((r ^ (m' + 1) : ℂ → ℂ) : Mero) = ((a0 * b0 ^ m' : ℂ → ℂ) : Mero) :=
    germ_eq_of_eqOn fun z hz => by simpa using hrm z hz
  simp only [Filter.Germ.coe_pow, Filter.Germ.coe_mul] at e1 ⊢
  rw [e1, ← hf0]
  ring

end GlobalTheory.KZ.H3.UnRoot
end
end

section

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem add_le_sum_of_mem_of_ne {s : Multiset ℕ} {p q : ℕ} (hp : p ∈ s) (hq : q ∈ s) (h : p ≠ q) : p + q ≤ s.sum := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hp
  have hq' : q ∈ t := (Multiset.mem_cons.mp hq).resolve_left (Ne.symm h)
  obtain ⟨u, rfl⟩ := Multiset.exists_cons_of_mem hq'
  rw [Multiset.sum_cons, Multiset.sum_cons, ← add_assoc]
  exact Nat.le_add_right _ _

theorem card_perm_no_long_cycle (N : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, N < 2 * p) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∀ p ∈ S, p ∉ σ.partition.parts).card +
      ∑ p ∈ S, (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts).card = N.factorial := by
  have hsum : ∀ σ : Equiv.Perm (Fin N), σ.partition.parts.sum = N := fun σ => by
    simpa using σ.partition.parts_sum
  have hdisj : (S : Set ℕ).PairwiseDisjoint
      fun p => Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts := by
    intro p hp q hq hpq
    rw [Function.onFun, Finset.disjoint_filter]
    intro σ _ hpσ hqσ
    have h1 := add_le_sum_of_mem_of_ne hpσ hqσ hpq
    rw [hsum σ] at h1
    have h2 := hS p hp
    have h3 := hS q hq
    omega
  rw [← Finset.card_biUnion hdisj]
  have hc : (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∀ p ∈ S, p ∉ σ.partition.parts) =
      (S.biUnion fun p => Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts)ᶜ := by
    ext σ
    simp
  rw [hc, Finset.card_compl_add_card, Fintype.card_perm, Fintype.card_fin]

theorem mass_not_hasPrimeFactor_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 100000 ≤ N →
    (mass g N fun f => ¬ HasPrimeFactor g N f) ≤ 1 - 1 / (10 * Real.log N) := by
  intro g _ N hN
  set S := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hSdef
  have hS : ∀ p ∈ S, N < 2 * p := fun p hp => (Finset.mem_filter.mp hp).2.2.1
  have hSN : ∀ p ∈ S, p ≤ N := fun p hp =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
  have hmono : (mass g N fun f => ¬ HasPrimeFactor g N f) ≤
      mass g N fun f => ∀ p ∈ S, p ∉ degType g f := by
    have hsub : (sqSet g N).filter (fun f => ¬ HasPrimeFactor g N f) ⊆
        (sqSet g N).filter (fun f => ∀ p ∈ S, p ∉ degType g f) := by
      intro f hf
      rw [Finset.mem_filter] at hf ⊢
      refine ⟨hf.1, ?_⟩
      intro p hp hpf
      apply hf.2
      unfold degType at hpf
      unfold HasPrimeFactor
      obtain ⟨h, hh, rfl⟩ := Multiset.mem_map.mp hpf
      obtain ⟨-, hpr, h2, h3⟩ := Finset.mem_filter.mp hp
      exact ⟨h, UniqueFactorizationMonoid.irreducible_of_normalized_factor h hh,
        UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hh, hpr, h2, h3⟩
    unfold mass
    convert Finset.sum_le_sum_of_subset_of_nonneg (f := fun f => ((torusCard g f : ℝ))⁻¹) hsub
      (fun f _ _ => by positivity)
  have hT := GlobalTheory.T.mass_degType_le_card_cycleType_div g N (fun m : Multiset ℕ => ∀ p ∈ S, p ∉ m)
  have hcount := card_perm_no_long_cycle N S hS
  have hlong : ∀ p ∈ S, ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      p ∈ σ.partition.parts).card : ℝ) = N.factorial / p := by
    intro p hp
    have hp0 : 0 < p := by have := hS p hp; omega
    have hp0' : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
    rw [eq_div_iff hp0']
    exact_mod_cast card_perm_long_cycle N p (hS p hp) (hSN p hp)
  have hfac : (N.factorial : ℝ) ≠ 0 := by positivity
  have hratio : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      ∀ p ∈ S, p ∉ σ.partition.parts).card : ℝ) / N.factorial = 1 - ∑ p ∈ S, (1 : ℝ) / p := by
    have hc : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
        ∀ p ∈ S, p ∉ σ.partition.parts).card : ℝ) = N.factorial - ∑ p ∈ S, (N.factorial : ℝ) / p := by
      rw [← Finset.sum_congr rfl hlong]
      have := congrArg (fun n : ℕ => (n : ℝ)) hcount
      push_cast at this
      linarith
    rw [hc, sub_div, div_self hfac, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [div_right_comm, div_self hfac]
  have hprimes := inv_log_le_sum_inv_primes_between N hN
  calc _ ≤ _ := hmono
    _ ≤ _ := hT
    _ = 1 - ∑ p ∈ S, (1 : ℝ) / p := by convert hratio
    _ ≤ 1 - 1 / (10 * Real.log N) := by linarith

end GlobalTheory.BadShare
end

section

open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem mass_true_le_one (g : ℕ) [Fact g.Prime] (N : ℕ) : (mass g N fun _ => True) ≤ 1 := by
  refine (GlobalTheory.T.mass_degType_le_card_cycleType_div g N (fun _ => True)).trans (le_of_eq ?_)
  rw [Finset.filter_true, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  have hN : (N.factorial : ℝ) ≠ 0 := by positivity
  exact div_self hN

theorem mass_dvd_le (g : ℕ) [Fact g.Prime] (N a : ℕ) (h : (ZMod g)[X]) (hh : h ∈ sqSet g a) :
    (mass g N fun f => h ∣ f) ≤ ((torusCard g h : ℝ))⁻¹ * mass g (N - a) fun _ => True := by
  obtain ⟨hmon, hdeg, -, -⟩ := mem_sqSet.1 hh
  have hh0 : h ≠ 0 := hmon.ne_zero
  unfold mass
  set S := (sqSet g N).filter fun f => h ∣ f with hS
  have hfac : ∀ f ∈ S, h * (f /ₘ h) = f := by
    intro f hf
    have hd : h ∣ f := (Finset.mem_filter.1 hf).2
    have e := Polynomial.modByMonic_add_div f h
    rwa [(Polynomial.modByMonic_eq_zero_iff_dvd hmon).2 hd, zero_add] at e
  have hmem : ∀ f ∈ S, f /ₘ h ∈ sqSet g (N - a) := by
    intro f hf
    obtain ⟨fmon, fdeg, fsq, fc0⟩ := mem_sqSet.1 (Finset.mem_filter.1 hf).1
    have e := hfac f hf
    have umon : (f /ₘ h).Monic := hmon.of_mul_monic_left (by rw [e]; exact fmon)
    refine mem_sqSet.2 ⟨umon, ?_, ?_, ?_⟩
    · have hd := hmon.natDegree_mul umon
      rw [e, fdeg, hdeg] at hd
      omega
    · exact Squarefree.of_mul_right (by rw [e]; exact fsq)
    · intro hz
      apply fc0
      rw [← e, Polynomial.mul_coeff_zero, hz, mul_zero]
  have hinj : Set.InjOn (fun f => f /ₘ h) (S : Set (ZMod g)[X]) := by
    intro f hf f' hf' hq
    rw [← hfac f hf, ← hfac f' hf']
    exact congrArg (h * ·) hq
  have hterm : ∀ f ∈ S, ((torusCard g f : ℝ))⁻¹ =
      ((torusCard g h : ℝ))⁻¹ * ((torusCard g (f /ₘ h) : ℝ))⁻¹ := by
    intro f hf
    have e := hfac f hf
    have hu0 : f /ₘ h ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at e
      exact (mem_sqSet.1 (Finset.mem_filter.1 hf).1).1.ne_zero e.symm
    conv_lhs => rw [← e]
    rw [torusCard_mul hh0 hu0, Nat.cast_mul, mul_inv]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 (Nat.cast_nonneg _))
  rw [← Finset.sum_image (f := fun u => ((torusCard g u : ℝ))⁻¹) hinj, Finset.filter_true]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => inv_nonneg.2 (Nat.cast_nonneg _))
  intro u hu
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 hu
  exact hmem f hf

theorem divisor_bound : ∀ (g : ℕ) [Fact g.Prime], (∀ N : ℕ, (mass g N fun _ => True) ≤ 1) ∧
    ∀ (N a : ℕ), ∀ h ∈ sqSet g a, (mass g N fun f => h ∣ f) ≤ ((torusCard g h : ℝ))⁻¹ := by
  intro g _
  refine ⟨mass_true_le_one g, fun N a h hh => ?_⟩
  refine (mass_dvd_le g N a h hh).trans ?_
  exact mul_le_of_le_one_right (inv_nonneg.2 (Nat.cast_nonneg _)) (mass_true_le_one g _)

end GlobalTheory.BadShare
end
