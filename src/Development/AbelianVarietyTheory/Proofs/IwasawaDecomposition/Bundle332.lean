module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle053
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle318
import Formalism.LocalRingCardinality.ConjSqrtMinusD
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle315
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle319
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
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

section

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host NumberField IsDedekindDomain Polynomial
open GlobalTheory.WeilDeligne

section

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

abbrev WDAt (N : NData R H what₂) (w : PlE H) : Type :=
  WD (E := H.E) (A := N.plOm.1 w) (w := w) (N.plOm.2 w)

abbrev UnrWDFam (N : NData R H what₂) (a : ℕ) : Type :=
  {p : (∀ w, WDAt N w) × ((H.E →+* ℂ) → Multiset ℂ) //
    (∀ w, (p.1 w).unr ∧ (p.1 w).lpDim = a) ∧ ∀ τ, Multiset.card (p.2 τ) = a}

theorem lpUnr_negOne_spec (N : NData R H what₂) (w : PlE H) :
    (WD.lpUnr (h := N.plOm.2 w) {-1}).unr ∧
      (WD.lpUnr (h := N.plOm.2 w) {-1}).frobEig = {-1} ∧
      (WD.lpUnr (h := N.plOm.2 w) {-1}).lpDim = 1 := by
  obtain ⟨hu, he, hd⟩ := WD.lpUnr_spec (h := N.plOm.2 w) ({-1} : Multiset ℂ) (by simp)
  exact ⟨hu, he, hd.trans (Multiset.card_singleton _)⟩

def negOneWDFam (N : NData R H what₂) : UnrWDFam N 1 :=
  ⟨(fun w => WD.lpUnr (h := N.plOm.2 w) {-1}, fun _ => {0}),
    fun w => ⟨(lpUnr_negOne_spec N w).1, (lpUnr_negOne_spec N w).2.2⟩, fun _ => rfl⟩

theorem UnrWDFam.exists_frobEig {N : NData R H what₂} (χ : UnrWDFam N 1) (w : PlE H) :
    ∃ c, (χ.1.1 w).frobEig = {c} := by
  have hu : (χ.1.1 w).unr := (χ.2.1 w).1
  have hd : (χ.1.1 w).lpDim = 1 := (χ.2.1 w).2
  have hc : Multiset.card (χ.1.1 w).frobEig = 1 := ((WD.unramified_laws (N.plOm.2 w)).2.2.2.2.2.2.2.2.2.2.2.2.1 _ hu).trans hd
  exact Multiset.card_eq_one.mp hc




def nAutWD (N : NData R H what₂) (hE : IsEmpty N.Loc) (pl : ∀ k, N.PlG k → PlE H)
    (h1 : ∀ k v, pl k v ∈ placesOver H.E (H.g k)) (h2 : ∀ k, Function.Injective (pl k))
    (h3 : ∀ k v v', ¬ IsConjPl H (pl k v) (pl k v'))
    (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ) (γ : Fin 2 → PlE H → G H.E N.Om) : NAut N where
  LP := WDAt N
  lpDim := WD.lpDim
  lpZero := fun w => WD.lpZero (h := N.plOm.2 w)
  lpSum := WD.lpSum
  lpTw := WD.lpTw
  lpChar := WD.lpChar
  lpUnr := fun w => WD.lpUnr (h := N.plOm.2 w)
  mono0 := WD.mono0
  unr := WD.unr
  frobEig := WD.frobEig
  tempered := WD.tempered
  inePol := WD.inePol
  items₂ := fun k w a => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩; WD.lab (τ k) (γ k w) a
  lpDim_zero := fun w => WD.lpDim_zero _
  lpDim_sum := WD.lpDim_sum
  lpDim_tw := WD.lpDim_tw
  lpUnr_spec := fun _ => WD.lpUnr_spec
  unr_sum := WD.unr_sum
  monomial_sum_iff := WD.monomial_sum_iff
  frobEig_sum := fun a b _ _ => WD.frobEig_lpSum a b
  unr_tw := WD.unr_tw
  monomial_twist_iff := WD.monomial_twist_iff
  frobEig_tw := WD.frobEig_tw
  frobEig_char := fun a χ c ha hχ _ => WD.frobEig_char a χ c ha hχ
  lpDim_char := WD.lpDim_char
  unr_char := fun a χ _ => WD.unr_lpChar a χ
  monomial_char_iff := WD.monomial_char_iff
  lpZero_unr := fun _ => WD.lpZero_unr
  frobEig_zero := fun _ => WD.frobEig_zero
  lpSum_zero := WD.lpSum_zero
  lpSum_comm := WD.lpSum_comm
  lpSum_assoc := WD.lpSum_assoc
  lpTw_zero := WD.lpTw_zero
  lpTw_add := WD.lpTw_add
  lpTw_sum := WD.lpTw_sum
  unr_eq_lpUnr := WD.unr_eq_lpUnr
  unr_mono0 := WD.unr_mono0
  frobEig_ne_zero := WD.frobEig_ne_zero
  frobEig_card := fun a _ => WD.card_eig a _
  tempered_unr := WD.tempered_unr
  inePol_sum := WD.inePol_sum
  inePol_tw := WD.inePol_tw
  unr_iff_ine := WD.unr_iff_ine
  inertiaCharpoly_zero := fun k w => by
    let : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    have hzero := WD.lpDim_zero (N.plOm.2 w)
    exact WD.lab_of_lpDim_eq_zero (τ k) (γ k w) hzero
  inertiaCharpoly_add := fun k _ a b => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩; WD.lab_lpSum _ _ a b
  CG := UnrWDFam N
  csd := fun π => ∀ w w', IsConjPl H w w' → (π.1.1 w').frobEig = (π.1.1 w).frobEig.map (·⁻¹)
  ralg := fun {a} π => ∀ τ, (π.1.2 τ).Nodup ∧ ∀ z ∈ π.1.2 τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2
  locG := fun π w => π.1.1 w
  locG_dim := fun π w => (π.2.1 w).2
  locG_unr_ae := fun π => Filter.Eventually.of_forall fun w => (π.2.1 w).1
  tw := fun π χ => ⟨(fun w => (π.1.1 w).lpChar (χ.1.1 w), fun τ => (π.1.2 τ).map (· + (χ.1.2 τ).sum)),
    fun w => ⟨WD.unr_lpChar _ _ (π.2.1 w).1 (χ.2.1 w).1, (WD.lpDim_char _ _ (χ.2.1 w).2).trans (π.2.1 w).2⟩,
    fun τ => (Multiset.card_map _ _).trans (π.2.2 τ)⟩
  locG_tw := fun _ _ _ => rfl
  infG := fun π τ => π.1.2 τ
  infG_card := fun π τ => π.2.2 τ
  ralg_def := fun _ => Iff.rfl
  infG_tw := fun π χ τ s h => by
    show (π.1.2 τ).map (· + (χ.1.2 τ).sum) = _
    rw [show χ.1.2 τ = {s} from h, Multiset.sum_singleton]
  csd_tw := fun π χ hχ hπ w w' h => by
    obtain ⟨c, hc⟩ := χ.exists_frobEig w
    have hc' := hχ w w' h
    rw [hc, Multiset.map_singleton] at hc'
    show ((π.1.1 w').lpChar (χ.1.1 w')).frobEig = ((π.1.1 w).lpChar (χ.1.1 w)).frobEig.map (·⁻¹)
    rw [WD.frobEig_char _ _ _ (π.2.1 w').1 (χ.2.1 w').1 hc', WD.frobEig_char _ _ _ (π.2.1 w).1 (χ.2.1 w).1 hc,
      hπ w w' h, Multiset.map_map, Multiset.map_map]
    exact Multiset.map_congr rfl fun x _ => (mul_inv _ _).symm
  csd_unr := fun π w w' h hc _ => ⟨(π.2.1 w').1, h w w' hc⟩
  etaT := negOneWDFam N
  etaTinv := negOneWDFam N
  etaT_unr := fun w => (lpUnr_negOne_spec N w).1
  etaT_inert := fun w _ => (lpUnr_negOne_spec N w).2.1
  etaTinv_def := fun w => ⟨(lpUnr_negOne_spec N w).1, by
    show (WD.lpUnr (h := N.plOm.2 w) {-1}).frobEig =
      (WD.lpUnr (h := N.plOm.2 w) {-1}).frobEig.map (·⁻¹)
    rw [(lpUnr_negOne_spec N w).2.1]
    simp⟩
  etaT_split := fun w w' _ _ a b ha hb => by
    have ha' : (-1 : ℂ) = a := Multiset.singleton_inj.1 ((lpUnr_negOne_spec N w).2.1.symm.trans ha)
    have hb' : (-1 : ℂ) = b := Multiset.singleton_inj.1 ((lpUnr_negOne_spec N w').2.1.symm.trans hb)
    rw [← ha', ← hb']
    norm_num
  plGw := pl
  plGw_over := h1
  plGw_inj := h2
  plGw_nconj := h3
  iotaQ := fun i => hE.elim i
  iotaQC := fun i => hE.elim i
  iota_LL := fun i => hE.elim i
  iotaQ_alg := fun i => hE.elim i
  muC := fun i => hE.elim i
  muC_csd := fun i => hE.elim i
  AV := fun i => hE.elim i
  finAV := fun i => hE.elim i
  ptV := fun i => hE.elim i
  typeV := fun i => hE.elim i
  typeV_ne := fun i => hE.elim i
  typeV_indep := fun i => hE.elim i
  typeV_top := fun i => hE.elim i
  pt_surj := fun i => hE.elim i
  eig_dim := fun i => hE.elim i
  locV := fun i => hE.elim i
  satV := fun i => hE.elim i
  locV_unr := fun i => hE.elim i
  pt_loc := fun i => hE.elim i
  infWt := fun i => hE.elim i
  locW := fun i => hE.elim i
  satW := fun i => hE.elim i
  lab_loc := fun i => hE.elim i
  wdOf := fun i => hE.elim i
  wdOf_dim := fun i => hE.elim i
  wdOf_unr := fun i => hE.elim i
  wdOf_frob := fun i => hE.elim i
  wdOf_ine := fun i => hE.elim i
  wdOf_mono0 := fun i => hE.elim i
  IsCrysW := fun i => hE.elim i
  IsPotCrysW := fun i => hE.elim i
  IsdRW := fun i => hE.elim i
  jumpsW := fun i => hE.elim i
  wdOf_unrL := fun i => hE.elim i
  wdOf_mono0L := fun i => hE.elim i
  jumpsInf := fun i => hE.elim i
  locAutHodgeTateWeightsLevelZero := fun i => hE.elim i
  jumpsInf_def := fun i => hE.elim i
  locAut_hodgeTateWeightsLevelZero_def := fun i => hE.elim i
  chi_mu := fun i => hE.elim i
  kFbar := fun i => hE.elim i

def wdTieWD (N : NData R H what₂) (hE : IsEmpty N.Loc) (pl : ∀ k, N.PlG k → PlE H)
    (h1 : ∀ k v, pl k v ∈ placesOver H.E (H.g k)) (h2 : ∀ k, Function.Injective (pl k))
    (h3 : ∀ k v v', ¬ IsConjPl H (pl k v) (pl k v'))
    (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ) (γ : Fin 2 → PlE H → G H.E N.Om) :
    GlobalTheory.RowTie.WDTie N (nAutWD N hE pl h1 h2 h3 τ γ) :=
  ⟨fun _ => Equiv.refl _, fun _ _ => rfl, fun _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ => Iff.rfl, fun _ _ => Iff.rfl, fun _ _ _ => rfl, fun _ _ => Iff.rfl, fun _ _ _ _ => rfl⟩

end

end GlobalTheory.HeightCounting

end
end

section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open scoped BigOperators

namespace GlobalTheory.Mem.Col2.SplitPrime

theorem mem_xor {A : Type*} [CommRing A] (P : Ideal A) (hP : P.IsPrime) (p t m : ℤ) (hp : (p : A) ∈ P) (a a' : A)
    (hm : a * a' = (p : A) * m) (ht : a + a' = t) (hc : IsCoprime p t) :
    (a ∈ P ∧ a' ∉ P) ∨ (a' ∈ P ∧ a ∉ P) := by
  have hnot : ¬ (a ∈ P ∧ a' ∈ P) := by
    rintro ⟨h1, h2⟩
    have h3 : (t : A) ∈ P := ht ▸ P.add_mem h1 h2
    obtain ⟨u, v, huv⟩ := hc
    have h4 : (u : A) * p + (v : A) * t = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → A) huv
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (h4 ▸ P.add_mem (P.mul_mem_left _ hp) (P.mul_mem_left _ h3)))
  have h5 : a * a' ∈ P := hm ▸ P.mul_mem_right _ hp
  rcases hP.mem_or_mem h5 with h | h
  · exact Or.inl ⟨h, fun h' => hnot ⟨h, h'⟩⟩
  · exact Or.inr ⟨h, fun h' => hnot ⟨h', h⟩⟩

theorem exists_over (K : Type*) [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    ∃ 𝔭 : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ 𝔭.asIdeal := by
  have hpr : (Ideal.span {(p : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 K) (Ideal.span {(p : ℤ)}) ⊥ (by
    rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K)))]
    exact bot_le)
  have hmem : (p : 𝓞 K) ∈ Q := by
    have : (p : ℤ) ∈ Ideal.under ℤ Q := by
      rw [hQc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ, ?_⟩, hmem⟩
  rintro rfl
  exact (Nat.cast_ne_zero.2 hp.ne_zero) ((Ideal.mem_bot).1 hmem)

theorem exists_elt {R : Ranks} (H : Host R) (p : ℕ) (hp : p.Prime) (hs : Th.SplitK H p) :
    ∃ (a : H.K) (t m : ℤ), IsIntegral ℤ a ∧ a * HostK.conjK H a = (p : H.K) * m ∧ a + HostK.conjK H a = t ∧
      IsCoprime (p : ℤ) t := by
  set θ : H.K := ⟨H.sqrtMinusD, HostK.sqrt_mem H⟩ with hθ
  have hsq : θ ^ 2 = -(H.d : H.K) := Subtype.ext (by simpa [hθ] using H.sqrtMinusD_sq)
  have hcj : HostK.conjK H θ = -θ := Subtype.ext (by simpa [hθ, HostK.coe_conjK] using H.conj_sqrtMinusD)
  by_cases h2 : p = 2
  · subst h2
    obtain ⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 8 * m := by
      have := H.hyp.2.2.2.1
      exact ⟨(H.d + 1) / 8, by omega⟩
    have hm' : (H.d : H.K) + 1 = 8 * m := by exact_mod_cast hm
    refine ⟨(1 + θ) / 2, 1, m, HostK.isIntegral_half H, ?_, ?_, isCoprime_one_right⟩
    · rw [map_div₀, map_add (f := _), map_one, hcj, map_ofNat]
      push_cast
      linear_combination (-1 / 4 : H.K) * hsq + (1 / 4 : H.K) * hm'
    · rw [map_div₀, map_add (f := _), map_one, hcj, map_ofNat]
      push_cast
      ring
  · have hj : jacobiSym (-(H.d : ℤ)) p = 1 := hs.resolve_left h2
    haveI : Fact p.Prime := ⟨hp⟩
    rw [← jacobiSym.legendreSym.to_jacobiSym] at hj
    have hne : ((-(H.d : ℤ) : ℤ) : ZMod p) ≠ 0 := by
      intro h
      rw [(legendreSym.eq_zero_iff p _).2 h] at hj
      exact zero_ne_one hj
    obtain ⟨s, hs'⟩ := (legendreSym.eq_one_iff p hne).1 hj
    obtain ⟨r, rfl⟩ := ZMod.intCast_surjective s
    have hr : ¬ (p : ℤ) ∣ r := by
      intro h
      rw [hs', (ZMod.intCast_zmod_eq_zero_iff_dvd r p).2 h] at hne
      exact hne (mul_zero _)
    have hdiv : (p : ℤ) ∣ r * r + H.d := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast at hs' ⊢
      linear_combination -hs'
    obtain ⟨m, hm⟩ := hdiv
    have hm' : (r : H.K) * r + H.d = (p : H.K) * m := by exact_mod_cast congrArg (Int.cast : ℤ → H.K) hm
    have hθi : IsIntegral ℤ θ := by
      refine IsIntegral.of_pow two_pos ?_
      rw [hsq]
      exact (isIntegral_natCast H.d).neg
    have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    refine ⟨r + θ, 2 * r, m, (isIntegral_intCast r).add hθi, ?_, ?_, ?_⟩
    · rw [map_add (f := _), map_intCast, hcj]
      linear_combination hm' - hsq
    · rw [map_add (f := _), map_intCast, hcj]
      push_cast
      ring
    · refine (hpi.coprime_iff_not_dvd).2 fun h => ?_
      rcases hpi.dvd_or_dvd h with h | h
      · have h' : p ∣ 2 := by exact_mod_cast h
        exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h')
      · exact hr h

theorem exists_prime_not_conj (R : Ranks) (H : Host R) (p : ℕ) (hp : p.Prime) (hs : Th.SplitK H p) :
    ∃ (𝔭 : HeightOneSpectrum (𝓞 H.K)) (α β : 𝓞 H.K), (p : 𝓞 H.K) ∈ 𝔭.asIdeal ∧ α ∈ 𝔭.asIdeal ∧ β ∉ 𝔭.asIdeal ∧
      (β : H.K) = HostK.conjK H α := by
  obtain ⟨a, t, m, hai, hm, ht, hc⟩ := exists_elt H p hp hs
  have hai' : IsIntegral ℤ (HostK.conjK H a) := by
    have : HostK.conjK H a = t - a := by linear_combination ht
    rw [this]
    exact (isIntegral_intCast t).sub hai
  obtain ⟨𝔭, h𝔭⟩ := exists_over H.K p hp
  let x : 𝓞 H.K := ⟨a, hai⟩
  let y : 𝓞 H.K := ⟨HostK.conjK H a, hai'⟩
  have hx : (x : H.K) = a := rfl
  have hy : (y : H.K) = HostK.conjK H a := rfl
  have h1 : x * y = ((p : ℤ) : 𝓞 H.K) * m := by
    apply RingOfIntegers.ext
    simpa [hx, hy] using hm
  have h2 : x + y = t := by
    apply RingOfIntegers.ext
    simpa [hx, hy] using ht
  rcases mem_xor 𝔭.asIdeal 𝔭.isPrime p t m (by exact_mod_cast h𝔭) x y h1 h2 hc with h | h
  · exact ⟨𝔭, x, y, h𝔭, h.1, h.2, rfl⟩
  · exact ⟨𝔭, y, x, h𝔭, h.1, h.2, by rw [hx, hy, HostK.conjK_conjK]⟩

end GlobalTheory.Mem.Col2.SplitPrime
end

section

noncomputable section

namespace GlobalTheory.LevelHecke

open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}

theorem pm_mulsF_of_mem (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (h : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (hh : h ∈ S.Uloc v) : MulsF S v hv 1 h := by
  rw [S.UlocAlt v hv] at hh
  obtain ⟨hg, h2⟩ := (Subgroup.mem_inf.1 hh).2
  exact ⟨hg, fun x => by rw [one_smul]; exact h2 x⟩

theorem pm_mulsF_mul (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {a b : ℤ} {g h : GL (Fin n) (E ⊗[F] v.adicCompletion F)} (hg : MulsF S v hv a g) (hh : MulsF S v hv b h) :
    MulsF S v hv (b * a) (g * h) := by
  obtain ⟨ha, ha'⟩ := hg
  obtain ⟨hb, hb'⟩ := hh
  refine ⟨Subgroup.mul_mem _ ha hb, fun x => ?_⟩
  have h1 := ha' ⟨h.1 *ᵥ x.1, (hb x.1).1 x.2⟩
  have h2 := hb' x
  rw [← h2, ← h1, mul_smul]
  congr 3
  apply Subtype.ext
  simp [Matrix.mulVec_mulVec]

theorem pm_gen (S : StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    {k : Type} [Field k] {C : Type} (y : C → GA σ J)
    (hy : Function.Surjective (fun c => (Quotient.mk'' (y c) : Cls S)))
    (q : C → Pr (𝓞 E) (Fin n → E) k)
    (h1 : ∀ (c c' : C) (γ : GL (Fin n) E) (a : ℤ), MulsF S v hv a (bc (prV (E := E) v)
      ((y c).1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c').1)) →
      (q c').act (glE γ) = (q c).dil (a : k))
    (h2 : ∀ (c c' : C) (γ : GL (Fin n) E), γ ∈ UJ (σ : E →+* E) J → (q c').act (glE γ) = q c →
      bc (prV (E := E) v) ((y c).1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c').1) ∈ S.Uloc v) :
    ∃ p : GA σ J → Pr (𝓞 E) (Fin n → E) k, PMap S v hv p ∧ (∀ c, p (y c) = q c) ∧
      ∀ x, ∃ c γ, p x = (q c).act (glE γ) := by
  have hpres : ∀ x : GA σ J, ∃ (c : C) (γ : GL (Fin n) E) (κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      γ ∈ UJ (σ : E →+* E) J ∧ κ ∈ S.U ∧
      x.1 = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ := by
    intro x
    obtain ⟨c, hc⟩ := hy (Quotient.mk'' x)
    obtain ⟨hh', hhm, kk, hkm, heq⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hc
    obtain ⟨γ, hγ, hγe⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hhm)
    refine ⟨c, γ, kk.1, hγ, Subgroup.mem_subgroupOf.1 hkm, ?_⟩
    rw [heq, Subgroup.coe_mul, Subgroup.coe_mul, ← hγe]
  choose cc gg kk hgg hkk hx using hpres
  have hloc : ∀ κ ∈ S.U, bc (prV (E := E) v) κ ∈ S.Uloc v := fun κ hκ => ((S.U_eq κ).1 hκ).2 v
  have hmov : ∀ (c c' : C) (γ γ' : GL (Fin n) E) (κ κ' δ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ' * (y c').1 * κ' =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ * δ →
      bc (prV (E := E) v) ((y c).1⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) (γ⁻¹ * γ') * (y c').1) =
        bc (prV (E := E) v) κ * bc (prV (E := E) v) δ * (bc (prV (E := E) v) κ')⁻¹ := by
    intro c c' γ γ' κ κ' δ h
    rw [← map_inv, ← map_mul, ← map_mul, map_mul (bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F))), map_inv]
    congr 1
    have h' := eq_mul_inv_of_mul_eq h
    rw [mul_assoc, mul_assoc, h']
    group
  have hact : ∀ (c' : C) (γ γ' : GL (Fin n) E),
      ((q c').act (glE (γ⁻¹ * γ'))).act (glE γ) = (q c').act (glE γ') := by
    intro c' γ γ'
    rw [Pr.act_act, ← glE_mul, mul_inv_cancel_left]
  have key : ∀ (c c' : C) (γ γ' : GL (Fin n) E) (κ κ' δ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (a : ℤ),
      κ ∈ S.U → κ' ∈ S.U →
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ' * (y c').1 * κ' =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ * δ →
      MulsF S v hv a (bc (prV (E := E) v) δ) →
      (q c').act (glE γ') = ((q c).act (glE γ)).dil (a : k) := by
    intro c c' γ γ' κ κ' δ a hκ hκ' h hδ
    have hm := pm_mulsF_mul S v hv (pm_mulsF_mul S v hv (pm_mulsF_of_mem S v hv _ (hloc κ hκ)) hδ)
      (pm_mulsF_of_mem S v hv _ (inv_mem (hloc κ' hκ')))
    rw [one_mul, mul_one, ← hmov c c' γ γ' κ κ' δ h] at hm
    rw [← hact c' γ γ', h1 c c' _ a hm, Pr.act_dil]
  have key1 : ∀ (c c' : C) (γ γ' : GL (Fin n) E) (κ κ' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)),
      κ ∈ S.U → κ' ∈ S.U →
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ' * (y c').1 * κ' =
        bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y c).1 * κ →
      (q c').act (glE γ') = (q c).act (glE γ) := by
    intro c c' γ γ' κ κ' hκ hκ' h
    have := key c c' γ γ' κ κ' 1 1 hκ hκ' (by rw [h, mul_one])
      (pm_mulsF_of_mem S v hv _ (by rw [map_one]; exact one_mem _))
    rwa [Int.cast_one, Pr.dil_one] at this
  refine ⟨fun x => (q (cc x)).act (glE (gg x)), ⟨fun γ _ x x' h => ?_, fun x δ => ⟨fun h => ?_, fun h => ?_⟩,
    fun x δ a h => ?_⟩, fun c => ?_, fun x => ⟨_, _, rfl⟩⟩
  · show (q (cc x')).act _ = ((q (cc x)).act _).act _
    rw [Pr.act_act, ← glE_mul]
    refine key1 _ _ _ _ (kk x) (kk x') (hkk x) (hkk x') ?_
    rw [← hx x', h, map_mul]
    conv_lhs => rw [hx x]
    simp only [mul_assoc]
  · have h' : (q (cc (x * δ))).act (glE (gg (x * δ))) = (q (cc x)).act (glE (gg x)) := h
    rw [← hact _ (gg x)] at h'
    have h3 := h2 _ _ _ (mul_mem (inv_mem (hgg x)) (hgg (x * δ))) (Pr.act_injective _ h')
    rw [hmov _ _ _ _ (kk x) (kk (x * δ)) δ.1 (by rw [← hx x, ← hx (x * δ)]; rfl)] at h3
    have h4 := mul_mem (mul_mem (inv_mem (hloc _ (hkk x))) h3) (hloc _ (hkk (x * δ)))
    rwa [← mul_assoc, inv_mul_cancel_right, inv_mul_cancel_left] at h4
  · have := key _ _ _ _ (kk x) (kk (x * δ)) δ.1 1 (hkk x) (hkk (x * δ)) (by rw [← hx x, ← hx (x * δ)]; rfl)
      (pm_mulsF_of_mem S v hv _ h)
    rwa [Int.cast_one, Pr.dil_one] at this
  · exact key _ _ _ _ (kk x) (kk (x * δ)) δ.1 a (hkk x) (hkk (x * δ)) (by rw [← hx x, ← hx (x * δ)]; rfl) h.2.2
  · have := key1 c (cc (y c)) 1 (gg (y c)) 1 (kk (y c)) (one_mem _) (hkk _)
      (by rw [← hx (y c), map_one, one_mul, mul_one])
    rwa [glE_one, Pr.act_refl] at this

end Gen



theorem exists_pmap : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v), FvTie P K fMe → cT (sigD D : D.host.E →+* D.host.E) (gramN D i hi) = gramN D i hi → ∀ v : (D.mem u).A.vT, ∃ p : GA (sigD D) (gramN D i hi) → Pr (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) ((D.mem u).A.Fv v), PMap K.lev (A.eV v).1 (A.eV v).2 p ∧ (∀ c, p (K.y c) = pc P v c) ∧ ∀ x, (p x).Ok (A.res v) := by
  intro D u A i hi P K fMe hF hJ v
  obtain ⟨p, h1, h2, h3⟩ := pm_gen K.lev (A.eV v).1 (A.eV v).2 K.y K.y_bij.2 (pc P v)
    (GlobalTheory.T.classPair_moved_of_multipliesLocalFunctional D u A i hi P K fMe hF v) (GlobalTheory.T.rationalUnitary_pairToPair_component_mem_localLevel D u A i hi P K fMe hF hJ v)
  refine ⟨p, h1, h2, fun x => ?_⟩
  obtain ⟨c, γ, h⟩ := h3 x
  rw [h]
  exact (pc_ok P v c).act _

end GlobalTheory.LevelHecke

end
end
