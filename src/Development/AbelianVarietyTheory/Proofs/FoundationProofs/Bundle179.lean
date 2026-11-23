module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle131
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle132
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle170
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle114
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle144
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle122
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle092
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle104
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle171
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle167
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsUnitarisableOfCharIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle169
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
public import Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform

@[expose] public section

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

def germCompMob (g : GQ) : Mero →+* Mero where
  toFun F := F.compTendsto (mob g) (GlobalTheory.T.tendsto_mob_codiscreteWithin_codiscreteWithin g)
  map_one' := rfl
  map_mul' F G := by
    induction F using Filter.Germ.inductionOn
    induction G using Filter.Germ.inductionOn
    rfl
  map_zero' := rfl
  map_add' F G := by
    induction F using Filter.Germ.inductionOn
    induction G using Filter.Germ.inductionOn
    rfl

theorem germCompMob_coe (g : GQ) (φ : ℂ → ℂ) :
    germCompMob g (φ : Mero) = ((fun z => φ (mob g z)) : Mero) := rfl

theorem an_sl_germ : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (g : GQ) (f : T.K) (φ : ℂ → ℂ), T.an f = (φ : Mero) → T.an (T.sl g f) = ((fun z => φ (mob g z)) : Mero) := by
  intro Ω _ _ _ ε T g f φ hf
  have key : T.an.comp ((T.sl g : T.K ≃ₐ[Ω] T.K) : T.K →+* T.K) = (germCompMob g).comp T.an := by
    apply (GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).1 Mero
    intro a
    obtain ⟨a', ha', hs⟩ := (GlobalTheory.T.fractionField_ext_closure_injective Ω ε T).2.1 g a
    simp only [RingHom.comp_apply]
    rw [show ((T.sl g : T.K ≃ₐ[Ω] T.K) : T.K →+* T.K) (T.io a) = T.sl g (T.io a) from rfl, hs, T.an_io, T.an_io]
    unfold germ
    rw [germCompMob_coe]
    apply (GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict).2.2.1
    intro z hz
    rw [ha']
    exact (GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob).2.2.2 g a z hz
  have h2 := RingHom.congr_fun key f
  simp only [RingHom.comp_apply] at h2
  rw [show ((T.sl g : T.K ≃ₐ[Ω] T.K) : T.K →+* T.K) f = T.sl g f from rfl] at h2
  rw [h2, hf, germCompMob_coe]

end GlobalTheory.FN
end
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN.Sat

theorem mdiff_comp_sl (f : ℍ → ℂ) (hf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) (γ : SL(2, ℤ)) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ : ℍ => f (γ • τ)) := by
  have hg : 0 < ((γ : GL (Fin 2) ℝ)).det.val := by simp
  exact hf.comp (UpperHalfPlane.mdifferentiable_smul hg)

theorem gamma_le {K L : ℕ} (hd : K ∣ L) : CongruenceSubgroup.Gamma L ≤ CongruenceSubgroup.Gamma K := by
  intro γ hγ
  have c : ∀ x y : ℤ, ((x : ZMod L) = y) → ((x : ZMod K) = y) := fun x y h => by
    have := congrArg (ZMod.castHom hd (ZMod K)) h
    simpa using this
  rw [CongruenceSubgroup.Gamma_mem] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using c _ 1 (by simpa using h1)
  · simpa using c _ 0 (by simpa using h2)
  · simpa using c _ 0 (by simpa using h3)
  · simpa using c _ 1 (by simpa using h4)

theorem alg (m : ℕ) (P : ℕ → ℂ) (x y : ℂ)
    (h : ∑ i ∈ Finset.range (m + 1 + 1), P i * x ^ i * y ^ (m + 1 - i) = 0) :
    (P (m + 1) * x) ^ (m + 1) +
      ∑ j : Fin (m + 1), (P j * P (m + 1) ^ (m - j)) * (P (m + 1) * x) ^ (j : ℕ) * y ^ (m + 1 - j) = 0 := by
  rw [Finset.sum_range_succ, ← Fin.sum_univ_eq_sum_range] at h
  have key : ∀ j : Fin (m + 1), (P j * P (m + 1) ^ (m - j)) * (P (m + 1) * x) ^ (j : ℕ) * y ^ (m + 1 - j) =
      P (m + 1) ^ m * (P j * x ^ (j : ℕ) * y ^ (m + 1 - j)) := by
    intro j
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.mp j.isLt)
    have e1 : m - j = k := by omega
    have e2 : P (m + 1) ^ m = P (m + 1) ^ k * P (m + 1) ^ (j : ℕ) := by rw [← pow_add]; congr 1; omega
    rw [e1, e2, mul_pow]; ring
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]
  have : (P (m + 1) * x) ^ (m + 1) = P (m + 1) ^ m * (P (m + 1) * x ^ (m + 1) * y ^ (m + 1 - (m + 1))) := by
    simp only [Nat.sub_self, pow_zero, mul_one]; ring
  rw [this]
  linear_combination (P (m + 1) ^ m) * h

theorem sat : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (M n : ℕ) (a b : ℍ → ℂ) (p : ℕ → ℍ → ℂ), 0 < M → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) b → b ≠ 0 → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, a (γ • τ) * b τ = a τ * b (γ • τ)) → (∀ i, InR ε.range (p i)) → p n ≠ 0 → (∀ τ, ∑ i ∈ Finset.range (n + 1), p i τ * a τ ^ i * b τ ^ (n - i) = 0) → ∃ h : ℍ → ℂ, InR ε.range h ∧ ∀ τ, p n τ * a τ = h τ * b τ := by
  intro Ω _ _ ε M n a b p hM ha hb hb0 hab hp hpn heq
  obtain ⟨-, hiff, -, -, hmem⟩ := GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict
  have hring := GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range
  have inR_mul : ∀ f g : ℍ → ℂ, InR ε.range f → InR ε.range g → InR ε.range (f * g) := fun f g hf hg =>
    (hring.1 _).1 (Subring.mul_mem _ ((hring.1 _).2 hf) ((hring.1 _).2 hg))
  have inR_pow : ∀ (f : ℍ → ℂ) (k : ℕ), InR ε.range f → InR ε.range (f ^ k) := fun f k hf =>
    (hring.1 _).1 (Subring.pow_mem _ ((hring.1 _).2 hf) k)
  have hol : ∀ i, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (p i) := fun i => GlobalTheory.T.mdifferentiable_of_hasSomeLevelOver _ _ (hp i)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · exfalso; apply hpn; funext τ; have := heq τ; simpa using this
    · exact ⟨m, rfl⟩
  have hHs : IsOpen Hs := by
    show IsOpen {z : ℂ | 0 < z.im}; exact isOpen_lt continuous_const Complex.continuous_im
  have hHc : IsPreconnected Hs := by
    apply Convex.isPreconnected
    show Convex ℝ {z : ℂ | 0 < z.im}
    intro x hx y hy s t hs ht hst
    simp only [Set.mem_setOf_eq, Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero] at hx hy ⊢
    rcases hs.eq_or_lt with rfl | hs'
    · simp at hst; subst hst; simpa using hy
    · nlinarith [mul_pos hs' hx, mul_nonneg ht hy.le]
  have dOn : ∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → DifferentiableOn ℂ (up f) Hs := fun f hf => (hiff f).1 hf
  have upc : ∀ (f : ℍ → ℂ) (τ : ℍ), up f (τ : ℂ) = f τ := fun f τ => by
    simp only [up, UpperHalfPlane.ofComplex_apply]
  obtain ⟨τ0, hτ0⟩ : ∃ τ, b τ ≠ 0 := by
    by_contra hc; push_neg at hc; exact hb0 (funext hc)
  obtain ⟨h', hh'd, hAD, hmon⟩ := GlobalTheory.T.exists_differentiableOn_quotient_of_integral Hs (m + 1) (fun z => up (p (m + 1)) z * up a z) (up b)
    (fun j z => up (p j) z * up (p (m + 1)) z ^ (m - j)) hHs hHc
    ((dOn _ (hol _)).mul (dOn _ ha)) (dOn _ hb) (fun j => (dOn _ (hol _)).mul ((dOn _ (hol _)).pow _))
    ⟨τ0, hmem τ0, by rw [upc]; exact hτ0⟩
    (fun z _ => alg m (fun i => p i (UpperHalfPlane.ofComplex z)) (a (UpperHalfPlane.ofComplex z))
      (b (UpperHalfPlane.ofComplex z)) (heq _))
  set h : ℍ → ℂ := fun τ => h' τ with hh
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
    rw [hiff]
    refine hh'd.congr fun z hz => ?_
    show h' (UpperHalfPlane.ofComplex z : ℂ) = h' z
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hPA : ∀ τ, p (m + 1) τ * a τ = h τ * b τ := fun τ => by
    have := hAD τ (hmem τ); simpa only [upc] using this
  obtain ⟨N, w, hN, hLv, -⟩ := hp (m + 1)
  have hinv : ∀ γ ∈ CongruenceSubgroup.Gamma (M * N), ∀ τ : ℍ, h (γ • τ) = h τ := by
    intro γ hγ
    have hγM := gamma_le (Dvd.intro N rfl) hγ
    have hγN := gamma_le (Dvd.intro_left M rfl) hγ
    have hprod : ∀ τ, (fun τ => h (γ • τ) - h τ) τ * (fun τ => b τ * b (γ • τ)) τ = 0 := by
      intro τ
      have E1 := hPA (γ • τ)
      have E2 := hPA τ
      have E3 := hLv γ hγN τ
      have E4 := hab γ hγM τ
      simp only
      linear_combination (-(b τ)) * E1 + b (γ • τ) * E2 + (a (γ • τ) * b τ) * E3 + p (m + 1) τ * E4
    rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff _ _ ((mdiff_comp_sl h hhol γ).sub hhol) (hb.mul (mdiff_comp_sl b hb γ)) hprod with h0 | h0
    · intro τ; have := congrFun h0 τ; simpa [sub_eq_zero] using this
    · exfalso
      have hbb : ∀ τ, b τ * (fun τ => b (γ • τ)) τ = 0 := fun τ => congrFun h0 τ
      rcases GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff _ _ hb (mdiff_comp_sl b hb γ) hbb with h1 | h1
      · exact hb0 h1
      · apply hτ0
        have := congrFun h1 (γ⁻¹ • τ0)
        simpa using this
  refine ⟨h, ?_, hPA⟩
  refine GlobalTheory.T.hasSomeLevelOver_of_integral_invariant Ω ε (M * N) (m + 1) h (fun j τ => p j τ * p (m + 1) τ ^ (m - j)) (Nat.mul_pos hM hN)
    hhol hinv (fun j => inR_mul _ _ (hp _) (inR_pow _ _ (hp _))) ?_
  intro τ
  have := hmon τ (hmem τ)
  simpa only [upc] using this

end GlobalTheory.FN.Sat
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem j_in_frac : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), ∃ a : GlobalTheory.FN.ring ε.range, (a : ℍ → ℂ) = jT ∧ (∀ γ : SL(2, ℤ), T.sl (ofSL γ) (T.io a) = T.io a) ∧ (T.exp (T.io a)).coeff (-1) = 1 ∧ (∀ r : ℚ, r < -1 → (T.exp (T.io a)).coeff r = 0) ∧ ∀ r : ℚ, ∃ n : ℤ, (T.exp (T.io a)).coeff r = n := by
  intro Ω _ _ _ ε T
  have hlv := (GlobalTheory.T.lv_jT_one_and_jT_smul_eq ε.range).1
  let a : GlobalTheory.FN.ring ε.range := ⟨jT, mem_ring_of_inR ⟨1, 1, one_pos, hlv⟩⟩
  have ha : (a : ℍ → ℂ) = jT := rfl
  obtain ⟨h, hexp, h1, h2, h3⟩ := GlobalTheory.T.exists_integral_cuspExpansion_jInvariant Ω ε
  have heq : T.exp (T.io a) = h :=
    (GlobalTheory.T.isCuspExpansionAtInfinity_properties Ω ε).2.1 jT _ _ (T.exp_io a) hexp
  refine ⟨a, ha, fun γ => ?_, ?_, ?_, ?_⟩
  · apply T.sl_io
    rw [ha, (GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob).2.2.1 γ jT]
    funext τ
    exact ((GlobalTheory.T.lv_jT_one_and_jT_smul_eq ε.range).2 γ τ).symm
  · rw [heq]; exact h1
  · rw [heq]; exact h2
  · rw [heq]; exact h3

end GlobalTheory.FN
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_sl_right_action : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ f, T.sl 1 f = f) ∧ ∀ g h f, T.sl (g * h) f = T.sl h (T.sl g f) := by
  intro Ω _ _ _ ε T
  obtain ⟨hext, hcl, -, -⟩ := GlobalTheory.T.fractionField_ext_closure_injective Ω ε T
  obtain ⟨c1, cmul, -, -⟩ := GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob
  refine ⟨fun f => ?_, fun g h f => ?_⟩
  · have e : (T.sl 1 : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom = RingHom.id T.K := by
      apply hext
      intro a
      exact T.sl_io 1 a a (c1 a).symm
    exact congrArg (fun φ : T.K →+* T.K => φ f) e
  · have e : (T.sl (g * h) : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom =
        ((T.sl h : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom).comp ((T.sl g : T.K ≃ₐ[Ω] T.K).toRingEquiv.toRingHom) := by
      apply hext
      intro a
      obtain ⟨a', ha', hga⟩ := hcl g a
      obtain ⟨a'', ha'', hha⟩ := hcl h a'
      have : (a'' : ℍ → ℂ) = cmp (g * h) a := by rw [ha'', ha', cmul]
      simp only [RingHom.comp_apply]
      show T.sl (g * h) (T.io a) = T.sl h (T.sl g (T.io a))
      rw [T.sl_io (g * h) a a'' this, hga, hha]
    exact congrArg (fun φ : T.K →+* T.K => φ f) e

end GlobalTheory.FN
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem norm_trm_le (j : ℕ) (s : ℝ) (hj : j ≠ 0) (z : ℂ) : ‖trm j s z‖ ≤ ‖z‖ ^ (-((j : ℝ) + 2 * s)) := by
  by_cases hz : z = 0
  · subst hz
    simp only [trm, zero_pow hj, inv_zero, zero_mul, norm_zero]
    exact Real.rpow_nonneg le_rfl _
  · have h0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    unfold trm
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg h0.le _),
      show -((j : ℝ) + 2 * s) = -(j : ℝ) + -2 * s by ring, Real.rpow_add h0, Real.rpow_neg h0.le,
      Real.rpow_natCast]

theorem lat_eq_tsum_of_kills : ∀ (j L : ℕ) (s : ℝ) (v : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ), 2 ≤ j → 0 < s → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Kills L v Φ → (Summable fun x : ℤ × ℤ => ‖trm j s ((x.1 : ℂ) * τ + x.2)‖) ∧ lat j s L v Φ τ = ∑' x : ℤ × ℤ, Φ x * trm j s ((x.1 : ℂ) * τ + x.2) := by
  intro j L s v Φ τ hj hs hL hΦ hK
  have hk : (2 : ℝ) < j + 2 * s := by
    have : (2 : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  have hG : Summable fun x : ℤ × ℤ => ‖trm j s ((x.1 : ℂ) * τ + x.2)‖ := by
    have h1 := (EisensteinSeries.summable_one_div_norm_rpow hk).mul_left
      ((EisensteinSeries.r τ) ^ (-((j : ℝ) + 2 * s)))
    have h2 : Summable (fun x : Fin 2 → ℤ => ‖trm j s ((x 0 : ℂ) * τ + x 1)‖) :=
      Summable.of_nonneg_of_le (fun x => norm_nonneg _)
        (fun x => (norm_trm_le j s (by omega) _).trans (EisensteinSeries.summand_bound τ (by linarith) x)) h1
    have h3 := ((finTwoArrowEquiv ℤ).symm.summable_iff).mpr h2
    exact h3.congr fun p => by simp
  obtain ⟨h1s, h1e⟩ := GlobalTheory.T.killsTranslates_sum_mul_meanDifference_eq L v Φ _ hL hΦ hK hG
  obtain ⟨_, h2e⟩ := GlobalTheory.T.killsTranslates_sum_mul_meanDifference_eq L v Φ _ hL hΦ hK h1s
  refine ⟨hG, ?_⟩
  unfold lat
  rw [h2e, h1e]

end GlobalTheory.EisM
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.RepInd

theorem exists_inj (L : ℕ) (Δ : Set M2) {ι κ : Type} (β : ι → M2) (β' : κ → M2)
    (hβ : LRep L Δ β) (hβ' : LRep L Δ β') :
    ∃ σ : κ → ι, Function.Injective σ ∧ ∃ g : κ → Gamma0 L,
      ∀ j, β' j = (((g j : SL(2, ℤ)) : M2)) * β (σ j) := by
  have hmem : ∀ j, ∃ p : Gamma0 L × ι, ((p.1 : SL(2, ℤ)) : M2) * β p.2 = β' j := by
    intro j
    have h1 : β' j ∈ Δ := by
      have := hβ'.mapsTo (Set.mem_univ ((1 : Gamma0 L), j))
      simpa using this
    obtain ⟨p, -, hp⟩ := hβ.surjOn h1
    exact ⟨p, hp⟩
  choose p hp using hmem
  refine ⟨fun j => (p j).2, ?_, fun j => (p j).1, fun j => (hp j).symm⟩
  intro j j' hjj
  have key : (((((p j).1 * ((p j').1)⁻¹ : Gamma0 L) : SL(2, ℤ)) : M2)) * β' j'
      = (((1 : Gamma0 L) : SL(2, ℤ)) : M2) * β' j := by
    rw [← hp j', ← hp j]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_mul,
      Subgroup.coe_one, Matrix.SpecialLinearGroup.coe_one, one_mul]
    simp only at hjj
    rw [hjj, ← mul_assoc, mul_assoc (((p j).1 : SL(2, ℤ)) : M2)]
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, mul_one]
  have := hβ'.injOn (Set.mem_univ (((p j).1 * ((p j').1)⁻¹), j')) (Set.mem_univ ((1 : Gamma0 L), j)) key
  exact (congrArg Prod.snd this).symm

end GlobalTheory.EisM.RepInd

namespace GlobalTheory.EisM.RepInd

theorem term_eq (k L N : ℕ) (ε : DirichletCharacter ℂ N) (β : M2) (γ : Gamma0 L) (f : ℍ → ℂ)
    (hk : 1 ≤ k) (hNL : N ∣ L) (hdet : 0 < β.det) (hN : (N : ℤ) ∣ β 1 0) (hf : Inv k L (ch ε) f) (τ : ℍ) :
    ch ε (((((γ : SL(2, ℤ)) : M2)) * β) 0 0) * slz k ((((γ : SL(2, ℤ)) : M2)) * β) f τ
      = ch ε (β 0 0) * slz k β f τ := by
  obtain ⟨hc, -, hinv, -, -⟩ := GlobalTheory.T.slashIntMatrixPosDet_properties k f hk
  set g : SL(2, ℤ) := (γ : SL(2, ℤ)) with hg
  have hgL : (L : ℤ) ∣ g 1 0 := by
    have := (Gamma0_mem).1 γ.2
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  have hgN : (N : ℤ) ∣ g 1 0 := dvd_trans (Int.natCast_dvd_natCast.2 hNL) hgL
  have hgdet : 0 < (g : M2).det := by simp
  rw [hc _ _ hgdet hdet, (hinv L (ch ε)).1 hf g hgL]
  have hlin : slz k β (fun τ => ch ε (g 1 1) * f τ) τ = ch ε (g 1 1) * slz k β f τ := by
    simp only [slz]; ring
  rw [hlin]
  have hdetg : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.2
    rw [Matrix.det_fin_two] at this
    exact this
  have h00 : ((((g : M2)) * β) 0 0 : ZMod N) = (g 0 0 : ZMod N) * (β 0 0 : ZMod N) := by
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    have : ((β 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hN
    push_cast
    rw [this]; simp
  have h1 : (g 0 0 : ZMod N) * (g 1 1 : ZMod N) = 1 := by
    have : ((g 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hgN
    have h2 : ((g 0 0 * g 1 1 - g 0 1 * g 1 0 : ℤ) : ZMod N) = 1 := by rw [hdetg]; simp
    push_cast at h2
    rw [this, mul_zero, sub_zero] at h2
    exact h2
  simp only [ch]
  rw [h00, map_mul]
  have : ε (g 0 0 : ZMod N) * ε (g 1 1 : ZMod N) = 1 := by rw [← map_mul, h1, map_one]
  calc ε (g 0 0 : ZMod N) * ε (β 0 0 : ZMod N) * (ε (g 1 1 : ZMod N) * slz k β f τ)
      = (ε (g 0 0 : ZMod N) * ε (g 1 1 : ZMod N)) * (ε (β 0 0 : ZMod N) * slz k β f τ) := by ring
    _ = ε (β 0 0 : ZMod N) * slz k β f τ := by rw [this, one_mul]

theorem hsum_indep : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (Δ : Set M2) (ι κ : Type) [Fintype ι] [Fintype κ] (β : ι → M2) (β' : κ → M2) (f : ℍ → ℂ), 1 ≤ k → N ∣ L → (∀ δ ∈ Δ, 0 < δ.det ∧ (N : ℤ) ∣ δ 1 0) → LRep L Δ β → LRep L Δ β' → Inv k L (ch ε) f → hsum k (ch ε) β f = hsum k (ch ε) β' f := by
  intro k L N ε Δ ι κ _ _ β β' f hk hNL hΔ hβ hβ' hf
  obtain ⟨σ, hσ, g, hg⟩ := exists_inj L Δ β β' hβ hβ'
  obtain ⟨σ', hσ', -, -⟩ := exists_inj L Δ β' β hβ' hβ
  have hcard : Fintype.card κ = Fintype.card ι :=
    le_antisymm (Fintype.card_le_of_injective σ hσ) (Fintype.card_le_of_injective σ' hσ')
  have hbij : Function.Bijective σ := (Fintype.bijective_iff_injective_and_card σ).2 ⟨hσ, hcard⟩
  have hin : ∀ i, β i ∈ Δ := fun i => by
    have := hβ.mapsTo (Set.mem_univ ((1 : Gamma0 L), i))
    simpa using this
  funext τ
  simp only [hsum]
  symm
  refine Fintype.sum_bijective σ hbij _ _ ?_
  intro j
  rw [hg j]
  exact term_eq k L N ε (β (σ j)) (g j) f hk hNL (hΔ _ (hin _)).1 (hΔ _ (hin _)).2 hf τ

end GlobalTheory.EisM.RepInd
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.atkinLehner_slash_inverse_character : ∀ (k N l : ℕ) (χ : DirichletCharacter ℂ N) (f : ℍ → ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ k → 0 < N → Inv k (N * l) (ch χ) f → Inv k (N * l) (ch χ⁻¹) (slz k !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] f) := by
  first | exact @GlobalTheory.EisM.inv_slz_atkinLehner | exact GlobalTheory.EisM.inv_slz_atkinLehner | (intros; apply GlobalTheory.EisM.inv_slz_atkinLehner <;> assumption)
end

section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

theorem _root_.GlobalTheory.T.strips_exhaust_parabolicUnipotentRadical : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ) (ϖ : k), (∀ i, IsSmoothChar (ψ i)) → ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → ∀ y ∈ unipRad k (two (stdSum (rfl : r + t = r + t))), ∃ m, y ∈ strip ψ r ϖ m := by
  first | exact @GlobalTheory.PsType.strip_exhaust | exact GlobalTheory.PsType.strip_exhaust | (intros; apply GlobalTheory.PsType.strip_exhaust <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.modularFormCoeffSeq_eq_of_pos_coeff_eq : ∀ (k L : ℕ) (χ : ℤ → ℂ) (a b : ℕ → ℂ), 1 ≤ k → 0 < L → MF k L χ a → MF k L χ b → (∀ n, n ≠ 0 → a n = b n) → a = b := by
  first | exact @GlobalTheory.EisM.eq_of_coeff_pos_eq | exact GlobalTheory.EisM.eq_of_coeff_pos_eq | (intros; apply GlobalTheory.EisM.eq_of_coeff_pos_eq <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.exists_bound_norm_qs_of_one_le_im : ∀ (b : ℕ → ℂ), PolyB b → ∃ M : ℝ, ∀ τ : ℍ, 1 ≤ τ.im → ‖qs b τ‖ ≤ M := by
  first | exact @GlobalTheory.EisM.qs_bdd_above_one | exact GlobalTheory.EisM.qs_bdd_above_one | (intros; apply GlobalTheory.EisM.qs_bdd_above_one <;> assumption)
end

section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

theorem _root_.GlobalTheory.T.exists_towerUnion_zetaDerivation_modIntegralClosure : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : Tower p Ω), ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω, IsDerOn (towerAlg T) D ∧ ∀ m : ℕ, D (zS T m) = Submodule.Quotient.mk (T.ζ m * p / (p : Ω) ^ m) ∧ D (qS T m) = 0 := by
  first | exact @GlobalTheory.AlmostEt.zeta_derivation | exact GlobalTheory.AlmostEt.zeta_derivation | (intros; apply GlobalTheory.AlmostEt.zeta_derivation <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM Filter Topology
open scoped MatrixGroups Real ComplexConjugate

theorem _root_.GlobalTheory.T.dirichletFourier_mixed_twist_multiple : ∀ (N l : ℕ) (ν : DirichletCharacter ℂ N) (ω : DirichletCharacter ℂ l) (φ : ZMod l → ℂ) (a c : ℤ),
    0 < N → 0 < l → N.Coprime l → (∀ x : ℤ, hat φ x = ch ω x) →
    (∀ d u : ZMod l, IsUnit d → φ u = ω d * φ (d * u)) → IsUnit (c : ZMod N) → IsUnit (a : ZMod l) →
    (∃ C : ℂ, C ≠ 0 ∧ ∀ x : ℤ, hat (fun z : ZMod (N * l) => ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) z) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) z)) x = C * (ch ω x * hat ν x)) ∧
    ∀ d : ℤ, IsCoprime d (N * l : ℕ) → ∀ y : ZMod (N * l),
      ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) y) * φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) y) =
      ch ω d * ch ν⁻¹ d * (ν (-(c : ZMod N) * ZMod.castHom (Dvd.intro l rfl) (ZMod N) (y * d)) *
        φ ((a : ZMod l) * ZMod.castHom (Dvd.intro_left N rfl) (ZMod l) (y * d))) := by
  first | exact @GlobalTheory.EisM.hat_mix_twist | exact GlobalTheory.EisM.hat_mix_twist | (intros; apply GlobalTheory.EisM.hat_mix_twist <;> assumption)
end
