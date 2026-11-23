module

import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.ComplexMultiplication.ExtEmbEquivComp
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle003
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle253
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle256
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle189
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle105
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCocycleTwistedCoboundary
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle002
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle263
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle110
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MuModelProductValueNeZeroOfDepleted
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Mathlib.NumberTheory.ModularForms.Basic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUlSemisimpleOnLOldSpace
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle262
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle106
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle079
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle083
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle005
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
public import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Algebraic.Cardinality
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Newform
import Std.Tactic.BVDecide.Normalize.Prop
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle003

@[expose] public section

section

noncomputable section

open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg GlobalTheory.QFam Cardinal

namespace GlobalTheory.KZ.GalUnits

theorem exists_equiv_comp {R K L : Type} [Field R] [Field K] [Field L] [IsAlgClosed K]
    [IsAlgClosed L] (f : R →+* K) (g : R →+* L) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K) (hKL : #K = #L) :
    ∃ σ : K ≃+* L, ∀ r : R, σ (f r) = g r := by
  apply Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.extEmb_equiv_comp <;> assumption

theorem exists_ext {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (s : Ω ≃ₐ[ℚ] Ω) :
    ∃ σ : ℂ ≃+* ℂ, ∀ x : Ω, σ (ε x) = ε (s x) := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hR : #Ω ≤ ℵ₀ :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ Ω).trans (max_le Cardinal.mk_le_aleph0 le_rfl)
  exact exists_equiv_comp ε (ε.comp (s : Ω →+* Ω)) hR
    (by simp [Cardinal.mk_complex, Cardinal.aleph0_lt_continuum]) rfl

theorem mem_range_of_pow_eq_one {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (ε : Ω →+* ℂ) {n : ℕ}
    (hn : 0 < n) {w : ℂ} (hw : w ^ n = 1) : ∃ y, ε y = w := by
  have : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic n Ω)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos n Ω hn))
  have hz' : IsPrimitiveRoot z n := Polynomial.isRoot_cyclotomic_iff.1 hz
  have he : IsPrimitiveRoot (ε z) n := hz'.map_of_injective ε.injective
  obtain ⟨i, -, hi⟩ := he.eq_pow_of_pow_eq_one hw
  exact ⟨z ^ i, by rw [map_pow, hi]⟩

theorem eps_eOm {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ε (eOm ε x) = ee (x : ℂ) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hw : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = x.num * (2 * Real.pi * Complex.I) := by
      have hd : (x.den : ℂ) ≠ 0 := by exact_mod_cast x.den_ne_zero
      have : (x : ℂ) = (x.num : ℂ) / x.den := by exact_mod_cast (Rat.num_div_den x).symm
      rw [this]; field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have hex := mem_range_of_pow_eq_one ε x.den_pos hw
  unfold eOm ee
  exact Function.invFun_eq hex


open Classical in
def lc {R : Type} [Zero R] (M : ℕ) (k : ℤ) (A : ℕ → R) (r : ℚ) : R :=
  if h : ∃ n : ℕ, r = ((k : ℚ) + n) / M then A h.choose else 0

theorem lc_eq {R : Type} [Zero R] {M : ℕ} (hM : 0 < M) (k : ℤ) (A : ℕ → R) (n : ℕ) :
    lc M k A (((k : ℚ) + n) / M) = A n := by
  have h : ∃ m : ℕ, ((k : ℚ) + n) / M = ((k : ℚ) + m) / M := ⟨n, rfl⟩
  unfold lc
  rw [dite_eq_left h]
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have := h.choose_spec
  rw [div_left_inj' hM', add_right_inj] at this
  have : h.choose = n := by exact_mod_cast this.symm
  rw [this]

theorem lc_zero {R : Type} [Zero R] {M : ℕ} {k : ℤ} (A : ℕ → R) {r : ℚ} (h : ∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) :
    lc M k A r = 0 := by
  unfold lc
  rw [dite_eq_right]
  push_neg
  exact h

theorem lc_map {R S : Type} [Zero R] [Zero S] (M : ℕ) (k : ℤ) (A : ℕ → R) (g : R → S) (hg : g 0 = 0) (r : ℚ) :
    lc M k (fun n => g (A n)) r = g (lc M k A r) := by
  unfold lc
  split_ifs <;> simp [hg]

theorem eq_lc {R : Type} [Zero R] {M : ℕ} (hM : 0 < M) {k : ℤ} {A : ℕ → R} {F : ℚ → R}
    (h1 : ∀ n : ℕ, F (((k : ℚ) + n) / M) = A n) (h2 : ∀ r : ℚ, (∀ n : ℕ, r ≠ ((k : ℚ) + n) / M) → F r = 0) :
    ∀ r, F r = lc M k A r := by
  intro r
  by_cases h : ∃ n : ℕ, r = ((k : ℚ) + n) / M
  · obtain ⟨n, rfl⟩ := h
    rw [h1, lc_eq hM]
  · push_neg at h
    rw [h2 r h, lc_zero A h]

theorem lc_unique {M : ℕ} (hM : 0 < M) {f : ℍ → ℂ} {k k' : ℤ} {A A' : ℕ → ℂ}
    (h : HasQ M (fun τ => f τ * ee (-((k : ℂ) / M) * (τ : ℂ))) A)
    (h' : HasQ M (fun τ => f τ * ee (-((k' : ℂ) / M) * (τ : ℂ))) A') : lc M k A = lc M k' A' := by
  wlog hk : k ≤ k' generalizing k k' A A'
  · exact (this h' h (le_of_not_ge hk)).symm
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k' = k + m := ⟨(k' - k).toNat, by omega⟩
  have hs : HasQ M (fun τ => f τ * ee (-((k : ℂ) / M) * (τ : ℂ))) (fun n => if m ≤ n then A' (n - m) else 0) := by
    rw [hasQ_iff] at h' ⊢
    intro τ
    set Q := Complex.exp (2 * Real.pi * Complex.I * τ / M) with hQ
    have h2 := (h' τ).mul_right (Q ^ m)
    have e : f τ * ee (-(((k + m : ℤ) : ℂ) / M) * (τ : ℂ)) * Q ^ m = f τ * ee (-((k : ℂ) / M) * (τ : ℂ)) := by
      rw [mul_assoc]; congr 1
      unfold ee
      rw [hQ, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [e] at h2
    refine (Function.Injective.hasSum_iff (f := fun n => (if m ≤ n then A' (n - m) else 0) * Q ^ n)
      (add_left_injective m) ?_).mp ?_
    · intro x hx
      have : ¬ m ≤ x := by
        intro hmx; exact hx ⟨x - m, by simp only; omega⟩
      simp [this]
    · rw [← hQ] at h2
      have e2 : (fun n => (if m ≤ n then A' (n - m) else 0) * Q ^ n) ∘ (· + m) = fun i => A' i * Q ^ i * Q ^ m := by
        funext n
        simp only [Function.comp, le_add_iff_nonneg_left, zero_le, if_true, Nat.add_sub_cancel, pow_add]
        ring
      rw [e2]; exact h2
  have hA := HasQ.coeff_unique hM h hs
  subst hA
  have hM' : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  funext r
  by_cases hr : ∃ n : ℕ, r = ((k : ℚ) + n) / M
  · obtain ⟨n, rfl⟩ := hr
    rw [lc_eq hM]
    by_cases hmn : m ≤ n
    · rw [if_pos hmn]
      have : ((k : ℚ) + n) / M = (((k + m : ℤ) : ℚ) + ((n - m : ℕ) : ℚ)) / M := by
        push_cast [Nat.cast_sub hmn]; ring
      rw [this, lc_eq hM]
    · rw [if_neg hmn, lc_zero]
      intro n' hn'
      rw [div_left_inj' hM'] at hn'
      push_cast at hn'
      have : (n : ℚ) = m + n' := by linarith
      have : n = m + n' := by exact_mod_cast this
      omega
  · push_neg at hr
    rw [lc_zero _ hr, lc_zero]
    intro n' hn'
    apply hr (m + n')
    rw [hn']; push_cast; ring

end GlobalTheory.KZ.GalUnits

namespace GlobalTheory.KZ

open GalUnits

theorem gal_siegel : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ) (M a b d : ℕ) (s : Ω ≃ₐ[ℚ] Ω), 0 < M → a < M → s (eOm ε (1 / M)) = eOm ε (d / M) → GlobalTheory.Sieg.admitted c ![(a : ℚ) / M, (b : ℚ) / M] → GlobalTheory.Sieg.admitted c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] → T.gal s (siegel T c ![(a : ℚ) / M, (b : ℚ) / M]) = siegel T c ![(a : ℚ) / M, ((d * b : ℕ) : ℚ) / M] := by
  intro Ω _ _ _ ε T c M a b d s hM ha hs h1 h2
  obtain ⟨σ, hσ⟩ := exists_ext ε s
  have hσM : σ (ee (1 / (M : ℂ))) = ee ((d : ℂ) / M) := by
    have e1 := eps_eOm ε (1 / M)
    have e2 := eps_eOm ε (d / M)
    push_cast at e1 e2
    rw [← e1, hσ, hs, e2]
  obtain ⟨k0, B, hB, hB'⟩ := GlobalTheory.T.smoothedSiegelUnit_coeff_galois_level c M a b d σ hM ha hσM h1 h2
  obtain ⟨k1, A1, hA1, c1, z1⟩ := GlobalTheory.T.siegel_unit_q_expansion_coefficients Ω ε T c M a b hM ha h1
  obtain ⟨k2, A2, hA2, c2, z2⟩ := GlobalTheory.T.siegel_unit_q_expansion_coefficients Ω ε T c M a (d * b) hM ha h2
  have L1 := eq_lc hM c1 z1
  have L2 := eq_lc hM c2 z2
  have U1 := lc_unique hM hA1 hB
  have U2 := lc_unique hM hB' hA2
  apply T.exp.toRingHom.injective
  ext r
  apply ε.injective
  show ε ((T.exp (T.gal s _)).coeff r) = ε ((T.exp _).coeff r)
  rw [T.gal_exp, ← hσ, L1, L2, ← lc_map M k1 A1 ε (map_zero ε), U1, ← lc_map M k0 B σ (map_zero σ), U2,
    lc_map M k2 A2 ε (map_zero ε)]

end GlobalTheory.KZ
end
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.muModelProduct_value_ne_zero_of_depleted : ∀ (e N l : ℕ) (χ θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (g : ℕ → ℂ) (α β : ℂ) (a₀ b₀ c₀ d₀ : ℤ), N * a₀ * d₀ - l * b₀ * c₀ = 1 → 1 ≤ e → 0 < N → l.Prime → ¬ l ∣ N → Prim (2 * e + 1) N χ⁻¹ (fun n => conj (g n)) → α + β = χ l * conj (g l) → α * β = χ l * (l : ℂ) ^ (2 * e) → α ≠ 0 → θ (-1) = (-1) ^ e * ψ (-1) → θ * χ⁻¹ ≠ 1 → ∀ (B : ℕ) (c : ℕ → ℂ), EigF (2 * e + 1) N l χ (fun q => χ q * conj (g q)) α B c → val B c l α 1 (Zs (2 * e + 1) l (ch θ) (hat ⇑(θ * χ⁻¹)) (fun x y => ψ x * ψ⁻¹ y * ((y : ℂ) / x) ^ e)) ≠ 0 → ∀ (B' : ℕ) (c' : ℕ → ℂ), (∀ a a', MF (2 * e + 1) (N * l) (ch χ⁻¹) a → MF (2 * e + 1) (N * l) (ch χ) a' → qs a' = slz (2 * e + 1) !![(N : ℤ) * a₀, b₀; N * l * c₀, N * d₀] (qs a) → lam B' c' a = lam B c a') → (∀ a, MF (2 * e + 1) (N * l) (ch χ⁻¹) a → lam B' c' (Uo l a) = χ⁻¹ l * α * lam B' c' a) → val B' c' l (χ⁻¹ l * α) 1 (Zm (2 * e + 1) l (hat θ) (ch (θ * χ⁻¹)) (fun A d => ψ A * ψ⁻¹ d * ((d : ℂ) / A) ^ e)) ≠ 0 := by
  first | exact @GlobalTheory.zm_val_ne_zero | exact GlobalTheory.zm_val_ne_zero | (intros; apply GlobalTheory.zm_val_ne_zero <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.heckeUl_semisimple_on_lOldSpace : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (χ : DirichletCharacter ℂ N) (α : ℂ), α ^ 2 ≠ χ l * (l : ℂ) ^ (k - 1) →
  ∀ f₁ f₂ : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ),
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₁ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₁) →
    (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑f₂ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑f₂) →
    (∃ g₁ g₂ : CuspForm (CongruenceSubgroup.Gamma1 N) (k : ℤ),
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑g₁ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑g₁) ∧
      (∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 N → ⇑g₂ ∣[(k : ℤ)] γ = χ ((mat γ 1 1 : ℤ) : ZMod N) • ⇑g₂) ∧
      UlF (k : ℤ) l (⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1)) = ⇑g₁ + ⇑g₂ ∣[(k : ℤ)] toGL (dg l 1)) ∧
    ∀ n : ℕ, (fun F => UlF (k : ℤ) l F - α • F)^[n] (⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1)) = 0 →
      UlF (k : ℤ) l (⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1)) = α • (⇑f₁ + ⇑f₂ ∣[(k : ℤ)] toGL (dg l 1)) := by
  first | exact @GlobalTheory.OldSpace.ul_oldSpace | exact GlobalTheory.OldSpace.ul_oldSpace | (intros; apply GlobalTheory.OldSpace.ul_oldSpace <;> assumption)
end

section

open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

theorem _root_.GlobalTheory.T.exists_eichlerShimura_decomposition_cocycle : ∀ (N M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℕ), 5 ≤ N → 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → Γ ≤ CongruenceSubgroup.Gamma1 N → Odd k → 3 ≤ k → ∀ z ∈ Z1 Γ (k - 2), ∃ (f : ModularForm Γ (k : ℤ)) (h : CuspForm Γ (k : ℤ)), z - per Γ (k - 2) ⇑f - cj (per Γ (k - 2) ⇑h) ∈ B1 Γ (k - 2) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.EichlerShimura.exists_per_add_cj_per | exact GlobalTheory.HeckeFamilyMatrices.EichlerShimura.exists_per_add_cj_per | (intros; apply GlobalTheory.HeckeFamilyMatrices.EichlerShimura.exists_per_add_cj_per <;> assumption)
end

section

open GlobalTheory.NeedB Polynomial

namespace GlobalTheory.KummerCob

theorem descent_abstract (A K E Ω : Type) [CommRing A] [IsDedekindDomain A] [Field K] [CharZero K] [Algebra A K]
    [IsFractionRing A K] [Field E] [Algebra K E] [FiniteDimensional K E] [IsGalois K E] [Algebra A E]
    [IsScalarTower A K E] [Field Ω] [Algebra E Ω] (N : ℕ) (hN : 0 < N) (hNu : IsUnit (N : A))
    (s : Finset E) (hs : IntermediateField.adjoin K (s : Set E) = ⊤)
    (hsu : ∀ x ∈ s, ∃ u : Aˣ, x ^ N = algebraMap A E u)
    (hcl : ∀ c : ClassGroup A, ∃ d, c = d ^ N) (w : E) (hw : w ≠ 0)
    (hσ : ∀ σ : E ≃ₐ[K] E, ∃ u : E, u ≠ 0 ∧ σ w = w * u ^ N) :
    ∃ f : K, f ≠ 0 ∧ ∀ B : ValuationSubring Ω, (∀ x : A, algebraMap E Ω (algebraMap A E x) ∈ B) →
      ∃ c : E, c ≠ 0 ∧ B.valuation (algebraMap E Ω (w / algebraMap K E f / c ^ N)) = 1 := by
  haveI : IsDedekindDomain (integralClosure A E) := integralClosure.isDedekindDomain A K E
  haveI : IsFractionRing (integralClosure A E) E := integralClosure.isFractionRing_of_finite_extension K E
  obtain ⟨f, J, hf, hJ⟩ := GlobalTheory.T.divisor_descent_mod_unramified_galois_submodule A (integralClosure A E) K E N hN
    (GlobalTheory.T.kummer_extension_prime_not_map_comap_le_sq A K E N hNu s hs hsu) hcl w hw hσ
  refine ⟨f, hf, fun B hB => ?_⟩
  refine GlobalTheory.T.exists_valuation_div_pow_eq_one_of_pow_eq_span E Ω (integralClosure A E).toSubring B J N hN ?_ _ ?_ hJ
  · intro x
    show algebraMap E Ω (x : E) ∈ B
    obtain ⟨p, hp, hpx⟩ : IsIntegral A (x : E) := x.2
    let φ : A →+* B := ((algebraMap E Ω).comp (algebraMap A E)).codRestrict B.toSubring hB
    have hint : IsIntegral B (algebraMap E Ω x) := by
      refine ⟨p.map φ, hp.map φ, ?_⟩
      rw [Polynomial.eval₂_map]
      have h := congrArg (algebraMap E Ω) hpx
      rw [Polynomial.hom_eval₂, map_zero] at h
      exact h
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    rw [← hy]
    exact y.2
  · exact div_ne_zero hw ((_root_.map_ne_zero _).mpr hf)

theorem isGalois_adjoin_pair (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω) (hN : 0 < N) (hζ : IsPrimitiveRoot ζ N) (hζK : ζ ∈ Set.range (algebraMap K Ω))
    (a b : K) (α β : Ω) (ha : a ≠ 0) (hb : b ≠ 0) (hα : α ^ N = algebraMap K Ω a) (hβ : β ^ N = algebraMap K Ω b) :
    IsGalois K (IntermediateField.adjoin K {α, β}) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have key : ∀ (c : K) (γ x : Ω), c ≠ 0 → γ ^ N = algebraMap K Ω c → γ ∈ IntermediateField.adjoin K {α, β} →
      x ^ N = algebraMap K Ω c → x ∈ IntermediateField.adjoin K {α, β} := by
    intro c γ x hc hγ hm hx
    have hc' : algebraMap K Ω c ≠ 0 := (_root_.map_ne_zero _).mpr hc
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      rw [zero_pow hN.ne'] at hγ
      exact hc' hγ.symm
    have h1 : (x / γ) ^ N = 1 := by rw [div_pow, hx, hγ, div_self hc']
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one h1
    obtain ⟨z, rfl⟩ := hζK
    have : x = algebraMap K Ω z ^ i * γ := by rw [hi, div_mul_cancel₀ _ hγ0]
    rw [this]
    exact mul_mem (pow_mem (IntermediateField.algebraMap_mem _ z) i) hm
  let p : K[X] := (X ^ N - C a) * (X ^ N - C b)
  have hp0 : p ≠ 0 := mul_ne_zero (X_pow_sub_C_ne_zero hN a) (X_pow_sub_C_ne_zero hN b)
  have hroot : ∀ x : Ω, x ∈ p.rootSet Ω ↔ x ^ N = algebraMap K Ω a ∨ x ^ N = algebraMap K Ω b := by
    intro x
    rw [mem_rootSet_of_ne hp0]
    simp [p, sub_eq_zero]
  have heq : IntermediateField.adjoin K {α, β} = IntermediateField.adjoin K (p.rootSet Ω) := by
    apply le_antisymm
    · apply IntermediateField.adjoin.mono
      rintro x (rfl | rfl)
      · exact (hroot _).mpr (Or.inl hα)
      · exact (hroot _).mpr (Or.inr hβ)
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rcases (hroot x).mp hx with h | h
      · exact key a α x ha hα (IntermediateField.subset_adjoin _ _ (by simp)) h
      · exact key b β x hb hβ (IntermediateField.subset_adjoin _ _ (by simp)) h
  rw [heq]
  haveI := IntermediateField.adjoin_rootSet_isSplittingField (K := K) (L := Ω) (p := p) (IsAlgClosed.splits _)
  haveI : Normal K (IntermediateField.adjoin K (p.rootSet Ω)) := Normal.of_isSplittingField p
  exact ⟨⟩

theorem adjoin_pair_eq_top (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (α β : Ω)
    (α' β' : IntermediateField.adjoin K {α, β}) (hα : (α' : Ω) = α) (hβ : (β' : Ω) = β) :
    IntermediateField.adjoin K ({α', β'} : Set (IntermediateField.adjoin K {α, β})) = ⊤ := by
  apply IntermediateField.map_injective (IntermediateField.adjoin K {α, β}).val
  rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val,
    Set.image_pair]
  simp [hα, hβ]

theorem divisor_descends : ∀ (k K Ω : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k[X] K] [Algebra (RatFunc k) K]
    [IsScalarTower k[X] (RatFunc k) K] [FiniteDimensional (RatFunc k) K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (N : ℕ) (ζ : Ω), 0 < N → IsPrimitiveRoot ζ N →
    ∀ (a b : K) (α β : Ω), a ∈ FunctionField.ringOfIntegers k K → a⁻¹ ∈ FunctionField.ringOfIntegers k K →
      b ∈ FunctionField.ringOfIntegers k K → b⁻¹ ∈ FunctionField.ringOfIntegers k K → a ≠ 0 → b ≠ 0 →
      α ^ N = algebraMap K Ω a → β ^ N = algebraMap K Ω b →
      ∀ θ : Ω, θ ≠ 0 → θ ^ N ∈ IntermediateField.adjoin K {α, β} →
      (∀ s : Ω ≃ₐ[K] Ω, ∃ u ∈ IntermediateField.adjoin K {α, β}, u ≠ 0 ∧ s (θ ^ N) = θ ^ N * u ^ N) →
      ∃ f : K, f ≠ 0 ∧ ∀ B : ValuationSubring Ω, GlobalTheory.NeedB.Over (FunctionField.ringOfIntegers k K).toSubring B →
        ∃ c ∈ IntermediateField.adjoin K {α, β}, c ≠ 0 ∧ B.valuation (θ ^ N / (algebraMap K Ω f * c ^ N)) = 1 := by
  intro k K Ω _ _ _ _ _ _ _ _ _ _ _ N ζ hN hζ a b α β ha ha' hb hb' ha0 hb0 hα hβ θ hθ hw hs
  classical
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap (RatFunc k) K).injective
  haveI := isGalois_adjoin_pair K Ω N ζ hN hζ (zeta_mem_range k K Ω N ζ hN hζ) a b α β ha0 hb0 hα hβ
  haveI : FiniteDimensional K (IntermediateField.adjoin K {α, β}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  have hNu : IsUnit (N : FunctionField.ringOfIntegers k K) := by
    have h1 : IsUnit (N : k) := (Nat.cast_ne_zero.mpr hN.ne').isUnit
    have h2 := h1.map ((algebraMap k[X] (FunctionField.ringOfIntegers k K)).comp C)
    rwa [map_natCast] at h2
  let α' : IntermediateField.adjoin K {α, β} := ⟨α, IntermediateField.subset_adjoin _ _ (by simp)⟩
  let β' : IntermediateField.adjoin K {α, β} := ⟨β, IntermediateField.subset_adjoin _ _ (by simp)⟩
  obtain ⟨f, hf, hB⟩ := descent_abstract (FunctionField.ringOfIntegers k K) K (IntermediateField.adjoin K {α, β}) Ω
    N hN hNu {α', β'} (by rw [Finset.coe_pair]; exact adjoin_pair_eq_top K Ω α β α' β' rfl rfl)
    (by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨⟨⟨a, ha⟩, ⟨a⁻¹, ha'⟩, Subtype.ext (mul_inv_cancel₀ ha0), Subtype.ext (inv_mul_cancel₀ ha0)⟩,
          Subtype.ext hα⟩
      · rw [Finset.mem_singleton.mp hx]
        exact ⟨⟨⟨b, hb⟩, ⟨b⁻¹, hb'⟩, Subtype.ext (mul_inv_cancel₀ hb0), Subtype.ext (inv_mul_cancel₀ hb0)⟩,
          Subtype.ext hβ⟩)
    (GlobalTheory.T.classGroup_affineCurve_divisible_charZero k K N hN) ⟨θ ^ N, hw⟩ (fun h => pow_ne_zero N hθ (congrArg Subtype.val h))
    (by
      intro σ
      obtain ⟨u, hu, hu0, h⟩ := hs (σ.liftNormal Ω)
      refine ⟨⟨u, hu⟩, fun h => hu0 (congrArg Subtype.val h), Subtype.ext ?_⟩
      exact (σ.liftNormal_commutes Ω ⟨θ ^ N, hw⟩).symm.trans h)
  refine ⟨f, hf, fun B hO => ?_⟩
  obtain ⟨c, hc, hv⟩ := hB B fun x => hO x.1 x.2
  refine ⟨c, c.2, fun h => hc (Subtype.ext h), ?_⟩
  rw [div_div, map_div₀, map_mul, map_pow] at hv
  exact hv

end GlobalTheory.KummerCob
end

section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem exists_conj_of_inR : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ) (s : Ω ≃+* Ω) (f : ℍ → ℂ), InR ε.range f → ∃ f' : ℍ → ℂ, InR ε.range f' ∧ ∀ h h' : HahnSeries ℚ Ω, IsExp ε f h → IsExp ε f' h' → ∀ r, h'.coeff r = s (h.coeff r) := by
  intro Ω _ ε s f hf
  obtain ⟨N, w, hN, hLv⟩ := hf
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_complex_ringEquiv_extending_subfield_aut Ω ε s
  have hgE : ∀ x ∈ ε.range, g x ∈ ε.range := by
    rintro x ⟨y, rfl⟩
    exact ⟨s y, (hg y).symm⟩
  obtain ⟨d, hd⟩ := GlobalTheory.WpFam.exists_unit_zetaAct N g
  obtain ⟨f', hLv', hconj⟩ := GlobalTheory.T.levelN_function_galois_conj_qExpansion g ε.range N d w f hgE hd hLv
  refine ⟨f', ⟨N, w, hN, hLv'⟩, ?_⟩
  intro h h' hh hh' r
  have h1 : dg d * redGL N 1 = redGL N 1 * dg d := by
    rw [GlobalTheory.WpFam.Act.redGL_one]; simp
  have hc := hconj 1 1 h1
  simp only [one_smul] at hc
  have hq := hLv.2 1
  simp only [one_smul] at hq
  exact GlobalTheory.T.cuspExpansion_coeff_conj_of_qExpansion_conj Ω ε s.toRingHom g N w f f' h h' hg hN hq hc hh hh' r

end GlobalTheory.FN
end

section

open GlobalTheory.K5

theorem _root_.GlobalTheory.T.kummer_cocycle_twisted_coboundary : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (k : ℕ) (χ κ : Gal p Ω → ZMod (p ^ k)), IsKum T k (Ggeo p Ω) (T.qq k) κ →
  (∀ a : Gal p Ω → Ω, IntegralLocallyConstCochainModPow k (Ggeo p Ω) a → IsTwistedOneCocycle 0 k (Ggeo p Ω) χ a →
      ∃ o : Ω, IsInt (p := p) o ∧ (∀ g ∈ Ggeo p Ω, g o = o) ∧
        IsTwistedOneCoboundary 0 k (Ggeo p Ω) χ (fun g => (p : Ω) ^ c * a g - o * ((κ g).val : Ω))) ∧
  (∀ o : Ω, IsInt (p := p) o → (∀ g ∈ Ggeo p Ω, g o = o) →
      IsTwistedOneCoboundary 0 k (Ggeo p Ω) χ (fun g => o * ((κ g).val : Ω)) → Cong (p := p) k ((p : Ω) ^ c * o) 0) := by
  first | exact @GlobalTheory.K5.TopGeo.top | exact GlobalTheory.K5.TopGeo.top | (intros; apply GlobalTheory.K5.TopGeo.top <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.halfPeterssonIntegral_heckeU_adjoint : ∀ (k L N l : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h a : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L → l.Prime → l ∣ L → ¬ l ∣ N → Wt L ρ → CF k L (ch ε) h → MF k L (ch ε) a → pet k ρ (qs h) (qs (Uo l a)) = pet k ρ (fun τ => ∑ j : Fin l, slz k (repL L l (some j)) (qs h) τ) (qs a) := by
  first | exact @GlobalTheory.adjoint_U | exact GlobalTheory.adjoint_U | (intros; apply GlobalTheory.adjoint_U <;> assumption)
end

section

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem _root_.GlobalTheory.T.rankinIntegral_tendsto_at_zero : ∀ (k j L L' N : ℕ) (ε : DirichletCharacter ℂ N) (Φ : ℤ × ℤ → ℂ) (ρ : ℍ → ℝ) (h b : ℕ → ℂ), 1 ≤ k → 2 ≤ j → 0 < L → 0 < L' → N ∣ L' → Wt L' ρ → CF k L' (ch ε) h → PolyB b → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Tendsto (fun s : ℝ => pet k ρ (qs h) (fun τ => qs b τ * lat j s L (0, 1) Φ τ * ((τ.im ^ s : ℝ) : ℂ))) (𝓝[>] 0) (𝓝 (pet k ρ (qs h) (fun τ => qs b τ * lat j 0 L (0, 1) Φ τ))) := by
  first | exact @GlobalTheory.EisM.rankin_tendsto | exact GlobalTheory.EisM.rankin_tendsto | (intros; apply GlobalTheory.EisM.rankin_tendsto <;> assumption)
end
