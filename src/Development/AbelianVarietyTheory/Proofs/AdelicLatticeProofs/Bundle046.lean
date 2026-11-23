module

import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.Bundle002
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle031
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle042
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle044
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle002
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle037
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle024
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle041
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle045
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle028
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle020
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

section

namespace GlobalTheory.IntegralMultipleClearDenominators

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ K : ℕ, 0 < K ∧ IsIntegral ℤ ((K : E) * c) := by
  have h : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hint⟩ := h.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h1 | h1
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h1]
      exact (Int.cast_natCast _).symm
    rw [this]; exact hint
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h1]
      rw [Int.cast_neg, neg_neg]
      exact (Int.cast_natCast _).symm
    rw [this, neg_mul]; exact hint.neg

theorem exists_nsmul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (↑L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ N : ℕ, 0 < N ∧ N • w ∈ L := by
  apply PI.WAU.exists_nat_smul_mem <;> assumption

theorem exists_nsmul_mulVec_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (↑L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ N : ℕ, 0 < N ∧ ∀ v ∈ L, N • Matrix.mulVec M v ∈ L := by
  obtain ⟨s, hs⟩ := hfg
  choose f hf0 hf using exists_nsmul_mem L hL
  refine ⟨∏ x ∈ s, f (M.mulVec x), Finset.prod_pos fun x _ => hf0 _, ?_⟩
  intro v hv
  rw [← hs] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => f (M.mulVec x)) (Finset.mem_coe.1 hx)
    rw [hk, mul_comm, mul_smul]
    exact nsmul_mem (hf _) k
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add, smul_add]
    exact L.add_mem hx hy
  | smul c x _ hx =>
    rw [Matrix.mulVec_smul, smul_comm]
    exact L.smul_mem c hx

end GlobalTheory.IntegralMultipleClearDenominators
end

section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem norm_of_isSquare_mul {L : Type} [Field L] {x y δ : L} (hx : x ≠ 0)
    (h : IsSquare (x * y)) (hn : ∃ a b : L, x = a ^ 2 - δ * b ^ 2) :
    ∃ a b : L, y = a ^ 2 - δ * b ^ 2 := by
  obtain ⟨s, hs⟩ := h
  obtain ⟨a, b, hab⟩ := hn
  refine ⟨a * s / x, b * s / x, ?_⟩
  field_simp
  linear_combination x * hs + s ^ 2 * hab

theorem mem_normSub_real_of_pos {F : Type} [Field F] (σ : F →+* ℝ) (δ : F) (x : Fˣ)
    (h : 0 < σ (x : F)) : x ∈ normSub σ δ :=
  ⟨Real.sqrt (σ (x : F)), 0, by rw [Real.sq_sqrt h.le]; ring⟩

theorem locSq_le_locNorm_of_delta (F : Type) [Field F] [NumberField F] (δ : F)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : locSq F S ≤ locNorm F δ S := by
  unfold locSq locNorm finSq
  exact inf_le_inf (iInf_mono fun v => iInf_mono fun _ => sqSub_le_normSub _ _)
    (iInf_mono fun σ => sqSub_le_normSub _ _)

theorem two_pow_le_index_locNorm :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))),
      δ ≠ 0 → (locNorm F δ S).index ≠ 0 ∧
        2 ^ (tFin F δ S + tReal F δ) ≤ (locNorm F δ S).index := by
  intro F _ _ δ S hδ
  classical
  have h0 : (locNorm F δ S).index ≠ 0 :=
    ne_zero_of_dvd_ne_zero (GlobalTheory.T.index_unitsLocalSquaresFiniteRealPlaces_le F S).1
      (Subgroup.index_dvd_of_le (locSq_le_locNorm_of_delta F δ S))
  refine ⟨h0, ?_⟩
  set A : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | v ∈ S ∧ ¬ IsSquare (algebraMap F (v.adicCompletion F) δ)} with hA
  set B : Set (F →+* ℝ) := {σ | σ δ < 0} with hB
  have hAf : A.Finite := S.finite_toSet.subset fun v hv => hv.1
  have hBf : B.Finite := Set.toFinite _
  letI : Fintype A := hAf.fintype
  letI : Fintype B := hBf.fintype
  let K : A ⊕ B → Subgroup Fˣ := Sum.elim
    (fun v => normSub (algebraMap F (v.1.adicCompletion F)) δ) (fun σ => normSub σ.1 δ)
  have hle : locNorm F δ S ≤ ⨅ i, K i := by
    refine le_iInf ?_
    rintro (v | σ)
    · exact inf_le_left.trans (iInf₂_le v.1 v.2.1)
    · exact inf_le_right.trans (iInf_le _ σ.1)
  have hdvd := Subgroup.index_dvd_of_le hle
  have hcard : Fintype.card (A ⊕ B) = tFin F δ S + tReal F δ := by
    rw [Fintype.card_sum, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    rfl
  rw [← hcard]
  refine le_trans (GlobalTheory.T.two_pow_card_le_index_iInf_of_independent Fˣ (A ⊕ B) K ?_ (ne_zero_of_dvd_ne_zero h0 hdvd))
    (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd)
  rintro (v | σ)
  · obtain ⟨y, hy0, hy⟩ := GlobalTheory.T.exists_local_nonnorm_of_nonsquare_adicCompletion F v.1 (algebraMap F _ δ) (by simpa using hδ) v.2.2
    obtain ⟨x, hx0, hxv, hxσ⟩ := GlobalTheory.T.exists_approx_mod_local_squares F S
      (Function.update (fun w : HeightOneSpectrum (𝓞 F) => (1 : w.adicCompletion F)) v.1 y)
      (fun _ => 1) (by
        intro w
        by_cases hw : w = v.1
        · subst hw; simpa using hy0
        · simp [Function.update_of_ne hw]) (by simp)
    refine ⟨Units.mk0 x hx0, ?_, ?_⟩
    · intro hm
      have h1 := hxv v.1 v.2.1
      rw [Function.update_self] at h1
      exact hy (norm_of_isSquare_mul (by simpa using hx0) h1 hm)
    · rintro (w | τ) hj
      · have hw : w.1 ≠ v.1 := fun h => hj (congrArg Sum.inl (Subtype.ext h))
        have h1 := hxv w.1 w.2.1
        rw [Function.update_of_ne hw, mul_one] at h1
        exact sqSub_le_normSub _ _ h1
      · exact mem_normSub_real_of_pos _ _ _ (by simpa using hxσ τ.1)
  · obtain ⟨x, hx0, hxv, hxσ⟩ := GlobalTheory.T.exists_approx_mod_local_squares F S (fun _ => 1)
      (fun τ => if τ = σ.1 then -1 else 1) (by simp) (by
        intro τ
        split_ifs <;> simp)
    refine ⟨Units.mk0 x hx0, ?_, ?_⟩
    · rintro ⟨a, b, hab⟩
      have h1 := hxσ σ.1
      have h2 : σ.1 δ < 0 := σ.2
      simp only [if_true] at h1
      have h3 : σ.1 x = a ^ 2 - σ.1 δ * b ^ 2 := hab
      nlinarith [sq_nonneg a, mul_nonneg (neg_nonneg.2 h2.le) (sq_nonneg b)]
    · rintro (w | τ) hj
      · have h1 := hxv w.1 w.2.1
        rw [mul_one] at h1
        exact sqSub_le_normSub _ _ h1
      · have hw : τ.1 ≠ σ.1 := fun h => hj (congrArg Sum.inr (Subtype.ext h))
        exact mem_normSub_real_of_pos _ _ _ (by simpa [hw] using hxσ τ.1)

end GlobalTheory.QNorm
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem corner_mul_corner {A : Type} [Ring A] (E x y : A) (hE : E * E = E)
    (hx : E * x * (1 - E) = x) (hy : E * y * (1 - E) = y) : x * y = 0 := by
  have h : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  calc x * y = (E * x * (1 - E)) * (E * y * (1 - E)) := by rw [hx, hy]
    _ = E * x * ((1 - E) * E) * y * (1 - E) := by simp only [mul_assoc]
    _ = 0 := by rw [h]; simp

theorem exists_linExt_corner_proj : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsQGroup Γ → e * e = e → ∃ c : ι × ι → ι × ι → ℚ, (∀ X : Matrix ι ι ℂ, 1 + linExt c X ∈ Γ ∧ e.map (algebraMap ℚ ℂ) * linExt c X * (1 - e.map (algebraMap ℚ ℂ)) = linExt c X) ∧ ∀ ε : Matrix ι ι ℂ, 1 + ε ∈ Γ → e.map (algebraMap ℚ ℂ) * ε * (1 - e.map (algebraMap ℚ ℂ)) = ε → linExt c ε = ε := by
  intro ι _ _ Γ e hΓ he
  set E : Matrix ι ι ℂ := e.map (algebraMap ℚ ℂ) with hEdef
  have hE : E * E = E := by
    rw [hEdef, ← Matrix.map_mul, he]
  let S : Submodule ℂ (Matrix ι ι ℂ) :=
    { carrier := {ε | 1 + ε ∈ Γ ∧ E * ε * (1 - E) = ε}
      zero_mem' := ⟨by simpa using hΓ.one_mem, by simp⟩
      add_mem' := by
        rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
        refine ⟨?_, by rw [mul_add, add_mul, hx2, hy2]⟩
        have h0 := corner_mul_corner E x y hE hx2 hy2
        have h1 := hΓ.mul_mem _ hx1 _ hy1
        have h2 : (1 + x) * (1 + y) = 1 + (x + y) := by
          rw [mul_add, add_mul, add_mul, h0]; simp [add_assoc]
        rwa [h2] at h1
      smul_mem' := by
        rintro t x ⟨hx1, hx2⟩
        refine ⟨GlobalTheory.T.one_add_smul_mem_of_sq_zero' ι Γ hΓ x (corner_mul_corner E x x hE hx2 hx2) hx1 t, ?_⟩
        rw [Matrix.mul_smul, Matrix.smul_mul, hx2] }
  have hS : ∀ σ : ℂ ≃+* ℂ, ∀ x ∈ S, x.map σ ∈ S := by
    rintro σ x ⟨hx1, hx2⟩
    have hEσ : (σ : ℂ →+* ℂ).mapMatrix E = E := by
      ext i j
      simp [hEdef]
    have hx : x.map σ = (σ : ℂ →+* ℂ).mapMatrix x := rfl
    refine ⟨?_, ?_⟩
    · have h1 := hΓ.aut_mem σ _ hx1
      have h2 : (1 + x).map σ = (σ : ℂ →+* ℂ).mapMatrix (1 + x) := rfl
      rw [h2, map_add (f := _), map_one] at h1
      exact h1
    · have h3 := congrArg (σ : ℂ →+* ℂ).mapMatrix hx2
      rw [map_mul, map_mul, map_sub, map_one, hEσ] at h3
      exact h3
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.T.exists_rat_projector_of_autStable_matrices ι S hS
  exact ⟨c, fun X => hc1 X, fun ε h1 h2 => hc2 ε ⟨h1, h2⟩⟩

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_rat_idempotent_blk_eq_zero : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ¬ SS Γ → ∃ e : Matrix ι ι ℚ, e * e = e ∧ (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) ∧ ∃ a ∈ Submodule.span ℂ Γ, a ≠ 0 ∧ blk e a = 0 := by
  intro ι _ _ Γ hΓ hss
  obtain ⟨W, hWinv, hWσ, a, ha_span, ha0, ha_into, ha_kill⟩ := GlobalTheory.T.invariant_subspace_not_semisimple ι Γ hΓ hss
  obtain ⟨e, hee, hW⟩ := GlobalTheory.T.exists_rat_idempotent_of_autStable_subspace ι W hWσ

  have hEE : e.map (algebraMap ℚ ℂ) * e.map (algebraMap ℚ ℂ) = e.map (algebraMap ℚ ℂ) := by
    rw [← Matrix.map_mul, hee]
  have hEmem : ∀ v, e.map (algebraMap ℚ ℂ) *ᵥ v ∈ W := fun v => by
    rw [hW, Matrix.mulVec_mulVec, hEE]
  have hfix : ∀ w ∈ W, e.map (algebraMap ℚ ℂ) *ᵥ w = w := fun w hw => (hW w).1 hw
  refine ⟨e, hee, ?_, a, ha_span, ha0, ?_⟩
  ·
    intro g hg
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      hfix _ (hWinv g hg _ (hEmem v)), sub_self, Matrix.zero_mulVec]
  ·
    rw [Matrix.ext_iff_mulVec]
    intro v
    unfold blk
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha_kill _ (hEmem v),
      Matrix.mulVec_zero, zero_add, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      Matrix.sub_mulVec, Matrix.one_mulVec, hfix _ (ha_into _), sub_self, Matrix.zero_mulVec]

end GlobalTheory.ClassFin
end

section

open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

theorem exists_component_mem_vanI_of_mem_span {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ))
    (l : ℂ →ₗ[ℚ] ℚ) (f : MvPolynomial (ι × ι) ℂ)
    (hf : f ∈ Submodule.span ℂ ((MvPolynomial.map (algebraMap ℚ ℂ)) '' vanI Γ)) :
    ∀ c : ℂ, ∃ f' ∈ vanI Γ, ∀ m, AddMonoidAlgebra.coeff f' m = l (c * AddMonoidAlgebra.coeff f m) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, hp, rfl⟩ := hx
    intro c
    have hvan : l c • p ∈ vanI Γ := by
      show ∀ g ∈ Γ, ev (l c • p) g = 0
      intro g hg
      have h0 : ev p g = 0 := hp g hg
      simp only [ev] at h0 ⊢
      rw [map_smul, h0, smul_zero]
    refine ⟨l c • p, hvan, fun m => ?_⟩
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul, mul_comm c,
      ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
  | zero =>
    intro c
    have hvan : (0 : MvPolynomial (ι × ι) ℚ) ∈ vanI Γ := by
      show ∀ g ∈ Γ, ev (0 : MvPolynomial (ι × ι) ℚ) g = 0
      intro g _
      simp [ev]
    exact ⟨0, hvan, fun m => by simp⟩
  | add x y _ _ hx hy =>
    intro c
    obtain ⟨a, ha, ha'⟩ := hx c
    obtain ⟨b, hb, hb'⟩ := hy c
    have hvan : a + b ∈ vanI Γ := by
      show ∀ g ∈ Γ, ev (a + b) g = 0
      intro g hg
      have h1 : ev a g = 0 := ha g hg
      have h2 : ev b g = 0 := hb g hg
      simp only [ev] at h1 h2 ⊢
      rw [map_add (f := _), h1, h2, add_zero]
    refine ⟨a + b, hvan, fun m => ?_⟩
    rw [MvPolynomial.coeff_add, ha', hb', MvPolynomial.coeff_add, mul_add, map_add (f := _)]
  | smul a x _ hx =>
    intro c
    obtain ⟨f', hf', h'⟩ := hx (c * a)
    exact ⟨f', hf', fun m => by rw [h', MvPolynomial.coeff_smul, smul_eq_mul, mul_assoc]⟩

theorem component_mem_vanI : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ σ : ℂ ≃+* ℂ, ∀ g ∈ Γ, g.map σ ∈ Γ) → ∀ f : MvPolynomial (ι × ι) ℂ, (∀ g ∈ Γ, evC f g = 0) → ∀ (l : ℂ →ₗ[ℚ] ℚ) (f' : MvPolynomial (ι × ι) ℚ), (∀ m, AddMonoidAlgebra.coeff f' m = l (AddMonoidAlgebra.coeff f m)) → f' ∈ vanI Γ := by
  intro ι _ _ Γ hΓ f hf l f' hf'
  obtain ⟨p, hp, hpc⟩ :=
    exists_component_mem_vanI_of_mem_span Γ l f (GlobalTheory.T.mem_span_ratPolysVanishing_of_autStable ι Γ hΓ f hf) 1
  have hfp : f' = p := by
    ext m
    rw [hf', hpc, one_mul]
  exact hfp ▸ hp

end GlobalTheory.ClassFin
end

section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem nonnorm_pIdx_map (p : ℕ) {G H : Type} [CommGroup G] [CommGroup H] (f : G →* H)
    (hf : Function.Injective f) (U : Subgroup G) : pIdx p (U.map f) = pIdx p U := by
  have h : pows p (U.map f) = (pows p U).map f := by
    unfold pows
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp
  unfold pIdx
  rw [h, Subgroup.relIndex_map_map_of_injective _ _ hf]

theorem nonnorm_pTor_map (p : ℕ) {G H : Type} [CommGroup G] [CommGroup H] (f : G →* H)
    (hf : Function.Injective f) (U : Subgroup G) : pTor p (U.map f) = pTor p U := by
  unfold pTor
  symm
  refine Nat.card_eq_of_bijective
    (fun x => ⟨f x.1, Subgroup.mem_map_of_mem f x.2.1, by rw [← map_pow, x.2.2, map_one]⟩) ⟨?_, ?_⟩
  · intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  · rintro ⟨_, ⟨x, hx, rfl⟩, h⟩
    refine ⟨⟨x, hx, hf ?_⟩, rfl⟩
    rw [map_pow, h, map_one]

theorem exists_local_nonnorm : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (ζ δ : F)
    (v : HeightOneSpectrum (𝓞 F)), p.Prime → IsPrimitiveRoot ζ p →
    (∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ) →
    ∃ c : (v.adicCompletion F)ˣ, c ∉ kNorm p (RingHom.id (v.adicCompletion F))
      (algebraMap F (v.adicCompletion F) δ) := by
  intro p F _ _ ζ δ v hp hζ hδ
  by_contra hall
  push_neg at hall
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  have hζ' : IsPrimitiveRoot (algebraMap F (v.adicCompletion F) ζ) p :=
    hζ.map_of_injective (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨L, _, _, θ, σ, hK⟩ := exists_isKum p (v.adicCompletion F) _ _ hp hζ' hδ
  obtain ⟨hfd, hrk, hσp, hfix, -, -, hnorm⟩ := GlobalTheory.T.cyclic_hilbert90_kummer_and_mem_kNorm_iff p _ L _ _ θ σ hK
  obtain ⟨e, he⟩ : ∃ e : ℕ, v.valuation F (p : F) = WithZero.exp (-(e : ℤ)) := by
    have h0 : v.valuation F (p : F) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact_mod_cast hp.ne_zero
    have h1 : v.valuation F (p : F) ≤ 1 := by
      have := v.valuation_le_one (K := F) (p : 𝓞 F)
      simpa using this
    have h2 : WithZero.log (v.valuation F (p : F)) ≤ 0 := by
      rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
      exact h1
    refine ⟨(-WithZero.log (v.valuation F (p : F))).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]
  obtain ⟨htL, hiL⟩ := GlobalTheory.T.pIdx_units_finite_extension_adicCompletion' p F v e L hp.pos he
  obtain ⟨htK, hiK⟩ := GlobalTheory.T.pIdx_units_finite_extension_adicCompletion' p F v e (v.adicCompletion F) hp.pos he
  rw [hrk] at hiL
  rw [Module.finrank_self, pow_one] at hiK
  have hQ : Ideal.absNorm v.asIdeal ^ e ≠ 0 :=
    pow_ne_zero _ (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  generalize Ideal.absNorm v.asIdeal ^ e = Q at hiL hiK hQ
  let s : Lˣ →* Lˣ := Units.map (σ : L →* L)
  have hs : ∀ (n : ℕ) (a : Lˣ), ((s^[n] a : Lˣ) : L) = σ^[n] (a : L) := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  let f : (v.adicCompletion F)ˣ →* Lˣ :=
    Units.map (algebraMap (v.adicCompletion F) L : v.adicCompletion F →* L)
  have hf : Function.Injective f :=
    Units.map_injective (algebraMap (v.adicCompletion F) L).injective
  have hfx : fix s = (⊤ : Subgroup (v.adicCompletion F)ˣ).map f := by
    ext a
    rw [mem_fix]
    constructor
    · intro ha
      obtain ⟨b, hb⟩ := hfix a (congrArg Units.val ha)
      have hb0 : b ≠ 0 := by
        rintro rfl
        exact a.ne_zero (by rw [hb, map_zero])
      exact ⟨Units.mk0 b hb0, trivial, Units.ext hb.symm⟩
    · rintro ⟨b, -, rfl⟩
      exact Units.ext (σ.commutes (b : v.adicCompletion F))
  have hiL0 : pIdx p (⊤ : Subgroup Lˣ) ≠ 0 := by
    rw [hiL]
    exact mul_ne_zero (mul_ne_zero hp.ne_zero (pow_ne_zero _ hQ)) htL
  obtain ⟨-, h1, -, -, hH⟩ := GlobalTheory.T.herbrand_prime_order' p Lˣ s hp
    (fun a => Units.ext (by rw [hs, hσp])) hiL0 htL
  have h0 : (nrm s p).range.relIndex (fix s) = 1 := by
    rw [Subgroup.relIndex_eq_one, hfx]
    rintro _ ⟨c, -, rfl⟩
    obtain ⟨y, hy⟩ := (hnorm c).1 (hall c)
    have hy0 : y ≠ 0 := by
      rintro rfl
      have : ∏ i ∈ Finset.range p, σ^[i] (0 : L) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.2 hp.pos) rfl
      rw [this] at hy
      exact c.ne_zero ((map_eq_zero _).1 hy.symm)
    refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
    rw [nrm_apply, Units.coe_prod]
    simp only [hs, Units.val_mk0]
    exact hy
  rw [h0, hfx, nonnorm_pIdx_map p f hf, nonnorm_pTor_map p f hf, hiL, hiK, one_pow] at hH
  generalize pTor p (⊤ : Subgroup Lˣ) = tL at hH htL
  generalize pTor p (⊤ : Subgroup (v.adicCompletion F)ˣ) = tK at hH htK
  generalize (dif s).range.relIndex (nrm s p).ker = h at hH h1
  have hc : Q ^ p * tL * tK ^ p ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hQ) htL) (pow_ne_zero _ htK)
  have key : p = h ^ (p - 1) * p ^ p := by
    apply mul_right_cancel₀ hc
    rw [mul_pow, mul_pow] at hH
    linear_combination hH
  have hle : p ^ p ≤ p := by
    calc p ^ p ≤ h ^ (p - 1) * p ^ p := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (pow_ne_zero _ h1))
      _ = p := key.symm
  have hlt : p ^ 1 < p ^ p := Nat.pow_lt_pow_right hp.one_lt hp.one_lt
  rw [pow_one] at hlt
  omega

end GlobalTheory.CNorm
end
