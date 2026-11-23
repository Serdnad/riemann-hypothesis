module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle024
public import Formalism.ConjugateSelfDual.Bundle001
public import Formalism.CyclotomicNorms.StatementT
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Formalism.LocalRingCardinality.DataCD
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle023
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle029
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.GaloisValuations.GlobalA
public import ReciprocityTheory.GaloisValuations.GlobalB
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import Mathlib.Algebra.Algebra.ZMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle021

@[expose] public section

section

open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

namespace GlobalTheory.Mem.Lift.DCalc

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]

theorem hasDerivAt_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : V → E} (hF : Differentiable ℝ F)
    (w y : V) : HasDerivAt (fun t : ℝ => F (w + t • y)) (fderiv ℝ F w y) 0 := by
  have hl : HasDerivAt (fun t : ℝ => w + t • y) y 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const y).const_add w
  have hF' : HasFDerivAt F (fderiv ℝ F w) (w + (0 : ℝ) • y) := by
    simpa using (hF w).hasFDerivAt
  exact hF'.comp_hasDerivAt (0 : ℝ) hl

theorem hasDerivAt_lin (a : ℝ) : HasDerivAt (fun t : ℝ => (π * I * ((t * a : ℝ) : ℂ))) (π * I * a) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => ((t * a : ℝ) : ℂ)) (a : ℂ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const a).ofReal_comp
  exact h1.const_mul (π * I)

theorem hasDerivAt_phase (a : ℝ) {G : ℝ → B} {G' : B} (hG : HasDerivAt G G' 0) :
    HasDerivAt (fun t : ℝ => cexp (π * I * ((t * a : ℝ) : ℂ)) • G t) (G' + (π * I * a : ℂ) • G 0) 0 := by
  have hc := (hasDerivAt_lin a).cexp
  have hp : HasDerivAt (fun t : ℝ => cexp (π * I * ((t * a : ℝ) : ℂ)) • G t) _ 0 := hc.smul hG
  convert hp using 1
  simp

variable {om : V →L[ℝ] V →L[ℝ] ℝ} {ρ : V → B →L[ℂ] B}

theorem skew (h0 : ∀ x, om x x = 0) (x y : V) : om y x = -om x y := by
  have hxy := h0 (x + y)
  simp only [map_add (f := _), _root_.add_apply, h0] at hxy
  linarith

theorem heis_dH (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (w y : V) :
    ρ w (dH ρ y f) = fderiv ℝ (fun u => ρ u f) w y + (π * I * (om w y : ℂ)) • ρ w f := by
  have hd : Differentiable ℝ (fun u => ρ u f) :=
    (show ContDiff ℝ ∞ (fun u => ρ u f) from hf).differentiable (by simp)
  have h1 : HasDerivAt (fun t : ℝ => ρ w (ρ (t • y) f)) (ρ w (dH ρ y f)) 0 := by
    have hl := hasDerivAt_dH y hf
    exact ((ρ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hl
  have h2 : HasDerivAt (fun t : ℝ => ρ w (ρ (t • y) f))
      (fderiv ℝ (fun u => ρ u f) w y + (π * I * (om w y : ℂ)) • ρ w f) 0 := by
    have hp := hasDerivAt_phase (om w y) (hasDerivAt_line hd w y)
    convert (preTransparency := .reducible) hp using 1
    · funext t
      rw [h.2.1]
      simp
    · simp
  exact h1.unique h2

theorem sm_heis (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (w : V) : Sm ρ (ρ w f) := by
  have hf' : ContDiff ℝ ∞ (fun u => ρ u f) := hf
  have e : (fun u => ρ u (ρ w f)) = fun u => cexp (π * I * (om u w : ℂ)) • ρ (u + w) f := by
    funext u
    exact h.2.1 u w f
  show ContDiff ℝ ∞ (fun u => ρ u (ρ w f))
  rw [e]
  apply ContDiff.smul
  · apply ContDiff.cexp
    exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (om.contDiff.clm_apply contDiff_const))
  · exact hf'.comp (contDiff_id.add contDiff_const)

theorem contDiff_fderiv {f : B} (hf : Sm ρ f) : ContDiff ℝ ∞ (fderiv ℝ fun u => ρ u f) := (contDiff_infty_iff_fderiv.1 (show ContDiff ℝ ∞ (fun u => ρ u f) from hf)).2

theorem sm_dH (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (v : V) : Sm ρ (dH ρ v f) := by
  have hf' : ContDiff ℝ ∞ (fun u => ρ u f) := hf
  have e : (fun u => ρ u (dH ρ v f)) =
      fun u => fderiv ℝ (fun u => ρ u f) u v + (π * I * (om u v : ℂ)) • ρ u f := by
    funext u
    exact heis_dH h hf u v
  show ContDiff ℝ ∞ (fun u => ρ u (dH ρ v f))
  rw [e]
  refine ((contDiff_fderiv hf).clm_apply contDiff_const).add ?_
  exact (contDiff_const.mul
    (Complex.ofRealCLM.contDiff.comp (om.contDiff.clm_apply contDiff_const))).smul hf'

theorem dH_heis (h0 : ∀ x, om x x = 0) (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (v w : V) :
    dH ρ v (ρ w f) = ρ w (dH ρ v f) + (2 * π * I * (om v w : ℂ)) • ρ w f := by
  have hd : Differentiable ℝ (fun u => ρ u f) :=
    (show ContDiff ℝ ∞ (fun u => ρ u f) from hf).differentiable (by simp)
  have h1 := hasDerivAt_dH v (sm_heis h hf w)
  have h2 : HasDerivAt (fun t : ℝ => ρ (t • v) (ρ w f))
      (fderiv ℝ (fun u => ρ u f) w v + (π * I * (om v w : ℂ)) • ρ w f) 0 := by
    have hp := hasDerivAt_phase (om v w) (hasDerivAt_line hd w v)
    convert (preTransparency := .reducible) hp using 1
    · funext t
      rw [h.2.1, add_comm (t • v) w]
      simp
    · simp
  rw [h1.unique h2, heis_dH h hf w v, skew h0 w v, add_assoc, ← add_smul]
  congr 2
  push_cast
  ring

theorem dH_dH (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (u v : V) :
    dH ρ u (dH ρ v f) = fderiv ℝ (fderiv ℝ fun u => ρ u f) 0 u v + (π * I * (om u v : ℂ)) • f := by
  have hd2 : Differentiable ℝ (fderiv ℝ fun u => ρ u f) :=
    (contDiff_fderiv hf).differentiable (by simp)
  have h1 := hasDerivAt_dH u (sm_dH h hf v)
  have hA : HasDerivAt (fun t : ℝ => fderiv ℝ (fun u => ρ u f) (0 + t • u) v)
      (fderiv ℝ (fderiv ℝ fun u => ρ u f) 0 u v) 0 := by
    have hl := (hasDerivAt_line hd2 0 u).clm_apply (hasDerivAt_const (0 : ℝ) v)
    simpa using hl
  have hB := (hasDerivAt_lin (om u v)).smul (hasDerivAt_dH u hf)
  have h2 := hA.add hB
  have e : (fun t : ℝ => ρ (t • u) (dH ρ v f)) = fun t : ℝ =>
      fderiv ℝ (fun u => ρ u f) (0 + t • u) v + (π * I * ((t * om u v : ℝ) : ℂ)) • ρ (t • u) f := by
    funext t
    rw [heis_dH h hf]
    simp
  rw [e] at h1
  rw [h1.unique h2]
  simp [h.1]

theorem dH_commutator (h0 : ∀ x, om x x = 0) (h : IsHeis (fun x y => om x y) ρ) {f : B} (hf : Sm ρ f) (u v : V) :
    dH ρ u (dH ρ v f) - dH ρ v (dH ρ u f) = (2 * π * I * (om u v : ℂ)) • f := by
  have hf' : ContDiff ℝ ∞ (fun u => ρ u f) := hf
  have hs : IsSymmSndFDerivAt ℝ (fun u => ρ u f) 0 := hf'.contDiffAt.isSymmSndFDerivAt
    (by simpa using (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤)))
  rw [dH_dH h hf u v, dH_dH h hf v u, hs v u, skew h0 u v, add_sub_add_left_eq_sub, ← sub_smul]
  congr 1
  push_cast
  ring

theorem dH_calculus : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (om : V →L[ℝ] V →L[ℝ] ℝ) (ρ : V → B →L[ℂ] B), (∀ x, om x x = 0) → IsHeis (fun x y => om x y) ρ → ∀ f, Sm ρ f → (∀ v, Sm ρ (dH ρ v f)) ∧ (∀ w, Sm ρ (ρ w f)) ∧ (∀ w y, fderiv ℝ (fun u => ρ u f) w y = ρ w (dH ρ y f) - (π * I * (om w y : ℂ)) • ρ w f) ∧ (∀ v w, dH ρ v (ρ w f) = ρ w (dH ρ v f) + (2 * π * I * (om v w : ℂ)) • ρ w f) ∧ ∀ u v, dH ρ u (dH ρ v f) - dH ρ v (dH ρ u f) = (2 * π * I * (om u v : ℂ)) • f := by
  intro V _ _ B _ _ om ρ h0 h f hf
  exact ⟨fun v => sm_dH h hf v, fun w => sm_heis h hf w,
    fun w y => eq_sub_of_add_eq (heis_dH h hf w y).symm, fun v w => dH_heis h0 h hf v w,
    fun u v => dH_commutator h0 h hf u v⟩

end GlobalTheory.Mem.Lift.DCalc
end

section

open NumberField IsDedekindDomain

namespace GlobalTheory.TamePowTeich

variable {Ω : Type} [Field Ω]

theorem valuation_pow_sub_lt (A : ValuationSubring Ω) {x y : Ω} (hx : A.valuation x = 1) (hy : A.valuation y = 1)
    (hxy : A.valuation (x - y) < 1) : ∀ k : ℕ, A.valuation (x ^ k - y ^ k) < 1 := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h : x ^ (k + 1) - y ^ (k + 1) = x * (x ^ k - y ^ k) + (x - y) * y ^ k := by ring
    rw [h]
    apply Valuation.map_add_lt
    · rw [map_mul, hx, one_mul]; exact ih
    · rw [map_mul, map_pow, hy, one_pow, mul_one]; exact hxy

theorem valuation_zpow_sub_lt (A : ValuationSubring Ω) {x y : Ω} (hx : A.valuation x = 1) (hy : A.valuation y = 1)
    (hxy : A.valuation (x - y) < 1) (e : ℤ) : A.valuation (x ^ e - y ^ e) < 1 := by
  cases e with
  | ofNat k => simpa using valuation_pow_sub_lt A hx hy hxy k
  | negSucc k =>
    simp only [zpow_negSucc]
    have hxk : A.valuation (x ^ (k + 1)) = 1 := by rw [map_pow, hx, one_pow]
    have hyk : A.valuation (y ^ (k + 1)) = 1 := by rw [map_pow, hy, one_pow]
    have hx0 : x ^ (k + 1) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hxk; exact zero_ne_one hxk
    have hy0 : y ^ (k + 1) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hyk; exact zero_ne_one hyk
    rw [inv_sub_inv hx0 hy0, map_div₀, map_mul, hxk, hyk, mul_one, div_one, Valuation.map_sub_swap]
    exact valuation_pow_sub_lt A hx hy hxy (k + 1)

end GlobalTheory.TamePowTeich

open GlobalTheory.TamePowTeich in
theorem GlobalTheory.TamePowTeich.exists_zeta_pow_close : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    (P : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (ζ : Ω),
    Formalism.ConjugateSelfDual.IsPlaceOver A P → IsPrimitiveRoot ζ (Formalism.ConjugateSelfDual.normV P - 1) → ∀ (u : 𝓞 E) (e : ℤ), u ∉ P.asIdeal →
    ∃ a : ℕ, A.valuation (ζ ^ a - (algebraMap E Ω (u : E)) ^ e) < 1 := by
  intro E Ω _ _ _ _ P A ζ hA hζ u e hu
  classical
  set n := Formalism.ConjugateSelfDual.normV P - 1 with hn_def
  letI : Field (𝓞 E ⧸ P.asIdeal) := @Ideal.Quotient.field _ _ P.asIdeal P.isMaximal
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  letI : Fintype (𝓞 E ⧸ P.asIdeal) := Fintype.ofFinite _
  have hcard : Formalism.ConjugateSelfDual.normV P = Fintype.card (𝓞 E ⧸ P.asIdeal) := by
    show Nat.card _ = _
    exact Nat.card_eq_fintype_card
  have hn : 0 < n := by
    have : 1 < Fintype.card (𝓞 E ⧸ P.asIdeal) := Fintype.one_lt_card
    omega

  have hmem : u ^ n - 1 ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero, hn_def, hcard]
    apply FiniteField.pow_card_sub_one_eq_one
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  set U : Ω := algebraMap E Ω (u : E) with hU
  have hUn : A.valuation (U ^ n - 1) < 1 := by
    have := (hA (u ^ n - 1)).2 hmem
    simpa [hU] using this
  have hUint : U ∈ A := by
    apply ReciprocityTheory.Gal.mem_of_isIntegral_int
    exact (u.isIntegral_coe).algebraMap
  have hU1 : A.valuation U = 1 := by
    apply le_antisymm ((A.valuation_le_one_iff U).2 hUint)
    rw [← not_lt]
    intro h
    exact hu ((hA u).1 h)
  have hζ1 : A.valuation ζ = 1 :=
    ReciprocityTheory.Gal.valuation_eq_one_of_pow_eq_one A hn.ne' hζ.pow_eq_one

  have hprod : U ^ n - 1 = ∏ μ ∈ Polynomial.nthRootsFinset n (1 : Ω), (U - μ) := by
    have := congrArg (Polynomial.eval U) (Polynomial.X_pow_sub_one_eq_prod hn hζ)
    simpa [Polynomial.eval_prod] using this
  have hex : ∃ μ ∈ Polynomial.nthRootsFinset n (1 : Ω), A.valuation (U - μ) < 1 := by
    by_contra hcon
    push_neg at hcon
    have : 1 ≤ A.valuation (U ^ n - 1) := by
      rw [hprod, map_prod]
      exact Finset.one_le_prod' hcon
    exact absurd hUn (not_lt.2 this)
  obtain ⟨μ, hμ, hμU⟩ := hex
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨b, -, hb⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hn 1).1 hμ)
  have hb1 : A.valuation (ζ ^ b) = 1 := by rw [map_pow, hζ1, one_pow]
  have hclose : A.valuation (ζ ^ b - U) < 1 := by
    rw [Valuation.map_sub_swap, hb]; exact hμU
  have key := valuation_zpow_sub_lt A hb1 hU1 hclose e

  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn.ne'
  refine ⟨((b * e) % (n : ℤ)).toNat, ?_⟩
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnonneg : 0 ≤ (b * e) % (n : ℤ) := Int.emod_nonneg _ hnz
  have hpow : (ζ ^ b) ^ e = ζ ^ ((b * e) % (n : ℤ)).toNat := by
    have h1 : ζ ^ ((b * e) % (n : ℤ)).toNat = ζ ^ ((b * e) % (n : ℤ)) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg hnonneg]
    rw [h1, ← zpow_natCast ζ b, ← zpow_mul]
    conv_lhs => rw [← Int.emod_add_mul_ediv ((b : ℤ) * e) n]
    rw [zpow_add₀ hζ0, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow, mul_one]
  rw [← hpow]
  exact key
end

section

noncomputable section

namespace GlobalTheory.ResidueFieldAlgClosed

open Polynomial

theorem isAlgClosed_residueField {Ω : Type} [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω) :
    IsAlgClosed (IsLocalRing.ResidueField A) := by
  refine IsAlgClosed.of_exists_root _ fun p hmon hirr => ?_
  have hlift : p ∈ Polynomial.lifts (IsLocalRing.residue A) :=
    Polynomial.map_surjective _ IsLocalRing.residue_surjective p
  obtain ⟨P, hPmap, hPdeg, hPmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hmon
  have hinj : Function.Injective (algebraMap A Ω) := IsFractionRing.injective A Ω
  have hdeg : (P.map (algebraMap A Ω)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective hinj, hPdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root _ hdeg
  have hint : IsIntegral A α := ⟨P, hPmon, by rw [← Polynomial.eval_map]; exact hα⟩
  obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have h0 : P.eval a = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map]
    exact hα
  refine ⟨IsLocalRing.residue A a, ?_⟩
  rw [← hPmap, Polynomial.eval_map, Polynomial.eval₂_hom, h0, map_zero]

theorem isAlgebraic_residueField {Ω : Type} [Field Ω] [CharZero Ω] (A : ValuationSubring Ω)
    (hΩ : ∀ y : Ω, IsAlgebraic ℤ y) (g : ℕ) [Fact g.Prime] [Algebra (ZMod g) (IsLocalRing.ResidueField A)] :
    Algebra.IsAlgebraic (ZMod g) (IsLocalRing.ResidueField A) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨p, hp0, hpa⟩ := hΩ (a : Ω)
  have hc : (p.content : Ω) ≠ 0 := Int.cast_ne_zero.mpr (mt Polynomial.content_eq_zero_iff.mp hp0)
  have hqa : Polynomial.aeval (a : Ω) p.primPart = 0 := by
    rw [Polynomial.eq_C_content_mul_primPart p, map_mul, Polynomial.aeval_C] at hpa
    exact (mul_eq_zero.mp hpa).resolve_left (by simpa using hc)
  have hA0 : Polynomial.aeval a p.primPart = 0 := by
    apply IsFractionRing.injective A Ω
    rw [map_zero]
    calc algebraMap A Ω (Polynomial.aeval a p.primPart)
        = Polynomial.aeval (algebraMap A Ω a) p.primPart :=
          (Polynomial.aeval_algHom_apply (algebraMap A Ω).toIntAlgHom a p.primPart).symm
      _ = 0 := hqa
  have hqg : p.primPart.map (Int.castRingHom (ZMod g)) ≠ 0 := by
    intro h
    have hdvd : Polynomial.C (g : ℤ) ∣ p.primPart := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro i
      have hi := congrArg (fun r => _root_.AddMonoidAlgebra.coeff (M := ℕ) r i) h
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, eq_intCast] at hi
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ g).mp hi
    have hu := Polynomial.isPrimitive_primPart p _ hdvd
    rw [Int.isUnit_iff] at hu
    have h2 := (Fact.out : g.Prime).two_le
    omega
  refine ⟨p.primPart.map (Int.castRingHom (ZMod g)), hqg, ?_⟩
  have h2 := Polynomial.aeval_algHom_apply (IsLocalRing.residue A).toIntAlgHom a p.primPart
  rw [hA0, map_zero] at h2
  rw [Polynomial.aeval_def, Polynomial.eval₂_map]
  rw [Polynomial.aeval_def] at h2
  have hφ : (algebraMap (ZMod g) (IsLocalRing.ResidueField A)).comp (Int.castRingHom (ZMod g)) =
      algebraMap ℤ (IsLocalRing.ResidueField A) := RingHom.ext_int _ _
  rw [hφ]
  exact h2

theorem residueField_equiv (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hA : Formalism.ConjugateSelfDual.IsPlaceOver A v) (g : ℕ) [Fact (Nat.Prime g)]
    (hg : (g : NumberField.RingOfIntegers E) ∈ v.asIdeal) :
    Nonempty (IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) := by
  classical
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
  have hΩ : ∀ y : Ω, IsAlgebraic ℤ y := fun y =>
    (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).mpr (Algebra.IsAlgebraic.isAlgebraic y)
  have hg0 : (g : IsLocalRing.ResidueField A) = 0 := by
    have h1 := (hA (g : NumberField.RingOfIntegers E)).mpr hg
    have h2 : A.valuation ((g : A) : Ω) < 1 := by simpa using h1
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact (A.valuation_lt_one_iff (g : A)).mpr h2
  have : CharP (IsLocalRing.ResidueField A) g := (CharP.charP_iff_prime_eq_zero Fact.out).mpr hg0
  let _ : Algebra (ZMod g) (IsLocalRing.ResidueField A) := ZMod.algebra _ g
  have _ := isAlgClosed_residueField A
  have _ := isAlgebraic_residueField A hΩ g
  have : IsAlgClosure (ZMod g) (IsLocalRing.ResidueField A) := ⟨inferInstance, inferInstance⟩
  exact ⟨(IsAlgClosure.equiv (ZMod g) (IsLocalRing.ResidueField A) (Formalism.CyclotomicNorms.Fbar g)).toRingEquiv⟩

end GlobalTheory.ResidueFieldAlgClosed

end
end

section

noncomputable section

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

namespace GlobalTheory.UpqTopology

variable {P Q : ℕ}

theorem jpq_sq : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem left_inv {u : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ}
    (h : uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q) : Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q * u = 1 := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, h, jpq_sq]

theorem mat_unitary (b : UpqT P Q) : (UpqT.mat b)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat b = Formalism.UG.Jpq P Q := b.2

theorem continuous_mat : Continuous (UpqT.mat (P := P) (Q := Q)) :=
  Units.continuous_val.comp continuous_subtype_val

theorem range_mat : Set.range (UpqT.mat (P := P) (Q := Q)) =
    {u | uᴴ * Formalism.UG.Jpq P Q * u = Formalism.UG.Jpq P Q} := by
  ext u
  constructor
  · rintro ⟨b, rfl⟩
    exact mat_unitary b
  · intro h
    exact ⟨(⟨⟨u, Formalism.UG.Jpq P Q * uᴴ * Formalism.UG.Jpq P Q, mul_eq_one_comm.1 (left_inv h), left_inv h⟩, h⟩ :
      Formalism.UG.Upq P Q), rfl⟩

theorem isInducing_mat : IsInducing (UpqT.mat (P := P) (Q := Q)) := by
  let f : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ →
      Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ × (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ᵐᵒᵖ :=
    fun g => (g, MulOpposite.op (Formalism.UG.Jpq P Q * gᴴ * Formalism.UG.Jpq P Q))
  have hf : Continuous f :=
    continuous_id.prodMk (MulOpposite.continuous_op.comp
      ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const))
  have hcomp : f ∘ UpqT.mat =
      Units.embedProduct _ ∘ (Subtype.val : Formalism.UG.Upq P Q → GL (Fin P ⊕ Fin Q) ℂ) := by
    funext g
    refine Prod.ext rfl (congrArg MulOpposite.op ?_)
    exact (Units.inv_eq_of_mul_eq_one_left (left_inv (mat_unitary g))).symm
  refine IsInducing.of_comp continuous_mat hf ?_
  rw [hcomp]
  exact Units.isEmbedding_embedProduct.isInducing.comp IsInducing.subtypeVal

theorem isClosedEmbedding_mat : IsClosedEmbedding (UpqT.mat (P := P) (Q := Q)) := by
  refine ⟨⟨isInducing_mat, fun _ _ h => Subtype.ext (Units.ext h)⟩, ?_⟩
  rw [range_mat]
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
    continuous_id) continuous_const

theorem upq_lcsc : ∀ P Q : ℕ, IsTopologicalGroup (UpqT P Q) ∧ T2Space (UpqT P Q) ∧
    LocallyCompactSpace (UpqT P Q) ∧ SecondCountableTopology (UpqT P Q) ∧ BorelSpace (UpqT P Q) ∧
    Topology.IsClosedEmbedding (UpqT.mat : UpqT P Q → Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := by
  intro P Q
  have : LocallyCompactSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (LocallyCompactSpace ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  have : SecondCountableTopology (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :=
    inferInstanceAs (SecondCountableTopology ((Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ))
  exact ⟨inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q)), isClosedEmbedding_mat.isEmbedding.t2Space,
    isClosedEmbedding_mat.locallyCompactSpace, isClosedEmbedding_mat.isEmbedding.secondCountableTopology,
    ⟨rfl⟩, isClosedEmbedding_mat⟩

end GlobalTheory.UpqTopology
end
end

section

open CategoryTheory Polynomial GlobalTheory.NormalDescent

theorem _root_.GlobalTheory.T.charpoly_dvd_pow_finrank_of_aeval_eq_zero : ∀ {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : Module.End K V) (G : K[X]), aeval f G = 0 → f.charpoly ∣ G ^ Module.finrank K V := by
  first | exact @GlobalTheory.CharpolyDvd.main | exact GlobalTheory.CharpolyDvd.main | (intros; apply GlobalTheory.CharpolyDvd.main <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_linearIndependent_rat_basis_adapted_subspace : ∀ (g r : ℕ) (I L : Submodule ℚ (Fin r → ℚ)), I ≤ L → Module.finrank ℚ L = g → ∃ rk : ℕ, rk ≤ g ∧ ∃ ε : Fin g → Fin r → ℚ, LinearIndependent ℚ ε ∧ (∀ i, ε i ∈ L) ∧ (∀ i : Fin g, i.val < rk → ε i ∈ I) ∧ ∀ x ∈ I, x ∈ Submodule.span ℚ (ε '' {i | i.val < rk}) := by
  first | exact @GlobalTheory.adapted_basis_extension | exact GlobalTheory.adapted_basis_extension | (intros; apply GlobalTheory.adapted_basis_extension <;> assumption)
end
