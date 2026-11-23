module

public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle042
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle744
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle977
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1318
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
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
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle034
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem eab_mul_eab {p q : ℕ} (a b c d : Ix p q) :
    Eab a b * Eab c d = if b = c then Eab a d else 0 := by
  unfold Eab
  split_ifs with h
  · subst h; rw [Matrix.single_mul_single_same, mul_one]
  · exact Matrix.single_mul_single_of_ne _ _ _ _ h _

theorem mat_eq_sum_eab {p q : ℕ} (X : Mat p q) : X = ∑ a, ∑ b, X a b • Eab a b := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  unfold Eab; rw [Matrix.smul_single, smul_eq_mul, mul_one]

theorem act_eq_sum_units {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (X : Mat p q) (v : V) :
    act X v = ∑ a, ∑ b, X a b • units act a b v := by
  conv_lhs => rw [mat_eq_sum_eab X]

  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, units]

theorem sameBlock_iff_isLeft {p q : ℕ} (a b : Ix p q) : sameBlock a b ↔ a.isLeft = b.isLeft := by
  cases a <;> cases b <;> simp [sameBlock]

theorem lie_units_stab : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V),
    (IsLieAct act → IsGl (units act)) ∧
    (∀ N : Submodule ℂ V, (∀ a b : Ix p q, a.isLeft = b.isLeft → ∀ u ∈ N, units act a b u ∈ N) ↔ KStable act N) ∧
    ∀ N : Submodule ℂ V, (∀ a b, ∀ u ∈ N, units act a b u ∈ N) → Stab act N := by
  intro p q V _ _ act
  refine ⟨fun hL a b c d => ?_, fun N => ⟨fun h X hX w hw => ?_, fun h a b hab u hu => ?_⟩, fun N h Z y hy => ?_⟩
  · simp only [units]
    rw [← hL, eab_mul_eab, eab_mul_eab, map_sub]
    congr 1
    · split_ifs <;> simp
    · split_ifs <;> simp
  · rw [act_eq_sum_units]
    refine N.sum_mem fun a _ => N.sum_mem fun b _ => ?_
    by_cases hab : a.isLeft = b.isLeft
    · exact N.smul_mem _ (h a b hab w hw)
    · rw [hX a b (fun hs => hab ((sameBlock_iff_isLeft a b).1 hs)), zero_smul]; exact N.zero_mem
  · refine h (Eab a b) (fun c d hcd => ?_) u hu
    unfold Eab
    rw [Matrix.single_apply]
    split_ifs with h'
    · obtain ⟨rfl, rfl⟩ := h'; exact absurd ((sameBlock_iff_isLeft _ _).2 hab) hcd
    · rfl
  · rw [act_eq_sum_units]
    exact N.sum_mem fun a _ => N.sum_mem fun b _ => N.smul_mem _ (h a b y hy)

end GlobalTheory.HoweR
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem cas_diag_unitOn (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M) (U : Submodule ℂ M) (hU : UnitOn s F U) :
    (∀ (c : ℂ), ∀ v ∈ U, v ≠ 0 → cas s F v = c • v → c.im = 0 ∧ 0 ≤ c.re) ∧
      (U ≠ ⊥ → ∃ (ω : ℝ) (v : M), v ∈ U ∧ v ≠ 0 ∧ cas s F v = (ω : ℂ) • v) := by
  obtain ⟨hfin, hst, ip, hherm, hpos, hadj⟩ := hU
  have hw : ∀ w ∈ U, (ip w w).im = 0 ∧ 0 ≤ (ip w w).re := by
    intro w hw
    constructor
    · have h := congrArg Complex.im (hherm w hw w hw)
      simp at h
      linarith
    · by_cases h0 : w = 0
      · simp [h0]
      · exact le_of_lt (hpos w hw h0)
  have key : ∀ v ∈ U, ip v (cas s F v) = ∑ a, ∑ b, if s a = s b then ip (F b a v) (F b a v) else 0 := by
    intro v hv

    simp only [cas, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    split_ifs with h
    · rw [Module.End.mul_apply]
      exact (hadj b a h.symm v hv (F b a v) (hst b a h.symm v hv)).symm
    · simp
  have hS : ∀ v ∈ U, (ip v (cas s F v)).im = 0 ∧ 0 ≤ (ip v (cas s F v)).re := by
    intro v hv
    rw [key v hv, Complex.im_sum, Complex.re_sum]
    constructor
    · refine Finset.sum_eq_zero fun a _ => ?_
      rw [Complex.im_sum]
      refine Finset.sum_eq_zero fun b _ => ?_
      split_ifs with h
      · exact (hw _ (hst b a h.symm v hv)).1
      · simp
    · refine Finset.sum_nonneg fun a _ => ?_
      rw [Complex.re_sum]
      refine Finset.sum_nonneg fun b _ => ?_
      split_ifs with h
      · exact (hw _ (hst b a h.symm v hv)).2
      · simp
  have first : ∀ (c : ℂ), ∀ v ∈ U, v ≠ 0 → cas s F v = c • v → c.im = 0 ∧ 0 ≤ c.re := by
    intro c v hv h0 hc
    have e := hS v hv
    rw [hc, map_smul, smul_eq_mul, Complex.mul_im, Complex.mul_re] at e
    have r0 := (hw v hv).1
    have rp := hpos v hv h0
    rw [r0] at e
    simp only [mul_zero, zero_add, sub_zero] at e
    obtain ⟨e1, e2⟩ := e
    refine ⟨?_, ?_⟩
    · rcases mul_eq_zero.mp e1 with h | h
      · exact h
      · exact absurd h (ne_of_gt rp)
    · by_contra hneg
      push_neg at hneg
      nlinarith
  refine ⟨first, fun hne => ?_⟩
  have hcU : ∀ x ∈ U, cas s F x ∈ U := by
    intro x hx
    simp only [cas, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
    split_ifs with h
    · rw [Module.End.mul_apply]
      exact hst a b h _ (hst b a h.symm x hx)
    · simp
  haveI : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hne
  haveI : FiniteDimensional ℂ U := hfin
  let g : Module.End ℂ U := (cas s F).restrict hcU
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue g
  obtain ⟨w, hw'⟩ := hc.exists_hasEigenvector
  have hgw : g w = c • w := Module.End.mem_eigenspace_iff.mp hw'.1
  have hw0 : (w : M) ≠ 0 := fun h => hw'.2 (Subtype.ext h)
  have hcw : cas s F (w : M) = c • (w : M) := by
    have := congrArg Subtype.val hgw
    simpa [g] using this
  have hc' := first c w w.2 hw0 hcw
  refine ⟨c.re, w, w.2, hw0, ?_⟩
  rw [hcw]
  congr 1
  apply Complex.ext <;> simp [hc'.1]

end GlobalTheory.HoweR
end

section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS.FlatDiag

theorem norm_diagChar_flatWt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (τ : Psi H) (t : Ix Dw → (CAt σ)ˣ), ‖GlobalTheory.CompHS.diagChar (exOf Dw (flatWt Dw τ) 0) t‖ = (∏ j : Fin (Dw.mult (conjEmb τ.1)), ‖toC ((t (some ⟨conjEmb τ.1, j⟩) : CAt σ))‖) / ∏ i : Fin (Dw.mult τ.1), ‖toC ((t (some ⟨τ.1, i⟩) : CAt σ))‖ := by
  classical
  intro E _ _ _ H Dw l c σ τ t
  set e := exOf Dw (flatWt Dw τ) 0 with he_def
  have hne : τ.1 ≠ conjEmb τ.1 := fun h => conj_not_mem τ (h ▸ τ.2)
  have hE : ∀ (ρ : E →+* ℂ) (i : Fin (Dw.mult ρ)),
      e (some ⟨ρ, i⟩) = if ρ = τ.1 then -1 else if ρ = conjEmb τ.1 then 1 else 0 := by
    intro ρ i
    obtain ⟨n, hi⟩ := i
    simp only [he_def, exOf, exZ, wtOf, flatWt, parWt, Datum.mult] at hi ⊢
    by_cases h : ρ (H.rt : E) = H.rt0
    · rw [if_pos h] at hi
      rw [dite_eq_left h, dite_eq_left hi]
      have h2 : ρ ≠ conjEmb τ.1 := fun e => conj_not_mem τ (e ▸ h)
      by_cases h1 : ρ = τ.1
      · subst h1
        simp
      · have h3 : (⟨ρ, h⟩ : Psi H) ≠ τ := fun e => h1 (congrArg Subtype.val e)
        simp [h1, h2, h3]
    · rw [if_neg h] at hi
      rw [dite_eq_right h]
      have h1 : ρ ≠ τ.1 := fun e => h (e ▸ τ.2)
      by_cases h' : conjEmb ρ (H.rt : E) = H.rt0
      · rw [dite_eq_left h', dite_eq_left hi]
        by_cases h2 : ρ = conjEmb τ.1
        · have h3 : (⟨conjEmb ρ, h'⟩ : Psi H) = τ := Subtype.ext (show conjEmb ρ = τ.1 by rw [h2, _root_.GlobalTheory.AllWt.conjEmb_conjEmb])
          rw [if_pos h3, if_neg h1, if_pos h2]
          norm_num
        · have h3 : (⟨conjEmb ρ, h'⟩ : Psi H) ≠ τ := fun e => h2 (by
            rw [← congrArg Subtype.val e, _root_.GlobalTheory.AllWt.conjEmb_conjEmb])
          rw [if_neg h3, if_neg h1, if_neg h2]
          norm_num
      · rw [dite_eq_right h']
        have h2 : ρ ≠ conjEmb τ.1 := fun e => h' (by rw [e, _root_.GlobalTheory.AllWt.conjEmb_conjEmb]; exact τ.2)
        simp [h1, h2]
  have e0 : e none = 0 := by simp [he_def, exOf, exZ, wtOf_snd]
  let f : (CAt σ)ˣ →* ℂˣ := Units.map (MonoidHom.id ℂ)
  have hf : ∀ u : (CAt σ)ˣ, ((f u : ℂˣ) : ℂ) = toC (u : CAt σ) := fun _ => rfl
  have e₁ : GlobalTheory.CompHS.diagChar e t = ((∏ ix, f (t ix) ^ e ix : ℂˣ) : ℂ) := by
    have : (∏ ix, f (t ix) ^ e ix) = f (∏ ix, t ix ^ e ix) := by simp only [map_prod, map_zpow]
    rw [this, hf]
    rfl
  let g : (E →+* ℂ) → ℝ := fun ρ => ∏ i : Fin (Dw.mult ρ), ‖toC ((t (some ⟨ρ, i⟩) : CAt σ))‖ ^ e (some ⟨ρ, i⟩)
  have e₂ : ‖GlobalTheory.CompHS.diagChar e t‖ = ∏ ρ, g ρ := by
    rw [e₁, Units.coe_prod, norm_prod, Fintype.prod_option, e0, zpow_zero, Units.val_one, norm_one, one_mul,
      Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun ρ _ => Finset.prod_congr rfl fun i _ => ?_
    rw [Units.val_zpow_eq_zpow_val, norm_zpow, hf]
  have e₃ : ∏ ρ, g ρ = g τ.1 * g (conjEmb τ.1) := by
    rw [← Finset.prod_pair hne]
    refine (Finset.prod_subset (Finset.subset_univ _) fun ρ _ hρ => ?_).symm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hρ
    exact Finset.prod_eq_one fun i _ => by rw [hE, if_neg hρ.1, if_neg hρ.2, zpow_zero]
  have gτ : g τ.1 = (∏ i : Fin (Dw.mult τ.1), ‖toC ((t (some ⟨τ.1, i⟩) : CAt σ))‖)⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [hE, if_pos rfl, zpow_neg_one]
  have gc : g (conjEmb τ.1) = ∏ j : Fin (Dw.mult (conjEmb τ.1)), ‖toC ((t (some ⟨conjEmb τ.1, j⟩) : CAt σ))‖ :=
    Finset.prod_congr rfl fun i _ => by rw [hE, if_neg hne.symm, if_pos rfl, zpow_one]
  rw [e₂, e₃, gτ, gc, div_eq_mul_inv, mul_comm]

end GlobalTheory.CompHS.FlatDiag
end
end

section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.SecondQuad

section Ring

variable {A : Type} [Ring A] {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  (u l : I × J → A)

theorem left_expand (hlu : ∀ i j, l i * u j = u j * l i + if i = j then 1 else 0) (c e : J) :
    ∑ d, (∑ a, u (a, c) * l (a, d)) * (∑ b, u (b, d) * l (b, e)) =
      ∑ d, ∑ a, ∑ b, u (a, c) * u (b, d) * (l (a, d) * l (b, e)) +
        Fintype.card J • ∑ a, u (a, c) * l (a, e) := by
  have h1 : ∀ d a b, u (a, c) * l (a, d) * (u (b, d) * l (b, e)) =
      u (a, c) * u (b, d) * (l (a, d) * l (b, e)) + if a = b then u (a, c) * l (a, e) else 0 := by
    intro d a b
    have h := hlu (a, d) (b, d)
    simp only [Prod.mk.injEq, and_true] at h
    have : u (a, c) * l (a, d) * (u (b, d) * l (b, e)) = u (a, c) * (l (a, d) * u (b, d)) * l (b, e) := by
      simp only [mul_assoc]
    rw [this, h]
    by_cases hab : a = b
    · subst hab; simp [mul_add, add_mul, mul_assoc]
    · simp [hab, mul_add, add_mul, mul_assoc]
  simp only [Finset.sum_mul_sum, h1, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ]

theorem right_expand (hlu : ∀ i j, l i * u j = u j * l i + if i = j then 1 else 0) (c e : J) :
    ∑ a, ∑ b, (∑ d, u (b, d) * l (a, d)) * (u (a, c) * l (b, e)) =
      ∑ a, ∑ b, ∑ d, u (b, d) * u (a, c) * (l (a, d) * l (b, e)) +
        Fintype.card I • ∑ b, u (b, c) * l (b, e) := by
  have h1 : ∀ a b d, u (b, d) * l (a, d) * (u (a, c) * l (b, e)) =
      u (b, d) * u (a, c) * (l (a, d) * l (b, e)) + if d = c then u (b, c) * l (b, e) else 0 := by
    intro a b d
    have h := hlu (a, d) (a, c)
    simp only [Prod.mk.injEq, true_and] at h
    have : u (b, d) * l (a, d) * (u (a, c) * l (b, e)) = u (b, d) * (l (a, d) * u (a, c)) * l (b, e) := by
      simp only [mul_assoc]
    rw [this, h]
    by_cases hdc : d = c
    · subst hdc; simp [mul_add, add_mul, mul_assoc]
    · simp [hdc, mul_add, add_mul, mul_assoc]
  simp only [Finset.sum_mul, h1, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const, Finset.card_univ]

theorem key (hlu : ∀ i j, l i * u j = u j * l i + if i = j then 1 else 0)
    (huu : ∀ i j, u i * u j = u j * u i) (c e : J) :
    ∑ d, (∑ a, u (a, c) * l (a, d)) * (∑ b, u (b, d) * l (b, e)) + Fintype.card I • ∑ a, u (a, c) * l (a, e) =
      ∑ a, ∑ b, (∑ d, u (b, d) * l (a, d)) * (u (a, c) * l (b, e)) +
        Fintype.card J • ∑ a, u (a, c) * l (a, e) := by
  rw [left_expand u l hlu, right_expand u l hlu]
  have hT : ∑ d, ∑ a, ∑ b, u (a, c) * u (b, d) * (l (a, d) * l (b, e)) =
      ∑ a, ∑ b, ∑ d, u (b, d) * u (a, c) * (l (a, d) * l (b, e)) := by
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun d _ => by rw [huu]
  rw [hT]
  abel

end Ring

variable {P Q R S : ℕ}

theorem raiB_comm (l m : Ln P Q R S) : raiB l * raiB m = raiB m * raiB l := by
  by_cases hlm : l = m
  · rw [hlm]
  refine LinearMap.ext fun f => ?_
  cases hl : linePos l <;> cases hm : linePos m <;>
    simp [raiB, hl, hm, MvPolynomial.pderiv_X, Pi.single_apply, hlm, Ne.symm hlm,
      GlobalTheory.FockCasimir.pderiv_pderiv_comm l m, mul_left_comm]

theorem fockSecondAction_matrixUnit_eq (c d : Ix R S) :
    fockAct2 P Q R S (Eab c d) = ∑ a, raiB (a, c) * lowB (a, d) +
      if c = d then ((Fintype.card (Ix P Q) : ℂ) / 2) • (1 : Module.End ℂ (Pol P Q R S)) else 0 := by
  rw [fockAct2_Eab]
  simp only [omE, Finset.sum_add_distrib, Prod.mk.injEq, true_and]
  by_cases hcd : c = d
  · simp [hcd, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv, mul_comm]
  · simp [hcd]

theorem fockFirstAction_matrixUnit_eq (b a : Ix P Q) :
    fockAct1 P Q R S (Eab b a) = ∑ d, raiB (b, d) * lowB (a, d) +
      if b = a then ((Fintype.card (Ix R S) : ℂ) / 2) • (1 : Module.End ℂ (Pol P Q R S)) else 0 := by
  rw [fockAct1_Eab]
  simp only [omE, Finset.sum_add_distrib, Prod.mk.injEq, and_true]
  by_cases hba : b = a
  · simp [hba, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, div_eq_mul_inv, mul_comm]
  · simp [hba]

theorem trace_Eab (b a : Ix P Q) : (Eab b a).trace = if b = a then 1 else 0 := by
  by_cases h : b = a
  · subst h; simp [Eab, Matrix.trace, Matrix.single_apply]
  · simp [Eab, Matrix.trace, Matrix.single_apply, h]

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A] {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem sq_shift (X : J → J → A) (k : ℂ) (c e : J) :
    ∑ d, (X c d + if c = d then k • (1 : A) else 0) * (X d e + if d = e then k • (1 : A) else 0) =
      ∑ d, X c d * X d e + (2 * k) • X c e + if c = e then (k * k) • (1 : A) else 0 := by
  simp only [mul_add, add_mul, Finset.sum_add_distrib, ite_mul, mul_ite, zero_mul, mul_zero,
    smul_mul_assoc, one_mul, mul_smul_comm, mul_one, Finset.sum_ite_eq, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, smul_smul]
  by_cases hce : c = e
  · subst hce; simp only [if_true]; module
  · simp only [hce, if_false]; module

theorem rhs_shift (E : I → I → A) (Y : I → I → A) (m x : ℂ) :
    ∑ a, ∑ b, (E b a + (if b = a then m • (1 : A) else 0) - (x * if b = a then 1 else 0) • (1 : A)) * Y a b =
      ∑ a, ∑ b, E b a * Y a b + (m - x) • ∑ a, Y a a := by
  have : ∀ a b, (E b a + (if b = a then m • (1 : A) else 0) - (x * if b = a then 1 else 0) • (1 : A)) * Y a b =
      E b a * Y a b + if b = a then (m - x) • Y a b else 0 := by
    intro a b
    by_cases h : b = a
    · simp only [h, if_true, mul_one, sub_mul, add_mul, smul_mul_assoc, one_mul, sub_smul]; abel
    · simp [h]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.smul_sum]

end Alg

variable {P Q R S : ℕ}

theorem qop_eq (x : ℂ) (c e : Ix R S) :
    qop (units (fockAct2 P Q R S)) (x + (Fintype.card (Ix R S) : ℂ) / 2)
        ((Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 - (x + (Fintype.card (Ix R S) : ℂ) / 2) * ((Fintype.card (Ix P Q) : ℂ) / 2)) c e =
      ∑ a, ∑ b, (fockAct1 P Q R S (Eab b a) - (x * (Eab b a).trace) • (1 : Module.End ℂ (Pol P Q R S))) *
        (raiB (a, c) * lowB (b, e)) := by
  have hk := key (fun i : Ln P Q R S => raiB i) (fun i => lowB i) GlobalTheory.FockCasimir.lowB_mul_raiB raiB_comm c e
  simp only [← Nat.cast_smul_eq_nsmul ℂ] at hk
  simp only [qop, units, fockSecondAction_matrixUnit_eq, fockFirstAction_matrixUnit_eq, trace_Eab]
  have hs := sq_shift (A := Module.End ℂ (Pol P Q R S)) (fun c d => ∑ a, raiB (a, c) * lowB (a, d))
    ((Fintype.card (Ix P Q) : ℂ) / 2) c e
  have hr := rhs_shift (A := Module.End ℂ (Pol P Q R S)) (fun b a => ∑ d, raiB (b, d) * lowB (a, d))
    (fun a b => raiB (a, c) * lowB (b, e)) ((Fintype.card (Ix R S) : ℂ) / 2) x
  rw [hs, hr]
  by_cases hce : c = e
  · subst hce; simp only [if_true]
    linear_combination (norm := module) hk
  · simp only [hce, if_false]
    linear_combination (norm := module) hk

theorem qop_mem_coinv (P Q R S : ℕ) (x : ℂ) :
    ∃ α β : ℂ, ∀ a b f, qop (units (fockAct2 P Q R S)) α β a b f ∈ coinv P Q R S x := by
  refine ⟨x + (Fintype.card (Ix R S) : ℂ) / 2,
    (Fintype.card (Ix P Q) : ℂ) ^ 2 / 4 - (x + (Fintype.card (Ix R S) : ℂ) / 2) * ((Fintype.card (Ix P Q) : ℂ) / 2),
    fun c e f => ?_⟩
  rw [qop_eq x c e, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun a _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun b _ => ?_
  refine Submodule.subset_span ⟨Eab b a, (raiB (a, c) * lowB (b, e)) f, ?_⟩
  simp [Module.End.mul_apply, LinearMap.sub_apply]

end GlobalTheory.HoweR.SecondQuad

end
end

section

noncomputable section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem pcTrace_eq_zero {p q : ℕ} {Z : Mat p q} (hZ : IsPC Z) : Z.trace = 0 := by
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_eq_zero fun a _ => hZ a a ?_
  rcases a with a | a <;> simp [sameBlock]

theorem span_harm2_sup_coinv_eq_univ : ∀ (P Q R S : ℕ) (x : ℂ),
    Submodule.span ℂ (harm2 P Q R S) ⊔ coinv P Q R S x = ⊤ := by
  intro P Q R S x
  refine eq_top_iff.2 fun f _ => ?_
  have hpr : ∀ Z : Mat P Q, IsPC Z → ∀ g, (coinv P Q R S x).mkQ (fockAct1 P Q R S Z g) = 0 := by
    intro Z hZ g
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine Submodule.subset_span ⟨Z, g, ?_⟩
    rw [pcTrace_eq_zero hZ, mul_zero, zero_smul, sub_zero]
  obtain ⟨h, hh, he⟩ := GlobalTheory.FockAlg.HarmLift.exists_harm2_rep P Q R S _ (coinv P Q R S x).mkQ hpr f
  have hd : f - h ∈ coinv P Q R S x := by
    rw [← Submodule.Quotient.eq]; exact he.symm
  have : f = h + (f - h) := by abel
  rw [this]
  exact Submodule.add_mem_sup (Submodule.subset_span hh) hd

end GlobalTheory.HoweR
end
end

section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem _root_.GlobalTheory.T.quadratic_extension_symplectic_coordinates : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ)
    (K : Matrix (Fin d) (Fin d) E), (∀ a, σ (σ a) = a) → Module.finrank F E = 2 → (∀ i j, σ (K j i) = -K i j) → K.det ≠ 0 →
    ∃ p q : (Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) ≃ₗ[AF F] (Fin 2 × Fin d → AF F),
      (∀ a b, q b ⬝ᵥ p a = Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (-∑ j, ∑ l, b j * incM F K j l * cA σ (a l))) ∧
      (∀ a b, q b ⬝ᵥ p a = Algebra.trace (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (∑ j, ∑ l, a j * incM F K j l * cA σ (b l))) ∧
      (∀ a : Fin d → E, ∃ y : Fin 2 × Fin d → F, p (incV F a) = fun k => algebraMap F (AF F) (y k)) ∧
      (∀ a : Fin d → E, ∃ y : Fin 2 × Fin d → F, q (incV F a) = fun k => algebraMap F (AF F) (y k)) := by
  first | exact @GlobalTheory.PairCoords.exists_pair_coords | exact GlobalTheory.PairCoords.exists_pair_coords | (intros; apply GlobalTheory.PairCoords.exists_pair_coords <;> assumption)
end
