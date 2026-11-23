module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Bundle006
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
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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

@[expose] public section

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.framePoint_y_coord_eq :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (Q : Type) [CommRing Q] [Algebra k Q] (ρ : NRep F 3 Q), ρ.IsBar (algebraMap k Q) → ρ.triM = ⊥ → (∀ i j, IsLocallyConstant fun g => ρ.r g i j) → (fun g => ρ.r g 1 0) ∈ F.strY Q := by
  intro l _ k _ _ F C₀ hF Q _ _ ρ hbar htri hlc
  have hd0 : ∀ g : F.G0, ρ.r g 0 0 = algebraMap k Q ((F.Ψ (g : F.Γ) : k)) := by
    intro g
    have h := hbar.1 g 0
    simpa [w] using h
  have hd1 : ∀ g : F.G0, ρ.r g 1 1 = 1 := by
    intro g
    have h := hbar.1 g 1
    simpa [w] using h
  have hd2 : ∀ g : F.G0, ρ.r g 2 2 = algebraMap k Q ((F.Ψ (g : F.Γ) : k))⁻¹ := by
    intro g
    have h := hbar.1 g 2
    simpa [w] using h
  have hup : ∀ (g : F.G0) (i j : Fin 3), i < j → ρ.r g i j = 0 := by
    intro g i j hij
    have h : ρ.r g i j ∈ ρ.triM := by
      apply Ideal.subset_span
      exact ⟨g, i, j, hij, rfl⟩
    rw [htri, Ideal.mem_bot] at h
    exact h
  have h01 := fun g => hup g 0 1 (by decide)
  have h02 := fun g => hup g 0 2 (by decide)
  have h12 := fun g => hup g 1 2 (by decide)
  have hψ0 : ∀ v (s : F.Gv v), ((ρ.ψ v 0 s : Qˣ) : Q) = algebraMap k Q ((F.Ψ (F.loc v s) : k)) := by
    intro v s
    have h := hbar.2 v 0 s
    simpa [w] using h
  have hψ1 : ∀ v (s : F.Gv v), ((ρ.ψ v 1 s : Qˣ) : Q) = 1 := by
    intro v s
    have h := hbar.2 v 1 s
    simpa [w] using h
  have hψ2 : ∀ v (s : F.Gv v), ((ρ.ψ v 2 s : Qˣ) : Q) = algebraMap k Q ((F.Ψ (F.loc v s) : k))⁻¹ := by
    intro v s
    have h := hbar.2 v 2 s
    simpa [w] using h
  refine ⟨hlc 1 0, ?_, ?_, ?_, ?_⟩
  · intro g h
    simp only [map_mul, Matrix.mul_apply, Fin.sum_univ_three, Algebra.smul_def]
    rw [hd0, hd1, h12]
    ring
  · have h := ρ.diag 1 0 (by decide)
    rw [Matrix.sub_apply, sub_eq_zero] at h
    exact h
  · intro v
    obtain ⟨t, ht⟩ := hF.f3 v
    have hne := Units.ne_zero (F.Ψ (F.loc v t))
    have hsq : ((F.Ψ (F.loc v t) : k)) * (F.Ψ (F.loc v t) : k) ≠ 1 := by
      intro h
      apply ht
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, pow_two, h]
    have hf : ((F.Ψ (F.loc v t) : k)) - 1 ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      apply hsq
      rw [h, one_mul]
    have he : ((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹ ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      apply hsq
      calc ((F.Ψ (F.loc v t) : k)) * (F.Ψ (F.loc v t) : k)
          = (F.Ψ (F.loc v t) : k) * ((F.Ψ (F.loc v t) : k))⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hne
    have hl : ∀ s, ((F.loc0 v s : F.G0) : F.Γ) = F.loc v s := fun _ => rfl
    refine ⟨algebraMap k Q (((F.Ψ (F.loc v t) : k)) - 1)⁻¹ * ρ.r (F.loc0 v t) 1 0, fun s => ?_⟩
    have h10 := congrFun (congrFun (ρ.ord v ![t, s, t]) 1) 0
    simp [ordProd, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hd0, hd1, hd2, h01, h02, h12,
      hψ0, hψ1, hψ2, hl] at h10
    simp only [Algebra.smul_def, mul_one] at h10
    have hE : (algebraMap k Q ((F.Ψ (F.loc v t) : k)) - algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹) * algebraMap k Q (((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹ = 1 := by
      rw [← map_sub, ← map_mul, mul_inv_cancel₀ he, map_one]
    have hF : (algebraMap k Q ((F.Ψ (F.loc v t) : k)) - 1) * algebraMap k Q (((F.Ψ (F.loc v t) : k)) - 1)⁻¹ = 1 := by
      rw [← map_one (algebraMap k Q), ← map_sub, ← map_mul, mul_inv_cancel₀ hf, map_one]
    simp only [Algebra.smul_def, map_sub, map_one]
    linear_combination (-(algebraMap k Q (((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹ * algebraMap k Q (((F.Ψ (F.loc v t) : k)) - 1)⁻¹)) * h10
      + ((algebraMap k Q ((F.Ψ (F.loc v s) : k)) - 1) * algebraMap k Q (((F.Ψ (F.loc v t) : k)) - 1)⁻¹ * ρ.r (F.loc0 v t) 1 0 - ρ.r (F.loc0 v s) 1 0) * hE
      - algebraMap k Q (((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹ * (algebraMap k Q ((F.Ψ (F.loc v t) : k)) - algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹) * ρ.r (F.loc0 v s) 1 0 * hF
  · intro v
    obtain ⟨t, ht⟩ := hF.f3 v
    have hne := Units.ne_zero (F.Ψ (F.loc v t))
    have hsq : ((F.Ψ (F.loc v t) : k)) * (F.Ψ (F.loc v t) : k) ≠ 1 := by
      intro h
      apply ht
      rw [Units.ext_iff, Units.val_pow_eq_pow_val, Units.val_one, pow_two, h]
    have hf : ((F.Ψ (F.loc v t) : k)) - 1 ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      apply hsq
      rw [h, one_mul]
    have he : ((F.Ψ (F.loc v t) : k)) - ((F.Ψ (F.loc v t) : k))⁻¹ ≠ 0 := by
      intro h
      rw [sub_eq_zero] at h
      apply hsq
      calc ((F.Ψ (F.loc v t) : k)) * (F.Ψ (F.loc v t) : k)
          = (F.Ψ (F.loc v t) : k) * ((F.Ψ (F.loc v t) : k))⁻¹ := by rw [← h]
        _ = 1 := mul_inv_cancel₀ hne
    have hl : ∀ s, ((F.loc0 v s : F.G0) : F.Γ) = F.loc v s := fun _ => rfl
    have hg : 1 - ((F.Ψ (F.loc v t) : k))⁻¹ ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      exact hf (by rw [← inv_eq_one.mp h.symm, sub_self])
    refine ⟨algebraMap k Q (1 - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹ * ρ.r (F.loc0 v t) 2 1, fun s => ?_⟩
    have h21 := congrFun (congrFun (ρ.ord v ![t, s, t]) 2) 1
    simp [ordProd, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, hd0, hd1, hd2, h01, h02, h12,
      hψ0, hψ1, hψ2, hl] at h21
    simp only [Algebra.smul_def, mul_one] at h21
    have hD : (algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹ - algebraMap k Q ((F.Ψ (F.loc v t) : k))) * algebraMap k Q (((F.Ψ (F.loc v t) : k))⁻¹ - ((F.Ψ (F.loc v t) : k)))⁻¹ = 1 := by
      rw [← map_sub, ← map_mul, mul_inv_cancel₀ (by rw [← neg_sub]; exact neg_ne_zero.mpr he), map_one]
    have hG : (1 - algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹) * algebraMap k Q (1 - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹ = 1 := by
      rw [← map_one (algebraMap k Q), ← map_sub, ← map_mul, mul_inv_cancel₀ hg, map_one]
    show ρ.r (F.star (F.loc0 v s)) 1 0 = _
    rw [(UpperTheory.V.Fr.star hF).2.2.2.2 ρ _ 1 0]
    change ρ.r (F.loc0 v s) 2 1 = _
    simp only [Algebra.smul_def, map_sub, map_one, Units.val_inv_eq_inv_val]
    linear_combination (algebraMap k Q (((F.Ψ (F.loc v t) : k))⁻¹ - ((F.Ψ (F.loc v t) : k)))⁻¹ * algebraMap k Q (1 - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹) * h21
      + ((1 - algebraMap k Q ((F.Ψ (F.loc v s) : k))⁻¹) * algebraMap k Q (1 - ((F.Ψ (F.loc v t) : k))⁻¹)⁻¹ * ρ.r (F.loc0 v t) 2 1 - ρ.r (F.loc0 v s) 2 1) * hD
      - algebraMap k Q (((F.Ψ (F.loc v t) : k))⁻¹ - ((F.Ψ (F.loc v t) : k)))⁻¹ * (algebraMap k Q ((F.Ψ (F.loc v t) : k))⁻¹ - algebraMap k Q ((F.Ψ (F.loc v t) : k))) * ρ.r (F.loc0 v s) 2 1 * hG
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.framePoint_alg_coord_eq :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ}, F.Ok C₀ → ∀ (Q : Type) [CommRing Q] [Algebra k Q] (ρ : NRep F 3 Q), ρ.IsBar (algebraMap k Q) → ρ.triM = ⊥ → (∀ i j, IsLocallyConstant fun g => ρ.r g i j) → ∀ U : Subalgebra k Q, (∀ g, ρ.r g 1 0 ∈ U) → (fun g => (Subalgebra.toSubmodule U).mkQ (ρ.r g 2 0)) ∈ F.strS (Q ⧸ Subalgebra.toSubmodule U) := by
  intro l _ k _ _ F C₀ hF Q _ _ ρ hb ht hlc U hU
  have hz : ∀ g (i j : Fin 3), i < j → ρ.r g i j = 0 := by
    intro g i j hij
    have hm : ρ.r g i j ∈ ρ.triM := Ideal.subset_span ⟨g, i, j, hij, rfl⟩
    rw [ht] at hm
    exact (Ideal.mem_bot).1 hm
  have hd : ∀ g (i : Fin 3), ρ.r g i i = algebraMap k Q ↑(F.Ψ ↑g ^ w 3 i) := hb.1
  have h21 : ∀ g, ρ.r g 2 1 ∈ U := by
    intro g
    have e : ρ.r g 2 1 = ρ.r (F.star g) 1 0 := by
      rw [(star hF).2.2.2.2 ρ g 1 0]
      rfl
    rw [e]
    exact hU _
  have w0 : w 3 0 = 1 := by simp [w]
  have w1 : w 3 1 = 0 := by simp [w]
  have w2 : w 3 2 = -1 := by simp [w]
  have hq : ∀ x : Q, x ∈ U → (Subalgebra.toSubmodule U).mkQ x = 0 := by
    intro x hx
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  refine ⟨(hlc 2 0).comp _, ?_, ?_, ?_⟩
  · intro g h
    dsimp only
    rw [map_mul, Matrix.mul_apply, Fin.sum_univ_three, hd h 0, hd g 2, w0, w2, zpow_one, _root_.zpow_neg_one]
    have e1 : ρ.r g 2 0 * algebraMap k Q ↑(F.Ψ ↑h) = (↑(F.Ψ ↑h) : k) • ρ.r g 2 0 := by
      rw [Algebra.smul_def, mul_comm]
    have e3 : algebraMap k Q ↑(F.Ψ ↑g)⁻¹ * ρ.r h 2 0 = (↑(F.Ψ ↑g)⁻¹ : k) • ρ.r h 2 0 := by
      rw [Algebra.smul_def]
    rw [e1, e3, map_add (f := _), map_add (f := _), map_smul, map_smul, hq _ (U.mul_mem (h21 g) (hU h)), add_zero]
  · intro g
    dsimp only
    rw [(star hF).2.2.2.2 ρ g 2 0]
    rfl
  · intro v
    obtain ⟨t, ht2⟩ := hF.f3 v
    refine ⟨((↑(F.Ψ (F.loc v t)) : k) - ↑(F.Ψ (F.loc v t))⁻¹)⁻¹ • (Subalgebra.toSubmodule U).mkQ (ρ.r (F.loc0 v t) 2 0), fun s => ?_⟩
    have hl : ∀ x, ((F.loc0 v x : F.G0) : F.Γ) = F.loc v x := fun _ => rfl
    have e := congrArg (fun M => M 2 0) (ρ.ord v ![t, t, s])
    have z01 := hz (F.loc0 v t) 0 1 (by decide)
    have z02 := hz (F.loc0 v t) 0 2 (by decide)
    have z12 := hz (F.loc0 v t) 1 2 (by decide)
    have y01 := hz (F.loc0 v s) 0 1 (by decide)
    have y02 := hz (F.loc0 v s) 0 2 (by decide)
    have y12 := hz (F.loc0 v s) 1 2 (by decide)
    simp (config := {decide := true}) only [ordProd, List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one, Matrix.mul_apply, Fin.sum_univ_three, Matrix.sub_apply, Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Matrix.one_apply, Matrix.zero_apply, smul_eq_mul, z01, z02, z12, y01, y02, y12, hd, hb.2, hl, w0, w1, w2, zpow_one, zpow_zero, _root_.zpow_neg_one, Units.val_one, map_one, if_true, if_false, mul_zero, zero_mul, sub_zero, zero_sub, add_zero, zero_add] at e
    set x : k := ↑(F.Ψ (F.loc v t)) with hx
    set xi : k := ↑(F.Ψ (F.loc v t))⁻¹ with hxi
    set y : k := ↑(F.Ψ (F.loc v s)) with hy
    set yi : k := ↑(F.Ψ (F.loc v s))⁻¹ with hyi
    have key : algebraMap k Q ((xi - x) * (xi - 1)) * ρ.r (F.loc0 v s) 2 0 + algebraMap k Q ((xi - 1) * (y - yi)) * ρ.r (F.loc0 v t) 2 0 = -(ρ.r (F.loc0 v t) 2 1 * ρ.r (F.loc0 v t) 1 0 * (algebraMap k Q y - algebraMap k Q yi) + (algebraMap k Q xi - algebraMap k Q x) * ρ.r (F.loc0 v t) 2 1 * ρ.r (F.loc0 v s) 1 0) := by
      simp only [map_mul, map_sub, map_one]
      linear_combination e
    have hne1 : xi - 1 ≠ 0 := by
      intro h
      apply ht2
      have h' : (F.Ψ (F.loc v t))⁻¹ = 1 := Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h)
      rw [inv_eq_one.1 h', one_pow]
    have hne2 : xi - x ≠ 0 := by
      intro h
      apply ht2
      have h' : (F.Ψ (F.loc v t))⁻¹ = F.Ψ (F.loc v t) := Units.ext (sub_eq_zero.1 h)
      calc F.Ψ (F.loc v t) ^ 2 = (F.Ψ (F.loc v t))⁻¹ * F.Ψ (F.loc v t) := by rw [sq, h']
        _ = 1 := inv_mul_cancel _
    have hne3 : x - xi ≠ 0 := fun h => hne2 (by rw [← neg_sub, h, neg_zero])
    have hc : (xi - x) * (xi - 1) ≠ 0 := mul_ne_zero hne2 hne1
    dsimp only
    rw [smul_smul, ← map_smul, ← sub_eq_zero, ← map_sub]
    apply hq
    have eq : ρ.r (F.loc0 v s) 2 0 - ((y - yi) * (x - xi)⁻¹) • ρ.r (F.loc0 v t) 2 0 = algebraMap k Q ((xi - x) * (xi - 1))⁻¹ * (algebraMap k Q ((xi - x) * (xi - 1)) * ρ.r (F.loc0 v s) 2 0 + algebraMap k Q ((xi - 1) * (y - yi)) * ρ.r (F.loc0 v t) 2 0) := by
      rw [Algebra.smul_def, mul_add, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul]
      have h3 : ((xi - x) * (xi - 1))⁻¹ * ((xi - 1) * (y - yi)) = -((y - yi) * (x - xi)⁻¹) := by
        field_simp
        ring
      rw [h3, map_neg, neg_mul, sub_eq_add_neg]
    rw [eq, key]
    exact mul_mem (U.algebraMap_mem _) (neg_mem (add_mem (mul_mem (mul_mem (h21 _) (hU _)) (sub_mem (U.algebraMap_mem _) (U.algebraMap_mem _))) (mul_mem (mul_mem (sub_mem (U.algebraMap_mem _) (U.algebraMap_mem _)) (h21 _)) (hU _))))
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem two_ne {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (h : l ≠ 2) : (2 : k) ≠ 0 := by
  intro h2
  have h3 : ((2 : ℕ) : k) = 0 := by simpa using h2
  rw [CharP.cast_eq_zero_iff k l] at h3
  exact h ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h3)

private theorem sq_facts {k : Type} [Field k] {t : kˣ} (h : t ^ 2 ≠ 1) :
    (t : k) ≠ (t : k)⁻¹ ∧ (t : k) ≠ 1 ∧ (t : k)⁻¹ ≠ 1 := by
  have h0 : (t : k) ≠ 0 := t.ne_zero
  have h1 : (t : k) ≠ 1 := fun e => h (by ext; simp [e])
  refine ⟨fun e => h ?_, h1, fun e => h1 (inv_eq_one.1 e)⟩
  ext
  rw [Units.val_pow_eq_pow_val, sq, Units.val_one]
  nth_rewrite 2 [e]
  exact mul_inv_cancel₀ h0

private theorem pow_inj {k : Type} [Field k] {t : kˣ} (h : t ^ 2 ≠ 1) {n : ℕ} (hn : n = 2 ∨ n = 3)
    (i j : Fin n) (hij : i ≠ j) : ((t ^ w n i : kˣ) : k) ≠ ((t ^ w n j : kˣ) : k) := by
  obtain ⟨a, b, c⟩ := sq_facts h
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [w, a, b, c, a.symm, b.symm, c.symm]

private theorem diff_inj {k : Type} [Field k] (h2 : (2 : k) ≠ 0) {t : kˣ} (h : t ^ 2 ≠ 1) {n : ℕ}
    (hn : n = 2 ∨ n = 3) (i j : Fin n) (hij : i ≠ j) :
    ((t ^ w n i : kˣ) : k) - ((t⁻¹ ^ w n i : kˣ) : k) ≠ ((t ^ w n j : kˣ) : k) - ((t⁻¹ ^ w n j : kˣ) : k) := by
  obtain ⟨a, -, -⟩ := sq_facts h
  have b : (t : k) - (t : k)⁻¹ ≠ 0 := sub_ne_zero.2 a
  have c : (t : k)⁻¹ - (t : k) ≠ 0 := sub_ne_zero.2 a.symm
  have d : (t : k) - (t : k)⁻¹ ≠ (t : k)⁻¹ - (t : k) := fun e =>
    mul_ne_zero h2 b (by linear_combination e)
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;>
    first
    | exact absurd rfl hij
    | simp [w, b, c, d, b.symm, c.symm, d.symm]

theorem UpperTheory.V.Fr.pr_good :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (K : Type) [Field K] (φ : k →+* K) (ρ : NRep F n K), ρ.IsBar φ → ρ.Good ∧ lieT K n ≠ 0 ∧ thetaLie (lieT K n) = lieT K n := by
  intro l _ k _ _ F C₀ n hF hn K _ φ ρ hρ
  have h2 : (2 : k) ≠ 0 := two_ne hF.l_odd
  have hs : F.Ψ (F.star F.g0) = (F.Ψ F.g0)⁻¹ := by
    have e : ((F.star F.g0 : F.G0) : F.Γ) = F.c * (F.g0 : F.Γ)⁻¹ * F.c⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, map_inv, hF.Ψ_c]
    simp
  refine ⟨⟨?_, fun i j hij => ?_, fun v => ?_⟩, ?_, ?_⟩
  · have := (map_ne_zero φ).2 h2
    rwa [map_ofNat] at this
  · rw [Matrix.sub_apply, Matrix.sub_apply, hρ.1, hρ.1, hρ.1, hρ.1, hs, ← map_sub, ← map_sub]
    exact fun e => diff_inj h2 hF.baseSubgroup_spec hn i j hij (φ.injective e)
  · obtain ⟨s, hs⟩ := hF.f3 v
    refine ⟨s, fun i j hij e => pow_inj hs hn i j hij (φ.injective ?_)⟩
    rw [← hρ.2, ← hρ.2, e]
  · intro e
    rcases hn with rfl | rfl
    · have := congrFun (congrFun e 0) 0
      simp [lieT, w] at this
    · have := congrFun (congrFun e 0) 0
      simp [lieT, w] at this
  · rcases hn with rfl | rfl
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [thetaLie, lieT, w, Matrix.mul_apply, Fin.sum_univ_two, Jmat, Matrix.diagonal, Fin.rev] <;> norm_num
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [thetaLie, lieT, w, Matrix.mul_apply, Fin.sum_univ_three, Jmat, Matrix.diagonal, Fin.rev] <;> norm_num
end

section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem tri_zero {K G ι : Type} [Field K] [Fintype ι] [LinearOrder ι] (M : G → Matrix ι ι K) (ω : G → K)
    (Φ : Matrix ι ι K) (hM : ∀ g i j, j < i → M g i j = 0)
    (h : ∀ g i j, ∑ p, M g i p * Φ p j = ω g * ∑ q, Φ i q * M g q j)
    (key : ∀ i j, (∀ g, M g i i * Φ i j = ω g * (Φ i j * M g j j)) → Φ i j = 0) : ∀ i j, Φ i j = 0 := by
  intro i
  induction i using WellFoundedGT.induction with
  | _ i ih =>
  intro j
  induction j using WellFoundedLT.induction with
  | _ j ih' =>
  refine key i j fun g => ?_
  have := h g i j
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j] at this
  · exact this
  · intro q _ hq
    rcases lt_or_gt_of_ne hq with h1 | h1
    · rw [ih' q h1, zero_mul]
    · rw [hM g q j h1, mul_zero]
  · simp
  · intro p _ hp
    rcases lt_or_gt_of_ne hp with h1 | h1
    · rw [hM g i p h1, zero_mul]
    · rw [ih p h1 j, mul_zero]
  · simp

private theorem om_map {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] (F : Frame l k) {K : Type} [Field K]
    [CharP K l] (φ : k →+* K) (g : F.Γ) : φ (F.om k g : k) = (F.om K g : K) := by
  have : φ.comp (ZMod.castHom (dvd_refl l) k) = ZMod.castHom (dvd_refl l) K := Subsingleton.elim _ _
  exact RingHom.congr_fun this _

private theorem w_cases {n : ℕ} (hn : n = 2 ∨ n = 3) (i j : Fin n) :
    w n j - w n i = 0 ∨ (w n j - w n i = 1 ∨ w n j - w n i = -1) ∨
      ((w n j - w n i = 2 ∨ w n j - w n i = -2) ∧ j = i.rev) := by
  rcases hn with rfl | rfl
  · revert i j; decide
  · revert i j; decide

private theorem thetaLie_single {K : Type} [Field K] {n : ℕ} (i : Fin n) :
    thetaLie (Matrix.single i i.rev (1 : K)) = -Matrix.single i i.rev (1 : K) := by
  unfold thetaLie
  congr 1
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single b.rev, Matrix.mul_apply, Finset.sum_eq_single a.rev]
  · simp only [Jmat, Matrix.transpose_apply, Matrix.single_apply, Fin.rev_rev, if_true, one_mul, mul_one,
      Fin.rev_inj]
    congr 1
    refine propext ⟨?_, ?_⟩
    · rintro ⟨rfl, rfl⟩; simp
    · rintro ⟨rfl, rfl⟩; simp
  · intro p _ hp
    simp [Jmat, hp]
  · simp
  · intro p _ hp
    have : b ≠ p.rev := fun h => hp (by simp [h])
    simp [Jmat, this]
  · simp

theorem UpperTheory.V.Fr.pr_dual :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ (K : Type) [Field K] [CharP K l] (φ : k →+* K) (ρ : NRep F n K) (B : Box F n K), B.Of ρ → ρ.IsBar φ → ((∀ g, UpT (ρ.r g)) ∨ ∀ g, UpT (ρ.r g)ᵀ) → ∀ f : Matrix (Fin n) (Fin n) K →ₗ[K] K, (∀ g X, f (B.ad g X) = F.om K g * f X) → f = 0 := by
  intro l _ k _ _ F C₀ n ok hn K _ _ φ ρ B hB hbar htri f hf
  set Φ : Matrix (Fin n) (Fin n) K := fun i j => f (Matrix.single i j 1) with hΦ
  have hsum : ∀ X : Matrix (Fin n) (Fin n) K, f X = ∑ i, ∑ j, X i j * Φ i j := fun X => by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]

    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hΦ, ← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  have h0 : ∀ (g : F.G0) X, f (ρ.r g * X) = F.om K g * f (X * ρ.r g) := fun g X => by
    rw [← hf]
    congr 1
    have hr : (B.r g).right = 1 := (B.nu g).trans g.2
    show _ = (B.r g).adFun _
    rw [GG.adFun, if_pos hr, ← hB.res g, GG.mat]
    simp [Matrix.mul_assoc]
  have h1 : ∀ (g : F.G0) i j, ∑ p, ρ.r g p i * Φ p j = F.om K g * ∑ q, Φ i q * ρ.r g j q := fun g i j => by
    have := h0 g (Matrix.single i j 1)
    rw [hsum, hsum] at this
    rw [Finset.sum_eq_single i (s := Finset.univ) (f := fun a => ∑ b, (Matrix.single i j (1 : K) * ρ.r g) a b * Φ a b)]
      at this
    · convert this using 2 with p
      · rw [Finset.sum_eq_single j]
        · simp
        · intro b _ hb
          rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hb, zero_mul]
        · simp
      · simp [mul_comm]
    · intro a _ ha
      exact Finset.sum_eq_zero fun b _ => by rw [Matrix.single_mul_apply_of_ne _ _ _ _ _ ha, zero_mul]
    · simp
  have hc : ∀ i, -Φ i i.rev = F.om K F.c * Φ i i.rev := fun i => by
    rw [hΦ]
    dsimp only
    rw [← hf, ← map_neg, ← thetaLie_single]
    congr 1
    have hr : (B.r F.c).right ≠ 1 := by rw [B.nu, ok.del_c]; decide
    have hl : (B.r F.c).left = 1 := Units.ext hB.atc
    show _ = (B.r F.c).adFun _
    rw [GG.adFun, if_neg hr, GG.mat, hl]
    simp
  have key : ∀ i j, (∀ g : F.G0, ρ.r g i i * Φ i j = F.om K g * (Φ i j * ρ.r g j j)) → Φ i j = 0 := by
    intro i j h
    by_contra hne
    have h2 : ∀ g : F.G0, F.om k g * F.Ψ g ^ (w n j - w n i) = 1 := fun g => by
      have e := h g
      rw [hbar.1, hbar.1, ← om_map F φ, mul_comm (Φ i j), ← mul_assoc, ← map_mul] at e
      have e2 := φ.injective (mul_right_cancel₀ hne e)
      rw [← Units.val_mul, Units.val_inj] at e2
      rw [_root_.zpow_sub, ← mul_assoc, ← e2, mul_inv_cancel]
    rcases w_cases hn i j with h3 | h3 | ⟨h3, rfl⟩
    · obtain ⟨g, hg⟩ := ok.f2a
      exact hg (by simpa [h3] using h2 g)
    · obtain ⟨g, hg⟩ := ok.f2b _ h3
      exact hg (h2 g)
    · obtain ⟨g, hg⟩ := ok.f2c _ h3
      apply hg
      rcases Int.units_eq_one_or (F.del g) with hd | hd
      · rw [h2 ⟨g, hd⟩, one_mul]
        simp [Frame.delK, hd]
      · have hm : g * F.c ∈ F.del.ker := by rw [MonoidHom.mem_ker, map_mul, hd, ok.del_c]; rfl
        have e := h2 ⟨_, hm⟩
        have ec : F.om k F.c = -1 := by
          apply Units.ext
          apply φ.injective
          rw [om_map]
          have := hc i
          rw [← neg_one_mul] at this
          rw [← mul_right_cancel₀ hne this]
          simp
        have ed : F.delK k g = -1 := by
          apply Units.ext
          simp [Frame.delK, hd]
        simp only [map_mul, ec, ok.Ψ_c, mul_one] at e
        rw [ed, mul_right_comm, e]
  have hz : ∀ i j, Φ i j = 0 := by
    rcases htri with ht | ht
    · exact tri_zero (ι := (Fin n)ᵒᵈ) (fun g : F.G0 => (ρ.r g)ᵀ) (fun g => F.om K g) Φ
        (fun g i j hij => ht g j i hij) h1 key
    · exact tri_zero (fun g : F.G0 => (ρ.r g)ᵀ) (fun g => F.om K g) Φ ht h1 key
  ext1 X
  simp [hsum, hz]
end
