module

public import Formalism.GradedWeylDivisibility.Bundle001
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle004
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.MvPolynomial.Monad

@[expose] public section

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem aeval_eq_self_of_eq_X_on_vars {τ B : Type*} [CommRing B] (g : τ → MvPolynomial τ B)
    (p : MvPolynomial τ B) (h : ∀ i ∈ p.vars, g i = X i) : aeval g p = p := by
  have key := hom_congr_vars (f₁ := (aeval g : MvPolynomial τ B →ₐ[B] MvPolynomial τ B).toRingHom)
    (f₂ := RingHom.id _) (p₁ := p) (p₂ := p) (RingHom.ext fun b => by simp [algebraMap_eq])
    (fun i hi _ => by simpa using h i hi) rfl
  simpa using key

private theorem degreeOf_eq_zero_of_not_mem_vars {τ B : Type*} [CommRing B] (i : τ)
    (p : MvPolynomial τ B) (h : i ∉ p.vars) : degreeOf i p = 0 := by
  refine Nat.le_zero.1 (degreeOf_le_iff.2 fun m hm => ?_)
  by_contra hne
  exact h ((MvPolynomial.mem_vars_iff_mem_support i).2 ⟨m, hm, Finsupp.mem_support_iff.2 (by omega)⟩)

private theorem not_mem_vars_of_degreeOf_eq_zero {τ B : Type*} [CommRing B] (i : τ)
    (p : MvPolynomial τ B) (h : degreeOf i p = 0) : i ∉ p.vars := by
  intro hi
  obtain ⟨m, hm, hmi⟩ := (MvPolynomial.mem_vars_iff_mem_support i).1 hi
  have h1 := degreeOf_le_iff.1 h.le m hm
  exact Finsupp.mem_support_iff.1 hmi (by omega)

private theorem le_and_degreeOf_top_le_of_degreeOf_sum_le {B τ : Type} [CommRing B] [IsDomain B] [DecidableEq τ]
    (hE : EvalDeg) (x y c : τ) (hxy : x ≠ y) (hxc : x ≠ c) (hyc : y ≠ c) (K e s : ℕ)
    (W : ℕ → MvPolynomial τ B) (hW : ∀ k, ∀ i ∈ (W k).vars, i ≠ x ∧ i ≠ y) (hWK : W K ≠ 0)
    (hs : degreeOf c ((X y + X c * X x) ^ e *
      ∑ k ∈ Finset.range (K + 1), X x ^ k * (X y + X c * X x) ^ (K - k) * W k) ≤ s) :
    e ≤ s ∧ degreeOf c (W K) ≤ s - e + K := by
  obtain ⟨Y, hY⟩ : ∃ Y : MvPolynomial τ B, Y = X y + X c * X x := ⟨_, rfl⟩
  rw [← hY] at hs
  obtain ⟨Q, hQ⟩ : ∃ Q : MvPolynomial τ B,
      Q = ∑ k ∈ Finset.range (K + 1), X x ^ k * Y ^ (K - k) * W k := ⟨_, rfl⟩
  rw [← hQ] at hs
  have hX : ∀ v : τ, (X v : MvPolynomial τ B) ≠ 0 := by
    intro v hv
    have h1 : degreeOf v (0 : MvPolynomial τ B) ≤ 0 := degreeOf_le_iff.2 fun m hm => by simp at hm
    rw [← hv, degreeOf_X] at h1
    simp at h1
  have hYσ : aeval (fun v : τ => if v = x then (1 : MvPolynomial τ B) else if v = y then -X c else X v)
      Y = 0 := by
    rw [hY]; simp [hxy.symm, hxc.symm, hyc.symm]
  have hWσ : ∀ k, aeval (fun v : τ => if v = x then (1 : MvPolynomial τ B) else if v = y then -X c
      else X v) (W k) = W k := by
    intro k
    refine aeval_eq_self_of_eq_X_on_vars _ _ fun i hi => ?_
    simp [(hW k i hi).1, (hW k i hi).2]
  have hsum : aeval (fun v : τ => if v = x then (1 : MvPolynomial τ B) else if v = y then -X c
      else X v) Q = W K := by

    rw [hQ, map_sum, Finset.sum_eq_single K]
    · rw [Nat.sub_self, pow_zero, mul_one, map_mul, map_pow, hWσ, aeval_X]
      simp
    · intro k hk hkK
      have hk' : K - k ≠ 0 := by
        rw [Finset.mem_range] at hk; omega
      simp only [map_mul, map_pow, hYσ, zero_pow hk', mul_zero, zero_mul]
    · intro h; exact absurd (Finset.self_mem_range_succ K) h
  have hQ0 : Q ≠ 0 := by
    intro h; rw [h, map_zero] at hsum; exact hWK hsum.symm
  have hcY : 1 ≤ degreeOf c Y := by
    by_contra hlt
    have h0 : degreeOf c Y = 0 := by omega
    have hfix : aeval (fun v : τ => if v = c then (0 : MvPolynomial τ B) else X v) Y = Y := by
      refine aeval_eq_self_of_eq_X_on_vars _ _ fun i hi => ?_
      have hic : i ≠ c := fun h => not_mem_vars_of_degreeOf_eq_zero c Y h0 (by rwa [h] at hi)
      simp [hic]
    have h2 : (X c : MvPolynomial τ B) * X x = 0 := by
      have h3 : aeval (fun v : τ => if v = c then (0 : MvPolynomial τ B) else X v)
          (X y + X c * X x : MvPolynomial τ B) = X y := by
        simp [hyc, hxc]
      rw [← hY, hfix, hY] at h3
      linear_combination h3
    exact mul_ne_zero (hX c) (hX x) h2
  have hY0 : Y ≠ 0 := by
    rintro rfl
    have h1 : degreeOf c (0 : MvPolynomial τ B) ≤ 0 := degreeOf_le_iff.2 fun m hm => by simp at hm
    omega
  have hyQ : degreeOf y Q ≤ K := by
    rw [hQ]
    refine Finset.sum_induction _ (fun q => degreeOf y q ≤ K)
      (fun a b ha hb => (degreeOf_add_le y a b).trans (max_le ha hb))
      (degreeOf_le_iff.2 fun m hm => by simp at hm) ?_
    intro k _
    show degreeOf y (X x ^ k * Y ^ (K - k) * W k) ≤ K
    have h1 := degreeOf_mul_le y (X x ^ k * Y ^ (K - k)) (W k)
    have h2 := degreeOf_mul_le y (X x ^ k) (Y ^ (K - k))
    have h3 := degreeOf_pow_le y (X x : MvPolynomial τ B) k
    have h4 := degreeOf_pow_le y Y (K - k)
    have h5 : degreeOf y (X x : MvPolynomial τ B) = 0 := by
      rw [degreeOf_X]; simp [hxy.symm]
    have h6 : degreeOf y Y ≤ 1 := by
      rw [hY]
      refine (degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
      · rw [degreeOf_X]; split_ifs <;> omega
      · refine (degreeOf_mul_le _ _ _).trans ?_
        rw [degreeOf_X, degreeOf_X]
        simp [hyc, hxy.symm]
    have h7 : degreeOf y (W k) = 0 :=
      degreeOf_eq_zero_of_not_mem_vars y (W k) fun hi => (hW k y hi).2 rfl
    rw [h5, mul_zero] at h3
    have h8 : (K - k) * degreeOf y Y ≤ K - k := by
      simpa using Nat.mul_le_mul_left (K - k) h6
    generalize (K - k) * degreeOf y Y = t at h4 h8
    omega
  have key : degreeOf c (W K) ≤ degreeOf c Q + degreeOf y Q := by
    convert hE B τ x y c hxy hxc hyc Q using 2
    exact hsum.symm
  rw [degreeOf_mul_eq (pow_ne_zero _ hY0) hQ0, degreeOf_pow_eq c Y e hY0] at hs
  have he : e ≤ e * degreeOf c Y := by simpa using Nat.mul_le_mul_left e hcY
  generalize e * degreeOf c Y = t at hs he
  constructor <;> omega

theorem peelDegBound_of (hE : EvalDeg) : PeelDegBound := by
  intro B _ _ r n l j hlj a0 K e s w hw hK hs
  have hφX : ∀ v : Fin r × Fin n, colAddGen B l j (X v : MvPolynomial (Fin r × Fin n) B) =
      if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) := by
    intro v; simp only [colAddGen, aeval_X]
  have hinj : ∀ f : MvPolynomial (Fin r × Fin n) B, colAddGen B l j f = 0 → f = 0 := by
    intro f hf
    have hl : (aeval (fun v : Option (Fin r × Fin n) => v.elim (0 : MvPolynomial (Fin r × Fin n) B) X)).comp
        (colAddGen B l j) = AlgHom.id B _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp only [AlgHom.comp_apply, AlgHom.id_apply, hφX]
      split_ifs <;> simp
    have h1 := congrArg (aeval (fun v : Option (Fin r × Fin n) =>
      v.elim (0 : MvPolynomial (Fin r × Fin n) B) X)) hf
    rw [map_zero, ← AlgHom.comp_apply, hl, AlgHom.id_apply] at h1
    exact h1
  have hvars : ∀ k, ∀ i ∈ (colAddGen B l j (w k)).vars,
      i ≠ some (a0, l) ∧ i ≠ some (a0, j) := by
    intro k i hi
    have hi2 : i ∈ ((bind₁ fun v : Fin r × Fin n => if v.2 = j then
        (X (some v) + X none * X (some (v.1, l)) : MvPolynomial (Option (Fin r × Fin n)) B)
        else X (some v)) (w k)).vars := by
      rw [← aeval_eq_bind₁]; exact hi
    have hi3 := vars_bind₁ _ _ hi2
    rw [Finset.mem_biUnion] at hi3
    obtain ⟨v, hv, hiv⟩ := hi3
    obtain ⟨m, hm, hmv⟩ := (MvPolynomial.mem_vars_iff_mem_support v).1 hv
    have hvl : v ≠ (a0, l) := by
      rintro rfl; exact (Finsupp.mem_support_iff.1 hmv) (hw k m hm).1
    have hvj : v ≠ (a0, j) := by
      rintro rfl; exact (Finsupp.mem_support_iff.1 hmv) (hw k m hm).2
    split_ifs at hiv with hv2
    · rcases Finset.mem_union.1 (vars_add_subset _ _ hiv) with h1 | h1
      · rw [vars_X, Finset.mem_singleton] at h1
        subst h1; simp [hvl, hvj]
      · rcases Finset.mem_union.1 (vars_mul _ _ h1) with h2 | h2
        · rw [vars_X, Finset.mem_singleton] at h2
          subst h2; simp
        · rw [vars_X, Finset.mem_singleton] at h2
          subst h2
          refine ⟨fun h => ?_, by simp [hlj]⟩
          simp only [Option.some.injEq, Prod.mk.injEq, and_true] at h
          exact hvj (Prod.ext h hv2)
    · rw [vars_X, Finset.mem_singleton] at hiv
      subst hiv; simp [hvl, hvj]
  have e1 : colAddGen B l j (X (a0, l) : MvPolynomial (Fin r × Fin n) B) = X (some (a0, l)) := by
    rw [hφX]; simp [hlj]
  have e2 : colAddGen B l j (X (a0, j) : MvPolynomial (Fin r × Fin n) B) =
      X (some (a0, j)) + X none * X (some (a0, l)) := by
    rw [hφX]; simp
  have hQ : colAddGen B l j
      (∑ k ∈ Finset.range (K + 1), X (a0, l) ^ k * X (a0, j) ^ (e + (K - k)) * w k) =
      (X (some (a0, j)) + X none * X (some (a0, l))) ^ e * ∑ k ∈ Finset.range (K + 1),
        X (some (a0, l)) ^ k * (X (some (a0, j)) + X none * X (some (a0, l))) ^ (K - k) *
          colAddGen B l j (w k) := by

    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow, e1, e2, pow_add]
    ring
  rw [hQ] at hs
  exact le_and_degreeOf_top_le_of_degreeOf_sum_le hE (some (a0, l)) (some (a0, j)) none (by simp [hlj]) (by simp) (by simp)
    K e s (fun k => colAddGen B l j (w k)) hvars (fun h => hK (hinj _ h)) hs

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

private theorem rowGen_map_intCast {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℤ) :
    rowGen ℚ a b (map (Int.castRingHom ℚ) f) =
      Polynomial.map (map (Int.castRingHom ℚ)) (rowGen ℤ a b f) := by
  induction f using MvPolynomial.induction_on
  next c =>
    simp [rowGen]
  next p q hp hq =>
    rw [_root_.map_add (f := _), _root_.map_add (f := _), _root_.map_add (f := _), hp, hq, Polynomial.map_add (f := _)]
  next p v hp =>
    rw [_root_.map_mul, map_X, _root_.map_mul, _root_.map_mul, Polynomial.map_mul, hp]
    congr 1
    simp only [rowGen, aeval_X]
    split_ifs <;> simp

private theorem rowDiv_map_intCast {r n : ℕ} (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) ℤ) :
    rowDiv ℚ a b k (map (Int.castRingHom ℚ) f) = map (Int.castRingHom ℚ) (rowDiv ℤ a b k f) := by
  unfold rowDiv
  rw [rowGen_map_intCast, Polynomial.coeff_map]

private theorem map_intCast_applyWord {r n : ℕ} (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) ℤ) :
    map (Int.castRingHom ℚ) (applyWord ℤ w f) = applyWord ℚ w (map (Int.castRingHom ℚ) f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show map (Int.castRingHom ℚ) (rowDiv ℤ x.1 x.2.1 x.2.2 (applyWord ℤ w f)) =
      rowDiv ℚ x.1 x.2.1 x.2.2 (applyWord ℚ w (map (Int.castRingHom ℚ) f))
    rw [← rowDiv_map_intCast, ih]

private theorem map_intCast_hw {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) :
    map (Int.castRingHom ℚ) (hw ℤ hn ν) = hw ℚ hn ν := by
  unfold hw
  rw [_root_.map_prod]
  refine Finset.prod_congr rfl (fun s _ => ?_)
  rw [_root_.map_pow]
  congr 1
  unfold lpMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

theorem lclosedeq_weyl_denom {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)
    (F : MvPolynomial (Fin r × Fin n) ℚ) (hF : F ∈ weyl ℚ r n hn ν) :
    ∃ c : ℤ, c ≠ 0 ∧ ∃ u ∈ weyl ℤ r n hn ν, map (Int.castRingHom ℚ) u = (c : ℚ) • F := by
  unfold weyl at hF
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine ⟨1, one_ne_zero, applyWord ℤ w (hw ℤ hn ν), Submodule.subset_span ⟨w, rfl⟩, ?_⟩
    rw [map_intCast_applyWord, map_intCast_hw]
    simp
  | zero => exact ⟨1, one_ne_zero, 0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, u, hu, hu'⟩ := hx
    obtain ⟨d, hd, v, hv, hv'⟩ := hy
    refine ⟨c * d, mul_ne_zero hc hd, d • u + c • v,
      Submodule.add_mem _ (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hv), ?_⟩
    rw [_root_.map_add (f := _), MvPolynomial.smul_eq_C_mul u d, MvPolynomial.smul_eq_C_mul v c,
      _root_.map_mul, _root_.map_mul, map_C, map_C, hu', hv']
    simp only [MvPolynomial.smul_eq_C_mul, eq_intCast, Int.cast_mul, MvPolynomial.C_mul]
    ring
  | smul q x _ hx =>
    obtain ⟨c, hc, u, hu, hu'⟩ := hx
    refine ⟨(q.den : ℤ) * c, mul_ne_zero (by exact_mod_cast q.den_nz) hc, q.num • u,
      Submodule.smul_mem _ _ hu, ?_⟩
    rw [MvPolynomial.smul_eq_C_mul u q.num, _root_.map_mul, map_C, hu']
    have hq : q * (q.den : ℚ) = (q.num : ℚ) := Rat.mul_den_eq_num q
    simp only [MvPolynomial.smul_eq_C_mul, eq_intCast, Int.cast_mul, Int.cast_natCast,
      MvPolynomial.C_mul, ← hq]
    ring

private theorem colAddGen_map_intCast {r n : ℕ} (l j : Fin n) (f : MvPolynomial (Fin r × Fin n) ℤ) :
    colAddGen ℚ (r := r) l j (map (Int.castRingHom ℚ) f) =
      map (Int.castRingHom ℚ) (colAddGen ℤ (r := r) l j f) := by
  induction f using MvPolynomial.induction_on
  next c =>
    simp [colAddGen]
  next p q hp hq =>
    rw [_root_.map_add (f := _), _root_.map_add (f := _), _root_.map_add (f := _), hp, hq, _root_.map_add (f := _)]
  next p v hp =>
    rw [_root_.map_mul, map_X, _root_.map_mul, _root_.map_mul, _root_.map_mul, hp]
    congr 1
    simp only [colAddGen, aeval_X]
    split_ifs <;> simp

private theorem map_intCast_mem_dualWeyl {r n : ℕ} (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) ℤ)
    (hf : f ∈ dualWeyl ℤ r n ν) : map (Int.castRingHom ℚ) f ∈ dualWeyl ℚ r n ν := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero,
    mem_weightedHomogeneousSubmodule] at hf ⊢
  obtain ⟨h1, h2⟩ := hf
  refine ⟨?_, ?_⟩
  · intro d hd
    apply h1
    intro h0
    apply hd
    rw [coeff_map, h0, _root_.map_zero]
  · intro l j hlj
    rw [colAddGen_map_intCast, h2 l j hlj, map_rename]

theorem weyl_module_rational : WeylRationalOf := by
  unfold WeylRationalOf WeylRational
  intro h r n hn ν hν f hf
  have hfQ : map (Int.castRingHom ℚ) f ∈ weyl ℚ r n hn ν := by
    rw [h r n hn ν hν]
    exact map_intCast_mem_dualWeyl ν f hf
  obtain ⟨c, hc, u, hu, hmap⟩ := lclosedeq_weyl_denom hn ν _ hfQ
  refine ⟨c, hc, ?_⟩
  have huf : u = c • f := by
    apply MvPolynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℚ))
    rw [hmap, _root_.map_zsmul]
    exact Int.cast_smul_eq_zsmul ℚ c _
  rw [← huf]
  exact hu

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lcpeel_support {B : Type*} [CommRing B] {r n : ℕ} (l j : Fin n) (a0 : Fin r) (k : ℕ)
    (g : MvPolynomial (Fin r × Fin n) B) (d : Fin r × Fin n →₀ ℕ)
    (hd : AddMonoidAlgebra.coeff (peel l j a0 k g) d ≠ 0) :
    ∃ m ∈ g.support, m (a0, l) = k ∧ d = (m.erase (a0, l)).erase (a0, j) := by
  unfold peel at hd
  rw [coeff_sum] at hd
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd
  obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
  refine ⟨m, hm1, hm2, ?_⟩
  rw [coeff_monomial] at hne
  split_ifs at hne with h
  · exact h.symm
  · exact absurd rfl hne

private theorem weight_single_eq_nsmul {σ M : Type*} [AddCommMonoid M] (w : σ → M) (s : σ) (c : ℕ) :
    Finsupp.weight w (Finsupp.single s c) = c • w s := by
  first
    | (rw [Finsupp.weight_apply, Finsupp.sum_single_index]; exact zero_smul ℕ (w s))
    | simp [Finsupp.weight_apply]

private theorem eq_erase_erase_add_single_add_single {r n : ℕ} (l j : Fin n) (hlj : l ≠ j) (a0 : Fin r)
    (m : Fin r × Fin n →₀ ℕ) :
    m = (m.erase (a0, l)).erase (a0, j) + Finsupp.single (a0, l) (m (a0, l)) +
      Finsupp.single (a0, j) (m (a0, j)) := by
  ext ⟨b, t⟩
  simp only [Finsupp.add_apply, Finsupp.erase_apply, Finsupp.single_apply, Prod.mk.injEq]
  by_cases hb : b = a0
  · subst hb
    by_cases hl : t = l
    · subst hl
      simp [hlj, Ne.symm hlj]
    · by_cases hj : t = j
      · subst hj
        simp [hl, Ne.symm hl]
      · simp [hl, hj, Ne.symm hl, Ne.symm hj]
  · simp [hb, Ne.symm hb]

private theorem weight_pairW_apply_eq_zero_of_vanish {r n : ℕ} (l j : Fin n) (a0 : Fin r)
    (d : Fin r × Fin n →₀ ℕ) (hl : d (a0, l) = 0) (hj : d (a0, j) = 0) :
    Finsupp.weight (pairW l j) d (a0, l) = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  dsimp only
  have hi0 : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
  obtain ⟨b, t⟩ := i
  by_cases ht : t = j
  · have hne : ¬ ((b, l) = (a0, l)) := by
      intro h
      simp only [Prod.mk.injEq] at h
      rw [h.1, ht] at hi0
      exact hi0 hj
    have hp : pairW (r := r) l j (b, t) = Finsupp.single (b, l) 1 := by
      simp [pairW, ht]
    rw [hp, Finsupp.smul_apply, Finsupp.single_apply, if_neg hne, smul_zero]
  · have hne : ¬ ((b, t) = (a0, l)) := by
      intro h
      rw [h] at hi0
      exact hi0 hl
    have hp : pairW (r := r) l j (b, t) = Finsupp.single (b, t) 1 := by
      simp [pairW, ht]
    rw [hp, Finsupp.smul_apply, Finsupp.single_apply, if_neg hne, smul_zero]

private theorem weight_pairW_eq_erase_of_split {r n : ℕ} (l j : Fin n) (hlj : l ≠ j) (a0 : Fin r)
    (m d ω : Fin r × Fin n →₀ ℕ) (hdl : d (a0, l) = 0) (hdj : d (a0, j) = 0)
    (hsplit : m = d + Finsupp.single (a0, l) (m (a0, l)) + Finsupp.single (a0, j) (m (a0, j)))
    (hw : Finsupp.weight (pairW l j) m = ω) :
    Finsupp.weight (pairW l j) d = ω.erase (a0, l) := by
  have hpl : pairW (r := r) l j (a0, l) = Finsupp.single (a0, l) 1 := by
    simp [pairW, hlj]
  have hpj : pairW (r := r) l j (a0, j) = Finsupp.single (a0, l) 1 := by
    simp [pairW]
  have key : ω = Finsupp.weight (pairW l j) d +
      Finsupp.single (a0, l) (m (a0, l) + m (a0, j)) := by
    rw [← hw]
    conv_lhs => rw [hsplit]
    rw [map_add (f := _), map_add (f := _), weight_single_eq_nsmul, weight_single_eq_nsmul, hpl, hpj]
    first
      | (rw [add_assoc, ← add_smul, Finsupp.smul_single, smul_eq_mul, mul_one])
      | (ext y
         simp only [Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
         split_ifs <;> ring)
  ext x
  by_cases hx : x = (a0, l)
  · rw [hx, Finsupp.erase_same]
    exact weight_pairW_apply_eq_zero_of_vanish l j a0 d hdl hdj
  · rw [Finsupp.erase_ne hx, key, Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm hx),
      add_zero]

theorem sliceHomogeneous : PeelHomog := by
  intro B _ r n l j hlj a0 ω k g hg
  refine ⟨?_, ?_⟩
  · intro d hd
    obtain ⟨m, hm, -, rfl⟩ := lcpeel_support l j a0 k g d hd
    exact weight_pairW_eq_erase_of_split l j hlj a0 m _ ω
      (by simp [Finsupp.erase_apply, hlj]) (by simp [Finsupp.erase_apply])
      (eq_erase_erase_add_single_add_single l j hlj a0 m) (hg (mem_support_iff.mp hm))
  · intro d hd
    obtain ⟨m, -, -, rfl⟩ :=
      lcpeel_support l j a0 k g d (mem_support_iff.mp hd)
    exact ⟨by simp [Finsupp.erase_apply, hlj], by simp [Finsupp.erase_apply]⟩

end Formalism.GradedWeylDivisibility
end
end

section

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem dualWeylModuleMap : DualWeylMap := by
  intro R S _ _ φ r n ν f hf
  rw [lsat_mem_dualWeyl] at hf ⊢
  refine ⟨lsat_isWH_map φ _ _ f hf.1, fun l j hlj => ?_⟩
  rw [← lsat_map_colAddGen, hf.2 l j hlj, map_rename]

end Formalism.GradedWeylDivisibility
end
end
