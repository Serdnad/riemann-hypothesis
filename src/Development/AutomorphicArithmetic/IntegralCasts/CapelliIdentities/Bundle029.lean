module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.NNReal.Defs
public import Mathlib.RingTheory.Valuation.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.Continuity
public import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section

section

theorem UpperTheory.Reformulated.B.Qk60.conj_eq_neg_of_sq :
    ∀ {z : ℂ} {d : ℕ},
    (0 : ℕ) < d → z ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  intro z d hd h
  have hd' : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    simpa [pow_two] using congrArg Complex.re h
  have him : z.re * z.im + z.im * z.re = 0 := by
    simpa [pow_two] using congrArg Complex.im h
  have h0 : z.re = 0 := by
    have hmul : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp hmul with h1 | h1
    · exact h1
    · rw [h1] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [h0]
  · simp
end

section

theorem UpperTheory.Reformulated.B.ConjEqNegOfSquare.conj_eq_neg_of_sq :
    ∀ {d : ℕ},
    (0 : ℕ) < d → ∀ {z : ℂ}, z ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  intro d hd z hz
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    have h := congrArg Complex.re hz
    simpa [pow_two] using h
  have him : z.re * z.im + z.im * z.re = 0 := by
    have h := congrArg Complex.im hz
    simpa [pow_two] using h
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h0 : z.re = 0 := by
    have hmul : z.re * z.im = 0 := by linarith [mul_comm z.im z.re]
    rcases mul_eq_zero.mp hmul with h | h
    · exact h
    · exfalso
      rw [h] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [h0]
  · simp
end

section

theorem UpperTheory.Reformulated.B.Qh17.conj_of_sq_neg :
    ∀ {t : ℂ} {r : ℝ},
    r < (0 : ℝ) → t ^ (2 : ℕ) = (↑r : ℂ) → (starRingEnd ℂ : ℂ → ℂ) t = -t := by
  intro t r hr h
  have h1 : t.re * t.re - t.im * t.im = r := by
    have := congrArg Complex.re h
    simpa [pow_two] using this
  have h2 : t.re * t.im + t.im * t.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two] using this
  have h3 : t.re = 0 := by
    have hm : t.re * t.im = 0 := by linarith [mul_comm t.im t.re]
    rcases mul_eq_zero.mp hm with h0 | h0
    · exact h0
    · exfalso
      rw [h0] at h1
      nlinarith [mul_self_nonneg t.re]
  apply Complex.ext
  · simp [h3]
  · simp
end

section

theorem UpperTheory.Reformulated.B.ConjEqNegOfSqEqNegNat₂.main :
    ∀ {d : ℕ}, (0 : ℕ) < d → ∀ {z : ℂ}, z ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  intro d hd z hz
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    have h := congrArg Complex.re hz
    simpa [pow_two] using h
  have him : z.re * z.im + z.im * z.re = 0 := by
    have h := congrArg Complex.im hz
    simpa [pow_two] using h
  have hprod : z.re * z.im = 0 := by linarith
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.mp hprod with h | h
    · exact h
    · rw [h] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [hre0]
  · simp
end

section

theorem UpperTheory.Reformulated.B.Ydc3.main :
    ∀ {d : ℕ}, (0 : ℕ) < d → ∀ {z : ℂ}, z ^ (2 : ℕ) = -(↑d : ℂ) → (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  intro d hd z hz
  have h1 : (z ^ 2).re = z.re * z.re - z.im * z.im := by
    rw [pow_two, Complex.mul_re]
  have h2 : (z ^ 2).im = z.re * z.im + z.im * z.re := by
    rw [pow_two, Complex.mul_im]
  have e1 : (-(d : ℂ)).re = -(d : ℝ) := by simp
  have e2 : (-(d : ℂ)).im = 0 := by simp
  rw [hz, e1] at h1
  rw [hz, e2] at h2
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hm : z.re * z.im = 0 := by linarith
  have ha : z.re = 0 := by
    rcases mul_eq_zero.mp hm with h | h
    · exact h
    · exfalso
      have : z.im * z.im = 0 := by rw [h]; ring
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [ha]
  · simp
end

section

theorem UpperTheory.Reformulated.B.Ra8.star_eq_of_sq :
    ∀ {z : ℂ} {r : ℝ},
    (0 : ℝ) ≤ r → z * z = (↑r : ℂ) → Star.star z = z := by
  intro z r hr h
  have hre : z.re * z.re - z.im * z.im = r := by
    simpa using congrArg Complex.re h
  have him : z.re * z.im + z.im * z.re = 0 := by
    simpa using congrArg Complex.im h
  have h0 : z.im = 0 := by
    by_contra hne
    have h1 : z.re * z.im = 0 := by linarith [mul_comm z.re z.im]
    have h2 : z.re = 0 := (mul_eq_zero.mp h1).resolve_right hne
    have h3 : 0 < z.im * z.im := mul_self_pos.mpr hne
    rw [h2] at hre
    linarith
  exact Complex.conj_eq_iff_im.mpr h0
end

section

theorem UpperTheory.Reformulated.B.Qh56.conj_of_sq :
    ∀ {w : ℂ} {q : ℕ},
    (0 : ℕ) < q → w ^ (2 : ℕ) = (↑q : ℂ) → (starRingEnd ℂ : ℂ → ℂ) w = w := by
  intro w q _ h
  have hs : ((Real.sqrt q : ℝ) : ℂ) ^ 2 = (q : ℂ) := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg q), Complex.ofReal_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (h.trans hs.symm) with hw | hw
  · rw [hw, Complex.conj_ofReal]
  · rw [hw, map_neg, Complex.conj_ofReal]
end

section

theorem UpperTheory.Reformulated.B.ProdSubProdLeOfFactorsClose.main.{u_1} :
    ∀ {ι : Type u_1} (ν : Valuation ℂ NNReal) (s : Finset ι) (f g : ι → ℂ) (m : NNReal),
      (∀ i ∈ s, (ν : ℂ → NNReal) (f i) ≤ (1 : NNReal)) →
        (∀ i ∈ s, (ν : ℂ → NNReal) (g i) ≤ (1 : NNReal)) →
          (∀ i ∈ s, (ν : ℂ → NNReal) (f i - g i) ≤ m) →
            (ν : ℂ → NNReal) (∏ i ∈ s, f i) ≤ (1 : NNReal) ∧
              (ν : ℂ → NNReal) (∏ i ∈ s, g i) ≤ (1 : NNReal) ∧ (ν : ℂ → NNReal) (∏ i ∈ s, f i - ∏ i ∈ s, g i) ≤ m := by
  classical
  intro ι ν s f g m
  induction s using Finset.induction_on with
  | empty =>
    intro _ _ _
    simp
  | insert a s ha ih =>
    intro hf hg hfg
    obtain ⟨h1, h2, h3⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
    have fa := hf a (Finset.mem_insert_self a s)
    have ga := hg a (Finset.mem_insert_self a s)
    have fga := hfg a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    refine ⟨?_, ?_, ?_⟩
    · rw [map_mul]
      calc ν (f a) * ν (∏ i ∈ s, f i) ≤ 1 * 1 := mul_le_mul' fa h1
        _ = 1 := one_mul 1
    · rw [map_mul]
      calc ν (g a) * ν (∏ i ∈ s, g i) ≤ 1 * 1 := mul_le_mul' ga h2
        _ = 1 := one_mul 1
    · have e : f a * ∏ i ∈ s, f i - g a * ∏ i ∈ s, g i
          = f a * (∏ i ∈ s, f i - ∏ i ∈ s, g i) + (f a - g a) * ∏ i ∈ s, g i := by ring
      rw [e]
      refine le_trans (Valuation.map_add ν _ _) (max_le ?_ ?_)
      · rw [map_mul]
        calc ν (f a) * ν (∏ i ∈ s, f i - ∏ i ∈ s, g i) ≤ 1 * m := mul_le_mul' fa h3
          _ = m := one_mul m
      · rw [map_mul]
        calc ν (f a - g a) * ν (∏ i ∈ s, g i) ≤ m * 1 := mul_le_mul' fga h2
          _ = m := mul_one m
end

section

noncomputable def UpperTheory.Reformulated.B.Qe19.LiftEquiv :
    Prop :=
    ∀ (Γ X : Type) [inst : Group Γ] [inst_1 : MulAction Γ X],
      (∀ (x : X), Finite ↥(MulAction.stabilizer Γ x)) →
        ∀ (A B : Rep.{0, 0, 0} ℂ Γ) (f : A ⟶ B),
          Function.Surjective (⇑(Rep.Hom.hom f) : (↑A : Type) → (↑B : Type)) →
            ∀ (φ : X → (↑B : Type)),
              (∀ (g : Γ) (x : X),
                  φ (g • x) = ((B.ρ : Γ → (↑B : Type) →ₗ[ℂ] (↑B : Type)) g : (↑B : Type) → (↑B : Type)) (φ x)) →
                ∃ (ψ : X → (↑A : Type)),
                  (∀ (g : Γ) (x : X),
                      ψ (g • x) = ((A.ρ : Γ → (↑A : Type) →ₗ[ℂ] (↑A : Type)) g : (↑A : Type) → (↑A : Type)) (ψ x)) ∧
                    ∀ (x : X), (Rep.Hom.hom f : (↑A : Type) → (↑B : Type)) (ψ x) = φ x

private theorem UpperTheory.Reformulated.B.Qe19.fixed_lift {Γ : Type} [Group Γ] (H : Subgroup Γ) [Finite H]
    (A B : Rep.{0, 0, 0} ℂ Γ) (f : A ⟶ B) (hf : Function.Surjective (Rep.Hom.hom f))
    (b : B) (hb : ∀ h ∈ H, B.ρ h b = b) :
    ∃ a : A, (∀ h ∈ H, A.ρ h a = a) ∧ (Rep.Hom.hom f) a = b := by
  classical
  haveI := Fintype.ofFinite H
  obtain ⟨a, ha⟩ := hf b
  have hc : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨(Fintype.card H : ℂ)⁻¹ • ∑ k : H, A.ρ k a, ?_, ?_⟩
  · intro h hh

    rw [map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨h, hh⟩ : H)) _ _ ?_
    intro k
    simp [map_mul]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [map_smul, map_sum]
    have h1 : ∀ k : H, (Rep.Hom.hom f) (A.ρ k a) = b := by
      intro k
      rw [Rep.hom_comm_apply, ha, hb k k.2]
    simp only [h1, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem UpperTheory.Reformulated.B.Qe19.pins_of_closed_subgroup_padic_character_inv :
    UpperTheory.Reformulated.B.Qe19.LiftEquiv := by
  intro Γ X _ _ hfin A B f hf φ hφ
  have h1 : ∀ x : X, ∃ a : A, (∀ h ∈ MulAction.stabilizer Γ x, A.ρ h a = a) ∧
      (Rep.Hom.hom f) a = φ x := by
    intro x
    haveI := hfin x
    refine UpperTheory.Reformulated.B.Qe19.fixed_lift _ A B f hf (φ x) ?_
    intro h hh
    rw [← hφ, MulAction.mem_stabilizer_iff.mp hh]
  choose a ha hfa using h1
  have h2 : ∃ r : X → X, (∀ (g : Γ) (x : X), r (g • x) = r x) ∧ ∀ x, ∃ g : Γ, g • r x = x := by
    refine ⟨fun x => (Quotient.mk (MulAction.orbitRel Γ X) x).out, ?_, ?_⟩
    · intro g x
      have : Quotient.mk (MulAction.orbitRel Γ X) (g • x) = Quotient.mk (MulAction.orbitRel Γ X) x :=
        Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit x g))
      simp only [this]
    · intro x
      have h := Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel Γ X) x)).symm
      exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)
  obtain ⟨r, hr, hg⟩ := h2
  choose s hs using hg
  refine ⟨fun x => A.ρ (s x) (a (r x)), ?_, ?_⟩
  · intro g x
    have hm : (s (g • x))⁻¹ * (g * s x) ∈ MulAction.stabilizer Γ (r x) := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hs x, inv_smul_eq_iff, ← hr g x, hs]
    have h3 := congrArg (A.ρ (s (g • x))) (ha (r x) _ hm)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left, map_mul, Module.End.mul_apply] at h3
    simp only [hr g x]
    exact h3.symm
  · intro x
    show (Rep.Hom.hom f) (A.ρ (s x) (a (r x))) = φ x
    rw [Rep.hom_comm_apply, hfa, ← hφ, hs]
end

section

theorem UpperTheory.Reformulated.B.Qh57.exists_perm_of_map_eq :
    ∀ {n : ℕ} (a b : Fin n → ℂ),
    Multiset.map a Finset.univ.val = Multiset.map b Finset.univ.val →
      ∃ (e : Equiv.Perm (Fin n)), ∀ (i : Fin n), b ((e : Fin n → Fin n) i) = a i := by
  intro n a b h
  classical
  have key : ∀ (f : Fin n → ℂ) (c : ℂ),
      Fintype.card {i // f i = c} = Multiset.count c (Multiset.map f Finset.univ.val) := by
    intro f c
    rw [Fintype.card_subtype, Multiset.count_map, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun _ _ => eq_comm)
  have hc : ∀ c : ℂ, Fintype.card {i // a i = c} = Fintype.card {i // b i = c} := by
    intro c
    rw [key a c, key b c, h]
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩
end

section

theorem UpperTheory.Reformulated.B.Yoa3.exists_perm_of_map_eq :
    ∀ {n : ℕ} {z z' : Fin n → ℂˣ},
      Multiset.map (fun (i : Fin n) ↦ (↑(z i) : ℂ)) Finset.univ.val =
          Multiset.map (fun (i : Fin n) ↦ (↑(z' i) : ℂ)) Finset.univ.val →
        ∃ (σ : Equiv.Perm (Fin n)), z' = z ∘ (⇑σ : Fin n → Fin n) := by
  classical
  intro n z z' h
  have key : ∀ (w : Fin n → ℂˣ) (c : ℂ),
      Fintype.card {i : Fin n // (w i : ℂ) = c} =
        Multiset.count c (Multiset.map (fun (i : Fin n) ↦ (↑(w i) : ℂ)) Finset.univ.val) := by
    intro w c
    rw [Multiset.count_map, Fintype.card_subtype, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun _ _ => eq_comm)
  have hc : ∀ c : ℂ, Fintype.card {i : Fin n // (z' i : ℂ) = c} =
      Fintype.card {i : Fin n // (z i : ℂ) = c} := by
    intro c
    rw [key, key, h]
  let e : ∀ c : ℂ, {i : Fin n // (z' i : ℂ) = c} ≃ {i : Fin n // (z i : ℂ) = c} :=
    fun c => Fintype.equivOfCardEq (hc c)
  refine ⟨Equiv.ofFiberEquiv (f := fun i => (z' i : ℂ)) (g := fun i => (z i : ℂ)) e, ?_⟩
  funext i
  apply Units.ext
  exact (Equiv.ofFiberEquiv_map (f := fun i => (z' i : ℂ)) (g := fun i => (z i : ℂ)) e i).symm
end

section

theorem UpperTheory.Reformulated.B.Yhd8.main :
    ∀ {n : ℕ} (g g' D : Matrix (Fin n) (Fin n) ℂ),
      g' * g = (1 : Matrix (Fin n) (Fin n) ℂ) →
        g * g' = (1 : Matrix (Fin n) (Fin n) ℂ) → ∀ (k : ℕ), (g' * D * g) ^ k = g' * D ^ k * g := by
  intro n g g' D h1 h2 k
  induction k with
  | zero => simp [h1]
  | succ k ih =>
    rw [pow_succ, ih, pow_succ]
    calc g' * D ^ k * g * (g' * D * g) = g' * D ^ k * (g * g') * D * g := by
          simp only [Matrix.mul_assoc]
      _ = g' * (D ^ k * D) * g := by rw [h2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
end
