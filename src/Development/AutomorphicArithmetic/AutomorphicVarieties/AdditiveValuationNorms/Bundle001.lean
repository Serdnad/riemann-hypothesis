module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
public import Mathlib.RingTheory.Nakayama
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.AlgebraMap

@[expose] public section

section

open UpperTheory.V UpperTheory.V.PropA

private theorem dvd_of_norm_le' {l : ℕ} [Fact l.Prime] {d y : ℤ_[l]} (h : ‖y‖ ≤ ‖d‖) : d ∣ y := by
  by_cases hy : y = 0
  · subst hy
    exact dvd_zero d
  by_cases hd : d = 0
  · subst hd
    rw [norm_zero, norm_le_zero_iff] at h
    exact absurd h hy
  have hav : ∀ x : ℤ_[l], x ≠ 0 → IsDiscreteValuationRing.addVal ℤ_[l] x = x.valuation :=
    fun x hx => IsDiscreteValuationRing.addVal_def x (PadicInt.unitCoeff hx) PadicInt.irreducible_p _
      (PadicInt.unitCoeff_spec hx)
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, hav d hd, hav y hy, Nat.cast_le]
  rw [PadicInt.norm_eq_zpow_neg_valuation hd, PadicInt.norm_le_pow_iff_le_valuation y hy] at h
  exact h

private theorem vl_prod {l : ℕ} [Fact l.Prime] {ι : Type} (s : Finset ι) (f : ι → ℤ_[l]) :
    vl l (∏ i ∈ s, f i) = ∑ i ∈ s, vl l (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [vl]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ← ih]
    exact IsDiscreteValuationRing.addVal_mul

theorem UpperTheory.V.PropA.normVal :
    ∀ (l : ℕ) [Fact l.Prime] (R c : ℕ) (d : ℤ_[l]) (x : Fin R → ℤ_[l]),
      ∏ i, (((l : ℝ) ^ c)⁻¹ * ‖x i‖) ≤ ‖d‖ → vl l d ≤ ∑ i, ((c : ℕ∞) + vl l (x i)) := by
  intro l _ R c d x h
  have h1 : ‖∏ i, ((l : ℤ_[l]) ^ c * x i)‖ = ∏ i, (((l : ℝ) ^ c)⁻¹ * ‖x i‖) := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [norm_mul, norm_pow, PadicInt.norm_p, inv_pow]
  have h2 : d ∣ ∏ i, ((l : ℤ_[l]) ^ c * x i) := dvd_of_norm_le' (h1 ▸ h)
  have h3 : vl l (∏ i, ((l : ℤ_[l]) ^ c * x i)) = ∑ i, ((c : ℕ∞) + vl l (x i)) := by
    rw [vl_prod]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := (PadicInt.irreducible_p (p := l)).addVal_pow c
    unfold vl
    rw [IsDiscreteValuationRing.addVal_mul, this]
  rw [← h3]
  exact IsDiscreteValuationRing.addVal_le_iff_dvd.mpr h2
end

section

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.phi :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] [Module.Finite ℤ_[l] X] (w : Module.End ℤ_[l] X), InPow 2 (w - 1) →
      LinearMap.range ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X)) ≤ LinearMap.range (∑ i ∈ Finset.range l, w ^ i) := by
  intro l _ X _ _ _ w hw
  have hpow : ∀ (i : ℕ) (x : X), ∃ y : X, (w ^ i) x = x + (l : ℤ_[l]) ^ 2 • y := by
    intro i
    induction i with
    | zero => intro x; exact ⟨0, by simp⟩
    | succ i ih =>
      intro x
      obtain ⟨y, hy⟩ := ih (w x)
      obtain ⟨z, hz⟩ := hw x
      refine ⟨z + y, ?_⟩
      rw [pow_succ, Module.End.mul_apply, hy, smul_add, ← hz]
      simp only [LinearMap.sub_apply, Module.End.one_apply]
      abel
  have hsum : ∀ (n : ℕ) (x : X), ∃ y : X,
      (∑ i ∈ Finset.range n, w ^ i) x = (n : ℤ_[l]) • x + (l : ℤ_[l]) ^ 2 • y := by
    intro n x
    induction n with
    | zero => exact ⟨0, by simp⟩
    | succ n ih =>
      obtain ⟨y, hy⟩ := ih
      obtain ⟨z, hz⟩ := hpow n x
      refine ⟨y + z, ?_⟩
      rw [Finset.sum_range_succ, LinearMap.add_apply, hy, hz, smul_add, Nat.cast_succ, add_smul, one_smul]
      abel
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {(l : ℤ_[l])}) ?_ ?_ ?_
  · exact IsNoetherian.noetherian _
  · rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, PadicInt.maximalIdeal_eq_span_p]
  · rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := hsum l x
    have e : ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X)) x
        = (∑ i ∈ Finset.range l, w ^ i) x + (l : ℤ_[l]) • (((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X)) (-y)) := by
      rw [hy]
      simp only [LinearMap.smul_apply, Module.End.one_apply, smul_neg, pow_two, mul_smul]
      abel
    rw [e]
    exact Submodule.add_mem_sup (LinearMap.mem_range_self _ _)
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (LinearMap.mem_range_self _ _))
end

section

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.cokL :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (R : ℕ), GenBy l R X → cokLen ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X)) ≤ R := by
  intro l _ X _ _ R hgen
  obtain ⟨π, hπ⟩ := hgen
  classical
  let I : Submodule ℤ_[l] ℤ_[l] := IsLocalRing.maximalIdeal ℤ_[l]
  have hsimple : IsSimpleModule ℤ_[l] (ℤ_[l] ⧸ I) :=
    isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 (IsLocalRing.maximalIdeal.isMaximal ℤ_[l]))
  let P : Submodule ℤ_[l] (Fin R → ℤ_[l]) := Submodule.pi Set.univ (fun _ => I)
  let q : Submodule ℤ_[l] X := LinearMap.range ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X))
  have hle : P ≤ q.comap π := by
    intro v hv
    rw [Submodule.mem_pi] at hv
    have hex : ∀ i, ∃ w : ℤ_[l], v i = (l : ℤ_[l]) * w := by
      intro i
      have hi := hv i (Set.mem_univ i)
      change v i ∈ IsLocalRing.maximalIdeal ℤ_[l] at hi
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hi
      obtain ⟨a, ha⟩ := hi
      exact ⟨a, by rw [← ha, mul_comm]⟩
    choose w hw using hex
    have hv' : v = (l : ℤ_[l]) • w := funext fun i => by simp [hw i]
    rw [Submodule.mem_comap, LinearMap.mem_range]
    refine ⟨π w, ?_⟩
    rw [LinearMap.smul_apply, Module.End.one_apply, hv', map_smul]
  have hφ : Function.Surjective (P.mapQ q π hle) := by
    intro z
    refine Submodule.Quotient.induction_on _ z ?_
    intro x
    obtain ⟨v, rfl⟩ := hπ x
    exact ⟨Submodule.Quotient.mk v, Submodule.mapQ_apply _ _ _ _⟩
  have h1 := Module.length_le_of_surjective (P.mapQ q π hle) hφ
  have h2 : Module.length ℤ_[l] ((Fin R → ℤ_[l]) ⧸ P) = R := by
    rw [(Submodule.quotientPi (fun _ : Fin R => I)).length_eq, Module.length_pi_of_fintype]
    simp [Module.length_eq_one]
  exact h1.trans h2.le
end

section

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.frob :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (g : Module.End ℤ_[l] X) (k : ℕ),
      InPow 1 ((g - 1) ^ l ^ k) ↔ InPow 1 (g ^ l ^ k - 1) := by
  intro l _ X _ _ g k
  have hpoly : (Polynomial.C (l : ℤ)) ∣
      ((Polynomial.X - 1) ^ l ^ k - (Polynomial.X ^ l ^ k - 1) : Polynomial ℤ) := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    have hmap : Polynomial.map (Int.castRingHom (ZMod l))
        ((Polynomial.X - 1) ^ l ^ k - (Polynomial.X ^ l ^ k - 1) : Polynomial ℤ) = 0 := by
      simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one]
      rw [sub_pow_char_pow, one_pow, sub_self]
    have hc := congrArg (fun P => _root_.AddMonoidAlgebra.coeff (M := ℕ) P i) hmap
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at hc
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).1 hc
  obtain ⟨Q, hQ⟩ := hpoly
  have key : (g - 1) ^ l ^ k - (g ^ l ^ k - 1) = (l : Module.End ℤ_[l] X) * Polynomial.aeval g Q := by
    have := congrArg (Polynomial.aeval g) hQ
    simpa using this
  have step : ∀ f f' : Module.End ℤ_[l] X, (∃ h : Module.End ℤ_[l] X, f - f' = (l : Module.End ℤ_[l] X) * h) →
      InPow 1 f' → InPow 1 f := by
    rintro f f' ⟨h, hh⟩ H x
    obtain ⟨y, hy⟩ := H x
    refine ⟨y + h x, ?_⟩
    have hf : f = (l : Module.End ℤ_[l] X) * h + f' := eq_add_of_sub_eq hh
    rw [pow_one] at hy ⊢
    rw [hf, LinearMap.add_apply, Module.End.mul_apply, Module.End.natCast_apply, hy, smul_add,
      Nat.cast_smul_eq_nsmul ℤ_[l] l (h x), add_comm]
  constructor
  · exact step _ _ ⟨-Polynomial.aeval g Q, by rw [mul_neg, ← key, neg_sub]⟩
  · exact step _ _ ⟨Polynomial.aeval g Q, key⟩
end

section

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.mono :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (g : Module.End ℤ_[l] X) (a b : ℕ), a ∣ b →
      cokLen (g ^ a - 1) ≤ cokLen (g ^ b - 1) := by
  intro l _ X _ _ g a b hab
  apply cokLen_le_of_range_le
  obtain ⟨k, rfl⟩ := hab
  rw [pow_mul, ← mul_geom_sum]
  exact LinearMap.range_comp_le_range _ _
end

section

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.powIn :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (w : Module.End ℤ_[l] X),
      (∀ k n : ℕ, InPow k (w - 1) → InPow k (w ^ n - 1)) ∧ (InPow 1 (w - 1) → InPow 2 (w ^ l - 1)) := by
  intro l _ X _ _ w
  refine ⟨?_, ?_⟩
  · intro k n H x
    obtain ⟨y, hy⟩ := H x
    refine ⟨(∑ i ∈ Finset.range n, w ^ i) y, ?_⟩
    rw [← geom_sum_mul, Module.End.mul_apply, hy, map_smul]
  · intro H x
    obtain ⟨y, hy⟩ := H x
    obtain ⟨y', hy'⟩ := H y
    rw [pow_one] at hy hy'
    refine ⟨y + ∑ i ∈ Finset.range l, (∑ j ∈ Finset.range i, w ^ j) y', ?_⟩
    have hw : ∀ i, (w ^ i) y = y + (l : ℤ_[l]) • (∑ j ∈ Finset.range i, w ^ j) y' := by
      intro i
      have h0 : (w ^ i - 1) y = (∑ j ∈ Finset.range i, w ^ j) ((w - 1) y) := by
        rw [← Module.End.mul_apply, geom_sum_mul]
      rw [hy', map_smul] at h0
      rw [← h0, LinearMap.sub_apply, Module.End.one_apply, add_sub_cancel]
    rw [← geom_sum_mul, Module.End.mul_apply, hy, map_smul, LinearMap.sum_apply]
    simp_rw [hw]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, ← Finset.smul_sum,
      ← Nat.cast_smul_eq_nsmul ℤ_[l], ← smul_add, pow_two, mul_smul]
end
