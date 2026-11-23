module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Bundle001
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal
public import Mathlib.RingTheory.Filtration

@[expose] public section

section

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem inf_pow_bot (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R)
    (h : maximalIdeal R * I = ⊥) : ∃ N : ℕ, ∀ x ∈ I, x ∈ maximalIdeal R ^ N → x = 0 := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal R) (I : Submodule R R)
  refine ⟨k + 1, fun x hxI hxm => ?_⟩
  have hx : x ∈ (maximalIdeal R ^ (k + 1) • ⊤ ⊓ (I : Submodule R R)) :=
    ⟨by simpa [smul_eq_mul] using hxm, hxI⟩
  rw [hk (k + 1) (by omega), Nat.add_sub_cancel_left, pow_one] at hx
  have hmem : x ∈ maximalIdeal R • (I : Submodule R R) := Submodule.smul_mono le_rfl inf_le_right hx
  rw [smul_eq_mul, h] at hmem
  simpa using hmem

theorem UpperTheory.V.Ws.X1.contLift :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → (∀ (S : Type) [TopologicalSpace S] (x : S → R), AdicCont (maximalIdeal R) x → ∃ y : S → A, AdicCont (maximalIdeal A) y ∧ ∀ s, p (y s) = x s) ∧ ∀ (S : Type) [TopologicalSpace S] (y : S → A), AdicCont (maximalIdeal A) y → (∀ s, p (y s) = 0) → IsLocallyConstant y := by
  intro Λ _ _ _ _ A R _ _ _ _ _ _ p hp hK
  haveI : IsNoetherianRing A := IsCO.toIsNoetherian Λ
  obtain ⟨N0, hN0⟩ := inf_pow_bot A (RingHom.ker p) hK
  have hm : ∀ a : A, a ∈ maximalIdeal A ↔ p a ∈ maximalIdeal R := by
    intro a
    rw [← res_eq_zero_iff Λ A, ← res_eq_zero_iff Λ R, res_map]
  have hmap1 : Ideal.map p (maximalIdeal A) = maximalIdeal R := by
    ext r
    rw [Ideal.mem_map_iff_of_surjective p hp]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (hm a).mp ha
    · intro hr
      obtain ⟨a, rfl⟩ := hp r
      exact ⟨a, (hm a).mpr hr, rfl⟩
  have hmap : ∀ n, ∀ r ∈ maximalIdeal R ^ n, ∃ z ∈ maximalIdeal A ^ n, p z = r := by
    intro n r hr
    rw [← hmap1, ← Ideal.map_pow, Ideal.mem_map_iff_of_surjective p hp] at hr
    exact hr
  choose ρ hρ using fun c : R ⧸ maximalIdeal R ^ N0 => Ideal.Quotient.mk_surjective c
  choose l hl using fun c : R ⧸ maximalIdeal R ^ N0 => hp (ρ c)
  have hu : ∀ r : R, ∃ z ∈ maximalIdeal A ^ N0, p z = r - ρ (Ideal.Quotient.mk _ r) := by
    intro r
    apply hmap
    rw [← Ideal.Quotient.eq, hρ]
  choose u hu1 hu2 using hu
  let σ : R → A := fun r => l (Ideal.Quotient.mk _ r) + u r
  have hpσ : ∀ r, p (σ r) = r := by
    intro r
    simp only [σ, map_add (f := _), hl, hu2]
    ring
  have hL : ∀ M, N0 ≤ M → ∀ r r' : R, r - r' ∈ maximalIdeal R ^ M → σ r - σ r' ∈ maximalIdeal A ^ M := by
    intro M hM r r' h
    have hq : (Ideal.Quotient.mk (maximalIdeal R ^ N0) r) = Ideal.Quotient.mk _ r' :=
      Ideal.Quotient.eq.mpr (Ideal.pow_le_pow_right hM h)
    obtain ⟨z, hz, hpz⟩ := hmap M _ h
    have hzero : z - (u r - u r') = 0 := by
      apply hN0
      · rw [RingHom.mem_ker]
        simp only [map_sub]
        rw [hpz, hu2, hu2, hq]
        ring
      · exact sub_mem (Ideal.pow_le_pow_right hM hz) (sub_mem (hu1 r) (hu1 r'))
    have hz' : u r - u r' = z := (sub_eq_zero.mp hzero).symm
    simp only [σ]
    rw [hq, add_sub_add_left_eq_sub, hz']
    exact hz
  refine ⟨?_, ?_⟩
  · intro S _ x hx
    refine ⟨fun s => σ (x s), ?_, fun s => hpσ _⟩
    intro n
    have hc := hx (max n N0)
    rw [IsLocallyConstant.iff_eventually_eq] at hc ⊢
    intro s
    filter_upwards [hc s] with s' hs'
    have h1 := Ideal.Quotient.eq.mp hs'
    have h2 := hL (max n N0) (le_max_right _ _) _ _ h1
    exact Ideal.Quotient.eq.mpr (Ideal.pow_le_pow_right (le_max_left _ _) h2)
  · intro S _ y hy h0
    have hc := hy N0
    rw [IsLocallyConstant.iff_eventually_eq] at hc ⊢
    intro s
    filter_upwards [hc s] with s' hs'
    have h1 := Ideal.Quotient.eq.mp hs'
    have h2 : y s' - y s = 0 := by
      apply hN0 _ _ h1
      rw [RingHom.mem_ker, map_sub, h0, h0, sub_zero]
    exact sub_eq_zero.mp h2
end

section

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.X1.coefEx :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {A : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] (K : Ideal A), maximalIdeal A * K = ⊥ → ∀ (κ : Type) [Fintype κ] (ε : κ → A), K = Ideal.span (Set.range ε) → (∀ c : κ → Λ, ∑ u, c u • ε u = 0 → ∀ u, c u ∈ maximalIdeal Λ) → ∃ co : κ → A → ResidueField Λ, (∀ u, ∀ x ∈ K, ∀ y ∈ K, co u (x + y) = co u x + co u y) ∧ (∀ u (a : A), ∀ x ∈ K, co u (a * x) = res Λ A a * co u x) ∧ ∀ x ∈ K, ∃ a : κ → Λ, (∀ u, residue Λ (a u) = co u x) ∧ x = ∑ u, a u • ε u := by
  intro Λ _ _ A _ _ _ K hK κ _ ε hspan hind
  classical
  have hkill : ∀ m ∈ maximalIdeal A, ∀ e ∈ K, m * e = 0 := by
    intro m hm e he
    have h := Ideal.mul_mem_mul hm he
    rw [hK] at h
    exact (Submodule.mem_bot A).mp h
  have hsc : ∀ b : A, ∃ l : Λ, b - algebraMap Λ A l ∈ maximalIdeal A := fun b => IsCO.res_surj (O := Λ) b
  have hact : ∀ b : A, ∀ l : Λ, b - algebraMap Λ A l ∈ maximalIdeal A → ∀ e ∈ K, b * e = l • e := by
    intro b l hb e he
    have h := hkill _ hb e he
    rw [sub_mul] at h
    rw [Algebra.smul_def]
    exact sub_eq_zero.mp h
  have hres : ∀ b : A, ∀ l : Λ, b - algebraMap Λ A l ∈ maximalIdeal A → res Λ A b = residue Λ l := by
    intro b l hb
    have h := (res_eq_zero_iff Λ A _).mpr hb
    rw [map_sub, AlgHom.commutes, sub_eq_zero] at h
    rw [h]
    rfl
  have hex : ∀ x ∈ K, ∃ a : κ → Λ, x = ∑ u, a u • ε u := by
    intro x hx
    have hx' := hx
    rw [hspan] at hx'
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hx'
    choose l hl using fun u => hsc (b u)
    refine ⟨l, ?_⟩
    rw [← hb]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [smul_eq_mul]
    refine hact _ _ (hl u) _ ?_
    rw [hspan]
    exact Ideal.subset_span ⟨u, rfl⟩
  have huniq : ∀ a a' : κ → Λ, ∑ u, a u • ε u = ∑ u, a' u • ε u →
      ∀ u, residue Λ (a u) = residue Λ (a' u) := by
    intro a a' h u
    have h0 := hind (a - a') (by simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]) u
    rw [← sub_eq_zero, ← map_sub]
    exact (residue_eq_zero_iff _).mpr h0
  let co : κ → A → ResidueField Λ := fun u x => if h : x ∈ K then residue Λ ((hex x h).choose u) else 0
  have hco : ∀ x (h : x ∈ K) (a : κ → Λ), x = ∑ u, a u • ε u → ∀ u, co u x = residue Λ (a u) := by
    intro x h a hx u
    simp only [co, dif_pos h]
    exact huniq _ _ ((hex x h).choose_spec.symm.trans hx) u
  refine ⟨co, ?_, ?_, ?_⟩
  · intro u x hx y hy
    obtain ⟨a, ha⟩ := hex x hx
    obtain ⟨b, hb⟩ := hex y hy
    rw [hco x hx a ha, hco y hy b hb, hco (x + y) (K.add_mem hx hy) (a + b)
      (by rw [ha, hb, ← Finset.sum_add_distrib]; simp [add_smul]), Pi.add_apply, map_add (f := _)]
  · intro u c x hx
    obtain ⟨a, ha⟩ := hex x hx
    obtain ⟨l, hl⟩ := hsc c
    rw [hco x hx a ha, hco (c * x) (K.mul_mem_left c hx) (l • a) ?_, hres c l hl, Pi.smul_apply, smul_eq_mul,
      map_mul]
    rw [hact c l hl x hx, ha, Finset.smul_sum]
    simp [smul_smul]
  · intro x hx
    obtain ⟨a, ha⟩ := hex x hx
    exact ⟨a, fun u => (hco x hx a ha u).symm, ha⟩
end
