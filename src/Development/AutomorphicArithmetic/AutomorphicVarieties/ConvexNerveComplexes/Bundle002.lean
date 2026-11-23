module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.Bundle001
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Convex.KreinMilman
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Analysis.Convex.Extreme

@[expose] public section

section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.acyc_union :
    ∀ {I : Type} (A B : ∀ n, Set (Fin n → I)), FaceClosed A → FaceClosed B → Acyc A → Acyc B → Acyc (fun n => A n ∩ B n) → Acyc (fun n => A n ∪ B n) := by
  intro I A B hA hB hAc hBc hABc
  refine ⟨?_, ?_⟩
  · intro c hc
    rw [Finsupp.supported_union, Submodule.mem_sup] at hc
    obtain ⟨y, hy, z, hz, rfl⟩ := hc
    obtain ⟨f, hf, rfl⟩ := hAc.1 y hy
    obtain ⟨g, hg, rfl⟩ := hBc.1 z hz
    refine ⟨f + g, ?_, map_add _ _ _⟩
    rw [Finsupp.supported_union]
    exact Submodule.add_mem_sup hf hg
  · intro n c hc hcyc
    rw [Finsupp.supported_union, Submodule.mem_sup] at hc
    obtain ⟨y, hy, z, hz, rfl⟩ := hc
    rw [map_add (f := _)] at hcyc
    have hdA : bd I n y ∈ Finsupp.supported ℤ ℤ (A n) := bd_mem hA n y hy
    have hdB : bd I n y ∈ Finsupp.supported ℤ ℤ (B n) := by
      rw [eq_neg_of_add_eq_zero_left hcyc]
      exact Submodule.neg_mem _ (bd_mem hB n z hz)
    have hd : bd I n y ∈ Finsupp.supported ℤ ℤ (A n ∩ B n) := by
      rw [Finsupp.supported_inter]
      exact ⟨hdA, hdB⟩
    obtain ⟨e, he, hee⟩ : ∃ e ∈ Finsupp.supported ℤ ℤ (A (n + 1) ∩ B (n + 1)), bd I n e = bd I n y := by
      cases n with
      | zero => exact hABc.1 _ hd
      | succ m => exact hABc.2 m _ hd (bd_bd I m y)
    rw [Finsupp.supported_inter] at he
    obtain ⟨f, hf, hfe⟩ := hAc.2 n (y - e) (Submodule.sub_mem _ hy he.1) (by rw [map_sub, hee, sub_self])
    obtain ⟨g, hg, hge⟩ := hBc.2 n (z + e) (Submodule.add_mem _ hz he.2) (by rw [map_add (f := _), hee, add_comm]; exact hcyc)
    refine ⟨f + g, ?_, ?_⟩
    · rw [Finsupp.supported_union]
      exact Submodule.add_mem_sup hf hg
    · rw [map_add (f := _), hfe, hge]
      abel
end

section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.simp_span :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : Y → E →L[ℝ] ℝ} {T : Set E}, LocFin q → ∀ (n : ℕ) (t : Fin (n + 1) → Vert q), t ∈ simp q T (n + 1) → ∀ k ∈ T, (∀ y, (∀ j, q y (t j).1 = 1) → q y k = 0) → k = 0 := by
  intro E Y _ _ q T hq n t ht k hk hkq
  obtain ⟨x, hx, hxt⟩ := ht
  by_contra hk0
  have hxk : 0 < x k := hx k hk hk0
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (n : ℝ) + 1 := ⟨_, rfl⟩
  have hNpos : (0 : ℝ) < N := by rw [hN]; positivity
  obtain ⟨c, hc⟩ : ∃ c : E, c = N⁻¹ • ∑ j, (t j).1 := ⟨_, rfl⟩
  have hlin : ∀ f : E →L[ℝ] ℝ, f c = N⁻¹ * ∑ j, f (t j).1 := by
    intro f

    rw [hc, map_smul, map_sum, smul_eq_mul]
  have hpoly : ∀ j, (t j).1 ∈ poly q := fun j => (t j).2.1
  have hconst : ∀ a : ℝ, (∑ _j : Fin (n + 1), a) = N * a := by
    intro a
    simp [hN]
  have hcpoly : c ∈ poly q := by
    intro y
    rw [hlin, le_inv_mul_iff₀ hNpos]
    have h1 := hconst 1
    rw [mul_one] at h1
    rw [mul_one, ← h1]
    exact Finset.sum_le_sum fun j _ => hpoly j y
  have htight : ∀ y, q y c = 1 → ∀ j, q y (t j).1 = 1 := by
    intro y hy j
    rw [hlin, inv_mul_eq_one₀ hNpos.ne'] at hy
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ q y (t i).1 - 1 := fun i _ => sub_nonneg.mpr (hpoly i y)
    have hz : ∑ i, (q y (t i).1 - 1) = 0 := by
      rw [Finset.sum_sub_distrib, ← hy, hconst, mul_one, sub_self]
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz j (Finset.mem_univ j)
    linarith
  obtain ⟨ε, hε, hpert⟩ := perturb hq c hcpoly k (fun y hy => hkq y (htight y hy))
  have hmem : c + (-ε) • k ∈ poly q := hpert (-ε) (by rw [abs_neg, abs_of_pos hε])
  have hsum_le : ∑ j, x (t j).1 ≤ N * x (c + (-ε) • k) := by
    rw [← hconst]
    exact Finset.sum_le_sum fun j _ => hxt j _ hmem
  have hexp : x (c + (-ε) • k) = x c - ε * x k := by
    rw [map_add (f := _), map_smul, smul_eq_mul]
    ring
  have hxc : N * x c = ∑ j, x (t j).1 := by
    rw [hlin x, ← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul]
  rw [hexp, ← hxc] at hsum_le
  nlinarith [mul_pos hNpos (mul_pos hε hxk)]
end

section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.cone_finite :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {q : Y → E →L[ℝ] ℝ} {T : Set E}, Good q T → ∀ s : Set (E →L[ℝ] ℝ), s.Finite → s ⊆ posDual T → {v : Vert q | (convexHull ℝ s ∩ normalCone q v.1).Nonempty}.Finite := by
  intro E Y _ _ _ q T hg s hs hsT
  obtain ⟨h0, hh0⟩ := hg.nonempty
  let K : Set E := ⋃ x ∈ s, {h | h ∈ poly q ∧ x h ≤ x h0}
  have hK : IsCompact K := hs.isCompact_biUnion fun x hx => sublevel hg x (hsT hx) (x h0)
  have hKp : K ⊆ poly q := by
    intro h hh
    simp only [K, Set.mem_iUnion] at hh
    obtain ⟨x, _, hp, _⟩ := hh
    exact hp
  refine ((vert_finite hg.locFin K hK hKp).preimage Subtype.val_injective.injOn).subset ?_
  rintro v ⟨z, hzs, hzv⟩
  refine ⟨?_, v.2⟩
  simp only [K, Set.mem_iUnion]
  by_contra hno
  push_neg at hno
  have hconv : Convex ℝ {f : E →L[ℝ] ℝ | 0 < f (v.1 - h0)} := by
    refine convex_halfSpace_gt ?_ 0
    exact ⟨fun f g => rfl, fun c f => rfl⟩
  have hsub : s ⊆ {f : E →L[ℝ] ℝ | 0 < f (v.1 - h0)} := by
    intro x hx
    have hlt : x h0 < x v.1 := by
      by_contra hle
      exact hno x hx ⟨v.2.1, not_lt.mp hle⟩
    simp only [Set.mem_setOf_eq, map_sub]
    linarith
  have hz := convexHull_min hsub hconv hzs
  have hz2 := hzv h0 hh0
  simp only [Set.mem_setOf_eq, map_sub] at hz
  linarith
end

section

open Set UpperTheory.V.ConeExtensionAcyclic

theorem UpperTheory.V.ConeExtensionAcyclic.exists_vert :
    ∀ {E Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {q : Y → E →L[ℝ] ℝ} {T : Set E}, Good q T → ∀ x ∈ posDual T, ∃ v : Vert q, x ∈ normalCone q v.1 := by
  intro E Y _ _ _ q T hG x hx
  obtain ⟨h0, hh0⟩ := hG.nonempty
  have hK := sublevel hG x hx (x h0)
  obtain ⟨hm, hmK, hmin⟩ := hK.exists_isMinOn ⟨h0, hh0, le_rfl⟩ x.continuous.continuousOn
  have hglob : ∀ h' ∈ poly q, x hm ≤ x h' := by
    intro h' hh'
    by_cases hle : x h' ≤ x h0
    · exact hmin ⟨hh', hle⟩
    · have : x hm ≤ x h0 := hmK.2
      linarith [not_le.mp hle]
  have hF := sublevel hG x hx (x hm)
  obtain ⟨e, he⟩ := hF.extremePoints_nonempty ⟨hm, hmK.1, le_rfl⟩
  rw [mem_extremePoints] at he
  obtain ⟨⟨hep, hex⟩, hext⟩ := he
  refine ⟨⟨e, hep, ?_⟩, ?_⟩
  · intro k hk
    obtain ⟨ε, hε, hs⟩ := perturb hG.locFin e hep k hk
    have ha := hs ε (by rw [abs_of_pos hε])
    have hb := hs (-ε) (by rw [abs_neg, abs_of_pos hε])
    have hxa := hglob _ ha
    have hxb := hglob _ hb
    simp only [map_add (f := _), map_smul, smul_eq_mul] at hxa hxb
    have hmem1 : e + ε • k ∈ {h | h ∈ poly q ∧ x h ≤ x hm} :=
      ⟨ha, by simp only [map_add (f := _), map_smul, smul_eq_mul]; linarith⟩
    have hmem2 : e + (-ε) • k ∈ {h | h ∈ poly q ∧ x h ≤ x hm} :=
      ⟨hb, by simp only [map_add (f := _), map_smul, smul_eq_mul]; linarith⟩
    have hseg : e ∈ openSegment ℝ (e + ε • k) (e + (-ε) • k) := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      module
    have heq := (hext _ hmem1 _ hmem2 hseg).1
    have hzero : ε • k = 0 := by
      have := congrArg (fun w => w - e) heq
      simpa using this
    exact (smul_eq_zero.mp hzero).resolve_left hε.ne'
  · simp only [normalCone, Set.mem_setOf_eq]
    intro h' hh'
    exact le_trans hex (hglob h' hh')
end
