module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Module.Lattice.Basic
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle006
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import ReciprocityTheory.Automorphisms.Bundle001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle024
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle006
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimOfIsUnitDet

@[expose] public section

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory

theorem two_geometric_sums_index_bound :
    ∀ (q ρ a : ℕ), 2 ≤ q → 4 ≤ ρ →
      (∑ i ∈ Finset.Icc 1 a, ((q : ℝ) ^ i - (q : ℝ) ^ (i - 1)) * (q : ℝ) ^ (-(i * ρ : ℤ))
        ≤ 8 / 7 * (q : ℝ) ^ (1 - (ρ : ℤ))) ∧
      ∀ j : ℕ, 1 + ∑ i ∈ Finset.Icc 1 a,
        ((q : ℝ) ^ i - (q : ℝ) ^ (i - 1)) * (q : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ))
          ≤ 8 / 7 * (q : ℝ) ^ j := by
  intro q ρ a hq hρ
  have hQ : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hQ0 : (0:ℝ) < q := by linarith
  have hQ1 : (1:ℝ) ≤ q := by linarith
  set r : ℝ := (q:ℝ) ^ (1 - (ρ:ℤ)) with hr
  have hr0 : 0 ≤ r := by positivity
  have hr8 : r ≤ 1 / 8 := by
    have h1 : r ≤ (q:ℝ) ^ (-3:ℤ) := zpow_le_zpow_right₀ hQ1 (by omega)
    have h2 : (q:ℝ) ^ (-3:ℤ) = ((q:ℝ) ^ 3)⁻¹ := by norm_num [zpow_neg]
    have h3 : (8:ℝ) ≤ (q:ℝ) ^ 3 := by
      have := pow_le_pow_left₀ (by norm_num) hQ 3
      norm_num at this
      linarith
    have h4 : ((q:ℝ) ^ 3)⁻¹ ≤ (8:ℝ)⁻¹ := inv_anti₀ (by norm_num) h3
    rw [h2] at h1
    linarith [show (8:ℝ)⁻¹ = 1 / 8 by norm_num]
  have key : ∀ i : ℕ, (q:ℝ) ^ i * (q:ℝ) ^ (-(i * ρ : ℤ)) = r ^ i := by
    intro i
    rw [hr, ← zpow_natCast ((q:ℝ)) i, ← zpow_natCast ((q:ℝ) ^ (1 - (ρ:ℤ))) i, ← zpow_mul,
      ← zpow_add₀ hQ0.ne']
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · have hterm : ∀ i ∈ Finset.Icc 1 a,
        ((q:ℝ) ^ i - (q:ℝ) ^ (i - 1)) * (q:ℝ) ^ (-(i * ρ : ℤ)) ≤ r ^ i := by
      intro i _
      rw [← key i]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have : (0:ℝ) ≤ (q:ℝ) ^ (i - 1) := by positivity
      linarith
    have hgeom : ∑ i ∈ Finset.Icc 1 a, r ^ i ≤ r ^ 1 / (1 - r) := by
      have hIcc : Finset.Icc 1 a = Finset.Ico 1 (a + 1) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      rw [hIcc]
      exact geom_sum_Ico_le_of_lt_one hr0 (by linarith)
    have hfrac : r ^ 1 / (1 - r) ≤ 8 / 7 * r := by
      rw [pow_one, div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg hr0 (show (0:ℝ) ≤ 1 / 8 - r by linarith)]
    linarith [Finset.sum_le_sum hterm]
  · intro j
    have main : ∀ n : ℕ, 1 + ∑ i ∈ Finset.Icc 1 n,
          ((q : ℝ) ^ i - (q : ℝ) ^ (i - 1)) * (q : ℝ) ^ (-(((i - j : ℕ) : ℤ) * ρ))
          ≤ (q:ℝ) ^ (min n j) + 1 / 7 * (q:ℝ) ^ j * (1 - (1 / 8 : ℝ) ^ (n - j)) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc]
        rcases Nat.lt_or_ge n j with h | h
        · have e1 : n + 1 - j = 0 := by omega
          have e2 : n - j = 0 := by omega
          have e3 : min (n + 1) j = n + 1 := by omega
          have e4 : min n j = n := by omega
          rw [e1, e3, Nat.add_sub_cancel]
          rw [e2, e4] at ih
          simp only [Nat.cast_zero, zero_mul, neg_zero, zpow_zero, mul_one, pow_zero, sub_self,
            mul_zero, add_zero] at ih ⊢
          linarith
        · have e1 : n + 1 - j = (n - j) + 1 := by omega
          have e3 : min (n + 1) j = j := by omega
          have e4 : min n j = j := by omega
          rw [e4] at ih
          rw [e3, Nat.add_sub_cancel]
          have hterm : ((q:ℝ) ^ (n + 1) - (q:ℝ) ^ n) * (q:ℝ) ^ (-(((n + 1 - j : ℕ) : ℤ) * ρ))
              ≤ (q:ℝ) ^ j * ((1 / 8 : ℝ) ^ (n - j) * (1 / 8)) := by
            have hk := key ((n - j) + 1)
            rw [← e1] at hk
            calc ((q:ℝ) ^ (n + 1) - (q:ℝ) ^ n) * (q:ℝ) ^ (-(((n + 1 - j : ℕ) : ℤ) * ρ))
                ≤ (q:ℝ) ^ (n + 1) * (q:ℝ) ^ (-(((n + 1 - j : ℕ) : ℤ) * ρ)) := by
                  apply mul_le_mul_of_nonneg_right _ (by positivity)
                  have : (0:ℝ) ≤ (q:ℝ) ^ n := by positivity
                  linarith
              _ = (q:ℝ) ^ j * ((q:ℝ) ^ (n + 1 - j) * (q:ℝ) ^ (-(((n + 1 - j : ℕ) : ℤ) * ρ))) := by
                  rw [← mul_assoc, ← pow_add]
                  congr 2
                  omega
              _ = (q:ℝ) ^ j * r ^ (n + 1 - j) := by rw [hk]
              _ ≤ (q:ℝ) ^ j * ((1 / 8 : ℝ) ^ (n - j) * (1 / 8)) := by
                  rw [e1, ← pow_succ]
                  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr8 _) (by positivity)
          have h8 : (1 / 8 : ℝ) ^ (n + 1 - j) = (1 / 8) ^ (n - j) * (1 / 8) := by
            rw [e1, pow_succ]
          rw [h8]
          linarith
    have hmin : (q:ℝ) ^ (min a j) ≤ (q:ℝ) ^ j := pow_le_pow_right₀ hQ1 (min_le_right _ _)
    have hX : (0:ℝ) ≤ (q:ℝ) ^ j := by positivity
    have hY : (0:ℝ) ≤ (1 / 8 : ℝ) ^ (a - j) := by positivity
    nlinarith [main a, mul_nonneg hX hY]

end GlobalTheory
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical ComplexConjugate

namespace GlobalTheory.HL.GaussSum

theorem sq_norm_sum_mul_index_le {G : Type*} [AddCommGroup G] [Fintype G] (Q : AddSubgroup G)
    (f : G → ℂ) (hf : ∀ u, ‖f u‖ = 1)
    (hQ : ∀ h, h ∉ Q → ∃ (v : G) (c : ℂ), c ≠ 1 ∧
      ∀ u, f (u + v + h) * conj (f (u + v)) = c * (f (u + h) * conj (f u))) :
    ‖∑ u, f u‖ ^ 2 * (Q.index : ℝ) ≤ (Fintype.card G : ℝ) ^ 2 := by
  classical
  have hzero : ∀ h, h ∉ Q → ∑ u, f (u + h) * conj (f u) = 0 := by
    intro h hh
    obtain ⟨v, c, hc, hrel⟩ := hQ h hh
    have h1 : ∑ u, f (u + h) * conj (f u) = c * ∑ u, f (u + h) * conj (f u) := by
      rw [Finset.mul_sum]
      calc ∑ u, f (u + h) * conj (f u) = ∑ u, f (u + v + h) * conj (f (u + v)) :=
            (Fintype.sum_equiv (Equiv.addRight v) (fun u => f (u + v + h) * conj (f (u + v)))
              (fun u => f (u + h) * conj (f u)) (fun u => rfl)).symm
        _ = ∑ u, c * (f (u + h) * conj (f u)) := Finset.sum_congr rfl fun u _ => hrel u
    have h2 : (1 - c) * ∑ u, f (u + h) * conj (f u) = 0 := by
      rw [sub_mul, one_mul, ← h1, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd (sub_eq_zero.mp h3).symm hc
    · exact h3
  have hexp : (∑ u, f u) * conj (∑ u, f u) = ∑ h, ∑ u, f (u + h) * conj (f u) := by
    calc (∑ u, f u) * conj (∑ u, f u) = ∑ w, ∑ u, f w * conj (f u) := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.sum_mul_sum]
      _ = ∑ u, ∑ w, f w * conj (f u) := Finset.sum_comm
      _ = ∑ u, ∑ h, f (u + h) * conj (f u) := Finset.sum_congr rfl fun u _ =>
          (Fintype.sum_equiv (Equiv.addLeft u) (fun h => f (u + h) * conj (f u))
            (fun w => f w * conj (f u)) (fun h => rfl)).symm
      _ = ∑ h, ∑ u, f (u + h) * conj (f u) := Finset.sum_comm
  have hnorm : ‖∑ u, f u‖ ^ 2 ≤ (Fintype.card G : ℝ) * (Nat.card Q : ℝ) := by
    calc ‖∑ u, f u‖ ^ 2 = ‖(∑ u, f u) * conj (∑ u, f u)‖ := by
          rw [norm_mul, RCLike.norm_conj, sq]
      _ = ‖∑ h, ∑ u, f (u + h) * conj (f u)‖ := by rw [hexp]
      _ ≤ ∑ h, ‖∑ u, f (u + h) * conj (f u)‖ := norm_sum_le _ _
      _ ≤ ∑ h, (if h ∈ Q then (Fintype.card G : ℝ) else 0) := by
          refine Finset.sum_le_sum fun h _ => ?_
          split_ifs with hh
          · calc ‖∑ u, f (u + h) * conj (f u)‖ ≤ ∑ u, ‖f (u + h) * conj (f u)‖ :=
                  norm_sum_le _ _
              _ = ∑ _u : G, (1 : ℝ) := by simp [hf]
              _ = Fintype.card G := by simp
          · rw [hzero h hh, norm_zero]
      _ = (Fintype.card G : ℝ) * (Nat.card Q : ℝ) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            mul_comm]
          congr 1
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hci : (Nat.card Q : ℝ) * (Q.index : ℝ) = Fintype.card G := by
    rw [← Nat.card_eq_fintype_card, ← AddSubgroup.card_mul_index (H := Q)]
    push_cast
    ring
  calc ‖∑ u, f u‖ ^ 2 * (Q.index : ℝ) ≤ (Fintype.card G : ℝ) * Nat.card Q * Q.index :=
        mul_le_mul_of_nonneg_right hnorm (Nat.cast_nonneg _)
    _ = (Fintype.card G : ℝ) ^ 2 := by rw [mul_assoc, hci, sq]

theorem sq_norm_sum_reps_mul_index_le {M : Type*} [AddCommGroup M] (P Q : AddSubgroup M)
    (hPQ : P ≤ Q) (R : Finset M) (hR : ∀ u, ∃! w, w ∈ R ∧ u - w ∈ P)
    (f : M → ℂ) (hf : ∀ u, ‖f u‖ = 1) (hP : ∀ u, ∀ p ∈ P, f (u + p) = f u)
    (hQ : ∀ h, h ∉ Q → ∃ (v : M) (c : ℂ), c ≠ 1 ∧
      ∀ u, f (u + v + h) * conj (f (u + v)) = c * (f (u + h) * conj (f u))) :
    ‖∑ u ∈ R, f u‖ ^ 2 * (Q.index : ℝ) ≤ (R.card : ℝ) ^ 2 := by
  classical
  have hsurj : ∀ x : M ⧸ P, ∃ w ∈ R, (w : M ⧸ P) = x := by
    intro x
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨w, ⟨hwR, hw⟩, -⟩ := hR u
    refine ⟨w, hwR, ?_⟩
    rw [QuotientAddGroup.eq]
    have e : -w + u = u - w := by abel
    rw [e]
    exact hw
  have hinj : ∀ w ∈ R, ∀ w' ∈ R, (w : M ⧸ P) = w' → w = w' := by
    intro w hw w' hw' h
    rw [QuotientAddGroup.eq] at h
    obtain ⟨z, -, hz⟩ := hR w
    have h1 : w = z := hz w ⟨hw, by simp⟩
    have h2 : w' = z := hz w' ⟨hw', by
      rw [show w - w' = -(-w + w') by abel]
      exact P.neg_mem h⟩
    rw [h1, h2]
  have : Finite (M ⧸ P) := by
    apply Finite.of_surjective (fun w : R => ((w : M) : M ⧸ P))
    intro x
    obtain ⟨w, hw, rfl⟩ := hsurj x
    exact ⟨⟨w, hw⟩, rfl⟩
  let : Fintype (M ⧸ P) := Fintype.ofFinite _
  have hf' : ∀ u : M, f ((u : M ⧸ P)).out = f u := by
    intro u
    have h := QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' (u : M ⧸ P))
    have e := hP ((u : M ⧸ P)).out _ h
    rw [add_neg_cancel_left] at e
    exact e.symm
  have h1 := GlobalTheory.HL.GaussSum.sq_norm_sum_mul_index_le (Q.map (QuotientAddGroup.mk' P))
    (fun x : M ⧸ P => f x.out) (fun x => hf _) (by
      intro h' hh'
      obtain ⟨h, rfl⟩ := QuotientAddGroup.mk_surjective h'
      have hhQ : h ∉ Q := fun hq => hh' (AddSubgroup.mem_map_of_mem _ hq)
      obtain ⟨v, c, hc, hrel⟩ := hQ h hhQ
      refine ⟨(v : M ⧸ P), c, hc, fun x => ?_⟩
      obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective x
      simp only [← QuotientAddGroup.mk_add, hf']
      exact hrel u)
  have hidx : (Q.map (QuotientAddGroup.mk' P)).index = Q.index :=
    AddSubgroup.index_map_eq (H := Q) (QuotientAddGroup.mk'_surjective P)
      (by rw [QuotientAddGroup.ker_mk']; exact hPQ)
  have hi1 : ∀ a ∈ R, ((a : M ⧸ P)) ∈ (Finset.univ : Finset (M ⧸ P)) :=
    fun _ _ => Finset.mem_univ _
  have hi2 : Set.InjOn (fun a : M => (a : M ⧸ P)) R := by
    intro w hw w' hw' h
    exact hinj w hw w' hw' h
  have hi3 : Set.SurjOn (fun a : M => (a : M ⧸ P)) R (↑(Finset.univ : Finset (M ⧸ P)) : Set (M ⧸ P)) := by
    intro x _
    obtain ⟨w, hw, rfl⟩ := hsurj x
    exact ⟨w, hw, rfl⟩
  have hsum : ∑ u ∈ R, f u = ∑ x : M ⧸ P, f x.out :=
    Finset.sum_nbij (fun a : M => (a : M ⧸ P)) hi1 hi2 hi3 (fun u _ => (hf' u).symm)
  have hcard : R.card = Fintype.card (M ⧸ P) := by
    rw [← Finset.card_univ]
    exact Finset.card_nbij (fun a : M => (a : M ⧸ P)) hi1 hi2 hi3
  rw [hsum, hcard, ← hidx]
  exact h1

theorem mul_conj_eq {A : Type*} [AddCommGroup A] (ψ : AddChar A ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x y : A) :
    ψ x * conj (ψ y) = ψ (x - y) := by
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, Complex.inv_def,
    Complex.normSq_eq_norm_sq, h y]
  simp

end GlobalTheory.HL.GaussSum
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

theorem GlobalTheory.glue_latt_isLattice {E : Type} [Field E] [NumberField E] (n : ℕ) (Γ : Submodule (𝓞 E) (Fin n → E)) (N : ℕ) (hN : N ≠ 0)
    (hlow : ∀ x : Fin n → E, (∀ i, IsIntegral ℤ (x i)) → (N : E) • x ∈ Γ)
    (hup : ∀ x ∈ Γ, ∀ i, IsIntegral ℤ ((N : E) * x i)) : Submodule.IsLattice E Γ := by
  have hNE : (N : E) ≠ 0 := Nat.cast_ne_zero.mpr hN
  let f : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) :=
    ((N : E)⁻¹ • (LinearMap.pi fun i => (Algebra.linearMap (𝓞 E) E).comp (LinearMap.proj i)))
  have hle : Γ ≤ LinearMap.range f := by
    intro x hx
    refine ⟨fun i => ⟨(N : E) * x i, hup x hx i⟩, ?_⟩
    ext i
    change (N : E)⁻¹ * ((N : E) * x i) = x i
    rw [← mul_assoc, inv_mul_cancel₀ hNE, one_mul]
  refine ⟨?_, ?_⟩
  · rw [← Submodule.map_comap_eq_self hle]
    exact (IsNoetherian.noetherian _).map f
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DenClear

theorem ringOfIntegers_smul_eq {E : Type} [Field E] [NumberField E] (o : 𝓞 E) (x : E) :
    o • x = (o : E) * x := rfl

theorem coeO_mul {E : Type} [Field E] [NumberField E] (a b : 𝓞 E) :
    ((a * b : 𝓞 E) : E) = (a : E) * b := rfl

theorem coeO_add {E : Type} [Field E] [NumberField E] (a b : 𝓞 E) :
    ((a + b : 𝓞 E) : E) = (a : E) + b := rfl

theorem coeO_int {E : Type} [Field E] [NumberField E] (k : ℤ) : ((k : 𝓞 E) : E) = (k : E) := by
  rfl

theorem exists_int_mul_eq {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ m : ℤ, m ≠ 0 ∧ ∃ o : 𝓞 E, (m : E) * e = o := by
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {e}
  have h := hy e (Finset.mem_singleton_self e)
  rw [zsmul_eq_mul] at h
  exact ⟨y, hy0, ⟨(y : E) * e, h⟩, rfl⟩

theorem clear_of_dvd {E : Type} [Field E] [NumberField E] {m D : ℤ} (h : m ∣ D) {e : E}
    (he : ∃ o : 𝓞 E, (m : E) * e = o) : ∃ o : 𝓞 E, (D : E) * e = o := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨o, ho⟩ := he
  refine ⟨(k : 𝓞 E) * o, ?_⟩
  rw [coeO_mul, coeO_int, ← ho]
  push_cast
  ring

theorem exists_int_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsFullLattice E Λ) (w : Fin n → E) :
    ∃ m : ℤ, m ≠ 0 ∧ (m : 𝓞 E) • w ∈ Λ := by
  exact _root_.GlobalTheory.IntMulIntegerSmulMemLattice.exists_int_smul_mem_lattice Λ hΛ w

theorem den_clear : ∀ {E : Type} [Field E] [NumberField E] {n : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ] (v : ι → E) (g : κ → Fin n → E) (Hm : Matrix (Fin n) (Fin n) E) (sg : E →+* E) (Λ : Submodule (𝓞 E) (Fin n → E)), Submodule.IsFullLattice E Λ → ∃ D : ℤ, D ≠ 0 ∧ (∀ i, ∃ o : 𝓞 E, (D : E) * v i = o) ∧ (∀ x ∈ Λ, ∀ l, ∃ o : 𝓞 E, (D : E) * ∑ a, ∑ b, x a * Hm a b * sg (g l b) = o) ∧ ∀ l, (D : 𝓞 E) • g l ∈ Λ := by
  intro E _ _ n ι κ _ _ v g Hm sg Λ hΛ
  choose mv hmv0 hmv using fun i => exists_int_mul_eq (v i)
  choose mg hmg0 hmg using fun l => exists_int_smul_mem Λ hΛ (g l)
  obtain ⟨s, hs⟩ := Submodule.IsLattice.fg (A := E) (M := Λ)
  choose mp hmp0 hmp using fun (p : κ × (Fin n → E)) =>
    exists_int_mul_eq (∑ a, ∑ b, p.2 a * Hm a b * sg (g p.1 b))
  let T : Finset (κ × (Fin n → E)) := Finset.univ ×ˢ s
  let A : ℤ := ∏ i, mv i
  let B : ℤ := ∏ l, mg l
  let C : ℤ := ∏ p ∈ T, mp p
  have hA : A ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hmv0 i
  have hB : B ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hmg0 i
  have hC : C ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hmp0 i
  have dA : ∀ i, mv i ∣ A * B * C := fun i =>
    ((Finset.dvd_prod_of_mem mv (Finset.mem_univ i)).mul_right B).mul_right C
  have dB : ∀ l, mg l ∣ A * B * C := fun l =>
    ((Finset.dvd_prod_of_mem mg (Finset.mem_univ l)).mul_left A).mul_right C
  have dC : ∀ p ∈ T, mp p ∣ A * B * C := fun p hp =>
    (Finset.dvd_prod_of_mem mp hp).mul_left _
  refine ⟨A * B * C, mul_ne_zero (mul_ne_zero hA hB) hC, fun i => clear_of_dvd (dA i) (hmv i),
    ?_, ?_⟩
  · intro x hx l
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      exact clear_of_dvd (dC (l, x) (Finset.mem_product.2 ⟨Finset.mem_univ l, hx⟩)) (hmp (l, x))
    | zero => exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨o₁, h₁⟩ := hx
      obtain ⟨o₂, h₂⟩ := hy
      refine ⟨o₁ + o₂, ?_⟩
      rw [coeO_add, ← h₁, ← h₂, ← mul_add, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [Pi.add_apply]
      ring
    | smul c x _ hx =>
      obtain ⟨o, h⟩ := hx
      refine ⟨c * o, ?_⟩
      rw [coeO_mul, ← h]
      simp only [Pi.smul_apply, ringOfIntegers_smul_eq, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  · intro l
    obtain ⟨k, hk⟩ := dB l
    have : ((A * B * C : ℤ) : 𝓞 E) • g l = (k : 𝓞 E) • ((mg l : 𝓞 E) • g l) := by
      rw [smul_smul, hk]
      push_cast
      rw [mul_comm]
    rw [this]
    exact Λ.smul_mem _ (hmg l)

end GlobalTheory.DenClear
end

section

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

theorem index_comap_of_dense_image {A B : Type} [Group A] [Group B] (f : A →* B) (H : Subgroup B)
    (hf : ∀ b, ∃ a, (f a)⁻¹ * b ∈ H) : (H.comap f).index = H.index := by
  first
  | exact @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit
  | (apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IndexComapCosets.index_comap_eq_of_cosets_hit ..)

theorem relIndex_comap_of_dense_image {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G)
    (K U : Subgroup G) (h : ∀ g ∈ U, ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) :
    (K.comap φ).relIndex (U.comap φ) = K.relIndex U := by
  let f : U.comap φ →* U := φ.subgroupComap U
  have hc : (K.comap φ).subgroupOf (U.comap φ) = (K.subgroupOf U).comap f := by
    ext x
    exact Iff.rfl
  have key := index_comap_of_dense_image f (K.subgroupOf U) (by
    rintro ⟨b, hb⟩
    obtain ⟨γ, hγK, hγU⟩ := h b hb
    have hγ : φ γ ∈ U := by
      have := U.mul_mem hb (U.inv_mem hγU)
      simpa using this
    refine ⟨⟨γ, hγ⟩, ?_⟩
    exact hγK)
  simp only [Subgroup.relIndex]
  rw [hc, key]

theorem relIndex_pair_comap_of_dense_image : ∀ {Γ G : Type} [Group Γ] [Group G] (φ : Γ →* G) (K U : Subgroup G), (∀ g, g ∈ K ∨ g ∈ U → ∃ γ, (φ γ)⁻¹ * g ∈ K ⊓ U) → (K.comap φ).relIndex (U.comap φ) = K.relIndex U ∧ (U.comap φ).relIndex (K.comap φ) = U.relIndex K := by
  intro Γ G _ _ φ K U h
  refine ⟨relIndex_comap_of_dense_image φ K U fun g hg => h g (Or.inr hg), ?_⟩
  refine relIndex_comap_of_dense_image φ U K fun g hg => ?_
  obtain ⟨γ, hγ⟩ := h g (Or.inl hg)
  exact ⟨γ, by rwa [inf_comm]⟩

end GlobalTheory.HL
end

section

open GlobalTheory.GramCount
open scoped Classical

theorem _root_.GlobalTheory.T.exists_primitive_addChar_involution_invariant : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B), (∀ u, c (c u) = u) → ∀ (ω : B), IsUnit (ω - c ω) → (∀ t, c t = t → t ≠ 0 → IsUnit t) → ∃ χ : AddChar B ℂ, χ.IsPrimitive ∧ ∀ u, χ (c u) = χ u := by
  first | exact @GlobalTheory.GramCount.exists_isPrimitive_invol_invariant | exact GlobalTheory.GramCount.exists_isPrimitive_invol_invariant | (intros; apply GlobalTheory.GramCount.exists_isPrimitive_invol_invariant <;> assumption)
end

section

open Matrix

theorem _root_.GlobalTheory.T.exists_unitary_conjugator_of_split_idempotents : ∀ (R : Type) [CommRing R] (σ : R →+* R), (∀ a, σ (σ a) = a) → ∀ (m n : ℕ) (ι : Type) [Fintype ι] (ε : ι → R), (∀ j, ε j * ε j = ε j) → (∀ j, ε j * σ (ε j) = 0) → (∀ j k, j ≠ k → ε j * ε k = 0 ∧ ε j * σ (ε k) = 0) → ∀ (Z P : Matrix (Fin m) (Fin n) R) (Z' P' : Matrix (Fin n) (Fin m) R), Z * Z' = 1 → Z' * Z = 1 → P * P' = 1 → P' * P = 1 → ∃ c : GL (Fin n) R, (c : Matrix (Fin n) (Fin n) R) * ReciprocityTheory.Aut.conjT σ (c : Matrix (Fin n) (Fin n) R) = 1 ∧ ∀ j, ε j • (Z * (c : Matrix (Fin n) (Fin n) R)) = ε j • P ∧ ε j • (((c⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * Z') = ε j • P' := by
  first | exact @GlobalTheory.unitary_conjugator_of_split_idempotents | exact GlobalTheory.unitary_conjugator_of_split_idempotents | (intros; apply GlobalTheory.unitary_conjugator_of_split_idempotents <;> assumption)
end
