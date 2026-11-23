module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Length
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
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.Order.CompletePartialOrder
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
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe

@[expose] public section

section

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.detFactor :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (n : ℕ) (S : Matrix (Fin n) (Fin n) K),
      ∃ z : Fin n → K, ∀ c : K, (c • S - 1).det = ∏ i, (c * z i - 1) := by
  intro K _ _ n S
  classical
  set p := S.charpoly with hp
  have hmon : p.Monic := Matrix.charpoly_monic S
  have hprod : (p.roots.map (fun a => Polynomial.X - Polynomial.C a)).prod = p :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon IsAlgClosed.card_roots_eq_natDegree
  have hcard : Multiset.card p.roots = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hp, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have heval : ∀ x : K, (Matrix.scalar (Fin n) x - S).det = (p.roots.map (fun a => x - a)).prod := by
    intro x
    rw [← Matrix.eval_charpoly, ← hp]
    conv_lhs => rw [← hprod]
    rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp
  have hz : ∃ z : Fin n → K, ∀ f : K → K, (p.roots.map f).prod = ∏ i, f (z i) := by
    obtain ⟨L, hL⟩ : ∃ L : List K, (L : Multiset K) = p.roots := ⟨_, Multiset.coe_toList _⟩
    have hlen : L.length = n := by rw [← hcard, ← hL, Multiset.coe_card]
    refine ⟨fun i => L.get (Fin.cast hlen.symm i), fun f => ?_⟩
    rw [← hL, Multiset.map_coe, Multiset.prod_coe, ← List.prod_ofFn]
    congr 1
    apply List.ext_get <;> simp [hlen]
  obtain ⟨z, hz⟩ := hz
  refine ⟨z, fun c => ?_⟩
  by_cases hc : c = 0
  · subst hc
    simp [Matrix.det_neg]
  · have hmat : c • S - 1 = (-c) • (Matrix.scalar (Fin n) c⁻¹ - S) := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [Matrix.sub_apply, Matrix.one_apply]
        field_simp
        ring
      · simp [Matrix.sub_apply, Matrix.one_apply, hij]
    rw [hmat, Matrix.det_smul, heval, hz, Fintype.card_fin, ← Fin.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    field_simp
    ring
end

section

open UpperTheory.V UpperTheory.V.PropA

theorem UpperTheory.V.PropA.helly :
    ∀ (l : ℕ) [Fact l.Prime] (x : ℕ → ℤ_[l]) (r : ℕ → ℝ), (∀ a b, ‖x a - x b‖ ≤ max (r a) (r b)) →
      ∃ s : ℤ_[l], ∀ a, ‖s - x a‖ ≤ r a := by
  intro l _ x r hx
  have hne : ∀ u : Finset ℕ,
      ((Set.univ : Set ℤ_[l]) ∩ ⋂ a ∈ u, Metric.closedBall (x a) (r a)).Nonempty := by
    intro u
    rcases u.eq_empty_or_nonempty with hu | hu
    · exact ⟨0, by simp [hu]⟩
    · obtain ⟨a0, ha0, hmin⟩ := u.exists_min_image r hu
      refine ⟨x a0, Set.mem_univ _, ?_⟩
      simp only [Set.mem_iInter, Metric.mem_closedBall, dist_eq_norm]
      intro a ha
      exact (hx a0 a).trans (max_le (hmin a ha) le_rfl)
  obtain ⟨s, -, hs⟩ := isCompact_univ.inter_iInter_nonempty
    (fun a => Metric.closedBall (x a) (r a)) (fun a => Metric.isClosed_closedBall) hne
  refine ⟨s, fun a => ?_⟩
  have h1 := Set.mem_iInter.1 hs a
  rw [Metric.mem_closedBall, dist_eq_norm] at h1
  exact h1
end

section

open UpperTheory.V UpperTheory.V.PropA

private theorem nilLen_range_succ {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (f : Module.End A M) (k : ℕ) :
    LinearMap.range (f ^ (k + 1)) = (LinearMap.range (f ^ k)).map f := by
  rw [pow_succ', Module.End.mul_eq_comp, LinearMap.range_comp]

private theorem nilLen_lt {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (f : Module.End A M) (hf : IsNilpotent f) (k : ℕ) (hk : f ^ k ≠ 0) :
    LinearMap.range (f ^ (k + 1)) < LinearMap.range (f ^ k) := by
  refine lt_of_le_of_ne ?_ ?_
  · rw [pow_succ, Module.End.mul_eq_comp]
    exact LinearMap.range_comp_le_range _ _
  · intro h
    apply hk
    obtain ⟨n, hn⟩ := hf
    have key : ∀ j, LinearMap.range (f ^ (k + j)) = LinearMap.range (f ^ k) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih => rw [← add_assoc, nilLen_range_succ, ih, ← nilLen_range_succ, h]
    have hkn := key n
    rw [pow_add, hn, mul_zero, LinearMap.range_zero] at hkn
    exact LinearMap.range_eq_bot.mp hkn.symm

theorem UpperTheory.V.PropA.nilLen :
    ∀ (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (f : Module.End A M) (n : ℕ), IsNilpotent f →
      Module.length A M ≤ n → f ^ n = 0 := by
  intro A M _ _ _ f n hf hlen
  by_contra hne
  have hm : ∀ m, m ≤ n → f ^ m ≠ 0 := fun m hm h0 => hne (pow_eq_zero_of_le hm h0)
  have key : ∀ j m, m + j = n → (j : ℕ∞) + 1 ≤ Order.height (LinearMap.range (f ^ m)) := by
    intro j
    induction j with
    | zero =>
      intro m hmj
      have hlt : (⊥ : Submodule A M) < LinearMap.range (f ^ m) := by
        rw [bot_lt_iff_ne_bot, Ne, LinearMap.range_eq_bot]
        exact hm m (by omega)
      have h0 := Order.height_add_one_le hlt
      simp only [Nat.cast_zero, zero_add]
      exact le_trans le_add_self h0
    | succ j ih =>
      intro m hmj
      have h1 := ih (m + 1) (by omega)
      have h2 := Order.height_add_one_le (nilLen_lt f hf m (hm m (by omega)))
      calc ((j + 1 : ℕ) : ℕ∞) + 1 = ((j : ℕ∞) + 1) + 1 := by push_cast; rfl
        _ ≤ Order.height (LinearMap.range (f ^ (m + 1))) + 1 := by gcongr
        _ ≤ _ := h2
  have h3 := key n 0 (by omega)
  rw [Module.length_eq_height] at hlen
  have h4 : Order.height (LinearMap.range (f ^ 0)) ≤ Order.height (⊤ : Submodule A M) :=
    Order.height_mono le_top
  have h5 : ((n : ℕ) : ℕ∞) + 1 ≤ (n : ℕ∞) := h3.trans (h4.trans hlen)
  norm_cast at h5
  omega
end
