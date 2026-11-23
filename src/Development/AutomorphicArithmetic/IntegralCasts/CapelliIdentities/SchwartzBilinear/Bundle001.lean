module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Data.Finset.Defs
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Data.Finset.Empty
public import Mathlib.Data.Finset.Insert
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Nat.Prime.Infinite

@[expose] public section

section

namespace UpperTheory.Reformulated.B.P6.r20a

theorem finsum_const_eq_card_mul {α : Type} [Finite α] (c : ℂ) : ∑ᶠ _ : α, c = (Nat.card α : ℂ) * c := by
  haveI : Fintype α := Fintype.ofFinite α
  rw [finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem quotient_out_right_invariant {H : Type} [Group H] (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ (x k : H), k ∈ K → u (x * k) = u x) (x : H) :
    u (Quotient.out (x : H ⧸ K)) = u x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K x
  rw [hk]
  exact hu x k k.2

theorem PositivityTheory.Rg.BcN.F2.LocOpPf.finsum_quot_le :
    ∀ {H : Type} [inst : Group H] {S T : Subgroup H}, S ≤ T → ∀ (u : H → ℂ), (∀ (x t : H), t ∈ T → u (x * t) = u x) → S.relIndex T ≠ OfNat.ofNat (nat_lit 0) → (Function.support fun (q : H ⧸ S) ↦ u (Quotient.out q)).Finite → ∑ᶠ (q : H ⧸ S), u (Quotient.out q) = (S.relIndex T).cast * ∑ᶠ (q : H ⧸ T), u (Quotient.out q) := by
  intro H _ S T hST u hu hidx hfin
  have huS : ∀ (x s : H), s ∈ S → u (x * s) = u x := fun x s hs => hu x s (hST hs)
  set e := Subgroup.quotientEquivProdOfLE hST with he
  have hfst : ∀ x : H, (e (x : H ⧸ S)).1 = (x : H ⧸ T) := fun x => rfl
  have key : ∀ q : H ⧸ S, u (Quotient.out q) = u (Quotient.out (e q).1) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [hfst x, quotient_out_right_invariant S u huS x, quotient_out_right_invariant T u hu x]
  have hcard : S.relIndex T = Nat.card (T ⧸ S.subgroupOf T) := rfl
  haveI : Finite (T ⧸ S.subgroupOf T) := Nat.finite_of_card_ne_zero (by rw [← hcard]; exact hidx)
  set F : (H ⧸ T) × (T ⧸ S.subgroupOf T) → ℂ := fun pr => u (Quotient.out pr.1) with hF
  have h1 : ∑ᶠ (q : H ⧸ S), u (Quotient.out q) = ∑ᶠ (q : H ⧸ S), F (e q) :=
    finsum_congr key
  have h2 : ∑ᶠ (q : H ⧸ S), F (e q) = ∑ᶠ pr, F pr := finsum_comp_equiv e
  have hFfin : (Function.support F).Finite := by
    apply (hfin.image e).subset
    intro pr hpr
    refine ⟨e.symm pr, ?_, by simp⟩
    have : u (Quotient.out (e.symm pr)) = F pr := by
      rw [key]; simp [hF]
    simpa [Function.mem_support, this] using hpr
  have h3 : ∑ᶠ pr, F pr = ∑ᶠ (p : H ⧸ T) (r : T ⧸ S.subgroupOf T), F (p, r) := finsum_curry F hFfin
  have h4 : ∀ p : H ⧸ T, ∑ᶠ (r : T ⧸ S.subgroupOf T), F (p, r)
      = (Nat.card (T ⧸ S.subgroupOf T) : ℂ) * u (Quotient.out p) := fun p =>
    finsum_const_eq_card_mul (u (Quotient.out p))
  have hffin : (Function.support fun (p : H ⧸ T) => u (Quotient.out p)).Finite := by
    apply (hfin.image fun q => (e q).1).subset
    intro p hp
    refine ⟨((Quotient.out p : H) : H ⧸ S), ?_, ?_⟩
    · have h5 : u (Quotient.out ((Quotient.out p : H) : H ⧸ S)) = u (Quotient.out p) :=
        quotient_out_right_invariant S u huS _
      simpa [Function.mem_support, h5] using hp
    · show (e ((Quotient.out p : H) : H ⧸ S)).1 = p
      rw [hfst]
      exact QuotientGroup.out_eq' p
  rw [h1, h2, h3, finsum_congr h4, hcard]
  have hsub : (Function.support fun p : H ⧸ T =>
      (Nat.card (T ⧸ S.subgroupOf T) : ℂ) * u (Quotient.out p)) ⊆ ↑hffin.toFinset := by
    intro p hp
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    rw [Function.mem_support] at hp
    intro h0
    apply hp
    simp only [h0, mul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsub, finsum_eq_sum _ hffin, Finset.mul_sum]

end UpperTheory.Reformulated.B.P6.r20a
end

section

namespace UpperTheory.Reformulated.B.P6.r14a

theorem eigenvectors_sum_zero_eq_zero {ι κ A : Type} [DecidableEq ι] [AddCommGroup A] [Module ℂ A]
    (T : κ → Module.End ℂ A) (f : ι → κ → ℂ) (hf : Function.Injective f) :
    ∀ (s : Finset ι) (v : ι → A), (∀ i ∈ s, ∀ k, T k (v i) = f i k • v i) →
      ∑ i ∈ s, v i = 0 → ∀ i ∈ s, v i = 0 := by
  classical
  intro s
  induction s using Finset.strongInduction with
  | H s ih =>
    intro v hv hsum a ha
    by_cases hall : ∀ b ∈ s, b = a
    · have h1 : ∑ i ∈ s, v i = v a := by
        apply Finset.sum_eq_single_of_mem a ha
        intro b hb hba
        exact absurd (hall b hb) hba
      rw [← h1]
      exact hsum
    · push_neg at hall
      obtain ⟨b, hb, hba⟩ := hall
      have hfb : f b ≠ f a := fun h => hba (hf h)
      obtain ⟨k, hk⟩ : ∃ k, f b k ≠ f a k := Function.ne_iff.mp hfb
      have hw_eig : ∀ i ∈ s.erase a, ∀ k', T k' ((f i k - f a k) • v i)
          = f i k' • ((f i k - f a k) • v i) := by
        intro i hi k'
        rw [map_smul, hv i (Finset.mem_of_mem_erase hi) k', smul_comm]
      have h2 : ∑ i ∈ s, (f i k - f a k) • v i = 0 := by
        have h3 : ∑ i ∈ s, (f i k - f a k) • v i
            = T k (∑ i ∈ s, v i) - f a k • ∑ i ∈ s, v i := by

          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [hv i hi k, sub_smul]
        rw [h3, hsum, map_zero, smul_zero, sub_zero]
      have hw_sum : ∑ i ∈ s.erase a, (f i k - f a k) • v i = 0 := by
        have h4 := Finset.sum_erase_add s (fun i => (f i k - f a k) • v i) ha
        simp only [sub_self, zero_smul, add_zero] at h4
        rw [h4]
        exact h2
      have hw0 := ih (s.erase a) (Finset.erase_ssubset ha)
        (fun i => (f i k - f a k) • v i) hw_eig hw_sum
      have hz : ∀ i ∈ s, f i k ≠ f a k → v i = 0 := by
        intro i hi hne
        have hia : i ≠ a := fun h => hne (by rw [h])
        have h5 : (f i k - f a k) • v i = 0 := hw0 i (Finset.mem_erase.mpr ⟨hia, hi⟩)
        rcases smul_eq_zero.mp h5 with h | h
        · exact absurd (sub_eq_zero.mp h) hne
        · exact h
      have hts : s.filter (fun i => f i k = f a k) ⊂ s := by
        rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
        exact ⟨b, hb, fun h => hk (Finset.mem_filter.mp h).2⟩
      have hsum_t : ∑ i ∈ s.filter (fun i => f i k = f a k), v i = 0 := by
        rw [Finset.sum_filter_of_ne]
        · exact hsum
        · intro i hi hvi
          by_contra hne
          exact hvi (hz i hi hne)
      exact ih _ hts v (fun i hi k' => hv i (Finset.filter_subset _ _ hi) k') hsum_t a
        (Finset.mem_filter.mpr ⟨ha, rfl⟩)

theorem GlobalTheory.CompanionTheory.PresRho.eq_zero_of_sum_weightVec :
    ∀ {ι κ A : Type} [DecidableEq ι] [inst : AddCommGroup A] [inst_1 : _root_.Module ℂ A] (T : κ → Module.End ℂ A) (f : ι → κ → ℂ), Function.Injective f → ∀ (s : Finset ι) (v : ι → A), (∀ i ∈ s, ∀ (k : κ), DFunLike.coe (T k) (v i) = f i k • v i) → ∑ i ∈ s, v i = OfNat.ofNat (nat_lit 0) → ∀ i ∈ s, v i = OfNat.ofNat (nat_lit 0) := by
  intro ι κ A _ _ _ T f hf s v hv hsum
  exact eigenvectors_sum_zero_eq_zero T f hf s v hv hsum

end UpperTheory.Reformulated.B.P6.r14a
end

section

namespace UpperTheory.Reformulated.B.P6.r26a

open scoped HSub SubNegMonoid AddGroup AddGroupWithOne Ring HMul Distrib OfNat Zero MulZeroClass Finset Semiring Fin Complex AddCommGroup Module Module.End

noncomputable def PositivityTheory.D.DSIC.KRel :
    {n : ℕ} → {A : Type} → [inst_h0 : Ring A] → (Fin n → Bool) → (Fin n → Fin n → A) → Prop :=
  fun {n : ℕ} {A : Type} {inst_f0 : Ring A} (ε_h1 : Fin n → Bool) (F : Fin n → Fin n → A) ↦ ∀ (a b c d : Fin n), ε_h1 a = ε_h1 b → ε_h1 c = ε_h1 d → F a b * F c d - F c d * F a b = (if b = c then F a d else OfNat.ofNat (nat_lit 0)) - if d = a then F c b else OfNat.ofNat (nat_lit 0)

noncomputable def Formalism.REAL.CasK.{u_1} :
    {A : Type u_1} → [inst_h0 : Ring A] → {n : ℕ} → (Fin n → Bool) → (Fin n → Fin n → A) → A :=
  fun {A : Type u_1} {inst_f1 : Ring A} {n : ℕ} (ε_h1 : Fin n → Bool) (E : Fin n → Fin n → A) ↦ ∑ a : Fin n, ∑ b : Fin n, if ε_h1 a = ε_h1 b then E a b * E b a else OfNat.ofNat (nat_lit 0)

theorem commutator_casimir_term {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (hK : PositivityTheory.D.DSIC.KRel ε E) {c d : Fin n} (hcd : ε c = ε d)
    (a b : Fin n) :
    E c d * (if ε a = ε b then E a b * E b a else 0) - (if ε a = ε b then E a b * E b a else 0) * E c d
      = ((if ε a = ε b then (if d = a then E c b * E b a else 0) else 0)
          - (if ε a = ε b then (if a = c then E a b * E b d else 0) else 0))
        + ((if ε a = ε b then (if d = b then E a b * E c a else 0) else 0)
          - (if ε a = ε b then (if b = c then E a d * E b a else 0) else 0)) := by
  by_cases h : ε a = ε b
  · simp only [if_pos h]
    have h1 : E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0) :=
      hK a b c d h hcd
    have h2 : E b a * E c d - E c d * E b a = (if a = c then E b d else 0) - (if d = b then E c a else 0) :=
      hK b a c d h.symm hcd
    have key : E c d * (E a b * E b a) - E a b * E b a * E c d
        = -((E a b * E c d - E c d * E a b) * E b a) - E a b * (E b a * E c d - E c d * E b a) := by
      noncomm_ring
    rw [key, h1, h2]
    simp only [sub_mul, mul_sub, ite_mul, mul_ite, zero_mul, mul_zero]
    abel
  · simp only [if_neg h]
    simp

theorem double_sum_reduce_first {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if d = a then E c b * E b a else 0) else 0))
      = ∑ b : Fin n, (if ε d = ε b then E c b * E b d else 0) := by
  rw [Finset.sum_eq_single d]
  · apply Finset.sum_congr rfl
    intro b _
    simp
  · intro a _ had
    apply Finset.sum_eq_zero
    intro b _
    simp [Ne.symm had]
  · intro h
    exact absurd (Finset.mem_univ d) h

theorem double_sum_reduce_fourth {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if a = c then E a b * E b d else 0) else 0))
      = ∑ b : Fin n, (if ε c = ε b then E c b * E b d else 0) := by
  rw [Finset.sum_eq_single c]
  · apply Finset.sum_congr rfl
    intro b _
    simp
  · intro a _ hac
    apply Finset.sum_eq_zero
    intro b _
    simp [hac]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem double_sum_reduce_third {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if d = b then E a b * E c a else 0) else 0))
      = ∑ a : Fin n, (if ε a = ε d then E a d * E c a else 0) := by
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single d]
  · simp
  · intro b _ hbd
    simp [Ne.symm hbd]
  · intro h
    exact absurd (Finset.mem_univ d) h

theorem double_sum_reduce_second {V : Type} [AddCommGroup V] [_root_.Module ℂ V] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (c d : Fin n) :
    (∑ a : Fin n, ∑ b : Fin n, (if ε a = ε b then (if b = c then E a d * E b a else 0) else 0))
      = ∑ a : Fin n, (if ε a = ε c then E a d * E c a else 0) := by
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hbc
    simp [hbc]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem PositivityTheory.D.LK.casK_comm :
    ∀ {n : ℕ} {ε_h0 : Fin n → Bool} {V : Type} [inst_h2 : AddCommGroup V] [inst_h3 : _root_.Module ℂ V] {E : Fin n → Fin n → Module.End ℂ V}, PositivityTheory.D.DSIC.KRel ε_h0 E → ∀ {c d : Fin n}, ε_h0 c = ε_h0 d → Commute (E c d) (Formalism.REAL.CasK ε_h0 E) := by
  intro n ε V _ _ E hK c d hcd
  show E c d * Formalism.REAL.CasK ε E = Formalism.REAL.CasK ε E * E c d
  rw [← sub_eq_zero]
  have hsum : E c d * Formalism.REAL.CasK ε E - Formalism.REAL.CasK ε E * E c d
      = ∑ a : Fin n, ∑ b : Fin n, (E c d * (if ε a = ε b then E a b * E b a else 0)
          - (if ε a = ε b then E a b * E b a else 0) * E c d) := by
    unfold Formalism.REAL.CasK
    simp only [Finset.mul_sum, Finset.sum_mul, Finset.sum_sub_distrib]
  rw [hsum]
  simp only [commutator_casimir_term ε E hK hcd, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [double_sum_reduce_first, double_sum_reduce_fourth, double_sum_reduce_third, double_sum_reduce_second, hcd]
  simp

end UpperTheory.Reformulated.B.P6.r26a
end

section

namespace UpperTheory.Reformulated.B.P6.r08a

theorem GlobalTheory.CompanionTheory.AvgFree.Cov.exists_sep :
    ∀ {K : Type} [inst : AddCommGroup K] (H : AddSubgroup K) (T : Finset K), ∃ Rep ⊆ T, (∀ x ∈ T, ∃ r ∈ Rep, x - r ∈ H) ∧ ∀ r ∈ Rep, ∀ r' ∈ Rep, r - r' ∈ H → r = r' := by
  intro K inst H T
  classical
  refine Finset.induction_on T ?_ ?_
  · refine ⟨∅, Finset.Subset.refl _, ?_, ?_⟩
    · intro x hx
      exact absurd hx (Finset.notMem_empty x)
    · intro r hr
      exact absurd hr (Finset.notMem_empty r)
  · intro a S _ha ih
    obtain ⟨Rep, hsub, hcov, hsep⟩ := ih
    by_cases h : ∃ r ∈ Rep, a - r ∈ H
    · refine ⟨Rep, hsub.trans (Finset.subset_insert a S), ?_, hsep⟩
      intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hx
      · rw [hxa]
        exact h
      · exact hcov x hx
    · have h' : ∀ r ∈ Rep, a - r ∉ H := fun r hr har => h ⟨r, hr, har⟩
      refine ⟨insert a Rep, Finset.insert_subset_insert a hsub, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with hxa | hx
        · refine ⟨a, Finset.mem_insert_self a Rep, ?_⟩
          rw [hxa, sub_self]
          exact H.zero_mem
        · obtain ⟨r, hr, hxr⟩ := hcov x hx
          exact ⟨r, Finset.mem_insert_of_mem hr, hxr⟩
      · intro r hr r' hr' hrr
        rcases Finset.mem_insert.mp hr with hra | hr
        · rcases Finset.mem_insert.mp hr' with hr'a | hr'
          · rw [hra, hr'a]
          · rw [hra] at hrr
            exact absurd hrr (h' r' hr')
        · rcases Finset.mem_insert.mp hr' with hr'a | hr'
          · rw [hr'a] at hrr
            have hn := H.neg_mem hrr
            rw [neg_sub] at hn
            exact absurd hn (h' r hr)
          · exact hsep r hr r' hr' hrr

end UpperTheory.Reformulated.B.P6.r08a
end

section

namespace UpperTheory.Reformulated.B.P6.LargePrimeDivisors

open scoped Int LT OfNat Polynomial Dvd

open Polynomial in
theorem mul_sub_mul_add_ne_zero (f : Polynomial ℤ) (hf : 0 < f.natDegree) (c : ℤ) :
    f * (f - C c) * (f + C c) ≠ 0 := by
  have h1 : f ≠ 0 := by
    rintro rfl
    simp at hf
  have h2 : f - C c ≠ 0 := by
    intro h
    have h' : f = C c := sub_eq_zero.mp h
    rw [h', natDegree_C] at hf
    exact lt_irrefl _ hf
  have h3 : f + C c ≠ 0 := by
    intro h
    have h' : f = -C c := eq_neg_of_add_eq_zero_left h
    rw [h', natDegree_neg, natDegree_C] at hf
    exact lt_irrefl _ hf
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

theorem exists_nat_eval_mul_ne_zero (P : Polynomial ℤ) (hP : P ≠ 0) (a : ℤ) (ha : a ≠ 0) :
    ∃ t : ℕ, P.eval (a * (t : ℤ)) ≠ 0 := by
  by_contra h
  push_neg at h
  apply hP
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.infinite_of_injective_forall_mem (f := fun t : ℕ => a * (t : ℤ))
  · intro x y hxy
    have h2 : (x : ℤ) = (y : ℤ) := mul_left_cancel₀ ha hxy
    exact_mod_cast h2
  · intro t
    exact h t

theorem exists_prime_gt_dvd_eval_of_natDegree_pos (f : Polynomial ℤ) (hf : 0 < f.natDegree) (N : ℕ) :
    ∃ (p : ℕ) (m : ℤ), Nat.Prime p ∧ N < p ∧ (p : ℤ) ∣ Polynomial.eval m f := by
  by_cases hc : f.eval 0 = 0
  · obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes (N + 1)
    refine ⟨p, p, hp, by omega, ?_⟩
    have h1 := Polynomial.sub_dvd_eval_sub (p : ℤ) 0 f
    rw [hc, sub_zero, sub_zero] at h1
    exact h1
  · have hM0 : ((N.factorial : ℕ) : ℤ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos N).ne'
    have hcM : f.eval 0 * (N.factorial : ℤ) ≠ 0 := mul_ne_zero hc hM0
    obtain ⟨t, ht⟩ := exists_nat_eval_mul_ne_zero _ (mul_sub_mul_add_ne_zero f hf (f.eval 0)) _ hcM
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_add,
      Polynomial.eval_C] at ht
    obtain ⟨k, hk⟩ := Polynomial.sub_dvd_eval_sub (f.eval 0 * (N.factorial : ℤ) * (t : ℤ)) 0 f
    have hw : f.eval (f.eval 0 * (N.factorial : ℤ) * (t : ℤ)) =
        f.eval 0 * (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) := by
      linear_combination hk
    rw [hw] at ht
    have hv0 : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) ≠ 0 := by
      intro h0
      apply ht
      rw [h0]
      ring
    have hv1 : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) ≠ 1 := by
      intro h0
      apply ht
      rw [h0]
      ring
    have hv2 : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) ≠ -1 := by
      intro h0
      apply ht
      rw [h0]
      ring
    have hna : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs ≠ 1 := by
      intro h0
      rcases Int.natAbs_eq_iff.mp h0 with h | h
      · exact hv1 (by exact_mod_cast h)
      · exact hv2 (by rw [h]; norm_num)
    have hp : Nat.Prime ((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac) :=
      Nat.minFac_prime hna
    have hpv : ((((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac : ℕ)) : ℤ) ∣
        (1 + (N.factorial : ℤ) * ((t : ℤ) * k)) :=
      Int.ofNat_dvd_left.mpr (Nat.minFac_dvd _)
    refine ⟨_, f.eval 0 * (N.factorial : ℤ) * (t : ℤ), hp, ?_, ?_⟩
    · by_contra hle
      push_neg at hle
      have hpN : ((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac) ∣ N.factorial :=
        Nat.dvd_factorial hp.pos hle
      have hpN' : ((((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac : ℕ)) : ℤ) ∣
          (N.factorial : ℤ) * ((t : ℤ) * k) :=
        Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr hpN) _
      have h1 : ((((1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac : ℕ)) : ℤ) ∣ 1 :=
        (dvd_add_left hpN').mp hpv
      have h2 : (1 + (N.factorial : ℤ) * ((t : ℤ) * k)).natAbs.minFac ∣ 1 := by
        exact_mod_cast h1
      exact hp.one_lt.ne' (Nat.dvd_one.mp h2)
    · rw [hw]
      exact Dvd.dvd.mul_left hpv _

theorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.exists_large_prime_dvd_eval :
    ∀ (f : Polynomial ℤ), OfNat.ofNat (nat_lit 0) < f.natDegree → ∀ (N : ℕ), ∃ (p : ℕ) (m : ℤ), Nat.Prime p ∧ N < p ∧ p.cast ∣ Polynomial.eval m f := by
  intro f hf N
  exact exists_prime_gt_dvd_eval_of_natDegree_pos f hf N

end UpperTheory.Reformulated.B.P6.LargePrimeDivisors
end
