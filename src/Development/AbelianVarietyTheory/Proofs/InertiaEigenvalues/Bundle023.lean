module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Basic.Finite.Defs
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.ToDual
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Finite
public import Mathlib.Topology.ClusterPt
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

@[expose] public section

section

noncomputable section

open Finset PowerSeries

namespace GlobalTheory.JSW

theorem sum_finsuppAntidiag_univ_fin {M : Type*} [AddCommMonoid M] {m : ℕ} (d : ℕ)
    (F : (Fin m → ℕ) → M) :
    ∑ l ∈ finsuppAntidiag (univ : Finset (Fin m)) d, F l =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d, F k := by
  refine Finset.sum_equiv Finsupp.equivFunOnFinite ?_ ?_
  · intro l
    simp [mem_finsuppAntidiag, Finset.Nat.mem_antidiagonalTuple]
  · intro l _
    rfl

theorem coeff_prod_mk_fin {m : ℕ} (f : Fin m → ℕ → ℂ) (d : ℕ) :
    coeff d (∏ j, PowerSeries.mk (f j)) =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, f j (k j) := by
  rw [coeff_prod, sum_finsuppAntidiag_univ_fin d (fun k => ∏ j, coeff (k j) (PowerSeries.mk (f j)))]
  simp only [coeff_mk]

theorem prod_map_X_eq_monomial_toFinsupp {n : ℕ} (s : Multiset (Fin n)) :
    (s.map (MvPolynomial.X : Fin n → MvPolynomial (Fin n) ℤ)).prod =
      MvPolynomial.monomial (Multiset.toFinsupp s) 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add, map_add (f := _),
      Multiset.toFinsupp_singleton, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul]

theorem sum_toFinsupp_fin {n : ℕ} (s : Multiset (Fin n)) :
    ∑ i, Multiset.toFinsupp s i = Multiset.card s := by
  simp [Multiset.toFinsupp_apply, Multiset.sum_count_eq_card]

theorem hsymm_fin_eq_sum_monomial {n : ℕ} (k : ℕ) :
    MvPolynomial.hsymm (Fin n) ℤ k =
      ∑ l ∈ finsuppAntidiag (univ : Finset (Fin n)) k, MvPolynomial.monomial l 1 := by
  rw [MvPolynomial.hsymm]
  refine Finset.sum_bij (fun s _ => Multiset.toFinsupp s.1) ?_ ?_ ?_ ?_
  · intro s _
    rw [mem_finsuppAntidiag]
    refine ⟨?_, subset_univ _⟩
    rw [sum_toFinsupp_fin, s.2]
  · intro a _ b _ h
    exact Sym.coe_injective (Multiset.toFinsupp.injective h)
  · intro l hl
    rw [mem_finsuppAntidiag] at hl
    refine ⟨⟨Finsupp.toMultiset l, ?_⟩, mem_univ _, ?_⟩
    · rw [Finsupp.card_toMultiset, Finsupp.sum_fintype _ _ (fun _ => rfl)]
      exact hl.1
    · simp
  · intro s _
    exact prod_map_X_eq_monomial_toFinsupp s.1

theorem eval₂_hsymm_fin {n : ℕ} (α : Fin n → ℂ) (k : ℕ) :
    MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ k) =
      ∑ l ∈ Finset.Nat.antidiagonalTuple n k, ∏ i, α i ^ l i := by
  rw [hsymm_fin_eq_sum_monomial, MvPolynomial.eval₂_sum,
    ← sum_finsuppAntidiag_univ_fin k (fun l => ∏ i, α i ^ l i)]
  refine sum_congr rfl fun l _ => ?_
  rw [MvPolynomial.eval₂_monomial, map_one, one_mul, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]

theorem one_sub_C_mul_X_mul_mk_pow (a : ℂ) :
    (1 - PowerSeries.C a * PowerSeries.X) * PowerSeries.mk (fun k => a ^ k) = 1 := by
  ext k
  rw [sub_mul, one_mul, map_sub, mul_assoc, coeff_C_mul]
  cases k with
  | zero => simp
  | succ k => simp [pow_succ, mul_comm]

theorem mk_hsymm_mul_prod_one_sub {n : ℕ} (α : Fin n → ℂ) (u : ℂ) :
    PowerSeries.mk (fun k => MvPolynomial.eval₂ (Int.castRingHom ℂ) α
        (MvPolynomial.hsymm (Fin n) ℤ k) * u ^ k) *
      ∏ i, (1 - PowerSeries.C (α i * u) * PowerSeries.X) = 1 := by
  have h : PowerSeries.mk (fun k => MvPolynomial.eval₂ (Int.castRingHom ℂ) α
        (MvPolynomial.hsymm (Fin n) ℤ k) * u ^ k) =
      ∏ i, PowerSeries.mk (fun k => (α i * u) ^ k) := by
    ext k
    rw [coeff_prod_mk_fin, coeff_mk, eval₂_hsymm_fin, sum_mul]
    refine sum_congr rfl fun l hl => ?_
    rw [Finset.Nat.mem_antidiagonalTuple] at hl
    simp_rw [mul_pow, prod_mul_distrib, prod_pow_eq_pow_sum, hl]
  rw [h, ← prod_mul_distrib]
  exact prod_eq_one fun i _ => by rw [mul_comm]; exact one_sub_C_mul_X_mul_mk_pow _

theorem mk_sum_prod_hsymm_mul_prod_one_sub : ∀ {m n : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (T : ℂ),
    PowerSeries.mk (fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j)) *
      ∏ p : Fin n × Fin m, (1 - PowerSeries.C (α p.1 * β p.2 * T) * PowerSeries.X) = 1 := by
  intro m n α β T
  have h1 : PowerSeries.mk (fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j)) =
      ∏ j, PowerSeries.mk (fun k => MvPolynomial.eval₂ (Int.castRingHom ℂ) α
        (MvPolynomial.hsymm (Fin n) ℤ k) * (β j * T) ^ k) := by
    ext d
    rw [coeff_mk, coeff_prod_mk_fin, mul_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [Finset.Nat.mem_antidiagonalTuple] at hk
    simp_rw [mul_pow, ← mul_assoc, prod_mul_distrib, prod_pow_eq_pow_sum, hk]
    ring
  have h2 : ∏ p : Fin n × Fin m, (1 - PowerSeries.C (α p.1 * β p.2 * T) * PowerSeries.X) =
      ∏ j, ∏ i, (1 - PowerSeries.C (α i * (β j * T)) * PowerSeries.X) := by
    rw [Fintype.prod_prod_type, Finset.prod_comm]
    simp_rw [mul_assoc]
  rw [h1, h2, ← prod_mul_distrib]
  exact prod_eq_one fun j _ => mk_hsymm_mul_prod_one_sub α (β j * T)

end GlobalTheory.JSW
end
end

section

namespace GlobalTheory

theorem involution_pair_representatives :
    ∀ (ι : Type) [Finite ι] (s : ι → ι), (∀ i, s (s i) = i) → ∃ (r : ℕ) (e : Fin r → ι),
      (∀ j k, e j = e k → j = k) ∧ (∀ j k, s (e j) ≠ e k) ∧
        ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j) := by
  intro ι _ s hs
  classical
  haveI := Fintype.ofFinite ι
  set enc : ι → ℕ := fun i => (Fintype.equivFin ι i : ℕ) with henc_def
  have henc : Function.Injective enc := fun a b h =>
    (Fintype.equivFin ι).injective (Fin.ext h)
  set S : Finset ι := Finset.univ.filter (fun i => enc i < enc (s i)) with hS
  have memS : ∀ x : S, enc (x : ι) < enc (s x) := fun x => (Finset.mem_filter.1 x.2).2
  refine ⟨S.card, fun j => (S.equivFin.symm j : ι), ?_, ?_, ?_⟩
  · intro j k h
    exact S.equivFin.symm.injective (Subtype.ext h)
  · intro j k h
    simp only at h
    have hj := memS (S.equivFin.symm j)
    have hk := memS (S.equivFin.symm k)
    generalize (S.equivFin.symm j : ι) = a at h hj
    generalize (S.equivFin.symm k : ι) = b at h hk
    subst h
    rw [hs] at hk
    omega
  · intro i
    by_cases hi : s i = i
    · exact Or.inl hi
    right
    have hne : enc i ≠ enc (s i) := fun h => hi (henc h).symm
    rcases lt_or_gt_of_ne hne with h | h
    · have hm : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
      exact ⟨S.equivFin ⟨i, hm⟩, Or.inl (by simp)⟩
    · have hm : s i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hs]; exact h⟩
      exact ⟨S.equivFin ⟨s i, hm⟩, Or.inr (by simp [hs])⟩

end GlobalTheory
end

section

noncomputable section

open Classical

namespace GlobalTheory.PositionData

def intPts (A : Set ℚ) : Finset ℤ :=
  if h : ((fun z : ℤ => (z : ℚ)) ⁻¹' A).Finite then h.toFinset else ∅

theorem mem_intPts {A : Set ℚ} (hA : A.Finite) (z : ℤ) : z ∈ intPts A ↔ (z : ℚ) ∈ A := by
  have h : ((fun z : ℤ => (z : ℚ)) ⁻¹' A).Finite :=
    hA.preimage (Set.injOn_of_injective Int.cast_injective)
  unfold intPts
  rw [dite_eq_left h, Set.Finite.mem_toFinset]
  rfl

def mnLo (Fl : Finset ℤ) : ℤ := (insert 0 Fl).min' (Finset.insert_nonempty _ _)

def mxLo (t : ℕ) (Fl : Finset ℤ) : ℤ := (insert ((t : ℤ) - 1) Fl).max' (Finset.insert_nonempty _ _)

def mnAll (Fl Fc : Finset ℤ) : ℤ := (insert 0 (Fl ∪ Fc)).min' (Finset.insert_nonempty _ _)

def mxAll (t : ℕ) (Fl Fc : Finset ℤ) : ℤ :=
  (insert ((t : ℤ) - 1) (Fl ∪ Fc)).max' (Finset.insert_nonempty _ _)

def wS (up : Bool) (Fl Fc : Finset ℤ) : ℕ :=
  if up then (1 - mnLo Fl).toNat else (1 - mnAll Fl Fc).toNat

def etaS (t : ℕ) (Fl : Finset ℤ) : ℕ := (mxLo t Fl - mnLo Fl + 1).toNat

def hS (up : Bool) (t : ℕ) (Fl Fc : Finset ℤ) : ℕ :=
  if up then (mxAll t Fl Fc + wS up Fl Fc + 1).toNat else (mxLo t Fl + wS up Fl Fc + 1).toNat

def US (up : Bool) (Fl Fc : Finset ℤ) : Multiset ℤ :=
  (Fl ∪ Fc).val.map (fun z => z + (wS up Fl Fc : ℤ))

theorem count_US (up : Bool) (Fl Fc : Finset ℤ) (b : ℤ) :
    (US up Fl Fc).count (b + wS up Fl Fc) = if b ∈ Fl ∪ Fc then 1 else 0 := by
  unfold US
  rw [Multiset.count_map_eq_count' _ _ (add_left_injective _)]
  split_ifs with h
  · exact Multiset.count_eq_one_of_mem (Fl ∪ Fc).nodup h
  · exact Multiset.count_eq_zero.mpr h

end GlobalTheory.PositionData
end
end

section

open scoped BigOperators

namespace GlobalTheory

theorem exists_limit_family_of_finite_coefficients (σ I R : Type) [Finite σ] [Finite I] [Finite R]
    (F : ℕ → I → (σ →₀ ℕ) → R) :
    ∃ G : I → (σ →₀ ℕ) → R, ∀ N M₀ : ℕ, ∃ M, M₀ ≤ M ∧
      ∀ x m, m.degree ≤ N → F M x m = G x m := by
  let _ : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩

  obtain ⟨G, hG⟩ : ∃ G : I → (σ →₀ ℕ) → R, MapClusterPt G Filter.atTop F :=
    exists_clusterPt_of_compactSpace _
  refine ⟨G, fun N M₀ => ?_⟩

  have hnhds : ∀ᶠ H in nhds G, ∀ x, ∀ m ∈ {m : σ →₀ ℕ | m.degree ≤ N}, H x m = G x m := by
    refine Filter.eventually_all.2 fun x => ?_
    refine ((Finsupp.finite_of_degree_le N).eventually_all).2 fun m _ => ?_
    have hc : Continuous fun H : I → (σ →₀ ℕ) → R => H x m :=
      (continuous_apply m).comp (continuous_apply x)
    exact hc.continuousAt.eventually (isOpen_discrete {G x m} |>.mem_nhds rfl)
  obtain ⟨M, hM, hFM⟩ := Filter.frequently_atTop.1 (hG.frequently hnhds) M₀
  exact ⟨M, hM, fun x m hm => hFM x m hm⟩

end GlobalTheory
end

section

namespace GlobalTheory

theorem block_is_the_run : ∀ (n p t : ℕ) (a : ℕ → ℤ) (c : ℤ), (∀ i j, i ≤ j → j < n → a j ≤ a i) →
    p + t ≤ n → p < t → n - (p + t) < t → (∀ j, p ≤ j → j < p + t → a j = a p) →
    (1 ≤ p → a p < a (p - 1)) → (p + t < n → a (p + t) < a p) →
    (∀ i < t, ∃ j < n, a j - j = c - i) → c = a p - p := by
  intro n p t a c hmono hpt hpt' hn hrun hleft hright hwin
  obtain ⟨j0, hj0n, hj0⟩ := hwin 0 (by omega)

  have key : ∀ i, i < t → j0 + i < n ∧ a (j0 + i) = a j0 := by
    intro i
    induction i with
    | zero => intro _; simpa using hj0n
    | succ i ih =>
      intro hi
      obtain ⟨h1, h2⟩ := ih (by omega)
      obtain ⟨j, hjn, hj⟩ := hwin (i + 1) hi
      push_cast at hj hj0
      have hge : j0 + i + 1 ≤ j := by
        by_contra hlt
        have := hmono j (j0 + i) (by omega) h1
        omega
      have hle := hmono (j0 + i) j (by omega) hjn
      have hj' : j = j0 + i + 1 := by omega
      refine ⟨by omega, ?_⟩
      rw [show j0 + (i + 1) = j by omega]
      omega
  have hq := (key (t - 1) (by omega)).1
  have hconst : ∀ k, j0 ≤ k → k < j0 + t → a k = a j0 := by
    intro k h1 h2
    have := (key (k - j0) (by omega)).2
    rwa [show j0 + (k - j0) = k by omega] at this
  rcases lt_trichotomy j0 p with h | h | h
  ·
    exfalso
    have e1 := hconst (p - 1) (by omega) (by omega)
    have e2 := hconst p (by omega) (by omega)
    have := hleft (by omega)
    omega
  · subst h
    push_cast at hj0
    omega
  ·
    exfalso
    have e1 := hconst (p + t - 1) (by omega) (by omega)
    have e2 := hconst (p + t) (by omega) (by omega)
    have e3 := hrun (p + t - 1) (by omega) (by omega)
    have := hright (by omega)
    omega

end GlobalTheory
end

section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem exists_residue_annihilator_of_not_standard_column_form (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O) (hϖ : Irreducible ϖ) (x : Matrix (Fin r ⊕ Fin t) (Fin r) O)
    (hx : ¬ ∃ (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K)) :
    ∃ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 ∧ ∀ u : Fin r ⊕ Fin t → O, (fun i => algebraMap O K (u i)) ∈ Submodule.span K (Set.range fun j => fun i => algebraMap O K (x i j)) → (∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0) → a ⬝ᵥ (fun i => IsLocalRing.residue O (u (Sum.inl i))) = 0 := by
  classical
  set V := Submodule.span K (Set.range fun j => fun i => algebraMap O K (x i j)) with hV
  let A : Set (Fin r → IsLocalRing.ResidueField O) :=
    {v | ∃ u : Fin r ⊕ Fin t → O, (fun i => algebraMap O K (u i)) ∈ V ∧
      (∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0) ∧ (fun i => IsLocalRing.residue O (u (Sum.inl i))) = v}
  have hA0 : (0 : Fin r → IsLocalRing.ResidueField O) ∈ A :=
    ⟨0, by convert V.zero_mem using 1; ext; simp, by simp, by ext; simp⟩
  have hAadd : ∀ v w, v ∈ A → w ∈ A → v + w ∈ A := by
    rintro v w ⟨u, hu, hu0, rfl⟩ ⟨u', hu', hu0', rfl⟩
    refine ⟨u + u', ?_, ?_, ?_⟩
    · have := V.add_mem hu hu'
      convert this using 1
      ext i; simp
    · intro i; simp [hu0 i, hu0' i]
    · ext i; simp
  have hAsmul : ∀ (c : IsLocalRing.ResidueField O) v, v ∈ A → c • v ∈ A := by
    rintro c v ⟨u, hu, hu0, rfl⟩
    obtain ⟨c', rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨c' • u, ?_, ?_, ?_⟩
    · have := V.smul_mem (algebraMap O K c') hu
      convert this using 1
      ext i; simp
    · intro i; simp [hu0 i]
    · ext i; simp
  have hspan : ∀ v ∈ Submodule.span (IsLocalRing.ResidueField O) A, v ∈ A := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact hA0
    | add y w _ _ hy hw => exact hAadd y w hy hw
    | smul c y _ hy => exact hAsmul c y hy
  by_cases htop : Submodule.span (IsLocalRing.ResidueField O) A = ⊤
  · exfalso
    apply hx
    have hmem : ∀ i : Fin r, (Pi.single i 1 : Fin r → IsLocalRing.ResidueField O) ∈ A :=
      fun i => hspan _ (htop ▸ Submodule.mem_top)
    choose u hu hu0 hu1 using hmem
    let B : Matrix (Fin r ⊕ Fin t) (Fin r) O := fun p j => u j p
    let T : Matrix (Fin r) (Fin r) O := fun i j => u j (Sum.inl i)
    have hT : IsUnit T.det := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
      have : (IsLocalRing.residue O).mapMatrix T = 1 := by
        ext i j
        have := congrFun (hu1 j) i
        show IsLocalRing.residue O (u j (Sum.inl i)) = _
        rw [this]; simp [Pi.single_apply, Matrix.one_apply]
      rw [this, Matrix.det_one]; exact one_ne_zero
    have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
    have hdiv : ∀ (i : Fin t) (j : Fin r), ∃ c, u j (Sum.inr i) = ϖ * c := by
      intro i j
      have : u j (Sum.inr i) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.residue_eq_zero_iff _).1 (hu0 j i)
      rw [hmax, Ideal.mem_span_singleton] at this
      exact this
    choose C hC using hdiv
    have hcol : ∀ j, ∃ c : Fin r → K, ∑ l, c l • (fun i => algebraMap O K (x i l)) = fun i => algebraMap O K (u j i) :=
      fun j => (Submodule.mem_span_range_iff_exists_fun K).1 (hu j)
    choose d hd using hcol
    let D : Matrix (Fin r) (Fin r) K := fun l j => d j l
    have hBD : x.map (algebraMap O K) * D = B.map (algebraMap O K) := by
      ext p j
      have := congrFun (hd j) p
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [Matrix.mul_apply, Matrix.map_apply]
      show _ = algebraMap O K (u j p)
      rw [← this]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hTD : (x.submatrix Sum.inl id).map (algebraMap O K) * D = T.map (algebraMap O K) := by
      ext i j
      have := congrFun₂ hBD (Sum.inl i) j
      simpa [Matrix.mul_apply] using this
    have hdetT : (T.map (algebraMap O K)).det = algebraMap O K T.det := by
      rw [RingHom.map_det]; rfl
    have hTK : IsUnit (T.map (algebraMap O K)).det := by
      rw [hdetT]; exact hT.map _
    have hDu : IsUnit D.det := by
      rw [← hTD, Matrix.det_mul] at hTK
      exact isUnit_of_mul_isUnit_right hTK
    have hdetTi : ((T⁻¹).map (algebraMap O K)).det = algebraMap O K (T⁻¹).det := by
      rw [RingHom.map_det]; rfl
    have hg : IsUnit (D * (T⁻¹).map (algebraMap O K)) := by
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, hdetTi]
      exact hDu.mul ((Matrix.isUnit_nonsing_inv_det T hT).map _)
    refine ⟨hg.unit, Matrix.fromRows 0 (Matrix.of fun i j => ∑ l, C i l * T⁻¹ l j), ?_⟩
    rw [IsUnit.unit_spec, ← Matrix.mul_assoc, hBD, ← Matrix.map_mul]
    congr 1
    ext p j
    rcases p with i | i
    · rw [Matrix.mul_apply]
      have := congrFun₂ (Matrix.mul_nonsing_inv T hT) i j
      rw [Matrix.mul_apply] at this
      simpa [B, T] using this
    · rw [Matrix.mul_apply]
      simp [B, hC, Finset.mul_sum, mul_assoc]
  · obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 htop)
    have hf : ∀ v, f v = (fun i => f (Pi.single i 1)) ⬝ᵥ v := by
      intro v
      conv_lhs => rw [pi_eq_sum_univ v]

      simp only [map_sum, map_smul, smul_eq_mul, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm]; congr 2; ext j; simp [Pi.single_apply, eq_comm]
    refine ⟨fun i => f (Pi.single i 1), ?_, ?_⟩
    · intro h0
      apply hf0
      apply LinearMap.ext
      intro v
      rw [LinearMap.zero_apply, hf v, h0, zero_dotProduct]
    · intro u hu hu0
      rw [← hf]
      exact hle (Submodule.subset_span ⟨u, hu, hu0, rfl⟩)

end GlobalTheory
end
